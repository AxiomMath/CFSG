module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixE
public import CFSG.LocalAnalysis.SteinbergSFSingleCommModel3Linear
public import CFSG.LocalAnalysis.SteinbergSFSingleCommModel3Unitary
public import CFSG.LocalAnalysis.SteinbergSFSingleCommModel3Transfer
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Open.StatedAPI

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup
open CFSG.Assembly.LowTwoRank (StatedSL StatedSU StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

section Axis

variable {F' : Type} [Field F']

theorem model3ax_scalar_pow_three {K : Type} [Field K]
    (g : Matrix.GeneralLinearGroup (Fin 3) K)
    (hg : g ∈ StatedScalars (Fin 3) K) (hdet : (g : Matrix (Fin 3) (Fin 3) K).det = 1) :
    g ^ 3 = 1 := by
  unfold StatedScalars at hg
  obtain ⟨c, rfl⟩ := MonoidHom.mem_range.mp hg
  have hc : (c : K) ^ 3 = 1 := by
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.det_diagonal] using hdet
  rw [← map_pow]
  have h1 : c ^ 3 = 1 := Units.ext (by simpa using hc)
  rw [h1, map_one]

theorem model3ax_pow_three_of_mem {K : Type} [Field K]
    {H : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K)}
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K).det = 1) {g : ↥H}
    (hg : (g : Matrix.GeneralLinearGroup (Fin 3) K) ∈ StatedScalars (Fin 3) K) :
    g ^ 3 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  exact model3ax_scalar_pow_three _ hg (hdet _ g.2)

theorem model3ax_finite_GL (K : Type) [Field K] [Finite K] :
    Finite (Matrix.GeneralLinearGroup (Fin 3) K) := by
  have : Finite (Matrix (Fin 3) (Fin 3) K) := inferInstanceAs (Finite (Fin 3 → Fin 3 → K))
  exact Finite.of_injective (fun g : Matrix.GeneralLinearGroup (Fin 3) K =>
    (g : Matrix (Fin 3) (Fin 3) K)) (fun a b h => Units.ext h)

theorem model3ax_finite_subgroup_GL {K : Type} [Field K] [Finite K]
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K)) : Finite ↥H := by
  have := model3ax_finite_GL K
  infer_instance

theorem model3ax_odd_card_of_pow_three {G : Type*} [Group G] [Finite G]
    (h : ∀ g : G, g ^ 3 = 1) : Odd (Nat.card G) := by
  rcases Nat.even_or_odd (Nat.card G) with he | ho
  · exfalso
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := G) 2 (even_iff_two_dvd.mp he)
    have h3 := orderOf_dvd_of_pow_eq_one (h x)
    rw [hx] at h3
    omega
  · exact ho

theorem model3ax_odd_ker_of_exp_three {G Y : Type*} [Group G] [Finite G] [Group Y]
    (γ : G →* Y) (h : ∀ g ∈ γ.ker, g ^ 3 = 1) : Odd (Nat.card γ.ker) := by
  apply model3ax_odd_card_of_pow_three
  intro g
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  exact h g.1 g.2

theorem model3_odd_card_ker_statedSU {m : ℕ} (hF' : UnitaryFieldData 2 m F') {Y : Type*} [Group Y]
    (γ : ↥(StatedSU 3 (2 ^ m) F') →* Y)
    (hker : γ.ker ≤ (StatedScalars (Fin 3) F').subgroupOf (StatedSU 3 (2 ^ m) F')) :
    Odd (Nat.card γ.ker) := by
  haveI := hF'.finite
  haveI : Finite ↥(StatedSU 3 (2 ^ m) F') := model3ax_finite_subgroup_GL _
  apply model3ax_odd_ker_of_exp_three γ
  intro g hg
  exact model3ax_pow_three_of_mem (H := StatedSU 3 (2 ^ m) F')
    (fun x hx => CFSG.Open.StatedAPI.det_of_mem_statedSU hx) (Subgroup.mem_subgroupOf.mp (hker hg))

theorem model3_of_linear_cover [Finite F'] [CharP F' 2] {Y : Type*} [Group Y]
    (γ : ↥(StatedSL 3 F') →* Y) (hγ : Function.Surjective γ)
    (hker : γ.ker ≤ (StatedScalars (Fin 3) F').subgroupOf (StatedSL 3 F')) (R : Sylow 2 Y) :
    Model3Concl Y (R : Subgroup Y) (Nat.card F') := by
  haveI : Finite ↥(StatedSL 3 F') := model3ax_finite_subgroup_GL _
  let e := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F'
  haveI : Finite (Matrix.SpecialLinearGroup (Fin 3) F') := Finite.of_injective (⇑e) e.injective
  have hodd : Odd (Nat.card (γ.comp e.toMonoidHom).ker) := by
    apply model3ax_odd_ker_of_exp_three (γ.comp e.toMonoidHom)
    intro g hg
    have hg' : e g ∈ γ.ker := MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hg)
    have hcs : ((e g : ↥(StatedSL 3 F')) : Matrix.GeneralLinearGroup (Fin 3) F') ∈
        StatedScalars (Fin 3) F' :=
      Subgroup.mem_subgroupOf.mp (hker hg')
    have h3 : (e g) ^ 3 = 1 :=
      model3ax_pow_three_of_mem (H := StatedSL 3 F')
        (fun x hx => CFSG.Open.StatedAPI.det_of_mem_statedSL hx) hcs
    apply e.injective
    rw [map_pow, h3, map_one]
  exact model3_of_cover (γ.comp e.toMonoidHom) (hγ.comp e.surjective) hodd model3_linear
    ⟨R, rfl⟩

theorem model3_of_unitary_cover {m : ℕ} (hm : 2 ≤ m) (hF' : UnitaryFieldData 2 m F')
    {Y : Type*} [Group Y] (γ : ↥(StatedSU 3 (2 ^ m) F') →* Y) (hγ : Function.Surjective γ)
    (hker : γ.ker ≤ (StatedScalars (Fin 3) F').subgroupOf (StatedSU 3 (2 ^ m) F'))
    (R : Sylow 2 Y) : Model3Concl Y (R : Subgroup Y) (2 ^ m) := by
  haveI := hF'.finite
  haveI : Finite ↥(StatedSU 3 (2 ^ m) F') := model3ax_finite_subgroup_GL _
  exact model3_of_cover γ hγ (model3_odd_card_ker_statedSU hF' γ hker) (model3_unitary hm hF')
    ⟨R, rfl⟩

theorem model3_of_axis_conclusions {F : Type} [Group F] [Finite F] {K : Type} [Field K] {n : ℕ}
    {S Y V : Subgroup F} {t : F} (hn : 2 ≤ n)
    (hmod : LocalSixE.NontrivialModel F n S Y V t)
    (hc : PrincipalLayers.NontrivialAxisConclusion F K n S Y V t) :
    ∃ R : Sylow 2 ↥Y, (R : Subgroup ↥Y).map Y.subtype = V ∧
      Model3Concl ↥Y (R : Subgroup ↥Y) (2 ^ n) := by
  obtain ⟨-, -, hcm, hsyl⟩ := hmod
  obtain ⟨⟨R, hR⟩, -, -⟩ := hsyl
  refine ⟨R, hR, ?_⟩
  obtain ⟨-, -, -, -, hlin, hunit⟩ := hc
  rcases hcm with hPSL | hPSU
  · obtain ⟨-, K', hKf, hKfin, hKc, ⟨η⟩⟩ := hPSL
    haveI : Fintype K' := Fintype.ofFinite K'
    haveI : CharP K' 2 := charP_of_card_eq_prime_pow (f := n)
      (by rw [← Nat.card_eq_fintype_card, hKc])
    obtain ⟨-, -, -, γ, -, -, hγ, hker, -, -, -, -⟩ := hlin n K' hKc η
    have key := model3_of_linear_cover γ hγ hker R
    rw [hKc] at key
    exact key
  · obtain ⟨-, K', hKf, hKfin, hKc, ⟨η⟩⟩ := hPSU
    have hF' : UnitaryFieldData 2 n K' :=
      ⟨Nat.prime_two, by omega, by rw [hKc]; ring⟩
    obtain ⟨-, -, -, γ, -, -, hγ, hker, -, -, -, -⟩ := hunit n K' hF' η
    exact model3_of_unitary_cover hn hF' γ hγ hker R

end Axis

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
