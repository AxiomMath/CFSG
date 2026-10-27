module

public import CFSG.RankThree.PartTwo.Sec16.Kcd166.ThetaTriple
public import CFSG.RankThree.PartTwo.Sec16.Kcd166.IOne
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.RankThree.PartTwo.Sec16.Kcd166

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec17 CFSG.RankThree.PartTwo.Sec16 CFSG.GH74.GLS
open scoped Pointwise commutatorElement

section General

variable {G : Type} [Group G]

private theorem commutator_zpowers_le_self {Q : Subgroup G} {c : G}
    (hc : c ∈ Subgroup.normalizer (Q : Set G)) : ⁅Q, Subgroup.zpowers c⁆ ≤ Q := by
  rw [Subgroup.commutator_le]
  intro q hq y hy
  have hyN : y ∈ Subgroup.normalizer (Q : Set G) := (Subgroup.zpowers_le.mpr hc) hy
  have h1 : y * q⁻¹ * y⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hyN q⁻¹).mp (inv_mem hq)
  rw [commutatorElement_def, show q * y * q⁻¹ * y⁻¹ = q * (y * q⁻¹ * y⁻¹) by group]
  exact mul_mem hq h1

private theorem mem_normalizer_commutator {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hH hK ⊢
  rw [Subgroup.map_commutator, hH, hK]

private theorem mem_normalizer_inSubgroup_perfectResidual {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer (inSubgroup perfectResidual K : Set G) :=
  CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (perfectResidual ↥K) hg

private theorem commutator_le_inf_centralizer {P : Subgroup G} {b c : G}
    (hcP : c ∈ Subgroup.normalizer (P : Set G)) (hcb : Commute c b) :
    ⁅P ⊓ Subgroup.centralizer ({b} : Set G), Subgroup.zpowers c⁆ ≤
      P ⊓ Subgroup.centralizer ({b} : Set G) := by
  refine commutator_zpowers_le_self ?_
  refine Subgroup.inf_normalizer_le_normalizer_inf ⟨hcP, ?_⟩
  exact Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hcb.eq)

private theorem le_normalizer_of_commutator_le {P J : Subgroup G} (h : ⁅P, J⁆ ≤ J) :
    P ≤ Subgroup.normalizer (J : Set G) := by
  have key : ∀ y ∈ P, ∀ j ∈ J, y * j * y⁻¹ ∈ J := by
    intro y hy j hj
    have h1 : ⁅y, j⁆ ∈ J := h (Subgroup.commutator_mem_commutator hy hj)
    rw [show y * j * y⁻¹ = ⁅y, j⁆ * j by rw [commutatorElement_def]; group]
    exact mul_mem h1 hj
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro j
  refine ⟨key x hx j, fun hj => ?_⟩
  have := key x⁻¹ (inv_mem hx) _ hj
  simpa [mul_assoc] using this

private theorem mem_normalizer_subgroupOf {X U : Subgroup G} {g : G} (hgX : g ∈ X)
    (hg : g ∈ Subgroup.normalizer (U : Set G)) :
    (⟨g, hgX⟩ : ↥X) ∈ Subgroup.normalizer ((U.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact Subgroup.mem_normalizer_iff.mp hg (x : G)

end General

section Transport

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem exists_iOne_at (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d)
    {b : G} (hb : b ∈ ({c * d, c * d ^ 2} : Set G)) {X : Subgroup G}
    (hXL : X = lB A (Subgroup.closure {c, d}) ⊔ inSubgroup (aschbacherSolvableCore 3) X)
    {J P : Subgroup G} {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) (hPU : IsPGroup p P)
    (hAP : A ≤ Subgroup.normalizer (P : Set G)) (hPJ : ⁅P, J⁆ ≤ CFSG.Open.pCoreOf 2 J)
    (hIX : inSubgroup perfectResidual (J ⊓ Subgroup.centralizer ({b} : Set G)) ≤ X)
    (hIA5 : Nonempty (↥(inSubgroup perfectResidual (J ⊓ Subgroup.centralizer ({b} : Set G))) ⧸
      CFSG.pCore 2 ↥(inSubgroup perfectResidual (J ⊓ Subgroup.centralizer ({b} : Set G))) ≃*
      alternatingGroup (Fin 5)))
    (hUθ : ⁅P ⊓ Subgroup.centralizer ({b} : Set G), Subgroup.zpowers c⁆ ≤
      inSubgroup (aschbacherSolvableCore 3) X)
    (hUidem : ⁅⁅P ⊓ Subgroup.centralizer ({b} : Set G), Subgroup.zpowers c⁆,
      Subgroup.zpowers d⁆ = ⁅P ⊓ Subgroup.centralizer ({b} : Set G), Subgroup.zpowers c⁆) :
    IsPGroup p ↥((⁅P ⊓ Subgroup.centralizer ({b} : Set G), Subgroup.zpowers c⁆).subgroupOf X) ∧
      (⁅P ⊓ Subgroup.centralizer ({b} : Set G), Subgroup.zpowers c⁆).subgroupOf X ≤
        aschbacherSolvableCore 3 ↥X ∧
      ⁅(⁅P ⊓ Subgroup.centralizer ({b} : Set G), Subgroup.zpowers c⁆).subgroupOf X,
        Subgroup.zpowers (⟨d, mem_of_eq_lB_sup h hJ hdA hd1 hdc hXL⟩ : ↥X)⁆ =
        (⁅P ⊓ Subgroup.centralizer ({b} : Set G), Subgroup.zpowers c⁆).subgroupOf X ∧
      ∃ I₁ : Subgroup ↥X, Group.IsPerfect ↥I₁ ∧
        I₁ ≤ Subgroup.centralizer
          ({(⟨d, mem_of_eq_lB_sup h hJ hdA hd1 hdc hXL⟩ : ↥X)} : Set ↥X) ∧
        (⁅P ⊓ Subgroup.centralizer ({b} : Set G), Subgroup.zpowers c⁆).subgroupOf X ≤
          Subgroup.centralizer (I₁ : Set ↥X) ∧
        IsPGroup 2 ↥(I₁ ⊓ aschbacherSolvableCore 3 ↥X) ∧
        Nonempty (↥(I₁.map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X))) ≃*
          alternatingGroup (Fin 5)) := by
  classical
  set U := ⁅P ⊓ Subgroup.centralizer ({b} : Set G), Subgroup.zpowers c⁆
  set I := inSubgroup perfectResidual (J ⊓ Subgroup.centralizer ({b} : Set G))
  set θ' := aschbacherSolvableCore 3 ↥X
  have hdX : d ∈ X := mem_of_eq_lB_sup h hJ hdA hd1 hdc hXL
  set d' : ↥X := ⟨d, hdX⟩
  have hAab := h.toSec14Std.isE27.1.1.is_comm
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, Commute x y := fun x hx y hy =>
    congrArg Subtype.val (hAab.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcA : c ∈ A := (Sec13.zpowers_mem_omegaA_iff.mp h.zpowers_mem_omegaA).1
  have hbA : b ∈ A := by
    rcases hb with rfl | rfl
    · exact mul_mem hcA hdA
    · exact mul_mem hcA (pow_mem hdA 2)
  have hcb : Commute c b := hcomm c hcA b hbA
  have hdb : Commute d b := hcomm d hdA b hbA
  have hdcomm : Commute d c := hcomm d hdA c hcA
  have hUPb : U ≤ P ⊓ Subgroup.centralizer ({b} : Set G) :=
    commutator_le_inf_centralizer (hAP hcA) hcb
  have hUp : IsPGroup p U := hPU.to_le (hUPb.trans inf_le_left)
  have hUX : U ≤ X := hUθ.trans (Subgroup.map_subtype_le _)
  have hdNb : d ∈ Subgroup.normalizer (Subgroup.centralizer ({b} : Set G) : Set G) :=
    Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hdb.eq)
  have hdNc : d ∈ Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    congr 1
    simp [MulAut.conj_apply, hdcomm.eq]
  have hdNU : d ∈ Subgroup.normalizer (U : Set G) :=
    mem_normalizer_commutator (Subgroup.inf_normalizer_le_normalizer_inf ⟨hAP hdA, hdNb⟩) hdNc
  have hdNI : d ∈ Subgroup.normalizer (I : Set G) :=
    mem_normalizer_inSubgroup_perfectResidual
      (Subgroup.inf_normalizer_le_normalizer_inf ⟨hAJ hdA, hdNb⟩)
  have hPJn : P ≤ Subgroup.normalizer (J : Set G) :=
    le_normalizer_of_commutator_le (hPJ.trans (Subgroup.map_subtype_le _))
  have hUNI : ∀ u ∈ U, u ∈ Subgroup.normalizer (I : Set G) := by
    intro u hu
    have hu' := hUPb hu
    refine mem_normalizer_inSubgroup_perfectResidual
      (Subgroup.inf_normalizer_le_normalizer_inf ⟨hPJn hu'.1, ?_⟩)
    exact Subgroup.le_normalizer hu'.2
  set U' := U.subgroupOf X with hU'
  set I' := I.subgroupOf X
  have hUp' : IsPGroup p ↥U' := hUp.comap_subtype
  have hUD' : U' ≤ θ' := by
    intro x hx
    have hx' : (x : G) ∈ U := Subgroup.mem_subgroupOf.mp hx
    exact (Subgroup.mem_map_iff_mem X.subtype_injective).mp (hUθ hx')
  have hU'map : U'.map X.subtype = U := by
    rw [hU', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hUX]
  have hUd' : ⁅U', Subgroup.zpowers d'⁆ = U' := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_commutator, hU'map, MonoidHom.map_zpowers]
    exact hUidem
  have hdU' : d' ∈ Subgroup.normalizer (U' : Set ↥X) := mem_normalizer_subgroupOf hdX hdNU
  have hdI' : d' ∈ Subgroup.normalizer (I' : Set ↥X) := mem_normalizer_subgroupOf hdX hdNI
  have hUI' : U' ≤ Subgroup.normalizer (I' : Set ↥X) := by
    intro x hx
    have := mem_normalizer_subgroupOf x.2 (hUNI x (Subgroup.mem_subgroupOf.mp hx))
    simpa using this
  have hIA5' : Nonempty (↥I' ⧸ CFSG.pCore 2 ↥I' ≃* alternatingGroup (Fin 5)) := by
    obtain ⟨e⟩ := hIA5
    let φ : ↥I' ≃* ↥I := Subgroup.subgroupOfEquivOfLe hIX
    exact ⟨(QuotientGroup.congr _ _ φ (CFSG.pCore_map_iso 2 φ)).trans e⟩
  have hT := isTripleCover_quot h hJ hdA hd1 hdc hXL
  have hθs : Group.IsSolvable θ' :=
    (solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three).1
  have hkerS : Group.IsSolvable (QuotientGroup.mk' θ').ker := by
    rw [QuotientGroup.ker_mk']
    exact hθs
  have hd3 : d' ^ 3 = 1 := Subtype.ext (h.toSec14Std.isE27.1.2 d hdA)
  have hdZ := mk_mem_center h hJ hdA hd1 hdc hXL
  have hUker : U' ≤ (QuotientGroup.mk' θ').ker := by
    rw [QuotientGroup.ker_mk']
    exact hUD'
  obtain ⟨I₁, -, hI₁p, hI₁d, hI₁U, hI₁2, hI₁A5⟩ :=
    exists_iOne (QuotientGroup.mk' θ') hT hkerS hd3 hdZ hIA5' hdI' hp (by omega) hUp'
      hUker hUI' hdU'
  refine ⟨hUp', hUD', hUd', I₁, hI₁p, hI₁d, ?_, ?_, hI₁A5⟩
  · intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro i hi
    exact ((Subgroup.mem_centralizer_iff.mp (hI₁U hi)) u hu).symm
  · rw [QuotientGroup.ker_mk'] at hI₁2
    exact hI₁2

end Transport

end CFSG.RankThree.PartTwo.Sec16.Kcd166
