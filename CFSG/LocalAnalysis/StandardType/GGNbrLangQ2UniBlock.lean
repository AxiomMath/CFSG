module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TorUniMark
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2UniLift
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniComp
import CFSG.LieType.SemisimpleCentralizers.HeldUCDMain
import CFSG.LieType.SemisimpleCentralizers.HeldCompTrivSU
import CFSG.LieType.SemisimpleCentralizers.HeldCompTrivSL
import CFSG.Timmesfeld.Orders.ClassicalLinear
import CFSG.Timmesfeld.Orders.Distinct
import CFSG.LieType.Universal.Unitary.Clause0
import CFSG.LieType.SemisimpleCentralizers.OrderThree.CenterQuot
import CFSG.RankThree.PartOne.KF.UnitaryModel
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUTypes
import CFSG.LieType.SemisimpleCentralizers.HeldUCDForm
import Mathlib.LinearAlgebra.Projection
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUnitary

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open CFSG.Open (StatedSL StatedSU StatedScalars StatedProj)
open CFSG.LieType.SemisimpleCentralizers CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.SemisimpleCentralizers.Held CFSG.LieType.SemisimpleCentralizers.HeldUCD
open Polynomial Matrix


private theorem cuq2b_isComponentOf_map_mulEquiv {G G' : Type*} [Group G] [Group G']
    (e : G ≃* G') {L K : Subgroup G} (hL : CFSG.Open.IsComponentOf L K) :
    CFSG.Open.IsComponentOf (L.map e.toMonoidHom) (K.map e.toMonoidHom) := by
  refine ⟨Subgroup.map_mono hL.1, CFSG.Open.IsSubnormal.map e.toMonoidHom hL.2.1, ?_⟩
  exact CFSG.Open.IsQuasisimple.of_mulEquiv
    (Subgroup.equivMapOfInjective L e.toMonoidHom e.injective).symm hL.2.2

private theorem cuq2b_isComponentOf_subgroupOf_top {G : Type*} [Group G] {L K : Subgroup G}
    (hL : CFSG.Open.IsComponentOf L K) : CFSG.Open.IsComponentOf (L.subgroupOf K) ⊤ := by
  refine ⟨le_top, ?_, ?_⟩
  · exact CFSG.Open.IsSubnormal.of_mathlib
      ((CFSG.Open.IsSubnormal.iff_subgroupOf hL.1).mp hL.2.1)
  · exact (CFSG.Open.IsQuasisimple.congr (Subgroup.subgroupOfEquivOfLe hL.1)).2 hL.2.2

private theorem cuq2b_component_heldGU_eq_heldSU (hSU : SUComponentsTrivial)
    {a Q : ℕ} {E : Type} [Field E] [Finite E] {τ : E ≃+* E} {hτ : ∀ x, τ (τ x) = x}
    (hcard : Nat.card E = Q ^ 2) (hτQ : ∀ x, τ x = x ^ Q)
    {J : Subgroup (GL (Fin a) E)} (hJ : CFSG.Open.IsComponentOf J (heldGU a E τ hτ)) :
    J = heldSU a E τ hτ := by
  have hle : J ≤ heldSU a E τ hτ := by
    have hperf : Group.IsPerfect ↥J := Group.isPerfect_def.mpr hJ.2.2.1
    have hcomm : ⁅J, J⁆ ≤ ⁅heldGU a E τ hτ, heldGU a E τ hτ⁆ :=
      Subgroup.commutator_mono hJ.1 hJ.1
    have hGU : ⁅heldGU a E τ hτ, heldGU a E τ hτ⁆ ≤ heldSU a E τ hτ :=
      Subgroup.commutator_le.mpr fun x hx y hy => commutatorElement_mem_heldSU hx hy
    rw [Subgroup.isPerfect_iff.mp hperf] at hcomm
    exact hcomm.trans hGU
  have hsub : CFSG.Open.IsSubnormal J (heldSU a E τ hτ) := by
    have h := CFSG.Open.IsSubnormal.inf_of_le hJ.2.1
      (inf_le_left : heldSU a E τ hτ ≤ heldGU a E τ hτ)
    change CFSG.Open.IsSubnormal (J ⊓ heldSU a E τ hτ) (heldSU a E τ hτ) at h
    rwa [inf_eq_left.mpr hle] at h
  have hcomp : CFSG.Open.IsComponentOf J (heldSU a E τ hτ) := ⟨hle, hsub, hJ.2.2⟩
  have htop : (J.subgroupOf (heldSU a E τ hτ)) = ⊤ :=
    hSU a Q E τ hτ hcard hτQ _ (cuq2b_isComponentOf_subgroupOf_top hcomp)
  exact le_antisymm hle (Subgroup.subgroupOf_eq_top.mp htop)

private theorem cuq2b_component_GL_eq_statedSL (hSL : SLComponentsTrivial)
    {b : ℕ} {E : Type} [Field E] [Finite E]
    {J : Subgroup (GL (Fin b) E)} (hJ : CFSG.Open.IsComponentOf J ⊤) :
    J = StatedSL b E := by
  have hle : J ≤ StatedSL b E := by
    have hperf : Group.IsPerfect ↥J := Group.isPerfect_def.mpr hJ.2.2.1
    have hcomm : ⁅J, J⁆ ≤ ⁅(⊤ : Subgroup (GL (Fin b) E)), ⊤⁆ :=
      Subgroup.commutator_mono hJ.1 hJ.1
    have hGL : ⁅(⊤ : Subgroup (GL (Fin b) E)), ⊤⁆ ≤ StatedSL b E :=
      Subgroup.commutator_le.mpr fun x _ y _ => commutatorElement_mem_statedSL x y
    rw [Subgroup.isPerfect_iff.mp hperf] at hcomm
    exact hcomm.trans hGL
  have hsub : CFSG.Open.IsSubnormal J (StatedSL b E) := by
    have h := CFSG.Open.IsSubnormal.inf_of_le hJ.2.1
      (le_top : StatedSL b E ≤ ⊤)
    rwa [inf_eq_left.mpr hle] at h
  have hcomp : CFSG.Open.IsComponentOf J (StatedSL b E) := ⟨hle, hsub, hJ.2.2⟩
  have htop : (J.subgroupOf (StatedSL b E)) = ⊤ :=
    hSL b E _ (cuq2b_isComponentOf_subgroupOf_top hcomp)
  exact le_antisymm hle (Subgroup.subgroupOf_eq_top.mp htop)

private theorem cuq2b_selfDual_block_iso {L : Type} [Field L] [Finite L] {n m Q : ℕ}
    {τ : L ≃+* L} {s : Matrix (Fin n) (Fin n) L} {F : Finset L[X]} {aa bb : L[X] → L[X]}
    {f : L[X]} [Fact (Irreducible f)]
    [Fact (∀ x ∈ Vf s bb F f, Matrix.mulVec (Polynomial.aeval s f) x = 0)]
    (H : PrimaryHyp τ s m F aa bb) (hQ : Nat.card L = Q ^ 2) (hτQ : ∀ x, τ x = x ^ Q)
    (hf : f ∈ F) (hPf : Pmat s bb F f ≠ 0)
    (hsa : adjM τ (Pmat s bb F f) = Pmat s bb F f) :
    ∃ (a' : ℕ) (ρE : AdjoinRoot f ≃+* AdjoinRoot f) (hρE : ∀ x, ρE (ρE x) = x),
      a' = Module.finrank (AdjoinRoot f) (Vf s bb F f) ∧
      Nat.card (AdjoinRoot f) = (Q ^ f.natDegree) ^ 2 ∧
      (∀ x, ρE x = x ^ (Q ^ f.natDegree)) ∧
      Nonempty (↥(unitaryBlock τ s bb F f) ≃* heldGU a' (AdjoinRoot f) ρE hρE) := by
  classical
  have hf0 : f ≠ 0 := (Fact.out : Irreducible f).ne_zero
  have hdiv : f ∣ starP τ m f := dvd_starP_of_self_dual H hf hPf hsa
  have hdvd : f ∣ (X ^ m - 1 : L[X]) := by
    rw [← H.hprod]
    exact Finset.dvd_prod_of_mem _ hf
  have hσσ : ∀ x, sigmaK τ m hdiv (sigmaK τ m hdiv x) = x :=
    sigmaK_sigmaK τ H.hτ H.hm hdiv hdvd
  have hσL : ∀ l : L, sigmaK τ m hdiv (algebraMap L (AdjoinRoot f) l) =
      algebraMap L (AdjoinRoot f) (τ l) := fun l => sigmaK_of τ m hdiv l
  have : Module.Finite L (AdjoinRoot f) := (H.hmon f hf).finite_adjoinRoot
  have : Finite (AdjoinRoot f) :=
    Finite.of_equiv (Fin (Module.finrank L (AdjoinRoot f)) → L)
      (Module.finBasis L (AdjoinRoot f)).equivFun.toEquiv.symm
  let σE : AdjoinRoot f ≃+* AdjoinRoot f := invEquiv (sigmaK τ m hdiv) hσσ
  obtain ⟨p, e, hp, he1, hQe, hodd, hcard, hsig⟩ :=
    sigma_eq_frobenius_pow hQ τ hτQ σE hσL hσσ
  set k := Module.finrank L (AdjoinRoot f) with hk
  have hbar_card : Nat.card (AdjoinRoot f) = p ^ (2 * (e * k)) := by
    rw [hcard, hQe, ← pow_mul]
    congr 1
    ring
  have hUFD : UnitaryFieldData p (e * k) (AdjoinRoot f) :=
    ⟨hp, Nat.mul_pos he1 hodd.pos, hbar_card⟩
  have hbar : ∀ x, hUFD.bar x = sigmaK τ m hdiv x := by
    intro x
    rw [UnitaryFieldData.bar_apply]
    have h1 := hsig x
    rw [hQe, ← pow_mul] at h1
    exact h1.symm
  have hρE : ∀ x, hUFD.bar (hUFD.bar x) = x := hUFD.bar_bar
  have hρL : ∀ l : L, hUFD.bar (algebraMap L (AdjoinRoot f) l) =
      algebraMap L (AdjoinRoot f) (τ l) := fun l => by
    rw [hbar]
    exact hσL l
  have hherm : ∀ x y : Vf s bb F f, τ (hW τ s bb F f x y) = hW τ s bb F f y x := by
    intro x y
    rw [hW_apply, hW_apply]
    exact hfm_symm τ H.hτ _ _
  have hadj : ∀ (c : AdjoinRoot f) (x y : Vf s bb F f),
      hW τ s bb F f (c • x) y = hW τ s bb F f x (hUFD.bar c • y) := by
    intro c x y
    rw [hbar]
    exact hW_smul_adj H hdiv c x y
  obtain ⟨B, hsymm, hsep, hrep⟩ :=
    exists_trace_form hUFD.bar (τ : L →+* L) hρE hρL (hW τ s bb F f) hherm hadj
      (hW_nondeg H hf hsa)
  have : Module.Finite L (Vf s bb F f) := inferInstance
  have : FiniteDimensional (AdjoinRoot f) (Vf s bb F f) :=
    Module.Finite.of_restrictScalars_finite L (AdjoinRoot f) (Vf s bb F f)
  obtain ⟨e0, he0⟩ :=
    UnitaryFieldData.exists_orthonormal_basis hUFD (B := B) (LinearMap.isSymm_def.mpr hsymm) hsep
  let ρE : AdjoinRoot f ≃+* AdjoinRoot f := invEquiv hUFD.bar hρE
  obtain ⟨φ⟩ := nonempty_mulEquiv_heldGU ρE hρE B e0 he0
  have hsub : unitaryBlock τ s bb F f = sesqUnitaryGroup B := by
    ext g
    rw [mem_sesqUnitaryGroup]
    exact unitary_trace_iff (hW τ s bb F f) B hrep g.1
  have hkf : k = f.natDegree := by
    rw [hk]
    exact ((AdjoinRoot.powerBasis (K := L) hf0).finrank).trans (AdjoinRoot.powerBasis_dim hf0)
  have hcard' : Nat.card (AdjoinRoot f) = (Q ^ f.natDegree) ^ 2 := by
    rw [hcard, hkf, mul_comm 2, pow_mul]
  have hτQ' : ∀ x, ρE x = x ^ (Q ^ f.natDegree) := by
    intro x
    change hUFD.bar x = x ^ (Q ^ f.natDegree)
    have h := hsig x
    rw [hkf] at h
    rw [hbar]
    simpa [σE, invEquiv] using h
  exact ⟨Module.finrank (AdjoinRoot f) (Vf s bb F f), ρE, hρE, rfl, hcard', hτQ',
    ⟨(MulEquiv.subgroupCongr hsub).trans φ⟩⟩

private theorem cuq2b_projMk_eq_iff {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (H : Subgroup (GL ι K)) (x y : ↥H) :
    LargeEvenProjMk H x = LargeEvenProjMk H y ↔
      ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c = (x : GL ι K)⁻¹ * (y : GL ι K) := by
  rw [LargeEvenProjMk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  exact MonoidHom.mem_range

private theorem cuq2b_ker_projMk_le_center {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] (H : Subgroup (GL ι K)) : (LargeEvenProjMk H).ker ≤ Subgroup.center ↥H := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hx' : LargeEvenProjMk H x = LargeEvenProjMk H 1 := by rw [hx, map_one]
  obtain ⟨c, hc⟩ := (cuq2b_projMk_eq_iff H x 1).mp hx'
  have hxG : (x : GL ι K) = Matrix.GeneralLinearGroup.scalar ι c⁻¹ := by
    have : (x : GL ι K)⁻¹ = Matrix.GeneralLinearGroup.scalar ι c := by simpa using hc.symm
    rw [map_inv, ← this, inv_inv]
  have hxZ : (x : GL ι K) ∈ Subgroup.center (GL ι K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c⁻¹, hxG.symm⟩
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  exact Subgroup.mem_center_iff.1 hxZ (y : GL ι K)

private theorem cuq2b_center_heldSU_eq_scalars {a mD : ℕ} {D : Type} [Field D] [Finite D]
    (hD : UnitaryFieldData 2 mD D) (ha : 2 ≤ a) (hne : ¬ (a = 3 ∧ mD = 1))
    {ρ : D ≃+* D} (hρ : ∀ x, ρ (ρ x) = x) (hρpow : ∀ x, ρ x = x ^ 2 ^ mD) :
    Subgroup.center (heldSU a D ρ hρ) =
      (StatedScalars (Fin a) D).subgroupOf (heldSU a D ρ hρ) := by
  have hcard : Nat.card D = (2 ^ mD) ^ 2 := by
    rw [hD.card, ← pow_mul, mul_comm]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP D 2 := hD.charP
  have hheld : heldSU a D ρ hρ = StatedSU a (2 ^ mD) D :=
    hct_heldSU_eq_statedSU hρpow
  rw [hheld]
  rcases Nat.lt_or_ge a 3 with ha3 | ha3
  · have ha2 : a = 2 := by omega
    subst ha2
    rw [CFSG.ComponentClassification.RankTwoClassical.center_statedSU_two_eq_bot hcard,
      CFSG.RankThree.PartOne.KFU.scalars_subgroupOf_eq_bot hcard (by norm_num)
        (Nat.coprime_iff_gcd_eq_one.mp (Nat.coprime_two_left.mpr
          (Timmesfeld.Orders.odd_pow_add_one (f := 1) (a := mD) (by norm_num) hD.one_le)))]
  · have hnq : (a, 2 ^ mD) ≠ (3, 2) := by
      intro h
      obtain ⟨h3, h2⟩ := Prod.mk.inj h
      exact hne ⟨h3, Nat.pow_right_injective (le_refl 2) h2⟩
    exact (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hcard (by omega) hnq).2

private noncomputable def cuq2b_blockGL {L : Type} [Field L] [Finite L] {n : ℕ}
    {τ : L ≃+* L} {m : ℕ} {s : Matrix (Fin n) (Fin n) L} {F : Finset L[X]}
    {aa bb : L[X] → L[X]} (Hp : PrimaryHyp τ s m F aa bb)
    (hK : ∀ g : ↥(Fset s bb F), Fact (∀ x ∈ Vf s bb F g.1, aeval s g.1 *ᵥ x = 0))
    (f : ↥(Fset s bb F)) (hBl : Bl Hp f = ⊤) :
    ↥(Bl Hp f) ≃* GL (Fin (Module.finrank (AdjoinRoot f.1) (Vf s bb F f.1)))
      (AdjoinRoot f.1) := by
  classical
  haveI : Fact (Irreducible f.1) := ⟨Hp.hirr f.1 (mem_Fset.mp f.2).1⟩
  haveI := hK
  haveI : Module.Finite L (AdjoinRoot f.1) :=
    (Hp.hmon f.1 (mem_Fset.mp f.2).1).finite_adjoinRoot
  haveI : Finite (AdjoinRoot f.1) :=
    Finite.of_equiv (Fin (Module.finrank L (AdjoinRoot f.1)) → L)
      (Module.finBasis L (AdjoinRoot f.1)).equivFun.toEquiv.symm
  haveI : Module.Finite L (Vf s bb F f.1) := inferInstance
  haveI : Module.Finite (AdjoinRoot f.1) (Vf s bb F f.1) :=
    Module.Finite.of_restrictScalars_finite L (AdjoinRoot f.1) (Vf s bb F f.1)
  haveI : Module.Free (AdjoinRoot f.1) (Vf s bb F f.1) :=
    Module.Free.of_divisionRing _ _
  exact (MulEquiv.subgroupCongr hBl).trans (Subgroup.topEquiv.trans
    (Matrix.GeneralLinearGroup.toLin'
      (Module.finBasis (AdjoinRoot f.1) (Vf s bb F f.1))).symm)

private noncomputable def cuq2b_projC {N m : ℕ} {K : Type} [Field K]
    {C : Subgroup (GL (Fin N) K)} (hCSU : C ≤ LargeEvenSUGroup (Fin N) K (2 ^ m))
    {J₀ : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ m)))}
    (hJ₀ : J₀ = (C.subgroupOf (LargeEvenSUGroup (Fin N) K (2 ^ m))).map
      (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ m)))) :
    ↥C →* ↥J₀ where
  toFun c := ⟨LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ m))
      (Subgroup.inclusion hCSU c), by
    rw [hJ₀]
    exact Subgroup.mem_map.mpr ⟨Subgroup.inclusion hCSU c,
      Subgroup.mem_subgroupOf.mpr c.2, rfl⟩⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by apply Subtype.ext; simp

private theorem cuq2b_projC_surjective {N m : ℕ} {K : Type} [Field K]
    {C : Subgroup (GL (Fin N) K)} (hCSU : C ≤ LargeEvenSUGroup (Fin N) K (2 ^ m))
    {J₀ : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ m)))}
    (hJ₀ : J₀ = (C.subgroupOf (LargeEvenSUGroup (Fin N) K (2 ^ m))).map
      (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ m)))) :
    Function.Surjective (cuq2b_projC (m := m) hCSU hJ₀) := by
  rintro ⟨j, hj⟩
  have hj' : j ∈ (C.subgroupOf (LargeEvenSUGroup (Fin N) K (2 ^ m))).map
      (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ m))) := by
    rw [← hJ₀]; exact hj
  obtain ⟨y, hy, hyj⟩ := Subgroup.mem_map.mp hj'
  refine ⟨⟨(y : GL (Fin N) K), Subgroup.mem_subgroupOf.mp hy⟩, ?_⟩
  apply Subtype.ext
  change LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ m))
    (Subgroup.inclusion hCSU ⟨(y : GL (Fin N) K), Subgroup.mem_subgroupOf.mp hy⟩) = j
  have hpc : Subgroup.inclusion hCSU ⟨(y : GL (Fin N) K), Subgroup.mem_subgroupOf.mp hy⟩ = y :=
    Subtype.ext rfl
  rw [hpc]
  exact hyj

private theorem cuq2b_projC_ker {N m : ℕ} {K : Type} [Field K]
    {C : Subgroup (GL (Fin N) K)} (hCSU : C ≤ LargeEvenSUGroup (Fin N) K (2 ^ m))
    {J₀ : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ m)))}
    (hJ₀ : J₀ = (C.subgroupOf (LargeEvenSUGroup (Fin N) K (2 ^ m))).map
      (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ m)))) :
    (cuq2b_projC (m := m) hCSU hJ₀).ker ≤ Subgroup.center ↥C := by
  intro c hc
  rw [MonoidHom.mem_ker] at hc
  have hc' : Subgroup.inclusion hCSU c ∈
      (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ m))).ker := by
    rw [MonoidHom.mem_ker]
    simpa [cuq2b_projC] using congrArg Subtype.val hc
  have hcen := cuq2b_ker_projMk_le_center (LargeEvenSUGroup (Fin N) K (2 ^ m)) hc'
  rw [Subgroup.mem_center_iff] at hcen ⊢
  intro d
  apply Subtype.ext
  show (Subgroup.inclusion hCSU d : GL (Fin N) K) *
      (Subgroup.inclusion hCSU c : GL (Fin N) K) =
    (Subgroup.inclusion hCSU c : GL (Fin N) K) *
      (Subgroup.inclusion hCSU d : GL (Fin N) K)
  exact congrArg Subtype.val (hcen (Subgroup.inclusion hCSU d))

private noncomputable def cuq2b_ecent {N m : ℕ} {K : Type} [Field K]
    {C : Subgroup (GL (Fin N) K)} (hCperf : Group.IsPerfect ↥C)
    (hCSU : C ≤ LargeEvenSUGroup (Fin N) K (2 ^ m))
    {J₀ : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ m)))}
    (hJ₀ : J₀ = (C.subgroupOf (LargeEvenSUGroup (Fin N) K (2 ^ m))).map
      (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ m)))) :
    ↥C ⧸ Subgroup.center ↥C ≃* ↥J₀ ⧸ Subgroup.center ↥J₀ := by
  let πC := cuq2b_projC (m := m) hCSU hJ₀
  let φq : ↥C →* ↥J₀ ⧸ Subgroup.center ↥J₀ :=
    (QuotientGroup.mk' (Subgroup.center ↥J₀)).comp πC
  have hφqsurj : Function.Surjective φq :=
    (QuotientGroup.mk'_surjective (Subgroup.center ↥J₀)).comp
      (cuq2b_projC_surjective (m := m) hCSU hJ₀)
  have hcomap : (Subgroup.center ↥J₀).comap πC = Subgroup.center ↥C :=
    CFSG.LocalCores.comap_center_eq_of_perfect hCperf πC
      (cuq2b_projC_surjective (m := m) hCSU hJ₀) (cuq2b_projC_ker (m := m) hCSU hJ₀)
  have hφqker : Subgroup.center ↥C = φq.ker := by
    dsimp only [φq]
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hcomap]
  exact QuotientGroup.liftEquiv (Subgroup.center ↥C) (φ := φq) hφqsurj hφqker

private theorem cuq2b_ecent_mk {N m : ℕ} {K : Type} [Field K]
    {C : Subgroup (GL (Fin N) K)} (hCperf : Group.IsPerfect ↥C)
    (hCSU : C ≤ LargeEvenSUGroup (Fin N) K (2 ^ m))
    {J₀ : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ m)))}
    (hJ₀ : J₀ = (C.subgroupOf (LargeEvenSUGroup (Fin N) K (2 ^ m))).map
      (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ m)))) (c : ↥C) :
    cuq2b_ecent hCperf hCSU hJ₀ (QuotientGroup.mk c) =
      QuotientGroup.mk (cuq2b_projC (m := m) hCSU hJ₀ c) := by
  let πC := cuq2b_projC (m := m) hCSU hJ₀
  let φq : ↥C →* ↥J₀ ⧸ Subgroup.center ↥J₀ :=
    (QuotientGroup.mk' (Subgroup.center ↥J₀)).comp πC
  have hφqsurj : Function.Surjective φq :=
    (QuotientGroup.mk'_surjective (Subgroup.center ↥J₀)).comp
      (cuq2b_projC_surjective (m := m) hCSU hJ₀)
  have hcomap : (Subgroup.center ↥J₀).comap πC = Subgroup.center ↥C :=
    CFSG.LocalCores.comap_center_eq_of_perfect hCperf πC
      (cuq2b_projC_surjective (m := m) hCSU hJ₀) (cuq2b_projC_ker (m := m) hCSU hJ₀)
  have hφqker : Subgroup.center ↥C = φq.ker := by
    dsimp only [φq]
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hcomap]
  exact QuotientGroup.liftEquiv_mk (Subgroup.center ↥C) (φ := φq) hφqsurj hφqker c

private theorem cuq2bt_finrank_le_of_semilinear {K : Type} [Field K] {V W : Type}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    {σ : K ≃+* K} (f : V → W)
    (hadd : ∀ x y : V, f (x + y) = f x + f y)
    (hsmul : ∀ (c : K) (x : V), f (c • x) = σ c • f x)
    (hinj : Function.Injective f) : Module.finrank K V ≤ Module.finrank K W := by
  classical
  have hf0 : f 0 = 0 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact (add_left_cancel (show f 0 + 0 = f 0 + f 0 by rw [add_zero]; exact h)).symm
  set b := Module.finBasis K V with hb
  have key : ∀ (t : Finset (Fin (Module.finrank K V))) (g : Fin (Module.finrank K V) → K),
      f (∑ j ∈ t, (σ.symm (g j)) • b j) = ∑ j ∈ t, g j • f (b j) := by
    intro t g
    induction t using Finset.induction_on with
    | empty => simpa using hf0
    | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih, hsmul,
        σ.apply_symm_apply]
  have hli : LinearIndependent K (fun i => f (b i)) := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    have h1 : f (∑ j ∈ s, (σ.symm (g j)) • b j) = 0 := by
      rw [key s g, hg]
    have h3 : ∑ j ∈ s, (σ.symm (g j)) • b j = 0 := by
      apply hinj
      rw [h1, hf0]
    have hci : σ.symm (g i) = 0 := linearIndependent_iff'.mp b.linearIndependent s
      (fun j => σ.symm (g j)) h3 i hi
    rw [← σ.apply_symm_apply (g i), hci, map_zero]
  have hcard := hli.fintype_card_le_finrank
  simpa using hcard

private theorem cuq2bt_hfm_sub_left {L : Type} [Field L] {n : ℕ} (τ : L ≃+* L)
    (x x' : Fin n → L) (y : Fin n → L) :
    hfm τ (x - x') y = hfm τ x y - hfm τ x' y := by
  have h := hfm_add_left τ (x - x') x' y
  rw [sub_add_cancel] at h
  exact eq_sub_iff_add_eq.mpr h.symm

private theorem cuq2bt_hfm_injective {L : Type} [Field L] {n : ℕ} {τ : L ≃+* L} {m : ℕ}
    {s : Matrix (Fin n) (Fin n) L} {F : Finset L[X]} {a b : L[X] → L[X]}
    (H : PrimaryHyp τ s m F a b) (f : ↥(Fset s b F)) :
    Function.Injective (fun x : ↥(Vf s b F f.1) =>
      (⟨⟨fun y : ↥(Vf s b F (piI H f).1) => hfm τ (x : Fin n → L) (y : Fin n → L),
        fun y y' => by simp only [Submodule.coe_add, hfm_add_right]⟩,
        fun c y => by simp only [Submodule.coe_smul, hfm_smul_right, smul_eq_mul, RingHom.id_apply]⟩ :
      ↥(Vf s b F (piI H f).1) →ₗ[L] L)) := by
  intro x x' hxx'
  have hval : ∀ y : ↥(Vf s b F (piI H f).1),
      hfm τ (x : Fin n → L) (y : Fin n → L) = hfm τ (x' : Fin n → L) (y : Fin n → L) :=
    fun y => LinearMap.congr_fun hxx' y
  have hzero : ((x - x' : ↥(Vf s b F f.1)) : Fin n → L) = 0 := by
    apply eq_zero_of_hfm_piI H f (Submodule.sub_mem _ x.2 x'.2)
    intro q hq
    rw [hfm_comm_tau H.hτ, cuq2bt_hfm_sub_left τ, hval ⟨q, hq⟩, sub_self, map_zero]
  have hsub : (x - x' : ↥(Vf s b F f.1)) = 0 := Subtype.ext hzero
  exact sub_eq_zero.mp hsub

private theorem cuq2bt_finrank_Vf_eq_piI {L : Type} [Field L] {n : ℕ} {τ : L ≃+* L} {m : ℕ}
    {s : Matrix (Fin n) (Fin n) L} {F : Finset L[X]} {a b : L[X] → L[X]}
    (H : PrimaryHyp τ s m F a b) (f : ↥(Fset s b F)) :
    Module.finrank L (Vf s b F f.1) = Module.finrank L (Vf s b F (piI H f).1) := by
  refine le_antisymm ?_ ?_
  · have h := cuq2bt_finrank_le_of_semilinear (σ := τ)
      (V := ↥(Vf s b F f.1))
      (W := ↥(Vf s b F (piI H f).1) →ₗ[L] L)
      (f := fun x => ⟨⟨fun y => hfm τ (x : Fin n → L) (y : Fin n → L),
        fun y y' => by simp only [Submodule.coe_add, hfm_add_right]⟩,
        fun c y => by simp only [Submodule.coe_smul, hfm_smul_right, smul_eq_mul, RingHom.id_apply]⟩)
      (fun x x' => by
        ext y
        show hfm τ ((x + x' : ↥(Vf s b F f.1)) : Fin n → L) (y : Fin n → L) =
          hfm τ (x : Fin n → L) (y : Fin n → L) + hfm τ (x' : Fin n → L) (y : Fin n → L)
        rw [Submodule.coe_add, hfm_add_left])
      (fun c x => by
        ext y
        show hfm τ ((c • x : ↥(Vf s b F f.1)) : Fin n → L) (y : Fin n → L) =
          τ c * hfm τ (x : Fin n → L) (y : Fin n → L)
        rw [Submodule.coe_smul, hfm_smul_left])
      (cuq2bt_hfm_injective H f)
    rwa [Subspace.dual_finrank_eq] at h
  · have h := cuq2bt_finrank_le_of_semilinear (σ := τ)
      (V := ↥(Vf s b F (piI H f).1))
      (W := ↥(Vf s b F (piI H (piI H f)).1) →ₗ[L] L)
      (f := fun x => ⟨⟨fun y => hfm τ (x : Fin n → L) (y : Fin n → L),
        fun y y' => by simp only [Submodule.coe_add, hfm_add_right]⟩,
        fun c y => by simp only [Submodule.coe_smul, hfm_smul_right, smul_eq_mul, RingHom.id_apply]⟩)
      (fun x x' => by
        ext y
        show hfm τ ((x + x' : ↥(Vf s b F (piI H f).1)) : Fin n → L) (y : Fin n → L) =
          hfm τ (x : Fin n → L) (y : Fin n → L) + hfm τ (x' : Fin n → L) (y : Fin n → L)
        rw [Submodule.coe_add, hfm_add_left])
      (fun c x => by
        ext y
        show hfm τ ((c • x : ↥(Vf s b F (piI H f).1)) : Fin n → L) (y : Fin n → L) =
          τ c * hfm τ (x : Fin n → L) (y : Fin n → L)
        rw [Submodule.coe_smul, hfm_smul_left])
      (cuq2bt_hfm_injective H (piI H f))
    rw [Subspace.dual_finrank_eq] at h
    rwa [show piI H (piI H f) = f from piI_piI H f] at h

private theorem cuq2bt_injective_su2_su3 {q : ℕ} (hq : 1 ≤ q) {K : Type} [Field K] :
    ∃ β : ↥(StatedSU 2 q K) →* ↥(StatedSU 3 q K), Function.Injective β := by
  let β : ↥(StatedSU 2 q K) →* ↥(StatedSU 3 q K) :=
    (CFSG.RankThree.SubgroupLists.blockGL3.comp (StatedSU 2 q K).subtype).codRestrict
      (StatedSU 3 q K) fun A =>
        CFSG.RankThree.SubgroupLists.map_blockGL3_statedSU_le hq ⟨A, A.2, rfl⟩
  refine ⟨β, ?_⟩
  rw [injective_iff_map_eq_one]
  intro A hA
  have h1 : CFSG.RankThree.SubgroupLists.blockGL3 (A : GL (Fin 2) K) = 1 :=
    congrArg Subtype.val hA
  exact Subtype.ext (CFSG.RankThree.SubgroupLists.blockGL3_eq_one_of_scalar
    (by rw [h1]; exact one_mem _))

theorem q2Uni_block {N m : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ m) ^ 2)
    (τ : K ≃+* K) (hτ : ∀ x, τ (τ x) = x) (hτQ : ∀ x, τ x = x ^ 2 ^ m)
    (s : GL (Fin N) K) (hs : s ∈ Held.heldGU N K τ hτ) (hso : Odd (orderOf s))
    (C : Subgroup (GL (Fin N) K))
    (hC : CFSG.Assembly.IsComponentOf C
      (Subgroup.centralizer ({s} : Set (GL (Fin N) K)) ⊓ Held.heldGU N K τ hτ))
    (hCSU : C ≤ LargeEvenSUGroup (Fin N) K (2 ^ m))
    (J₀ : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ m))))
    (hJ₀ : J₀ = (C.subgroupOf (LargeEvenSUGroup (Fin N) K (2 ^ m))).map
      (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ m))))
    {d m' : ℕ} {E : Type} [Field E] (hE : UnitaryFieldData 2 m' E) (hd : 3 ≤ d)
    (hdm : ¬ (d = 3 ∧ m' = 1))
    (hJE : Nonempty (↥J₀ ⧸ Subgroup.center ↥J₀ ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin d) E (2 ^ m')))) :
    ∃ (a mD : ℕ) (D : Type) (_ : Field D) (hD : UnitaryFieldData 2 mD D)
      (ψ : ↥J₀ ⧸ Subgroup.center ↥J₀ ≃* LargeEvenProj (LargeEvenSUGroup (Fin a) D (2 ^ mD)))
      (π : ↥(Subgroup.centralizer ({s} : Set (GL (Fin N) K)) ⊓ Held.heldGU N K τ hτ) →*
        ↥(TableB.unitGroup (ι := Fin a) hD.bar)),
      ∀ (h : ↥(Subgroup.centralizer ({s} : Set (GL (Fin N) K)) ⊓ Held.heldGU N K τ hτ))
        (hN : (h : GL (Fin N) K) ∈
          Subgroup.normalizer (LargeEvenSUGroup (Fin N) K (2 ^ m) : Set (GL (Fin N) K)))
        (j j' : ↥J₀),
        (j' : LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ m))) =
            TableB.projConj (LargeEvenSUGroup (Fin N) K (2 ^ m)) ⟨(h : GL (Fin N) K), hN⟩
              (j : LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ m))) →
          CFSG.HardMathSupport.C14Cl.uniConj hD a (π h) (ψ (QuotientGroup.mk j)) =
            ψ (QuotientGroup.mk j') := by
  have _ : ¬ (d = 3 ∧ m' = 1) := hdm
  classical
  have hmpos : 0 < m := by
    by_contra h
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos h
    rw [hm0] at hK
    norm_num at hK
    haveI : Fintype K := Fintype.ofFinite K
    have : 1 < Nat.card K := by rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
    omega
  have hUFD : UnitaryFieldData 2 m K :=
    CFSG.ComponentClassification.RankTwoClassical.unitaryFieldData_of_card hK hmpos
  haveI : CharP K 2 := hUFD.charP
  have hord : (orderOf s : K) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff K 2] at h
    exact (Nat.not_even_iff_odd.mpr hso) (even_iff_two_dvd.mpr h)
  have hM : CFSG.Open.IsComponentOf C
      (Subgroup.centralizer ({s} : Set (GL (Fin N) K)) ⊓ heldGU N K τ hτ) :=
    (CFSG.Assembly.isComponentOf_iff_open).1 hC
  have hm0 : 0 < orderOf s := orderOf_pos s
  have hsm : (s : Matrix (Fin N) (Fin N) K) ^ orderOf s = 1 := by
    rw [← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
  have hs' : adjM τ (s : Matrix (Fin N) (Fin N) K) * (s : Matrix (Fin N) (Fin N) K) = 1 :=
    Held.mem_heldGU.mp hs
  set F : Finset K[X] := factorsOf (L := K) (orderOf s) with hF
  have hirr : ∀ f ∈ F, Irreducible f := fun f hf => factorsOf_irreducible hf
  have hmon : ∀ f ∈ F, Monic f := fun f hf => factorsOf_monic hf
  have hprod : ∏ f ∈ F, f = X ^ orderOf s - 1 := prod_factorsOf hord hm0
  have hcop : ∀ f ∈ F, ∃ u v : K[X], u * f + v * gcF F f = 1 :=
    fun f hf => isCoprime_gcF hirr hmon hf
  choose! aa bb hab using hcop
  let Hp : PrimaryHyp τ (s : Matrix (Fin N) (Fin N) K) (orderOf s) F aa bb :=
    ⟨hτ, hm0, hirr, hmon, hprod, hsm, hs', hab⟩
  haveI hKfact : ∀ f : ↥(Fset (s : Matrix (Fin N) (Fin N) K) bb F),
      Fact (∀ x ∈ Vf (s : Matrix (Fin N) (Fin N) K) bb F f.1,
        aeval (s : Matrix (Fin N) (Fin N) K) f.1 *ᵥ x = 0) :=
    fun f => ⟨fun x hx => aeval_factor_mulVec_eq_zero Hp (mem_Fset.mp f.2).1 hx⟩
  let H0 : Subgroup (GL (Fin N) K) :=
    Subgroup.centralizer ({s} : Set (GL (Fin N) K)) ⊓ heldGU N K τ hτ
  let Hact : Activ Hp → Type := fun f => ↥(Bl Hp f.1)
  haveI hHfin : ∀ f : Activ Hp, Finite (Hact f) := fun f => finite_Bl Hp f.1
  let Φ : ↥H0 ≃* (∀ f : Activ Hp, Hact f) :=
    (centralizerEquivGlin hτ s).trans (glinEquivBlocks Hp)
  let Ctop : Subgroup ↥H0 := C.subgroupOf H0
  have hCtop : CFSG.Open.IsComponentOf Ctop ⊤ := cuq2b_isComponentOf_subgroupOf_top hM
  let C' : Subgroup (∀ f : Activ Hp, Hact f) := Ctop.map Φ.toMonoidHom
  have hC' : CFSG.Open.IsComponentOf C' ⊤ := by
    have h := isComponentOf_map_of_injective Φ.toMonoidHom Φ.injective
      ((CFSG.Assembly.isComponentOf_iff_open).2 hCtop)
    rw [← MonoidHom.range_eq_map] at h
    exact (CFSG.Assembly.isComponentOf_iff_open).1 (by simpa [C'] using h)
  obtain ⟨f0, hf0⟩ := exists_factor_of_isComponentOf_top hC'
  let Fsub : Subgroup (∀ f : Activ Hp, Hact f) := factorSub f0
  let ρF : ↥Fsub ≃* Hact f0 :=
    { toFun := fun w => w.1 f0
      invFun := fun x => ⟨MonoidHom.mulSingle Hact f0 x, by
        dsimp only [Fsub]
        rw [mem_factorSub]
        intro j hj
        rw [MonoidHom.mulSingle_apply]
        simp [hj]⟩
      left_inv := by
        intro w
        apply Subtype.ext
        funext j
        by_cases hj : j = f0
        · subst hj; simp [MonoidHom.mulSingle_apply]
        · simp [MonoidHom.mulSingle_apply, hj, mem_factorSub.mp w.2 j hj]
      right_inv := by intro x; simp [MonoidHom.mulSingle_apply]
      map_mul' := fun x y => rfl }
  have hf0F : f0.1.1 ∈ F := (mem_Fset.mp f0.1.2).1
  have hPf : Pmat (s : Matrix (Fin N) (Fin N) K) bb F f0.1.1 ≠ 0 :=
    (mem_Fset.mp f0.1.2).2
  have hC'F : CFSG.Open.IsComponentOf (C'.subgroupOf Fsub) ⊤ := by
    apply CFSG.ComponentClassification.LocalComponents.of_overgroup hC'
    simpa [Fsub] using hf0
  let C'' : Subgroup (Hact f0) := (C'.subgroupOf Fsub).map ρF.toMonoidHom
  have hC'' : CFSG.Open.IsComponentOf C'' ⊤ := by
    have h := isComponentOf_map_of_injective ρF.toMonoidHom ρF.injective
      ((CFSG.Assembly.isComponentOf_iff_open).2 hC'F)
    rw [Subgroup.map_top, MonoidHom.range_eq_top.mpr ρF.surjective] at h
    exact (CFSG.Assembly.isComponentOf_iff_open).1 (by simpa [C''] using h)
  let πblock : ↥H0 →* Hact f0 := (Pi.evalMonoidHom Hact f0).comp Φ.toMonoidHom
  let eCtop : ↥C ≃* ↥Ctop := (Subgroup.subgroupOfEquivOfLe hM.1).symm
  let eC' : ↥Ctop ≃* ↥C' := Subgroup.equivMapOfInjective Ctop Φ.toMonoidHom Φ.injective
  let eM2 : ↥C' ≃* ↥(C'.subgroupOf Fsub) := (Subgroup.subgroupOfEquivOfLe hf0).symm
  let eM3 : ↥(C'.subgroupOf Fsub) ≃* ↥C'' :=
    Subgroup.equivMapOfInjective _ ρF.toMonoidHom ρF.injective
  let eM : ↥C ≃* ↥C'' := eCtop.trans (eC'.trans (eM2.trans eM3))
  have heM_apply : ∀ c : ↥C, ((eM c : ↥C'') : Hact f0) = πblock ⟨c.1, hM.1 c.2⟩ := by
    intro c
    rfl
  by_cases hself : piI Hp f0.1 = f0.1
  · have hselfA : adjM τ (Pmat (s : Matrix (Fin N) (Fin N) K) bb F f0.1.1) =
        Pmat (s : Matrix (Fin N) (Fin N) K) bb F f0.1.1 := by
      have h := adjM_piI Hp f0.1
      rw [hself] at h
      simpa using h
    haveI : Fact (Irreducible f0.1.1) := ⟨hirr f0.1.1 hf0F⟩
    haveI : Fact (∀ x ∈ Vf (s : Matrix (Fin N) (Fin N) K) bb F f0.1.1,
        aeval (s : Matrix (Fin N) (Fin N) K) f0.1.1 *ᵥ x = 0) :=
      ⟨fun x hx => aeval_factor_mulVec_eq_zero Hp hf0F hx⟩
    obtain ⟨a', ρE, hρE, _, hcardE, hτQ', ⟨φ0⟩⟩ :=
      cuq2b_selfDual_block_iso Hp hK hτQ hf0F hPf hselfA
    have hBl : Bl Hp f0.1 = unitaryBlock τ (s : Matrix (Fin N) (Fin N) K) bb F f0.1.1 :=
      Bl_of_selfDual Hp hself
    let φU : ↥(Bl Hp f0.1) ≃* heldGU a' (AdjoinRoot f0.1.1) ρE hρE :=
      (MulEquiv.subgroupCongr hBl).trans φ0
    let J : Subgroup ↥(heldGU a' (AdjoinRoot f0.1.1) ρE hρE) := C''.map φU.toMonoidHom
    have hJcomp : CFSG.Open.IsComponentOf J ⊤ := by
      have h := isComponentOf_map_of_injective φU.toMonoidHom φU.injective
        ((CFSG.Assembly.isComponentOf_iff_open).2 hC'')
      rw [Subgroup.map_top, MonoidHom.range_eq_top.mpr φU.surjective] at h
      exact (CFSG.Assembly.isComponentOf_iff_open).1 (by simpa [J] using h)
    have hJmapcomp : CFSG.Open.IsComponentOf
        (J.map (heldGU a' (AdjoinRoot f0.1.1) ρE hρE).subtype)
        (heldGU a' (AdjoinRoot f0.1.1) ρE hρE) := by
      have h := isComponentOf_map_of_injective (heldGU a' (AdjoinRoot f0.1.1) ρE hρE).subtype
        (heldGU a' (AdjoinRoot f0.1.1) ρE hρE).subtype_injective
        ((CFSG.Assembly.isComponentOf_iff_open).2 hJcomp)
      rw [← MonoidHom.range_eq_map] at h
      exact (CFSG.Assembly.isComponentOf_iff_open).1 (by simpa using h)
    have hJeqGL : J.map (heldGU a' (AdjoinRoot f0.1.1) ρE hρE).subtype =
        heldSU a' (AdjoinRoot f0.1.1) ρE hρE :=
      cuq2b_component_heldGU_eq_heldSU SUComponentsTrivial_holds
        (Q := (2 ^ m) ^ f0.1.1.natDegree) hcardE hτQ' hJmapcomp
    let eJ : ↥J ≃* ↥(heldSU a' (AdjoinRoot f0.1.1) ρE hρE) :=
      (Subgroup.equivMapOfInjective J (heldGU a' (AdjoinRoot f0.1.1) ρE hρE).subtype
        (heldGU a' (AdjoinRoot f0.1.1) ρE hρE).subtype_injective).trans
        (MulEquiv.subgroupCongr hJeqGL)
    let eC : ↥C ≃* ↥(heldSU a' (AdjoinRoot f0.1.1) ρE hρE) :=
      eM.trans ((Subgroup.equivMapOfInjective C'' φU.toMonoidHom φU.injective).trans eJ)
    let πGU : ↥H0 →* ↥(heldGU a' (AdjoinRoot f0.1.1) ρE hρE) :=
      φU.toMonoidHom.comp πblock
    let D : Type := AdjoinRoot f0.1.1
    let mD : ℕ := m * f0.1.1.natDegree
    have hcardD : Nat.card D = 2 ^ (2 * mD) := by
      dsimp only [D, mD]
      rw [hcardE, ← pow_mul, ← pow_mul]
      congr 1
      ring
    have hfdeg : 0 < f0.1.1.natDegree := (hirr f0.1.1 hf0F).natDegree_pos
    have hD : UnitaryFieldData 2 mD D :=
      ⟨Nat.prime_two, Nat.mul_pos hmpos hfdeg, hcardD⟩
    have hρbar : ∀ x : D, ρE x = hD.bar x := by
      intro x
      rw [hτQ', hD.bar_apply]
      dsimp only [mD]
      rw [pow_mul]
    have hEqGU : heldGU a' D ρE hρE = TableB.unitGroup (ι := Fin a') hD.bar := by
      ext A
      rw [Held.mem_heldGU, TableB.mem_unitGroup]
      have hmap : (A : Matrix (Fin a') (Fin a') D).map ρE =
          (A : Matrix (Fin a') (Fin a') D).map hD.bar := by
        ext i j
        simp only [Matrix.map_apply, hρbar]
      rw [hmap]
    let eGU : ↥(heldGU a' D ρE hρE) ≃* ↥(TableB.unitGroup (ι := Fin a') hD.bar) :=
      MulEquiv.subgroupCongr hEqGU
    let π : ↥H0 →* ↥(TableB.unitGroup (ι := Fin a') hD.bar) :=
      eGU.toMonoidHom.comp πGU
    have hτQmD : ∀ x, ρE x = x ^ 2 ^ mD := by
      intro x
      rw [hτQ']
      dsimp only [mD]
      rw [pow_mul]
    have hSUeq : heldSU a' D ρE hρE = StatedSU a' (2 ^ mD) D :=
      hct_heldSU_eq_statedSU hτQmD
    have ha2 : 2 ≤ a' := by
      by_contra hlt
      have hle1 : a' ≤ 1 := by omega
      exact absurd hC.2.2 (not_isQuasisimple_of_mulEquiv eC fun x y =>
        Subtype.ext (mul_comm_GL_of_le_one hle1 (x : GL (Fin a') D) (y : GL (Fin a') D)))
    have hne : ¬ (a' = 3 ∧ mD = 1) := by
      rintro ⟨ha3, hmD1⟩
      have hcardD4 : Nat.card D = (2 ^ 1) ^ 2 := by
        rw [hD.card, hmD1]
        norm_num
      haveI : Group.IsSolvable ↥(StatedSU a' (2 ^ mD) D) := by
        rw [ha3, hmD1]
        exact CFSG.Quasithin.isSolvable_statedSU_one hcardD4
      haveI : Group.IsSolvable ↥(heldSU a' D ρE hρE) := by
        rw [hSUeq]
        infer_instance
      have hsolvC : Group.IsSolvable ↥C :=
        Group.isSolvable_of_isSolvable_injective (f := eC.toMonoidHom) eC.injective
      haveI : Nontrivial ↥C := by
        haveI : Nontrivial (↥C ⧸ Subgroup.center ↥C) := hC.2.2.2.toNontrivial
        have hne_top : Subgroup.center ↥C ≠ ⊤ := QuotientGroup.nontrivial_iff.mp inferInstance
        by_contra hsub
        haveI : Subsingleton ↥C := not_nontrivial_iff_subsingleton.mp hsub
        exact hne_top (by
          ext x
          constructor
          · intro _; trivial
          · intro _; rw [Subgroup.mem_center_iff]; intro y; exact Subsingleton.elim _ _)
      haveI : Group.IsPerfect ↥C := Group.isPerfect_def.mpr hC.2.2.1
      exact (Group.IsPerfect.not_isSolvable _ hsolvC).elim
    have hcenter : Subgroup.center (heldSU a' D ρE hρE) =
        (StatedScalars (Fin a') D).subgroupOf (heldSU a' D ρE hρE) :=
      cuq2b_center_heldSU_eq_scalars hD ha2 hne hρE hτQmD
    have hcenterSU : Subgroup.center (StatedSU a' (2 ^ mD) D) =
        (StatedScalars (Fin a') D).subgroupOf (StatedSU a' (2 ^ mD) D) := by
      have h := hcenter
      rw [hSUeq] at h
      exact h
    let eSU : ↥(heldSU a' D ρE hρE) ≃* ↥(StatedSU a' (2 ^ mD) D) :=
      MulEquiv.subgroupCongr hSUeq
    let eCZ : ↥C ⧸ Subgroup.center ↥C ≃*
        ↥(heldSU a' D ρE hρE) ⧸ Subgroup.center ↥(heldSU a' D ρE hρE) :=
      QuotientGroup.congr _ _ eC (Subgroup.map_center_eq eC)
    let eProj : ↥(heldSU a' D ρE hρE) ⧸ Subgroup.center ↥(heldSU a' D ρE hρE) ≃*
        StatedProj (StatedSU a' (2 ^ mD) D) :=
      (QuotientGroup.congr _ _ eSU (Subgroup.map_center_eq eSU)).trans
        (QuotientGroup.quotientMulEquivOfEq hcenterSU)
    have hCperf : Group.IsPerfect ↥C := Group.isPerfect_def.mpr hC.2.2.1
    let πC : ↥C →* ↥J₀ := cuq2b_projC (m := m) hCSU hJ₀
    let ecent : ↥C ⧸ Subgroup.center ↥C ≃* ↥J₀ ⧸ Subgroup.center ↥J₀ :=
      cuq2b_ecent hCperf hCSU hJ₀
    have hecent_mk : ∀ a : ↥C, ecent (QuotientGroup.mk a) = QuotientGroup.mk (πC a) :=
      fun a => cuq2b_ecent_mk hCperf hCSU hJ₀ a
    let ψ : ↥J₀ ⧸ Subgroup.center ↥J₀ ≃*
        LargeEvenProj (LargeEvenSUGroup (Fin a') D (2 ^ mD)) :=
      ecent.symm.trans (eCZ.trans eProj)
    refine ⟨a', mD, D, inferInstance, hD, ψ, π, ?_⟩
    intro h hN j j' hj'
    have hSUleN : (heldGU a' D ρE hρE) ≤
        Subgroup.normalizer (heldSU a' D ρE hρE : Set (GL (Fin a') D)) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        exact CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.heldSU_normal_in_heldGU
          hρE g hg x hx
      · intro hx
        have h := CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.heldSU_normal_in_heldGU
          hρE g⁻¹ (inv_mem hg) (g * x * g⁻¹) hx
        simpa [mul_assoc] using h
    have hJeq : J = (heldSU a' D ρE hρE).subgroupOf (heldGU a' D ρE hρE) := by
      ext x
      constructor
      · intro hx
        rw [Subgroup.mem_subgroupOf]
        rw [← hJeqGL]
        exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      · intro hx
        rw [Subgroup.mem_subgroupOf] at hx
        rw [← hJeqGL] at hx
        obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
        have hxy : y = x := (heldGU a' D ρE hρE).subtype_injective hyx
        simpa [hxy] using hy
    have hJnormal : J.Normal := by
      rw [hJeq]
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer
        (inf_le_left : heldSU a' D ρE hρE ≤ heldGU a' D ρE hρE)).mpr hSUleN
    have hC''eq : C'' = J.comap φU.toMonoidHom := by
      ext x
      constructor
      · intro hx
        exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      · intro hx
        obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
        have : y = x := φU.injective hyx
        simpa [this] using hy
    have hC''normal : C''.Normal := by
      rw [hC''eq]
      exact hJnormal.comap φU.toMonoidHom
    have hC'_eq : C' = Fsub ⊓ (C''.comap (Pi.evalMonoidHom Hact f0)) := by
      ext w
      constructor
      · intro hw
        refine ⟨hf0 hw, ?_⟩
        change (Pi.evalMonoidHom Hact f0) w ∈ C''
        rw [show (Pi.evalMonoidHom Hact f0) w = ρF ⟨w, hf0 hw⟩ from rfl]
        exact Subgroup.mem_map.mpr ⟨⟨w, hf0 hw⟩, hw, rfl⟩
      · rintro ⟨hwF, hwC''⟩
        have hwC''' : (Pi.evalMonoidHom Hact f0) w ∈ C'' := hwC''
        obtain ⟨z, hz, hzρ⟩ := Subgroup.mem_map.mp hwC'''
        have hzF : (z : ↥Fsub) = ⟨w, hwF⟩ := by
          exact ρF.injective hzρ
        have hzC' : ((z : ↥Fsub) : ∀ f : Activ Hp, Hact f) ∈ C' :=
          Subgroup.mem_subgroupOf.mp hz
        simpa [hzF] using hzC'
    have hCtop_iff : ∀ x : ↥H0, x ∈ Ctop ↔ Φ x ∈ C' := by
      intro x
      constructor
      · intro hx
        exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      · intro hx
        obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
        have : y = x := Φ.injective hyx
        simpa [this] using hy
    have hCnormal : ∀ (h : ↥H0) (c : ↥C),
        h * ⟨c.1, hM.1 c.2⟩ * h⁻¹ ∈ Ctop := by
      intro h c
      rw [hCtop_iff]
      have hc0 : Φ ⟨c.1, hM.1 c.2⟩ ∈ C' := Subgroup.mem_map_of_mem _ c.2
      have hfac : Φ (h * ⟨c.1, hM.1 c.2⟩ * h⁻¹) ∈ Fsub := by
        rw [map_mul, map_mul, map_inv]
        rw [mem_factorSub]
        intro g hg
        have hc1 : Φ ⟨c.1, hM.1 c.2⟩ g = 1 :=
          mem_factorSub.mp (hf0 hc0) g hg
        rw [Pi.mul_apply, Pi.mul_apply, Pi.inv_apply, hc1, mul_one]
        exact mul_inv_cancel _
      have hπcC'' : πblock ⟨c.1, hM.1 c.2⟩ ∈ C'' :=
        Subgroup.mem_map.mpr ⟨⟨Φ ⟨c.1, hM.1 c.2⟩, hf0 hc0⟩, hc0, rfl⟩
      have hmem : Φ (h * ⟨c.1, hM.1 c.2⟩ * h⁻¹) ∈
          Fsub ⊓ (C''.comap (Pi.evalMonoidHom Hact f0)) := by
        refine ⟨hfac, ?_⟩
        refine (Subgroup.mem_comap).mpr ?_
        have hz : (Pi.evalMonoidHom Hact f0) (Φ (h * ⟨c.1, hM.1 c.2⟩ * h⁻¹)) =
            πblock h * πblock ⟨c.1, hM.1 c.2⟩ * (πblock h)⁻¹ := by
          show (Φ (h * ⟨c.1, hM.1 c.2⟩ * h⁻¹)) f0 =
            (Φ h * Φ ⟨c.1, hM.1 c.2⟩ * (Φ h)⁻¹) f0
          rw [map_mul, map_mul, map_inv]
        rw [hz]
        exact hC''normal.conj_mem _ hπcC'' (πblock h)
      rw [hC'_eq]
      exact hmem
    obtain ⟨c, hc⟩ := cuq2b_projC_surjective (m := m) hCSU hJ₀ j
    let c0 : ↥H0 := ⟨c.1, hM.1 c.2⟩
    have hbC : h * c0 * h⁻¹ ∈ Ctop := hCnormal h c
    let b : ↥C := ⟨h.1 * c.1 * h.1⁻¹, Subgroup.mem_subgroupOf.mp hbC⟩
    have hbcoe : (⟨b.1, hM.1 b.2⟩ : ↥H0) = h * c0 * h⁻¹ := by
      apply Subtype.ext
      rfl
    have heJ_coe : ∀ x : ↥J, ((eJ x : ↥(heldSU a' (AdjoinRoot f0.1.1) ρE hρE)) :
        GL (Fin a') D) = (x : GL (Fin a') D) := by
      intro x
      rfl
    have heC_apply : ∀ c : ↥C, (eC c : GL (Fin a') D) =
        (πGU ⟨c.1, hM.1 c.2⟩ : GL (Fin a') D) := by
      intro c
      dsimp only [eC]
      change ((eJ ((Subgroup.equivMapOfInjective C'' φU.toMonoidHom φU.injective)
        (eM c)) : ↥(heldSU a' (AdjoinRoot f0.1.1) ρE hρE)) : GL (Fin a') D) = _
      rw [heJ_coe]
      change (φU (eM c) : GL (Fin a') D) =
        (φU (πblock ⟨c.1, hM.1 c.2⟩) : GL (Fin a') D)
      rw [heM_apply c]
    have hconj : (eC b : GL (Fin a') D) =
        (πGU ⟨h.1, h.2⟩ : GL (Fin a') D) * (eC c : GL (Fin a') D) *
          ((πGU ⟨h.1, h.2⟩ : GL (Fin a') D))⁻¹ := by
      rw [heC_apply b, heC_apply c, hbcoe]
      simp only [map_mul, map_inv, πGU, MonoidHom.comp_apply]
      rfl
    have hπCb : (πC b : LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ m))) =
        (j' : LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ m))) := by
      have hproj : (πC b : LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ m))) =
          TableB.projConj (LargeEvenSUGroup (Fin N) K (2 ^ m))
            ⟨h.1, hN⟩ (πC c) := by
        change ((Subgroup.inclusion hCSU b : LargeEvenSUGroup (Fin N) K (2 ^ m)) :
            LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ m))) =
          TableB.projConj (LargeEvenSUGroup (Fin N) K (2 ^ m)) ⟨h.1, hN⟩
            ((Subgroup.inclusion hCSU c : LargeEvenSUGroup (Fin N) K (2 ^ m)) :
              LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ m)))
        rw [TableB.projConj_mk]
        apply congrArg (QuotientGroup.mk :
          LargeEvenSUGroup (Fin N) K (2 ^ m) →
            LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ m)))
        apply Subtype.ext
        rfl
      calc (πC b : LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ m)))
          = TableB.projConj (LargeEvenSUGroup (Fin N) K (2 ^ m))
              ⟨h.1, hN⟩ (πC c) := hproj
        _ = TableB.projConj (LargeEvenSUGroup (Fin N) K (2 ^ m))
              ⟨h.1, hN⟩ (j : LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ m))) := by
              rw [hc]
        _ = (j' : LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ m))) := hj'.symm
    have hecent_c : ecent (QuotientGroup.mk c) = QuotientGroup.mk j := by
      rw [hecent_mk c, hc]
    have hecent_b : ecent (QuotientGroup.mk b) = QuotientGroup.mk j' := by
      rw [hecent_mk b, show πC b = j' from Subtype.ext hπCb]
    have heSU_coe : ∀ x : ↥(heldSU a' D ρE hρE),
        ((eSU x : ↥(StatedSU a' (2 ^ mD) D)) : GL (Fin a') D) = (x : GL (Fin a') D) := by
      intro x
      rfl
    have hψj : ψ (QuotientGroup.mk j) =
        (QuotientGroup.mk (eSU (eC c)) :
          LargeEvenProj (LargeEvenSUGroup (Fin a') D (2 ^ mD))) := by
      change eProj (eCZ (ecent.symm (QuotientGroup.mk j))) = _
      rw [show ecent.symm (QuotientGroup.mk j) = QuotientGroup.mk c from by
        rw [← hecent_c, MulEquiv.symm_apply_apply]]
      rfl
    have hψj' : ψ (QuotientGroup.mk j') =
        (QuotientGroup.mk (eSU (eC b)) :
          LargeEvenProj (LargeEvenSUGroup (Fin a') D (2 ^ mD))) := by
      change eProj (eCZ (ecent.symm (QuotientGroup.mk j'))) = _
      rw [show ecent.symm (QuotientGroup.mk j') = QuotientGroup.mk b from by
        rw [← hecent_b, MulEquiv.symm_apply_apply]]
      rfl
    have heSU_mem : ∀ x : ↥(heldSU a' D ρE hρE),
        (eSU x : GL (Fin a') D) ∈ LargeEvenSUGroup (Fin a') D (2 ^ mD) := by
      intro x
      rw [largeEvenSUGroup_eq_statedSU]
      exact (eSU x).2
    let u : ↥(LargeEvenSUGroup (Fin a') D (2 ^ mD)) :=
      ⟨(eSU (eC c) : GL (Fin a') D), heSU_mem (eC c)⟩
    let ub : ↥(LargeEvenSUGroup (Fin a') D (2 ^ mD)) :=
      ⟨(eSU (eC b) : GL (Fin a') D), heSU_mem (eC b)⟩
    rw [hψj, hψj']
    change TableB.projConj (LargeEvenSUGroup (Fin a') D (2 ^ mD))
      (Subgroup.inclusion (CFSG.HardMathSupport.C14Cl.uniGroup_le_normalizer hD)
        (π ⟨h.1, h.2⟩)) (u : LargeEvenProj (LargeEvenSUGroup (Fin a') D (2 ^ mD))) =
      (ub : LargeEvenProj (LargeEvenSUGroup (Fin a') D (2 ^ mD)))
    rw [TableB.projConj_mk]
    apply congrArg (QuotientGroup.mk :
      ↥(LargeEvenSUGroup (Fin a') D (2 ^ mD)) →
        LargeEvenProj (LargeEvenSUGroup (Fin a') D (2 ^ mD)))
    apply Subtype.ext
    change (Subgroup.inclusion (CFSG.HardMathSupport.C14Cl.uniGroup_le_normalizer hD)
        (π ⟨h.1, h.2⟩) : GL (Fin a') D) * (eSU (eC c) : GL (Fin a') D) *
        ((Subgroup.inclusion (CFSG.HardMathSupport.C14Cl.uniGroup_le_normalizer hD)
          (π ⟨h.1, h.2⟩) : GL (Fin a') D))⁻¹ = (eSU (eC b) : GL (Fin a') D)
    rw [heSU_coe, heSU_coe]
    rw [hconj]
    rfl

  ·
    have hrep : IsRep Hp f0.1 := f0.2.resolve_left hself
    have hBl : Bl Hp f0.1 = ⊤ := Bl_of_isRep Hp hrep
    haveI : Fact (Irreducible f0.1.1) := ⟨hirr f0.1.1 hf0F⟩
    haveI : Module.Finite K (AdjoinRoot f0.1.1) := (hmon f0.1.1 hf0F).finite_adjoinRoot
    haveI : Finite (AdjoinRoot f0.1.1) :=
      Finite.of_equiv (Fin (Module.finrank K (AdjoinRoot f0.1.1)) → K)
        (Module.finBasis K (AdjoinRoot f0.1.1)).equivFun.toEquiv.symm
    let W := Vf (s : Matrix (Fin N) (Fin N) K) bb F f0.1.1
    haveI : Module.Finite (AdjoinRoot f0.1.1) W :=
      Module.Finite.of_restrictScalars_finite K (AdjoinRoot f0.1.1) W
    haveI : Module.Free (AdjoinRoot f0.1.1) W := Module.Free.of_divisionRing _ _
    let bdim := Module.finrank (AdjoinRoot f0.1.1) W
    let φGL : Hact f0 ≃* GL (Fin bdim) (AdjoinRoot f0.1.1) :=
      cuq2b_blockGL Hp hKfact f0.1 hBl
    let J : Subgroup (GL (Fin bdim) (AdjoinRoot f0.1.1)) := C''.map φGL.toMonoidHom
    have hJcomp : CFSG.Open.IsComponentOf J ⊤ := by
      have htop : (⊤ : Subgroup (Hact f0)).map φGL.toMonoidHom = ⊤ := by
        rw [Subgroup.map_top, MonoidHom.range_eq_top]
        simpa using φGL.surjective
      have h := cuq2b_isComponentOf_map_mulEquiv φGL hC''
      simpa [J, htop] using h
    let S : Subgroup (GL (Fin bdim) (AdjoinRoot f0.1.1)) :=
      StatedSL bdim (AdjoinRoot f0.1.1)
    have hJeq : J = S := by
      simpa only [S] using cuq2b_component_GL_eq_statedSL SLComponentsTrivial_holds hJcomp
    have e1 : ↥C'' ≃* ↥J :=
      Subgroup.equivMapOfInjective C'' φGL.toMonoidHom φGL.injective
    let eSL : ↥C'' ≃* ↥S := e1.trans (MulEquiv.subgroupCongr hJeq)
    let eC : ↥C ≃* ↥S := eM.trans eSL
    have hb2 : 2 ≤ bdim := by
      by_contra hlt
      have hle1 : bdim ≤ 1 := by omega
      exact absurd hC.2.2 (not_isQuasisimple_of_mulEquiv eC fun x y =>
        CFSG.LieType.SemisimpleCentralizers.OrderThree.mul_comm_statedSL_of_le_one hle1
          (show ↥(StatedSL bdim (AdjoinRoot f0.1.1)) from x)
          (show ↥(StatedSL bdim (AdjoinRoot f0.1.1)) from y))
    have hCperf : Group.IsPerfect ↥C := Group.isPerfect_def.mpr hC.2.2.1
    let πC : ↥C →* ↥J₀ := cuq2b_projC (m := m) hCSU hJ₀
    let ecent : ↥C ⧸ Subgroup.center ↥C ≃* ↥J₀ ⧸ Subgroup.center ↥J₀ :=
      cuq2b_ecent hCperf hCSU hJ₀
    let eCZ : ↥C ⧸ Subgroup.center ↥C ≃*
        ↥(StatedSL bdim (AdjoinRoot f0.1.1)) ⧸
          Subgroup.center ↥(StatedSL bdim (AdjoinRoot f0.1.1)) :=
      QuotientGroup.congr _ _ eC (Subgroup.map_center_eq eC)
    obtain ⟨ψlin⟩ : Nonempty (↥J₀ ⧸ Subgroup.center ↥J₀ ≃*
        StatedProj (StatedSL bdim (AdjoinRoot f0.1.1))) :=
      ⟨ecent.symm.trans (eCZ.trans
        (QuotientGroup.quotientMulEquivOfEq
          (CFSG.LieType.SemisimpleCentralizers.Held.center_statedSL_eq (E := AdjoinRoot f0.1.1) bdim)))⟩
    obtain ⟨hJEe⟩ := hJE
    have hcardeq : Nat.card (StatedProj (StatedSL bdim (AdjoinRoot f0.1.1))) =
        Nat.card (StatedProj (StatedSU d (2 ^ m') E)) :=
      Nat.card_congr (ψlin.symm.trans hJEe).toEquiv
    have hcardD' : Nat.card (AdjoinRoot f0.1.1) = 2 ^ (2 * (m * f0.1.1.natDegree)) := by
      let pb := AdjoinRoot.powerBasis (K := K) (hirr f0.1.1 hf0F).ne_zero
      have hdim : pb.dim = f0.1.1.natDegree := AdjoinRoot.powerBasis_dim _
      have hfin : Nat.card (Fin pb.dim) = pb.dim := by simp
      rw [Nat.card_congr pb.basis.equivFun.toEquiv, Nat.card_fun, hfin, hdim, hK,
        ← pow_mul, pow_mul]
      ring_nf
    have hcardSL : Nat.card (StatedProj (StatedSL bdim (AdjoinRoot f0.1.1))) =
        CFSG.Open.ordA (bdim - 1) (2 ^ (2 * (m * f0.1.1.natDegree))) := by
      rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := AdjoinRoot f0.1.1)
        (n := bdim) (by omega), hcardD', CFSG.Open.ordA,
        Nat.sub_add_cancel (by omega : 1 ≤ bdim), mul_comm (bdim - 1) bdim]
    have hcardE' : Nat.card E = (2 ^ m') ^ 2 := by
      rw [hE.card, ← pow_mul, mul_comm]
    have hcardSU : Nat.card (StatedProj (StatedSU d (2 ^ m') E)) = CFSG.Open.ordTwistedA (d - 1) (2 ^ m') := by
      rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two hE.one_le
        hcardE' (by omega), CFSG.Open.ordTwistedA,
        Nat.sub_add_cancel (by omega : 1 ≤ d), mul_comm (d - 1) d]
    have hOrder : CFSG.Open.ordA (bdim - 1) (2 ^ (2 * (m * f0.1.1.natDegree))) =
        CFSG.Open.ordTwistedA (d - 1) (2 ^ m') := by
      rw [← hcardSL, ← hcardSU]
      exact hcardeq
    exfalso
    exact (Timmesfeld.Orders.ordA_ne_ordTwistedA (n := bdim - 1) (f := 2 * (m * f0.1.1.natDegree))
      (u := d - 1) (g := m') (by omega)
      (Nat.mul_pos (by norm_num) (Nat.mul_pos hmpos (hirr f0.1.1 hf0F).natDegree_pos)) (by omega) hE.one_le) hOrder


theorem q2Uni_blockType {N m : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ m) ^ 2)
    (τ : K ≃+* K) (hτ : ∀ x, τ (τ x) = x) (hτQ : ∀ x, τ x = x ^ 2 ^ m)
    (s : GL (Fin N) K) (hs : s ∈ Held.heldGU N K τ hτ) (hso : Odd (orderOf s))
    (C : Subgroup (GL (Fin N) K))
    (hC : CFSG.Assembly.IsComponentOf C
      (Subgroup.centralizer ({s} : Set (GL (Fin N) K)) ⊓ Held.heldGU N K τ hτ))
    (hCSU : C ≤ LargeEvenSUGroup (Fin N) K (2 ^ m))
    (J₀ : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ m))))
    (hJ₀ : J₀ = (C.subgroupOf (LargeEvenSUGroup (Fin N) K (2 ^ m))).map
      (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ m)))) :
    (∃ (a k : ℕ) (D : Type) (_ : Field D) (_ : UnitaryFieldData 2 (m * k) D), 1 ≤ k ∧ 2 ≤ a ∧
      a * k ≤ N ∧ ¬ (a = 2 ∧ m * k = 1) ∧ ¬ (a = 3 ∧ m * k = 1) ∧
      Nonempty (↥J₀ ⧸ Subgroup.center ↥J₀ ≃*
        LargeEvenProj (LargeEvenSUGroup (Fin a) D (2 ^ (m * k))))) ∨
    (∃ (b k : ℕ) (D : Type) (_ : Field D) (_ : Finite D), 1 ≤ k ∧ 2 ≤ b ∧ 2 * (b * k) ≤ N ∧
      Nat.card D = 2 ^ (2 * (m * k)) ∧
      Nonempty (↥J₀ ⧸ Subgroup.center ↥J₀ ≃* StatedProj (StatedSL b D))) := by
  classical
  have hmpos : 0 < m := by
    by_contra h
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos h
    rw [hm0] at hK
    norm_num at hK
    haveI : Fintype K := Fintype.ofFinite K
    have : 1 < Nat.card K := by rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
    omega
  have hUFD : UnitaryFieldData 2 m K :=
    CFSG.ComponentClassification.RankTwoClassical.unitaryFieldData_of_card hK hmpos
  haveI : CharP K 2 := hUFD.charP
  have hord : (orderOf s : K) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff K 2] at h
    exact (Nat.not_even_iff_odd.mpr hso) (even_iff_two_dvd.mpr h)
  have hM : CFSG.Open.IsComponentOf C
      (Subgroup.centralizer ({s} : Set (GL (Fin N) K)) ⊓ heldGU N K τ hτ) :=
    (CFSG.Assembly.isComponentOf_iff_open).1 hC
  have hm0 : 0 < orderOf s := orderOf_pos s
  have hsm : (s : Matrix (Fin N) (Fin N) K) ^ orderOf s = 1 := by
    rw [← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
  have hs' : adjM τ (s : Matrix (Fin N) (Fin N) K) * (s : Matrix (Fin N) (Fin N) K) = 1 :=
    Held.mem_heldGU.mp hs
  set F : Finset K[X] := factorsOf (L := K) (orderOf s) with hF
  have hirr : ∀ f ∈ F, Irreducible f := fun f hf => factorsOf_irreducible hf
  have hmon : ∀ f ∈ F, Monic f := fun f hf => factorsOf_monic hf
  have hprod : ∏ f ∈ F, f = X ^ orderOf s - 1 := prod_factorsOf hord hm0
  have hcop : ∀ f ∈ F, ∃ u v : K[X], u * f + v * gcF F f = 1 :=
    fun f hf => isCoprime_gcF hirr hmon hf
  choose! aa bb hab using hcop
  let Hp : PrimaryHyp τ (s : Matrix (Fin N) (Fin N) K) (orderOf s) F aa bb :=
    ⟨hτ, hm0, hirr, hmon, hprod, hsm, hs', hab⟩
  haveI hKfact : ∀ f : ↥(Fset (s : Matrix (Fin N) (Fin N) K) bb F),
      Fact (∀ x ∈ Vf (s : Matrix (Fin N) (Fin N) K) bb F f.1,
        aeval (s : Matrix (Fin N) (Fin N) K) f.1 *ᵥ x = 0) :=
    fun f => ⟨fun x hx => aeval_factor_mulVec_eq_zero Hp (mem_Fset.mp f.2).1 hx⟩
  let H0 : Subgroup (GL (Fin N) K) :=
    Subgroup.centralizer ({s} : Set (GL (Fin N) K)) ⊓ heldGU N K τ hτ
  let Hact : Activ Hp → Type := fun f => ↥(Bl Hp f.1)
  haveI hHfin : ∀ f : Activ Hp, Finite (Hact f) := fun f => finite_Bl Hp f.1
  let Φ : ↥H0 ≃* (∀ f : Activ Hp, Hact f) :=
    (centralizerEquivGlin hτ s).trans (glinEquivBlocks Hp)
  let Ctop : Subgroup ↥H0 := C.subgroupOf H0
  have hCtop : CFSG.Open.IsComponentOf Ctop ⊤ := cuq2b_isComponentOf_subgroupOf_top hM
  let C' : Subgroup (∀ f : Activ Hp, Hact f) := Ctop.map Φ.toMonoidHom
  have hC' : CFSG.Open.IsComponentOf C' ⊤ := by
    have h := isComponentOf_map_of_injective Φ.toMonoidHom Φ.injective
      ((CFSG.Assembly.isComponentOf_iff_open).2 hCtop)
    rw [← MonoidHom.range_eq_map] at h
    exact (CFSG.Assembly.isComponentOf_iff_open).1 (by simpa [C'] using h)
  obtain ⟨f0, hf0⟩ := exists_factor_of_isComponentOf_top hC'
  let Fsub : Subgroup (∀ f : Activ Hp, Hact f) := factorSub f0
  let ρF : ↥Fsub ≃* Hact f0 :=
    { toFun := fun w => w.1 f0
      invFun := fun x => ⟨MonoidHom.mulSingle Hact f0 x, by
        dsimp only [Fsub]
        rw [mem_factorSub]
        intro j hj
        rw [MonoidHom.mulSingle_apply]
        simp [hj]⟩
      left_inv := by
        intro w
        apply Subtype.ext
        funext j
        by_cases hj : j = f0
        · subst hj; simp [MonoidHom.mulSingle_apply]
        · simp [MonoidHom.mulSingle_apply, hj, mem_factorSub.mp w.2 j hj]
      right_inv := by intro x; simp [MonoidHom.mulSingle_apply]
      map_mul' := fun x y => rfl }
  have hf0F : f0.1.1 ∈ F := (mem_Fset.mp f0.1.2).1
  have hPf : Pmat (s : Matrix (Fin N) (Fin N) K) bb F f0.1.1 ≠ 0 :=
    (mem_Fset.mp f0.1.2).2
  have hC'F : CFSG.Open.IsComponentOf (C'.subgroupOf Fsub) ⊤ := by
    apply CFSG.ComponentClassification.LocalComponents.of_overgroup hC'
    simpa [Fsub] using hf0
  let C'' : Subgroup (Hact f0) := (C'.subgroupOf Fsub).map ρF.toMonoidHom
  have hC'' : CFSG.Open.IsComponentOf C'' ⊤ := by
    have h := isComponentOf_map_of_injective ρF.toMonoidHom ρF.injective
      ((CFSG.Assembly.isComponentOf_iff_open).2 hC'F)
    rw [Subgroup.map_top, MonoidHom.range_eq_top.mpr ρF.surjective] at h
    exact (CFSG.Assembly.isComponentOf_iff_open).1 (by simpa [C''] using h)
  let πblock : ↥H0 →* Hact f0 := (Pi.evalMonoidHom Hact f0).comp Φ.toMonoidHom
  let eCtop : ↥C ≃* ↥Ctop := (Subgroup.subgroupOfEquivOfLe hM.1).symm
  let eC' : ↥Ctop ≃* ↥C' := Subgroup.equivMapOfInjective Ctop Φ.toMonoidHom Φ.injective
  let eM2 : ↥C' ≃* ↥(C'.subgroupOf Fsub) := (Subgroup.subgroupOfEquivOfLe hf0).symm
  let eM3 : ↥(C'.subgroupOf Fsub) ≃* ↥C'' :=
    Subgroup.equivMapOfInjective _ ρF.toMonoidHom ρF.injective
  let eM : ↥C ≃* ↥C'' := eCtop.trans (eC'.trans (eM2.trans eM3))
  have heM_apply : ∀ c : ↥C, ((eM c : ↥C'') : Hact f0) = πblock ⟨c.1, hM.1 c.2⟩ := by
    intro c
    rfl
  by_cases hself : piI Hp f0.1 = f0.1
  · have hselfA : adjM τ (Pmat (s : Matrix (Fin N) (Fin N) K) bb F f0.1.1) =
        Pmat (s : Matrix (Fin N) (Fin N) K) bb F f0.1.1 := by
      have h := adjM_piI Hp f0.1
      rw [hself] at h
      simpa using h
    haveI : Fact (Irreducible f0.1.1) := ⟨hirr f0.1.1 hf0F⟩
    haveI : Fact (∀ x ∈ Vf (s : Matrix (Fin N) (Fin N) K) bb F f0.1.1,
        aeval (s : Matrix (Fin N) (Fin N) K) f0.1.1 *ᵥ x = 0) :=
      ⟨fun x hx => aeval_factor_mulVec_eq_zero Hp hf0F hx⟩
    obtain ⟨a', ρE, hρE, ha'def, hcardE, hτQ', ⟨φ0⟩⟩ :=
      cuq2b_selfDual_block_iso Hp hK hτQ hf0F hPf hselfA
    have hBl : Bl Hp f0.1 = unitaryBlock τ (s : Matrix (Fin N) (Fin N) K) bb F f0.1.1 :=
      Bl_of_selfDual Hp hself
    let φU : ↥(Bl Hp f0.1) ≃* heldGU a' (AdjoinRoot f0.1.1) ρE hρE :=
      (MulEquiv.subgroupCongr hBl).trans φ0
    let J : Subgroup ↥(heldGU a' (AdjoinRoot f0.1.1) ρE hρE) := C''.map φU.toMonoidHom
    have hJcomp : CFSG.Open.IsComponentOf J ⊤ := by
      have h := isComponentOf_map_of_injective φU.toMonoidHom φU.injective
        ((CFSG.Assembly.isComponentOf_iff_open).2 hC'')
      rw [Subgroup.map_top, MonoidHom.range_eq_top.mpr φU.surjective] at h
      exact (CFSG.Assembly.isComponentOf_iff_open).1 (by simpa [J] using h)
    have hJmapcomp : CFSG.Open.IsComponentOf
        (J.map (heldGU a' (AdjoinRoot f0.1.1) ρE hρE).subtype)
        (heldGU a' (AdjoinRoot f0.1.1) ρE hρE) := by
      have h := isComponentOf_map_of_injective (heldGU a' (AdjoinRoot f0.1.1) ρE hρE).subtype
        (heldGU a' (AdjoinRoot f0.1.1) ρE hρE).subtype_injective
        ((CFSG.Assembly.isComponentOf_iff_open).2 hJcomp)
      rw [← MonoidHom.range_eq_map] at h
      exact (CFSG.Assembly.isComponentOf_iff_open).1 (by simpa using h)
    have hJeqGL : J.map (heldGU a' (AdjoinRoot f0.1.1) ρE hρE).subtype =
        heldSU a' (AdjoinRoot f0.1.1) ρE hρE :=
      cuq2b_component_heldGU_eq_heldSU SUComponentsTrivial_holds
        (Q := (2 ^ m) ^ f0.1.1.natDegree) hcardE hτQ' hJmapcomp
    let eJ : ↥J ≃* ↥(heldSU a' (AdjoinRoot f0.1.1) ρE hρE) :=
      (Subgroup.equivMapOfInjective J (heldGU a' (AdjoinRoot f0.1.1) ρE hρE).subtype
        (heldGU a' (AdjoinRoot f0.1.1) ρE hρE).subtype_injective).trans
        (MulEquiv.subgroupCongr hJeqGL)
    let eC : ↥C ≃* ↥(heldSU a' (AdjoinRoot f0.1.1) ρE hρE) :=
      eM.trans ((Subgroup.equivMapOfInjective C'' φU.toMonoidHom φU.injective).trans eJ)
    let πGU : ↥H0 →* ↥(heldGU a' (AdjoinRoot f0.1.1) ρE hρE) :=
      φU.toMonoidHom.comp πblock
    let D : Type := AdjoinRoot f0.1.1
    let mD : ℕ := m * f0.1.1.natDegree
    have hcardD : Nat.card D = 2 ^ (2 * mD) := by
      dsimp only [D, mD]
      rw [hcardE, ← pow_mul, ← pow_mul]
      congr 1
      ring
    have hfdeg : 0 < f0.1.1.natDegree := (hirr f0.1.1 hf0F).natDegree_pos
    have hD : UnitaryFieldData 2 mD D :=
      ⟨Nat.prime_two, Nat.mul_pos hmpos hfdeg, hcardD⟩
    have hρbar : ∀ x : D, ρE x = hD.bar x := by
      intro x
      rw [hτQ', hD.bar_apply]
      dsimp only [mD]
      rw [pow_mul]
    have hEqGU : heldGU a' D ρE hρE = TableB.unitGroup (ι := Fin a') hD.bar := by
      ext A
      rw [Held.mem_heldGU, TableB.mem_unitGroup]
      have hmap : (A : Matrix (Fin a') (Fin a') D).map ρE =
          (A : Matrix (Fin a') (Fin a') D).map hD.bar := by
        ext i j
        simp only [Matrix.map_apply, hρbar]
      rw [hmap]
    let eGU : ↥(heldGU a' D ρE hρE) ≃* ↥(TableB.unitGroup (ι := Fin a') hD.bar) :=
      MulEquiv.subgroupCongr hEqGU
    let π : ↥H0 →* ↥(TableB.unitGroup (ι := Fin a') hD.bar) :=
      eGU.toMonoidHom.comp πGU
    have hτQmD : ∀ x, ρE x = x ^ 2 ^ mD := by
      intro x
      rw [hτQ']
      dsimp only [mD]
      rw [pow_mul]
    have hSUeq : heldSU a' D ρE hρE = StatedSU a' (2 ^ mD) D :=
      hct_heldSU_eq_statedSU hτQmD
    have ha2 : 2 ≤ a' := by
      by_contra hlt
      have hle1 : a' ≤ 1 := by omega
      exact absurd hC.2.2 (not_isQuasisimple_of_mulEquiv eC fun x y =>
        Subtype.ext (mul_comm_GL_of_le_one hle1 (x : GL (Fin a') D) (y : GL (Fin a') D)))
    have hne : ¬ (a' = 3 ∧ mD = 1) := by
      rintro ⟨ha3, hmD1⟩
      have hcardD4 : Nat.card D = (2 ^ 1) ^ 2 := by
        rw [hD.card, hmD1]
        norm_num
      haveI : Group.IsSolvable ↥(StatedSU a' (2 ^ mD) D) := by
        rw [ha3, hmD1]
        exact CFSG.Quasithin.isSolvable_statedSU_one hcardD4
      haveI : Group.IsSolvable ↥(heldSU a' D ρE hρE) := by
        rw [hSUeq]
        infer_instance
      have hsolvC : Group.IsSolvable ↥C :=
        Group.isSolvable_of_isSolvable_injective (f := eC.toMonoidHom) eC.injective
      haveI : Nontrivial ↥C := by
        haveI : Nontrivial (↥C ⧸ Subgroup.center ↥C) := hC.2.2.2.toNontrivial
        have hne_top : Subgroup.center ↥C ≠ ⊤ := QuotientGroup.nontrivial_iff.mp inferInstance
        by_contra hsub
        haveI : Subsingleton ↥C := not_nontrivial_iff_subsingleton.mp hsub
        exact hne_top (by
          ext x
          constructor
          · intro _; trivial
          · intro _; rw [Subgroup.mem_center_iff]; intro y; exact Subsingleton.elim _ _)
      haveI : Group.IsPerfect ↥C := Group.isPerfect_def.mpr hC.2.2.1
      exact (Group.IsPerfect.not_isSolvable _ hsolvC).elim
    have hcenter : Subgroup.center (heldSU a' D ρE hρE) =
        (StatedScalars (Fin a') D).subgroupOf (heldSU a' D ρE hρE) :=
      cuq2b_center_heldSU_eq_scalars hD ha2 hne hρE hτQmD
    have hcenterSU : Subgroup.center (StatedSU a' (2 ^ mD) D) =
        (StatedScalars (Fin a') D).subgroupOf (StatedSU a' (2 ^ mD) D) := by
      have h := hcenter
      rw [hSUeq] at h
      exact h
    let eSU : ↥(heldSU a' D ρE hρE) ≃* ↥(StatedSU a' (2 ^ mD) D) :=
      MulEquiv.subgroupCongr hSUeq
    let eCZ : ↥C ⧸ Subgroup.center ↥C ≃*
        ↥(heldSU a' D ρE hρE) ⧸ Subgroup.center ↥(heldSU a' D ρE hρE) :=
      QuotientGroup.congr _ _ eC (Subgroup.map_center_eq eC)
    let eProj : ↥(heldSU a' D ρE hρE) ⧸ Subgroup.center ↥(heldSU a' D ρE hρE) ≃*
        StatedProj (StatedSU a' (2 ^ mD) D) :=
      (QuotientGroup.congr _ _ eSU (Subgroup.map_center_eq eSU)).trans
        (QuotientGroup.quotientMulEquivOfEq hcenterSU)
    have hCperf : Group.IsPerfect ↥C := Group.isPerfect_def.mpr hC.2.2.1
    let πC : ↥C →* ↥J₀ := cuq2b_projC (m := m) hCSU hJ₀
    let ecent : ↥C ⧸ Subgroup.center ↥C ≃* ↥J₀ ⧸ Subgroup.center ↥J₀ :=
      cuq2b_ecent hCperf hCSU hJ₀
    have hecent_mk : ∀ a : ↥C, ecent (QuotientGroup.mk a) = QuotientGroup.mk (πC a) :=
      fun a => cuq2b_ecent_mk hCperf hCSU hJ₀ a
    let ψ : ↥J₀ ⧸ Subgroup.center ↥J₀ ≃*
        LargeEvenProj (LargeEvenSUGroup (Fin a') D (2 ^ mD)) :=
      ecent.symm.trans (eCZ.trans eProj)
    have hfinV : Module.finrank K (Vf (s : Matrix (Fin N) (Fin N) K) bb F f0.1.1) = a' * f0.1.1.natDegree := by
      have h1 : Module.finrank K (Vf (s : Matrix (Fin N) (Fin N) K) bb F f0.1.1) =
          Module.finrank K (AdjoinRoot f0.1.1) *
            Module.finrank (AdjoinRoot f0.1.1) (Vf (s : Matrix (Fin N) (Fin N) K) bb F f0.1.1) :=
        (Module.finrank_mul_finrank K (AdjoinRoot f0.1.1) (Vf (s : Matrix (Fin N) (Fin N) K) bb F f0.1.1)).symm
      have h2 : Module.finrank K (AdjoinRoot f0.1.1) = f0.1.1.natDegree :=
        ((AdjoinRoot.powerBasis (K := K) (hirr f0.1.1 hf0F).ne_zero).finrank).trans
          (AdjoinRoot.powerBasis_dim _)
      rw [h1, h2, ha'def]
      exact mul_comm _ _
    have hdimN : a' * f0.1.1.natDegree ≤ N := by
      rw [← hfinV]
      calc Module.finrank K (Vf (s : Matrix (Fin N) (Fin N) K) bb F f0.1.1) ≤ Module.finrank K (Fin N → K) :=
            Submodule.finrank_le _
        _ = N := Module.finrank_fin_fun K
    have hne2 : ¬ (a' = 2 ∧ mD = 1) := by
      rintro ⟨ha2', hmD1⟩
      have hcardD4 : Nat.card D = (2 ^ 1) ^ 2 := by
        rw [hD.card, hmD1]
        norm_num
      obtain ⟨β, hβ⟩ := cuq2bt_injective_su2_su3 (K := D) (q := 2 ^ 1) (by norm_num)
      have hsolv2 : Group.IsSolvable ↥(StatedSU 2 (2 ^ 1) D) := by
        haveI : Group.IsSolvable ↥(StatedSU 3 (2 ^ 1) D) :=
          CFSG.Quasithin.isSolvable_statedSU_one hcardD4
        exact Group.isSolvable_of_isSolvable_injective (f := β) hβ
      haveI : Group.IsSolvable ↥(StatedSU a' (2 ^ mD) D) := by
        rw [ha2', hmD1]
        exact hsolv2
      haveI : Group.IsSolvable ↥(heldSU a' D ρE hρE) := by
        rw [hSUeq]
        infer_instance
      have hsolvC : Group.IsSolvable ↥C :=
        Group.isSolvable_of_isSolvable_injective (f := eC.toMonoidHom) eC.injective
      haveI : Nontrivial ↥C := by
        haveI : Nontrivial (↥C ⧸ Subgroup.center ↥C) := hC.2.2.2.toNontrivial
        have hne_top : Subgroup.center ↥C ≠ ⊤ := QuotientGroup.nontrivial_iff.mp inferInstance
        by_contra hsub
        haveI : Subsingleton ↥C := not_nontrivial_iff_subsingleton.mp hsub
        exact hne_top (by
          ext x
          constructor
          · intro _; trivial
          · intro _; rw [Subgroup.mem_center_iff]; intro y; exact Subsingleton.elim _ _)
      haveI : Group.IsPerfect ↥C := Group.isPerfect_def.mpr hC.2.2.1
      exact (Group.IsPerfect.not_isSolvable _ hsolvC).elim
    exact Or.inl ⟨a', f0.1.1.natDegree, D, inferInstance, hD, hfdeg, ha2, hdimN, hne2, hne,
      ⟨ψ⟩⟩

  ·
    have hrep : IsRep Hp f0.1 := f0.2.resolve_left hself
    have hBl : Bl Hp f0.1 = ⊤ := Bl_of_isRep Hp hrep
    haveI : Fact (Irreducible f0.1.1) := ⟨hirr f0.1.1 hf0F⟩
    haveI : Module.Finite K (AdjoinRoot f0.1.1) := (hmon f0.1.1 hf0F).finite_adjoinRoot
    haveI : Finite (AdjoinRoot f0.1.1) :=
      Finite.of_equiv (Fin (Module.finrank K (AdjoinRoot f0.1.1)) → K)
        (Module.finBasis K (AdjoinRoot f0.1.1)).equivFun.toEquiv.symm
    let W := Vf (s : Matrix (Fin N) (Fin N) K) bb F f0.1.1
    haveI : Module.Finite (AdjoinRoot f0.1.1) W :=
      Module.Finite.of_restrictScalars_finite K (AdjoinRoot f0.1.1) W
    haveI : Module.Free (AdjoinRoot f0.1.1) W := Module.Free.of_divisionRing _ _
    let bdim := Module.finrank (AdjoinRoot f0.1.1) W
    let φGL : Hact f0 ≃* GL (Fin bdim) (AdjoinRoot f0.1.1) :=
      cuq2b_blockGL Hp hKfact f0.1 hBl
    let J : Subgroup (GL (Fin bdim) (AdjoinRoot f0.1.1)) := C''.map φGL.toMonoidHom
    have hJcomp : CFSG.Open.IsComponentOf J ⊤ := by
      have htop : (⊤ : Subgroup (Hact f0)).map φGL.toMonoidHom = ⊤ := by
        rw [Subgroup.map_top, MonoidHom.range_eq_top]
        simpa using φGL.surjective
      have h := cuq2b_isComponentOf_map_mulEquiv φGL hC''
      simpa [J, htop] using h
    let S : Subgroup (GL (Fin bdim) (AdjoinRoot f0.1.1)) :=
      StatedSL bdim (AdjoinRoot f0.1.1)
    have hJeq : J = S := by
      simpa only [S] using cuq2b_component_GL_eq_statedSL SLComponentsTrivial_holds hJcomp
    have e1 : ↥C'' ≃* ↥J :=
      Subgroup.equivMapOfInjective C'' φGL.toMonoidHom φGL.injective
    let eSL : ↥C'' ≃* ↥S := e1.trans (MulEquiv.subgroupCongr hJeq)
    let eC : ↥C ≃* ↥S := eM.trans eSL
    have hb2 : 2 ≤ bdim := by
      by_contra hlt
      have hle1 : bdim ≤ 1 := by omega
      exact absurd hC.2.2 (not_isQuasisimple_of_mulEquiv eC fun x y =>
        CFSG.LieType.SemisimpleCentralizers.OrderThree.mul_comm_statedSL_of_le_one hle1
          (show ↥(StatedSL bdim (AdjoinRoot f0.1.1)) from x)
          (show ↥(StatedSL bdim (AdjoinRoot f0.1.1)) from y))
    have hCperf : Group.IsPerfect ↥C := Group.isPerfect_def.mpr hC.2.2.1
    let πC : ↥C →* ↥J₀ := cuq2b_projC (m := m) hCSU hJ₀
    let ecent : ↥C ⧸ Subgroup.center ↥C ≃* ↥J₀ ⧸ Subgroup.center ↥J₀ :=
      cuq2b_ecent hCperf hCSU hJ₀
    let eCZ : ↥C ⧸ Subgroup.center ↥C ≃*
        ↥(StatedSL bdim (AdjoinRoot f0.1.1)) ⧸
          Subgroup.center ↥(StatedSL bdim (AdjoinRoot f0.1.1)) :=
      QuotientGroup.congr _ _ eC (Subgroup.map_center_eq eC)
    obtain ⟨ψlin⟩ : Nonempty (↥J₀ ⧸ Subgroup.center ↥J₀ ≃*
        StatedProj (StatedSL bdim (AdjoinRoot f0.1.1))) :=
      ⟨ecent.symm.trans (eCZ.trans
        (QuotientGroup.quotientMulEquivOfEq
          (CFSG.LieType.SemisimpleCentralizers.Held.center_statedSL_eq (E := AdjoinRoot f0.1.1) bdim)))⟩
    have hcardD' : Nat.card (AdjoinRoot f0.1.1) = 2 ^ (2 * (m * f0.1.1.natDegree)) := by
      let pb := AdjoinRoot.powerBasis (K := K) (hirr f0.1.1 hf0F).ne_zero
      have hdim : pb.dim = f0.1.1.natDegree := AdjoinRoot.powerBasis_dim _
      have hfin : Nat.card (Fin pb.dim) = pb.dim := by simp
      rw [Nat.card_congr pb.basis.equivFun.toEquiv, Nat.card_fun, hfin, hdim, hK,
        ← pow_mul, pow_mul]
      ring_nf
    have hfinW : Module.finrank K (Vf (s : Matrix (Fin N) (Fin N) K) bb F f0.1.1) = bdim * f0.1.1.natDegree := by
      have h1 : Module.finrank K (Vf (s : Matrix (Fin N) (Fin N) K) bb F f0.1.1) =
          Module.finrank K (AdjoinRoot f0.1.1) *
            Module.finrank (AdjoinRoot f0.1.1) (Vf (s : Matrix (Fin N) (Fin N) K) bb F f0.1.1) :=
        (Module.finrank_mul_finrank K (AdjoinRoot f0.1.1) (Vf (s : Matrix (Fin N) (Fin N) K) bb F f0.1.1)).symm
      have h2 : Module.finrank K (AdjoinRoot f0.1.1) = f0.1.1.natDegree :=
        ((AdjoinRoot.powerBasis (K := K) (hirr f0.1.1 hf0F).ne_zero).finrank).trans
          (AdjoinRoot.powerBasis_dim _)
      rw [h1, h2]
      exact mul_comm _ _
    have hfinW' : Module.finrank K (Vf (s : Matrix (Fin N) (Fin N) K) bb F (piI Hp f0.1).1) =
        bdim * f0.1.1.natDegree := by
      rw [← cuq2bt_finrank_Vf_eq_piI Hp f0.1, hfinW]
    have hdisj : Disjoint (Vf (s : Matrix (Fin N) (Fin N) K) bb F f0.1.1) (Vf (s : Matrix (Fin N) (Fin N) K) bb F (piI Hp f0.1).1) := by
      rw [Submodule.disjoint_def]
      intro x hx hx'
      have hPg : Pmat (s : Matrix (Fin N) (Fin N) K) bb F (piI Hp f0.1).1 *ᵥ x = x := mem_Vf.mp hx'
      calc x = Pmat (s : Matrix (Fin N) (Fin N) K) bb F f0.1.1 *ᵥ x := (mem_Vf.mp hx).symm
        _ = Pmat (s : Matrix (Fin N) (Fin N) K) bb F f0.1.1 *ᵥ (Pmat (s : Matrix (Fin N) (Fin N) K) bb F (piI Hp f0.1).1 *ᵥ x) := by rw [hPg]
        _ = (Pmat (s : Matrix (Fin N) (Fin N) K) bb F f0.1.1 * Pmat (s : Matrix (Fin N) (Fin N) K) bb F (piI Hp f0.1).1) *ᵥ x := by
              rw [Matrix.mulVec_mulVec]
        _ = 0 := by
              rw [Hp.Pmat_orth hf0F (mem_Fset.mp (piI Hp f0.1).2).1
                (fun h => hself (Subtype.ext h.symm)), Matrix.zero_mulVec]
    have hdim2 : 2 * (bdim * f0.1.1.natDegree) ≤ N := by
      have hsup : Module.finrank K ↥(Vf (s : Matrix (Fin N) (Fin N) K) bb F f0.1.1 ⊔ Vf (s : Matrix (Fin N) (Fin N) K) bb F (piI Hp f0.1).1) =
          Module.finrank K (Vf (s : Matrix (Fin N) (Fin N) K) bb F f0.1.1) +
            Module.finrank K (Vf (s : Matrix (Fin N) (Fin N) K) bb F (piI Hp f0.1).1) := by
        have h := Submodule.finrank_sup_add_finrank_inf_eq
          (Vf (s : Matrix (Fin N) (Fin N) K) bb F f0.1.1) (Vf (s : Matrix (Fin N) (Fin N) K) bb F (piI Hp f0.1).1)
        rw [hdisj.eq_bot, finrank_bot, add_zero] at h
        exact h
      have hle : Module.finrank K ↥(Vf (s : Matrix (Fin N) (Fin N) K) bb F f0.1.1 ⊔ Vf (s : Matrix (Fin N) (Fin N) K) bb F (piI Hp f0.1).1) ≤ N := by
        calc Module.finrank K ↥(Vf (s : Matrix (Fin N) (Fin N) K) bb F f0.1.1 ⊔ Vf (s : Matrix (Fin N) (Fin N) K) bb F (piI Hp f0.1).1)
            ≤ Module.finrank K (Fin N → K) := Submodule.finrank_le _
          _ = N := Module.finrank_fin_fun K
      rw [hsup, hfinW, hfinW'] at hle
      omega
    exact Or.inr ⟨bdim, f0.1.1.natDegree, AdjoinRoot f0.1.1, inferInstance, inferInstance,
      (hirr f0.1.1 hf0F).natDegree_pos, hb2, hdim2, hcardD', ⟨ψlin⟩⟩




end CFSG.StandardType

