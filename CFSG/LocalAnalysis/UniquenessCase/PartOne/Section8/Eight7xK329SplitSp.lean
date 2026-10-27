module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329KCThree
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329SplitTwist
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329SplitOrder
import CFSG.ClassicalGroups.Symplectic.StandardForm
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeRing
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport
import CFSG.LieType.SemisimpleCentralizers.HeldTwoDimUnitaryBlock
import CFSG.LieType.SemisimpleCentralizers.HeldUCDTransfer
import CFSG.LocalAnalysis.StandardType.GGNbrLSideSpTypeGL
import CFSG.LocalAnalysis.StandardType.GGNbrLSideSpTypeGU
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GCenterQuot
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSp
import CFSG.Adapters.StatedSLPerfect

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open (StatedLieAdmissible StatedScalars StatedSp StatedProj StatedSL StatedLieTag
  StatedSU)

open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCSpIsotypic CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.SemisimpleCentralizers.Held (heldGU heldSU)
open Polynomial
open scoped commutatorElement

open CFSG.Open (StatedLieAdmissible StatedScalars StatedSp StatedProj)
open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCSpIsotypic
open Polynomial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open scoped commutatorElement

private theorem k329s4_P_le_res {n : ℕ} {K : Type} [Field K] [Finite K]
    (x : StatedSp n K)
    (blocks : SpPrimaryBlocks 2 3 3 x (proj n K x))
    (facts : ∀ h : primaryFactors (spEnd x), SpBlockFacts (spForm n K) (spLin n K x) h) :
    ⁅Subgroup.centralizer ({x} : Set (StatedSp n K)),
      Subgroup.centralizer ({x} : Set (StatedSp n K))⁆ ≤ K329Lres x := by
  let C : Subgroup (StatedSp n K) := Subgroup.centralizer ({x} : Set (StatedSp n K))
  let P : Subgroup (StatedSp n K) := ⁅C, C⁆
  let M1 : Subgroup (LinearMap.GeneralLinearGroup K (Fin n ⊕ Fin n → K)) :=
    unitaryCentralizer (spForm n K) (spLin n K x)
  let J : Subgroup (LinearMap.GeneralLinearGroup K (Fin n ⊕ Fin n → K)) :=
    ⨆ a : SpBlockIdx x, specialBlock (spForm n K) (spLin n K x) (a.1 : K[X])
  change P ≤ K329Lres x
  have hmap : P.map (spLin n K) = J := by
    have h1 : C.map (spLin n K) = M1 := (unitaryCentralizer_spForm_eq_map x).symm
    have h2 : ⁅M1, M1⁆ = J := commutator_unitaryCentralizer_eq_iSup blocks facts
    change (⁅C, C⁆).map (spLin n K) = J
    rw [Subgroup.map_commutator, h1, h2]
  have hJperf : ⁅J, J⁆ = J := by
    apply le_antisymm
    · change ⁅J, J⁆ ≤ ⨆ a : SpBlockIdx x, specialBlock (spForm n K) (spLin n K x) (a.1 : K[X])
      rw [Subgroup.commutator_def]
      rw [Subgroup.closure_le]
      rintro g ⟨g₁, hg₁, g₂, hg₂, rfl⟩
      rw [commutatorElement_def]
      exact J.mul_mem (J.mul_mem (J.mul_mem hg₁ hg₂) (J.inv_mem hg₁)) (J.inv_mem hg₂)
    · change (⨆ a : SpBlockIdx x, specialBlock (spForm n K) (spLin n K x) (a.1 : K[X])) ≤ ⁅J, J⁆
      refine iSup_le fun a => ?_
      have hperf : ⁅specialBlock (spForm n K) (spLin n K x) (a.1 : K[X]),
          specialBlock (spForm n K) (spLin n K x) (a.1 : K[X])⁆ =
          specialBlock (spForm n K) (spLin n K x) (a.1 : K[X]) :=
        Subgroup.isPerfect_iff.mp ((facts a.1).quasisimple a.2).1
      calc specialBlock (spForm n K) (spLin n K x) (a.1 : K[X])
          = ⁅specialBlock (spForm n K) (spLin n K x) (a.1 : K[X]),
              specialBlock (spForm n K) (spLin n K x) (a.1 : K[X])⁆ := hperf.symm
        _ ≤ ⁅J, J⁆ := Subgroup.commutator_mono
            (le_iSup (fun b : SpBlockIdx x =>
              specialBlock (spForm n K) (spLin n K x) (b.1 : K[X])) a)
            (le_iSup (fun b : SpBlockIdx x =>
              specialBlock (spForm n K) (spLin n K x) (b.1 : K[X])) a)
  have hle : P ≤ ⁅P, P⁆ := by
    have hmap2 : (⁅P, P⁆).map (spLin n K) = P.map (spLin n K) := by
      rw [Subgroup.map_commutator, hmap, hJperf]
    intro g hg
    have hgz : spLin n K g ∈ (⁅P, P⁆).map (spLin n K) := by
      rw [hmap2]
      exact Subgroup.mem_map.mpr ⟨g, hg, rfl⟩
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hgz
    rw [spLin_injective hyeq] at hy
    exact hy
  have hge : ⁅P, P⁆ ≤ P := by
    rw [Subgroup.commutator_def]
    rw [Subgroup.closure_le]
    rintro g ⟨g₁, hg₁, g₂, hg₂, rfl⟩
    rw [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem hg₁ hg₂) (P.inv_mem hg₁)) (P.inv_mem hg₂)
  have hPperf : ⁅P, P⁆ = P := le_antisymm hge hle
  have hPC : P ≤ C := by
    change ⁅C, C⁆ ≤ C
    rw [Subgroup.commutator_def]
    rw [Subgroup.closure_le]
    rintro g ⟨g₁, hg₁, g₂, hg₂, rfl⟩
    rw [commutatorElement_def]
    exact C.mul_mem (C.mul_mem (C.mul_mem hg₁ hg₂) (C.inv_mem hg₁)) (C.inv_mem hg₂)
  exact k329_perfect_le_res hPC hPperf

private theorem k329s4_commute {n : ℕ} {K : Type} [Field K] [Finite K]
    (x : StatedSp n K)
    (blocks : SpPrimaryBlocks 2 3 3 x (proj n K x))
    (facts : ∀ h : primaryFactors (spEnd x), SpBlockFacts (spForm n K) (spLin n K x) h)
    (hPres : ⁅Subgroup.centralizer ({x} : Set (StatedSp n K)),
      Subgroup.centralizer ({x} : Set (StatedSp n K))⁆ ≤ K329Lres x)
    (R : Subgroup (StatedSp n K))
    (hRc : R ≤ Subgroup.centralizer ({x} : Set (StatedSp n K)))
    (hRcomm : ⁅R, K329Lres x⁆ = ⊥)
    (g : StatedSp n K) (hg : g ∈ R) (g' : StatedSp n K) (hg' : g' ∈ R) :
    g * g' = g' * g := by
  let C : Subgroup (StatedSp n K) := Subgroup.centralizer ({x} : Set (StatedSp n K))
  let P : Subgroup (StatedSp n K) := ⁅C, C⁆
  let J : Subgroup (LinearMap.GeneralLinearGroup K (Fin n ⊕ Fin n → K)) :=
    ⨆ a : SpBlockIdx x, specialBlock (spForm n K) (spLin n K x) (a.1 : K[X])
  have hmap : P.map (spLin n K) = J := by
    have h1 : C.map (spLin n K) = unitaryCentralizer (spForm n K) (spLin n K x) :=
      (unitaryCentralizer_spForm_eq_map x).symm
    have h2 : ⁅unitaryCentralizer (spForm n K) (spLin n K x),
        unitaryCentralizer (spForm n K) (spLin n K x)⁆ = J :=
      commutator_unitaryCentralizer_eq_iSup blocks facts
    change (⁅C, C⁆).map (spLin n K) = J
    rw [Subgroup.map_commutator, h1, h2]
  have hRcent : R ≤ Subgroup.centralizer ((K329Lres x : Subgroup (StatedSp n K)) : Set
      (StatedSp n K)) := (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hRcomm
  have hgl : ∀ {y : StatedSp n K}, y ∈ R → spLin n K y ∈ gl_centralizer (spLin n K x) := by
    intro y hy
    have hyx : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.mp (hRc hy)
    rw [mem_gl_centralizer, commute_iff_eq]
    rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, hyx]
  have hcommBlocks : ∀ a : primaryFactors (spEnd x), 2 ≤ primaryMultiplicity (spEnd x) (a : K[X]) →
      ∀ z ∈ specialBlock (spForm n K) (spLin n K x) (a : K[X]), Commute (spLin n K g) z := by
    intro a ha z hz
    have hzP : z ∈ P.map (spLin n K) := by
      rw [hmap]
      exact le_iSup (fun b : SpBlockIdx x => specialBlock (spForm n K) (spLin n K x)
        (b.1 : K[X])) ⟨a, ha⟩ hz
    obtain ⟨q, hqP, hqz⟩ := Subgroup.mem_map.mp hzP
    have hqres : q ∈ K329Lres x := hPres hqP
    have hgq : Commute g q := by
      rw [commute_iff_eq]
      exact (Subgroup.mem_centralizer_iff.mp (hRcent hg) q hqres).symm
    rw [← hqz]
    exact hgq.map (spLin n K)
  obtain ⟨hzg, hzgc⟩ := mem_center_of_commute_specialBlocks blocks facts (hgl hg) hcommBlocks
  have hz' : (spLin n K g' : Module.End K (Fin n ⊕ Fin n → K)) ∈ commutant (spEnd x) :=
    mem_commutant_of_mem_gl_centralizer (hgl hg')
  have hcenter := (Subalgebra.mem_center_iff.mp hzgc)
    (⟨(spLin n K g' : Module.End K (Fin n ⊕ Fin n → K)), hz'⟩ : commutant (spEnd x))
  have hEnd : (spLin n K g' : Module.End K (Fin n ⊕ Fin n → K)) *
      (spLin n K g : Module.End K (Fin n ⊕ Fin n → K)) =
      (spLin n K g : Module.End K (Fin n ⊕ Fin n → K)) *
      (spLin n K g' : Module.End K (Fin n ⊕ Fin n → K)) := congrArg Subtype.val hcenter
  have hGL : spLin n K g * spLin n K g' = spLin n K g' * spLin n K g := Units.ext hEnd.symm
  have hGL' : spLin n K (g * g') = spLin n K (g' * g) := by
    rw [map_mul, map_mul]
    exact hGL
  exact spLin_injective hGL'

theorem k329_Z3_PSp {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] :
    ∀ ω ∈ K329Zh (StatedSp n K), ω ^ 3 = 1 → ω = 1 := by
  intro ω hω h3
  have : Nonempty (Fin n ⊕ Fin n) := ⟨Sum.inl ⟨0, hn⟩⟩
  have hω' : (ω : GL (Fin n ⊕ Fin n) K) ∈ StatedScalars (Fin n ⊕ Fin n) K := hω
  obtain ⟨c, hc⟩ := hω'
  have hmem : (ω : GL (Fin n ⊕ Fin n) K) ∈ StatedSp n K := ω.2
  have hsqK : (c : K) ^ 2 = 1 := by
    have hform := (CFSG.ClassicalGroups.Symplectic.mem_statedSp_iff_forall _).1 hmem
      (Pi.single (Sum.inl ⟨0, hn⟩) 1) (Pi.single (Sum.inr ⟨0, hn⟩) 1)
    rw [← hc] at hform
    have hx : ∀ v : Fin n ⊕ Fin n → K,
        Matrix.mulVec
          (Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n) c : GL (Fin n ⊕ Fin n) K).val v =
          (c : K) • v := by
      intro v
      ext i
      simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mulVec_diagonal]
    rw [hx, hx] at hform
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul,
      CFSG.ClassicalGroups.Symplectic.spForm_single_inl_inr] at hform
    simpa [sq] using hform
  have hsq : c ^ 2 = 1 := Units.ext (by simpa using hsqK)
  have hc3 : c ^ 3 = 1 := by
    apply k329_scalar_injective (ι := Fin n ⊕ Fin n)
    rw [map_pow, hc, map_one]
    simpa using congrArg Subtype.val h3
  have hc1 : c = 1 := k329_unit_eq_one_of_sq_cube c hsq hc3
  apply Subtype.ext
  rw [← hc, hc1, map_one]
  rfl

private theorem k329s3f_zh_sq {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] :
    ∀ ω ∈ K329Zh (StatedSp n K), ω ^ 2 = 1 := by
  intro ω hω
  have : Nonempty (Fin n ⊕ Fin n) := ⟨Sum.inl ⟨0, hn⟩⟩
  have hω' : (ω : GL (Fin n ⊕ Fin n) K) ∈ StatedScalars (Fin n ⊕ Fin n) K := hω
  obtain ⟨c, hc⟩ := hω'
  have hmem : (ω : GL (Fin n ⊕ Fin n) K) ∈ StatedSp n K := ω.2
  have hsqK : (c : K) ^ 2 = 1 := by
    have hform := (CFSG.ClassicalGroups.Symplectic.mem_statedSp_iff_forall _).1 hmem
      (Pi.single (Sum.inl ⟨0, hn⟩) 1) (Pi.single (Sum.inr ⟨0, hn⟩) 1)
    rw [← hc] at hform
    have hx : ∀ v : Fin n ⊕ Fin n → K,
        Matrix.mulVec
          (Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n) c : GL (Fin n ⊕ Fin n) K).val v =
          (c : K) • v := by
      intro v
      ext i
      simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mulVec_diagonal]
    rw [hx, hx] at hform
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul,
      CFSG.ClassicalGroups.Symplectic.spForm_single_inl_inr] at hform
    simpa [sq] using hform
  apply Subtype.ext
  change ((ω : GL (Fin n ⊕ Fin n) K)) ^ 2 = 1
  rw [← hc, ← map_pow, show c ^ 2 = 1 from Units.ext (by simpa using hsqK), map_one]

private theorem k329s3f_fixSubgroup_conj {G : Type} [Group G] (x : G) :
    fixSubgroup (MulAut.conj x) = Subgroup.centralizer ({x} : Set G) := by
  ext g
  rw [mem_fixSubgroup, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g * x = (x * g * x⁻¹) * x := by rw [h]
      _ = x * g := by group
  · intro h
    calc x * g * x⁻¹ = (g * x) * x⁻¹ := by rw [h]
      _ = g := by group

private theorem k329s3f_reduce {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] (x : StatedSp n K)
    (hxZ : x ∉ K329Zh (StatedSp n K)) (hx3 : x ^ 3 ∈ K329Zh (StatedSp n K)) :
    ∃ y : StatedSp n K, y ^ 3 = 1 ∧ y ∉ K329Zh (StatedSp n K) ∧
      Subgroup.centralizer ({y} : Set (StatedSp n K)) =
        Subgroup.centralizer ({x} : Set (StatedSp n K)) := by
  let ε : StatedSp n K := x ^ 3
  have hεmem : ε ∈ K329Zh (StatedSp n K) := hx3
  have hεsq : ε ^ 2 = 1 := k329s3f_zh_sq hn ε hεmem
  have hεc : ∀ g : StatedSp n K, ε * g = g * ε := fun g =>
    (Subgroup.mem_center_iff.mp (k329_Zh_le_center (StatedSp n K) hεmem) g).symm
  refine ⟨ε * x, ?_, ?_, ?_⟩
  · have hcx : Commute ε x := hεc x
    rw [hcx.mul_pow]
    have hε3 : ε ^ 3 = ε := by
      rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, hεsq, one_mul]
    have hx3eq : x ^ 3 = ε := rfl
    rw [hε3, hx3eq, ← sq]
    exact hεsq
  · intro hy
    apply hxZ
    have hεinv : ε⁻¹ ∈ K329Zh (StatedSp n K) := Subgroup.inv_mem _ hεmem
    have hmem : ε⁻¹ * (ε * x) ∈ K329Zh (StatedSp n K) := Subgroup.mul_mem _ hεinv hy
    rwa [inv_mul_cancel_left] at hmem
  · ext g
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h1 : ε * (g * x) = ε * (x * g) := by
        calc ε * (g * x) = (ε * g) * x := by group
          _ = (g * ε) * x := by rw [hεc g]
          _ = g * (ε * x) := by group
          _ = (ε * x) * g := h
          _ = ε * (x * g) := by group
      exact mul_left_cancel h1
    · intro h
      calc g * (ε * x) = (g * ε) * x := by group
        _ = (ε * g) * x := by rw [← hεc g]
        _ = ε * (g * x) := by group
        _ = ε * (x * g) := by rw [h]
        _ = (ε * x) * g := by group

private theorem k329s3f_perf_cond {s : ℕ} {K : Type} [Field K] [Finite K]
    (hs : 2 ≤ s) (hne : (s, Nat.card K) ≠ (2, 2)) :
    (∃ t : Finset K, t.card = 4) ∨ (Nat.card K = 3 ∧ 2 ≤ s) ∨ (Nat.card K = 2 ∧ 3 ≤ s) := by
  have := Fintype.ofFinite K
  have h2 : 2 ≤ Nat.card K := Nat.succ_le_of_lt Finite.one_lt_card
  rcases Nat.lt_or_ge (Nat.card K) 4 with h4 | h4
  · rcases (show Nat.card K = 2 ∨ Nat.card K = 3 by omega) with hK | hK
    · right; right
      refine ⟨hK, ?_⟩
      by_contra hlt
      exact hne (Prod.ext (by omega) hK)
    · exact Or.inr (Or.inl ⟨hK, hs⟩)
  · left
    have h4' : 4 ≤ (Finset.univ : Finset K).card := by
      simpa [Nat.card_eq_fintype_card] using h4
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq h4'
    exact ⟨t, ht⟩

private theorem k329s3f_centerQuot_statedSp {X : Type} [Group X] {K : Type} [Field K] [Finite K]
    {s : ℕ} (hs : 2 ≤ s) (hne : (s, Nat.card K) ≠ (2, 2)) (e : X ≃* StatedSp s K) :
    Nonempty (X ⧸ Subgroup.center X ≃* StatedProj (StatedSp s K)) := by
  have := Fintype.ofFinite K
  have hcond := k329s3f_perf_cond hs hne
  have hcond' : (Infinite K ∨ 4 ≤ Nat.card K) ∨ (Nat.card K = 3 ∧ 2 ≤ s) ∨
      (Nat.card K = 2 ∧ 3 ≤ s) := by
    rcases hcond with ⟨t, ht⟩ | h | h
    · left; right
      have hle := Finset.card_le_univ t
      rw [ht] at hle
      rwa [← Nat.card_eq_fintype_card] at hle
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have : Group.IsPerfect (StatedSp s K) :=
    CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp s K hcond
  have : IsSimpleGroup (StatedProj (StatedSp s K)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K s (by omega) hcond'
  have hcenter : Subgroup.center (StatedSp s K) = K329Zh (StatedSp s K) :=
    CFSG.LieType.Universal.Spin.center_eq_statedScalars_subgroupOf
  refine ⟨(QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).trans ?_⟩
  exact QuotientGroup.quotientMulEquivOfEq hcenter

private theorem k329s3f_isSolvable_gl_of_le_one {E : Type*} [Field E] {m : ℕ} (hm : m ≤ 1) :
    Group.IsSolvable (Matrix.GeneralLinearGroup (Fin m) E) := by
  refine Group.isSolvable_of_comm fun a b => Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hm with rfl | rfl
  · exact Matrix.ext fun i => i.elim0
  · ext i j
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_one, Fin.sum_univ_one,
      Subsingleton.elim i 0, Subsingleton.elim j 0]
    exact mul_comm _ _

private theorem k329s3f_equiv_of_range {G X : Type} [Group G] [Group X] {A : Subgroup G}
    (ψ : X →* G) (hψ : Function.Injective ψ) (h : ψ.range = A) :
    Nonempty (↥A ≃* X) :=
  ⟨((Subgroup.equivMapOfInjective (⊤ : Subgroup X) ψ hψ).trans
      (MulEquiv.subgroupCongr (by rw [Subgroup.map_top, h]))).symm.trans Subgroup.topEquiv⟩

private theorem k329s3f_four_le_card {K : Type} [Field K] [Finite K]
    (hq : CFSG.IsQuasisimple ↥(commutator (StatedSp 1 K))) : 4 ≤ Nat.card K := by
  by_contra hlt
  have h2 : 2 ≤ Nat.card K := Nat.succ_le_of_lt Finite.one_lt_card
  have hcard : Nat.card K = 2 ∨ Nat.card K = 3 := by omega
  have : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) K) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable K hcard
  have : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) K) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin 2) K →* Matrix.GeneralLinearGroup (Fin 2) K))
      Matrix.SpecialLinearGroup.toGL_injective
  have : Group.IsSolvable (StatedSp 1 K) :=
    Group.isSolvable_of_surjective (f := (longBlockEquivOne K).toMonoidHom)
      (longBlockEquivOne K).surjective
  have : Group.IsSolvable ↥(commutator (StatedSp 1 K)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (commutator (StatedSp 1 K)).subtype) Subtype.val_injective
  have : Group.IsPerfect ↥(commutator (StatedSp 1 K)) := hq.1
  have : Nontrivial ↥(commutator (StatedSp 1 K)) :=
    CFSG.LocalCores.isQuasisimple_nontrivial hq
  exact Group.IsPerfect.not_isSolvable ↥(commutator (StatedSp 1 K)) inferInstance

private theorem k329s3f_lieModel_commutator_GL {m r e : ℕ} {K : Type} [Field K] [Finite K]
    (hr : r.Prime) (he : 1 ≤ e) (hK : Nat.card K = r ^ e)
    (hq : CFSG.IsQuasisimple ↥(commutator (Matrix.GeneralLinearGroup (Fin m) K))) :
    CFSG.Blueprint.LieModel
      (↥(commutator (Matrix.GeneralLinearGroup (Fin m) K)) ⧸
        Subgroup.center ↥(commutator (Matrix.GeneralLinearGroup (Fin m) K))) .PSL m r e := by
  classical
  have := Fintype.ofFinite K
  have : Fact r.Prime := ⟨hr⟩
  have hnotSolv : ¬ Group.IsSolvable (Matrix.GeneralLinearGroup (Fin m) K) := by
    intro hs
    have := hs
    have : Group.IsSolvable ↥(commutator (Matrix.GeneralLinearGroup (Fin m) K)) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (commutator (Matrix.GeneralLinearGroup (Fin m) K)).subtype) Subtype.val_injective
    have : Group.IsPerfect ↥(commutator (Matrix.GeneralLinearGroup (Fin m) K)) := hq.1
    have : Nontrivial ↥(commutator (Matrix.GeneralLinearGroup (Fin m) K)) :=
      CFSG.LocalCores.isQuasisimple_nontrivial hq
    exact Group.IsPerfect.not_isSolvable
      ↥(commutator (Matrix.GeneralLinearGroup (Fin m) K)) inferInstance
  have hm2 : 2 ≤ m := by
    by_contra hlt
    have : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin m) K) :=
      k329s3f_isSolvable_gl_of_le_one (E := K) (by omega)
    exact hnotSolv inferInstance
  have hcond : 3 ≤ m ∨ ∃ t : Finset K, t.card = 4 := by
    rcases Nat.lt_or_ge m 3 with h3 | h3
    · have hm : m = 2 := by omega
      subst hm
      right
      by_contra hno
      have hle : Nat.card K ≤ 3 := by
        by_contra hlt
        have h4 : 4 ≤ Nat.card K := by omega
        have h4' : 4 ≤ (Finset.univ : Finset K).card := by
          simpa [Nat.card_eq_fintype_card] using h4
        obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq h4'
        exact hno ⟨t, ht⟩
      have h2 : 2 ≤ Nat.card K := Nat.succ_le_of_lt Finite.one_lt_card
      have hcard : Nat.card K = 2 ∨ Nat.card K = 3 := by omega
      have : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) K) :=
        CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable K hcard
      exact hnotSolv inferInstance
    · exact Or.inl h3
  have hcomm : commutator (Matrix.GeneralLinearGroup (Fin m) K) = StatedSL m K :=
    CFSG.StandardType.GGNbrLSideKit.commutator_generalLinear_eq_statedSL hm2 hcond
  obtain ⟨eSL⟩ := k329s3f_equiv_of_range (Matrix.SpecialLinearGroup.toGL)
    Matrix.SpecialLinearGroup.toGL_injective
    (CFSG.Open.StatedAPI.statedSL_eq_range_toGL m K).symm
  have eiso : ↥(commutator (Matrix.GeneralLinearGroup (Fin m) K)) ≃*
      Matrix.SpecialLinearGroup (Fin m) K :=
    (MulEquiv.subgroupCongr hcomm).trans eSL
  obtain ⟨eZ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_sl m eiso
  have h4K : 3 ≤ m ∨ 4 ≤ Nat.card K := by
    rcases hcond with h3 | ⟨t, ht⟩
    · exact Or.inl h3
    · right
      have hle := Finset.card_le_univ t
      rw [ht] at hle
      rwa [← Nat.card_eq_fintype_card] at hle
  have hadm : StatedLieAdmissible .PSL m r e := by
    refine ⟨hr, he, hm2, ?_, ?_⟩
    · intro h
      obtain ⟨hm, h2⟩ := Prod.mk.inj h
      rcases h4K with h3 | h4
      · omega
      · rw [hK, h2] at h4; omega
    · intro h
      obtain ⟨hm, h3⟩ := Prod.mk.inj h
      rcases h4K with h3' | h4
      · omega
      · rw [hK, h3] at h4; omega
  exact Or.inl ⟨by decide, ⟨hadm, K, inferInstance, inferInstance, hK, ⟨eZ⟩⟩⟩

private theorem k329s3f_typeSp {s r e : ℕ} {K : Type} [Field K] [Finite K]
    (hr : r.Prime) (he : 1 ≤ e) (hK : Nat.card K = r ^ e)
    (hq : CFSG.IsQuasisimple ↥(commutator (StatedSp s K))) :
    (∃ (t : StatedLieTag) (m : ℕ), ((t = .PSp ∧ m = s) ∨ (t = .PSL ∧ m = 2)) ∧
        CFSG.Blueprint.LieModel
          (↥(commutator (StatedSp s K)) ⧸
            Subgroup.center ↥(commutator (StatedSp s K))) t m r e) ∨
      Nat.card (↥(commutator (StatedSp s K)) ⧸
        Subgroup.center ↥(commutator (StatedSp s K))) ≤ 360 := by
  classical
  have := Fintype.ofFinite K
  have : Fact r.Prime := ⟨hr⟩
  rcases Nat.eq_zero_or_pos s with rfl | hspos
  · exfalso
    have hcard : Nat.card (StatedSp 0 K) = 1 := by
      rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp]
      simp
    have : Subsingleton (StatedSp 0 K) := (Nat.card_eq_one_iff_unique.mp hcard).1
    have : Subsingleton ↥(commutator (StatedSp 0 K)) := inferInstance
    have : Nontrivial ↥(commutator (StatedSp 0 K)) :=
      CFSG.LocalCores.isQuasisimple_nontrivial hq
    obtain ⟨a, b, hab⟩ := exists_pair_ne ↥(commutator (StatedSp 0 K))
    exact hab (Subsingleton.elim a b)
  · by_cases h1 : s = 1
    · subst h1
      have h4 : 4 ≤ Nat.card K := k329s3f_four_le_card hq
      have h4' : 4 ≤ Fintype.card K := by rwa [Nat.card_eq_fintype_card] at h4
      obtain ⟨t4, -, ht4⟩ := Finset.exists_subset_card_eq h4'
      have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K) :=
        (CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_SL (F := K) (m := 2) le_rfl
          (Or.inr ⟨t4, ht4⟩)).1
      have hperfSp : Group.IsPerfect (StatedSp 1 K) :=
        Group.IsPerfect.ofSurjective (f := (longBlockEquivOne K).toMonoidHom)
          (longBlockEquivOne K).surjective
      have htop : commutator (StatedSp 1 K) = ⊤ := hperfSp.commutator_eq_top
      have eTop : ↥(commutator (StatedSp 1 K)) ≃* StatedSp 1 K :=
        (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
      obtain ⟨eZc⟩ :=
        CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_of_mulEquiv eTop
      obtain ⟨eZ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_sl 2
        (X := StatedSp 1 K) (longBlockEquivOne K).symm
      have eComb : ↥(commutator (StatedSp 1 K)) ⧸
          Subgroup.center ↥(commutator (StatedSp 1 K)) ≃* StatedProj (StatedSL 2 K) :=
        eZc.trans eZ
      have hadm : StatedLieAdmissible .PSL 2 r e := by
        refine ⟨hr, he, le_rfl, ?_, ?_⟩
        · intro h
          obtain ⟨-, h2⟩ := Prod.mk.inj h
          rw [hK] at h4
          omega
        · intro h
          obtain ⟨-, h3⟩ := Prod.mk.inj h
          rw [hK, h3] at h4
          omega
      refine Or.inl ⟨.PSL, 2, Or.inr ⟨rfl, rfl⟩, ?_⟩
      exact Or.inl ⟨by decide, ⟨hadm, K, inferInstance, inferInstance, hK, ⟨eComb⟩⟩⟩
    · have hs2 : 2 ≤ s := by omega
      by_cases hspecial : s = 2 ∧ Nat.card K = 2
      · obtain ⟨rfl, hK2⟩ := hspecial
        right
        have hfin : Module.finrank K (Fin 2 ⊕ Fin 2 → K) = 4 := by
          rw [Module.finrank_fintype_fun_eq_card]
          decide
        obtain ⟨e4⟩ := CFSG.RankThree.PartOne.nonempty_mulEquiv_sympFour hK2
          (spForm_isAlt (r := 2) (K := K)) (spForm_nondegenerate (r := 2) (K := K)) hfin
        let eSp := ((MonoidHom.ofInjective (spLin_injective (r := 2) (K := K))).trans
          (MulEquiv.subgroupCongr (range_spLin (r := 2) (K := K)))).trans e4
        obtain ⟨eA6⟩ := (CFSG.RankThree.PartOne.derived_alt_index_of_mulEquiv_sympFour eSp).1
        have hA6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
          have h : 2 * Nat.card (alternatingGroup (Fin 6)) = 720 := by
            rw [two_mul_nat_card_alternatingGroup, Nat.card_eq_fintype_card,
              Fintype.card_perm, Fintype.card_fin]
            norm_num
          omega
        calc Nat.card (↥(commutator (StatedSp 2 K)) ⧸
              Subgroup.center ↥(commutator (StatedSp 2 K)))
            ≤ Nat.card ↥(commutator (StatedSp 2 K)) :=
              Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
          _ = Nat.card (alternatingGroup (Fin 6)) := Nat.card_congr eA6.toEquiv
          _ = 360 := hA6
      · have hne : ¬ (s = 2 ∧ Nat.card K = 2) := hspecial
        have hne' : (s, Fintype.card K) ≠ (2, 2) := by
          intro h
          obtain ⟨h1, h2⟩ := Prod.mk.inj h
          exact hne ⟨h1, by rw [Nat.card_eq_fintype_card]; exact h2⟩
        have htop : commutator (StatedSp s K) = ⊤ :=
          (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.spFactorFacts_holds
            K s hs2 hne').perfect
        have eTop : ↥(commutator (StatedSp s K)) ≃* StatedSp s K :=
          (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
        obtain ⟨eZc⟩ :=
          CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_of_mulEquiv eTop
        obtain ⟨eZ⟩ := k329s3f_centerQuot_statedSp hs2
          (by rw [Nat.card_eq_fintype_card (α := K)]; exact hne') (MulEquiv.refl _)
        have eComb : ↥(commutator (StatedSp s K)) ⧸
            Subgroup.center ↥(commutator (StatedSp s K)) ≃* StatedProj (StatedSp s K) :=
          eZc.trans eZ
        have hadm : StatedLieAdmissible .PSp s r e := by
          refine ⟨hr, he, hs2, ?_⟩
          intro h
          obtain ⟨h1, h2⟩ := Prod.mk.inj h
          exact hne ⟨h1, by rw [hK]; exact h2⟩
        refine Or.inl ⟨.PSp, s, Or.inl ⟨rfl, rfl⟩, ?_⟩
        exact Or.inl ⟨by decide, ⟨hadm, K, inferInstance, inferInstance, hK, ⟨eComb⟩⟩⟩

private theorem k329s3f_commutator_le_heldSU {r : ℕ} {E : Type} [Field E] {τ : E ≃+* E}
    {hτ : ∀ y, τ (τ y) = y} :
    ⁅(heldGU r E τ hτ : Subgroup (GL (Fin r) E)), heldGU r E τ hτ⁆ ≤ heldSU r E τ hτ := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  exact CFSG.LieType.SemisimpleCentralizers.Held.commutatorElement_mem_heldSU hx hy

private noncomputable def k329s3f_commutator_equiv_self {G : Type} [Group G] (A : Subgroup G) :
    ↥(commutator ↥A) ≃* ↥⁅A, A⁆ :=
  (Subgroup.equivMapOfInjective (commutator ↥A) A.subtype Subtype.val_injective).trans
    (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator A))

private theorem k329s3f_lieModel_commutator_heldGU {m p k : ℕ} {M : Type} [Field M] [Finite M]
    {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y}
    (hp : p.Prime) (hk : 1 ≤ k) (hcard : Nat.card M = (p ^ k) ^ 2)
    (hτQ : ∀ y, τ y = y ^ (p ^ k))
    (hq : CFSG.IsQuasisimple ↥(commutator (heldGU m M τ hτ))) :
    ∃ (t : StatedLieTag) (m' : ℕ), ((t = .PSU ∧ m' = m) ∨ (t = .PSL ∧ m' = 2)) ∧
      CFSG.Blueprint.LieModel
        (↥(commutator (heldGU m M τ hτ)) ⧸
          Subgroup.center ↥(commutator (heldGU m M τ hτ))) t m' p k := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : CharP M p := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := p) (f := k) hcard
  have hq_notsolv : ¬ Group.IsSolvable ↥(commutator (heldGU m M τ hτ)) := by
    have : Nontrivial ↥(commutator (heldGU m M τ hτ)) :=
      CFSG.LocalCores.isQuasisimple_nontrivial hq
    have : Group.IsPerfect ↥(commutator (heldGU m M τ hτ)) := hq.1
    exact Group.IsPerfect.not_isSolvable ↥(commutator (heldGU m M τ hτ))
  have hm2 : 2 ≤ m := by
    by_contra hlt
    have hmle : m ≤ 1 := by omega
    have hsolSU : Group.IsSolvable ↥(heldSU m M τ hτ) := by
      have hcomm : ∀ a b : ↥(heldSU m M τ hτ), a * b = b * a := by
        intro a b
        exact Subtype.ext (CFSG.LieType.SemisimpleCentralizers.Held.mul_comm_GL_of_le_one
          (M := M) hmle (a : GL (Fin m) M) (b : GL (Fin m) M))
      exact Group.isSolvable_of_comm hcomm
    have := hsolSU
    have hle := k329s3f_commutator_le_heldSU (r := m) (E := M) (τ := τ) (hτ := hτ)
    have : Group.IsSolvable ↥⁅(heldGU m M τ hτ : Subgroup (GL (Fin m) M)), heldGU m M τ hτ⁆ :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
        (Subgroup.inclusion_injective hle)
    exact hq_notsolv (Group.isSolvable_of_surjective
      (f := (k329s3f_commutator_equiv_self (heldGU m M τ hτ)).symm.toMonoidHom)
      (k329s3f_commutator_equiv_self (heldGU m M τ hτ)).symm.surjective)
  have hbad : ¬ (m = 3 ∧ p ^ k = 2) := by
    rintro ⟨rfl, hpk⟩
    have hp2 : p = 2 := by
      have h : p ∣ 2 := by rw [← hpk]; exact dvd_pow_self p (by omega)
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h
    subst hp2
    have hk1 : k = 1 := by
      have h : (2 : ℕ) ^ k = 2 ^ 1 := by rw [pow_one]; exact hpk
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h
    subst hk1
    have hcard31 : Nat.card M = (2 ^ 1) ^ 2 := by simpa using hcard
    have h216 : Nat.card (StatedSU 3 (2 ^ 1) M) = 216 := by
      rw [CFSG.RankThree.PartTwo.Sec8.Item87Proof.card_statedSU_three_two hcard31]
      norm_num
    have hsol : Group.IsSolvable ↥(heldSU 3 M τ hτ) := by
      rw [CFSG.LieType.SemisimpleCentralizers.Held.hct_heldSU_eq_statedSU (a := 3) (Q := 2 ^ 1) hτQ]
      exact CFSG.LieType.SemisimpleCentralizers.Held.hct_isSolvable_of_natCard_eq
        (p := 2) (q := 3) (a := 3) (b := 3) Nat.prime_two Nat.prime_three (by norm_num)
        (by rw [h216]; norm_num)
    have hle := k329s3f_commutator_le_heldSU (r := 3) (E := M) (τ := τ) (hτ := hτ)
    have : Group.IsSolvable ↥⁅(heldGU 3 M τ hτ : Subgroup (GL (Fin 3) M)), heldGU 3 M τ hτ⁆ :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
        (Subgroup.inclusion_injective hle)
    exact hq_notsolv (Group.isSolvable_of_surjective
      (f := (k329s3f_commutator_equiv_self (heldGU 3 M τ hτ)).symm.toMonoidHom)
      (k329s3f_commutator_equiv_self (heldGU 3 M τ hτ)).symm.surjective)
  have hQ4or : 4 ≤ p ^ k ∨ 3 ≤ m := by
    by_cases hm3 : 3 ≤ m
    · exact Or.inr hm3
    · left
      have hm : m = 2 := by omega
      subst hm
      by_contra hlt
      have hle3 : p ^ k ≤ 3 := by omega
      have hQ2 : p ^ k = 2 ∨ p ^ k = 3 := by
        have h1 : 1 ≤ p ^ k := one_le_pow₀ hp.one_le
        have h2 : 2 ≤ p ^ k := by
          rcases Nat.eq_zero_or_pos k with rfl | hkpos
          · omega
          · exact hp.two_le.trans (Nat.le_self_pow (by omega) p)
        omega
      have hsolSU : Group.IsSolvable ↥(heldSU 2 M τ hτ) := by
        obtain ⟨eSL⟩ := CFSG.LieType.SemisimpleCentralizers.Held.nonempty_heldSU_two_mulEquiv_statedSL
          (hτ := hτ) (p := p) (k := k) (Q := p ^ k) rfl hcard hτQ
        have : Group.IsSolvable (StatedSL 2 (CFSG.LieType.Steinberg.fixedSubfield M p k)) := by
          rcases hQ2 with h | h
          · have hF : Nat.card (CFSG.LieType.Steinberg.fixedSubfield M p k) = 2 := by
              rw [CFSG.LieType.Steinberg.card_fixedSubfield hcard]; exact h
            have : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2)
                (CFSG.LieType.Steinberg.fixedSubfield M p k)) :=
              CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable
                _ (Or.inl hF)
            have : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2)
                (CFSG.LieType.Steinberg.fixedSubfield M p k)) :=
              Group.isSolvable_of_isSolvable_injective
                (f := (Matrix.SpecialLinearGroup.toGL :
                  Matrix.SpecialLinearGroup (Fin 2) (CFSG.LieType.Steinberg.fixedSubfield M p k) →*
                    Matrix.GeneralLinearGroup (Fin 2) (CFSG.LieType.Steinberg.fixedSubfield M p k)))
                Matrix.SpecialLinearGroup.toGL_injective
            exact Group.isSolvable_of_surjective
              (f := (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2
                (CFSG.LieType.Steinberg.fixedSubfield M p k)).toMonoidHom)
              (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2
                (CFSG.LieType.Steinberg.fixedSubfield M p k)).surjective
          · have hF : Nat.card (CFSG.LieType.Steinberg.fixedSubfield M p k) = 3 := by
              rw [CFSG.LieType.Steinberg.card_fixedSubfield hcard]; exact h
            have : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2)
                (CFSG.LieType.Steinberg.fixedSubfield M p k)) :=
              CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable
                _ (Or.inr hF)
            have : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2)
                (CFSG.LieType.Steinberg.fixedSubfield M p k)) :=
              Group.isSolvable_of_isSolvable_injective
                (f := (Matrix.SpecialLinearGroup.toGL :
                  Matrix.SpecialLinearGroup (Fin 2) (CFSG.LieType.Steinberg.fixedSubfield M p k) →*
                    Matrix.GeneralLinearGroup (Fin 2) (CFSG.LieType.Steinberg.fixedSubfield M p k)))
                Matrix.SpecialLinearGroup.toGL_injective
            exact Group.isSolvable_of_surjective
              (f := (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2
                (CFSG.LieType.Steinberg.fixedSubfield M p k)).toMonoidHom)
              (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2
                (CFSG.LieType.Steinberg.fixedSubfield M p k)).surjective
        exact Group.isSolvable_of_surjective (f := eSL.symm.toMonoidHom) eSL.symm.surjective
      have := hsolSU
      have hle := k329s3f_commutator_le_heldSU (r := 2) (E := M) (τ := τ) (hτ := hτ)
      have : Group.IsSolvable ↥⁅(heldGU 2 M τ hτ : Subgroup (GL (Fin 2) M)), heldGU 2 M τ hτ⁆ :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
          (Subgroup.inclusion_injective hle)
      exact hq_notsolv (Group.isSolvable_of_surjective
        (f := (k329s3f_commutator_equiv_self (heldGU 2 M τ hτ)).symm.toMonoidHom)
        (k329s3f_commutator_equiv_self (heldGU 2 M τ hτ)).symm.surjective)
  have ham : (m, p ^ k) ≠ (3, 2) := by
    intro h
    exact hbad ⟨(Prod.mk.inj h).1, (Prod.mk.inj h).2⟩
  have hperfSU : Group.IsPerfect ↥(heldSU m M τ hτ) := by
    rcases Nat.lt_or_ge m 3 with hm3 | hm3
    · have hm : m = 2 := by omega
      subst hm
      have hQ4 : 4 ≤ p ^ k := by rcases hQ4or with h | h <;> omega
      obtain ⟨eSL⟩ := CFSG.LieType.SemisimpleCentralizers.Held.nonempty_heldSU_two_mulEquiv_statedSL
        (hτ := hτ) (p := p) (k := k) (Q := p ^ k) rfl hcard hτQ
      have hF : 4 ≤ Nat.card (CFSG.LieType.Steinberg.fixedSubfield M p k) := by
        rw [CFSG.LieType.Steinberg.card_fixedSubfield hcard]; exact hQ4
      have : Group.IsPerfect (StatedSL 2 (CFSG.LieType.Steinberg.fixedSubfield M p k)) :=
        CFSG.Open.StatedAPI.isPerfect_statedSL_two_of_four_le_card hF
      exact Group.IsPerfect.ofSurjective (f := eSL.symm.toMonoidHom) eSL.symm.surjective
    · rw [CFSG.LieType.SemisimpleCentralizers.Held.hct_heldSU_eq_statedSU (a := m) (Q := p ^ k) hτQ]
      exact CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hcard hm3 ham
  have hcomm_eq := CFSG.StandardType.GGNbrLSideKit.commutator_heldGU_eq_heldSU_of_isPerfect
    (r := m) (E := M) (τ := τ) (hτ := hτ) hperfSU
  have e : ↥(commutator (heldGU m M τ hτ)) ≃* ↥(heldSU m M τ hτ) :=
    (k329s3f_commutator_equiv_self (heldGU m M τ hτ)).trans
      (MulEquiv.subgroupCongr hcomm_eq)
  obtain ⟨eZ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_of_mulEquiv e
  rcases Nat.lt_or_ge m 3 with hm3 | hm3
  ·
    have hm : m = 2 := by omega
    subst hm
    have hQ4 : 4 ≤ p ^ k := by rcases hQ4or with h | h <;> omega
    obtain ⟨ψ⟩ := CFSG.LieType.SemisimpleCentralizers.Held.nonempty_quotientCenter_heldSU_two_equiv_statedProj
      (hτ := hτ) (p := p) (k := k) (Q := p ^ k) rfl hcard hτQ
    refine ⟨.PSL, 2, Or.inr ⟨rfl, rfl⟩, Or.inl ⟨by decide, ?_⟩⟩
    refine ⟨⟨hp, hk, le_rfl, ?_, ?_⟩,
      CFSG.LieType.Steinberg.fixedSubfield M p k, inferInstance, inferInstance,
      CFSG.LieType.Steinberg.card_fixedSubfield hcard, ⟨eZ.trans ψ⟩⟩
    · intro h
      exact absurd (Prod.mk.inj h).2 (by omega)
    · intro h
      have h3 : p ^ k = 3 := (Prod.mk.inj h).2
      have hdvd : p ∣ p ^ k := dvd_pow_self p (by omega)
      rw [h3] at hdvd
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hdvd
      omega
  ·
    have hEq : heldSU m M τ hτ = StatedSU m (p ^ k) M :=
      CFSG.LieType.SemisimpleCentralizers.Held.hct_heldSU_eq_statedSU (a := m) (Q := p ^ k) hτQ
    have hperfSU' : Group.IsPerfect (StatedSU m (p ^ k) M) := by rw [← hEq]; exact hperfSU
    have hsimpleSU' : IsSimpleGroup (StatedProj (StatedSU m (p ^ k) M)) :=
      CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU M p k hcard m hm3 ham
    have hcenter : Subgroup.center (StatedSU m (p ^ k) M) =
        (StatedScalars (Fin m) M).subgroupOf (StatedSU m (p ^ k) M) :=
      (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU hperfSU' hsimpleSU').2
    have eSU : ↥(heldSU m M τ hτ) ⧸ Subgroup.center ↥(heldSU m M τ hτ) ≃*
        StatedProj (StatedSU m (p ^ k) M) := by
      rw [hEq]
      exact QuotientGroup.quotientMulEquivOfEq hcenter
    refine ⟨.PSU, m, Or.inl ⟨rfl, rfl⟩, Or.inl ⟨by decide, ?_⟩⟩
    exact ⟨⟨hp, hk, hm3, ham⟩, M, inferInstance, inferInstance, hcard, ⟨eZ.trans eSU⟩⟩

private theorem k329s3f_commutator_equiv {G B : Type*} [Group G] [Group B] {A : Subgroup G}
    (φ : ↥A ≃* B) : Nonempty (↥⁅A, A⁆ ≃* ↥(commutator B)) := by
  have e1 : ↥(commutator ↥A) ≃* ↥⁅A, A⁆ :=
    (Subgroup.equivMapOfInjective (commutator ↥A) A.subtype Subtype.val_injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator A))
  exact ⟨e1.symm.trans (MulEquiv.commutatorCongr φ)⟩

private theorem k329s3f_orbit {n r e : ℕ} (hadm : StatedLieAdmissible .PSp n r e) (hr : r ≠ 3)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = r ^ e) {x : StatedSp n K} (hx3 : x ^ 3 = 1)
    (hblocks : SpPrimaryBlocks r e 3 x (proj n K x))
    (O : reciprocalOrbits (spEnd x))
    (hQ : CFSG.IsQuasisimple ↥⁅spSupported x (O : Set K[X]), spSupported x (O : Set K[X])⁆)
    (hcard : Nat.card (↥⁅spSupported x (O : Set K[X]), spSupported x (O : Set K[X])⁆ ⧸
      Subgroup.center ↥⁅spSupported x (O : Set K[X]), spSupported x (O : Set K[X])⁆) = 504) :
    r ^ e = 8 := by
  classical
  have hrprime : r.Prime := hadm.1
  have : Fact r.Prime := ⟨hrprime⟩
  have he1 : 1 ≤ e := hadm.2.1
  have hn1 : 1 ≤ n := by have := hadm.2.2.1; omega
  have hchar : CharP K r := CFSG.LieType.BorelTits.charP_of_natCard_eq (p := r) (f := e) hK
  have := hchar
  have hpK : (3 : K) ≠ 0 := by
    intro h
    have h3 : r ∣ 3 := (CharP.cast_eq_zero_iff K r 3).mp h
    exact hr ((Nat.prime_dvd_prime_iff_eq hrprime Nat.prime_three).mp h3)
  have hsq : Squarefree (minpoly K (spEnd x)) := (altPrimaryData_spLin (p := 3) hpK hx3).squarefree
  obtain ⟨h, hh, hO⟩ := O.2
  have hO' : (O : Set K[X]) = ({h, reciprocalPolynomial h} : Set K[X]) := hO.symm
  rw [hO'] at hQ hcard
  by_cases h1 : (h : K[X]) = X - 1
  ·
    have hmem : (X - 1 : K[X]) ∈ primaryFactors (spEnd x) := by rwa [h1] at hh
    have hO2 : ({h, reciprocalPolynomial h} : Set K[X]) = {X - 1} := by
      rw [h1, CFSG.RankThree.Classical.reciprocalPolynomial_X_sub_one, Set.pair_eq_singleton]
    rw [hO2] at hQ hcard
    obtain ⟨φ, -⟩ := hblocks.fixedFactor hmem
    obtain ⟨s, hs, ⟨e⟩⟩ := CFSG.RankThree.PartOne.KCSpIsotypic.exists_mulEquiv_sesqUnitaryGroup_statedSp
      (B := (spForm n K).restrict (primaryComponent (spEnd x) (X - 1)))
      (fun v => spForm_isAlt (v : Fin n ⊕ Fin n → K)) hblocks.fixed_nondegenerate
    have hs1 : 1 ≤ s := by
      have : Nontrivial (primaryComponent (spEnd x) (X - 1)) :=
        Submodule.nontrivial_iff_ne_bot.mpr (primaryComponent_ne_bot hsq hmem)
      have := Module.finrank_pos (R := K) (M := primaryComponent (spEnd x) (X - 1))
      omega
    let eA : spSupported x {X - 1} ≃* StatedSp s K := φ.trans e
    obtain ⟨eD⟩ := k329s3f_commutator_equiv eA
    have hQ' : CFSG.IsQuasisimple ↥(commutator (StatedSp s K)) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv eD hQ
    have hcard' : Nat.card (↥(commutator (StatedSp s K)) ⧸
        Subgroup.center ↥(commutator (StatedSp s K))) = 504 := by
      rw [← Nat.card_congr (QuotientGroup.congr _ _ eD (Subgroup.map_center_eq eD)).toEquiv]
      exact hcard
    rcases k329s3f_typeSp hrprime he1 hK hQ' with ⟨t, m, htm, hmodel⟩ | hle
    · rcases htm with ⟨ht, hm⟩ | ⟨ht, hm⟩
      · subst ht
        rw [hm] at hmodel
        exact absurd (k329_S2_order504 (by omega : s ≠ 0) hmodel hcard').1 (by decide)
      · subst ht; subst hm
        exact (k329_S2_order504 (by norm_num : (2 : ℕ) ≠ 0) hmodel hcard').2.2
    · rw [hcard'] at hle
      exact absurd hle (by norm_num)
  · by_cases hself : reciprocalPolynomial (h : K[X]) = (h : K[X])
    ·
      have : Fact (Irreducible (h : K[X])) := ⟨irreducible_of_mem_primaryFactors hh⟩
      obtain ⟨d, hdeg, hpd, σ, hσq, hσne, hσinv, hσroot, hsmul, hE, hbar, Hf, hHf, hHfl, -,
        ⟨eb, heb⟩, φ, hφ⟩ := (hblocks.selfDual ⟨h, hh⟩ h1 hself).exists_half
      have hd1 : 1 ≤ d := by
        have hpos : 0 < (h : K[X]).natDegree :=
          Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors hh)
        rw [hdeg] at hpos
        omega
      have hO2 : ({h, reciprocalPolynomial h} : Set K[X]) = {h} := by
        rw [hself, Set.pair_eq_singleton]
      rw [hO2] at hQ hcard
      let τ : AdjoinRoot (h : K[X]) ≃+* AdjoinRoot (h : K[X]) :=
        RingEquiv.ofRingHom hE.bar hE.bar (RingHom.ext hE.bar_bar) (RingHom.ext hE.bar_bar)
      have hτ : ∀ y, τ (τ y) = y := fun y => hE.bar_bar y
      obtain ⟨eGU⟩ := CFSG.LieType.SemisimpleCentralizers.HeldUCD.nonempty_mulEquiv_heldGU
        (K := AdjoinRoot (h : K[X])) τ hτ Hf eb heb
      let eA : spSupported x {h} ≃* heldGU (primaryMultiplicity (spEnd x) (h : K[X]))
          (AdjoinRoot (h : K[X])) τ hτ := φ.trans eGU
      obtain ⟨eD⟩ := k329s3f_commutator_equiv eA
      have hQ' : CFSG.IsQuasisimple ↥(commutator (heldGU (primaryMultiplicity (spEnd x) (h : K[X]))
          (AdjoinRoot (h : K[X])) τ hτ)) :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv eD hQ
      have hcard' : Nat.card (↥(commutator (heldGU (primaryMultiplicity (spEnd x) (h : K[X]))
          (AdjoinRoot (h : K[X])) τ hτ)) ⧸
          Subgroup.center ↥(commutator (heldGU (primaryMultiplicity (spEnd x) (h : K[X]))
            (AdjoinRoot (h : K[X])) τ hτ))) = 504 := by
        rw [← Nat.card_congr (QuotientGroup.congr _ _ eD (Subgroup.map_center_eq eD)).toEquiv]
        exact hcard
      have hcardE : Nat.card (AdjoinRoot (h : K[X])) = (r ^ (e * d)) ^ 2 := by
        rw [hE.card, ← pow_mul]
        ring_nf
      have hτQ : ∀ y, τ y = y ^ (r ^ (e * d)) := by
        intro y
        change hE.bar y = y ^ (r ^ (e * d))
        rw [hE.bar_apply]
      have hmpos : primaryMultiplicity (spEnd x) (h : K[X]) ≠ 0 :=
        (CFSG.RankThree.PartOne.KCUnitaryModel.primaryMultiplicity_pos hsq ⟨h, hh⟩).ne'
      obtain ⟨t, m', htm, hmodel⟩ := k329s3f_lieModel_commutator_heldGU hrprime
        (by have := Nat.mul_pos (by omega : 0 < e) (by omega : 0 < d); omega) hcardE hτQ hQ'
      rcases htm with ⟨ht, hm⟩ | ⟨ht, hm⟩
      · rw [ht] at hmodel
        rw [hm] at hmodel
        exact absurd (k329_S2_order504 hmpos hmodel hcard').1 (by decide)
      · rw [ht] at hmodel
        rw [hm] at hmodel
        have hpow : r ^ (e * d) = 8 := (k329_S2_order504 (by norm_num : (2 : ℕ) ≠ 0)
          hmodel hcard').2.2
        have hr2 : r = 2 := by
          have hdvd : r ∣ 8 := by rw [← hpow]; exact dvd_pow_self r (Nat.mul_ne_zero (by omega) (by omega))
          rw [show (8 : ℕ) = 2 ^ 3 by norm_num] at hdvd
          exact (Nat.prime_dvd_prime_iff_eq hrprime Nat.prime_two).mp
            (hrprime.dvd_of_dvd_pow hdvd)
        have hed : e * d = 3 := by
          have h : r ^ (e * d) = 2 ^ 3 := by rw [hpow]; norm_num
          rw [hr2] at h
          exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h
        have hdeg3 : (h : K[X]).natDegree ≤ 3 := by
          have hmin : minpoly K (spEnd x) ∣ X ^ 3 - 1 := by
            apply minpoly.dvd
            rw [map_sub, map_pow, aeval_X, map_one, sub_eq_zero]
            exact spEnd_pow hx3
          have hdvd : (h : K[X]) ∣ X ^ 3 - 1 := (mem_primaryFactors.mp hh).2.2.trans hmin
          have hdegX : (X ^ 3 - 1 : K[X]).natDegree = 3 := by compute_degree!
          have hXne : (X ^ 3 - 1 : K[X]) ≠ 0 := by
            intro h0; rw [h0] at hdegX; simp at hdegX
          have := Polynomial.natDegree_le_of_dvd hdvd hXne
          omega
        have hd_eq : d = 1 := by
          have h1 : 2 * d ≤ 3 := by rw [← hdeg]; exact hdeg3
          omega
        rw [hd_eq, mul_one] at hed
        rw [hr2, hed]
        norm_num
    ·
      have hne : (h : K[X]) ≠ reciprocalPolynomial (h : K[X]) := fun e => hself e.symm
      have : Fact (Irreducible (h : K[X])) := ⟨irreducible_of_mem_primaryFactors hh⟩
      obtain ⟨eGL⟩ := (hblocks.paired ⟨h, hh⟩ hne).matrixFactor
      let E := AdjoinRoot (h : K[X])
      let m := primaryMultiplicity (spEnd x) (h : K[X])
      obtain ⟨eD⟩ := k329s3f_commutator_equiv eGL
      have hQ' : CFSG.IsQuasisimple ↥(commutator (Matrix.GeneralLinearGroup (Fin m) E)) :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv eD hQ
      have hcard' : Nat.card (↥(commutator (Matrix.GeneralLinearGroup (Fin m) E)) ⧸
          Subgroup.center ↥(commutator (Matrix.GeneralLinearGroup (Fin m) E))) = 504 := by
        rw [← Nat.card_congr (QuotientGroup.congr _ _ eD (Subgroup.map_center_eq eD)).toEquiv]
        exact hcard
      have hEcard : Nat.card E = r ^ (e * (h : K[X]).natDegree) := by
        rw [(hblocks.paired ⟨h, hh⟩ hne).card_field, ← pow_mul]
      have hdegpos : 0 < (h : K[X]).natDegree :=
        Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors hh)
      have hmpos : m ≠ 0 := (CFSG.RankThree.PartOne.KCUnitaryModel.primaryMultiplicity_pos hsq ⟨h, hh⟩).ne'
      have hmodel := k329s3f_lieModel_commutator_GL hrprime
        (by have := Nat.mul_pos (by omega : 0 < e) hdegpos; omega) hEcard hQ'
      have hpow : r ^ (e * (h : K[X]).natDegree) = 8 :=
        (k329_S2_order504 hmpos hmodel hcard').2.2
      have hdvd := (hblocks.paired ⟨h, hh⟩ hne).dvd
      rw [← pow_mul] at hdvd
      rw [hpow] at hdvd
      exact absurd hdvd (by norm_num)

private theorem k329s3f_core (n r e : ℕ) (hadm : StatedLieAdmissible .PSp n r e) (hr : r ≠ 3)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = r ^ e)
    (x : StatedSp n K) (hxZ : x ∉ K329Zh (StatedSp n K)) (hx3 : x ^ 3 = 1)
    (hQ : ∃ Q : Subgroup (StatedSp n K), Q ≤ K329Lres x ∧
      (Q.subgroupOf (K329Lres x)).Normal ∧ CFSG.Open.IsQuasisimple ↥Q ∧
      Nat.card (↥Q ⧸ Subgroup.center ↥Q) = 504) : r ^ e = 8 := by
  classical
  obtain ⟨Q, hQL, hQn, hQq, hQcard⟩ := hQ
  have hrprime : r.Prime := hadm.1
  have : Fact r.Prime := ⟨hrprime⟩
  have hchar : CharP K r := CFSG.LieType.BorelTits.charP_of_natCard_eq (p := r) (f := e) hK
  have := hchar
  have he1 : 1 ≤ e := hadm.2.1
  have hn2 : 2 ≤ n := hadm.2.2.1
  have hn1 : 1 ≤ n := by omega
  have hpK : (3 : K) ≠ 0 := by
    intro h
    have h3 : r ∣ 3 := (CharP.cast_eq_zero_iff K r 3).mp h
    exact hr ((Nat.prime_dvd_prime_iff_eq hrprime Nat.prime_three).mp h3)
  have hsq : Squarefree (minpoly K (spEnd x)) :=
    (altPrimaryData_spLin (p := 3) hpK hx3).squarefree
  have hxne : x ≠ 1 := by
    intro h; apply hxZ; rw [h]; exact Subgroup.one_mem _
  have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hxne
  have hpa : orderOf (proj n K x) = 3 := by
    have h3 : (proj n K x) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
    refine orderOf_eq_prime h3 ?_
    intro h
    apply hxZ
    have hmem : x ∈ (proj n K).ker := MonoidHom.mem_ker.mpr h
    rwa [CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.ker_proj] at hmem
  have hblocks : SpPrimaryBlocks r e 3 x (proj n K x) :=
    (symplectic_cross_prime_primary_centralizer_blocks (ℓ := r) (f := e) (p := 3) hrprime he1 hK
      Nat.prime_three (by norm_num) (Ne.symm hr) hn1 (proj n K x) hpa).2 x rfl hxord
  let C : Subgroup (StatedSp n K) := Subgroup.centralizer ({x} : Set (StatedSp n K))
  have hLC : K329Lres x ≤ C := by
    change K329Res (Subgroup.centralizer ({x} : Set (StatedSp n K))) ≤ C
    exact Subgroup.map_subtype_le _
  have hLnorm : ((K329Lres x).subgroupOf C).Normal := by
    have h := k329_res_normal (C := C) (D := C) le_rfl (by rw [Subgroup.subgroupOf_self]; infer_instance)
    simpa [K329Lres] using h
  have hQcomp : CFSG.Open.IsComponentOf Q C :=
    ⟨hQL.trans hLC,
      CFSG.Open.IsSubnormal.step hQL hQn
        (CFSG.Open.IsSubnormal.step hLC hLnorm (CFSG.Open.IsSubnormal.refl C)),
      hQq⟩
  have : Finite (reciprocalOrbits (spEnd x)) :=
    (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
  obtain ⟨hcomm, -, hjoin⟩ := hblocks.directProduct
  have hfix : fixSubgroup (MulAut.conj x) = C := k329s3f_fixSubgroup_conj x
  have hq2 : 2 ≤ r ^ e := by rw [← hK]; exact Nat.succ_le_of_lt Finite.one_lt_card
  obtain ⟨O, hOq, hQeq⟩ := components_conj_of_orbit_family (MonoidHom.id (StatedSp n K))
    Function.surjective_id (by rw [MonoidHom.ker_id]; exact bot_le) x
    (fun O : reciprocalOrbits (spEnd x) => spSupported x (O : Set K[X]))
    (fun i j hij a ha b hb => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) a ha b hb)
    hjoin (fun O => quasisimple_or_solvable_spSupported (p := 3) (by norm_num) hq2 hsq hblocks O)
    Q (hfix ▸ hQcomp)
  rw [Subgroup.map_id] at hQeq
  have hcard' : Nat.card (↥⁅spSupported x (O : Set K[X]), spSupported x (O : Set K[X])⁆ ⧸
      Subgroup.center ↥⁅spSupported x (O : Set K[X]), spSupported x (O : Set K[X])⁆) = 504 := by
    rw [← hQeq]; exact hQcard
  exact k329s3f_orbit hadm hr hK hx3 hblocks O hOq hcard'

theorem k329_S3f_PSp (n r e : ℕ) (hadm : StatedLieAdmissible .PSp n r e) (hr : r ≠ 3)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = r ^ e) :
    K329YMatrix (StatedSp n K) (r ^ e) := by
  intro x hxZ hx3 hQ
  have hn1 : 1 ≤ n := by have := hadm.2.2.1; omega
  obtain ⟨y, hy3, hyZ, hcent⟩ := k329s3f_reduce hn1 x hxZ hx3
  have hLres : K329Lres y = K329Lres x := by
    unfold K329Lres; rw [hcent]
  refine k329s3f_core n r e hadm hr K hK y hyZ hy3 ?_
  obtain ⟨Q, hQL, hQn, hQq, hQcard⟩ := hQ
  refine ⟨Q, ?_, ?_, hQq, hQcard⟩
  · rw [hLres]; exact hQL
  · rw [hLres]; exact hQn

section K329S3c

open Polynomial CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCSpIsotypic
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

private theorem k329s3c_squarefree {n : ℕ} {K : Type} [Field K] [Finite K]
    (hchar : CharP K 2) {x : StatedSp n K} (hx3 : x ^ 3 = 1) :
    Squarefree (minpoly K (spEnd x)) := by
  have hpK : (3 : K) ≠ 0 := by
    intro h
    have h23 : (2 : ℕ) ∣ 3 := (@CharP.cast_eq_zero_iff K _ 2 hchar 3).mp h
    omega
  exact (altPrimaryData_spLin (p := 3) hpK hx3).squarefree

private theorem k329s3c_self_reciprocal {n : ℕ} {K : Type} [Field K]
    {x : StatedSp n K} (hblocks : SpPrimaryBlocks 2 3 3 x (proj n K x))
    (hx3 : x ^ 3 = 1) :
    ∀ a : primaryFactors (spEnd x), reciprocalPolynomial (a : K[X]) = a := by
  intro a
  by_contra hne
  have hmin : minpoly K (spEnd x) ∣ X ^ 3 - 1 := by
    apply minpoly.dvd
    rw [map_sub, map_pow, aeval_X, map_one, sub_eq_zero]
    exact spEnd_pow hx3
  have hmem : reciprocalPolynomial (a : K[X]) ∈ primaryFactors (spEnd x) :=
    hblocks.bijOn.1 a.2
  let b : primaryFactors (spEnd x) := ⟨reciprocalPolynomial (a : K[X]), hmem⟩
  have hbval : (b : K[X]) = reciprocalPolynomial (a : K[X]) := rfl
  have hane : a ≠ b := by
    intro h
    apply hne
    have h' : (a : K[X]) = (b : K[X]) := congrArg Subtype.val h
    rw [hbval] at h'
    exact h'.symm
  have hp : SpPairedBlock 2 3 3 x a := hblocks.paired a (Ne.symm hne)
  have hdvd : 3 ∣ 8 ^ (a : K[X]).natDegree - 1 := by
    have h := hp.dvd
    norm_num at h ⊢
    exact h
  have ha_dvd : (a : K[X]) ∣ X ^ 3 - 1 :=
    (mem_primaryFactors.mp a.2).2.2.trans hmin
  have hb_dvd : (b : K[X]) ∣ X ^ 3 - 1 :=
    (mem_primaryFactors.mp b.2).2.2.trans hmin
  have hcop : IsCoprime (a : K[X]) (b : K[X]) := by
    refine isCoprime_of_mem_primaryFactors a.2 b.2 ?_
    intro h
    exact hane (Subtype.ext h)
  have hprod : (a : K[X]) * (b : K[X]) ∣ X ^ 3 - 1 := hcop.mul_dvd ha_dvd hb_dvd
  have hdeg3 : (X ^ 3 - 1 : K[X]).natDegree = 3 := by compute_degree!
  have hX3ne : (X ^ 3 - 1 : K[X]) ≠ 0 := by
    intro h
    rw [h] at hdeg3
    simp at hdeg3
  have ha_ne : (a : K[X]) ≠ 0 := (monic_of_mem_primaryFactors a.2).ne_zero
  have hb_ne : (b : K[X]) ≠ 0 := (monic_of_mem_primaryFactors b.2).ne_zero
  have hle : ((a : K[X]) * (b : K[X])).natDegree ≤ 3 := by
    have := Polynomial.natDegree_le_of_dvd hprod hX3ne
    omega
  rw [Polynomial.natDegree_mul ha_ne hb_ne] at hle
  have hbdeg : (b : K[X]).natDegree = (a : K[X]).natDegree := by
    rw [hbval]
    exact hp.natDegree_eq.symm
  rw [hbdeg] at hle
  have hpos : 0 < (a : K[X]).natDegree := (irreducible_of_mem_primaryFactors a.2).natDegree_pos
  have hdeg1 : (a : K[X]).natDegree = 1 := by omega
  rw [hdeg1] at hdvd
  norm_num at hdvd

theorem k329_S3c_PSp (n : ℕ) (hadm : StatedLieAdmissible .PSp n 2 3) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ 3) : K329CentralProductMatrix (StatedSp n K) := by
  classical
  intro x hxZ hx3
  have hn : 1 ≤ n := by have := hadm.2.2.1; omega
  have hchar : CharP K 2 := CFSG.LieType.BorelTits.charP_of_natCard_eq (p := 2) (f := 3) hK
  have hZbot : K329Zh (StatedSp n K) = ⊥ :=
    @CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot n K _ hchar
  have hx3' : x ^ 3 = 1 := by
    have h := hx3
    rw [hZbot] at h
    simpa using h
  have hxne : x ≠ 1 := by
    intro h
    apply hxZ
    rw [h]
    exact Subgroup.one_mem _
  have hxord : orderOf x = 3 := by
    have hdvd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3'
    rcases Nat.Prime.eq_one_or_self_of_dvd (p := 3) (by norm_num) (orderOf x) hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hxne
    · exact h
  have hpa : orderOf (proj n K x) = 3 := by
    have h3 : (proj n K x) ^ 3 = 1 := by rw [← map_pow, hx3', map_one]
    have hdvd : orderOf (proj n K x) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    have hne : proj n K x ≠ 1 := by
      intro h
      apply hxZ
      have hmem : x ∈ (proj n K).ker := MonoidHom.mem_ker.mpr h
      rwa [CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.ker_proj] at hmem
    rcases Nat.Prime.eq_one_or_self_of_dvd (p := 3) (by norm_num) (orderOf (proj n K x)) hdvd
      with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hne
    · exact h
  have hblocks : SpPrimaryBlocks 2 3 3 x (proj n K x) :=
    (CFSG.RankThree.Classical.symplectic_cross_prime_primary_centralizer_blocks
      (ℓ := 2) (f := 3) (p := 3) (by norm_num) (by norm_num) hK (by norm_num)
      (by norm_num) (by norm_num) hn (proj n K x) hpa).2 x rfl hxord
  have hsq : Squarefree (minpoly K (spEnd x)) := k329s3c_squarefree hchar hx3'
  have facts : ∀ h : primaryFactors (spEnd x), SpBlockFacts (spForm n K) (spLin n K x) h :=
    fun h => k329kc3_spBlockFacts (ℓ := 2) (f := 3) (p := 3) (by norm_num) hK hsq hblocks h
  have hself := k329s3c_self_reciprocal hblocks hx3'
  let SB : SpBlockIdx x → Subgroup (LinearMap.GeneralLinearGroup K (Fin n ⊕ Fin n → K)) :=
    fun a => specialBlock (spForm n K) (spLin n K x) (a.1 : K[X])
  let Lf : SpBlockIdx x → Subgroup ↥(StatedSp n K) := fun a => (SB a).comap (spLin n K)
  have hSB_le : ∀ a, SB a ≤ unitaryCentralizer (spForm n K) (spLin n K x) := fun a =>
    specialBlock_le_unitaryCentralizer
  have hSB_range : ∀ a, SB a ≤ (spLin n K).range := by
    intro a
    rw [range_spLin]
    exact (hSB_le a).trans fun g hg => (mem_unitaryCentralizer.mp hg).1
  have hLf_map : ∀ a, (Lf a).map (spLin n K) = SB a := fun a =>
    Subgroup.map_comap_eq_self (hSB_range a)
  have hopen : ∀ a, CFSG.Open.IsQuasisimple ↥(SB a) := fun a => by
    have h := (facts a.1).quasisimple a.2
    exact ⟨h.1.commutator_eq_top, h.2.1⟩
  have hLf_q : ∀ a, CFSG.Open.IsQuasisimple ↥(Lf a) := fun a => by
    have e : ↥(Lf a) ≃* ↥(SB a) := by
      have e0 := Subgroup.equivMapOfInjective (Lf a) (spLin n K)
        (spLin_injective (r := n) (K := K))
      rwa [hLf_map a] at e0
    exact k329_isQuasisimple_of_mulEquiv e.symm (hopen a)
  have hLf_c : ∀ a b, a ≠ b → ⁅Lf a, Lf b⁆ = ⊥ := by
    intro a b hab
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro g' hg'
    have hba : (b.1 : K[X]) ≠ (a.1 : K[X]) := fun h =>
      hab (Subtype.ext (Subtype.ext h.symm))
    have hbd : (b.1 : K[X]) ≠ reciprocalPolynomial (a.1 : K[X]) := by
      rw [hself a.1]
      exact hba
    have hcomm : Commute (spLin n K g) (spLin n K g') :=
      commute_specialBlock_of_ne hblocks a.1 b.1 hba hbd hg hg'
    exact spLin_injective (r := n) (K := K) (by
      rw [map_mul, map_mul]
      exact hcomm.eq.symm)
  have hLf_le : ∀ a, Lf a ≤ K329Lres x := by
    intro a
    refine k329_perfect_le_res ?_ (Subgroup.isPerfect_iff.mp ⟨(hLf_q a).1⟩)
    calc Lf a = (SB a).comap (spLin n K) := rfl
      _ ≤ (unitaryCentralizer (spForm n K) (spLin n K x)).comap (spLin n K) :=
          Subgroup.comap_mono (hSB_le a)
      _ = ((Subgroup.centralizer ({x} : Set ↥(StatedSp n K))).map (spLin n K)).comap
            (spLin n K) := by rw [unitaryCentralizer_spForm_eq_map]
      _ = Subgroup.centralizer ({x} : Set ↥(StatedSp n K)) :=
          Subgroup.comap_map_eq_self_of_injective (spLin_injective (r := n) (K := K)) _
  have hsup_ge : K329Lres x ≤ ⨆ a, Lf a := by
    calc K329Lres x = K329Res (Subgroup.centralizer ({x} : Set ↥(StatedSp n K))) := rfl
      _ ≤ ⁅Subgroup.centralizer ({x} : Set ↥(StatedSp n K)),
            Subgroup.centralizer ({x} : Set ↥(StatedSp n K))⁆ := k329_res_le_commutator _
      _ ≤ ⨆ a, Lf a := by
          refine (Subgroup.map_le_map_iff_of_injective (spLin_injective (r := n) (K := K))).mp ?_
          rw [Subgroup.map_commutator, Subgroup.map_iSup, ← unitaryCentralizer_spForm_eq_map,
            commutator_unitaryCentralizer_eq_iSup hblocks facts]
          exact le_of_eq (iSup_congr fun a => (hLf_map a).symm)
  exact ⟨SpBlockIdx x, inferInstance, Lf, hLf_q, hLf_c, le_antisymm (iSup_le hLf_le) hsup_ge⟩

end K329S3c

theorem k329_S4_PSp (n : ℕ) (hadm : StatedLieAdmissible .PSp n 2 3) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ 3) : K329SchurMatrix (StatedSp n K) := by
  intro x hxZh hx3Zh R hRc _hR3 hRcomm g hg g' hg'
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 :=
    @CFSG.LieType.BorelTits.charP_of_natCard_eq K _ _ 2 3 hfact hK
  have hZh_bot : K329Zh (StatedSp n K) = ⊥ :=
    @CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot n K _ hchar
  have hx1 : x ≠ 1 := by rw [hZh_bot] at hxZh; exact hxZh
  have hx3 : x ^ 3 = 1 := by rw [hZh_bot] at hx3Zh; exact hx3Zh
  have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  let a : StatedProj (StatedSp n K) := proj n K x
  have hker_bot : (proj n K).ker = ⊥ := by
    rw [show (proj n K).ker = K329Zh (StatedSp n K) from QuotientGroup.ker_mk' _, hZh_bot]
  have haord : orderOf a = 3 := by
    have ha3 : a ^ 3 = 1 := by
      change (proj n K x) ^ 3 = 1
      rw [← map_pow, hx3, map_one]
    refine orderOf_eq_prime ha3 ?_
    intro h
    have hxker : x ∈ (proj n K).ker := MonoidHom.mem_ker.mpr h
    rw [hker_bot] at hxker
    exact hx1 (Subgroup.mem_bot.mp hxker)
  have hpK : (3 : K) ≠ 0 := by
    intro h
    have h2 : 2 ∣ 3 := (CharP.cast_eq_zero_iff (self := hchar) K 2 3).mp h
    omega
  have hsq : Squarefree (minpoly K (spEnd x)) := (altPrimaryData_spLin hpK hx3).squarefree
  have blocks : SpPrimaryBlocks 2 3 3 x a :=
    (symplectic_cross_prime_primary_centralizer_blocks Nat.prime_two (by norm_num) hK
      Nat.prime_three (by norm_num) (by norm_num)
      (by have := hadm.2.2.1; omega) a haord).2 x rfl hxord
  have facts : ∀ h : primaryFactors (spEnd x), SpBlockFacts (spForm n K) (spLin n K x) h :=
    fun h => k329kc3_spBlockFacts (by norm_num) hK hsq blocks h
  have hPres := k329s4_P_le_res x blocks facts
  exact k329s4_commute x blocks facts hPres R hRc hRcomm g hg g' hg'

theorem k329_S5_PSp (n : ℕ) (hadm : StatedLieAdmissible .PSp n 2 3) (K : Type) [Field K] :
    K329TwistMatrix (StatedSp n K) False := by
  intro x _ hx3 g hg _ hgx
  exact hgx (k329_S5_of_no_order_three (K329Zh _) (k329_Zh_le_center _)
    (k329_Z3_PSp (by have := hadm.2.2.1; omega)) hx3 hg)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
