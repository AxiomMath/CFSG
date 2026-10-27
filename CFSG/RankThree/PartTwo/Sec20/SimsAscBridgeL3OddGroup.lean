module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.GLS.IVK.Defs
import CFSG.GH74.KGroups.L3EpsUniInv
import CFSG.RankThree.PartTwo.KFacts.L34Sections
import CFSG.RankThree.PartTwo.KFacts.K72L3Linear
import CFSG.RankThree.PartTwo.KFacts.K72L3Unitary
import CFSG.GH74.KGroups.L3EpsUniGraph

public section

namespace CFSG.RankThree.PartTwo.Sec20.L3OddGroup

open Subgroup Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups commutatorElement

section General

theorem card_le_two_of_inv_mul_mem {A : Type*} [Group A] {I R : Subgroup A} (hRI : R ⊓ I = ⊥)
    (h : ∀ r ∈ R, ∀ s ∈ R, r ∉ I → s ∉ I → r⁻¹ * s ∈ I) : Nat.card R ≤ 2 := by
  classical
  have hbot : ∀ r ∈ R, r ∈ I → r = 1 := fun r hr hrI => by
    have : r ∈ R ⊓ I := ⟨hr, hrI⟩
    rwa [hRI, Subgroup.mem_bot] at this
  have hinj : Function.Injective fun r : R => decide ((r : A) ∈ I) := by
    intro r s hrs
    simp only [decide_eq_decide] at hrs
    by_cases hr : (r : A) ∈ I
    · exact Subtype.ext ((hbot r r.2 hr).trans (hbot s s.2 (hrs.1 hr)).symm)
    · have hs : (s : A) ∉ I := fun hs => hr (hrs.2 hs)
      have h1 := hbot _ (R.mul_mem (R.inv_mem r.2) s.2) (h r r.2 s s.2 hr hs)
      exact Subtype.ext (inv_mul_eq_one.mp h1)
  calc Nat.card R ≤ Nat.card Bool := Nat.card_le_card_of_injective _ hinj
    _ = 2 := by simp

theorem congr_apply_apply {K X : Type*} [Group K] [Group X] (E : K ≃* X) (c : MulAut K)
    (x : K) : MulAut.congr E c (E x) = E (c x) := by
  simp [MulAut.congr_apply]

theorem mem_range_conj_of_congr {K X : Type*} [Group K] [Group X] (E : K ≃* X) {α : MulAut K}
    (h : MulAut.congr E α ∈ (MulAut.conj : X →* MulAut X).range) :
    α ∈ (MulAut.conj : K →* MulAut K).range := by
  obtain ⟨y, hy⟩ := h
  refine ⟨E.symm y, MulEquiv.ext fun x => E.injective ?_⟩
  have := DFunLike.congr_fun hy (E x)
  rw [congr_apply_apply, MulAut.conj_apply] at this
  rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  exact this

theorem mem_fixedSubgroup_iff {K : Type*} [Group K] {c : MulAut K} {x : K} :
    x ∈ CFSG.GH74.GLS.fixedSubgroup K c ↔ c x = x :=
  Iff.rfl

theorem eq_of_isPerfect_of_le_fixed {K : Type*} [Group K] {c : MulAut K} {N L : Subgroup K}
    (hN : CFSG.IsQuasisimple ↥N) (hNc : ∀ n ∈ N, c n = n)
    (hcomm : ∀ x y, c x = x → c y = y → ⁅x, y⁆ ∈ N) (hL : Group.IsPerfect ↥L) (hL1 : L ≠ ⊥)
    (hLc : L ≤ CFSG.GH74.GLS.fixedSubgroup K c)
    (hLn : ∀ y ∈ CFSG.GH74.GLS.fixedSubgroup K c, ∀ l ∈ L, y * l * y⁻¹ ∈ L) : L = N := by
  have hLL : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hL
  have hLN : L ≤ N := by
    rw [← hLL, Subgroup.commutator_le]
    exact fun x hx y hy => hcomm x y (mem_fixedSubgroup_iff.mp (hLc hx))
      (mem_fixedSubgroup_iff.mp (hLc hy))
  have hnorm : (L.subgroupOf N).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hLn g (mem_fixedSubgroup_iff.mpr (hNc g g.2)) n hn
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hN hnorm with h | h
  · exact le_antisymm hLN (Subgroup.subgroupOf_eq_top.mp h)
  · refine absurd ?_ hL1
    rw [← hLL, eq_bot_iff, Subgroup.commutator_le]
    intro x hx y hy
    have hxN : (⟨x, hLN hx⟩ : ↥N) ∈ L.subgroupOf N := Subgroup.mem_subgroupOf.mpr hx
    have hx' := Subgroup.mem_center_iff.mp (h hxN) ⟨y, hLN hy⟩
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (congrArg Subtype.val hx').symm

theorem nonempty_psl2_congr {k k' : Type} [Field k] [Field k'] (ι : k ≃+* k') :
    Nonempty (Matrix.ProjectiveSpecialLinearGroup (Fin 2) k ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) k') := by
  let s : SpecialLinearGroup (Fin 2) k ≃* SpecialLinearGroup (Fin 2) k' :=
    { toFun := SpecialLinearGroup.map ι.toRingHom
      invFun := SpecialLinearGroup.map ι.symm.toRingHom
      left_inv := fun A => by ext i j; simp
      right_inv := fun A => by ext i j; simp
      map_mul' := map_mul _ }
  exact ⟨QuotientGroup.congr _ _ s (Subgroup.map_center_eq s)⟩

end General

section Orthogonal

open CFSG.ComponentClassification CFSG.ComponentClassification.Burgoyne.PSL

variable {k : Type} [Field k]

private theorem ker_traceZeroAction :
    (CatalogueBOrthogonal.traceZeroOrthogonalAction.comp
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) k →* GL (Fin 2) k)).ker =
      center (SpecialLinearGroup (Fin 2) k) := by
  ext A
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
    CatalogueBOrthogonal.traceZeroOrthogonalAction_eq_one_iff,
    Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_, congrArg Units.val hc⟩
    have hd := congrArg Matrix.det (congrArg Units.val hc)
    rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hd
    rw [Fintype.card_fin, hd]
    exact A.2
  · rintro ⟨r, hr, hrA⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [Fintype.card_fin, zero_pow (by norm_num)] at hr
      exact zero_ne_one hr
    refine ⟨Units.mk0 r hr0, Units.ext ?_⟩
    rw [GeneralLinearGroup.coe_scalar, Units.val_mk0]
    exact hrA

variable [Finite k]

private theorem nonempty_commutator_isometryGroup_equiv_psl2 (hk : ringChar k ≠ 2)
    (h3 : Nat.card k ≠ 3) (R : GL (Fin 3) k) (hR : (R : Matrix (Fin 3) (Fin 3) k)ᵀ = R) :
    Nonempty (↥(⁅CatalogueBGraphForm.isometryGroup 3 k R,
      CatalogueBGraphForm.isometryGroup 3 k R⁆ : Subgroup (GL (Fin 3) k)) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) k) := by
  have hodd := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two k hk
  have hQnd := CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hk R hR
  have hdim : Module.finrank k (Fin 3 → k) = 3 := Module.finrank_fin_fun k
  obtain ⟨_, _, e, -, -, hcomm, -, -⟩ := orthogonal_three_derived hodd h3
    (CatalogueBLinearHigherB.matrixQuadraticForm R) hQnd hdim
  set eI := isoOrthGL hk R hR
  let eA : ↥(commutator (TauCeti.QuadraticMap.orthogonalGroup
      (CatalogueBLinearHigherB.matrixQuadraticForm R))) ≃*
      ↥(⁅CatalogueBGraphForm.isometryGroup 3 k R, CatalogueBGraphForm.isometryGroup 3 k R⁆ :
        Subgroup (GL (Fin 3) k)) :=
    (((commutator (TauCeti.QuadraticMap.orthogonalGroup
      (CatalogueBLinearHigherB.matrixQuadraticForm R))).equivMapOfInjective _ eI.injective).trans
      (((commutator (TauCeti.QuadraticMap.orthogonalGroup
        (CatalogueBLinearHigherB.matrixQuadraticForm R))).map eI.toMonoidHom).equivMapOfInjective
        _ (CatalogueBGraphForm.isometryGroup 3 k R).subtype_injective)).trans
      (MulEquiv.subgroupCongr (trans_commutator eI))
  let eB : ↥(commutator (TauCeti.QuadraticMap.orthogonalGroup
      (CatalogueBLinearHigherB.matrixQuadraticForm R))) ≃* ↥(traceZeroSpecialImage k) :=
    (MulEquiv.subgroupCongr hcomm).trans
      ((traceZeroSpecialImage k).equivMapOfInjective e.symm.toMonoidHom e.symm.injective).symm
  let eC : ↥(traceZeroSpecialImage k) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k :=
    (QuotientGroup.quotientKerEquivRange (CatalogueBOrthogonal.traceZeroOrthogonalAction.comp
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) k →* GL (Fin 2) k))).symm.trans
      (QuotientGroup.quotientMulEquivOfEq ker_traceZeroAction)
  exact ⟨(eA.symm.trans eB).trans eC⟩

end Orthogonal

section Linear

theorem odd_of_pow_mod_three_eq_two {p f : ℕ} (hq : p ^ f % 3 = 2) : Odd f := by
  rcases Nat.even_or_odd f with ⟨k, rfl⟩ | h
  · exfalso
    rw [pow_add, Nat.mul_mod] at hq
    rcases (by omega : p ^ k % 3 = 0 ∨ p ^ k % 3 = 1 ∨ p ^ k % 3 = 2) with h | h | h <;>
      rw [h] at hq <;> norm_num at hq
  · exact h

variable {p f : ℕ} [Fact p.Prime]

private theorem mem_range_conj_or_mul_dualAut_mem (hq : p ^ f % 3 = 2)
    {β : MulAut (projectiveSL 3 (GaloisField p f))} {k : ℕ} (hβ : β ^ 2 ^ k = 1) :
    β ∈ (MulAut.conj : projectiveSL 3 (GaloisField p f) →* _).range ∨
      β * dualAut 3 (GaloisField p f) ∈
        (MulAut.conj : projectiveSL 3 (GaloisField p f) →* _).range := by
  set F := GaloisField p f
  have hp : p.Prime := Fact.out
  have hf : Odd f := odd_of_pow_mod_three_eq_two hq
  have hf0 : f ≠ 0 := by rintro rfl; exact absurd hf (by decide)
  have hFc : Nat.card F = p ^ f := GaloisField.card p f hf0
  have hF3 : Nat.card F % 3 = 2 := by rwa [hFc]
  obtain ⟨-, hform⟩ := automorphism_generation (K := F) (n := 3) le_rfl
  obtain ⟨A, σ, ε, hε, rfl⟩ := hform β
  have hσ2 := CFSG.GH74.KGroups.L3Eps.sigma_two_pow A σ hε hβ
  have hσ : σ = 1 := by
    obtain ⟨hcard, -⟩ := card_ringAut_and_isCyclic hp F hFc
    have hσf : σ ^ Nat.card (RingAut F) = 1 := pow_card_eq_one'
    rw [hcard] at hσf
    have hg : Nat.gcd (2 ^ (k + 1)) f = 1 :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hf)
    have := pow_gcd_eq_one.mpr ⟨hσ2, hσf⟩
    rwa [hg, pow_one] at this
  subst hσ
  have hA : conjAut 3 F A ∈ (MulAut.conj : projectiveSL 3 F →* _).range :=
    KFacts.isInnerAut_of_mem_linearAutGroup hF3 (conjAut_mem_linearAutGroup A)
  rw [map_one, mul_one]
  interval_cases ε
  · left
    rwa [pow_zero, mul_one]
  · right
    rw [pow_one, mul_assoc, (standard_automorphism_transport (K := F) (n := 3)).2.2.2.1, mul_one]
    exact hA

theorem card_le_two_of_inf_inn_eq_bot_L3 {K : Type} [Group K] (hq : p ^ f % 3 = 2)
    (e : K ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField p f))
    {R : Subgroup (MulAut K)} (hR : IsPGroup 2 R)
    (hRinn : R ⊓ (MulAut.conj : K →* MulAut K).range = ⊥) :
    Nat.card R ≤ 2 := by
  set F := GaloisField p f
  set E : K ≃* projectiveSL 3 F := e.trans (KFacts.L34.projSLEquivProjectiveSL 3 F)
  have h2pow : ∀ t ∈ R, ∃ k : ℕ, MulAut.congr E t ^ 2 ^ k = 1 := fun t ht => by
    obtain ⟨k, hk⟩ := hR ⟨t, ht⟩
    have hk' : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact ⟨k, by rw [← map_pow, hk', map_one]⟩
  have hout : ∀ t, t ∉ (MulAut.conj : K →* MulAut K).range →
      MulAut.congr E t ∉ (MulAut.conj : projectiveSL 3 F →* _).range :=
    fun t ht h => ht (mem_range_conj_of_congr E h)
  refine card_le_two_of_inv_mul_mem hRinn fun r hr s hs hrI hsI => ?_
  obtain ⟨a, ha⟩ := h2pow r hr
  obtain ⟨b, hb⟩ := h2pow s hs
  rcases mem_range_conj_or_mul_dualAut_mem hq ha with h1 | h1
  · exact absurd h1 (hout r hrI)
  rcases mem_range_conj_or_mul_dualAut_mem hq hb with h3 | h3
  · exact absurd h3 (hout s hsI)
  apply mem_range_conj_of_congr E
  have e1 : MulAut.congr E (r⁻¹ * s) = dualAut 3 F *
      ((MulAut.congr E r * dualAut 3 F)⁻¹ * (MulAut.congr E s * dualAut 3 F)) *
        (dualAut 3 F)⁻¹ := by
    rw [map_mul, map_inv]
    group
  rw [e1]
  exact (CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _).conj_mem _
    (mul_mem (inv_mem h1) h3) _

open CFSG.ComponentClassification CFSG.ComponentClassification.Burgoyne.PSL in
private theorem exists_graph_centralizer_equiv_psl2 {F : Type} [Field F] [Finite F]
    (hF : ringChar F ≠ 2) (h3 : Nat.card F ≠ 3) (hF3 : Nat.card F % 3 = 2) {A : GL (Fin 3) F}
    (hA : (A : Matrix (Fin 3) (Fin 3) F)ᵀ = A) :
    ∃ N : Subgroup (projectiveSL 3 F), CFSG.IsQuasisimple ↥N ∧
      (∀ n ∈ N, (conjAut 3 F A * dualAut 3 F) n = n) ∧
      (∀ x y, (conjAut 3 F A * dualAut 3 F) x = x → (conjAut 3 F A * dualAut 3 F) y = y →
        ⁅x, y⁆ ∈ N) ∧
      Nonempty (↥N ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
  set R : GL (Fin 3) F := A⁻¹
  have hRsymm : (R : Matrix (Fin 3) (Fin 3) F)ᵀ = R :=
    CFSG.GH74.KGroups.L3Eps.transpose_inv_of_symm A hA
  set I := CatalogueBGraphForm.isometryGroup 3 F R
  set ΩS : Subgroup (SpecialLinearGroup (Fin 3) F) :=
    (⁅I, I⁆ : Subgroup (GL (Fin 3) F)).comap SpecialLinearGroup.toGL
  have hmapΩ : ΩS.map SpecialLinearGroup.toGL = ⁅I, I⁆ := map_comap_toGL_of_le_commutator le_rfl
  have eΩ : ↥ΩS ≃* ↥(⁅I, I⁆ : Subgroup (GL (Fin 3) F)) :=
    (ΩS.equivMapOfInjective _ SpecialLinearGroup.toGL_injective).trans
      (MulEquiv.subgroupCongr hmapΩ)
  have eN : ↥ΩS ≃* ↥(ΩS.map (proj 3 F)) :=
    ΩS.equivMapOfInjective _ (KFacts.proj_three_injective hF3)
  obtain ⟨ψ⟩ := nonempty_commutator_isometryGroup_equiv_psl2 hF h3 R hRsymm
  have hq := CFSG.GH74.KGroups.L3Eps.Uni.isQuasisimple_commutator_isometryGroup hF h3 R hRsymm
  have hrep : ∀ x : projectiveSL 3 F, (conjAut 3 F A * dualAut 3 F) x = x →
      ∃ g : SpecialLinearGroup (Fin 3) F, g ∈ isometrySL 3 A⁻¹ ∧ proj 3 F g = x := by
    intro x hx
    obtain ⟨g, rfl⟩ := proj_surjective 3 F x
    rw [conjAut_mul_dualAut_proj] at hx
    exact CFSG.GH74.KGroups.L3Eps.exists_isometrySL_rep hA hx
  refine ⟨ΩS.map (proj 3 F), CFSG.LocalCores.isQuasisimple_of_mulEquiv (eΩ.symm.trans eN) hq,
    ?_, ?_, ⟨(eN.symm.trans eΩ).trans ψ⟩⟩
  · rintro _ ⟨h, hh, rfl⟩
    rw [conjAut_mul_dualAut_proj]
    congr 1
    exact (graphLift_eq_iff A h).2 (Subgroup.commutator_le_self I hh)
  · intro x y hx hy
    obtain ⟨g, hg, rfl⟩ := hrep x hx
    obtain ⟨k, hk, rfl⟩ := hrep y hy
    refine ⟨⁅g, k⁆, ?_, by simp only [map_commutatorElement]⟩
    change SpecialLinearGroup.toGL ⁅g, k⁆ ∈ ⁅I, I⁆
    rw [map_commutatorElement]
    exact Subgroup.commutator_mem_commutator hg hk

theorem exists_L2_of_not_inner_L3 {K : Type} [Group K] (hp2 : p ≠ 2) (hq : p ^ f % 3 = 2)
    (e : K ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField p f)) {c : MulAut K}
    (hc : c * c = 1) (hout : c ∉ (MulAut.conj : K →* MulAut K).range) :
    ∃ N : Subgroup K, CFSG.IsQuasisimple ↥N ∧ (∀ n ∈ N, c n = n) ∧
      (∀ x y, c x = x → c y = y → ⁅x, y⁆ ∈ N) ∧
      Nonempty (↥N ≃* CFSG.GH74.GLS.IVK.L2 (GaloisField p f)) := by
  have hp : p.Prime := Fact.out
  set F := GaloisField p f
  have hf : Odd f := odd_of_pow_mod_three_eq_two hq
  have hf0 : f ≠ 0 := by rintro rfl; exact absurd hf (by decide)
  have hFc : Nat.card F = p ^ f := GaloisField.card p f hf0
  have hF2 : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF2
  have h3 : Nat.card F ≠ 3 := by rw [hFc]; omega
  have hF3 : Nat.card F % 3 = 2 := by rwa [hFc]
  set E : K ≃* projectiveSL 3 F := e.trans (KFacts.L34.projSLEquivProjectiveSL 3 F)
  have hβ2 : MulAut.congr E c * MulAut.congr E c = 1 := by rw [← map_mul, hc, map_one]
  have hβout : MulAut.congr E c ∉
      CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL 3 F) :=
    fun h => hout (mem_range_conj_of_congr E h)
  obtain ⟨A, hAs, hA⟩ := CFSG.GH74.KGroups.L3Eps.lin_involution_form hp hFc hf h2 hβ2 hβout
  obtain ⟨N, hNq, hNfix, hNcomm, ⟨ψ⟩⟩ := exists_graph_centralizer_equiv_psl2 hF2 h3 hF3 hAs
  rw [← hA] at hNfix hNcomm
  have eN : ↥N ≃* ↥(N.map E.symm.toMonoidHom) := N.equivMapOfInjective _ E.symm.injective
  refine ⟨N.map E.symm.toMonoidHom, CFSG.LocalCores.isQuasisimple_of_mulEquiv eN hNq, ?_, ?_,
    ⟨(eN.symm.trans ψ).trans (CFSG.GH74.GLS.IVK.L2.equivPSL F).symm⟩⟩
  · rintro _ ⟨n, hn, rfl⟩
    apply E.injective
    rw [← congr_apply_apply]
    simpa using hNfix n hn
  · intro x y hx hy
    refine ⟨⁅E x, E y⁆, hNcomm _ _ ?_ ?_, ?_⟩
    · rw [congr_apply_apply, hx]
    · rw [congr_apply_apply, hy]
    · simp [map_commutatorElement]

theorem nonempty_mulEquiv_L2_of_normal_fixed_L3 {K : Type} [Group K] (hp2 : p ≠ 2)
    (hq : p ^ f % 3 = 2) (e : K ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField p f))
    {c : MulAut K} (hc : c * c = 1) (hout : c ∉ (MulAut.conj : K →* MulAut K).range)
    {L : Subgroup K} (hL : Group.IsPerfect L) (hL1 : L ≠ ⊥)
    (hLc : L ≤ CFSG.GH74.GLS.fixedSubgroup K c)
    (hLn : ∀ y ∈ CFSG.GH74.GLS.fixedSubgroup K c, ∀ l ∈ L, y * l * y⁻¹ ∈ L) :
    Nonempty (↥L ≃* CFSG.GH74.GLS.IVK.L2 (GaloisField p f)) := by
  obtain ⟨N, hNq, hNfix, hNcomm, hψ⟩ := exists_L2_of_not_inner_L3 hp2 hq e hc hout
  rwa [eq_of_isPerfect_of_le_fixed hNq hNfix hNcomm hL hL1 hLc hLn]

end Linear

section Unitary

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem seven_le_of_mod_three_eq_one {p : ℕ} (hp : p.Prime) (hq : p % 3 = 1) : 7 ≤ p := by
  have h2 := hp.two_le
  rcases (by omega : p = 4 ∨ 7 ≤ p) with h | h
  · exact absurd (h ▸ hp) (by norm_num)
  · exact h

variable {p : ℕ} [Fact p.Prime]

theorem card_le_two_of_inf_inn_eq_bot_U3 {K : Type} [Group K] (hq : p % 3 = 1)
    (e : K ≃* CFSG.Assembly.RankThreeEven.projSU 3 p 1) {R : Subgroup (MulAut K)}
    (hRinn : R ⊓ (MulAut.conj : K →* MulAut K).range = ⊥) : Nat.card R ≤ 2 := by
  have hp : p.Prime := Fact.out
  have hp7 := seven_le_of_mod_three_eq_one hp hq
  set F := GaloisField p (2 * 1)
  have h : UnitaryFieldData p 1 F := ⟨hp, le_rfl, GaloisField.card p (2 * 1) (by norm_num)⟩
  set E : K ≃* unitaryPSU h 3 := e.trans ((CFSG.PGLModel.projSUEquivStatedProj 3 p 1).trans
    (unitaryPSUEquiv h (by norm_num)).symm)
  have hq2 : 2 < p ^ 1 := by rw [pow_one]; omega
  have hq1 : p ^ 1 % 3 = 1 := by rwa [pow_one]
  have hcard : Nat.card (F ≃+* F) = 2 := (card_ringAut_and_isCyclic hp F h.card).1
  have hinn : ∀ A : KFacts.unitaryIsom3 h,
      KFacts.psuConj h A ∈ (MulAut.conj : unitaryPSU h 3 →* _).range :=
    fun A => KFacts.isInnerAut_of_mem_psuConj_range h hq1 ⟨A, rfl⟩
  have hform : ∀ t, t ∉ (MulAut.conj : K →* MulAut K).range →
      ∃ (A : KFacts.unitaryIsom3 h) (σ : F ≃+* F), σ ≠ 1 ∧
        MulAut.congr E t = KFacts.psuConj h A * KFacts.psuField h σ := by
    intro t ht
    obtain ⟨A, σ, hAσ⟩ := KFacts.exists_psuConj_mul_psuField hq2 (MulAut.congr E t)
    refine ⟨A, σ, fun hσ => ht (mem_range_conj_of_congr E ?_), hAσ⟩
    rw [hAσ, hσ, map_one, mul_one (KFacts.psuConj h A)]
    exact hinn A
  refine card_le_two_of_inv_mul_mem hRinn fun r _ s _ hrI hsI => ?_
  obtain ⟨A, σ, hσ, hr⟩ := hform r hrI
  obtain ⟨B, τ, hτ, hs⟩ := hform s hsI
  have hστ : σ = τ := ((Nat.card_eq_two_iff' (1 : F ≃+* F)).mp hcard).unique hσ hτ
  apply mem_range_conj_of_congr E
  rw [map_mul, map_inv, hr, hs, hστ]
  have e1 : (KFacts.psuConj h A * KFacts.psuField h τ)⁻¹ *
      (KFacts.psuConj h B * KFacts.psuField h τ) =
      (KFacts.psuField h τ)⁻¹ * ((KFacts.psuConj h A)⁻¹ * KFacts.psuConj h B) *
        ((KFacts.psuField h τ)⁻¹)⁻¹ := by
    group
  rw [e1]
  exact (CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _).conj_mem _
    (mul_mem (inv_mem (hinn A)) (hinn B)) _

open CFSG.ComponentClassification CFSG.GH74.KGroups.L3Eps.Uni in
private theorem exists_L2_of_typeII {ℓ f : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData ℓ f F) (h5 : 5 ≤ ℓ ^ f) (hq : Odd (ℓ ^ f))
    {K : Type} [Group K] {θ : ↥(unitarySU ℓ f F 3) →* K} (hθ : IsCover h θ)
    {σ : MulAut K} {φ : F ≃+* F} {A : GL (Fin 3) F} (hφ : ∀ c, φ c = h.bar c)
    (hAu : ((A : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (A : Matrix (Fin 3) (Fin 3) F) = 1)
    (hAA : (A : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F).map h.bar = 1)
    (hrel : ∀ g : ↥(unitarySU ℓ f F 3), ∃ g' : ↥(unitarySU ℓ f F 3),
      (g' : GL (Fin 3) F) = A * glAut φ (g : GL (Fin 3) F) * A⁻¹ ∧ θ g' = σ (θ g)) :
    ∃ N : Subgroup K, CFSG.IsQuasisimple ↥N ∧ (∀ n ∈ N, σ n = n) ∧
      (∀ x y, σ x = x → σ y = y → ⁅x, y⁆ ∈ N) ∧
      Nonempty (↥N ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) h.fixedField) := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_pow h hq
  have : Finite F := h.finite
  obtain ⟨D⟩ := exists_realData h h2 hAu hAA
  have hk2 : (2 : h.fixedField) ≠ 0 := CFSG.GH74.Generic.S45.Uni.two_ne_zero_fixedField h h2
  have hk : ringChar h.fixedField ≠ 2 := ringChar_ne_two_of_two_ne_zero hk2
  have h3 : Nat.card h.fixedField ≠ 3 := by rw [h.card_fixedField]; omega
  have hΩq := isQuasisimple_commutator_isometryGroup hk h3 D.G D.hGs
  obtain ⟨ψ⟩ := nonempty_commutator_isometryGroup_equiv_psl2 hk h3 D.G D.hGs
  let Ω : Subgroup (GL (Fin 3) h.fixedField) := ⁅D.Iso, D.Iso⁆
  have hΩle : Ω ≤ D.Iso1 := by
    refine Subgroup.commutator_le.2 fun x hx y hy => ⟨?_, ?_⟩
    · exact D.Iso.mul_mem (D.Iso.mul_mem (D.Iso.mul_mem hx hy) (D.Iso.inv_mem hx))
        (D.Iso.inv_mem hy)
    · show ⁅x, y⁆ ∈ (Matrix.GeneralLinearGroup.det : GL (Fin 3) h.fixedField →*
        h.fixedFieldˣ).ker
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
  let ρ : ↥D.Iso1 →* K := θ.comp D.Phi
  have hρ : Function.Injective ρ := D.injective_theta_Phi hθ
  have hfixPhi : ∀ X : ↥D.Iso1, σ (ρ X) = ρ X := by
    intro X
    obtain ⟨g', hg'GL, hg'θ⟩ := hrel (D.Phi X)
    have hgg : g' = D.Phi X := Subtype.ext (by rw [hg'GL]; exact D.Phi_fixed hφ X)
    rw [hgg] at hg'θ
    exact hg'θ.symm
  have e1 : ↥(Ω.subgroupOf D.Iso1) ≃* ↥Ω := Subgroup.subgroupOfEquivOfLe hΩle
  have e2 : ↥(Ω.subgroupOf D.Iso1) ≃* ↥((Ω.subgroupOf D.Iso1).map ρ) :=
    Subgroup.equivMapOfInjective _ ρ hρ
  refine ⟨(Ω.subgroupOf D.Iso1).map ρ,
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (e1.symm.trans e2) hΩq, ?_, ?_,
    ⟨e2.symm.trans (e1.trans ψ)⟩⟩
  · rintro n ⟨ω, -, rfl⟩
    exact hfixPhi ω
  · intro x y hx hy
    obtain ⟨g, rfl, hg⟩ := exists_fixed_rep h hθ hφ hrel hx
    obtain ⟨X, hX⟩ := D.exists_Phi_of_fixed hφ hg
    obtain ⟨g', rfl, hg'⟩ := exists_fixed_rep h hθ hφ hrel hy
    obtain ⟨Y, hY⟩ := D.exists_Phi_of_fixed hφ hg'
    refine ⟨⁅X, Y⁆, ?_, ?_⟩
    · show ⁅(X : GL (Fin 3) h.fixedField), (Y : GL (Fin 3) h.fixedField)⁆ ∈ Ω
      exact Subgroup.commutator_mem_commutator X.2.1 Y.2.1
    · have h1 : θ g = ρ X := by rw [← hX]; rfl
      have h2' : θ g' = ρ Y := by rw [← hY]; rfl
      rw [h1, h2', map_commutatorElement]

theorem exists_L2_of_not_inner_U3 {K : Type} [Group K] (hq : p % 3 = 1)
    (e : K ≃* CFSG.Assembly.RankThreeEven.projSU 3 p 1) {c : MulAut K} (hc : c * c = 1)
    (hout : c ∉ (MulAut.conj : K →* MulAut K).range) :
    ∃ N : Subgroup K, CFSG.IsQuasisimple ↥N ∧ (∀ n ∈ N, c n = n) ∧
      (∀ x y, c x = x → c y = y → ⁅x, y⁆ ∈ N) ∧
      Nonempty (↥N ≃* CFSG.GH74.GLS.IVK.L2 (GaloisField p 1)) := by
  have hp : p.Prime := Fact.out
  have hp7 := seven_le_of_mod_three_eq_one hp hq
  have hp2 : p ≠ 2 := by omega
  set F := GaloisField p (2 * 1)
  have h : UnitaryFieldData p 1 F := ⟨hp, le_rfl, GaloisField.card p (2 * 1) (by norm_num)⟩
  have h5 : 5 ≤ p ^ 1 := by rw [pow_one]; omega
  have hqo : Odd (p ^ 1) := by rw [pow_one]; exact hp.odd_of_ne_two hp2
  obtain ⟨θ, hθ⟩ := CFSG.GH74.KGroups.L3Eps.Uni.exists_cover_of_equiv h
    (e.trans (CFSG.PGLModel.projSUEquivStatedProj 3 p 1))
  rcases CFSG.GH74.KGroups.L3Eps.Uni.involution_type h hp2 h5 hθ hc with
    ⟨A, hAu, hAA, hrel⟩ | ⟨φ, A, hφ, hAu, hAA, hrel⟩
  · obtain ⟨y, hy⟩ := CFSG.GH74.KGroups.L3Eps.Uni.exists_conj_of_typeI h hθ hAu hAA hrel
    exact absurd ⟨y, hy⟩ hout
  obtain ⟨N, hNq, hNfix, hNcomm, ⟨ψ⟩⟩ := exists_L2_of_typeII h h5 hqo hθ hφ hAu hAA hrel
  have : Finite F := h.finite
  have : Fintype h.fixedField := Fintype.ofFinite _
  have : Fintype (GaloisField p 1) := Fintype.ofFinite _
  have hk : Fintype.card h.fixedField = Fintype.card (GaloisField p 1) := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, h.card_fixedField,
      GaloisField.card p 1 one_ne_zero]
  obtain ⟨ι⟩ := nonempty_psl2_congr (FiniteField.ringEquivOfCardEq hk)
  exact ⟨N, hNq, hNfix, hNcomm,
    ⟨(ψ.trans ι).trans (CFSG.GH74.GLS.IVK.L2.equivPSL (GaloisField p 1)).symm⟩⟩

theorem nonempty_mulEquiv_L2_of_normal_fixed_U3 {K : Type} [Group K] (hq : p % 3 = 1)
    (e : K ≃* CFSG.Assembly.RankThreeEven.projSU 3 p 1)
    {c : MulAut K} (hc : c * c = 1) (hout : c ∉ (MulAut.conj : K →* MulAut K).range)
    {L : Subgroup K} (hL : Group.IsPerfect L) (hL1 : L ≠ ⊥)
    (hLc : L ≤ CFSG.GH74.GLS.fixedSubgroup K c)
    (hLn : ∀ y ∈ CFSG.GH74.GLS.fixedSubgroup K c, ∀ l ∈ L, y * l * y⁻¹ ∈ L) :
    Nonempty (↥L ≃* CFSG.GH74.GLS.IVK.L2 (GaloisField p 1)) := by
  obtain ⟨N, hNq, hNfix, hNcomm, hψ⟩ := exists_L2_of_not_inner_U3 hq e hc hout
  rwa [eq_of_isPerfect_of_le_fixed hNq hNfix hNcomm hL hL1 hLc hLn]

end Unitary

end CFSG.RankThree.PartTwo.Sec20.L3OddGroup
