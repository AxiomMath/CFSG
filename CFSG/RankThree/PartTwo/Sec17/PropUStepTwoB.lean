module

public import CFSG.RankThree.PartTwo.Sec17.PropUStepTwoA
public import CFSG.RankThree.PartTwo.Sec17.PropUGFree
public import CFSG.RankThree.PartTwo.Sec17.Ronan1724BFTStatement
public import CFSG.Sporadic.J2
public import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
public import CFSG.Foundations.HigherElementaryThompson
public import CFSG.Walter.Cited.HuppertBasic
public import CFSG.RankThree.PartTwo.Sec3.TwoGroupPrimeFiveAction
public import CFSG.Foundations.SteinbergCAGeneratedCoreNodes
public import CFSG.LocalAnalysis.SectionRank.GroupRankTransport

public section

namespace CFSG.RankThree.PartTwo.Sec17.PropU

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec17 CFSG.GH74.GLS
open scoped commutatorElement

theorem exists_elemAbelianEight_of_central
    (hCover : J2CoverHasElemAbelianEight) {Y : Type} [Group Y] [Finite Y] (S : Subgroup Y)
    [S.Normal] (hS : IsPGroup 2 S) (hSc : S ≤ Subgroup.center Y)
    (hYJ : Nonempty ((Y ⧸ S) ≃* J2)) :
    ∃ E : Subgroup Y, CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 8 := by
  classical
  obtain ⟨e⟩ := hYJ
  haveI : IsSimpleGroup J2 := Sporadic.J2.isSimpleGroup_J2
  have hncomm : ¬ IsMulCommutative J2 := by
    intro h
    have hp := IsSimpleGroup.prime_card (α := J2)
    rw [CFSG.RankThree.PartTwo.KFacts.KS14.card_nativeJ2] at hp
    exact absurd hp (by norm_num)
  have hperfJ : Group.IsPerfect J2 :=
    CFSG.OrderReductions.Helpers.simple_noncommutative_isPerfect J2 hncomm
  haveI := hperfJ
  have hperf : Group.IsPerfect (Y ⧸ S) :=
    Group.IsPerfect.ofSurjective (G := J2) (f := e.symm.toMonoidHom) e.symm.surjective
  obtain ⟨W, hWperf, hWS⟩ := exists_perfect_sup_eq_top S hperf
  set Z : Subgroup ↥W := S.subgroupOf W with hZdef
  haveI : Z.Normal := inferInstance
  have hZc : Z ≤ Subgroup.center ↥W := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hzS : (z : Y) ∈ S := hz
    have := Subgroup.mem_center_iff.mp (hSc hzS) (g : Y)
    simpa using this
  have hZp : IsPGroup 2 Z := hS.comap_subtype
  let f : ↥W →* Y ⧸ S := (QuotientGroup.mk' S).comp W.subtype
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have hy : y ∈ W ⊔ S := by rw [hWS]; trivial
    obtain ⟨w, hw, s, hs, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
    refine ⟨⟨w, hw⟩, ?_⟩
    show (QuotientGroup.mk w : Y ⧸ S) = QuotientGroup.mk (w * s)
    exact QuotientGroup.eq.mpr (by simpa using hs)
  have hker : f.ker = Z := by
    ext w
    simp [f, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, hZdef, Subgroup.mem_subgroupOf]
  have hiso : Nonempty (↥W ⧸ Z ≃* J2) :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)).trans e⟩
  obtain ⟨E, hE, hE8⟩ := hCover ↥W Z hZc hZp hWperf hiso
  haveI := hE.1
  refine ⟨E.map W.subtype, ⟨inferInstance, ?_⟩, ?_⟩
  · rintro x ⟨a, ha, rfl⟩
    have := hE.2 a ha
    simpa using congrArg Subtype.val this
  · rw [Subgroup.card_map_of_injective W.subtype_injective]
    exact hE8

theorem false_of_elemAbelianEight (hFT : J2NotSectionOfGLFourTwo)
    {q : ℕ} [Fact q.Prime] (hq5 : 5 ≤ q) {D Y : Type} [Group D] [Finite D] [Group Y] [Finite Y]
    (hD : IsPGroup q D) (hexp : ∀ x : D, x ^ q = 1) (hcl : commutator D ≤ Subgroup.center D)
    (ρ : Y →* MulAut D) (hρ : Function.Injective ρ) (S : Subgroup Y) [S.Normal]
    (hS : IsPGroup 2 S) (hF5 : ∀ K : Subgroup Y, K.Normal → K ≤ S ∨ K = ⊤)
    (hYJ : Nonempty ((Y ⧸ S) ≃* J2)) (hY3 : oPrimeResidual 3 Y = ⊤)
    (hrank : ∀ y : Y, y ≠ 1 → IsPGroup 2 (Subgroup.zpowers y) →
      CFSG.pRank q ↥(fixedSubgroupOf (ρ y)) ≤ 2)
    (E : Subgroup Y) (hE : CFSG.Assembly.IsElemAbelian 2 E) (hE8 : Nat.card E = 8) : False := by
  obtain ⟨hEc, hEexp⟩ := hE
  obtain ⟨e⟩ := hYJ
  letI : CommGroup ↥E :=
    { (inferInstance : Group ↥E) with mul_comm := fun a b => hEc.is_comm.comm a b }
  have hE2 : ∀ a : ↥E, a ^ 2 = 1 := fun a => Subtype.ext (by simpa using hEexp (a : Y) a.2)
  have hρ' : Function.Injective (ρ.comp E.subtype) := fun a b hab => Subtype.ext (hρ hab)
  have hfix : ∀ a : ↥E, a ≠ 1 → CFSG.pRank q ↥(fixedSubgroupOf ((ρ.comp E.subtype) a)) ≤ 2 := by
    intro a ha
    refine hrank (a : Y) (fun h => ha (Subtype.ext h)) ?_
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one (hEexp (a : Y) a.2)
  obtain ⟨-, hVcomm, hVexp, hVelem, d, hVcard, -⟩ :=
    CFSG.GroupTheory.frattini_elementary_quotient hD
  obtain ⟨hpr, -, -⟩ := CFSG.RankThree.PartTwo.class_two_eight_action_inverting_quotient
    (p := q) (A := ↥E) (by omega) hD hexp hcl hE2 hE8 (ρ.comp E.subtype) hρ' hfix
  haveI := hVelem
  have hk : CFSG.pRank q (D ⧸ frattini D) = d :=
    CFSG.pRank_eq_of_card_eq_pow (p := q) (by omega) hVcard
  rw [hk] at hpr
  have hdle : d ≤ 4 := by omega
  have hVle : Nat.card (D ⧸ frattini D) ≤ q ^ 4 := by
    rw [hVcard]
    exact Nat.pow_le_pow_right (by omega) hdle
  let φ : Y →* MulAut (D ⧸ frattini D) := (CFSG.Walter.Huppert.frattiniAut D).comp ρ
  have hker : φ.ker ≤ S := by
    rcases hF5 φ.ker inferInstance with h | h
    · exact h
    · exfalso
      have htriv : ∀ y : Y, CFSG.Walter.Huppert.frattiniAut D (ρ y) = 1 := by
        intro y
        have hy : y ∈ φ.ker := by
          rw [h]
          exact Subgroup.mem_top y
        exact MonoidHom.mem_ker.mp hy
      have key : ∀ y : Y, (∃ k : ℕ, y ^ (3 ^ k) = 1) → y = 1 := by
        rintro y ⟨k, hk3⟩
        have h1 : orderOf (ρ y) ∣ 3 ^ k :=
          orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hk3, map_one])
        have h3 : Nat.Coprime q 3 :=
          (Nat.coprime_primes (Fact.out : q.Prime) Nat.prime_three).mpr (by omega)
        have hcop : Nat.Coprime q (orderOf (ρ y)) :=
          Nat.Coprime.coprime_dvd_right h1 (Nat.Coprime.pow_right k h3)
        have hτ : ρ y = 1 := CFSG.Walter.Huppert.eq_one_of_frattiniAut_eq_one hD hcop (htriv y)
        apply hρ
        rw [hτ, map_one]
      have hYbot : ∀ x : Y, x = 1 := by
        intro x
        have hx : x ∈ oPrimeResidual 3 Y := by
          rw [hY3]
          exact Subgroup.mem_top x
        have hle : oPrimeResidual 3 Y ≤ ⊥ := by
          unfold oPrimeResidual
          rw [Subgroup.closure_le]
          intro z hz
          exact Subgroup.mem_bot.mpr (key z hz)
        exact Subgroup.mem_bot.mp (hle hx)
      have hsub : Subsingleton Y := ⟨fun a b => (hYbot a).trans (hYbot b).symm⟩
      have hY1 : Nat.card Y = 1 := Nat.card_of_subsingleton (1 : Y)
      have hdvd : Nat.card (Y ⧸ S) ∣ Nat.card Y := Subgroup.card_quotient_dvd_card S
      have hJ : Nat.card (Y ⧸ S) = 604800 :=
        (Nat.card_congr e.toEquiv).trans CFSG.RankThree.PartTwo.KFacts.KS14.card_nativeJ2
      rw [hJ, hY1] at hdvd
      norm_num at hdvd
  letI : CommGroup (D ⧸ frattini D) :=
    { (inferInstance : Group (D ⧸ frattini D)) with mul_comm := fun a b => hVcomm.is_comm.comm a b }
  haveI hemp := hFT q Fact.out hq5 (D ⧸ frattini D) hVexp hVle Y φ S hS hker
  exact IsEmpty.false e

theorem pu_conj_inl {D Y : Type} [Group D] [Group Y] (ρ : Y →* MulAut D) (a : Y) (d : D) :
    (SemidirectProduct.inr a : D ⋊[ρ] Y) * SemidirectProduct.inl d * (SemidirectProduct.inr a)⁻¹ =
      SemidirectProduct.inl (ρ a d) := by
  have h := (SemidirectProduct.inl_aut (φ := ρ) a d).symm
  rw [map_inv] at h
  exact h

theorem pu_comm_iff {D Y : Type} [Group D] [Group Y] (ρ : Y →* MulAut D) (a : Y) (d : D) :
    (SemidirectProduct.inl d : D ⋊[ρ] Y) * SemidirectProduct.inr a =
      SemidirectProduct.inr a * SemidirectProduct.inl d ↔ ρ a d = d := by
  have key := pu_conj_inl ρ a d
  constructor
  · intro h
    have h2 : (SemidirectProduct.inl (ρ a d) : D ⋊[ρ] Y) = SemidirectProduct.inl d := by
      rw [← key, ← h, mul_inv_cancel_right]
    exact SemidirectProduct.inl_injective h2
  · intro h
    rw [h] at key
    exact (mul_inv_eq_iff_eq_mul.mp key).symm

theorem false_of_order_seven_acts {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) {D Y : Type} [Group D]
    [Finite D] [Group Y] [Finite Y] (hD : IsPGroup q D) (ρ : Y →* MulAut D)
    (hρ : Function.Injective ρ) (S : Subgroup Y) [S.Normal] (hS : IsPGroup 2 S)
    (hrank : ∀ y : Y, y ≠ 1 → IsPGroup 2 (Subgroup.zpowers y) →
      CFSG.pRank q ↥(fixedSubgroupOf (ρ y)) ≤ 2)
    {y : Y} (hy : orderOf y = 7) (hnc : ¬ ∀ s ∈ S, y * s = s * y) : False := by
  have hq : Nat.Prime q := Fact.out
  haveI : Finite (D ⋊[ρ] Y) :=
    Finite.of_equiv (D × Y) (SemidirectProduct.equivProd (φ := ρ)).symm
  have hi : Function.Injective (SemidirectProduct.inl : D →* D ⋊[ρ] Y) :=
    SemidirectProduct.inl_injective
  have hj : Function.Injective (SemidirectProduct.inr : Y →* D ⋊[ρ] Y) :=
    SemidirectProduct.inr_injective
  obtain ⟨P, hP⟩ : ∃ P : Subgroup (D ⋊[ρ] Y),
      P = (SemidirectProduct.inl : D →* D ⋊[ρ] Y).range := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : Subgroup Y, A = ⁅S, Subgroup.zpowers y⁆ := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : Subgroup (D ⋊[ρ] Y),
      U = A.map (SemidirectProduct.inr : Y →* D ⋊[ρ] Y) := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : Subgroup (D ⋊[ρ] Y),
      X = (Subgroup.zpowers y).map (SemidirectProduct.inr : Y →* D ⋊[ρ] Y) := ⟨_, rfl⟩
  have hSub : A ≤ S := by
    rw [hA]
    exact Subgroup.commutator_le_left S (Subgroup.zpowers y)
  have hA2 : IsPGroup 2 A := by
    rw [hA]
    exact hS.to_le (Subgroup.commutator_le_left S (Subgroup.zpowers y))
  have hAcomm : ⁅A, Subgroup.zpowers y⁆ = A := by
    rw [hA]
    exact commutator_commutator_zpowers_eq S hS hy
  have hP2 : IsPGroup q P := by
    rw [hP]
    exact hD.of_surjective (SemidirectProduct.inl : D →* D ⋊[ρ] Y).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _)
  have hU2 : IsPGroup 2 U := by
    rw [hU]
    exact hA2.map (SemidirectProduct.inr : Y →* D ⋊[ρ] Y)
  have hX7 : Nat.card X = 7 := by
    rw [hX, Subgroup.card_map_of_injective hj, Nat.card_zpowers, hy]
  have hUX : ⁅U, X⁆ = U := by
    rw [hU, hX, ← Subgroup.map_commutator, hAcomm]
  have hPn : P.Normal := by
    rw [hP, SemidirectProduct.range_inl_eq_ker_rightHom]
    infer_instance
  have hNtop : Subgroup.normalizer (P : Set (D ⋊[ρ] Y)) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr hPn
  have hUP : U ≤ Subgroup.normalizer (P : Set (D ⋊[ρ] Y)) := by
    rw [hNtop]
    exact le_top
  have hXP : X ≤ Subgroup.normalizer (P : Set (D ⋊[ρ] Y)) := by
    rw [hNtop]
    exact le_top
  obtain ⟨s, hs, hne⟩ : ∃ s ∈ S, y * s ≠ s * y := by
    push Not at hnc
    exact hnc
  have hcomm_ne : ⁅s, y⁆ ≠ 1 := fun h => hne (commutatorElement_eq_one_iff_commute.mp h).symm.eq
  have hU1 : U ≠ ⊥ := by
    intro hUb
    have hmem : (SemidirectProduct.inr ⁅s, y⁆ : D ⋊[ρ] Y) ∈ U := by
      rw [hU]
      apply Subgroup.mem_map_of_mem
      rw [hA]
      exact Subgroup.commutator_mem_commutator hs (Subgroup.mem_zpowers y)
    rw [hUb, Subgroup.mem_bot, map_eq_one_iff (SemidirectProduct.inr : Y →* D ⋊[ρ] Y)
      SemidirectProduct.inr_injective] at hmem
    exact hcomm_ne hmem
  have hfaith : U ⊓ Subgroup.centralizer (P : Set (D ⋊[ρ] Y)) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgU, hgC⟩ := Subgroup.mem_inf.mp hg
    rw [hU] at hgU
    obtain ⟨a, _, rfl⟩ := Subgroup.mem_map.mp hgU
    have hfixall : ∀ d : D, ρ a d = d := by
      intro d
      have hdP : (SemidirectProduct.inl d : D ⋊[ρ] Y) ∈ P := by
        rw [hP]
        exact MonoidHom.mem_range.mpr ⟨d, rfl⟩
      exact (pu_comm_iff ρ a d).mp (Subgroup.mem_centralizer_iff.mp hgC _ hdP)
    have hρa : ρ a = 1 := by
      ext d
      exact hfixall d
    have ha1 : a = 1 := hρ (by rw [hρa, map_one])
    rw [Subgroup.mem_bot, ha1, map_one]
  have hfix : ∀ u ∈ U, u ≠ 1 →
      CFSG.Assembly.pRank q (P ⊓ Subgroup.centralizer ({u} : Set (D ⋊[ρ] Y))) ≤ 2 := by
    intro u hu hu1
    rw [hU] at hu
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hu
    have ha1 : a ≠ 1 := fun h => hu1 (by rw [h, map_one])
    have haS : a ∈ S := hSub ha
    have hS2 : IsPGroup 2 (Subgroup.zpowers a) := hS.to_le (Subgroup.zpowers_le.mpr haS)
    have hbound := hrank a ha1 hS2
    have hset : P ⊓ Subgroup.centralizer ({SemidirectProduct.inr a} : Set (D ⋊[ρ] Y)) =
        (fixedSubgroupOf (ρ a)).map (SemidirectProduct.inl : D →* D ⋊[ρ] Y) := by
      ext g
      constructor
      · intro hg
        obtain ⟨hgP, hgC⟩ := Subgroup.mem_inf.mp hg
        rw [hP] at hgP
        obtain ⟨d, rfl⟩ := MonoidHom.mem_range.mp hgP
        have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hgC
        exact Subgroup.mem_map.mpr
          ⟨d, (CFSG.RankThree.PartTwo.mem_fixedSubgroupOf _ _).mpr ((pu_comm_iff ρ a d).mp hcomm),
            rfl⟩
      · intro hg
        obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hg
        refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.mem_centralizer_singleton_iff.mpr
          ((pu_comm_iff ρ a d).mpr ((CFSG.RankThree.PartTwo.mem_fixedSubgroupOf _ _).mp hd))⟩
        rw [hP]
        exact MonoidHom.mem_range.mpr ⟨d, rfl⟩
    rw [hset]
    calc CFSG.Assembly.pRank q ((fixedSubgroupOf (ρ a)).map (SemidirectProduct.inl : D →* D ⋊[ρ] Y))
        = CFSG.pRank q ↥((fixedSubgroupOf (ρ a)).map (SemidirectProduct.inl : D →* D ⋊[ρ] Y)) :=
          (CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank hq _).symm
      _ = CFSG.pRank q ↥(fixedSubgroupOf (ρ a)) :=
          (CFSG.pRank_congr_of_mulEquiv ((fixedSubgroupOf (ρ a)).equivMapOfInjective
            (SemidirectProduct.inl : D →* D ⋊[ρ] Y) hi) q).symm
      _ ≤ 2 := hbound
  have h75 : (7 : ℕ) = 5 :=
    CFSG.RankThree.PartTwo.Sec3.rank3II_3_6 (p := q) (q := 7) hq hq2 (by norm_num)
      (by norm_num) hP2 hU2 hX7 hUX hU1 hUP hXP hfaith hfix
  omega

end CFSG.RankThree.PartTwo.Sec17.PropU
