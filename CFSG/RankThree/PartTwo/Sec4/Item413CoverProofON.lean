module

public import CFSG.RankThree.PartTwo.Sec4.Item413CoverProofG23
public import CFSG.RankThree.PartTwo.Sec4.Item413CoverProofU43McL
public import CFSG.RankThree.PartTwo.Sec4.Item417Res5ProofON
public import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRestON
public import CFSG.RankThree.PartTwo.Sec13.Item134ONProof

public section

namespace CFSG.RankThree.PartTwo.Sec4

attribute [local irreducible] dotProduct

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

namespace Res413Cover

variable {G : Type} [Group G]

theorem exists_centralizer_not_mem_of_inner {L : Subgroup G} {a l : G} (hl : l ∈ L)
    (hal : ∀ x ∈ L, a * x * a⁻¹ = l * x * l⁻¹) (ha3 : a ^ 3 = 1) (hl3 : l ^ 3 = 1)
    (haL : a ∉ L) : ∃ w : G, w ∈ Subgroup.centralizer (L : Set G) ∧ w ^ 3 = 1 ∧ w ∉ L := by
  have hla : l * a = a * l := by
    have h1 := hal l hl
    calc l * a = a * l * a⁻¹ * a := by rw [h1]; group
      _ = a * l := by group
  have hwC : l⁻¹ * a ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := hal x hx
    calc x * (l⁻¹ * a) = l⁻¹ * (l * x * l⁻¹) * l * l⁻¹ * a := by group
      _ = l⁻¹ * (a * x * a⁻¹) * l * l⁻¹ * a := by rw [h1]
      _ = l⁻¹ * a * x := by group
  refine ⟨l⁻¹ * a, hwC, ?_, fun hw => haL ?_⟩
  · have hcomm : Commute l⁻¹ a := Commute.inv_left hla
    rw [hcomm.mul_pow, inv_pow, hl3, ha3, inv_one, one_mul]
  · have : a = l * (l⁻¹ * a) := by group
    rw [this]
    exact L.mul_mem hl hw

end Res413Cover

open Res413Cover

section Of


theorem inputs413CoverON_of (h45 : Item4_5) : Inputs413CoverON := by
  intro G _ _ L A E c hyp hext
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hL := hyp.2.1
  have hZodd := odd_card_center_of_hyp413 h45 hyp
  obtain ⟨hG, -, hT, hr⟩ := hyp
  obtain ⟨hAmax, -, -, -, -, -⟩ := hT
  have hA := hAmax.prop
  obtain ⟨m, hm5, hm⟩ := exists_card_eq_of_four_lt_pRank hA hr
  have hAN : A ≤ Subgroup.normalizer (L : Set G) :=
    h45 G hG A (isPGroup_of_isElemAbelian hA) (Or.inr ⟨hA, m, by omega, hm⟩) L
      (mem_thetaComponents_of_isComponent3 hL)
  have hperf : Group.IsPerfect L := hL.1.1
  have hXq : CFSG.IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L) :=
    (CFSG.LocalCores.quasisimple_central_quotient hL.1 _
      (aschbacherSolvableCore_le_center hL.1)).1
  have hZS : Subgroup.center NativeSporadic.ON = ⊥ :=
    center_carrier_eq_bot_of_cover (s := .ONan) (by simp [sporadicCovers46])
  obtain ⟨hZ3, ⟨e₁⟩⟩ := center_eq_of_isExtOf hXq hZS hext
  have eL : L ⧸ Subgroup.center L ≃* NativeSporadic.ON :=
    (Res417Three.thetaQuotCenterEquiv hL.1).symm.trans e₁
  have hXc : Nonempty (NativeSporadic.ON ≃* NativeSporadic.Carrier .ONan) := ⟨MulEquiv.refl _⟩
  obtain ⟨eX⟩ := hXc
  have hZp : IsPGroup 3 (Subgroup.center L) := by
    refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd
      (Nat.card_pos (α := Subgroup.center L)).ne' fun {q} hq hqd => ?_)
    have hq2 := hq.two_le
    rcases (show q = 2 ∨ q = 3 ∨ 3 < q by omega) with rfl | rfl | h3
    · obtain ⟨k, hk⟩ := hZodd
      omega
    · rfl
    · obtain ⟨hpair, hnot⟩ := CFSG.RankThree.PartOne.Mult.sporadic_residual_of_center
        (eL.trans eX) hq h3 hqd
      simp only [CFSG.RankThree.PartOne.Mult.SporadicResidualPair, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hpair
      rcases hpair with ⟨-, hs⟩ | ⟨rfl, -⟩ | hs
      · simp at hs
      · exact (hnot CFSG.RankThree.PartOne.MultRes.sporadicKernelTrivial_on_seven).elim
      · simp at hs
  have hdvd : Nat.card (Subgroup.center L) ∣ 3 :=
    Census.CoverCenterThreeRest.card_center_dvd_three_of_ON hL.1 hZp eL
  have hθ := theta_eq_bot_of_card_center_dvd hL.1 hdvd
  have hZL3 : Nat.card (Subgroup.center L) = 3 := by
    have hmkinj : Function.Injective (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) := by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
      exact hθ
    have hbij : Function.Bijective (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) :=
      ⟨hmkinj, QuotientGroup.mk'_surjective _⟩
    set e := MulEquiv.ofBijective (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) hbij
    rw [← hZ3, ← Subgroup.map_center_eq e]
    exact (Subgroup.card_map_of_injective e.injective).symm
  obtain ⟨ψ⟩ := Sec13.ON134.nonempty_equiv_model (X := L) hperf ⟨hZL3, ⟨eL⟩⟩
  obtain ⟨a, haA, haL⟩ : ∃ a ∈ A, a ∉ L := by
    by_contra hall
    push Not at hall
    have hAL : A ≤ L := fun a ha => hall a ha
    set B : Subgroup CFSG.RankThree.Native.ONTriple.GM := (A.subgroupOf L).map ψ.toMonoidHom
      with hB
    have hBcard : Nat.card B = 3 ^ m := by
      rw [hB, Subgroup.card_map_of_injective ψ.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv, hm]
    have hB3 : IsPGroup 3 B := IsPGroup.of_card hBcard
    have hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      have h1 : (x : G) * y = y * x := congrArg Subtype.val (hA.1.is_comm.comm
        ⟨x, Subgroup.mem_subgroupOf.mp hx⟩ ⟨y, Subgroup.mem_subgroupOf.mp hy⟩)
      exact Subtype.ext h1
    have h27 := Res417Five.card_le_27_of_abelian_model hB3 hBab
    rw [hBcard] at h27
    have h243 : 3 ^ 5 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm5
    omega
  have ha3 : a ^ 3 = 1 := hA.2 a haA
  have hOut : ¬ 3 ∣ Nat.card (Outer L) :=
    not_three_dvd_card_outer_of_quotient (eL.trans eX) inputs47Core_outON
  set σ := L.normalizerMonoidHom ⟨a, hAN haA⟩ with hσ
  have hσ3 : σ ^ 3 = 1 := by
    have h1 : (⟨a, hAN haA⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using ha3)
    rw [hσ, ← map_pow, h1, map_one]
  obtain ⟨l, hl⟩ := mem_range_conj_of_pow_three hOut hσ3
  have hal : ∀ x ∈ L, a * x * a⁻¹ = (l : G) * x * (l : G)⁻¹ := by
    intro x hx
    have h1 := congrArg (fun τ : MulAut L => ((τ ⟨x, hx⟩ : L) : G)) hl
    exact h1.symm
  have hl3 : (l : G) ^ 3 = 1 := by
    have hc : l ^ 3 ∈ Subgroup.center L := by
      rw [← ker_conj_eq_center, MonoidHom.mem_ker, map_pow, hl, hσ3]
    have h9 := pow_card_eq_one' (G := Subgroup.center L) (x := ⟨_, hc⟩)
    rw [hZL3] at h9
    have h9' : l ^ 3 ^ 2 = 1 := by
      have h := congrArg Subtype.val h9
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h
      rw [← h, ← pow_mul]
      norm_num
    have := congrArg Subtype.val (Sec13.ON134.pow_three_eq_one ψ h9')
    simpa using this
  obtain ⟨w, hwC, hw3, hwL⟩ :=
    exists_centralizer_not_mem_of_inner l.2 hal ha3 hl3 haL
  obtain ⟨D', hD'⟩ := Res417Five.exists_isE27_model
  obtain ⟨S', hS'1, hS'2, hD'S'⟩ := Res417Five.exists_twoGroup_model hD'
  set ι : CFSG.RankThree.Native.ONTriple.GM →* G := L.subtype.comp ψ.symm.toMonoidHom with hι
  have hιinj : Function.Injective ι := L.subtype_injective.comp ψ.symm.injective
  have hιL : ∀ g, ι g ∈ L := fun g => (ψ.symm g).2
  have hD : Late.IsE27 (D'.map ι) := ⟨isElemAbelian_map ι hD'.1,
    by rw [Subgroup.card_map_of_injective hιinj, hD'.2]⟩
  have hS2 : IsPGroup 2 (S'.map ι) := hS'2.map ι
  have hS1 : S'.map ι ≠ ⊥ := fun hb =>
    hS'1 ((Subgroup.map_eq_bot_iff_of_injective _ hιinj).mp hb)
  have hDS : D'.map ι ≤ Subgroup.normalizer ((S'.map ι : Subgroup G) : Set G) :=
    (Subgroup.map_mono hD'S').trans (Subgroup.le_normalizer_map ι)
  have hwD : ∀ d ∈ D'.map ι, d * w = w * d := by
    rintro _ ⟨d, -, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp hwC _ (hιL d)
  have hwS : w ∈ Subgroup.normalizer ((S'.map ι : Subgroup G) : Set G) := by
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨s, -, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp hwC _ (hιL s)
  obtain ⟨d, -, rfl⟩ := Res417Five.mem_of_commute_of_isE27 hG hD hS2 hS1 hDS hw3 hwD hwS
  exact hwL (hιL d)

end Of

section Holds

theorem inputs413CoverON_holds
    : Inputs413CoverON :=
  inputs413CoverON_of rank3II_4_5

end Holds

end CFSG.RankThree.PartTwo.Sec4
