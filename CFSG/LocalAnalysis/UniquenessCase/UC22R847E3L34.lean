module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229L34Rank
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z3Good
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z3Inv
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z6
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bridge13
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128Layer
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus)

variable {G : Type} [Group G] [Finite G]

theorem R847E3.normalizer_le_or_l34 (hG3 : Gls3StronglyThreeEmbeddedPlus)
    (hRee : CFSG.AGLEmbedding.KFactReeInvolution) (hK3 : StronglyEmbeddedThree) (k : Sec7Core4 G)
    (hp3 : k.p = 3) {Y : Subgroup G} (hY : Y ∈ calC k.M) {q : ℕ} (hq : q.Prime)
    {X : Subgroup G} (hXY : X ≤ Y) (hXc : Nat.card X = q) {B₁ : Subgroup G} (hB₁M : B₁ ≤ k.M)
    (hB₁ : IsElemAbelian k.p B₁) (hB₁c : Nat.card B₁ = k.p ^ 2)
    (hB₁X : B₁ ≤ centralizer (X : Set G))
    (hB₁Y : ∀ b ∈ B₁, ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ pCoreOf 2 k.M) {t : G}
    (ht : t ∈ Y ⊓ normalizer (X : Set G)) (ht2 : orderOf t = 2) :
    normalizer (X : Set G) ≤ k.M ∨ (Sec7Core4.Config k (normalizer (X : Set G)) ∧
      IsoLie ↥(CFSG.generalizedFitting (↥(normalizer (X : Set G)) ⧸
        CFSG.pPrimeCore k.p ↥(normalizer (X : Set G))))
        (.A 2 ⟨2, 2, Nat.prime_two, by norm_num⟩)) := by
  have hX1 : X ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hXc
    exact hq.one_lt.ne hXc
  have hYM : Y ≤ k.M := hY.1.le
  rcases uc22ine229_normalizer_le_or_card_le_two k hp3 hK3 hX1 (hXY.trans hYM) hB₁M hB₁ hB₁c
    hB₁X with h | hQ
  · exact Or.inl h
  by_contra hnot
  have hnot' : ¬ normalizer (X : Set G) ≤ k.M := fun h => hnot (Or.inl h)
  have hB₁N : B₁ ≤ normalizer (X : Set G) :=
    hB₁X.trans (Subgroup.centralizer_le_normalizer (X : Set G))
  have hH := k.config_normalizer hX1 (hXY.trans hYM)
    (CFSG.SectionRank.le_pRank k.prime.one_lt (le_inf hB₁M hB₁N) hB₁ hB₁c) hnot'
  have htC := uc22ine229_le_centralizer3 hB₁M hQ (by rwa [hp3] at hB₁) hB₁X hB₁Y ht
  have h75 := k.step75_of_stronglyEmbeddedThree hp3 hK3
  rcases (k.goodZ3_of_config hG3 hRee hp3 hH).2 with hC2 | hL
  · exact k.false_of_involution h75 hH hC2 (le_inf hB₁N hB₁M) hB₁ hB₁c ⟨ht.2, hYM ht.1⟩ ht2
      fun a ha => (Subgroup.mem_centralizer_iff.1 htC) a ha
  · exact hnot (Or.inr ⟨hH, hL⟩)

theorem R847E3.two_le_pRank_centE_of_l34 (hG3 : Gls3StronglyThreeEmbeddedPlus)
    (hRee : CFSG.AGLEmbedding.KFactReeInvolution) (k : Sec7Core4 G) (hp3 : k.p = 3)
    {Y : Subgroup G} (hY : Y ∈ calC k.M) {X : Subgroup G} (hXY : X ≤ Y) {q : ℕ} (hq : q.Prime)
    (hq5 : 5 ≤ q) (hXc : Nat.card X = q) (hq1 : CFSG.Open.pRank q Y ≤ 1)
    (hH : Sec7Core4.Config k (normalizer (X : Set G)))
    (hF : IsoLie ↥(CFSG.generalizedFitting (↥(normalizer (X : Set G)) ⧸
        CFSG.pPrimeCore k.p ↥(normalizer (X : Set G))))
      (.A 2 ⟨2, 2, Nat.prime_two, by norm_num⟩))
    {B₁ : Subgroup G} (hB₁M : B₁ ≤ k.M) (hB₁ : IsElemAbelian 3 B₁) (hB₁c : Nat.card B₁ = 3 ^ 2)
    (hB₁Y : ∀ b ∈ B₁, ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ pCoreOf 2 k.M) :
    2 ≤ CFSG.Open.pRank 3 (barPreimage k.M (centE k.M)) := by
  obtain ⟨hnorm, hmul, hsol, -⟩ :=
    uc22ine229_l34_decomp hG3 hRee k hp3 hY hXY hq hq5 hXc hq1 hH hF
  have hYM : Y ≤ k.M := hY.1.le
  haveI hYb : (barImage k.M Y).Normal := PartTwo.s13_barImage_normal
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hYM).2 hnorm)
  let f : ↥(normalizer (X : Set G) ⊓ k.M) →* Bar2 k.M ⧸ barImage k.M Y :=
    (QuotientGroup.mk' (barImage k.M Y)).comp
      ((uc22p21cPi k.M).comp (Subgroup.inclusion inf_le_right))
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective _ z
    obtain ⟨m, rfl⟩ := uc22p21c_pi_surjective k.M w
    obtain ⟨h, hh, y, hy, hm⟩ := hmul m m.2
    refine ⟨⟨h, hh⟩, ?_⟩
    have hyb : QuotientGroup.mk' (barImage k.M Y) (uc22p21cPi k.M ⟨y, hYM hy⟩) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (uc22p21c_mem_barImage.2 ⟨⟨y, hYM hy⟩, hy, rfl⟩)
    have hm' : m = ⟨h, hh.2⟩ * ⟨y, hYM hy⟩ := Subtype.ext hm
    change QuotientGroup.mk' (barImage k.M Y) (uc22p21cPi k.M ⟨h, hh.2⟩) =
      QuotientGroup.mk' (barImage k.M Y) (uc22p21cPi k.M m)
    rw [hm', map_mul, map_mul, hyb, mul_one]
  haveI : Group.IsSolvable ↥(normalizer (X : Set G) ⊓ k.M) := hsol
  have hlayer : CFSG.layer (Bar2 k.M) ≤ barImage k.M Y :=
    CFSG.OddStandard.SmallF3.Omega.sec128_layer_le _ (solvable_of_surjective hf)
  have hle : B₁ ≤ barPreimage k.M (centE k.M) := by
    intro b hb
    refine uc22p21c_mem_barPreimage.2 ⟨hB₁M hb, Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
    obtain ⟨⟨y, hyM⟩, hy, rfl⟩ := uc22p21c_mem_barImage.1 (hlayer hl)
    have hc : b * y * b⁻¹ * y⁻¹ ∈ k.M := k.M.mul_mem (k.M.mul_mem (k.M.mul_mem (hB₁M hb) hyM)
      (k.M.inv_mem (hB₁M hb))) (k.M.inv_mem hyM)
    have h1 : uc22p21cPi k.M ⟨b * y * b⁻¹ * y⁻¹, hc⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).2 ((CFSG.mem_openPCoreOf_iff ⟨_, hc⟩).1 (hB₁Y b hb y hy))
    have h2 : (⟨b * y * b⁻¹ * y⁻¹, hc⟩ : ↥k.M) =
        ⟨b, hB₁M hb⟩ * ⟨y, hyM⟩ * ⟨b, hB₁M hb⟩⁻¹ * ⟨y, hyM⟩⁻¹ := rfl
    rw [h2, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    exact (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)).symm
  exact CFSG.SectionRank.le_pRank (by norm_num) hle hB₁ hB₁c

end CFSG.LocalAnalysis.UniquenessCase.UC22
