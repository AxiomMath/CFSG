module

public import CFSG.RankThree.PartTwo.Sec21.Item21EarlyProofQuasi
import CFSG.RankThree.PartTwo.Sec13.Item135SimpleReduce
import CFSG.RankThree.PartTwo.Sec21.Item21EarlyProofMono
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCover
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderThreeComplement
import CFSG.GroupTheory.ABGDGroups.LinearEmbedding
import CFSG.RankThree.PartTwo.Sec21.Hering233iQuasi
import CFSG.RankThree.PartTwo.Sec4.Item413Setup

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.Blueprint
open scoped commutatorElement
open Item21EarlyProof

namespace Hering2125

theorem isQuasisimple_of_items (h44 : Sec4.Item4_4)
    (hOrd : KS213Order) (hNine : KS213Nine) (hTwo : KS213TwoRank)
    {X : Type} [Group X] [Finite X] [hXp : Group.IsPerfect X] (hX4 : SectionFourHyp X)
    (hq : IsQuasisimple (X ⧸ aschbacherSolvableCore 3 X))
    (hB : IsBar211 (X ⧸ aschbacherSolvableCore 3 X)) (hO2c : CFSG.pCore 2 X ≤ Subgroup.center X)
    (h3Z : ¬ 3 ∣ Nat.card (Subgroup.center (X ⧸ aschbacherSolvableCore 3 X))) :
    IsQuasisimple X := by
  obtain ⟨hTs, -, hT3, -⟩ := solvable_prime_complement_core_characterization (H := X)
    Nat.prime_three
  set T := aschbacherSolvableCore 3 X with hT
  set K₀ := centerPre T with hK₀
  have hK₀s : Group.IsSolvable K₀ := isSolvable_centerPre T hTs
  have : IsSimpleGroup ((X ⧸ aschbacherSolvableCore 3 X) ⧸
      Subgroup.center (X ⧸ aschbacherSolvableCore 3 X)) := hq.2.1
  have : IsSimpleGroup (X ⧸ K₀) := (centerPreEquiv T).isSimpleGroup
  have hnc : ∃ a b : X ⧸ K₀, a * b ≠ b * a := by
    obtain ⟨-, -, a, b, hab⟩ := hq
    refine ⟨(centerPreEquiv T).symm a, (centerPreEquiv T).symm b, fun h => hab ?_⟩
    simpa using congrArg (centerPreEquiv T) h
  have hZK : Subgroup.center (X ⧸ K₀) = ⊥ := center_eq_bot_of_isSimpleGroup hnc
  have hbig : 5616 < Nat.card (X ⧸ K₀) := by
    rw [Nat.card_congr (centerPreEquiv T).toEquiv]
    exact hOrd _ hB
  have hcardA : ∀ n : ℕ, 5 ≤ n → n ≤ 6 →
      1 < Nat.card (alternatingGroup (Fin n)) ∧ Nat.card (alternatingGroup (Fin n)) < 5616 := by
    intro n hn5 hn6
    rw [KFacts.KS14.card_alternatingGroup_fin (by omega)]
    interval_cases n <;> decide
  rcases h44 X hX4 hXp K₀ hK₀s inferInstance with
    h1 | he2 | ⟨p, hp, hp3, he3⟩ | (he4 | h4b) | ⟨-, h5⟩
  ·
    exact isQuasisimple_of_quotient_pCore_two hq h1 hO2c
  ·
    exfalso
    obtain ⟨e2⟩ := he2
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hc : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) = 120 := by
      rw [Sec4.Census.card_SL2]
      norm_num
    exact Sec13.false_of_surjective_of_card_lt hK₀s (e2.toMonoidHom.comp (QuotientGroup.mk' _))
      (e2.surjective.comp (QuotientGroup.mk'_surjective _)) (by omega) (by omega)
  ·
    exfalso
    obtain ⟨e3⟩ := he3
    obtain ⟨E', hE'3, hE'9⟩ := hNine _ hB
    obtain ⟨E, hE3, hE9⟩ := exists_nine_quotient T hE'3 hE'9
    exact Sec13.false_of_oTwoP_equiv_SL2 hp hp3 e3 hE3 hE9
  ·
    exfalso
    obtain ⟨e4⟩ := he4
    have hc : Nat.card (projSL 3 (GaloisField 3 1)) = 5616 := by
      rw [← Nat.card_congr Sec4.Census.sl3EquivProjSL.toEquiv, Sec4.Census.card_SL3_three]
    exact Sec13.false_of_surjective_of_card_lt hK₀s (e4.toMonoidHom.comp (QuotientGroup.mk' _))
      (e4.surjective.comp (QuotientGroup.mk'_surjective _)) (by omega) (by omega)
  ·
    obtain ⟨h1, h2⟩ := hcardA 5 le_rfl (by norm_num)
    exact (Sec13.false_of_isExtOf_of_card_lt hK₀s h4b h1 (by omega)).elim
  ·
    have hK₀3 : ¬ 3 ∣ Nat.card K₀ := not_dvd_card_centerPre T Nat.prime_three hT3 h3Z
    exfalso
    rcases h5 hK₀3 with ⟨hm, hO | hext⟩ | ⟨-, hext | hext | hext⟩
    ·
      have hOK := Sec13.oddCore_le_of_isQuasisimple hK₀s hO
      have hZ := Sec13.center_quotient_oddCore_eq_map hK₀s hZK hO hOK
      let e : (X ⧸ CFSG.oddCore X) ⧸ Subgroup.center (X ⧸ CFSG.oddCore X) ≃* X ⧸ K₀ :=
        (QuotientGroup.quotientMulEquivOfEq hZ).trans
          (QuotientGroup.quotientQuotientEquivQuotient _ _ hOK)
      have hZ2 : IsPGroup 2 (Subgroup.center (X ⧸ CFSG.oddCore X)) :=
        Sec4.Census.isPGroup_two_center_of_oddCore_eq_bot
          (CFSG.LyonsUnitaryFour.oddCore_quotient_oddCore_eq_bot X)
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hrank : CFSG.Open.pRank 2 (⊤ : Subgroup (X ⧸ CFSG.oddCore X)) =
          CFSG.Open.pRank 2 (⊤ : Subgroup X) :=
        CFSG.SectionRank.pRank_quotient_eq (CFSG.oddCore X) (fun h2 =>
          (Nat.not_even_iff_odd.mpr (CFSG.ABGDGroups.odd_card_oddCore X))
            (even_iff_two_dvd.mpr h2))
      have := hTwo (X ⧸ aschbacherSolvableCore 3 X) hB (X ⧸ CFSG.oddCore X) hO hZ2
        ⟨e.trans (centerPreEquiv T)⟩
      omega
    · obtain ⟨h1, h2⟩ := hcardA 5 le_rfl (by norm_num)
      exact Sec13.false_of_isExtOf_of_card_lt hK₀s hext h1 (by omega)
    · obtain ⟨h1, h2⟩ := hcardA 5 le_rfl (by norm_num)
      exact Sec13.false_of_isExtOf_of_card_lt hK₀s hext h1 (by omega)
    · obtain ⟨h1, h2⟩ := hcardA 5 le_rfl (by norm_num)
      exact Sec13.false_of_isExtOf_of_card_lt hK₀s hext h1 (by omega)
    · obtain ⟨h1, h2⟩ := hcardA 6 (by norm_num) le_rfl
      exact Sec13.false_of_isExtOf_of_card_lt hK₀s hext h1 (by omega)

theorem isBar211_of_projSL3 {X : Type} [Group X] {n : ℕ} (hn : 0 < n) (hev : Even n)
    (e : X ≃* projSL 3 (GaloisField 2 n)) : IsBar211 X :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
    Or.inl ⟨n, hn, hev, Or.inl ⟨e⟩⟩

theorem isBar211_of_g2 {X : Type} [Group X] {n : ℕ} (hn : 0 < n) (hev : Even n)
    (h : ChevalleyExceptionalModel X .G2 2 n) : IsBar211 X :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
    Or.inl ⟨n, hn, hev, Or.inr <| Or.inr <| Or.inl h⟩

theorem isBar211_of_d4 {X : Type} [Group X] {n : ℕ} (hn : 0 < n) (hev : Even n)
    (h : ChevalleyExceptionalModel X .trialityD4 2 n) : IsBar211 X :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
    Or.inl ⟨n, hn, hev, Or.inr <| Or.inr <| Or.inr <| Or.inl h⟩

theorem exists_act_of_nontrivial {G : Type} [Group G] [Finite G] {A Y : Subgroup G} {c : G}
    (hcA : c ∈ A) (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hZ : Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y) = ⊥)
    (hcnt : c ∉ Sec4.thetaQuotCentralizer Y) :
    ∃ a : G, ∃ ha : a ∈ A, ∃ l : Y,
      (⟨⁅(l : G), a⁆, Item21EarlyProof.commutatorElement_mem (hAY ha) l.2⟩ : Y) ∉
        centerPre (aschbacherSolvableCore 3 Y) := by
  by_contra hcon
  push Not at hcon
  apply hcnt
  have hcN : c ∈ Subgroup.normalizer (Y : Set G) := hAY hcA
  refine ⟨⟨c, hcN⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
  ext z
  induction z using QuotientGroup.induction_on with
  | H l =>
    have h1 := hcon c hcA l
    have h2 : QuotientGroup.mk' (aschbacherSolvableCore 3 Y)
        (⟨⁅(l : G), c⁆, Item21EarlyProof.commutatorElement_mem (hAY hcA) l.2⟩ : Y) = 1 := by
      have : QuotientGroup.mk' (aschbacherSolvableCore 3 Y)
          (⟨⁅(l : G), c⁆, Item21EarlyProof.commutatorElement_mem (hAY hcA) l.2⟩ : Y) ∈
          Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y) := h1
      rwa [hZ, Subgroup.mem_bot] at this
    have h3 : (⟨⁅(l : G), c⁆, Item21EarlyProof.commutatorElement_mem (hAY hcA) l.2⟩ : Y) =
        l * (Y.normalizerMonoidHom ⟨c, hcN⟩ l)⁻¹ := by
      apply Subtype.ext
      show ⁅(l : G), c⁆ = (l : G) * (c * (l : G) * c⁻¹)⁻¹
      rw [commutatorElement_def]
      group
    rw [h3, map_mul, map_inv, mul_inv_eq_one] at h2
    exact congrArg (fun w => (w : Y ⧸ aschbacherSolvableCore 3 Y)) h2.symm

theorem theta_central_of_items (h44 : Sec4.Item4_4)
    (hOrd : KS213Order) (hNine : KS213Nine) (hTwo : KS213TwoRank) {G : Type} [Group G] [Finite G]
    (hG : TheoremFourHyp G) {A : Subgroup G} (hAS : A ∈ partTwoS G) {e : G} (he : e ∈ A)
    (he1 : e ≠ 1) {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt 3 e)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hB : IsBar211 (Y ⧸ aschbacherSolvableCore 3 Y))
    (hZ : Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y) = ⊥)
    (hact : ∃ a : G, ∃ ha : a ∈ A, ∃ l : Y,
      (⟨⁅(l : G), a⁆, Item21EarlyProof.commutatorElement_mem (hAY ha) l.2⟩ : Y) ∉
        centerPre (aschbacherSolvableCore 3 Y)) :
    ∀ t ∈ inSubgroup (aschbacherSolvableCore 3) Y, ∀ y ∈ Y, t * y = y * t := by
  haveI : Group.IsPerfect Y := Sec6.isPerfect_of_mem_thetaComponentsAt hY
  have hq : IsQuasisimple (Y ⧸ aschbacherSolvableCore 3 Y) :=
    Sec6.isQuasisimple_of_mem_thetaComponentsAt hY
  have hYC : Y ≤ Subgroup.centralizer ({e} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hY
  have hY4 : SectionFourHyp Y := by
    have hne : Y ≠ ⊤ := fun h =>
      Sec6.centralizer_ne_top_of_ne_one hG he1 (top_le_iff.mp (h ▸ hYC))
    exact hG.sectionFourHyp hne
  have hO2c := Hering233i.pCore_two_le_center_of_act hAS he he1 hY hAY hact
  have h3Z : ¬ 3 ∣ Nat.card (Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y)) := by
    rw [hZ, Subgroup.card_bot]
    norm_num
  have hquasi : IsQuasisimple Y := isQuasisimple_of_items h44 hOrd hNine hTwo hY4 hq hB hO2c h3Z
  intro t ht y hy
  obtain ⟨t₀, ht₀, rfl⟩ := ht
  have hz := Subgroup.mem_center_iff.mp (Sec4.aschbacherSolvableCore_le_center hquasi ht₀) ⟨y, hy⟩
  exact congrArg Subtype.val hz.symm

end Hering2125

end CFSG.RankThree.PartTwo.Sec21
