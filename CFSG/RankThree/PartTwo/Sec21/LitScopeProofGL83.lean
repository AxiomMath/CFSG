module

public import CFSG.RankThree.PartTwo.KFacts.AS76InvolutionsCentralizeThree
import CFSG.RankThree.PartTwo.KFacts.KS21TwoCentralMain
public import CFSG.RankThree.PartTwo.Sec21.Item231

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Open (GLBStronglyEmbedded)
open CFSG.Assembly (IsElemAbelian)

@[expose] def GL83StronglyEmbeddedNoSimpleThree : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsKGroup X → ∀ M : Subgroup X,
    GLBStronglyEmbedded 3 M → 2 ≤ CFSG.Open.pRank 3 M →
      ∀ H : Subgroup X, H ≤ M → IsSimpleGroup H →
        Nat.card H = 3 ∨ Nat.Coprime 3 (Nat.card H)

theorem rank3II_23_4_of_gl83Simple (h231 : Item231) (h233 : Item233)
    (hGL : GL83StronglyEmbeddedNoSimpleThree) : Item234 := by
  intro G _ _ A E U c L hpair
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hG := hpair.standing
  have hconc := h231 G A E U c L hpair
  have hT : KFacts.KS21.IsTerminalGroup (iGroup A) := by
    rcases hconc with ⟨he, -⟩ | ⟨he, -⟩ | ⟨he, -⟩
    · exact Or.inl he
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr he)
  have hSE := h233 G A E U c L hpair
  have hIN : iGroup A ≤ nGroup A := iGroup_le_nGroup A
  obtain ⟨T⟩ : Nonempty (Sylow 2 (nGroup A)) := inferInstance
  obtain ⟨z', hz'2, hzT, hTc, hrank, H, hHC, hHs, hH3, hH3'⟩ :=
    KFacts.KS21.terminalTwoCentralInvolution G (iGroup A) (nGroup A) hIN le_rfl hT T
  have hz2 : orderOf (z' : G) = 2 := (Subgroup.orderOf_coe z').trans hz'2
  have hmapC : (Subgroup.centralizer ({z'} : Set (iGroup A))).map (iGroup A).subtype ≤
      Subgroup.centralizer ({(z' : G)} : Set G) ⊓ nGroup A := by
    rintro _ ⟨y, hy, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨?_, hIN y.2⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val hy
  have hrankG : 2 ≤ CFSG.Open.pRank 3
      (Subgroup.centralizer ({(z' : G)} : Set G) ⊓ nGroup A : Subgroup G) :=
    hrank.trans ((CFSG.RankThreeEvenClassification.Helpers.pRank_le_map_of_injective 3
      Nat.prime_three _ (iGroup A).subtype_injective _).trans
      (CFSG.RankThreeEvenClassification.Helpers.pRank_mono 3 Nat.prime_three hmapC))
  refine ⟨(z' : G), hIN z'.2, hz2, ⟨T, hzT, hTc⟩, ?_, ?_⟩
  ·
    by_contra hCN
    set C := Subgroup.centralizer ({(z' : G)} : Set G)
    have h3 : 3 ∣ Nat.card (C ⊓ nGroup A : Subgroup G) :=
      (dvd_pow_self 3 (by omega)).trans
        (CFSG.RankThreeEvenClassification.Helpers.prime_power_pRank_dvd_card 3 Nat.prime_three _)
    have hSE' := glbStronglyEmbedded_subgroupOf_inf hSE hCN h3
    have hz1 : (z' : G) ≠ 1 := by
      intro h1
      have h1' : z' = 1 := Subtype.ext h1
      rw [h1', orderOf_one] at hz'2
      omega
    have hCtop : C ≠ ⊤ := by
      intro hC
      apply hz1
      have hcen : (z' : G) ∈ Subgroup.center G := by
        rw [Subgroup.mem_center_iff]
        intro g
        have hg : g ∈ C := hC ▸ Subgroup.mem_top g
        exact Subgroup.mem_centralizer_singleton_iff.mp hg
      have := hG.isSimpleGroup
      rwa [center_eq_bot_of_simple hG.nonabelian, Subgroup.mem_bot] at hcen
    have hK : CFSG.IsKGroup C := (hG.toTheoremFourHyp.sectionFourHyp hCtop).kGroup
    have hrank' : 2 ≤ CFSG.Open.pRank 3 ((C ⊓ nGroup A).subgroupOf C) :=
      hrankG.trans (pRank_le_pRank_subgroupOf Nat.prime_three inf_le_left)
    have hHmap : H.map (iGroup A).subtype ≤ C ⊓ nGroup A :=
      (Subgroup.map_mono hHC).trans hmapC
    set H' : Subgroup C := (H.map (iGroup A).subtype).subgroupOf C
    have hH'le : H' ≤ (C ⊓ nGroup A).subgroupOf C := fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hHmap (Subgroup.mem_subgroupOf.mp hx))
    have eH : H' ≃* H := (Subgroup.subgroupOfEquivOfLe (hHmap.trans inf_le_left)).trans
      (H.equivMapOfInjective _ (iGroup A).subtype_injective).symm
    have hcard : Nat.card H' = Nat.card H := Nat.card_congr eH.toEquiv
    have hH's : IsSimpleGroup H' := by
      have := hHs
      exact MulEquiv.isSimpleGroup eH
    rcases hGL C hK _ hSE' hrank' H' hH'le hH's with h | h
    · exact hH3' (hcard ▸ h)
    · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp h (hcard ▸ hH3)
  ·
    intro x hxN hx2
    obtain ⟨y0, hy0⟩ : ∃ y : iGroup A, orderOf y = 3 := by
      obtain ⟨E', hE'C, hE'e, hE'c⟩ := CFSG.RankThreeEvenClassification.Helpers.pRank_attained 3
        Nat.prime_three (Subgroup.centralizer ({z'} : Set (iGroup A)))
      have hE'1 : E' ≠ ⊥ := by
        intro hb
        rw [hb, Subgroup.card_bot] at hE'c
        have : 3 ^ 2 ≤ 3 ^ CFSG.Open.pRank 3 (Subgroup.centralizer ({z'} : Set (iGroup A))) :=
          Nat.pow_le_pow_right (by norm_num) hrank
        omega
      obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE'1
      exact ⟨(y : iGroup A), orderOf_eq_prime (hE'e.2 y y.2) (fun h => hy1 (Subtype.ext h))⟩
    have hxn : x ∈ Subgroup.normalizer ((iGroup A : Subgroup G) : Set G) := hxN
    let φ : MulAut (iGroup A) := ((MulAut.conj x).subgroupMap (iGroup A)).trans
      (MulEquiv.subgroupCongr (map_conj_eq_of_mem_normalizer hxn))
    have hφ : ∀ y : iGroup A, ((φ y : iGroup A) : G) = x * y * x⁻¹ := fun y => rfl
    have hφ2 : φ ^ 2 = 1 := by
      ext y
      rw [pow_two, MulAut.mul_apply, hφ, hφ, MulAut.one_apply]
      calc x * (x * (y : G) * x⁻¹) * x⁻¹ = (x * x) * (y : G) * (x * x)⁻¹ := by group
        _ = (y : G) := by rw [← pow_two, orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq hx2),
            one_mul, inv_one, mul_one]
    obtain ⟨y, hy3, hyφ⟩ : ∃ y : iGroup A, orderOf y = 3 ∧ φ y = y := by
      by_cases hφ1 : φ = 1
      · exact ⟨y0, hy0, by rw [hφ1, MulAut.one_apply]⟩
      · exact as76InvolutionsCentralizeThree (iGroup A) hT φ (orderOf_eq_prime hφ2 hφ1)
    have hyx : (y : G) ∈ nGroup A ⊓ Subgroup.centralizer {x} := by
      refine Subgroup.mem_inf.mpr ⟨hIN y.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : x * (y : G) * x⁻¹ = y := by rw [← hφ, hyφ]
      calc (y : G) * x = x * (y : G) * x⁻¹ * x := by rw [h1]
        _ = x * (y : G) := by group
    exact pRank_pos_of_orderOf_eq_three (by rw [Subgroup.orderOf_coe]; exact hy3) hyx

end CFSG.RankThree.PartTwo.Sec21
