module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Head

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

@[expose] def IsConjB (M B F : Subgroup G) : Prop := ∃ m ∈ M, F = conjSubgroup m B

@[expose] def GoodPt (M Q B Y F : Subgroup G) : Prop :=
  ∃ g ∈ M, conjSubgroup g Y = Y ∧ conjSubgroup g (LB M Q B) = LB M Q F

@[expose] def GoodAll (M Q B Y : Subgroup G) : Prop :=
  ∀ m ∈ M, GoodPt M Q B Y (conjSubgroup m B)

theorem isConjB_self (M B : Subgroup G) : IsConjB M B B :=
  ⟨1, M.one_mem, (conjSubgroup_one B).symm⟩

theorem goodPt_self (M Q B Y : Subgroup G) : GoodPt M Q B Y B :=
  ⟨1, M.one_mem, conjSubgroup_one Y, conjSubgroup_one (LB M Q B)⟩

@[expose] def Sec4Concl (M Q Z B X Y : Subgroup G) : Prop :=
  (∀ y, y ∈ LB M Q B ⊓ Y ↔ y ∈ Y ∧ ∀ b ∈ B, ⁅y, b⁆ ∈ Z) ∧
    Q.relIndex (LB M Q B ⊓ Y) = Nat.card Z ∧
    LB M Q B = (LB M Q B ⊓ X) ⊔ (LB M Q B ⊓ Y)

@[expose] def OneConcl (hc : Ctx M Q Z B) (X Y : Subgroup G) : Prop :=
  ∀ e ∈ LB M Q B ⊓ X, e ∉ Q →
    (LB M Q B ⊓ X) ⊔ Y ≤ Rt M (LB M Q B) e ∧
    (∀ r ∈ Rt M (LB M Q B) e, conjSubgroup r Y = Y) ∧
    (Rt M (LB M Q B) e = (LB M Q B ⊓ X) ⊔ Y ∨ OmegaPlusNat hc e 2) ∧
    ∀ Y' : Subgroup G, Q ≤ Y' → Y' ≤ Rt M (LB M Q B) e →
      (∀ r ∈ Rt M (LB M Q B) e, conjSubgroup r Y' = Y') →
      QuotSat Y' Q (IsSLModel 2 (Nat.card Z)) → Y' = Y

@[expose] def TwoConcl (M Q B X : Subgroup G) : Prop :=
  StronglyClosedMod M (LB M Q B ⊓ X) (LB M Q B)

@[expose] def ThreeConcl (M Q B X : Subgroup G) : Prop :=
  ∀ g ∈ M, (∀ f ∈ conjSubgroup g (LB M Q B ⊓ X), ∀ e ∈ LB M Q B ⊓ X,
      ⁅f, e⁆ ∈ conjSubgroup g (LB M Q B ⊓ X) ⊓ (LB M Q B ⊓ X)) →
    conjSubgroup g (LB M Q B ⊓ X) = LB M Q B ⊓ X

@[expose] def FourConcl (M Q B Y : Subgroup G) : Prop :=
  ∀ S F : Subgroup G, IsConjB M B S → IsConjB M B F → GoodPt M Q B Y S → F ≤ QB S →
    GoodPt M Q B Y F

@[expose] def FiveConcl (M Q Z B Y : Subgroup G) : Prop :=
  ∃ U₁ : Subgroup G, Z ≤ U₁ ∧ B ≤ U₁ ∧ U₁ ≤ Q ∧
    (∀ u ∈ U₁, ∃ m ∈ M, ∃ b ∈ B, u * (m * b * m⁻¹)⁻¹ ∈ Z) ∧
    (∀ m ∈ M, ∀ u ∈ U₁, u ∉ Z → u ∈ (conjSubgroup m B ⊔ Z : Subgroup G) →
      GoodPt M Q B Y (conjSubgroup m B)) ∧
    (∀ m ∈ M, ∀ u ∈ U₁, u ∉ Z → u ∈ (conjSubgroup m B ⊔ Z : Subgroup G) →
      conjSubgroup m B ≤ U₁) ∧
    Nat.card Z ^ 4 ≤ Nat.card U₁

@[expose] def SixConcl (M Q B Y : Subgroup G) : Prop :=
  ∀ S F : Subgroup G, IsConjB M B S → IsConjB M B F → GoodPt M Q B Y S →
    (∀ f ∈ F, ∀ s ∈ S, ⁅f, s⁆ = 1) → GoodPt M Q B Y F

end HS9

@[expose] def Sec4Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ X Y : Subgroup G, HS9.Split95 M Q Z B t X Y → HS9.Sec4Concl M Q Z B X Y

@[expose] def Sec97OneStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ X Y : Subgroup G, HS9.Split95 M Q Z B t X Y → HS9.Sec4Concl M Q Z B X Y →
      HS9.OneConcl hc X Y

@[expose] def Sec97TwoStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ X Y : Subgroup G, HS9.Split95 M Q Z B t X Y → HS9.Sec4Concl M Q Z B X Y →
      HS9.OneConcl hc X Y → HS9.TwoConcl M Q B X

@[expose] def Sec97ThreeStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ X Y : Subgroup G, HS9.Split95 M Q Z B t X Y → HS9.Sec4Concl M Q Z B X Y →
      HS9.OneConcl hc X Y → HS9.TwoConcl M Q B X → HS9.ThreeConcl M Q B X

@[expose] def Sec97FourStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ X Y : Subgroup G, HS9.Split95 M Q Z B t X Y → HS9.Sec4Concl M Q Z B X Y →
      HS9.OneConcl hc X Y → HS9.TwoConcl M Q B X → HS9.ThreeConcl M Q B X → HS9.FourConcl M Q B Y

@[expose] def Sec97FiveStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ X Y : Subgroup G, HS9.Split95 M Q Z B t X Y → HS9.Sec4Concl M Q Z B X Y →
      HS9.OneConcl hc X Y →
    ∀ r : G, Sec7A hc t r → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ s ∈ Z0, ∀ nn : G, ConjMod M Q s nn → nn ∈ LB M Q (conjSubgroup r B) ⊓ hc.CN t →
      nn ∉ Z0 → HS9.FiveConcl M Q Z B Y

@[expose] def Sec97ConnStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ P : Subgroup G → Prop, P B →
      (∀ S F : Subgroup G, HS9.IsConjB M B S → HS9.IsConjB M B F → P S →
        (∀ f ∈ F, ∀ s ∈ S, ⁅f, s⁆ = 1) → P F) →
      ∀ F : Subgroup G, HS9.IsConjB M B F → P F

@[expose] def Sec98EndStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ X Y : Subgroup G, HS9.Split95 M Q Z B t X Y → HS9.Sec4Concl M Q Z B X Y →
      HS9.GoodAll M Q B Y → ∀ y ∈ LB M Q B ⊓ Y, y ∉ Q → hc.CN y ≤ Y

namespace HS9

theorem exists_mem_LB_inf_Y_not_mem (hc : Ctx M Q Z B) {X Y : Subgroup G}
    (h4 : Sec4Concl M Q Z B X Y) : ∃ y ∈ LB M Q B ⊓ Y, y ∉ Q := by
  by_contra hno
  push Not at hno
  have hle : LB M Q B ⊓ Y ≤ Q := fun y hy => hno y hy
  have h1 : Q.relIndex (LB M Q B ⊓ Y) = 1 := Subgroup.relIndex_eq_one.mpr hle
  rw [h4.2.1] at h1
  have := hc.hyp.q4
  omega

theorem card_CN_le_of_le_Y (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) {y : G} (hyL : y ∈ LB M Q B) (hyQ : y ∉ Q)
    (hCN : hc.CN y ≤ Y) : Nat.card ↥(hc.CN y) ≤ Nat.card Q * Nat.card Z := by
  have hs5 := hs.toSec5
  have hsy : Sec5Hyp hc n y := ⟨hs5.width, hs5.n_gt, hs5.noA2, hs5.gen, hyL, hyQ⟩
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hq2 : ∃ s : ℕ, Nat.card Z = 2 ^ s := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact ⟨e, he⟩
  have hqev : 2 ∣ Nat.card Z := by
    obtain ⟨s, hs'⟩ := hq2
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hs'
      omega
    rw [hs']
    exact dvd_pow_self 2 hs0
  have hqpos : 0 < Nat.card Z := Nat.card_pos
  obtain ⟨⟨hQX, hXR, hQY, hYR, hXY, hXYQ, hcomm⟩, hYsl, -⟩ := hsplit
  obtain ⟨hYQnorm, hYmod⟩ := hYsl
  obtain ⟨hYcard, -⟩ := HS9.isSLModel_two_data hq4 hq2 hYmod
  have hQY_idx : Q.relIndex Y = Nat.card Z * (Nat.card Z ^ 2 - 1) := hYcard
  have hN2 : IsPGroup 2 ↥(hc.CN y) := by
    by_cases hR : Rt M (LB M Q B) y = LB M Q B
    · have hle : hc.CN y ≤ LB M Q B := fun x hx => hR ▸ (Ctx.mem_CN.mp hx).1
      exact (hc.isPGroup_LB h34 hs5.width hs5.n_gt hs5.noA2 hs5.gen).of_injective
        (Subgroup.inclusion hle) (Subgroup.inclusion_injective _)
    · exact hc.isPGroup_CN_of_311 h34 hsy
        (h311a G M Q Z B hc n hs5.width hs5.n_gt hs5.noA2 hs5.gen y hyL hyQ hR)
  have hQC : Q ≤ hc.CN y := hc.Q_le_CN hyL
  have hCM : hc.CN y ≤ M := fun x hx => Rt_le_M hc.LB_le_M y (Ctx.mem_CN.mp hx).1
  have hQn : hc.CN y ≤ Subgroup.normalizer (Q : Set G) := hCM.trans hc.hyp.Q_normal.2
  obtain ⟨k, hk⟩ := HS9.relIndex_two_pow_of_isPGroup Q hN2
  have hdvd := HS9.relIndex_dvd_of_normalizes (A := hc.CN y) (B := Q) (C := Y) hCN hQY hQn
  rw [hk, hQY_idx] at hdvd
  have hle := HS9.le_of_two_pow_dvd_mul_sq_sub_one hqev hqpos hdvd
  have h1 := Subgroup.relIndex_mul_card (H := Q) (K := hc.CN y)
  rw [inf_eq_left.mpr hQC, hk] at h1
  rw [← h1, mul_comm (Nat.card ↥Q) (Nat.card ↥Z)]
  exact Nat.mul_le_mul_right _ hle

end HS9

end CFSG.RankThree.GF2n.Stroth80
