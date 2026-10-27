module

public import CFSG.Quasithin.Background.F918Z8Sz1
public import CFSG.Quasithin.Vol2.Ch10SecAShapeCard
public import CFSG.Quasithin.Background.F918Z8Su0

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section Closing

variable {Y : Type} [CommGroup Y] [Finite Y]

@[expose] def SuzConcl (Λ X : Subgroup (MulAut Y)) : Prop :=
  5 ∣ Nat.card ↥X ∨ ∃ m : ℕ, 1 ≤ m ∧
    Nat.card ↥Λ ∣ ∏ i : Fin 4, ((2 ^ m) ^ 4 - (2 ^ m) ^ (i : ℕ)) ∧
    ∀ p : ℕ, p.Prime → p ∣ ((2 ^ m) ^ 3 - 1) * ((2 ^ m) ^ 2 - 1) → p ∣ Nat.card ↥X

structure SuzSec (Λ X A : Subgroup (MulAut Y)) (I J : Subgroup Y) : Prop where
  hJI : J ≤ I
  hXI : X ≤ stabSub I
  hXJ : X ≤ stabSub J
  hAI : A ≤ stabSub I
  hAJ : A ≤ stabSub J
  hyp : B4Hyp (autSec (X ⊔ A) I J) (autSec X I J)
  hq : qhatOf (autSec (X ⊔ A) I J) ≤ ((1 / 2 : ℚ) : WithTop ℚ)
  field : ∀ m : ℕ, BinaryNaturalSL (autSec X I J) ⊤ ⊥ 3 m →
    1 ≤ m ∧ Nat.card ↥Λ ∣ ∏ i : Fin 4, ((2 ^ m) ^ 4 - (2 ^ m) ^ (i : ℕ))

structure SuzData (Γ Λ S : Subgroup (MulAut Y)) (V : Subgroup Y) (A X K : Subgroup (MulAut Y))
    (W : Subgroup Y) : Prop where
  loc : LocCfg Γ Λ S V
  sz : ∃ n, IsSz n ↥Λ
  hA : A ∈ QhatStar Γ
  hAS : A ≤ S
  hAc : ∀ a ∈ A, ∀ x ∈ Λ, a * x = x * a
  hXΓ : X ≤ Γ
  hXc : ∀ x ∈ X, ∀ y ∈ Λ, x * y = y * x
  hAX : A ≤ Subgroup.normalizer (X : Set (MulAut Y))
  hXA : ⁅X, A⁆ = X
  hX1 : X ≠ ⊥
  hKc : IsComponentOf K Γ
  hKns : ¬ IsSuzukiComponent K
  hXK : X = ⨆ a ∈ A, conjAutSub a K
  h3 : 3 ∣ Nat.card ↥X
  hW0 : W ≠ ⊥
  hWΛ : ∀ l ∈ Λ, ∀ w ∈ W, l w ∈ W
  hWA : A ≤ stabSub W
  hWX : X ≤ stabSub W
  hBW : ∀ b ∈ A, (∀ x ∈ X, b * x = x * b) → ∀ w ∈ W, b w = w
  hXnt : ∃ x ∈ X, ∃ w ∈ W, x w ≠ w
  hUA : commSub W A ≠ ⊥
  hAU : IsA2 (autSub Γ W) (autSub A W)
  hA3 : commSeries (autSub A W) 3 = ⊥
  hrAU : rAV (autSub A W) ≤ 2

theorem suzFFClass_of_data
    (H : ∀ (Y : Type) [CommGroup Y] [Finite Y] (Γ Λ S : Subgroup (MulAut Y)) (V : Subgroup Y)
      (A X K : Subgroup (MulAut Y)) (W : Subgroup Y), SuzData Γ Λ S V A X K W → SuzConcl Λ X) :
    SuzFFClass := by
  intro Y _ _ Γ Λ S V h hsz A hA hAS hAc X hXΓ hXc hAX hXA hX1 hcomp h3 W hW0 hWΛ hWA hWX hBW
    hXnt hUA hAU hA3 hrAU
  obtain ⟨K, hKc, hKns, hXK⟩ := hcomp
  exact H Y Γ Λ S V A X K W ⟨h, hsz, hA, hAS, hAc, hXΓ, hXc, hAX, hXA, hX1, hKc, hKns, hXK, h3,
    hW0, hWΛ, hWA, hWX, hBW, hXnt, hUA, hAU, hA3, hrAU⟩

omit [Finite Y] in
theorem card_autSec_dvd {X : Subgroup (MulAut Y)} {I J : Subgroup Y} (hXI : X ≤ stabSub I)
    (hXJ : X ≤ stabSub J) : Nat.card (autSec X I J) ∣ Nat.card ↥X :=
  Dvd.intro _ (card_autSec_mul hXI hXJ)

theorem suz_close (hC1 : AsB42Half) (hexp : ∀ y : Y, y ^ 2 = 1) {Λ X A : Subgroup (MulAut Y)}
    {I J : Subgroup Y} (hs : SuzSec Λ X A I J) : SuzConcl Λ X := by
  have hV2 : ∀ v : Sec I J, v ^ 2 = 1 := by
    intro v
    obtain ⟨⟨w, hw⟩, rfl⟩ := QuotientGroup.mk_surjective v
    show QuotientGroup.mk (⟨w, hw⟩ ^ 2 : ↥I) = 1
    have : (⟨w, hw⟩ ^ 2 : ↥I) = 1 := Subtype.ext (by simpa using hexp w)
    rw [this]
    rfl
  have hdvd : Nat.card (autSec X I J) ∣ Nat.card ↥X := card_autSec_dvd hs.hXI hs.hXJ
  rcases hC1 (Sec I J) hV2 _ _ hs.hyp hs.hq with ⟨n, hnat, -⟩ | h4 | h5
  · obtain ⟨hn1, hΛ⟩ := hs.field n hnat
    right
    refine ⟨n, hn1, hΛ, fun p hp hpd => ?_⟩
    obtain ⟨F, _, _, hFc, ⟨e⟩⟩ := hnat.exists_equiv
    have hcard : Nat.card (autSec X I J) =
        2 ^ (3 * n) * ((2 ^ (3 * n) - 1) * (2 ^ (2 * n) - 1)) := by
      rw [← Nat.card_congr e.toEquiv, Vol2.Ch10.SecA.card_statedSL,
        Vol2.Ch10.SecA.card_SL_three_pow hFc]
    have e3 : (2 ^ n) ^ 3 = 2 ^ (3 * n) := by rw [← pow_mul, mul_comm]
    have e2 : (2 ^ n) ^ 2 = 2 ^ (2 * n) := by rw [← pow_mul, mul_comm]
    have h1 : ((2 ^ n) ^ 3 - 1) * ((2 ^ n) ^ 2 - 1) ∣ Nat.card (autSec X I J) := by
      rw [hcard, e3, e2]
      exact Dvd.intro_left _ rfl
    exact (hpd.trans h1).trans hdvd
  · left
    obtain ⟨F, _, _, hFc, ⟨e⟩⟩ := h4.exists_equiv
    have hF2 : Nat.card F = 2 := by rw [hFc]; norm_num
    have hc : Nat.card (autSec X I J) = 20160 := by
      rw [← Nat.card_congr e.toEquiv, Vol2.Ch10.SecA.card_statedSL,
        Vol2.Ch10.SecA.card_SL_four_of_two hF2]
    rw [hc] at hdvd
    exact (show 5 ∣ 20160 by norm_num).trans hdvd
  · left
    obtain ⟨F, _, _, hFc, ⟨e⟩⟩ := h5.exists_equiv
    have hF2 : Nat.card F = 2 := by rw [hFc]; norm_num
    have hc : Nat.card (autSec X I J) = 9999360 := by
      rw [← Nat.card_congr e.toEquiv, Vol2.Ch10.SecA.card_statedSL,
        Vol2.Ch10.SecA.card_SL_five_of_two hF2]
    rw [hc] at hdvd
    exact (show 5 ∣ 9999360 by norm_num).trans hdvd

end Closing

end CFSG.Quasithin
