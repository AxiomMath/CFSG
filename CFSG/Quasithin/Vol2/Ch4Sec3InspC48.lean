module

public import CFSG.Quasithin.Vol2.Ch4Sec3K
public import CFSG.Quasithin.Background.F420Orders
public import CFSG.Sporadic.Mathieu.M24
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.LieType.Steinberg.CentralExt.Model

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank

theorem card_psl_two_ne {n N : ℕ} (hn : 2 ≤ n)
    (hN : N = 168 ∨ N = 20160 ∨ N = 360 ∨ N = 2520 ∨ N = 1080 ∨ N = 6048 ∨ N = 9999360 ∨
      N = 244823040) : 2 ^ n * (4 ^ n - 1) ≠ N := by
  intro h
  have hbig : ∀ m, 10 ≤ m → 244823040 < 2 ^ m * (4 ^ m - 1) := by
    intro m hm
    have h1 : 2 ^ 10 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have h2 : 4 ^ 10 ≤ 4 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    calc 244823040 < 2 ^ 10 * (4 ^ 10 - 1) := by norm_num
      _ ≤ 2 ^ m * (4 ^ m - 1) := Nat.mul_le_mul h1 (Nat.sub_le_sub_right h2 1)
  have hle : n < 10 := by
    by_contra hge
    have h1 := hbig n (by omega)
    rw [h] at h1
    rcases hN with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num at h1
  interval_cases n <;> rcases hN with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at h

theorem card_of_l32 {X : Type} [Group X]
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 3 2 1) :
    Nat.card X = 168 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two h

theorem card_statedSL_three_two :
    Nat.card (CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) = 168 :=
  CFSG.Open.StatedAPI.card_statedSL_three_zmod_two

theorem card_of_alt' {X : Type} [Group X] {m : ℕ} (hm : 2 ≤ m)
    (e : X ≃* alternatingGroup (Fin m)) : Nat.card X = m.factorial / 2 := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]

theorem card_modO2_of_surjective {G : Type} [Group G] {L : Subgroup G} {X : Type} [Group X]
    (α : ↥L →* X) (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥L) :
    Nat.card (ModO2 L) = Nat.card X := by
  have e : ModO2 L ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα)
  exact Nat.card_congr e.toEquiv

theorem inspC48L2_holds : InspC48L2 := by
  intro G _ _ H R M L V K n hn hL hcase
  have hcardL : Nat.card (ModO2 L) = 2 ^ n * (4 ^ n - 1) :=
    F420.card_of_statedPSL_two_two (CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel
      (by decide) hL)
  have key : ∀ N : ℕ, Nat.card (ModO2 L) = N →
      (N = 168 ∨ N = 20160 ∨ N = 360 ∨ N = 2520 ∨ N = 1080 ∨ N = 6048 ∨ N = 9999360 ∨
        N = 244823040) → False :=
    fun N hN hN' => card_psl_two_ne hn hN' (hcardL.symm.trans hN)
  have halt6 : IsAltBlockType L 6 → False := by
    rintro ⟨-, α, hα, hker, -⟩
    refine key 360 ?_ (by norm_num)
    rw [card_modO2_of_surjective α hα hker, card_of_alt' (by norm_num)
      (MulEquiv.refl _)]
    decide
  rcases hcase with h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  ·
    obtain ⟨m, hm, hPSL, -⟩ := h2
    rcases hm with rfl | rfl
    · exact key 168 (card_of_l32 hPSL) (by norm_num)
    · exact key 20160 (F420.card_of_l42 hPSL) (by norm_num)
  ·
    exact halt6 h3.2
  ·
    obtain ⟨-, ⟨α, hα, hker⟩, -⟩ := h4.2
    refine key 2520 ?_ (by norm_num)
    rw [card_modO2_of_surjective α hα hker, card_of_alt' (by norm_num)
      (MulEquiv.refl _)]
    decide
  ·
    obtain ⟨-, ⟨-, hc, ⟨e⟩⟩, -⟩ := h5.2
    refine key 1080 ?_ (by norm_num)
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (ModO2 L)), hc,
      Nat.card_congr e.toEquiv, card_of_alt' (by norm_num) (MulEquiv.refl _)]
    decide
  ·
    obtain ⟨-, -, hM | hL5⟩ := h6
    · obtain ⟨⟨e⟩, -⟩ := hM
      refine key 244823040 ?_ (by norm_num)
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.Mathieu.card_M24
    · exact key 9999360 (F420.card_of_l52 hL5.1) (by norm_num)
  ·
    exact key 6048 (F420.card_of_u33 h7.2.2.1) (by norm_num)
  ·
    exact halt6 h8.2
  ·
    obtain ⟨-, α, hα, hker, -⟩ := h9.2.1
    refine key 168 ?_ (by norm_num)
    rw [card_modO2_of_surjective α hα hker, card_statedSL_three_two]

end CFSG.Quasithin.H13.Ch4
