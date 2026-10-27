module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerLastChoice
public import CFSG.LocalAnalysis.StandardType.GGSixStepThreeCFSeventeenTable
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCore
import CFSG.Timmesfeld.Orders.ClassicalLinear
import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section CQ

variable {G : Type*} [Group G]

@[expose] noncomputable def ggCQ (S : Subgroup G) : ℕ :=
  Nat.card (↥S ⧸ Subgroup.center ↥S)

theorem ggCQ_eq_of_mulEquiv {P : Type*} [Group P] {S : Subgroup G} (e : ↥S ≃* P) :
    ggCQ S = Nat.card (P ⧸ Subgroup.center P) :=
  Nat.card_congr (QuotientGroup.congr (Subgroup.center ↥S) (Subgroup.center P) e
    (Subgroup.map_center_eq e)).toEquiv

theorem ggCQ_congr {H : Type*} [Group H] {S : Subgroup G} {T : Subgroup H} (e : ↥S ≃* ↥T) :
    ggCQ S = ggCQ T :=
  ggCQ_eq_of_mulEquiv e

theorem ggCQ_map_of_injective {H : Type*} [Group H] (f : G →* H) (hf : Function.Injective f)
    (S : Subgroup G) : ggCQ (S.map f) = ggCQ S :=
  (ggCQ_congr (S.equivMapOfInjective f hf)).symm

theorem ggCQ_comap_of_injective {H : Type*} [Group H] (f : G →* H) (hf : Function.Injective f)
    {T : Subgroup H} (hT : T ≤ f.range) : ggCQ (T.comap f) = ggCQ T := by
  rw [← ggCQ_map_of_injective f hf, Subgroup.map_comap_eq_self hT]

theorem ggCQ_map_of_perfect {H : Type*} [Group H] (ψ : G →* H)
    (hker : ψ.ker ≤ Subgroup.center G) {S : Subgroup G} (hS : Group.IsPerfect S) :
    ggCQ (S.map ψ) = ggCQ S := by
  obtain ⟨e⟩ := ggCenterQuotEquiv_of_surjective hS (ψ.subgroupMap S)
    (ψ.subgroupMap_surjective S) (fun x hx => by
      have h1 : ψ (x : G) = 1 := congrArg Subtype.val hx
      have hxZ := hker h1
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_center_iff.mp hxZ g))
  exact (Nat.card_congr e.toEquiv).symm

theorem card_eq_ggCQ_mul (S : Subgroup G) :
    Nat.card S = ggCQ S * Nat.card (Subgroup.center ↥S) :=
  (Subgroup.center ↥S).card_eq_card_quotient_mul_card_subgroup

theorem odd_card_center_of {S : Subgroup G} [Finite S]
    (hz : ∀ z ∈ S, (∀ y ∈ S, z * y = y * z) → z ^ 2 = 1 → z = 1) :
    Odd (Nat.card (Subgroup.center ↥S)) := by
  refine LayerFacts.odd_card_of_forall_sq_eq_one fun x hx => ?_
  have h := hz ((x : S) : G) (x : S).2 (fun y hy => by
    have := Subgroup.mem_center_iff.mp x.2 ⟨y, hy⟩
    exact (congrArg Subtype.val this).symm) (by
    have := congrArg (fun w : Subgroup.center ↥S => ((w : S) : G)) hx
    simpa using this)
  exact Subtype.ext (Subtype.ext h)

theorem ggCQ_eq_card_of_center_eq_bot {S : Subgroup G} (h : Subgroup.center ↥S = ⊥) :
    ggCQ S = Nat.card S := by
  rw [card_eq_ggCQ_mul S, h, Subgroup.card_bot, mul_one]

end CQ

section Orders

@[expose] def GGNotExcThreeOrder (n : ℕ) : Prop :=
  n ≠ 174182400 ∧ n ≠ 25920 ∧ n ≠ 360

theorem ggNotExcThreeOrder_iff (n : ℕ) :
    GGNotExcThreeOrder n ↔ ∀ N₀, (N₀ = 174182400 ∨ N₀ = 25920 ∨ N₀ = 360) → n ≠ N₀ := by
  constructor
  · rintro ⟨h1, h2, h3⟩ N₀ (rfl | rfl | rfl) <;> assumption
  · intro h
    exact ⟨h _ (Or.inl rfl), h _ (Or.inr (Or.inl rfl)), h _ (Or.inr (Or.inr rfl))⟩

theorem ggNotExcThreeOrder_of_card {G : Type*} [Group G] {S : Subgroup G} [Finite S]
    (hz : ∀ z ∈ S, (∀ y ∈ S, z * y = y * z) → z ^ 2 = 1 → z = 1)
    (h : ∀ N₀ z : ℕ, (N₀ = 174182400 ∨ N₀ = 25920 ∨ N₀ = 360) → Odd z → Nat.card S ≠ N₀ * z) :
    GGNotExcThreeOrder (ggCQ S) := by
  refine (ggNotExcThreeOrder_iff _).mpr fun N₀ hN₀ heq =>
    h N₀ _ hN₀ (odd_card_center_of hz) ?_
  rw [card_eq_ggCQ_mul S, heq]

theorem ggAKFG_not_excThree {G : Type} [Group G] {C : Subgroup G}
    (h : GGNotExcThreeOrder (ggCQ C)) :
    ¬ LieModel (↥C ⧸ Subgroup.center ↥C) .POmegaPlus 4 2 1 ∧
      ¬ LieModel (↥C ⧸ Subgroup.center ↥C) .PSU 4 2 1 ∧
        IsEmpty ((↥C ⧸ Subgroup.center ↥C) ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨fun hD => h1 (ggAKFT_card_of_dFourTwo hD), fun hU => h2 (ggAKFL_card_of_uFourTwo hU),
    ⟨fun e => h3 ((Nat.card_congr e.toEquiv).trans ggAKFL_card_alternatingGroup_six)⟩⟩

end Orders

section Arith

theorem ggAKFG_le_of_two_pow_dvd {k e n : ℕ} (hn : Odd n) (h : 2 ^ k ∣ 2 ^ e * n) : k ≤ e :=
  (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp
    ((Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hn)).dvd_of_dvd_mul_right h)

theorem ggAKFG_le_of_dvd {k N₀ z : ℕ} (hz : Odd z) (h : 2 ^ k ∣ N₀ * z) :
    (N₀ = 174182400 → k ≤ 12) ∧ (N₀ = 25920 → k ≤ 6) ∧ (N₀ = 360 → k ≤ 3) := by
  have h' : 2 ^ k ∣ N₀ :=
    (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hz)).dvd_of_dvd_mul_right h
  refine ⟨fun hN => ?_, fun hN => ?_, fun hN => ?_⟩ <;> subst hN
  · exact ggAKFG_le_of_two_pow_dvd (n := 42525) ⟨21262, by norm_num⟩ (h'.trans (by norm_num))
  · exact ggAKFG_le_of_two_pow_dvd (n := 405) ⟨202, by norm_num⟩ (h'.trans (by norm_num))
  · exact ggAKFG_le_of_two_pow_dvd (n := 45) ⟨22, by norm_num⟩ (h'.trans (by norm_num))

theorem ggAKFG_ordSL_good {d a : ℕ} (hd : 2 ≤ d) (ha : 1 ≤ a) :
    GGNotExcThreeOrder ((2 ^ a) ^ (d * (d - 1) / 2) * (∏ j ∈ Finset.Icc 2 d, ((2 ^ a) ^ j - 1)) /
      Nat.gcd d (2 ^ a - 1)) :=
  ⟨ggAKFL_ordSL_ne_dFourTwo hd ha, ggAKFL_ordSL_ne_uFourTwo hd ha, ggAKFL_ordSL_ne_altSix hd ha⟩

theorem ggCQ_range_toGL {D : Type} [Field D] [Finite D] {m : ℕ} (hm : 1 ≤ m) :
    ggCQ (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin m) D →* GL (Fin m) D).range =
      Nat.card D ^ (m * (m - 1) / 2) * (∏ j ∈ Finset.Icc 2 m, (Nat.card D ^ j - 1)) /
        Nat.gcd m (Nat.card D - 1) := by
  rw [ggCQ_eq_of_mulEquiv
    (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).symm]
  exact (Nat.card_congr (projectiveSpecialLinearGroupEquivStatedProj m D).toEquiv).trans
    (CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL hm)

theorem ggAKFG_ordSU_ne {a d N₀ z : ℕ} (ha : 2 ≤ a) (hd : 2 ≤ d)
    (hN₀ : N₀ = 174182400 ∨ N₀ = 25920 ∨ N₀ = 360) (hz : Odd z) :
    ((2 ^ a : ℕ) : ℤ) ^ (d * (d - 1) / 2) *
        ∏ i ∈ Finset.Icc 2 d, (((2 ^ a : ℕ) : ℤ) ^ i - (-1) ^ i) ≠ ((N₀ * z : ℕ) : ℤ) := by
  intro h
  have h2 : 2 ^ (a * (d * (d - 1) / 2)) ∣ N₀ * z := by
    have h3 : ((2 ^ (a * (d * (d - 1) / 2)) : ℕ) : ℤ) ∣ ((N₀ * z : ℕ) : ℤ) := by
      rw [← h]
      push_cast
      rw [pow_mul]
      exact dvd_mul_right _ _
    exact Int.natCast_dvd_natCast.mp h3
  have h5 : ((N₀ : ℕ) : ℤ) ∣ ((2 ^ a : ℕ) : ℤ) ^ (d * (d - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 d, (((2 ^ a : ℕ) : ℤ) ^ i - (-1) ^ i) := by
    rw [h, Nat.cast_mul]
    exact dvd_mul_right _ _
  obtain ⟨hb1, hb2, hb3⟩ := ggAKFG_le_of_dvd hz h2
  have hd4 : d ≤ 4 := by
    by_contra h5'
    have h10 := ggAKFL_choose_two_le (s := 10) (by omega : 5 ≤ d) (by norm_num)
    have := Nat.mul_le_mul ha h10
    rcases hN₀ with rfl | rfl | rfl
    · have := hb1 rfl; omega
    · have := hb2 rfl; omega
    · have := hb3 rfl; omega
  clear h h2
  rcases hN₀ with rfl | rfl | rfl
  · have hb := hb1 rfl
    interval_cases d
    · have : a ≤ 12 := by norm_num at hb; omega
      interval_cases a <;> revert h5 <;> decide +kernel
    · have : a ≤ 4 := by norm_num at hb; omega
      interval_cases a <;> revert h5 <;> decide +kernel
    · have : a ≤ 2 := by norm_num at hb; omega
      interval_cases a
      revert h5
      decide +kernel
  · have hb := hb2 rfl
    interval_cases d
    · have : a ≤ 6 := by norm_num at hb; omega
      interval_cases a <;> revert h5 <;> decide +kernel
    · have : a ≤ 2 := by norm_num at hb; omega
      interval_cases a
      revert h5
      decide +kernel
    · norm_num at hb; omega
  · have hb := hb3 rfl
    interval_cases d
    · have : a ≤ 3 := by norm_num at hb; omega
      interval_cases a <;> revert h5 <;> decide +kernel
    · norm_num at hb; omega
    · norm_num at hb; omega

theorem ggAKFG_ordSp_ne {a s N₀ z : ℕ} (ha : 2 ≤ a) (hs : 1 ≤ s)
    (hN₀ : N₀ = 174182400 ∨ N₀ = 25920 ∨ N₀ = 360) (hz : Odd z) :
    (2 ^ a) ^ (s ^ 2) * ∏ j ∈ Finset.Icc 1 s, ((2 ^ a) ^ (2 * j) - 1) ≠ N₀ * z := by
  intro h
  have h2 : 2 ^ (a * s ^ 2) ∣ N₀ * z := by
    rw [← h, pow_mul]
    exact dvd_mul_right _ _
  have h5 : N₀ ∣ (2 ^ a) ^ (s ^ 2) * ∏ j ∈ Finset.Icc 1 s, ((2 ^ a) ^ (2 * j) - 1) := by
    rw [h]
    exact dvd_mul_right _ _
  obtain ⟨hb1, hb2, hb3⟩ := ggAKFG_le_of_dvd hz h2
  have hs2 : s ≤ 2 := by
    by_contra h3
    have h9 : 9 ≤ s ^ 2 := by nlinarith
    have := Nat.mul_le_mul ha h9
    rcases hN₀ with rfl | rfl | rfl
    · have := hb1 rfl; omega
    · have := hb2 rfl; omega
    · have := hb3 rfl; omega
  clear h h2
  rcases hN₀ with rfl | rfl | rfl
  · have hb := hb1 rfl
    interval_cases s
    · have : a ≤ 12 := by norm_num at hb; omega
      interval_cases a <;> revert h5 <;> decide +kernel
    · have : a ≤ 3 := by norm_num at hb; omega
      interval_cases a <;> revert h5 <;> decide +kernel
  · have hb := hb2 rfl
    interval_cases s
    · have : a ≤ 6 := by norm_num at hb; omega
      interval_cases a <;> revert h5 <;> decide +kernel
    · norm_num at hb; omega
  · have hb := hb3 rfl
    interval_cases s
    · have : a ≤ 3 := by norm_num at hb; omega
      interval_cases a <;> revert h5 <;> decide +kernel
    · norm_num at hb; omega

end Arith

namespace LayerExcThree

theorem exists_card_eq_two_pow (D : Type) [Field D] [Finite D] [CharP D 2] :
    ∃ a : ℕ, 1 ≤ a ∧ Nat.card D = 2 ^ a := by
  have : Fintype D := Fintype.ofFinite D
  obtain ⟨k, -, hk⟩ := FiniteField.card D 2
  exact ⟨k, k.pos, by rw [Nat.card_eq_fintype_card, hk]⟩

theorem ggNotExcThree_of_mulEquiv_SL {G : Type*} [Group G] {S : Subgroup G} {D : Type}
    [Field D] [Finite D] [CharP D 2] {m : ℕ} (hm : 2 ≤ m)
    (e : ↥S ≃* Matrix.SpecialLinearGroup (Fin m) D) : GGNotExcThreeOrder (ggCQ S) := by
  obtain ⟨a, ha1, ha⟩ := exists_card_eq_two_pow D
  rw [ggCQ_eq_of_mulEquiv e,
    Nat.card_congr (projectiveSpecialLinearGroupEquivStatedProj m D).toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by omega), ha]
  exact ggAKFG_ordSL_good hm ha1

end LayerExcThree

end CFSG.StandardType
