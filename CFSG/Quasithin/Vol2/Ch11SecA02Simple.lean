module

public import CFSG.Quasithin.Vol2.Ch11SecA02Card

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedSL)

theorem injective_of_isSimpleGroup {S Y : Type*} [Group S] [Group Y] [IsSimpleGroup S]
    (π : S →* Y) (hπ : Function.Surjective π) (hY : ∃ y : Y, y ≠ 1) : Function.Injective π := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h | h
  · exact (MonoidHom.ker_eq_bot_iff π).mp h
  · exfalso
    obtain ⟨y, hy⟩ := hY
    obtain ⟨s, rfl⟩ := hπ y
    apply hy
    have : s ∈ π.ker := by rw [h]; trivial
    exact this

theorem eq_of_normal_of_isSimpleGroup {Y : Type*} [Group Y] {A B : Subgroup Y} (hAB : A ≤ B)
    [(A.subgroupOf B).Normal] (hB : IsSimpleGroup ↥B) (hA : A ≠ ⊥) : A = B := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (A.subgroupOf B) with h | h
  · exfalso
    apply hA
    rw [eq_bot_iff]
    intro a ha
    have : (⟨a, hAB ha⟩ : ↥B) ∈ A.subgroupOf B := ha
    rw [h, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val this)
  · exact le_antisymm hAB (Subgroup.subgroupOf_eq_top.mp h)

theorem isSimpleGroup_SL_of_center_eq_bot {n : ℕ} {K : Type} [Field K] (hn : 2 ≤ n)
    (h22 : n ≠ 2 ∨ Nat.card K ≠ 2) (h23 : n ≠ 2 ∨ Nat.card K ≠ 3)
    (hZ : Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) = ⊥) :
    IsSimpleGroup (Matrix.SpecialLinearGroup (Fin n) K) := by
  have hs := CFSG.BenderSuzuki.External.huppert_II_6_13 (K := K) n hn h22 h23
  have e : Matrix.ProjectiveSpecialLinearGroup (Fin n) K ≃* Matrix.SpecialLinearGroup (Fin n) K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact e.symm.isSimpleGroup

theorem isSimpleGroup_SL_two {K : Type} [Field K] [Finite K] {m : ℕ} (hK : Nat.card K = 2 ^ m)
    (hm : 2 ≤ m) : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) := by
  have h4 : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have h2 : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  refine isSimpleGroup_SL_of_center_eq_bot le_rfl (Or.inr (by omega)) (Or.inr (by omega)) ?_
  apply Subgroup.card_eq_one.mp
  have h1 := (Subgroup.center
    (Matrix.SpecialLinearGroup (Fin 2) K)).card_eq_card_quotient_mul_card_subgroup
  have h3 : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := card_PSL_two hK
  have hpos : 0 < Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := Nat.card_pos
  have h5 : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) *
      Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) =
      Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) * 1 :=
    calc _ = Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := h1.symm
      _ = _ := by rw [mul_one, h3]
  exact Nat.eq_of_mul_eq_mul_left hpos h5

theorem card_center_SL_zmod_two {n : ℕ} (hn : 0 < n) :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) = 1 := by
  rw [Nat.card_congr
    (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (⟨0, hn⟩ : Fin n)).toEquiv]
  apply le_antisymm
  · calc _ ≤ Nat.card (ZMod 2)ˣ := Subgroup.card_le_card_group _
      _ = 1 := by rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]; rfl
  · exact Nat.card_pos

theorem isSimpleGroup_SL_zmod_two {n : ℕ} (hn : 3 ≤ n) :
    IsSimpleGroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :=
  isSimpleGroup_SL_of_center_eq_bot (by omega) (Or.inl (by omega)) (Or.inl (by omega))
    (Subgroup.card_eq_one.mp (card_center_SL_zmod_two (by omega)))

theorem isSimpleGroup_statedSL {n : ℕ} {K : Type} [Field K]
    (h : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin n) K)) : IsSimpleGroup ↥(StatedSL n K) :=
  (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K).symm.isSimpleGroup

theorem card_SL_five_two :
    Nat.card (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) = 2 ^ 10 * 9765 := by
  rw [OrderReductions.LinearOrders.card_specialLinear (ZMod 2) 5 (by norm_num), Nat.card_zmod]
  decide

theorem exists_two_pow_mul_odd_of_dvd {N E O : ℕ} (hO : Odd O) (hN : N ∣ 2 ^ E * O) :
    ∃ e o : ℕ, e ≤ E ∧ Odd o ∧ N = 2 ^ e * o := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    have := Nat.eq_zero_of_zero_dvd hN
    have hpos : 0 < 2 ^ E * O := Nat.mul_pos (by positivity) hO.pos
    omega
  obtain ⟨e, o, ho, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hN0
  refine ⟨e, o, ?_, ho, rfl⟩
  have h1 : 2 ^ e ∣ 2 ^ E * O := (Dvd.intro o rfl).trans hN
  have hc : Nat.Coprime (2 ^ e) O := Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hO)
  have h2 : 2 ^ e ∣ 2 ^ E := hc.dvd_of_dvd_mul_right h1
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h2

end CFSG.Quasithin.Vol2.Ch11.SecA
