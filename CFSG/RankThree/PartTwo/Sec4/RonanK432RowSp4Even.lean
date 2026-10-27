module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSp4
public import CFSG.RankThree.PartTwo.Sec4.RonanK432OuterTools

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSp)
open CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.GH74.GLS.IVK (fixedField fixedField_card_pow)

theorem evenSp4_center_eq_bot (F : Type) [Field F] [CharP F 2] :
    Subgroup.center (StatedProj (StatedSp 2 F)) = ⊥ := by
  have e : StatedSp 2 F ≃* StatedProj (StatedSp 2 F) :=
    MulEquiv.ofBijective (proj 2 F)
      ⟨KFacts.proj_injective_of_charTwo, proj_surjective (r := 2) (K := F)⟩
  rw [← Subgroup.map_center_eq e,
    CFSG.Timmesfeld.Transvection.center_statedSp_eq_bot (n := 2) (K := F) (by norm_num),
    Subgroup.map_bot]

theorem evenSp4_card_range_spIncl (F : Type) [Field F] [CharP F 2] (τ : F ≃+* F) :
    Nat.card (((proj 2 F).comp (KFacts.spIncl τ)).range) =
      Nat.card (StatedSp 2 (fixedField τ)) := by
  rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective (KFacts.proj_spIncl_injective τ),
    Subgroup.card_top]

theorem evenSp4_three_not_dvd_card (F : Type) [Field F] [Finite F] [CharP F 2] :
    ¬ 3 ∣ Nat.card F := by
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨m, -, hm⟩ := FiniteField.card F 2
  rw [Nat.card_eq_fintype_card, hm]
  intro h
  have h2 := Nat.prime_three.dvd_of_dvd_pow h
  norm_num at h2

theorem evenSp4_three_mul_dvd_aux (b : ℕ) (hb : 1 ≤ b) (h3 : 3 ∣ b ^ 2 + b + 1) :
    3 * (b ^ 2 * ((b - 1) * (b ^ 2 - 1))) ∣ b ^ 6 * ((b ^ 3 - 1) * (b ^ 6 - 1)) := by
  have h2 : 1 ≤ b ^ 2 := Nat.one_le_pow _ _ hb
  have h3' : 1 ≤ b ^ 3 := Nat.one_le_pow _ _ hb
  have h6 : 1 ≤ b ^ 6 := Nat.one_le_pow _ _ hb
  have key : b ^ 6 * ((b ^ 3 - 1) * (b ^ 6 - 1)) =
      b ^ 2 * ((b - 1) * (b ^ 2 - 1)) * (b ^ 4 * (b ^ 2 + b + 1) * (b ^ 4 + b ^ 2 + 1)) := by
    zify [hb, h2, h3', h6]
    ring
  have hd : 3 ∣ b ^ 4 * (b ^ 2 + b + 1) * (b ^ 4 + b ^ 2 + 1) :=
    Dvd.dvd.mul_right (Dvd.dvd.mul_left h3 _) _
  rw [key, mul_comm 3]
  exact mul_dvd_mul_left _ hd

theorem evenSp4_three_mul_dvd (a : ℕ) (ha : ¬ 3 ∣ a) :
    3 * (a ^ 4 * ((a ^ 2 - 1) * (a ^ 4 - 1))) ∣
      (a ^ 3) ^ 4 * (((a ^ 3) ^ 2 - 1) * ((a ^ 3) ^ 4 - 1)) := by
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · exact absurd (h ▸ dvd_zero 3) ha
    · exact h
  have hmod : a ^ 2 % 3 = 1 := by
    have : a % 3 = 1 ∨ a % 3 = 2 := by omega
    rcases this with h | h <;> simp [Nat.pow_mod, h]
  have h3 : 3 ∣ (a ^ 2) ^ 2 + a ^ 2 + 1 := by
    apply Nat.dvd_of_mod_eq_zero
    simp [Nat.add_mod, Nat.pow_mod, hmod]
  have hb : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ ha1
  have e4 : a ^ 4 = (a ^ 2) ^ 2 := by ring
  have e6 : (a ^ 3) ^ 2 = (a ^ 2) ^ 3 := by ring
  have e12 : (a ^ 3) ^ 4 = (a ^ 2) ^ 6 := by ring
  rw [e4, e6, e12]
  exact evenSp4_three_mul_dvd_aux (a ^ 2) hb h3

theorem evenSp4_outerRow_statedProj (F : Type) [Field F] [Finite F] [CharP F 2] :
    OuterRow (StatedProj (StatedSp 2 F)) := by
  refine outerRow_of_fixed_card_dvd (evenSp4_center_eq_bot F) fun α hα hout => ?_
  have hD : α ∉ (conjAut 2 F).range := by
    rintro ⟨A, rfl⟩
    exact hout (KFacts.conjAut_mem_inner_of_charTwo A)
  obtain ⟨τ, hτ3, H0, hαH⟩ := KFacts.sp4_even_order_three_field_descent α hα hD
  have hF : Nat.card F = Nat.card (fixedField τ) ^ 3 := by
    have h := fixedField_card_pow τ
    rw [hτ3] at h
    exact h.symm
  have hdiv : ¬ 3 ∣ Nat.card (fixedField τ) := fun h => by
    apply evenSp4_three_not_dvd_card F
    rw [hF]
    exact dvd_pow h (by norm_num)
  refine ⟨((proj 2 F).comp (KFacts.spIncl τ)).range.map (conjAut 2 F H0).toMonoidHom,
    Nat.card (StatedSp 2 (fixedField τ)), ?_, ?_, ?_⟩
  · intro x
    rw [Subgroup.mem_map_equiv, KFacts.mem_range_proj_spIncl_iff, hαH]
    simp only [MulAut.mul_apply, MulAut.inv_apply]
    constructor
    · intro h
      rw [h, MulEquiv.apply_symm_apply]
    · intro h
      have h' := congrArg (conjAut 2 F H0).symm h
      rwa [MulEquiv.symm_apply_apply] at h'
  · have hinj : Function.Injective (conjAut 2 F H0).toMonoidHom :=
      fun a b h => (conjAut 2 F H0).injective h
    refine dvd_of_eq ?_
    rw [Subgroup.card_map_of_injective hinj, evenSp4_card_range_spIncl F τ]
  · have hPcard : Nat.card (StatedProj (StatedSp 2 F)) = Nat.card (StatedSp 2 F) :=
      Nat.card_congr (Equiv.ofBijective (proj 2 F)
        ⟨KFacts.proj_injective_of_charTwo, proj_surjective (r := 2) (K := F)⟩).symm
    rw [hPcard, card_statedSp_two F, card_statedSp_two (fixedField τ), hF]
    exact evenSp4_three_mul_dvd _ hdiv

theorem evenSp4_outerRow_projSp (F : Type) [Field F] [Finite F] [CharP F 2] :
    OuterRow (projSp 2 F) :=
  OuterRow.of_mulEquiv (CFSG.PGLModel.projSpEquivStatedProj 2 F).symm
    (evenSp4_outerRow_statedProj F)

theorem rowOf_seven_Sp4 : ∀ n : ℕ, 1 ≤ n → RowOf (projSp 2 (GaloisField 2 n)) := by
  intro n hn S _ _ _ _ ⟨e⟩
  haveI : NeZero n := ⟨by omega⟩
  haveI : Finite (projSp 2 (GaloisField 2 n)) := Finite.of_equiv S e.toEquiv
  exact GoodRow.of_mulEquiv e.symm
    ⟨listRow_projSp_two (three_ne_zero_galoisField_two n),
      evenSp4_outerRow_projSp (GaloisField 2 n)⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
