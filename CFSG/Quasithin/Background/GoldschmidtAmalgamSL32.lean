module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamSModelL32Facts
public import CFSG.Quasithin.Background.GoldschmidtAmalgamSTwoLocal

public section

set_option synthInstance.maxSize 2000

namespace CFSG.Quasithin.F6.GoldAmS

open Matrix CFSG.Open

theorem center_SL3 : Subgroup.center SL3 = ⊥ := by
  let e12 : SL3 := ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩
  let e21 : SL3 := ⟨!![1, 0, 0; 1, 1, 0; 0, 0, 1], by decide⟩
  let e13 : SL3 := ⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], by decide⟩
  let e31 : SL3 := ⟨!![1, 0, 0; 0, 1, 0; 1, 0, 1], by decide⟩
  let e23 : SL3 := ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide⟩
  let e32 : SL3 := ⟨!![1, 0, 0; 0, 1, 0; 0, 1, 1], by decide⟩
  have key : ∀ g : SL3, g * e12 = e12 * g → g * e21 = e21 * g → g * e13 = e13 * g →
      g * e31 = e31 * g → g * e23 = e23 * g → g * e32 = e32 * g → g = 1 := by
    decide +kernel
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_center_iff] at hg
  exact Subgroup.mem_bot.2 (key g (hg e12).symm (hg e21).symm (hg e13).symm (hg e31).symm
    (hg e23).symm (hg e32).symm)

noncomputable def projEquivSL3 : SL3 ≃* ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) :=
  MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center SL3))
    ⟨by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', center_SL3],
     QuotientGroup.mk'_surjective _⟩

theorem isL32_SL3 : IsL32 SL3 := by
  refine ⟨⟨Nat.prime_two, le_rfl, by norm_num, by simp, by simp⟩, ZMod 2, inferInstance,
    inferInstance, by simp [ZMod.card], ⟨projEquivSL3.trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 (ZMod 2))⟩⟩

theorem index_K1 : K1.index = 7 := by
  have h := Subgroup.index_mul_card K1
  rw [card_K1, card_SL3] at h
  omega

theorem index_K2 : K2.index = 7 := by
  have h := Subgroup.index_mul_card K2
  rw [card_K2, card_SL3] at h
  omega

theorem exists_sylow_K12 : ∃ S : Sylow 2 SL3, (S : Subgroup SL3) = K1 ⊓ K2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 ↥(K1 ⊓ K2) := IsPGroup.of_card (n := 3) (by rw [card_K12]; norm_num)
  have hidx : ¬ 2 ∣ (K1 ⊓ K2).index := by
    have h := Subgroup.index_mul_card (K1 ⊓ K2)
    rw [card_K12, card_SL3] at h
    omega
  exact ⟨hP.toSylow hidx, rfl⟩

theorem isP_Q1 : IsPGroup 2 Q1 := IsPGroup.of_card (n := 2) (by rw [card_Q1]; norm_num)

theorem isP_Q2 : IsPGroup 2 Q2 := IsPGroup.of_card (n := 2) (by rw [card_Q2]; norm_num)

theorem Q1_ne_bot : Q1 ≠ ⊥ := by
  intro h
  have := card_Q1
  rw [h, Subgroup.card_bot] at this
  omega

theorem Q2_ne_bot : Q2 ≠ ⊥ := by
  intro h
  have := card_Q2
  rw [h, Subgroup.card_bot] at this
  omega

theorem K1_le_normalizer : K1 ≤ Subgroup.normalizer (Q1 : Set SL3) := fun g hg =>
  Subgroup.mem_normalizer_fintype fun n hn => K1_normalizes_Q1 g hg n hn

theorem K2_le_normalizer : K2 ≤ Subgroup.normalizer (Q2 : Set SL3) := fun g hg =>
  Subgroup.mem_normalizer_fintype fun n hn => K2_normalizes_Q2 g hg n hn

theorem K1_ne_K2 : K1 ≠ K2 := by
  intro h
  have h1 : ∃ g : SL3, g ∈ K1 ∧ g ∉ K2 := by decide +kernel
  obtain ⟨g, hg1, hg2⟩ := h1
  exact hg2 (h ▸ hg1)

theorem isTwoLocalAmalgam_K1_K2 : IsTwoLocalAmalgam K1 K2 := by
  obtain ⟨S, hS⟩ := exists_sylow_K12
  have hS' : ∀ x ∈ (S : Subgroup SL3), x ≠ 1 → ∃ g : SL3, g * x * g⁻¹ ∉ (S : Subgroup SL3) := by
    rw [hS]
    exact T_moved
  exact ⟨isMaxTwoLocal_of_isCoatom S hS' K1 Q1 (isCoatom_of_prime_index K1 (by
      rw [index_K1]; norm_num)) Q1_ne_bot isP_Q1 K1_le_normalizer,
    isMaxTwoLocal_of_isCoatom S hS' K2 Q2 (isCoatom_of_prime_index K2 (by
      rw [index_K2]; norm_num)) Q2_ne_bot isP_Q2 K2_le_normalizer, K1_ne_K2, S, hS⟩

theorem exists_model_L32 : ∃ (W : Type) (_ : Group W) (_ : Finite W) (K₁ K₂ : Subgroup W),
    IsL32 W ∧ IsTwoLocalAmalgam K₁ K₂ ∧ TypeA K₁ K₂ :=
  ⟨SL3, inferInstance, inferInstance, K1, K2, isL32_SL3, isTwoLocalAmalgam_K1_K2, typeA_K1_K2⟩

end CFSG.Quasithin.F6.GoldAmS
