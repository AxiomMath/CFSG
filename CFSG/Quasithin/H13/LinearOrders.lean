module

public import CFSG.Quasithin.H13.FiveMenu
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalLinearFourTwo
import CFSG.Adapters.LieModelSmallOrders

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

theorem card_sl_zmod_two_flag {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) =
      2 ^ (n * (n - 1) / 2) * ∏ j ∈ Finset.Icc 2 n, (2 ^ j - 1) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq hn, Nat.card_zmod]

theorem center_sl_zmod_two {n : ℕ} (hn : 1 ≤ n) :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Subgroup.mem_bot]
  have h01 : ∀ s : ZMod 2, s = 0 ∨ s = 1 := by decide
  have hr1 : r = 1 := by
    rw [Fintype.card_fin] at hr
    rcases h01 r with h | h
    · rw [h, zero_pow (by omega : n ≠ 0)] at hr
      exact absurd hr zero_ne_one
    · exact h
  apply Subtype.ext
  rw [← hA, hr1, map_one, Matrix.SpecialLinearGroup.coe_one]

theorem center_eq_bot_of_mulEquiv_sl {Q : Type*} [Group Q] {n : ℕ} (hn : 1 ≤ n)
    (e : Q ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) : Subgroup.center Q = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have h1 : e z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    have := hz (e.symm g)
    rw [← e.apply_symm_apply g, ← map_mul, ← map_mul, this]
  rw [center_sl_zmod_two hn, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  exact e.injective (h1.trans (map_one e).symm)

theorem card_of_lieModel_psu_three_three {Q : Type} [Group Q] (h : LieModel Q .PSU 3 3 1) :
    Nat.card Q = 6048 :=
  CFSG.Blueprint.LieModel.card_psu_three_three h

theorem nonempty_mulEquiv_alternating_eight_sl_four :
    Nonempty (alternatingGroup (Fin 8) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :=
  nonempty_mulEquiv_sl_two_of_lieModel
    ((CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff
      (alternatingGroup (Fin 8))).2 ⟨MulEquiv.refl _⟩)

theorem isSimpleGroup_sl_four_zmod_two :
    IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_alternating_eight_sl_four
  have : IsSimpleGroup (alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
  exact e.symm.isSimpleGroup

theorem sl_four_zmod_two_nonabelian :
    ∃ a b : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2), a * b ≠ b * a := by
  obtain ⟨e⟩ := nonempty_mulEquiv_alternating_eight_sl_four
  obtain ⟨a, b, hab⟩ := alternatingGroup_nonabelian (n := 8) (by norm_num)
  refine ⟨e a, e b, fun h => hab (e.injective ?_)⟩
  rw [map_mul, map_mul, h]

theorem card_eq_of_surjective_alternating {L : Type*} [Group L] [Finite L]
    (hq : CFSG.IsQuasisimple (L ⧸ CFSG.pCore 2 L))
    (hZ : Subgroup.center (L ⧸ CFSG.pCore 2 L) = ⊥) {m : ℕ} (hm : 5 ≤ m)
    (φ : L →* alternatingGroup (Fin m)) (hφ : Function.Surjective φ) :
    Nat.card (L ⧸ CFSG.pCore 2 L) = Nat.card (alternatingGroup (Fin m)) := by
  have hle := pCore_le_ker_of_surjective_alternating hm φ hφ
  have : IsSimpleGroup (alternatingGroup (Fin m)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; exact hm)
  have hψ : Function.Surjective (QuotientGroup.lift (CFSG.pCore 2 L) φ hle) :=
    QuotientGroup.lift_surjective_of_surjective _ φ hφ hle
  obtain ⟨hker, -⟩ := SteinbergBM.five_quasisimple_centerless_image hq
    (alternatingGroup_nonabelian (by omega)) (QuotientGroup.lift (CFSG.pCore 2 L) φ hle) hψ
  rw [hZ] at hker
  exact Nat.card_congr (Equiv.ofBijective _ ⟨(MonoidHom.ker_eq_bot_iff _).1 hker, hψ⟩)

theorem eq_eight_of_card_alternating {m : ℕ} (hm5 : 5 ≤ m) (hm8 : m ≤ 8)
    (h : Nat.card (alternatingGroup (Fin m)) = 20160) : m = 8 := by
  interval_cases m
  all_goals (try rfl)
  all_goals (rw [nat_card_alternatingGroup] at h; norm_num [Nat.factorial] at h)

theorem card_alternating_ne_five {m : ℕ} (hm5 : 5 ≤ m) (hm8 : m ≤ 8) :
    Nat.card (alternatingGroup (Fin m)) ≠ 9999360 := by
  interval_cases m <;> rw [nat_card_alternatingGroup] <;> norm_num [Nat.factorial]

end CFSG.Quasithin.H13
