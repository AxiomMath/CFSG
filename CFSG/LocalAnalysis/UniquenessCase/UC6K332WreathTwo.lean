module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieTwistFrame
import CFSG.RankThree.PartTwo.Sec4.RonanK432Sylow
import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route.Wreath

open CFSG.RankThree.PartTwo.Sec4.RonanK432
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure (TwistFrame)

variable {C S : Type} [CommGroup C] [Group S]

theorem zpow_coord_two (x : Fin 2 → C) (m : ℤ) (i : Fin 2) : (x ^ m) i = x i ^ m := rfl

theorem not_weaklyClosed_of_torus_two [Finite C] [Finite S] {a : ℕ} (hC : Nat.card C = 3 ^ a)
    {φ : (Fin 2 → C) →* S} (hφ : Function.Injective φ) {μ : ℤ} (hμ : ¬ (3 : ℤ) ∣ μ - 1)
    (htw : ∃ g : S, ∀ c, g * φ c * g⁻¹ = φ (Function.update c 0 (c 0 ^ μ)))
    (hsw : ∃ w : S, ∀ c, w * φ c * w⁻¹ = φ (c ∘ Equiv.swap 0 1))
    (hS : ¬ 3 ^ (2 * a + 1) ∣ Nat.card S) {z : S} (hz : orderOf z = 3) :
    ¬ WeaklyClosed (Subgroup.zpowers z) := by
  have hQcard : Nat.card φ.range = 3 ^ (2 * a) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv, Nat.card_fun, hC,
      Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul, mul_comm]
  refine not_weaklyClosed_of_sylow_witness (2 * a) φ.range hQcard hS ?_ hz
  rintro _ ⟨y, rfl⟩ hq3
  have hy3 : y ^ 3 = 1 := by
    have h := pow_orderOf_eq_one (φ y)
    rw [hq3] at h
    exact hφ (by rw [map_pow, map_one]; exact h)
  have hy3' : ∀ i, y i ^ 3 = 1 := fun i => by simpa using congr_fun hy3 i
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at hq3
    omega
  by_cases hboth : y 0 ≠ 1 ∧ y 1 ≠ 1
  · obtain ⟨g, hg⟩ := htw
    obtain ⟨y', hy'⟩ : ∃ y' : Fin 2 → C, y' = Function.update y 0 (y 0 ^ μ) := ⟨_, rfl⟩
    have hconj : g * φ y * g⁻¹ = φ y' := by rw [hy']; exact hg y
    have hy'0 : y' 0 = y 0 ^ μ := by rw [hy']; simp
    have hy'1 : y' 1 = y 1 := by rw [hy']; exact Function.update_of_ne (by decide) _ _
    refine ⟨g, ?_, ?_⟩
    · rw [hconj, ← map_mul, ← map_mul, mul_comm]
    · rw [hconj]
      intro hmem
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hsame : y ^ m = y' := hφ (by rw [map_zpow]; exact hm)
      have h0 : y 0 ^ m = y 0 ^ μ := by
        have := congr_fun hsame 0
        rwa [zpow_coord_two, hy'0] at this
      have h1 : y 1 ^ m = y 1 := by
        have := congr_fun hsame 1
        rwa [zpow_coord_two, hy'1] at this
      have ho0 : orderOf (y 0) = 3 := orderOf_eq_prime (hy3' 0) hboth.1
      have ho1 : orderOf (y 1) = 3 := orderOf_eq_prime (hy3' 1) hboth.2
      have d0 : ((3 : ℕ) : ℤ) ∣ m - μ := by
        rw [← ho0]
        exact orderOf_dvd_iff_zpow_eq_one.mpr (by rw [zpow_sub, h0, mul_inv_cancel])
      have d1 : ((3 : ℕ) : ℤ) ∣ m - 1 := by
        rw [← ho1]
        exact orderOf_dvd_iff_zpow_eq_one.mpr (by rw [zpow_sub_one, h1, mul_inv_cancel])
      apply hμ
      omega
  · obtain ⟨w, hw⟩ := hsw
    have hconj : w * φ y * w⁻¹ = φ (y ∘ Equiv.swap 0 1) := hw y
    refine ⟨w, ?_, ?_⟩
    · rw [hconj, ← map_mul, ← map_mul, mul_comm]
    · rw [hconj]
      intro hmem
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hsame : y ^ m = y ∘ Equiv.swap 0 1 := hφ (by rw [map_zpow]; exact hm)
      have h0 := congr_fun hsame 0
      have h1 := congr_fun hsame 1
      rw [zpow_coord_two] at h0 h1
      simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right] at h0 h1
      by_cases hy0 : y 0 = 1
      · rw [hy0, one_zpow] at h0
        apply hy1
        funext i
        fin_cases i
        · simpa using hy0
        · simpa using h0.symm
      · have hy1' : y 1 = 1 := by
          by_contra h
          exact hboth ⟨hy0, h⟩
        rw [hy1', one_zpow] at h1
        exact hy0 h1.symm

theorem listRow_of_torus_two [Finite C] [Finite S] {a : ℕ} (hC : Nat.card C = 3 ^ a)
    {φ : (Fin 2 → C) →* S} (hφ : Function.Injective φ) {μ : ℤ} (hμ : ¬ (3 : ℤ) ∣ μ - 1)
    (htw : ∃ g : S, ∀ c, g * φ c * g⁻¹ = φ (Function.update c 0 (c 0 ^ μ)))
    (hsw : ∃ w : S, ∀ c, w * φ c * w⁻¹ = φ (c ∘ Equiv.swap 0 1))
    (hS : ¬ 3 ^ (2 * a + 1) ∣ Nat.card S) : ListRow S :=
  listRow_of_forall_not_weaklyClosed fun _ hz =>
    not_weaklyClosed_of_torus_two hC hφ hμ htw hsw hS hz

theorem listRow_of_twistFrame_two [Finite S] {a : ℕ} {μ : ℤ} (hμ : ¬ (3 : ℤ) ∣ μ - 1)
    (F : TwistFrame (Multiplicative (ZMod (3 ^ a))) 2 S μ)
    (hS : ¬ 3 ^ (2 * a + 1) ∣ Nat.card S) : ListRow S := by
  haveI : NeZero (3 ^ a) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hC : Nat.card (Multiplicative (ZMod (3 ^ a))) = 3 ^ a := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  exact listRow_of_torus_two hC F.T_injective hμ (F.exists_twist 0) (F.exists_swap 0 1) hS

end CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route.Wreath
