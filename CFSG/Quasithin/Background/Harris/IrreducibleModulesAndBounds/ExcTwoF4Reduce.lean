module

public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.ExcThreeD4Generic
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeModel
public import CFSG.RankThree.SteinbergR3ELargeReeOrder
public import CFSG.LieType.Steinberg.CentralExt.GriessReeF4

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_model_field_outer_group_and_inner_involutions)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

section Main


theorem twistedF4_ppd_dvd_card {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ 2 ^ (12 * (2 * a + 1)) - 1)
    (h6 : ¬ p ∣ 2 ^ (6 * (2 * a + 1)) - 1) (h4 : ¬ p ∣ 2 ^ (4 * (2 * a + 1)) - 1) :
    p ∣ Nat.card (F4.reeGamma K a) := by
  obtain ⟨hcard, -⟩ :=
    CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion a K hK
  rw [hcard]
  set q := 2 ^ (2 * a + 1) with hq
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  have hq2 : 2 ≤ q := Nat.le_self_pow (by omega) 2
  have hfac : q ^ 12 - 1 = (q ^ 6 - 1) * ((q ^ 2 + 1) * (q ^ 4 - q ^ 2 + 1)) := by
    have h2 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ (by omega)
    have h12 : 1 ≤ q ^ 12 := Nat.one_le_pow _ _ (by omega)
    zify [h2, h6, h12]
    ring
  have h12 : (2 : ℕ) ^ (12 * (2 * a + 1)) = q ^ 12 := by rw [hq, ← pow_mul, mul_comm]
  have h6' : (2 : ℕ) ^ (6 * (2 * a + 1)) - 1 = q ^ 6 - 1 := by rw [hq, ← pow_mul, mul_comm]
  have h4' : (2 : ℕ) ^ (4 * (2 * a + 1)) - 1 = q ^ 4 - 1 := by rw [hq, ← pow_mul, mul_comm]
  rw [h12, hfac] at hdvd
  rw [h6'] at h6
  rw [h4'] at h4
  have hq2d : q ^ 2 + 1 ∣ q ^ 4 - 1 := by
    have : q ^ 4 - 1 = (q ^ 2 + 1) * (q ^ 2 - 1) := by
      have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
      have h4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
      zify [h2, h4]
      ring
    rw [this]
    exact dvd_mul_right _ _
  have hlast : p ∣ q ^ 4 - q ^ 2 + 1 := by
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
    · exact absurd h h6
    · rcases (Nat.Prime.dvd_mul hp).1 h with h' | h'
      · exact absurd (h'.trans hq2d) h4
      · exact h'
  exact Dvd.dvd.mul_left hlast _

theorem false_of_twistedF4_of_rank {f : ℕ} (hodd : Odd f) (hf3 : 3 ≤ f) {r : ℕ}
    (hlt : 2 * (r + 1) < 12 * f)
    (hrank : ∀ (K : Type) [Field K] [Finite K] [CharP K F4.prime] (a : ℕ), f = 2 * a + 1 →
      Nat.card K = 2 ^ f →
      ∀ B : Subgroup (F4.reeGamma K a),
        (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ r)
    {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    (hX : ReeTitsModel (↥L ⧸ Subgroup.center ↥L) .twistedF4 2 f) : False := by
  have hbig := large_Ree_model_field_outer_group_and_inner_involutions
    (↥L ⧸ Subgroup.center ↥L) 2 f hX
  obtain ⟨-, -, -, -, -, hinn, hdata⟩ := hbig
  have hX' := hX
  obtain ⟨hadm, a, hfa, K, instF, instFin, hK, ⟨e0⟩⟩ := hX
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hCharP : CharP K F4.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK]; rfl)
  obtain ⟨⟨eΓ⟩, -⟩ := hdata a K hfa hK ⟨e0⟩
  have hm1 : 1 ≤ a := by omega
  have hLie : LieModel (↥L ⧸ Subgroup.center ↥L) .twistedF4 0 2 (2 * a + 1) := by
    rw [← hfa]
    exact Or.inr (Or.inr (Or.inl ⟨rfl, by decide, hX'⟩))
  obtain ⟨-, hMsub⟩ := CFSG.LieType.Steinberg.CentralExt.GriessExceptional.reeF4_hopfMultiplier
    hm1 hLie
  have hZL : Subgroup.center ↥L = ⊥ :=
    center_eq_bot_of_hopf_subsingleton' h.L_comp.2.2 (MulEquiv.refl _) hMsub
  have hZX : Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥ := by
    refine center_eq_bot_of_mulEquiv_generic
      ((QuotientGroup.quotientMulEquivOfEq hZL).trans QuotientGroup.quotientBot) hZL
  have hAut := card_le_two_pow_of_inner hZX hinn (rank_transport eΓ (hrank K a hfa hK))
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  obtain ⟨p, hpP, hp2, hord, hdvd, hmin⟩ := exists_ppd_prime (k := 12 * f) (by omega) (by omega)
  haveI : Fact p.Prime := ⟨hpP⟩
  rw [hfa] at hdvd hmin hord
  have hpG : p ∣ Nat.card (F4.reeGamma K a) :=
    twistedF4_ppd_dvd_card hK' hpP hdvd (hmin _ (by omega) (by omega)) (hmin _ (by omega) (by omega))
  have hpS : p ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := by
    rw [Nat.card_congr eΓ.toEquiv]; exact hpG
  exact false_of_center_bot_rank_prime h hZL (MulEquiv.refl _) hAut hp2 hpS
    (by rw [hord]; omega)

end Main

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
