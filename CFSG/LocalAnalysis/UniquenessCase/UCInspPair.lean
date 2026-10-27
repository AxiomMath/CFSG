module

public import CFSG.Open.LocalVocabulary
public import CFSG.LocalAnalysis.UniquenessCase.UCInspBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Insp

open CFSG.Open Subgroup
open scoped commutatorElement

@[expose] def InspPair (ℓ : ℕ) {G : Type*} [Group G] (D R : Subgroup G) : Prop :=
  IsPGroup ℓ R ∧ IsMulCommutative ↥R ∧ R ≠ ⊥ ∧ D ≤ normalizer (R : Set G) ∧ ⁅D, R⁆ = R

section Pair

variable {G H : Type*} [Group G] [Group H] {ℓ : ℕ}

theorem InspPair.map (e : G ≃* H) {D R : Subgroup G} (h : InspPair ℓ D R) :
    InspPair ℓ (D.map e.toMonoidHom) (R.map e.toMonoidHom) := by
  obtain ⟨hp, hc, hb, hn, hk⟩ := h
  refine ⟨hp.of_equiv (e.subgroupMap R), inferInstance, ?_, ?_, ?_⟩
  · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective (H := R) e.injective]
  · calc D.map e.toMonoidHom ≤ (normalizer (R : Set G)).map e.toMonoidHom :=
          Subgroup.map_mono hn
      _ = normalizer ((R.map e.toMonoidHom : Subgroup H) : Set H) :=
          Subgroup.map_equiv_normalizer_eq R e
  · rw [← Subgroup.map_commutator, hk]

theorem card_zpowers_three {b : G} (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) :
    Nat.card (Subgroup.zpowers b) = 3 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime hb3 hb1

theorem inspPair_of_triple [Finite G] {b z : G} {ℓ k : ℕ} (hℓ : ℓ.Prime) (hb3 : b ^ 3 = 1)
    (hz : z ^ ℓ = 1) (hz1 : z ≠ 1) (hk : b * z * b⁻¹ = z ^ k) (hk1 : ¬ ℓ ∣ k - 1) :
    InspPair ℓ (Subgroup.zpowers b) (Subgroup.zpowers z) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hord : orderOf z = ℓ := orderOf_eq_prime hz hz1
  have hcard : Nat.card (Subgroup.zpowers z) = ℓ ^ 1 := by
    rw [Nat.card_zpowers, hord, pow_one]
  have hk0 : k ≠ 0 := fun h0 => hk1 (by rw [h0]; exact dvd_zero _)
  have hmap : ∀ w ∈ Subgroup.zpowers z, b * w * b⁻¹ ∈ Subgroup.zpowers z := by
    intro w hw
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    rw [← conj_zpow, hk, ← zpow_natCast, ← zpow_mul]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) _
  have hb2 : ∀ w : G, b ^ 2 * (b * w * b⁻¹) * (b ^ 2)⁻¹ = w := by
    intro w
    have h1 : b ^ 2 * b = 1 := by rw [← pow_succ, hb3]
    have h2 : b⁻¹ * (b ^ 2)⁻¹ = 1 := by rw [← mul_inv_rev, h1, inv_one]
    calc b ^ 2 * (b * w * b⁻¹) * (b ^ 2)⁻¹ = (b ^ 2 * b) * w * (b⁻¹ * (b ^ 2)⁻¹) := by group
      _ = w := by rw [h1, h2, one_mul, mul_one]
  have hnorm : b ∈ normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
    refine mem_normalizer_iff.2 fun h => ⟨hmap h, fun hh => ?_⟩
    have h1 := hmap _ hh
    have h2 := hmap _ h1
    rw [← hb2 h]
    have e : b ^ 2 * (b * h * b⁻¹) * (b ^ 2)⁻¹ = b * (b * (b * h * b⁻¹) * b⁻¹) * b⁻¹ := by
      simp only [pow_two, mul_inv_rev, mul_assoc]
    rw [e]
    exact h2
  have hD : Subgroup.zpowers b ≤ normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) :=
    (Subgroup.zpowers_le).2 hnorm
  refine ⟨IsPGroup.of_card hcard, inferInstance, ?_, hD, le_antisymm ?_ ?_⟩
  · intro h
    exact hz1 (by simpa using (Subgroup.zpowers_eq_bot.1 h))
  · rw [Subgroup.commutator_le]
    intro g hg s hs
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ ((mem_normalizer_iff.1 (hD hg) s).1 hs) (Subgroup.inv_mem _ hs)
  · have hcomm : ⁅b, z⁆ = z ^ (k - 1) := by
      rw [commutatorElement_def, hk]
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      simp [pow_succ]
    have hmem : z ^ (k - 1) ∈ ⁅Subgroup.zpowers b, Subgroup.zpowers z⁆ :=
      hcomm ▸ Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers b) (Subgroup.mem_zpowers z)
    have hcop : Nat.Coprime ℓ (k - 1) := (Nat.Prime.coprime_iff_not_dvd hℓ).2 hk1
    have hk1' : k - 1 ≠ 0 := fun h0 => hk1 (by rw [h0]; exact dvd_zero _)
    have hcard' : Nat.card (Subgroup.zpowers (z ^ (k - 1))) = Nat.card (Subgroup.zpowers z) := by
      rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_pow' _ hk1', hord, hcop.gcd_eq_one,
        Nat.div_one]
    have hle : Subgroup.zpowers (z ^ (k - 1)) ≤ Subgroup.zpowers z :=
      (Subgroup.zpowers_le).2 (Subgroup.pow_mem _ (Subgroup.mem_zpowers z) _)
    have heq : Subgroup.zpowers (z ^ (k - 1)) = Subgroup.zpowers z :=
      Subgroup.eq_of_le_of_card_ge hle hcard'.ge
    exact heq.symm.le.trans ((Subgroup.zpowers_le).2 hmem)

end Pair

end CFSG.LocalAnalysis.UniquenessCase.UCK.Insp
