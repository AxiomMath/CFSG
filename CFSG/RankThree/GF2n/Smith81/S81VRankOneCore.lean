module

public import CFSG.RankThree.GF2n.Smith81.S81VRankOneCount
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open Module

namespace RankOneData

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  {D : RankOneData K V}

private theorem rankOne_bitSum_empty {f : ℕ} : bitSum (∅ : Finset (Fin f)) = 0 := by
  simp [bitSum]

private theorem rankOne_bitSum_singleton {f : ℕ} (r : Fin f) :
    bitSum ({r} : Finset (Fin f)) = 2 ^ (r : ℕ) := by
  simp [bitSum]

private theorem rankOne_pow_eq_of_mod {F : Type} [Field F] [Fintype F] {c : F} (hc : c ≠ 0)
    {m n : ℕ} (h : m % (Fintype.card F - 1) = n % (Fintype.card F - 1)) : c ^ m = c ^ n := by
  have hq : c ^ (Fintype.card F - 1) = 1 := FiniteField.pow_card_sub_one_eq_one c hc
  have key : ∀ l : ℕ, c ^ l = c ^ (l % (Fintype.card F - 1)) := by
    intro l
    have hl : (Fintype.card F - 1) * (l / (Fintype.card F - 1)) + l % (Fintype.card F - 1) = l :=
      Nat.div_add_mod l _
    calc c ^ l = c ^ ((Fintype.card F - 1) * (l / (Fintype.card F - 1)) + l % (Fintype.card F - 1)) := by
          rw [hl]
      _ = c ^ (l % (Fintype.card F - 1)) := by
          rw [pow_add, pow_mul, hq, one_pow, one_mul]
  rw [key m, key n, h]

theorem Exp.exists {f : ℕ} (hf : Fintype.card K = 2 ^ f) : Nonempty (D.Exp f) := by
  have hx0 : (D.X 0 : V →ₗ[K] V) = 1 :=
    congrArg (fun φ : V ≃ₗ[K] V => (φ : V →ₗ[K] V)) D.X_zero
  have hx : ∀ s t : K, (D.X (s + t) : V →ₗ[K] V) = (D.X s : V →ₗ[K] V) * (D.X t : V →ₗ[K] V) :=
    fun s t => by rw [D.X_add, LinearEquiv.coe_toLinearMap_mul]
  obtain ⟨E, hE, hE0, hprod, hspan⟩ :=
    exists_rootExpansion hf (fun t => (D.X t : V →ₗ[K] V)) hx0 hx
  exact ⟨⟨hf, E, hE, hE0, hprod, hspan⟩⟩

theorem rankOne_core [FiniteDimensional K V] {f : ℕ} (hf : Fintype.card K = 2 ^ f) (hf2 : 2 ≤ f)
    {v₀ : V} {k : ℕ} (h : D.Setup v₀ k) {β : V →ₗ[K] V →ₗ[K] K} (hβalt : ∀ v, β v v = 0)
    (hβρ : ∀ n u w, β (D.ρ n u) (D.ρ n w) = β u w)
    (hβa : ∀ g u w, β (D.a g u) (D.a g w) = β u w)
    (hV1 : finrank K (D.V1 β) ≤ finrank K D.N + 1) :
    ∃ (i : ℕ) (lam : K), lam ≠ 0 ∧
      (∀ t : K, D.X t (D.s v₀) = D.s v₀ + (lam * t ^ (2 ^ i)) • v₀) ∧
      ∀ c : Kˣ, D.a (D.d c) v₀ = (c : K) ^ (2 ^ i) • v₀ := by
  obtain ⟨X⟩ := Exp.exists (D := D) hf
  obtain ⟨B', hne, hB', hv', hv'0, hmod⟩ := Exp.monomial_structure hf2 X h
  have hcard : B'.card ≤ 1 := Exp.card_le_one hf2 X h hβalt hβρ hβa hV1 hB' hv' hv'0
  have hcard1 : B'.card = 1 := by
    have := Finset.card_pos.2 hne
    omega
  obtain ⟨r, hr⟩ := Finset.card_eq_one.1 hcard1
  subst hr
  have hexp : ∀ t : K, D.X t (D.s v₀) = ∑ B : Finset (Fin f), t ^ bitSum B • X.E B (D.s v₀) := by
    intro t
    have h1 : (D.X t : V →ₗ[K] V) (D.s v₀) = ∑ B : Finset (Fin f), t ^ bitSum B • X.E B (D.s v₀) := by
      rw [X.hE t, LinearMap.sum_apply]
      simp only [LinearMap.smul_apply]
    exact h1
  have hsum : ∀ t : K,
      D.X t (D.s v₀) = D.s v₀ + t ^ bitSum ({r} : Finset (Fin f)) • X.E {r} (D.s v₀) := by
    intro t
    have hterm : ∀ c : Finset (Fin f), c ≠ ∅ → c ≠ {r} → t ^ bitSum c • X.E c (D.s v₀) = 0 := by
      intro c hc0 hc1
      have hnot : ¬ c ⊆ {r} := fun hsub => by
        rcases Finset.subset_singleton_iff.1 hsub with h' | h'
        · exact hc0 h'
        · exact hc1 h'
      have hz : X.E c (D.s v₀) = 0 := by
        by_contra hne'
        exact hnot ((hB' c).1 hne')
      rw [hz, smul_zero]
    have h0 : t ^ bitSum (∅ : Finset (Fin f)) • X.E ∅ (D.s v₀) = D.s v₀ := by
      rw [X.hE0, Module.End.one_apply, rankOne_bitSum_empty, pow_zero, one_smul]
    have hsum' : ∑ B : Finset (Fin f), t ^ bitSum B • X.E B (D.s v₀) =
        t ^ bitSum (∅ : Finset (Fin f)) • X.E ∅ (D.s v₀) +
          t ^ bitSum ({r} : Finset (Fin f)) • X.E {r} (D.s v₀) :=
      Finset.sum_eq_add _ _ (Finset.empty_ne_singleton r) (fun c _ hc => hterm c hc.1 hc.2)
        (fun h' => absurd (Finset.mem_univ _) h') (fun h' => absurd (Finset.mem_univ _) h')
    rw [hexp t, hsum', h0]
  obtain ⟨c0, hc0⟩ : ∃ c0 : K, c0 • v₀ = X.E {r} (D.s v₀) := by
    have hv : (⟨v₀, h.mem⟩ : D.fix) ≠ 0 := fun h' => h.ne0 (congrArg Subtype.val h')
    obtain ⟨c0, hc0⟩ := (finrank_eq_one_iff_of_nonzero' _ hv).1 h.fix1 ⟨_, hv'⟩
    exact ⟨c0, congrArg Subtype.val hc0⟩
  have hc0ne : c0 ≠ 0 := by
    rintro rfl
    apply hv'0
    rw [← hc0, zero_smul]
  rw [rankOne_bitSum_singleton r] at hmod
  refine ⟨(r : ℕ), c0, hc0ne, fun t => ?_, fun c => ?_⟩
  · rw [hsum t, rankOne_bitSum_singleton r, ← hc0, smul_smul, mul_comm (t ^ 2 ^ (r : ℕ)) c0]
  · rw [h.char c, rankOne_pow_eq_of_mod c.ne_zero hmod]

theorem rankOne_normalized [FiniteDimensional K V] {f : ℕ} (hf : Fintype.card K = 2 ^ f) (hf2 : 2 ≤ f)
    {v₀ : V} {k : ℕ} (h : D.Setup v₀ k) {β : V →ₗ[K] V →ₗ[K] K} (hβalt : ∀ v, β v v = 0)
    (hβρ : ∀ n u w, β (D.ρ n u) (D.ρ n w) = β u w)
    (hβa : ∀ g u w, β (D.a g u) (D.a g w) = β u w)
    (hV1 : finrank K (D.V1 β) ≤ finrank K D.N + 1)
    (hbraid : D.s = D.X 1 * (D.s * D.X 1 * D.s) * D.X 1) :
    ∃ i : ℕ, (∀ t : K, D.X t (D.s v₀) = D.s v₀ + (t ^ (2 ^ i)) • v₀) ∧
      (∀ t : K, (D.s * D.X t * D.s) v₀ = v₀ + (t ^ (2 ^ i)) • D.s v₀) ∧
      ∀ c : Kˣ, D.a (D.d c) v₀ = (c : K) ^ (2 ^ i) • v₀ := by
  obtain ⟨i, lam, -, hx, hc⟩ := rankOne_core hf hf2 h hβalt hβρ hβa hV1
  have hss : ∀ x : V, D.s (D.s x) = x := fun x => congrArg (fun φ : V ≃ₗ[K] V => φ x) D.s_sq
  have hX1v : D.X 1 v₀ = v₀ := by
    rw [D.X_def]
    exact D.mem_fix.1 h.mem _
  have hX1s : D.X 1 (D.s v₀) = D.s v₀ + lam • v₀ := by
    rw [hx 1, one_pow, mul_one]
  have hA : ∀ t : K, (D.s * D.X t * D.s) v₀ = v₀ + (lam * t ^ (2 ^ i)) • D.s v₀ := by
    intro t
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hx t, map_add, map_smul, hss]
  have hbr : D.s v₀ = D.X 1 ((D.s * D.X 1 * D.s) (D.X 1 v₀)) :=
    congrArg (fun φ : V ≃ₗ[K] V => φ v₀) hbraid
  have hA1 : (D.s * D.X 1 * D.s) v₀ = v₀ + lam • D.s v₀ := by
    rw [hA 1, one_pow, mul_one]
  rw [hX1v, hA1, map_add, map_smul, hX1v, hX1s] at hbr
  have hkey : (1 - lam) • D.s v₀ = (1 + lam * lam) • v₀ := by
    linear_combination (norm := module) hbr
  have hlam1 : lam = 1 := by
    by_contra hne
    have h1lam : (1 - lam) ≠ 0 := fun h0 => hne (sub_eq_zero.1 h0).symm
    apply h.sv
    have hsv : D.s v₀ = (1 - lam)⁻¹ • ((1 + lam * lam) • v₀) := by
      rw [← hkey, smul_smul, inv_mul_cancel₀ h1lam, one_smul]
    rw [hsv]
    exact D.fix.smul_mem _ (D.fix.smul_mem _ h.mem)
  subst hlam1
  refine ⟨i, fun t => ?_, fun t => ?_, hc⟩
  · rw [hx t, one_mul]
  · rw [hA t, one_mul]

end RankOneData

end CFSG.RankThree.GF2n.Smith81.S81V
