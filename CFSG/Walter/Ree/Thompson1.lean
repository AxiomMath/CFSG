module

public import CFSG.Walter.Ree.Thompson1.Label
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import CFSG.Walter.Ree.Thompson1.Normalize

public section

namespace CFSG.Walter.Ree

open Thompson1

theorem generates_of_fixed {K : Type*} [Field K] [Fintype K] [CharP K 3] (σ : K ≃+* K)
    (hfix : ∀ x : K, σ x = x → x = 0 ∨ x = 1 ∨ x = -1) : ∀ τ : K ≃+* K, ∃ k : ℤ, τ = σ ^ k := by
  let _ : Algebra (ZMod 3) K := ZMod.algebra K 3
  have hcomm : ∀ (f : K ≃+* K) (x : ZMod 3),
      f (algebraMap (ZMod 3) K x) = algebraMap (ZMod 3) K x := fun f x => by
    have := RingHom.ext_zmod (f.toRingHom.comp (algebraMap (ZMod 3) K)) (algebraMap (ZMod 3) K)
    exact congrArg (fun g : ZMod 3 →+* K => g x) this
  let toAlg : (K ≃+* K) → (K ≃ₐ[ZMod 3] K) := fun f => AlgEquiv.ofRingEquiv (hcomm f)
  let φ : (K ≃ₐ[ZMod 3] K) →* (K ≃+* K) :=
    { toFun := AlgEquiv.toRingEquiv, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hφ : ∀ f, φ (toAlg f) = f := fun f => rfl
  set H : Subgroup (K ≃ₐ[ZMod 3] K) := Subgroup.zpowers (toAlg σ)
  have hbot : IntermediateField.fixedField H = ⊥ := by
    refine le_bot_iff.1 fun x hx => ?_
    have hσx : σ x = x := ((IntermediateField.mem_fixedField_iff H x).1 hx) _
      (Subgroup.mem_zpowers _)
    rcases hfix x hσx with h | h | h
    · rw [h]; exact IntermediateField.zero_mem _
    · rw [h]; exact IntermediateField.one_mem _
    · rw [h]; exact IntermediateField.neg_mem _ (IntermediateField.one_mem _)
  have htop : H = ⊤ := by
    rw [← IntermediateField.fixingSubgroup_fixedField H, hbot,
      IntermediateField.fixingSubgroup_bot]
  intro τ
  have hτ : toAlg τ ∈ H := by rw [htop]; exact Subgroup.mem_top _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hτ
  refine ⟨k, ?_⟩
  rw [← hφ τ, ← hk, map_zpow, hφ]

theorem thompson_I (K : Type*) [Field K] [Fintype K] [CharP K 3] (n : ℕ) (hn : 1 ≤ n)
    (hK : Fintype.card K = 3 ^ (2 * n + 1)) {N : Type*} [Group N] [Finite N]
    (h : ThompsonIHyp N (3 ^ (2 * n + 1))) :
    ∃ σ : K ≃+* K, (∀ τ : K ≃+* K, ∃ k : ℤ, τ = σ ^ k) ∧ Nonempty (N ≃* ThompsonN K σ) := by
  obtain ⟨hN, P, R, hPR⟩ := h
  set q := 3 ^ (2 * n + 1) with hq
  have hm : Odd (2 * n + 1) := odd_two_mul_add_one n
  have hm3 : 3 ≤ 2 * n + 1 := by omega
  obtain ⟨σ, r, ℓ₁, ℓ₂, ℓ₃, hc⟩ := exists_normal_coords hPR hK rfl hm hm3
  obtain ⟨p, hp, hp1, hpinv⟩ := exists_p hPR hc
  have hKq : Fintype.card K = q := hK
  have hq3 : 3 < Fintype.card K := by
    rw [hK]
    calc 3 < 3 ^ 3 := by norm_num
      _ ≤ 3 ^ (2 * n + 1) := Nat.pow_le_pow_right (by norm_num) hm3
  have hsq : ∀ x : K, x ^ 2 ≠ -1 := by
    intro x hx
    have hsq' : IsSquare (-1 : K) := ⟨x, by rw [← hx, sq]⟩
    rw [FiniteField.isSquare_neg_one_iff, hK] at hsq'
    apply hsq'
    rw [hq, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  obtain ⟨c, hcf⟩ := Hf_formula hPR hc hKq hp hp1 hpinv hq3 hsq
  have hPR' : P ⊓ R = ⊥ := by
    refine disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard ?_)
    rw [hPR.card_P, hPR.card_R]
    refine Nat.Coprime.pow_left 3 ?_
    have h1 : 1 ≤ q := Nat.one_le_pow _ _ (by norm_num)
    rw [Nat.coprime_comm, Nat.coprime_self_sub_left h1]
    exact Nat.coprime_one_left q
  obtain ⟨e⟩ := nonempty_mulEquiv hPR hc hKq hp hp1 hpinv hcf hPR'
    (by rw [hN, hKq])
  exact ⟨σ, generates_of_fixed σ hc.fix, ⟨e.symm⟩⟩

end CFSG.Walter.Ree
