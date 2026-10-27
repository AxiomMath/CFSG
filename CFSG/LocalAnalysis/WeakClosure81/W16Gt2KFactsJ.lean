module

public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2KFactsI

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

theorem kFacts_suProjTv_comm_of_herm_eq_zero (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ}
    {c a : Fin m → F} (hc : herm (unitaryInvolution F 2 n) c c = 0)
    (ha : herm (unitaryInvolution F 2 n) a a = 0) (h : herm (unitaryInvolution F 2 n) c a = 0)
    {s t : F} (hs : s + unitaryInvolution F 2 n s = 0) (ht : t + unitaryInvolution F 2 n t = 0) :
    kFactsSuProjTv hF m c s * kFactsSuProjTv hF m a t =
      kFactsSuProjTv hF m a t * kFactsSuProjTv hF m c s := by
  have hσ := isUnitaryInvolution_unitaryInvolution hF
  have hac : herm (unitaryInvolution F 2 n) a c = 0 :=
    herm_eq_zero_comm (unitaryInvolution F 2 n) hσ.invol h
  have hfix : suTv hσ a t • c = c := by
    rw [suTv_smul hσ ha ht, hac, mul_zero, zero_smul, add_zero]
  have hconj := suTv_conj hσ (suTv hσ a t) hc hs
  rw [hfix] at hconj
  have hcomm : suTv hσ a t * suTv hσ c s = suTv hσ c s * suTv hσ a t :=
    mul_inv_eq_iff_eq_mul.mp hconj
  unfold kFactsSuProjTv
  rw [← map_mul, ← map_mul, hcomm.symm]

theorem kFacts_su_hyperbolic_pair (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 2 ≤ n) {m : ℕ}
    (hm : 4 ≤ m) (A B : Subgroup (StatedProj (StatedSU m (2 ^ n) F)))
    (hA : Nat.card A = 2 ^ n) (hB : Nat.card B = 2 ^ n)
    (hAt : ∀ x ∈ A, x ≠ 1 → IsUnitaryTransvectionIn m n x)
    (hBt : ∀ x ∈ B, x ≠ 1 → IsUnitaryTransvectionIn m n x)
    (hnc : ¬ (∀ a ∈ A, ∀ b ∈ B, a * b = b * a)) :
    ∃ e f : Fin m → F, herm (unitaryInvolution F 2 n) e e = 0 ∧
      herm (unitaryInvolution F 2 n) f f = 0 ∧ herm (unitaryInvolution F 2 n) e f = 1 ∧
      (∀ x : StatedProj (StatedSU m (2 ^ n) F), x ∈ A ↔
        ∃ s : F, s + unitaryInvolution F 2 n s = 0 ∧ x = kFactsSuProjTv hF m e s) ∧
      (∀ x : StatedProj (StatedSU m (2 ^ n) F), x ∈ B ↔
        ∃ s : F, s + unitaryInvolution F 2 n s = 0 ∧ x = kFactsSuProjTv hF m f s) := by
  set σ := unitaryInvolution F 2 n with hσdef
  have hσ := isUnitaryInvolution_unitaryInvolution hF
  obtain ⟨e, he0, he, hAe⟩ := kFacts_su_rootGroup hF hn hm A hA hAt
  obtain ⟨f, hf0, hf, hBf⟩ := kFacts_su_rootGroup hF hn hm B hB hBt
  have hef : herm σ e f ≠ 0 := by
    intro h0
    apply hnc
    intro x hx y hy
    obtain ⟨s, hs, rfl⟩ := (hAe x).mp hx
    obtain ⟨t, ht, rfl⟩ := (hBf y).mp hy
    exact kFacts_suProjTv_comm_of_herm_eq_zero hF he hf h0 hs ht
  obtain ⟨l, hl⟩ : ∃ l : F, l = (herm σ e f)⁻¹ := ⟨_, rfl⟩
  have hl0 : l ≠ 0 := by rw [hl]; exact inv_ne_zero hef
  have hν : σ l * l ≠ 0 := mul_ne_zero ((map_ne_zero_iff σ σ.injective).mpr hl0) hl0
  have hfixν : σ (σ l * l) = σ l * l := by rw [map_mul, hσ.invol, mul_comm]
  have htr : ∀ s : F, s + σ s = 0 → σ l * l * s + σ (σ l * l * s) = 0 := by
    intro s hs
    rw [map_mul, hfixν]
    calc σ l * l * s + σ l * l * σ s = σ l * l * (s + σ s) := by ring
      _ = 0 := by rw [hs, mul_zero]
  have htr' : ∀ s : F, s + σ s = 0 → (σ l * l)⁻¹ * s + σ ((σ l * l)⁻¹ * s) = 0 := by
    intro s hs
    rw [map_mul, map_inv₀, hfixν]
    calc (σ l * l)⁻¹ * s + (σ l * l)⁻¹ * σ s = (σ l * l)⁻¹ * (s + σ s) := by ring
      _ = 0 := by rw [hs, mul_zero]
  refine ⟨e, l • f, he, ?_, ?_, hAe, ?_⟩
  · rw [herm_smul_left, herm_smul_right, hf, mul_zero, mul_zero]
  · rw [herm_smul_right, hl, inv_mul_cancel₀ hef]
  · intro x
    rw [hBf x]
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨(σ l * l)⁻¹ * s, htr' s hs, ?_⟩
      rw [kFacts_suProjTv_smul_vec hF hf (htr' s hs) l, mul_inv_cancel_left₀ hν]
    · rintro ⟨s', hs', rfl⟩
      refine ⟨σ l * l * s', htr s' hs', ?_⟩
      rw [kFacts_suProjTv_smul_vec hF hf hs' l]

end CFSG.LocalAnalysis.WeakClosure81
