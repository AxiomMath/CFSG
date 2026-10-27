module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDefs

public section

namespace CFSG.StandardType

theorem ggDDot_eq_dotProduct {k : ℕ} (u v : Fin k → ℤ) : ggDDot u v = u ⬝ᵥ v := rfl

theorem ggDDot_comm {k : ℕ} (u v : Fin k → ℤ) : ggDDot u v = ggDDot v u :=
  dotProduct_comm u v

theorem ggDReflect_apply {k : ℕ} (γ δ : Fin k → ℤ) (c : Fin k) :
    ggDReflect γ δ c = δ c - ggDDot δ γ * γ c := rfl

theorem ggDReflect_neg {k : ℕ} (γ δ : Fin k → ℤ) : ggDReflect (-γ) δ = ggDReflect γ δ := by
  simp only [ggDReflect, ggDDot_eq_dotProduct, dotProduct_neg, neg_smul, smul_neg, neg_neg]

theorem ggDDot_single_add_single {k : ℕ} (a b : Fin k) (s t : ℤ) (v : Fin k → ℤ) :
    ggDDot (Pi.single a s + Pi.single b t) v = s * v a + t * v b := by
  rw [ggDDot_eq_dotProduct, add_dotProduct, single_dotProduct, single_dotProduct]

theorem ggDPair_apply_left {k : ℕ} {a b : Fin k} (hab : a ≠ b) (s t : ℤ) :
    (Pi.single a s + Pi.single b t : Fin k → ℤ) a = s := by
  simp [hab]

theorem ggDPair_apply_right {k : ℕ} {a b : Fin k} (hab : a ≠ b) (s t : ℤ) :
    (Pi.single a s + Pi.single b t : Fin k → ℤ) b = t := by
  simp [hab.symm]

theorem ggDPair_apply_of_ne {k : ℕ} {a b c : Fin k} (hca : c ≠ a) (hcb : c ≠ b) (s t : ℤ) :
    (Pi.single a s + Pi.single b t : Fin k → ℤ) c = 0 := by
  simp [hca, hcb]

theorem ggDRootSet_apply {k : ℕ} {η : Fin k → ℤ} (h : η ∈ ggDRootSet k) (c : Fin k) :
    η c = 0 ∨ η c = 1 ∨ η c = -1 := by
  obtain ⟨a, b, s, t, hab, hs, ht, rfl⟩ := h
  by_cases hca : c = a
  · rw [hca, ggDPair_apply_left hab]
    omega
  by_cases hcb : c = b
  · rw [hcb, ggDPair_apply_right hab]
    omega
  rw [ggDPair_apply_of_ne hca hcb]
  omega

theorem ggDRootSet_sign {k : ℕ} {η : Fin k → ℤ} (h : η ∈ ggDRootSet k) {c : Fin k}
    (hc : η c ≠ 0) : η c = 1 ∨ η c = -1 := by
  have := ggDRootSet_apply h c
  omega

theorem ggDRootSet_exists_pair {k : ℕ} {η : Fin k → ℤ} (h : η ∈ ggDRootSet k) :
    ∃ a b : Fin k, a ≠ b ∧ η a ≠ 0 ∧ η b ≠ 0 := by
  obtain ⟨a, b, s, t, hab, hs, ht, rfl⟩ := h
  refine ⟨a, b, hab, ?_, ?_⟩
  · rw [ggDPair_apply_left hab]
    omega
  · rw [ggDPair_apply_right hab]
    omega

theorem ggDRootSet_eq_zero {k : ℕ} {η : Fin k → ℤ} (h : η ∈ ggDRootSet k) {a b c : Fin k}
    (hab : a ≠ b) (ha : η a ≠ 0) (hb : η b ≠ 0) (hca : c ≠ a) (hcb : c ≠ b) : η c = 0 := by
  obtain ⟨a', b', s, t, -, -, -, rfl⟩ := h
  have key : ∀ x, (Pi.single a' s + Pi.single b' t : Fin k → ℤ) x ≠ 0 → x = a' ∨ x = b' := by
    intro x hx
    by_contra hne
    exact hx (ggDPair_apply_of_ne (fun e => hne (Or.inl e)) (fun e => hne (Or.inr e)) s t)
  by_contra hc
  rcases key a ha with rfl | rfl <;> rcases key b hb with rfl | rfl <;>
    rcases key c hc with rfl | rfl <;> simp_all

theorem ggDRootSet_eq_single_add_single {k : ℕ} {η : Fin k → ℤ} (h : η ∈ ggDRootSet k)
    {a b : Fin k} (hab : a ≠ b) (ha : η a ≠ 0) (hb : η b ≠ 0) :
    η = Pi.single a (η a) + Pi.single b (η b) := by
  funext c
  by_cases hca : c = a
  · rw [hca, ggDPair_apply_left hab]
  by_cases hcb : c = b
  · rw [hcb, ggDPair_apply_right hab]
  rw [ggDPair_apply_of_ne hca hcb, ggDRootSet_eq_zero h hab ha hb hca hcb]

theorem ggDRootSet_dot_eq {k : ℕ} {η : Fin k → ℤ} (h : η ∈ ggDRootSet k) {a b : Fin k}
    (hab : a ≠ b) (ha : η a ≠ 0) (hb : η b ≠ 0) (v : Fin k → ℤ) :
    ggDDot η v = η a * v a + η b * v b := by
  conv_lhs => rw [ggDRootSet_eq_single_add_single h hab ha hb]
  exact ggDDot_single_add_single a b (η a) (η b) v

theorem ggDDot_ggDReflect {k : ℕ} (v γ δ : Fin k → ℤ) :
    ggDDot v (ggDReflect γ δ) = ggDDot v δ - ggDDot δ γ * ggDDot v γ := by
  simp only [ggDReflect, ggDDot_eq_dotProduct, dotProduct_sub, dotProduct_smul, smul_eq_mul]

theorem ggDRootSet_exists_ne {k : ℕ} {η : Fin k → ℤ} (h : η ∈ ggDRootSet k) {a : Fin k}
    (ha : η a ≠ 0) : ∃ b, b ≠ a ∧ η b ≠ 0 := by
  obtain ⟨x, y, hxy, hx, hy⟩ := ggDRootSet_exists_pair h
  by_cases hax : a = x
  · exact ⟨y, fun e => hxy (hax.symm.trans e.symm), hy⟩
  by_cases hay : a = y
  · exact ⟨x, fun e => hxy (e.trans hay), hx⟩
  exact absurd (ggDRootSet_eq_zero h hxy hx hy hax hay) ha

theorem ggDDot_self_of_mem {k : ℕ} {η : Fin k → ℤ} (h : η ∈ ggDRootSet k) :
    ggDDot η η = 2 := by
  obtain ⟨a, b, s, t, hab, hs, ht, rfl⟩ := h
  rw [ggDDot_single_add_single, ggDPair_apply_left hab, ggDPair_apply_right hab]
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> norm_num

theorem GGDSubsys.neg_mem {k : ℕ} {Φ : Set (Fin k → ℤ)} (hΦ : GGDSubsys k Φ) {η : Fin k → ℤ}
    (hη : η ∈ Φ) : -η ∈ Φ := by
  have h := hΦ.2 η hη η hη
  rwa [ggDReflect, ggDDot_self_of_mem (hΦ.1 hη), two_smul, sub_add_cancel_left] at h

theorem ggDReflect_swap {k : ℕ} {x y : Fin k} (hxy : x ≠ y) (u : Fin k → ℤ) :
    ggDReflect (Pi.single x 1 + Pi.single y (-1)) u = u ∘ Equiv.swap x y := by
  funext c
  rw [ggDReflect_apply, ggDDot_comm, ggDDot_single_add_single, Function.comp_apply]
  by_cases hcx : c = x
  · rw [hcx, ggDPair_apply_left hxy, Equiv.swap_apply_left]
    ring
  by_cases hcy : c = y
  · rw [hcy, ggDPair_apply_right hxy, Equiv.swap_apply_right]
    ring
  rw [ggDPair_apply_of_ne hcx hcy, Equiv.swap_apply_of_ne_of_ne hcx hcy]
  ring

end CFSG.StandardType

end
