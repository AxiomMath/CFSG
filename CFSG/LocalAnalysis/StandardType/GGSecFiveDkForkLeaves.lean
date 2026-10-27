module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDkRoots
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDkRootsBasic
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDkRootsPairs
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDkRootsWeyl
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpupRoots

public section

namespace CFSG.StandardType

open CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin

private def GGSameSuppV {k : ℕ} (γ γ' : Fin k → ℤ) : Prop :=
  ∃ (a b : Fin k) (s : ℤ), a ≠ b ∧ (s = 1 ∨ s = -1) ∧
    (γ = Pi.single a 1 + Pi.single b s ∨ γ = -(Pi.single a 1 + Pi.single b s)) ∧
    (γ' = Pi.single a 1 - Pi.single b s ∨ γ' = -(Pi.single a 1 - Pi.single b s))

private def GGDisjSuppV {k : ℕ} (γ γ' : Fin k → ℤ) : Prop :=
  ∃ (a b c d : Fin k) (s s' u u' : ℤ), a ≠ b ∧ c ≠ d ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧
    (s = 1 ∨ s = -1) ∧ (s' = 1 ∨ s' = -1) ∧ (u = 1 ∨ u = -1) ∧ (u' = 1 ∨ u' = -1) ∧
    γ = Pi.single a s + Pi.single b s' ∧ γ' = Pi.single c u + Pi.single d u'

private theorem GGSameSuppV.toSameSupp {k : ℕ} {γ γ' : Fin k → ℤ} (h : GGSameSuppV γ γ')
    {t t' : ggWeylD k} (hγ : GGDReflRoot k t γ) (hγ' : GGDReflRoot k t' γ') :
    GGDSameSupp k t t' := by
  obtain ⟨a, b, s, hab, hs, hγe, hγ'e⟩ := h
  exact ⟨a, b, s, hab, hs, hγ.of_pm hγe, hγ'.of_pm hγ'e⟩

private theorem GGDisjSuppV.toDisjSupp {k : ℕ} {γ γ' : Fin k → ℤ} (h : GGDisjSuppV γ γ')
    {t t' : ggWeylD k} (hγ : GGDReflRoot k t γ) (hγ' : GGDReflRoot k t' γ') :
    GGDDisjSupp k t t' := by
  obtain ⟨a, b, c, d, s, s', u, u', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hγe, hγ'e⟩ := h
  exact ⟨a, b, c, d, s, s', u, u', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    hγ.of_pm (Or.inl hγe), hγ'.of_pm (Or.inl hγ'e)⟩

private theorem GGDisjSuppV.apply_eq_zero {k : ℕ} {γ γ' : Fin k → ℤ} (h : GGDisjSuppV γ γ')
    {z : Fin k} (hz : γ z ≠ 0) : γ' z = 0 := by
  obtain ⟨a, b, c, d, s, s', u, u', hab, hcd, hac, had, hbc, hbd, -, -, -, -, hγ, hγ'⟩ := h
  rw [hγ] at hz
  have hzab : z = a ∨ z = b := by
    by_contra h
    push Not at h
    exact hz (ggDPair_apply_of_ne h.1 h.2 s s')
  rcases hzab with rfl | rfl
  · rw [hγ', ggDPair_apply_of_ne hac had u u']
  · rw [hγ', ggDPair_apply_of_ne hbc hbd u u']

private theorem not_all_disj {k : ℕ} {γ₀ γ₁ γ₂ γ₃ : Fin k → ℤ} {x y : Fin k} {s t : ℤ}
    (h₀ : γ₀ = Pi.single x s + Pi.single y t)
    (d12 : GGDisjSuppV γ₁ γ₂) (d13 : GGDisjSuppV γ₁ γ₃) (d23 : GGDisjSuppV γ₂ γ₃)
    (hn1 : ggDDot γ₀ γ₁ ≠ 0) (hn2 : ggDDot γ₀ γ₂ ≠ 0) (hn3 : ggDDot γ₀ γ₃ ≠ 0) : False := by
  have h1xy : γ₁ x ≠ 0 ∨ γ₁ y ≠ 0 := by
    by_contra h
    push Not at h
    exact hn1 (by simp [h₀, ggDDot_single_add_single, h.1, h.2])
  have h2xy : γ₂ x ≠ 0 ∨ γ₂ y ≠ 0 := by
    by_contra h
    push Not at h
    exact hn2 (by simp [h₀, ggDDot_single_add_single, h.1, h.2])
  have h3xy : γ₃ x ≠ 0 ∨ γ₃ y ≠ 0 := by
    by_contra h
    push Not at h
    exact hn3 (by simp [h₀, ggDDot_single_add_single, h.1, h.2])
  by_cases hx1 : γ₁ x ≠ 0
  · have hx2 : γ₂ x = 0 := d12.apply_eq_zero hx1
    have hx3 : γ₃ x = 0 := d13.apply_eq_zero hx1
    have hy2 : γ₂ y ≠ 0 := by
      rcases h2xy with h | h
      · exact absurd hx2 h
      · exact h
    have hy3 : γ₃ y ≠ 0 := by
      rcases h3xy with h | h
      · exact absurd hx3 h
      · exact h
    exact hy3 (d23.apply_eq_zero hy2)
  · have hy1 : γ₁ y ≠ 0 := by
      rcases h1xy with h | h
      · exact absurd h hx1
      · exact h
    have hy2 : γ₂ y = 0 := d12.apply_eq_zero hy1
    have hy3 : γ₃ y = 0 := d13.apply_eq_zero hy1
    have hx2 : γ₂ x ≠ 0 := by
      rcases h2xy with h | h
      · exact h
      · exact absurd hy2 h
    have hx3 : γ₃ x ≠ 0 := by
      rcases h3xy with h | h
      · exact h
      · exact absurd hy3 h
    exact hx3 (d23.apply_eq_zero hx2)

private theorem pair_apply_ne_zero_iff {k : ℕ} {a b : Fin k} (hab : a ≠ b) {s : ℤ}
    (hs : s = 1 ∨ s = -1) (z : Fin k) :
    (Pi.single a 1 + Pi.single b s : Fin k → ℤ) z ≠ 0 ↔ z = a ∨ z = b := by
  constructor
  · intro hz
    by_contra h
    push Not at h
    exact hz (ggDPair_apply_of_ne h.1 h.2 1 s)
  · rintro (rfl | rfl)
    · rw [ggDPair_apply_left hab]
      norm_num
    · rw [ggDPair_apply_right hab]
      rcases hs with rfl | rfl <;> norm_num

private theorem not_all_same {k : ℕ} {γ₁ γ₂ γ₃ : Fin k → ℤ}
    (h12 : GGSameSuppV γ₁ γ₂) (h13 : GGSameSuppV γ₁ γ₃)
    (ho13 : ggDDot γ₁ γ₃ = 0) (ho23 : ggDDot γ₂ γ₃ = 0) : False := by
  obtain ⟨a, b, s, hab, hs, h1f, h2f⟩ := h12
  obtain ⟨c, d, t, hcd, ht, h1f', h3f'⟩ := h13
  have hc : c = a ∨ c = b := by
    have h1c : γ₁ c ≠ 0 := by
      rcases h1f' with h | h
      · rw [h, ggDPair_apply_left hcd]
        norm_num
      · rw [h]
        simp only [Pi.neg_apply, neg_ne_zero, ggDPair_apply_left hcd]
        norm_num
    rcases h1f with h | h
    · rw [h] at h1c
      exact (pair_apply_ne_zero_iff hab hs c).1 h1c
    · rw [h] at h1c
      simp only [Pi.neg_apply, neg_ne_zero] at h1c
      exact (pair_apply_ne_zero_iff hab hs c).1 h1c
  have hd : d = a ∨ d = b := by
    have h1d : γ₁ d ≠ 0 := by
      rcases h1f' with h | h
      · rw [h, ggDPair_apply_right hcd]
        rcases ht with rfl | rfl <;> norm_num
      · rw [h]
        simp only [Pi.neg_apply, neg_ne_zero, ggDPair_apply_right hcd]
        rcases ht with rfl | rfl <;> norm_num
    rcases h1f with h | h
    · rw [h] at h1d
      exact (pair_apply_ne_zero_iff hab hs d).1 h1d
    · rw [h] at h1d
      simp only [Pi.neg_apply, neg_ne_zero] at h1d
      exact (pair_apply_ne_zero_iff hab hs d).1 h1d
  have hswap : (c = a ∧ d = b) ∨ (c = b ∧ d = a) := by
    rcases hc with rfl | rfl
    · rcases hd with rfl | rfl
      · exact absurd rfl hcd
      · exact Or.inl ⟨rfl, rfl⟩
    · rcases hd with rfl | rfl
      · exact Or.inr ⟨rfl, rfl⟩
      · exact absurd rfl hcd
  have h3b : γ₃ b ≠ 0 := by
    rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases h3f' with h | h
      · rw [h, sub_eq_add_neg, ← Pi.single_neg, ggDPair_apply_right hab]
        rcases ht with rfl | rfl <;> norm_num
      · rw [h]
        simp only [Pi.neg_apply, neg_ne_zero, sub_eq_add_neg, ← Pi.single_neg,
          ggDPair_apply_right hab]
        rcases ht with rfl | rfl <;> norm_num
    · rcases h3f' with h | h
      · rw [h, sub_eq_add_neg, ← Pi.single_neg, ggDPair_apply_left (Ne.symm hab)]
        norm_num
      · rw [h]
        simp only [Pi.neg_apply, neg_ne_zero, sub_eq_add_neg, ← Pi.single_neg,
          ggDPair_apply_left (Ne.symm hab)]
        norm_num
  have e1 : γ₃ a + s * γ₃ b = 0 := by
    have h := ho13
    rcases h1f with h' | h'
    · rw [h', ggDDot_single_add_single] at h
      simpa using h
    · rw [h', ggDDot_eq_dotProduct, neg_dotProduct, ← ggDDot_eq_dotProduct,
        ggDDot_single_add_single] at h
      simpa using neg_eq_zero.1 h
  have e2 : γ₃ a - s * γ₃ b = 0 := by
    have h := ho23
    rcases h2f with h' | h'
    · rw [h', sub_eq_add_neg, ← Pi.single_neg, ggDDot_single_add_single] at h
      simpa [sub_eq_add_neg] using h
    · rw [h', ggDDot_eq_dotProduct, neg_dotProduct, ← ggDDot_eq_dotProduct,
        sub_eq_add_neg, ← Pi.single_neg, ggDDot_single_add_single] at h
      simpa [sub_eq_add_neg] using neg_eq_zero.1 h
  rcases hs with rfl | rfl
  · simp only [one_mul] at e1 e2
    have hb0 : γ₃ b = 0 := by omega
    exact h3b hb0
  · simp only [neg_one_mul] at e1 e2
    have hb0 : γ₃ b = 0 := by omega
    exact h3b hb0

theorem ggDDot_eq_zero_of_commute {k : ℕ} (hk : 2 ≤ k) {t t' : ggWeylD k}
    {γ γ' : Fin k → ℤ} (h : GGDReflRoot k t γ) (h' : GGDReflRoot k t' γ')
    (hcomm : t * t' = t' * t) (hne : t ≠ t') : ggDDot γ γ' = 0 := by
  obtain ⟨w, i, -, hw⟩ := id h
  have key : toStdD k (weylAction (isFiniteType_cartanD k) (t * t')
        (weylAction (isFiniteType_cartanD k) w (Pi.single i 1))) =
      toStdD k (weylAction (isFiniteType_cartanD k) (t' * t)
        (weylAction (isFiniteType_cartanD k) w (Pi.single i 1))) := by
    rw [hcomm]
  rw [weylAction_mul_apply, weylAction_mul_apply, h.action hk, h'.action hk,
    h'.action hk, h.action hk, hw] at key
  rcases ggDReflect_comm_dot (ggDDot_self_of_mem (h.mem (by omega)))
    (ggDDot_self_of_mem (h'.mem (by omega))) key with h0 | h0 | h0
  · exact h0
  · exact absurd (h.unique hk h' (Or.inl h0)) hne
  · exact absurd (h.unique hk h' (Or.inr h0)) hne

theorem ggDk_fork_leaves {k : ℕ} (hk : 4 ≤ k) {t₀ t₁ t₂ t₃ : ggWeylD k}
    (h₀ : ∃ γ, GGDReflRoot k t₀ γ) (h₁ : ∃ γ, GGDReflRoot k t₁ γ)
    (h₂ : ∃ γ, GGDReflRoot k t₂ γ) (h₃ : ∃ γ, GGDReflRoot k t₃ γ)
    (h12 : t₁ * t₂ = t₂ * t₁) (h13 : t₁ * t₃ = t₃ * t₁) (h23 : t₂ * t₃ = t₃ * t₂)
    (hn12 : t₁ ≠ t₂) (hn13 : t₁ ≠ t₃) (hn23 : t₂ ≠ t₃)
    (hn01 : t₀ * t₁ ≠ t₁ * t₀) (hn02 : t₀ * t₂ ≠ t₂ * t₀) (hn03 : t₀ * t₃ ≠ t₃ * t₀) :
    (GGDSameSupp k t₁ t₂ ∨ GGDSameSupp k t₁ t₃ ∨ GGDSameSupp k t₂ t₃) ∧
      (GGDDisjSupp k t₁ t₂ ∨ GGDDisjSupp k t₁ t₃ ∨ GGDDisjSupp k t₂ t₃) := by
  have hk2 : 2 ≤ k := by omega
  have hk1 : k ≠ 1 := by omega
  obtain ⟨γ₀, hγ₀⟩ := h₀
  obtain ⟨γ₁, hγ₁⟩ := h₁
  obtain ⟨γ₂, hγ₂⟩ := h₂
  obtain ⟨γ₃, hγ₃⟩ := h₃
  have hm0 : γ₀ ∈ ggDRootSet k := hγ₀.mem hk1
  have hm1 : γ₁ ∈ ggDRootSet k := hγ₁.mem hk1
  have hm2 : γ₂ ∈ ggDRootSet k := hγ₂.mem hk1
  have hm3 : γ₃ ∈ ggDRootSet k := hγ₃.mem hk1
  have ho12 : ggDDot γ₁ γ₂ = 0 := ggDDot_eq_zero_of_commute hk2 hγ₁ hγ₂ h12 hn12
  have ho13 : ggDDot γ₁ γ₃ = 0 := ggDDot_eq_zero_of_commute hk2 hγ₁ hγ₃ h13 hn13
  have ho23 : ggDDot γ₂ γ₃ = 0 := ggDDot_eq_zero_of_commute hk2 hγ₂ hγ₃ h23 hn23
  have hn0₁ : ggDDot γ₀ γ₁ ≠ 0 := fun h => hn01 (hγ₀.commute_of_dot_eq_zero hk2 hγ₁ h)
  have hn0₂ : ggDDot γ₀ γ₂ ≠ 0 := fun h => hn02 (hγ₀.commute_of_dot_eq_zero hk2 hγ₂ h)
  have hn0₃ : ggDDot γ₀ γ₃ ≠ 0 := fun h => hn03 (hγ₀.commute_of_dot_eq_zero hk2 hγ₃ h)
  have k12 := ggDRootSet_orth hm1 hm2 ho12
  have k13 := ggDRootSet_orth hm1 hm3 ho13
  have k23 := ggDRootSet_orth hm2 hm3 ho23
  have hS : GGSameSuppV γ₁ γ₂ ∨ GGSameSuppV γ₁ γ₃ ∨ GGSameSuppV γ₂ γ₃ := by
    rcases k12 with h | h
    · exact Or.inl h
    rcases k13 with h' | h'
    · exact Or.inr (Or.inl h')
    rcases k23 with h'' | h''
    · exact Or.inr (Or.inr h'')
    · obtain ⟨x, y, s, t, hxy, -, -, h0e⟩ := hm0
      exact False.elim (not_all_disj h0e h h' h'' hn0₁ hn0₂ hn0₃)
  have hD : GGDisjSuppV γ₁ γ₂ ∨ GGDisjSuppV γ₁ γ₃ ∨ GGDisjSuppV γ₂ γ₃ := by
    rcases k12 with h | h
    · rcases k13 with h' | h'
      · rcases k23 with h'' | h''
        · exact False.elim (not_all_same h h' ho13 ho23)
        · exact Or.inr (Or.inr h'')
      · exact Or.inr (Or.inl h')
    · exact Or.inl h
  refine ⟨?_, ?_⟩
  · rcases hS with h | h | h
    · exact Or.inl (h.toSameSupp hγ₁ hγ₂)
    · exact Or.inr (Or.inl (h.toSameSupp hγ₁ hγ₃))
    · exact Or.inr (Or.inr (h.toSameSupp hγ₂ hγ₃))
  · rcases hD with h | h | h
    · exact Or.inl (h.toDisjSupp hγ₁ hγ₂)
    · exact Or.inr (Or.inl (h.toDisjSupp hγ₁ hγ₃))
    · exact Or.inr (Or.inr (h.toDisjSupp hγ₂ hγ₃))

end CFSG.StandardType

end
