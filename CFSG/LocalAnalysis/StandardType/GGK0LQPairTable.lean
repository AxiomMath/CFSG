module

public import CFSG.LocalAnalysis.StandardType.GGK0LQExt

public section

namespace CFSG.StandardType.GGK0LQ

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.LieType.Steinberg.Adjoint in
private lemma lk0xlqpair_iform_zsmul_add
    {τ : Tag} (a b : ℤ) (α β : Fin τ.rank → ℤ) :
    iform (a • α + b • β) (a • α + b • β) =
      a ^ 2 * iform α α + 2 * a * b * iform α β + b ^ 2 * iform β β := by
  simp only [iform_add_left, iform_add_right, iform_smul_left, iform_smul_right]
  rw [iform_comm β α]
  ring

private lemma lk0xlqpair_no_sq_two (c : ℤ) : c ^ 2 ≠ 2 := by
  intro h
  have h' : c * c = 2 := by simpa [pow_two] using h
  have h3 : ((c : ZMod 3)) * (c : ZMod 3) = (2 : ZMod 3) := by
    rw [← Int.cast_mul, h']; norm_num
  have hno : ∀ x : ZMod 3, x * x ≠ (2 : ZMod 3) := by decide
  exact hno (c : ZMod 3) h3

open CFSG.LieType.Steinberg.Adjoint in
private lemma lk0xlqpair_noG2_E6 : NoG2 Tag.E6 := fun i => Or.inl (by fin_cases i <;> rfl)

open CFSG.LieType.Steinberg.Adjoint in
private lemma lk0xlqpair_noG2_E7 : NoG2 Tag.E7 := fun i => Or.inl (by fin_cases i <;> rfl)

open CFSG.LieType.Steinberg.Adjoint in
private lemma lk0xlqpair_noG2_F4 :
    NoG2 Tag.F4 := noG2_F4

open CFSG.LieType.Steinberg.Adjoint in
private lemma lk0xlqpair_noG2_E8 :
    NoG2 Tag.E8 := noG2_E8

open CFSG.LieType.Steinberg.Adjoint in
private lemma lk0xlqpair_axis
    {τ : Tag} (hτ : NoG2 τ) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) {c : ℤ}
    (hc : c ≠ 0) (h : IsRoot τ (c • γ)) : c • γ = γ ∨ c • γ = -γ := by
  have hform : iform (c • γ) (c • γ) = c ^ 2 * iform γ γ := by
    rw [iform_smul_left, iform_smul_right]; ring
  have hc2 : c ^ 2 = 1 := by
    have h1 := iform_self_cases hτ h
    have h2 := iform_self_cases hτ hγ
    rw [hform] at h1
    rcases h2 with h2 | h2
    · rw [h2] at h1
      rcases h1 with h1 | h1
      · nlinarith
      · exact absurd (by nlinarith : c ^ 2 = 2) (lk0xlqpair_no_sq_two c)
    · rw [h2] at h1
      rcases h1 with h1 | h1 <;> nlinarith
  rcases (sq_eq_one_iff.mp hc2) with hc1 | hc1
  · left; rw [hc1, one_smul]
  · right; rw [hc1]; simp

open CFSG.LieType.Steinberg.Adjoint in
private lemma lk0xlqpair_pos_single
    {τ : Tag} {α β : Fin τ.rank → ℤ} (hτ : NoG2 τ)
    (hα : IsRoot τ α) (hβ : IsRoot τ β) (hne : α ≠ β) (hne' : α ≠ -β)
    (hN : iform α α = iform β β) {a b : ℤ} (ha : 0 < a) (hb : 0 < b)
    (hv : IsRoot τ (a • α + b • β)) : a = 1 ∧ b = 1 := by
  have ha1 : 1 ≤ a := by omega
  have hb1 : 1 ≤ b := by omega
  have ha' : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg (by omega)
  have hb' : ((b.toNat : ℕ) : ℤ) = b := Int.toNat_of_nonneg (by omega)
  have hconv : (a.toNat) • α + (b.toNat) • β = a • α + b • β := by
    rw [← Nat.cast_smul_eq_nsmul ℤ a.toNat α, ← Nat.cast_smul_eq_nsmul ℤ b.toNat β, ha', hb']
  have hroot : IsRoot τ ((a.toNat) • α + (b.toNat) • β) := by rw [hconv]; exact hv
  have hia : 1 ≤ a.toNat := by omega
  have hib : 1 ≤ b.toNat := by omega
  rcases exponent_pair_cases hτ hα hβ hne hne' hia hib hroot with
    ⟨h1, h2⟩ | ⟨h1, h2, hA, hB, hS⟩ | ⟨h1, h2, hA, hB, hS⟩
  · rw [h1] at ha'; rw [h2] at hb'; omega
  · omega
  · omega

open CFSG.LieType.Steinberg.Adjoint in
private lemma lk0xlqpair_pos_double
    {τ : Tag} {α β : Fin τ.rank → ℤ} (hτ : NoG2 τ)
    (hα : IsRoot τ α) (hβ : IsRoot τ β) (hne : α ≠ β) (hne' : α ≠ -β)
    (hA : iform α α = 4) {a b : ℤ} (ha : 0 < a) (hb : 0 < b)
    (hv : IsRoot τ (a • α + b • β)) : (a = 1 ∧ b = 1) ∨ (a = 1 ∧ b = 2) := by
  have ha1 : 1 ≤ a := by omega
  have hb1 : 1 ≤ b := by omega
  have ha' : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg (by omega)
  have hb' : ((b.toNat : ℕ) : ℤ) = b := Int.toNat_of_nonneg (by omega)
  have hconv : (a.toNat) • α + (b.toNat) • β = a • α + b • β := by
    rw [← Nat.cast_smul_eq_nsmul ℤ a.toNat α, ← Nat.cast_smul_eq_nsmul ℤ b.toNat β, ha', hb']
  have hroot : IsRoot τ ((a.toNat) • α + (b.toNat) • β) := by rw [hconv]; exact hv
  have hia : 1 ≤ a.toNat := by omega
  have hib : 1 ≤ b.toNat := by omega
  rcases exponent_pair_cases hτ hα hβ hne hne' hia hib hroot with
    ⟨h1, h2⟩ | ⟨h1, h2, h4, h2', hs⟩ | ⟨h1, h2, h2', h4, hs⟩
  · left; rw [h1] at ha'; rw [h2] at hb'; exact ⟨by omega, by omega⟩
  · right; rw [h1] at ha'; rw [h2] at hb'; exact ⟨by omega, by omega⟩
  · omega

open CFSG.LieType.Steinberg.Adjoint in
private lemma lk0xlqpair_root_mem_span_single
    {τ : Tag} {α β : Fin τ.rank → ℤ} (hτ : NoG2 τ)
    (hα : IsRoot τ α) (hβ : IsRoot τ β) (hne : α ≠ β) (hne' : α ≠ -β)
    (hN : iform α α = iform β β) (h2S : 2 * iform α β = -(iform α α))
    (hsum : IsRoot τ (α + β))
    {v : Fin τ.rank → ℤ} (hv : IsRoot τ v)
    (hmem : v ∈ Submodule.span ℤ ({α, β} : Set (Fin τ.rank → ℤ))) :
    v = α ∨ v = β ∨ v = -α ∨ v = -β ∨ v = α + β ∨ v = -(α + β) := by
  obtain ⟨a, b, hab⟩ := (Submodule.mem_span_pair).1 hmem
  rw [← hab] at hv ⊢
  have hNpos : 2 ≤ iform α α := by
    rcases iform_self_cases hτ hα with h | h <;> omega
  have hform : ∀ a b : ℤ, iform (a • α + b • β) (a • α + b • β) =
      iform α α * (a ^ 2 - a * b + b ^ 2) := by
    intro a b
    rw [lk0xlqpair_iform_zsmul_add, ← hN]
    have hc : 2 * a * b * iform α β = -(a * b) * iform α α := by
      linear_combination (a * b) * h2S
    rw [hc]; ring
  have hnoMix : ¬ ((0 < a ∧ b < 0) ∨ (a < 0 ∧ 0 < b)) := by
    rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
    · have ha1 : 1 ≤ a := by omega
      have hb1 : b ≤ -1 := by omega
      have h2 := iform_self_cases hτ hv
      rw [hform a b] at h2
      have hge : 3 ≤ a ^ 2 - a * b + b ^ 2 := by
        nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a + b)]
      rcases h2 with h2 | h2 <;> nlinarith
    · have ha1 : a ≤ -1 := by omega
      have hb1 : 1 ≤ b := by omega
      have h2 := iform_self_cases hτ hv
      rw [hform a b] at h2
      have hge : 3 ≤ a ^ 2 - a * b + b ^ 2 := by
        nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a + b)]
      rcases h2 with h2 | h2 <;> nlinarith
  rcases lt_trichotomy a 0 with ha | ha | ha
  · rcases lt_trichotomy b 0 with hb | hb | hb
    · have hneg : IsRoot τ (-(a • α + b • β)) := IsRoot.neg hv
      have heq : -(a • α + b • β) = (-a) • α + (-b) • β := by ext k; simp; ring
      have h11 := lk0xlqpair_pos_single hτ hα hβ hne hne' hN
        (by omega : 0 < -a) (by omega : 0 < -b) (by rw [← heq]; exact hneg)
      have ha1 : a = -1 := by omega
      have hb1 : b = -1 := by omega
      have hgoal : a • α + b • β = -(α + β) := by rw [ha1, hb1]; ext k; simp; ring
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hgoal))))
    · have h0 : a • α + b • β = a • α := by rw [hb]; simp
      rw [h0] at hv ⊢
      rcases lk0xlqpair_axis hτ hα (by omega : a ≠ 0) hv with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
    · exact absurd (Or.inr ⟨ha, hb⟩) hnoMix
  · rcases lt_trichotomy b 0 with hb | hb | hb
    · have h0 : a • α + b • β = b • β := by rw [ha]; simp
      rw [h0] at hv ⊢
      rcases lk0xlqpair_axis hτ hβ (by omega : b ≠ 0) hv with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exfalso
      rw [ha, hb] at hv
      simp only [zero_smul, zero_add] at hv
      exact IsRoot.ne_zero hv rfl
    · have h0 : a • α + b • β = b • β := by rw [ha]; simp
      rw [h0] at hv ⊢
      rcases lk0xlqpair_axis hτ hβ (by omega : b ≠ 0) hv with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases lt_trichotomy b 0 with hb | hb | hb
    · exact absurd (Or.inl ⟨ha, hb⟩) hnoMix
    · have h0 : a • α + b • β = a • α := by rw [hb]; simp
      rw [h0] at hv ⊢
      rcases lk0xlqpair_axis hτ hα (by omega : a ≠ 0) hv with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
    · have h11 := lk0xlqpair_pos_single hτ hα hβ hne hne' hN ha hb hv
      have hgoal : a • α + b • β = α + β := by rw [h11.1, h11.2]; ext k; simp
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hgoal))))

open CFSG.LieType.Steinberg.Adjoint in
private lemma lk0xlqpair_root_mem_span_double
    {τ : Tag} {α β : Fin τ.rank → ℤ} (hτ : NoG2 τ)
    (hα : IsRoot τ α) (hβ : IsRoot τ β) (hne : α ≠ β) (hne' : α ≠ -β)
    (hA : iform α α = 4) (hB : iform β β = 2) (hS : iform α β = -2)
    (hsum : IsRoot τ (α + β)) (hsum2 : IsRoot τ (α + 2 • β))
    {v : Fin τ.rank → ℤ} (hv : IsRoot τ v)
    (hmem : v ∈ Submodule.span ℤ ({α, β} : Set (Fin τ.rank → ℤ))) :
    v = α ∨ v = β ∨ v = -α ∨ v = -β ∨ v = α + β ∨ v = -(α + β) ∨
      v = α + 2 • β ∨ v = -(α + 2 • β) := by
  obtain ⟨a, b, hab⟩ := (Submodule.mem_span_pair).1 hmem
  rw [← hab] at hv ⊢
  have hform : ∀ a b : ℤ, iform (a • α + b • β) (a • α + b • β) =
      4 * a ^ 2 - 4 * a * b + 2 * b ^ 2 := by
    intro a b
    rw [lk0xlqpair_iform_zsmul_add, hA, hB, hS]; ring
  have hnoMix : ¬ ((0 < a ∧ b < 0) ∨ (a < 0 ∧ 0 < b)) := by
    rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
    · have ha1 : 1 ≤ a := by omega
      have hb1 : b ≤ -1 := by omega
      have h2 := iform_self_cases hτ hv
      rw [hform a b] at h2
      rcases h2 with h2 | h2 <;> nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a + b)]
    · have ha1 : a ≤ -1 := by omega
      have hb1 : 1 ≤ b := by omega
      have h2 := iform_self_cases hτ hv
      rw [hform a b] at h2
      rcases h2 with h2 | h2 <;> nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a + b)]
  rcases lt_trichotomy a 0 with ha | ha | ha
  · rcases lt_trichotomy b 0 with hb | hb | hb
    · have hneg : IsRoot τ (-(a • α + b • β)) := IsRoot.neg hv
      have heq : -(a • α + b • β) = (-a) • α + (-b) • β := by ext k; simp; ring
      have hcases := lk0xlqpair_pos_double hτ hα hβ hne hne' hA
        (by omega : 0 < -a) (by omega : 0 < -b) (by rw [← heq]; exact hneg)
      rcases hcases with ⟨ha1, hb1⟩ | ⟨ha1, hb1⟩
      · have ha2 : a = -1 := by omega
        have hb2 : b = -1 := by omega
        have hgoal : a • α + b • β = -(α + β) := by rw [ha2, hb2]; ext k; simp; ring
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hgoal)))))
      · have ha2 : a = -1 := by omega
        have hb2 : b = -2 := by omega
        have hgoal : a • α + b • β = -(α + 2 • β) := by
          rw [ha2, hb2]; ext k; simp; ring
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hgoal))))))
    · have h0 : a • α + b • β = a • α := by rw [hb]; simp
      rw [h0] at hv ⊢
      rcases lk0xlqpair_axis hτ hα (by omega : a ≠ 0) hv with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
    · exact absurd (Or.inr ⟨ha, hb⟩) hnoMix
  · rcases lt_trichotomy b 0 with hb | hb | hb
    · have h0 : a • α + b • β = b • β := by rw [ha]; simp
      rw [h0] at hv ⊢
      rcases lk0xlqpair_axis hτ hβ (by omega : b ≠ 0) hv with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exfalso
      rw [ha, hb] at hv
      simp only [zero_smul, zero_add] at hv
      exact IsRoot.ne_zero hv rfl
    · have h0 : a • α + b • β = b • β := by rw [ha]; simp
      rw [h0] at hv ⊢
      rcases lk0xlqpair_axis hτ hβ (by omega : b ≠ 0) hv with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases lt_trichotomy b 0 with hb | hb | hb
    · exact absurd (Or.inl ⟨ha, hb⟩) hnoMix
    · have h0 : a • α + b • β = a • α := by rw [hb]; simp
      rw [h0] at hv ⊢
      rcases lk0xlqpair_axis hτ hα (by omega : a ≠ 0) hv with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
    · have hcases := lk0xlqpair_pos_double hτ hα hβ hne hne' hA ha hb hv
      rcases hcases with ⟨ha1, hb1⟩ | ⟨ha1, hb1⟩
      · have hgoal : a • α + b • β = α + β := by rw [ha1, hb1]; ext k; simp
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hgoal))))
      · have hgoal : a • α + b • β = α + 2 • β := by rw [ha1, hb1]; ext k; simp
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hgoal))))))

open CFSG.LieType.Steinberg.Adjoint in
private lemma lk0xlqpair_set_eq_single
    {τ : Tag} {α β : Fin τ.rank → ℤ} (hτ : NoG2 τ)
    (hα : IsRoot τ α) (hβ : IsRoot τ β) (hne : α ≠ β) (hne' : α ≠ -β)
    (hN : iform α α = iform β β) (h2S : 2 * iform α β = -(iform α α))
    (hsum : IsRoot τ (α + β)) :
    ({v : Fin τ.rank → ℤ | IsRoot τ v ∧
        v ∈ Submodule.span ℤ ({α, β} : Set (Fin τ.rank → ℤ))} : Set (Fin τ.rank → ℤ)) =
      (({α, β, -α, -β, α + β, -(α + β)} : Finset (Fin τ.rank → ℤ)) : Set _) := by
  ext v
  constructor
  · rintro ⟨hv, hmem⟩
    rcases lk0xlqpair_root_mem_span_single hτ hα hβ hne hne' hN h2S hsum hv hmem with
      h | h | h | h | h | h <;> (subst h; simp)
  · intro hv
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with h | h | h | h | h | h
    · subst h; exact ⟨hα, Submodule.subset_span (by simp)⟩
    · subst h; exact ⟨hβ, Submodule.subset_span (by simp)⟩
    · subst h; refine ⟨IsRoot.neg hα, ?_⟩
      rw [neg_mem_iff]; exact Submodule.subset_span (by simp)
    · subst h; refine ⟨IsRoot.neg hβ, ?_⟩
      rw [neg_mem_iff]; exact Submodule.subset_span (by simp)
    · subst h; exact ⟨hsum, Submodule.add_mem _
        (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))⟩
    · subst h; refine ⟨IsRoot.neg hsum, ?_⟩
      rw [neg_mem_iff]; exact Submodule.add_mem _
        (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))

open CFSG.LieType.Steinberg.Adjoint in
private lemma lk0xlqpair_set_eq_double
    {τ : Tag} {α β : Fin τ.rank → ℤ} (hτ : NoG2 τ)
    (hα : IsRoot τ α) (hβ : IsRoot τ β) (hne : α ≠ β) (hne' : α ≠ -β)
    (hA : iform α α = 4) (hB : iform β β = 2) (hS : iform α β = -2)
    (hsum : IsRoot τ (α + β)) (hsum2 : IsRoot τ (α + 2 • β)) :
    ({v : Fin τ.rank → ℤ | IsRoot τ v ∧
        v ∈ Submodule.span ℤ ({α, β} : Set (Fin τ.rank → ℤ))} : Set (Fin τ.rank → ℤ)) =
      (({α, β, -α, -β, α + β, -(α + β), α + 2 • β, -(α + 2 • β)} :
        Finset (Fin τ.rank → ℤ)) : Set _) := by
  ext v
  constructor
  · rintro ⟨hv, hmem⟩
    rcases lk0xlqpair_root_mem_span_double hτ hα hβ hne hne' hA hB hS hsum hsum2 hv hmem with
      h | h | h | h | h | h | h | h <;> (subst h; simp)
  · intro hv
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with h | h | h | h | h | h | h | h
    · subst h; exact ⟨hα, Submodule.subset_span (by simp)⟩
    · subst h; exact ⟨hβ, Submodule.subset_span (by simp)⟩
    · subst h; refine ⟨IsRoot.neg hα, ?_⟩
      rw [neg_mem_iff]; exact Submodule.subset_span (by simp)
    · subst h; refine ⟨IsRoot.neg hβ, ?_⟩
      rw [neg_mem_iff]; exact Submodule.subset_span (by simp)
    · subst h; exact ⟨hsum, Submodule.add_mem _
        (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))⟩
    · subst h; refine ⟨IsRoot.neg hsum, ?_⟩
      rw [neg_mem_iff]; exact Submodule.add_mem _
        (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
    · subst h; exact ⟨hsum2, Submodule.add_mem _
        (Submodule.subset_span (by simp))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))⟩
    · subst h; refine ⟨IsRoot.neg hsum2, ?_⟩
      rw [neg_mem_iff]; exact Submodule.add_mem _
        (Submodule.subset_span (by simp)) (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

open CFSG.LieType.Steinberg.Adjoint in
private lemma lk0xlqpair_ncard_six
    {τ : Tag} {α β : Fin τ.rank → ℤ} (hτ : NoG2 τ)
    (hα : IsRoot τ α) (hβ : IsRoot τ β) (hne : α ≠ β) (hne' : α ≠ -β)
    (hN : iform α α = iform β β) (h2S : 2 * iform α β = -(iform α α))
    (hsum : IsRoot τ (α + β))
    (hcard : ({α, β, -α, -β, α + β, -(α + β)} : Finset (Fin τ.rank → ℤ)).card = 6) :
    ({v : Fin τ.rank → ℤ | IsRoot τ v ∧
        v ∈ Submodule.span ℤ ({α, β} : Set (Fin τ.rank → ℤ))} : Set _).ncard = 6 := by
  rw [lk0xlqpair_set_eq_single hτ hα hβ hne hne' hN h2S hsum, Set.ncard_coe_finset]
  exact hcard

open CFSG.LieType.Steinberg.Adjoint in
private lemma lk0xlqpair_ncard_eight
    {τ : Tag} {α β : Fin τ.rank → ℤ} (hτ : NoG2 τ)
    (hα : IsRoot τ α) (hβ : IsRoot τ β) (hne : α ≠ β) (hne' : α ≠ -β)
    (hA : iform α α = 4) (hB : iform β β = 2) (hS : iform α β = -2)
    (hsum : IsRoot τ (α + β)) (hsum2 : IsRoot τ (α + 2 • β))
    (hcard : ({α, β, -α, -β, α + β, -(α + β), α + 2 • β, -(α + 2 • β)} :
      Finset (Fin τ.rank → ℤ)).card = 8) :
    ({v : Fin τ.rank → ℤ | IsRoot τ v ∧
        v ∈ Submodule.span ℤ ({α, β} : Set (Fin τ.rank → ℤ))} : Set _).ncard = 8 := by
  rw [lk0xlqpair_set_eq_double hτ hα hβ hne hne' hA hB hS hsum hsum2, Set.ncard_coe_finset]
  exact hcard

theorem lq_pair_ncard_table
    (τ : Tag) (T : GGKacType) (hτ : absTag T = τ) (x y : ℕ) (hxy : x < y)
    (hy : y < (k0DiagOf T).marks.length) (hadj : 0 < (k0DiagOf T).adj x y) :
    {v : Fin τ.rank → ℤ | IsRoot τ v ∧
        v ∈ Submodule.span ℤ {lqExtRoot τ T x, lqExtRoot τ T y}}.ncard =
      if (k0CompType (k0DiagOf T) [x, y]).1 = .A then 6 else 8 := by
  rw [← hτ] at *
  cases T
  case E6 =>
    change y < 7 at hy
    change 0 < (K0Diag.adj k0E6Diag x y) at hadj
    dsimp only [absTag] at ⊢
    interval_cases y <;> interval_cases x <;>
      (try (exfalso; exact absurd hadj (by decide))) <;>
      (try (rw [if_pos (by decide)])) <;>
      (try (rw [if_neg (by decide)])) <;>
      (first | apply lk0xlqpair_ncard_six | apply lk0xlqpair_ncard_eight) <;>
      (try (exact lk0xlqpair_noG2_F4)) <;>
      (try (exact lk0xlqpair_noG2_E8)) <;>
      (try (exact lk0xlqpair_noG2_E6)) <;>
      (try (exact lk0xlqpair_noG2_E7)) <;>
      (try decide) <;>
      (try (rw [isRoot_iff_mem_artifactRoots]; decide))
  case E7 =>
    change y < 8 at hy
    change 0 < (K0Diag.adj k0E7Diag x y) at hadj
    dsimp only [absTag] at ⊢
    interval_cases y <;> interval_cases x <;>
      (try (exfalso; exact absurd hadj (by decide))) <;>
      (try (rw [if_pos (by decide)])) <;>
      (try (rw [if_neg (by decide)])) <;>
      (first | apply lk0xlqpair_ncard_six | apply lk0xlqpair_ncard_eight) <;>
      (try (exact lk0xlqpair_noG2_F4)) <;>
      (try (exact lk0xlqpair_noG2_E8)) <;>
      (try (exact lk0xlqpair_noG2_E6)) <;>
      (try (exact lk0xlqpair_noG2_E7)) <;>
      (try decide) <;>
      (try (rw [isRoot_iff_mem_artifactRoots]; decide))
  case E8 =>
    change y < 9 at hy
    change 0 < (K0Diag.adj k0E8Diag x y) at hadj
    dsimp only [absTag] at ⊢
    interval_cases y <;> interval_cases x <;>
      (try (exfalso; exact absurd hadj (by decide))) <;>
      (try (rw [if_pos (by decide)])) <;>
      (try (rw [if_neg (by decide)])) <;>
      (first | apply lk0xlqpair_ncard_six | apply lk0xlqpair_ncard_eight) <;>
      (try (exact lk0xlqpair_noG2_F4)) <;>
      (try (exact lk0xlqpair_noG2_E8)) <;>
      (try (exact lk0xlqpair_noG2_E6)) <;>
      (try (exact lk0xlqpair_noG2_E7)) <;>
      (try decide) <;>
      (try (rw [isRoot_iff_mem_artifactRoots]; decide))
  case F4 =>
    change y < 5 at hy
    change 0 < (K0Diag.adj k0F4Diag x y) at hadj
    dsimp only [absTag] at ⊢
    interval_cases y <;> interval_cases x <;>
      (try (exfalso; exact absurd hadj (by decide))) <;>
      (try (rw [if_pos (by decide)])) <;>
      (try (rw [if_neg (by decide)])) <;>
      (first | apply lk0xlqpair_ncard_six | apply lk0xlqpair_ncard_eight) <;>
      (try (exact lk0xlqpair_noG2_F4)) <;>
      (try (exact lk0xlqpair_noG2_E8)) <;>
      (try (exact lk0xlqpair_noG2_E6)) <;>
      (try (exact lk0xlqpair_noG2_E7)) <;>
      (try decide) <;>
      (try (rw [isRoot_iff_mem_artifactRoots]; decide))

end CFSG.StandardType.GGK0LQ

end
