module

public import CFSG.RankThree.GF2n.Smith81.S81BGeom

public section

namespace CFSG.RankThree.GF2n.Smith81.EGeom

section Generic

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem closure_fix_sub {S : Set (V ≃ₗ[K] V)} {p v : V} (h : ∀ s ∈ S, s p = p)
    (hv : ∀ s ∈ S, s v - v ∈ Submodule.span K {p}) :
    ∀ u ∈ Subgroup.closure S, u p = p ∧ u v - v ∈ Submodule.span K {p} := by
  intro u hu
  refine Subgroup.closure_induction
    (p := fun u _ => u p = p ∧ u v - v ∈ Submodule.span K {p}) (fun s hs => ⟨h s hs, hv s hs⟩)
    ⟨rfl, by simp⟩ ?_ ?_ hu
  · rintro x y - - ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨?_, ?_⟩
    · show x (y p) = p
      rw [hy, hx]
    · have hsplit : (x * y) v - v = x (y v - v) + (x v - v) := by
        show x (y v) - v = _
        rw [map_sub]
        abel
      rw [hsplit]
      refine add_mem ?_ hx'
      obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hy'
      rw [← ht, map_smul, hx]
      exact Submodule.smul_mem _ t (Submodule.mem_span_singleton_self p)
  · rintro x - ⟨hx, hx'⟩
    have hinv : x⁻¹ p = p := by
      have h1 : x⁻¹ (x p) = p := by simp
      rwa [hx] at h1
    refine ⟨hinv, ?_⟩
    have hsplit : x⁻¹ v - v = x⁻¹ (-(x v - v)) := by
      rw [map_neg, map_sub]
      have h2 : x⁻¹ (x v) = v := by simp
      rw [h2]
      abel
    rw [hsplit]
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (neg_mem hx')
    rw [← ht, map_smul, hinv]
    exact Submodule.smul_mem _ t (Submodule.mem_span_singleton_self p)

theorem mem_Wsp_closure_iff {S : Set (V ≃ₗ[K] V)} {p v : V} (h : ∀ s ∈ S, s p = p) :
    v ∈ Wsp (Submodule.span K {p}) (Subgroup.closure S) ↔
      ∀ s ∈ S, s v - v ∈ Submodule.span K {p} := by
  constructor
  · intro hv s hs
    exact hv s (Subgroup.subset_closure hs)
  · intro hv u hu
    exact (closure_fix_sub h hv u hu).2

theorem card_le_of_vanish {ι : Type*} [Finite K] {W : Submodule K (ι →₀ K)} (N : Finset ι)
    (h : ∀ v ∈ W, ∀ b, b ∉ N → v b = 0) : Nat.card W ≤ Nat.card K ^ N.card := by
  have hinj : Function.Injective (fun (v : W) (b : N) => (v : ι →₀ K) b) := by
    intro v w hvw
    apply Subtype.ext
    apply Finsupp.ext
    intro b
    by_cases hb : b ∈ N
    · exact congrFun hvw ⟨b, hb⟩
    · rw [h v v.2 b hb, h w w.2 b hb]
  calc Nat.card W ≤ Nat.card (N → K) := Nat.card_le_card_of_injective _ hinj
    _ = Nat.card K ^ Nat.card N := Nat.card_fun
    _ = Nat.card K ^ N.card := by rw [Nat.card_eq_finsetCard]

theorem exists_sl2 {Γ : Subgroup (V ≃ₗ[K] V)} {e₁ e₂ : V} {X Y : K → (V ≃ₗ[K] V)}
    (hX : ∀ c, X c ∈ Γ) (hY : ∀ c, Y c ∈ Γ) (hX1 : ∀ c, X c e₁ = e₁)
    (hX2 : ∀ c, X c e₂ = e₂ + c • e₁) (hY1 : ∀ c, Y c e₁ = e₁ + c • e₂)
    (hY2 : ∀ c, Y c e₂ = e₂) (a b : K) (h : a ≠ 0 ∨ b ≠ 0) :
    ∃ g ∈ Γ, g e₁ = a • e₁ + b • e₂ := by
  have hn : ∀ t : K, t ≠ 0 → (X t * Y (-t⁻¹) * X t) ∈ Γ := fun t _ =>
    mul_mem (mul_mem (hX t) (hY _)) (hX t)
  have hn1 : ∀ t : K, t ≠ 0 → (X t * Y (-t⁻¹) * X t) e₁ = (-t⁻¹) • e₂ := by
    intro t ht
    show X t (Y (-t⁻¹) (X t e₁)) = _
    simp only [hX1, hY1, map_add, map_smul, hX2]
    match_scalars <;> field_simp <;> ring
  have hn2 : ∀ t : K, t ≠ 0 → (X t * Y (-t⁻¹) * X t) e₂ = t • e₁ := by
    intro t ht
    show X t (Y (-t⁻¹) (X t e₂)) = _
    simp only [hX2, map_add, map_smul, hY1, hY2, hX1]
    match_scalars <;> field_simp <;> ring
  by_cases hb : b = 0
  · have ha : a ≠ 0 := h.resolve_right (by simpa using hb)
    refine ⟨(X a * Y (-a⁻¹) * X a) * (X (-1) * Y (-(-1 : K)⁻¹) * X (-1)), mul_mem (hn a ha)
      (hn (-1) (by simp)), ?_⟩
    show (X a * Y (-a⁻¹) * X a) ((X (-1) * Y (-(-1 : K)⁻¹) * X (-1)) e₁) = _
    rw [hn1 (-1) (by simp)]
    simp only [map_smul, hn2 a ha, hb]
    match_scalars <;> field_simp <;> ring
  · refine ⟨X (a / b) * (X (-b⁻¹) * Y (-(-b⁻¹)⁻¹) * X (-b⁻¹)), mul_mem (hX _)
      (hn (-b⁻¹) (by simpa using hb)), ?_⟩
    show X (a / b) ((X (-b⁻¹) * Y (-(-b⁻¹)⁻¹) * X (-b⁻¹)) e₁) = _
    rw [hn1 (-b⁻¹) (by simpa using hb)]
    simp only [map_smul, hX2]
    match_scalars <;> field_simp <;> ring

end Generic

section Basis

variable {K : Type*} [Field K] {ι : Type*}

theorem vanish_of_far {S : Set ((ι →₀ K) ≃ₗ[K] (ι →₀ K))} {i₀ : ι}
    (hfix : ∀ s ∈ S, s (Finsupp.single i₀ 1) = Finsupp.single i₀ 1) {b : ι}
    (hb : ∃ s ∈ S, ∃ b', b' ≠ i₀ ∧ ∀ v : ι →₀ K, (s v - v) b' = v b) {v : ι →₀ K}
    (hv : v ∈ Wsp (Submodule.span K {(Finsupp.single i₀ 1 : ι →₀ K)}) (Subgroup.closure S)) :
    v b = 0 := by
  obtain ⟨s, hs, b', hb', hsb⟩ := hb
  have h1 := (mem_Wsp_closure_iff hfix).mp hv s hs
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp h1
  rw [← hsb v, ← ht]
  simp [Finsupp.single_apply, hb'.symm]

theorem minuscGeom_of_basis [Finite K] {Γ : Subgroup ((ι →₀ K) ≃ₗ[K] (ι →₀ K))}
    {S : Set ((ι →₀ K) ≃ₗ[K] (ι →₀ K))} {i₀ μ : ι} {N : Finset ι} {n : ℕ}
    (hS : S ⊆ Γ) (hfix : ∀ s ∈ S, s (Finsupp.single i₀ 1) = Finsupp.single i₀ 1)
    (hN : N.card = n)
    (hfar : ∀ b, b ∉ N → ∃ s ∈ S, ∃ b', b' ≠ i₀ ∧ ∀ v : ι →₀ K, (s v - v) b' = v b)
    (hμ : μ ≠ i₀)
    (hμW : ∀ s ∈ S, s (Finsupp.single μ 1) - Finsupp.single μ 1 ∈
      Submodule.span K {(Finsupp.single i₀ 1 : ι →₀ K)})
    (X Y : K → ((ι →₀ K) ≃ₗ[K] (ι →₀ K))) (hX : ∀ c, X c ∈ Γ) (hY : ∀ c, Y c ∈ Γ)
    (hX1 : ∀ c, X c (Finsupp.single i₀ 1) = Finsupp.single i₀ 1)
    (hX2 : ∀ c, X c (Finsupp.single μ 1) = Finsupp.single μ 1 + c • Finsupp.single i₀ 1)
    (hY1 : ∀ c, Y c (Finsupp.single i₀ 1) = Finsupp.single i₀ 1 + c • Finsupp.single μ 1)
    (hY2 : ∀ c, Y c (Finsupp.single μ 1) = Finsupp.single μ 1) :
    MinuscGeom Γ (Finsupp.single i₀ 1) (Subgroup.closure S) n where
  p₀_ne := Finsupp.single_ne_zero.mpr one_ne_zero
  U₀_le := (Subgroup.closure_le Γ).mpr hS
  U₀_fix := fun u hu => (closure_fix_sub hfix (v := 0) (fun s _ => by simp) u hu).1
  W_le := by
    calc Nat.card (Wsp (Submodule.span K {(Finsupp.single i₀ 1 : ι →₀ K)}) (Subgroup.closure S))
        ≤ Nat.card K ^ N.card :=
          card_le_of_vanish N fun v hv b hb => vanish_of_far hfix (hfar b hb) hv
      _ = Nat.card K ^ n := by rw [hN]
  line := by
    have hpW : (Finsupp.single i₀ 1 : ι →₀ K) ∈
        Wsp (Submodule.span K {(Finsupp.single i₀ 1 : ι →₀ K)}) (Subgroup.closure S) := by
      rw [mem_Wsp_closure_iff hfix]
      intro s hs
      rw [hfix s hs, sub_self]
      exact zero_mem _
    have hμW' : (Finsupp.single μ 1 : ι →₀ K) ∈
        Wsp (Submodule.span K {(Finsupp.single i₀ 1 : ι →₀ K)}) (Subgroup.closure S) :=
      (mem_Wsp_closure_iff hfix).mpr hμW
    refine ⟨Y 1, hY 1, ?_, ?_, ?_⟩
    · rw [hY1, one_smul]
      exact add_mem hpW hμW'
    · rw [hY1, one_smul]
      intro h
      obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp h
      have h2 := congrArg (fun f : ι →₀ K => f μ) ht
      simp [Finsupp.single_apply, hμ, hμ.symm] at h2
    · intro a b hab
      have h' : a + b ≠ 0 ∨ b ≠ 0 := by
        by_cases hb : b = 0
        · left
          rw [hb, add_zero]
          exact hab.resolve_right (by simpa using hb)
        · exact Or.inr hb
      obtain ⟨g, hg, hgp⟩ := exists_sl2 hX hY hX1 hX2 hY1 hY2 (a + b) b h'
      refine ⟨g, hg, ?_⟩
      rw [hgp, hY1, one_smul]
      module

end Basis

end CFSG.RankThree.GF2n.Smith81.EGeom
