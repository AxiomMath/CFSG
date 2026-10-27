module

public import CFSG.Monster.B.TwoA.Amalgam.Triangle

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open SimpleGraph CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam

@[expose] def cvSetStab
    (C : Set CVert) : Subgroup Shat where
  carrier := {s | ∀ x, cvMul x s ∈ C ↔ x ∈ C}
  mul_mem' {a b} ha hb := fun x => by
    rw [cvMul_mul]
    exact (hb (cvMul x a)).trans (ha x)
  one_mem' := fun x => by rw [cvMul_one]
  inv_mem' {a} ha := fun x => by
    have h := ha (cvMul x a⁻¹)
    rw [cvMul_inv_cancel'] at h
    exact h.symm

theorem mem_cvSetStab
    {C : Set CVert} {s : Shat} :
    s ∈ cvSetStab C ↔ ∀ x, cvMul x s ∈ C ↔ x ∈ C := Iff.rfl

theorem mem_cvSetStab_of
    {C : Set CVert} {s : Shat} (hmaps : ∀ x ∈ C, cvMul x s ∈ C)
    (hsurj : ∀ y ∈ C, ∃ x ∈ C, cvMul x s = y) : s ∈ cvSetStab C := fun x => by
  refine ⟨fun hx => ?_, hmaps x⟩
  obtain ⟨x', hx', e⟩ := hsurj _ hx
  rwa [← cvMul_injective s e]

theorem mem_cvSetStab_pair
    {v w : CVert} (hvw : v ≠ w) {s : Shat} :
    s ∈ cvSetStab {v, w} ↔
      (cvMul v s = v ∧ cvMul w s = w) ∨ (cvMul v s = w ∧ cvMul w s = v) := by
  constructor
  · intro h
    have hv : cvMul v s = v ∨ cvMul v s = w := (h v).2 (Set.mem_insert v _)
    have hw : cvMul w s = v ∨ cvMul w s = w := (h w).2 (Set.mem_insert_of_mem v rfl)
    have hne : cvMul v s ≠ cvMul w s := fun e => hvw (cvMul_injective s e)
    rcases hv with hv | hv <;> rcases hw with hw | hw
    · exact absurd (hv.trans hw.symm) hne
    · exact Or.inl ⟨hv, hw⟩
    · exact Or.inr ⟨hv, hw⟩
    · exact absurd (hv.trans hw.symm) hne
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · refine mem_cvSetStab_of ?_ ?_
      · rintro x (rfl | rfl)
        · rw [h1]; exact Set.mem_insert x _
        · rw [h2]; exact Set.mem_insert_of_mem v rfl
      · rintro y (rfl | rfl)
        · exact ⟨y, Set.mem_insert y _, h1⟩
        · exact ⟨y, Set.mem_insert_of_mem v rfl, h2⟩
    · refine mem_cvSetStab_of ?_ ?_
      · rintro x (rfl | rfl)
        · rw [h1]; exact Set.mem_insert_of_mem x rfl
        · rw [h2]; exact Set.mem_insert v _
      · rintro y (rfl | rfl)
        · exact ⟨w, Set.mem_insert_of_mem y rfl, h2⟩
        · exact ⟨v, Set.mem_insert v _, h1⟩

theorem mem_cvSetStab_triple
    {v w u : CVert} {s : Shat}
    (hmaps : cvMul v s ∈ ({v, w, u} : Set CVert) ∧ cvMul w s ∈ ({v, w, u} : Set CVert) ∧
      cvMul u s ∈ ({v, w, u} : Set CVert))
    (hsurj : ∀ y ∈ ({v, w, u} : Set CVert), ∃ x ∈ ({v, w, u} : Set CVert), cvMul x s = y) :
    s ∈ cvSetStab {v, w, u} := by
  refine mem_cvSetStab_of ?_ hsurj
  rintro x (rfl | rfl | rfl)
  · exact hmaps.1
  · exact hmaps.2.1
  · exact hmaps.2.2

theorem triType_cvMul
    (a b c : CVert) (s : Shat) :
    triType (cvMul a s) (cvMul b s) (cvMul c s) = triType a b c := by
  have e : pairStabOrbit (cvMul a s) (cvMul b s) (cvMul c s) =
      (fun x => cvMul x s) '' pairStabOrbit a b c := by
    ext x
    constructor
    · rintro ⟨t, h1, h2, h3⟩
      refine ⟨cvMul x s⁻¹, ⟨s * t * s⁻¹, ?_, ?_, ?_⟩, cvMul_inv_cancel' x s⟩
      · rw [cvMul_mul, cvMul_mul, h1, cvMul_inv_cancel]
      · rw [cvMul_mul, cvMul_mul, h2, cvMul_inv_cancel]
      · rw [cvMul_mul, cvMul_mul, h3]
    · rintro ⟨y, ⟨t, h1, h2, h3⟩, rfl⟩
      refine ⟨s⁻¹ * t * s, ?_, ?_, ?_⟩
      · rw [cvMul_mul, cvMul_mul, cvMul_inv_cancel, h1]
      · rw [cvMul_mul, cvMul_mul, cvMul_inv_cancel, h2]
      · rw [cvMul_mul, cvMul_mul, cvMul_inv_cancel, h3]
  rw [triType, triType, e, Set.ncard_image_of_injective _ (cvMul_injective s)]

theorem exists_cvMul_eq_of_triType_eq
    {a b c c' : CVert} (hab : cgraph.Adj a b)
    (hac : cgraph.Adj a c) (hac' : cgraph.Adj a c') (h : triType a b c = triType a b c') :
    ∃ t : Shat, cvMul a t = a ∧ cvMul b t = b ∧ cvMul c t = c' := by
  obtain ⟨M, -⟩ := exists_rootModel a
  have e := M.triType_eq_orbSize ⟨b, hab⟩ ⟨c, hac⟩
  have e' := M.triType_eq_orbSize ⟨b, hab⟩ ⟨c', hac'⟩
  obtain ⟨γ, hγ, hγc⟩ := mem_conjOrbit_of_orbSize_eq (M.pt_mem ⟨b, hab⟩) (M.pt_mem ⟨c, hac⟩)
    (M.pt_mem ⟨c', hac'⟩) (e.symm.trans (h.trans e'))
  obtain ⟨y, hya, hy⟩ := M.exists_act γ⁻¹
  refine ⟨y, hya, ?_, ?_⟩
  · obtain ⟨hw, hpt⟩ := hy ⟨b, hab⟩
    have hc : γ * M.pt ⟨b, hab⟩ = M.pt ⟨b, hab⟩ * γ :=
      Subgroup.mem_centralizer_singleton_iff.1 hγ
    have hpt' : M.pt ⟨cvMul b y, hw⟩ = γ⁻¹⁻¹ * M.pt ⟨b, hab⟩ * γ⁻¹ := hpt
    have h1 : M.pt ⟨cvMul b y, hw⟩ = M.pt ⟨b, hab⟩ := by
      rw [hpt', inv_inv, hc, mul_inv_cancel_right]
    exact congrArg Subtype.val (M.pt_injective h1)
  · obtain ⟨hw, hpt⟩ := hy ⟨c, hac⟩
    have hpt' : M.pt ⟨cvMul c y, hw⟩ = γ⁻¹⁻¹ * M.pt ⟨c, hac⟩ * γ⁻¹ := hpt
    have h1 : M.pt ⟨cvMul c y, hw⟩ = M.pt ⟨c', hac'⟩ := by
      rw [hpt', inv_inv, hγc]
    exact congrArg Subtype.val (M.pt_injective h1)

theorem exists_swap_of_isCTriangle
    {v w u : CVert} (h : IsCTriangle v w u) :
    ∃ s : Shat, cvMul v s = w ∧ cvMul w s = v ∧ cvMul u s = u := by
  obtain ⟨hvw, hvu, hwu⟩ := h
  obtain ⟨s, hsv, hsw⟩ := cvMul_edge_transitive hvw hvw.symm
  have hu1 : cgraph.Adj v (cvMul u s) := by
    have h' := (cgraph_adj_cvMul w u s).2 hwu
    rwa [hsw] at h'
  have htype : triType v w (cvMul u s) = triType v w u := by
    have h' := triType_cvMul w v u s
    rw [hsw, hsv] at h'
    rw [h', triType_swap_left]
  obtain ⟨t, htv, htw, htu⟩ := exists_cvMul_eq_of_triType_eq hvw hu1 hvu htype
  exact ⟨s * t, by rw [cvMul_mul, hsv, htw], by rw [cvMul_mul, hsw, htv],
    by rw [cvMul_mul, htu]⟩

theorem exists_cycle_of_isCTriangle
    {v w u : CVert} (h : IsCTriangle v w u) :
    ∃ s : Shat, cvMul v s = w ∧ cvMul w s = u ∧ cvMul u s = v := by
  obtain ⟨hvw, hvu, hwu⟩ := h
  obtain ⟨s, hsv, hsw⟩ := cvMul_edge_transitive hvw hwu
  have hu1 : cgraph.Adj w (cvMul u s) := by
    have h' := (cgraph_adj_cvMul v u s).2 hvu
    rwa [hsv] at h'
  have htype : triType w u (cvMul u s) = triType w u v := by
    have h' := triType_cvMul v w u s
    rw [hsv, hsw] at h'
    rw [h', (triType_perm ⟨hvw, hvu, hwu⟩).2.2.1]
  obtain ⟨t, htw, htu, htv⟩ := exists_cvMul_eq_of_triType_eq hwu hu1 hvw.symm htype
  exact ⟨s * t, by rw [cvMul_mul, hsv, htw], by rw [cvMul_mul, hsw, htu],
    by rw [cvMul_mul, htv]⟩

theorem exists_triangle_orbit
    {v w : CVert} (hvw : cgraph.Adj v w) {u : Fin 2 → CVert}
    (hu : ∀ j, cgraph.Adj v (u j) ∧ cgraph.Adj w (u j))
    (htype : triType v w (u 0) = 1782 ∧ triType v w (u 1) = 44352) {y₁ y₂ : CVert}
    (h₁ : cgraph.Adj v y₁) (h₁₂ : cgraph.Adj y₁ y₂) (h₂ : cgraph.Adj y₂ v) :
    ∃ j, ∃ s : Shat, cvMul v s = v ∧ cvMul w s = y₁ ∧ cvMul (u j) s = y₂ := by
  obtain ⟨s, hsv, hsw⟩ := cvMul_edge_transitive hvw h₁
  have hy₂v : cgraph.Adj v (cvMul y₂ s⁻¹) := by
    have h' := (cgraph_adj_cvMul v y₂ s⁻¹).2 h₂.symm
    rwa [cvMul_inv_eq_of_cvMul_eq hsv] at h'
  have hy₂w : cgraph.Adj w (cvMul y₂ s⁻¹) := by
    have h' := (cgraph_adj_cvMul y₁ y₂ s⁻¹).2 h₁₂
    rwa [← hsw, cvMul_inv_cancel] at h'
  obtain ⟨M, -⟩ := exists_rootModel v
  have hj : ∃ j, triType v w (u j) = triType v w (cvMul y₂ s⁻¹) := by
    rcases triType_eq_or M ⟨hvw, hy₂v, hy₂w⟩ with h | h
    · exact ⟨0, htype.1.trans h.symm⟩
    · exact ⟨1, htype.2.trans h.symm⟩
  obtain ⟨j, hj⟩ := hj
  obtain ⟨t, htv, htw, htu⟩ := exists_cvMul_eq_of_triType_eq hvw (hu j).1 hy₂v hj
  exact ⟨j, t * s, by rw [cvMul_mul, htv, hsv], by rw [cvMul_mul, htw, hsw],
    by rw [cvMul_mul, htu, cvMul_inv_cancel']⟩

theorem exists_triangle_types
    {v w : CVert} (hvw : cgraph.Adj v w) :
    ∃ u : Fin 2 → CVert, (∀ j, cgraph.Adj v (u j) ∧ cgraph.Adj w (u j)) ∧
      triType v w (u 0) = 1782 ∧ triType v w (u 1) = 44352 := by
  obtain ⟨-, -, -, -, ⟨a₀, b₀, c₀, h₀, e₀⟩, a₁, b₁, c₁, h₁, e₁⟩ :=
    native_triangle_local_orbit_permutation_invariance
  have move : ∀ {a b c : CVert}, IsCTriangle a b c → ∃ u, cgraph.Adj v u ∧ cgraph.Adj w u ∧
      triType v w u = triType a b c := by
    intro a b c hT
    obtain ⟨s, hsa, hsb⟩ := cvMul_edge_transitive hT.1 hvw
    refine ⟨cvMul c s, ?_, ?_, ?_⟩
    · have h' := (cgraph_adj_cvMul a c s).2 hT.2.1
      rwa [hsa] at h'
    · have h' := (cgraph_adj_cvMul b c s).2 hT.2.2
      rwa [hsb] at h'
    · rw [← hsa, ← hsb, triType_cvMul]
  obtain ⟨u₀, hu₀v, hu₀w, hu₀⟩ := move h₀
  obtain ⟨u₁, hu₁v, hu₁w, hu₁⟩ := move h₁
  refine ⟨![u₀, u₁], fun j => ?_, hu₀.trans e₀, hu₁.trans e₁⟩
  fin_cases j
  · exact ⟨hu₀v, hu₀w⟩
  · exact ⟨hu₁v, hu₁w⟩

end CFSG.Monster.B.GSide
