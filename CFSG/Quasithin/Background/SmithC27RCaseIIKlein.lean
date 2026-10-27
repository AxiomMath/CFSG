module

public import CFSG.Quasithin.Background.SmithC27RCaseIIPerm

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.QuasithinUnique Equiv Equiv.Perm

variable {α : Type} [Fintype α] [DecidableEq α]

@[expose] def kleinGens (Γ : Set α) : Set (Perm α) :=
  {g | (∀ x, x ∉ Γ → g x = x) ∧ (∀ x ∈ Γ, g x ≠ x) ∧ g * g = 1}

@[expose] def kleinOf (Γ : Set α) : Subgroup (Perm α) := Subgroup.closure (kleinGens Γ)

omit [Fintype α] [DecidableEq α] in
theorem conj_mem_kleinGens {Γ : Set α} {m g : Perm α} (hg : g ∈ kleinGens Γ) :
    m * g * m⁻¹ ∈ kleinGens ((m : α → α) '' Γ) := by
  obtain ⟨h1, h2, h3⟩ := hg
  refine ⟨fun x hx => ?_, fun x hx => ?_, ?_⟩
  · have hx' : m⁻¹ x ∉ Γ := fun h => hx ⟨m⁻¹ x, h, by simp⟩
    show m (g (m⁻¹ x)) = x
    rw [h1 _ hx']
    exact m.apply_symm_apply x
  · obtain ⟨y, hy, rfl⟩ := hx
    show m (g (m⁻¹ (m y))) ≠ m y
    rw [show m⁻¹ (m y) = y from m.symm_apply_apply y]
    intro h
    exact h2 y hy (m.injective h)
  · calc m * g * m⁻¹ * (m * g * m⁻¹) = m * (g * g) * m⁻¹ := by group
      _ = 1 := by rw [h3, mul_one, mul_inv_cancel]

omit [Fintype α] [DecidableEq α] in
theorem map_conj_kleinOf (Γ : Set α) (m : Perm α) :
    (kleinOf Γ).map (MulAut.conj m).toMonoidHom = kleinOf ((m : α → α) '' Γ) := by
  apply le_antisymm
  · rw [kleinOf, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    exact Subgroup.subset_closure (conj_mem_kleinGens hg)
  · rw [kleinOf, Subgroup.closure_le]
    intro g hg
    refine ⟨m⁻¹ * g * m, Subgroup.subset_closure ?_, by simp [mul_assoc]⟩
    have h1 := conj_mem_kleinGens (m := m⁻¹) hg
    have e : ((m⁻¹ : Perm α) : α → α) '' ((m : α → α) '' Γ) = Γ := by
      ext x
      simp
    rw [e] at h1
    simpa using h1

omit [Fintype α] [DecidableEq α] in
theorem mem_normalizer_kleinOf {Γ : Set α} {m : Perm α} (hm : ∀ x, m x ∈ Γ ↔ x ∈ Γ) :
    m ∈ Subgroup.normalizer (kleinOf Γ : Set (Perm α)) := by
  have hΓ : (m : α → α) '' Γ = Γ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hm y).2 hy
    · intro hx
      exact ⟨m⁻¹ x, (hm _).1 (by simpa using hx), by simp⟩
  rw [Subgroup.mem_normalizer_iff]
  intro g
  have h1 := map_conj_kleinOf Γ m
  rw [hΓ] at h1
  constructor
  · intro hg
    rw [← h1]
    exact ⟨g, hg, rfl⟩
  · intro hg
    rw [← h1] at hg
    obtain ⟨g', hg', hgg'⟩ := hg
    have : g' = g := by
      have h2 : m * g' * m⁻¹ = m * g * m⁻¹ := hgg'
      exact mul_left_cancel (mul_right_cancel h2)
    rw [← this]
    exact hg'

omit [Fintype α] [DecidableEq α] in
theorem eq_of_eqOn_of_fix {Γ : Set α} {f g : Perm α} (hf : ∀ x, x ∉ Γ → f x = x)
    (hg : ∀ x, x ∉ Γ → g x = x) (h : ∀ x ∈ Γ, f x = g x) : f = g := by
  refine Equiv.ext fun x => ?_
  by_cases hx : x ∈ Γ
  · exact h x hx
  · rw [hf x hx, hg x hx]

omit [Fintype α] in
theorem swap_mul_swap_mem_kleinGens {a b c d : α} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    swap a b * swap c d ∈ kleinGens ({a, b, c, d} : Set α) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, ?_⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hx.2.2.1 hx.2.2.2,
      swap_apply_of_ne_of_ne hx.1 hx.2.1]
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · rw [Perm.mul_apply, swap_apply_of_ne_of_ne hac had, swap_apply_left]
      exact hab.symm
    · rw [Perm.mul_apply, swap_apply_of_ne_of_ne hbc hbd, swap_apply_right]
      exact hab
    · rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne had.symm hbd.symm]
      exact hcd.symm
    · rw [Perm.mul_apply, swap_apply_right, swap_apply_of_ne_of_ne hac.symm hbc.symm]
      exact hcd
  · have hc : Commute (swap a b) (swap c d) := by
      refine Equiv.Perm.Disjoint.commute ?_
      intro x
      by_cases hx : x = a ∨ x = b
      · right
        rcases hx with rfl | rfl
        · exact swap_apply_of_ne_of_ne hac had
        · exact swap_apply_of_ne_of_ne hbc hbd
      · left
        push Not at hx
        exact swap_apply_of_ne_of_ne hx.1 hx.2
    calc swap a b * swap c d * (swap a b * swap c d)
        = swap a b * (swap c d * swap a b) * swap c d := by group
      _ = swap a b * (swap a b * swap c d) * swap c d := by rw [hc.eq]
      _ = 1 := by
        rw [← mul_assoc, swap_mul_self, one_mul, swap_mul_self]

omit [Fintype α] in
theorem swap_mul_swap_apply {p q r s : α} (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) :
    (swap p q * swap r s) p = q ∧ (swap p q * swap r s) q = p ∧
      (swap p q * swap r s) r = s ∧ (swap p q * swap r s) s = r := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne hpr hps, swap_apply_left]
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne hqr hqs, swap_apply_right]
  · rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hps.symm hqs.symm]
  · rw [Perm.mul_apply, swap_apply_right, swap_apply_of_ne_of_ne hpr.symm hqr.symm]

omit [Fintype α] in
theorem mem_kleinGens_quad {a b c d : α} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) {g : Perm α}
    (hg : g ∈ kleinGens ({a, b, c, d} : Set α)) :
    g = swap a b * swap c d ∨ g = swap a c * swap b d ∨ g = swap a d * swap b c := by
  obtain ⟨h1, h2, h3⟩ := hg
  have hgg : ∀ x, g (g x) = x := fun x => by
    have := congrArg (fun p : Perm α => p x) h3
    simpa using this
  have hmem : ∀ x ∈ ({a, b, c, d} : Set α), g x ∈ ({a, b, c, d} : Set α) := by
    intro x hx
    by_contra hgx
    have := h1 _ hgx
    rw [hgg] at this
    exact h2 x hx this.symm
  have hcases : ∀ x ∈ ({a, b, c, d} : Set α), x = a ∨ x = b ∨ x = c ∨ x = d := by
    intro x hx
    simpa using hx
  have ha : a ∈ ({a, b, c, d} : Set α) := by simp
  have hb : b ∈ ({a, b, c, d} : Set α) := by simp
  have hc : c ∈ ({a, b, c, d} : Set α) := by simp
  have hd : d ∈ ({a, b, c, d} : Set α) := by simp
  have hinj : ∀ x y, g x = g y → x = y := fun x y h => g.injective h
  have key : ∀ f : Perm α, (∀ x, x ∉ ({a, b, c, d} : Set α) → f x = x) →
      g a = f a → g b = f b → g c = f c → g d = f d → g = f := by
    intro f hf ea eb ec ed
    refine eq_of_eqOn_of_fix h1 hf fun x hx => ?_
    rcases hcases x hx with h | h | h | h <;> rw [h]
    exacts [ea, eb, ec, ed]
  have hset2 : ({a, c, b, d} : Set α) = {a, b, c, d} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hset3 : ({a, d, b, c} : Set α) = {a, b, c, d} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hf1 := (swap_mul_swap_mem_kleinGens hab hac had hbc hbd hcd).1
  have hf2 := (swap_mul_swap_mem_kleinGens hac hab had hbc.symm hcd hbd).1
  have hf3 := (swap_mul_swap_mem_kleinGens had hab hac hbd.symm hcd.symm hbc).1
  rw [hset2] at hf2
  rw [hset3] at hf3
  obtain ⟨p1, p2, p3, p4⟩ := swap_mul_swap_apply hac had hbc hbd
  obtain ⟨q1, q2, q3, q4⟩ := swap_mul_swap_apply hab had hbc.symm hcd
  obtain ⟨r1, r2, r3, r4⟩ := swap_mul_swap_apply hab hac hbd.symm hcd.symm
  rcases hcases _ (hmem a ha) with hga | hga | hga | hga
  · exact absurd hga (h2 a ha)
  · have hgb : g b = a := by rw [← hga, hgg]
    have hgc : g c = d := by
      rcases hcases _ (hmem c hc) with h | h | h | h
      · exact absurd (hinj c b (h.trans hgb.symm)) hbc.symm
      · exact absurd (hinj c a (h.trans hga.symm)) hac.symm
      · exact absurd h (h2 c hc)
      · exact h
    have hgd : g d = c := by rw [← hgc, hgg]
    exact Or.inl (key _ hf1 (hga.trans p1.symm) (hgb.trans p2.symm) (hgc.trans p3.symm)
      (hgd.trans p4.symm))
  · have hgc : g c = a := by rw [← hga, hgg]
    have hgb : g b = d := by
      rcases hcases _ (hmem b hb) with h | h | h | h
      · exact absurd (hinj b c (h.trans hgc.symm)) hbc
      · exact absurd h (h2 b hb)
      · exact absurd (hinj b a (h.trans hga.symm)) hab.symm
      · exact h
    have hgd : g d = b := by rw [← hgb, hgg]
    exact Or.inr (Or.inl (key _ hf2 (hga.trans q1.symm) (hgb.trans q3.symm)
      (hgc.trans q2.symm) (hgd.trans q4.symm)))
  · have hgd : g d = a := by rw [← hga, hgg]
    have hgb : g b = c := by
      rcases hcases _ (hmem b hb) with h | h | h | h
      · exact absurd (hinj b d (h.trans hgd.symm)) hbd
      · exact absurd h (h2 b hb)
      · exact h
      · exact absurd (hinj b a (h.trans hga.symm)) hab.symm
    have hgc : g c = b := by rw [← hgb, hgg]
    exact Or.inr (Or.inr (key _ hf3 (hga.trans r1.symm) (hgb.trans r3.symm)
      (hgc.trans r4.symm) (hgd.trans r2.symm)))

omit [Fintype α] in
theorem commute_swap_mul_swap {a b c d : α} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Commute (swap a b * swap c d) (swap a c * swap b d) := by
  have hf1 := (swap_mul_swap_mem_kleinGens hab hac had hbc hbd hcd).1
  have hf2 := (swap_mul_swap_mem_kleinGens hac hab had hbc.symm hcd hbd).1
  have hset : ({a, c, b, d} : Set α) = {a, b, c, d} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [hset] at hf2
  obtain ⟨p1, p2, p3, p4⟩ := swap_mul_swap_apply hac had hbc hbd
  obtain ⟨q1, q2, q3, q4⟩ := swap_mul_swap_apply hab had hbc.symm hcd
  have hfix : ∀ f g : Perm α, (∀ x, x ∉ ({a, b, c, d} : Set α) → f x = x) →
      (∀ x, x ∉ ({a, b, c, d} : Set α) → g x = x) →
      ∀ x, x ∉ ({a, b, c, d} : Set α) → (f * g) x = x := by
    intro f g hf hg x hx
    rw [Perm.mul_apply, hg x hx, hf x hx]
  refine eq_of_eqOn_of_fix (hfix _ _ hf1 hf2) (hfix _ _ hf2 hf1) fun x hx => ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> simp only [Perm.mul_apply] at * <;>
    simp only [p1, p2, p3, p4, q1, q2, q3, q4]

omit [Fintype α] in
theorem isPGroup_kleinOf_quad {a b c d : α} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    IsPGroup 2 (kleinOf ({a, b, c, d} : Set α)) := by
  set x := swap a b * swap c d
  set y := swap a c * swap b d
  set z := swap a d * swap b c
  have hxy := commute_swap_mul_swap hab hac had hbc hbd hcd
  have hxz : Commute x z := by
    have h := commute_swap_mul_swap hab had hac hbd hbc hcd.symm
    rwa [swap_comm d c] at h
  have hyz : Commute y z := by
    have h := commute_swap_mul_swap hac had hab hcd hbc.symm hbd.symm
    rwa [swap_comm d b, swap_comm c b] at h
  have hgen : ∀ g ∈ kleinGens ({a, b, c, d} : Set α), g = x ∨ g = y ∨ g = z :=
    fun g hg => mem_kleinGens_quad hab hac had hbc hbd hcd hg
  have hcomm : ∀ g ∈ kleinGens ({a, b, c, d} : Set α),
      ∀ h ∈ kleinGens ({a, b, c, d} : Set α), g * h = h * g := by
    intro g hg h hh
    rcases hgen g hg with rfl | rfl | rfl <;> rcases hgen h hh with rfl | rfl | rfl
    exacts [rfl, hxy.eq, hxz.eq, hxy.symm.eq, rfl, hyz.eq, hxz.symm.eq, hyz.symm.eq, rfl]
  have hcl : ∀ g ∈ kleinOf ({a, b, c, d} : Set α), ∀ h ∈ kleinOf ({a, b, c, d} : Set α),
      g * h = h * g := by
    intro g hg h hh
    have h1 : kleinOf ({a, b, c, d} : Set α) ≤
        Subgroup.centralizer (kleinGens ({a, b, c, d} : Set α)) :=
      (Subgroup.closure_le _).2 fun s hs =>
        _root_.Subgroup.mem_centralizer_iff.2 fun t ht => hcomm t ht s hs
    have h2 : kleinOf ({a, b, c, d} : Set α) ≤ Subgroup.centralizer {h} :=
      (Subgroup.closure_le _).2 fun s hs => _root_.Subgroup.mem_centralizer_iff.2 fun t ht => by
        rw [Set.mem_singleton_iff] at ht
        rw [ht]
        exact (_root_.Subgroup.mem_centralizer_iff.1 (h1 hh) s hs).symm
    have h3 := _root_.Subgroup.mem_centralizer_iff.1 (h2 hg) h (Set.mem_singleton h)
    exact h3.symm
  have hsq : ∀ g ∈ kleinOf ({a, b, c, d} : Set α), g * g = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg => exact hg.2.2
    | one => exact mul_one 1
    | mul g h hg hh ihg ihh =>
      have hgh : g * h = h * g := hcl g hg h hh
      calc g * h * (g * h) = g * (h * g) * h := by group
        _ = g * (g * h) * h := by rw [hgh]
        _ = 1 := by rw [← mul_assoc, ihg, one_mul, ihh]
    | inv g _ ihg => rw [← mul_inv_rev, ihg, inv_one]
  intro g
  exact ⟨1, Subtype.ext (by rw [pow_one, pow_two]; exact hsq g g.2)⟩

omit [Fintype α] [DecidableEq α] in
theorem IsRadSig.kleinOf_le {P : Subgroup (Perm α)} (hrad : IsRadSig P) {Γ : Set α}
    (hΓ : IsPGroup 2 (kleinOf Γ))
    (hN : ∀ m ∈ Subgroup.normalizer (P : Set (Perm α)), ∀ x, m x ∈ Γ ↔ x ∈ Γ) :
    kleinOf Γ ≤ P :=
  hrad _ hΓ fun m hm => mem_normalizer_kleinOf (hN m hm)

end CFSG.Quasithin.SmithC27
