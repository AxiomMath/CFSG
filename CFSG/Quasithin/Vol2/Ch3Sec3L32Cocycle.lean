module

public import CFSG.Quasithin.Background.B4L3Fin
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.H13

open CFSG.Assembly.LowTwoRank

namespace L32Coc

open CFSG.Quasithin.L3

@[expose] def aL : Γ := ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩

@[expose] def bL : Γ := ⟨!![0, 0, 1; 0, 1, 1; 1, 0, 1], by decide⟩

@[expose] def step (da db : Vec) (s : Γ × Vec) (l : Bool) : Γ × Vec :=
  (s.1 * (if l then bL else aL), s.2 + act s.1 (if l then db else da))

@[expose] def wordVal (da db : Vec) (w : List Bool) : Γ × Vec := w.foldl (step da db) (1, 0)

@[expose] def r₁ : List Bool := [true, true, true]

@[expose] def r₂ : List Bool := (List.replicate 7 [false, true]).flatten

@[expose] def r₃ : List Bool := (List.replicate 4 [false, true, false, true, true]).flatten

theorem aL_invol : IsInvol aL := by decide +kernel

theorem rels_one : (wordVal 0 0 r₁).1 = 1 ∧ (wordVal 0 0 r₂).1 = 1 ∧ (wordVal 0 0 r₃).1 = 1 := by
  decide +kernel

theorem relCheck : ∀ x : Vec, (wordVal 0 x r₁).2 = 0 → (wordVal 0 x r₂).2 = 0 →
    (wordVal 0 x r₃).2 = 0 → ∃ v : Vec, act aL v = v ∧ x = v - act bL v := by
  decide +kernel

theorem fst_wordVal (da db da' db' : Vec) (w : List Bool) :
    (wordVal da db w).1 = (wordVal da' db' w).1 := by
  unfold wordVal
  suffices h : ∀ s s' : Γ × Vec, s.1 = s'.1 →
      (w.foldl (step da db) s).1 = (w.foldl (step da' db') s').1 from h _ _ rfl
  induction w with
  | nil => intro s s' h; exact h
  | cons l w ih =>
    intro s s' h
    simp only [List.foldl_cons]
    exact ih _ _ (by simp only [step, h])

variable {δ : Γ → Vec} (hδ : ∀ g h, δ (g * h) = δ g + act g (δ h))

include hδ in
theorem cocycle_one : δ 1 = 0 := by
  have h := hδ 1 1
  rw [one_mul, act_one] at h
  have : δ 1 + δ 1 = δ 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel this

include hδ in
theorem snd_wordVal (w : List Bool) :
    (wordVal (δ aL) (δ bL) w).2 = δ (wordVal (δ aL) (δ bL) w).1 := by
  unfold wordVal
  suffices h : ∀ s : Γ × Vec, s.2 = δ s.1 →
      (w.foldl (step (δ aL) (δ bL)) s).2 = δ (w.foldl (step (δ aL) (δ bL)) s).1 from
    h _ (cocycle_one hδ).symm
  induction w with
  | nil => intro s h; exact h
  | cons l w ih =>
    intro s h
    simp only [List.foldl_cons]
    refine ih _ ?_
    simp only [step]
    rw [hδ, h]
    cases l <;> rfl

theorem fst_wordVal_mem (da db : Vec) (w : List Bool) :
    (wordVal da db w).1 ∈ Subgroup.closure ({aL, bL} : Set Γ) := by
  unfold wordVal
  suffices h : ∀ s : Γ × Vec, s.1 ∈ Subgroup.closure ({aL, bL} : Set Γ) →
      (w.foldl (step da db) s).1 ∈ Subgroup.closure ({aL, bL} : Set Γ) from
    h _ (Subgroup.one_mem _)
  induction w with
  | nil => intro s h; exact h
  | cons l w ih =>
    intro s h
    simp only [List.foldl_cons]
    refine ih _ ?_
    simp only [step]
    refine Subgroup.mul_mem _ h (Subgroup.subset_closure ?_)
    cases l <;> simp

@[expose] def transWords : List (List Bool) :=
  [[false], [true, true, false, true, false, true, true, false, true],
    [false, true, true, false, true, true, false, true, false, true, false],
    [false, true, false, true, false, true, false, true, true, false, true, false, true],
    [false, true, false, true, true, false], [false, true, false, true, true, false, true, false,
      true, true]]

theorem transvection_words : ∀ (i j : Fin 3) (hij : i ≠ j), ∃ w ∈ transWords,
    (wordVal 0 0 w).1 = Matrix.SpecialLinearGroup.transvection hij (1 : ZMod 2) := by
  decide +kernel

theorem closure_tb : Subgroup.closure ({aL, bL} : Set Γ) = ⊤ := by
  have hall : ∀ (i j : Fin 3) (hij : i ≠ j) (c : ZMod 2),
      Matrix.SpecialLinearGroup.transvection hij c ∈ Subgroup.closure ({aL, bL} : Set Γ) := by
    intro i j hij c
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · rw [Matrix.SpecialLinearGroup.transvection_coeff_zero]
      exact Subgroup.one_mem _
    · obtain ⟨w, -, hw⟩ := transvection_words i j hij
      rw [← hw]
      exact fst_wordVal_mem 0 0 w
  rw [eq_top_iff,
    ← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
      (ι := Fin 3) (K := ZMod 2), Subgroup.closure_le]
  rintro _ ⟨t, rfl⟩
  exact hall t.i t.j t.hij t.c

include hδ in
theorem inner_of_t12 (h0 : δ aL = 0) : ∃ v : Vec, ∀ g, δ g = v - act g v := by
  obtain ⟨hr₁, hr₂, hr₃⟩ := rels_one
  have hrel : ∀ r : List Bool, (wordVal 0 0 r).1 = 1 → (wordVal 0 (δ bL) r).2 = 0 := by
    intro r hr
    have h1 := snd_wordVal hδ r
    rw [h0] at h1
    rw [h1, fst_wordVal 0 (δ bL) 0 0, hr]
    exact cocycle_one hδ
  obtain ⟨v, hv, hb⟩ := relCheck (δ bL) (hrel _ hr₁) (hrel _ hr₂) (hrel _ hr₃)
  refine ⟨v, fun g => ?_⟩
  let H : Subgroup Γ :=
    { carrier := {g | δ g = v - act g v}
      one_mem' := by
        show δ 1 = v - act 1 v
        rw [cocycle_one hδ, act_one, sub_self]
      mul_mem' := by
        intro x y hx hy
        show δ (x * y) = v - act (x * y) v
        rw [hδ, hx, hy]
        simp only [act_sub, act_mul]
        abel
      inv_mem' := by
        intro x hx
        show δ x⁻¹ = v - act x⁻¹ v
        have h1 := hδ x⁻¹ x
        rw [inv_mul_cancel, cocycle_one hδ, hx, act_sub, act_inv_act] at h1
        have h2 : δ x⁻¹ = -(act x⁻¹ v - v) := eq_neg_of_add_eq_zero_left h1.symm
        rw [h2]
        abel }
  have hle : Subgroup.closure ({aL, bL} : Set Γ) ≤ H := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · show δ aL = v - act aL v
      rw [h0, hv, sub_self]
    · exact hb
  rw [closure_tb] at hle
  exact hle (Subgroup.mem_top g)

include hδ in
theorem inner_of_invol {a : Γ} (ha : IsInvol a) (h0 : δ a = 0) :
    ∃ v : Vec, ∀ g, δ g = v - act g v := by
  obtain ⟨x, hx⟩ := conj_invol aL_invol ha
  have hδ'c : ∀ g h, act x⁻¹ (δ (x * (g * h) * x⁻¹)) =
      act x⁻¹ (δ (x * g * x⁻¹)) + act g (act x⁻¹ (δ (x * h * x⁻¹))) := by
    intro g h
    have e : x * (g * h) * x⁻¹ = (x * g * x⁻¹) * (x * h * x⁻¹) := by group
    rw [e, hδ, act_add, ← act_mul, ← act_mul]
    have e' : x⁻¹ * (x * g * x⁻¹) = g * x⁻¹ := by group
    rw [e']
  have h0' : act x⁻¹ (δ (x * aL * x⁻¹)) = 0 := by
    rw [hx, h0]
    exact act_zero x⁻¹
  obtain ⟨v, hv⟩ := inner_of_t12 (δ := fun g => act x⁻¹ (δ (x * g * x⁻¹))) hδ'c h0'
  refine ⟨act x v, fun g => ?_⟩
  have h1 : act x⁻¹ (δ (x * (x⁻¹ * g * x) * x⁻¹)) = v - act (x⁻¹ * g * x) v :=
    hv (x⁻¹ * g * x)
  have e : x * (x⁻¹ * g * x) * x⁻¹ = g := by group
  rw [e] at h1
  have h2 := congrArg (act x) h1
  rw [act_act_inv, act_sub, ← act_mul] at h2
  rw [h2]
  have e' : x * (x⁻¹ * g * x) = g * x := by group
  rw [e', act_mul]

end L32Coc

open L32Coc in
theorem factL32Cocycle_holds :
    ∀ δ : ↥(StatedSL 3 (ZMod 2)) → (Fin 3 → ZMod 2),
      (∀ g h, δ (g * h) = δ g +
        ((g : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (δ h)) →
      ∀ a, a ≠ 1 → a ^ 2 = 1 → δ a = 0 →
        ∃ v : Fin 3 → ZMod 2, ∀ g,
          δ g = v - ((g : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v := by
  intro δ hδ a ha1 ha2 h0
  set e := specialLinearGroupEquivStatedSL 3 (ZMod 2) with he
  set δ₀ : L3.Γ → L3.Vec := fun g => δ (e g) with hδ₀
  have hc : ∀ g h, δ₀ (g * h) = δ₀ g + L3.act g (δ₀ h) := by
    intro g h
    simp only [hδ₀, map_mul, hδ]
    rfl
  have hinv : L3.IsInvol (e.symm a) := by
    refine ⟨?_, ?_⟩
    · rw [← map_mul, ← pow_two, ha2, map_one]
    · intro h1
      apply ha1
      have := congrArg e h1
      rwa [MulEquiv.apply_symm_apply, map_one] at this
  have h0' : δ₀ (e.symm a) = 0 := by
    simp only [hδ₀, MulEquiv.apply_symm_apply]
    exact h0
  obtain ⟨v, hv⟩ := inner_of_invol hc hinv h0'
  refine ⟨v, fun g => ?_⟩
  have := hv (e.symm g)
  simp only [hδ₀, MulEquiv.apply_symm_apply] at this
  rw [this]
  have hg : ((g : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      ((e.symm g : L3.Γ) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
    conv_lhs => rw [← e.apply_symm_apply g]
    exact specialLinearGroupEquivStatedSL_coe 3 (ZMod 2) (e.symm g)
  rw [hg]
  rfl

end CFSG.Quasithin.H13
