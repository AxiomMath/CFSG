module

public import CFSG.Quasithin.Background.G9StmtsModels

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open Matrix

namespace CFSG.Quasithin

namespace G11

namespace P3Ortho

@[expose] def pairVec (i j : Fin 8) : Fin 8 → ZMod 2 := Pi.single i 1 + Pi.single j 1

theorem sum_pairVec (i j : Fin 8) : ∑ m, pairVec i j m = 0 := by
  simp only [pairVec, Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single']
  simp only [Finset.mem_univ, ite_true]
  decide

theorem pairVec_mem (i j : Fin 8) : pairVec i j ∈ permCore 8 := sum_pairVec i j

theorem pairVec_self (i : Fin 8) : pairVec i i = 0 := by
  funext m
  simp only [pairVec, Pi.add_apply, Pi.zero_apply, Pi.single_apply]
  split_ifs <;> decide

theorem pairVec_add (i j k : Fin 8) : pairVec i j + pairVec j k = pairVec i k := by
  funext m
  simp only [pairVec, Pi.add_apply, Pi.single_apply]
  split_ifs <;> rfl

theorem permAct_single (σ : Equiv.Perm (Fin 8)) (i : Fin 8) :
    permAct σ (Pi.single i (1 : ZMod 2)) = Pi.single (σ i) 1 := by
  funext m
  simp only [permAct, Pi.single_apply]
  by_cases h : m = σ i
  · subst h
    simp
  · have h' : ¬ σ.symm m = i := fun h' => h (by rw [← h']; simp)
    simp [h, h']

theorem permAct_pairVec (σ : Equiv.Perm (Fin 8)) (i j : Fin 8) :
    permAct σ (pairVec i j) = pairVec (σ i) (σ j) := by
  simp only [pairVec, ← permAct_single]
  rfl

theorem permAct_mem (σ : Equiv.Perm (Fin 8)) {x : Fin 8 → ZMod 2} (hx : x ∈ permCore 8) :
    permAct σ x ∈ permCore 8 := by
  have h : ∑ i, x i = 0 := hx
  show ∑ i, permAct σ x i = 0
  simp only [permAct]
  rw [Equiv.sum_comp σ⁻¹ x]
  exact h

theorem ones_dot {y : Fin 8 → ZMod 2} (hy : y ∈ permCore 8) :
    (fun _ : Fin 8 => (1 : ZMod 2)) ⬝ᵥ y = 0 := by
  have h : ∑ i, y i = 0 := hy
  simp [dotProduct, h]

theorem dot_pairVec (x : Fin 8 → ZMod 2) (i j : Fin 8) : x ⬝ᵥ pairVec i j = x i + x j := by
  simp [pairVec, dotProduct_add, dotProduct_single]

theorem dot_pairVec_pairVec (a b : Fin 8) (ha : a ≠ 0) (hb : b ≠ 0) :
    pairVec 0 a ⬝ᵥ pairVec 0 b = if a = b then 0 else 1 := by
  revert a b
  decide

theorem dot_of_zero_or_ones {z : ↥(permCore 8)}
    (hz : z = 0 ∨ ∀ i, (z : Fin 8 → ZMod 2) i = 1) (w : ↥(permCore 8)) :
    (z : Fin 8 → ZMod 2) ⬝ᵥ (w : Fin 8 → ZMod 2) = 0 := by
  rcases hz with rfl | h
  · simp
  · have : (z : Fin 8 → ZMod 2) = fun _ => 1 := funext h
    rw [this]
    exact ones_dot w.2

theorem exists_alt_three {a b c a' b' c' : Fin 8} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hab' : a' ≠ b') (hac' : a' ≠ c') (hbc' : b' ≠ c') :
    ∃ σ : Equiv.Perm (Fin 8), σ ∈ alternatingGroup (Fin 8) ∧ σ a = a' ∧ σ b = b' ∧ σ c = c' := by
  have h6 : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 8)) (Fin 8) 6 := by
    simpa using alternatingGroup.isMultiplyPretransitive (Fin 8)
  have h3 : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 8)) (Fin 8) 3 :=
    MulAction.isMultiplyPretransitive_of_le (n := 6) (by norm_num) (by simp)
  let f : Fin 3 ↪ Fin 8 :=
    ⟨![a, b, c], by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all⟩
  let g : Fin 3 ↪ Fin 8 :=
    ⟨![a', b', c'], by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all⟩
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 8)) f g
  have hk : ∀ i, (σ : Equiv.Perm (Fin 8)) (f i) = g i := fun i => by
    have := congrArg (fun e : Fin 3 ↪ Fin 8 => e i) hσ
    simpa [Function.Embedding.smul_apply, Subgroup.smul_def, Equiv.Perm.smul_def] using this
  exact ⟨σ, σ.2, hk 0, hk 1, hk 2⟩

theorem exists_alt_two {a b a' b' : Fin 8} (hab : a ≠ b) (hab' : a' ≠ b') :
    ∃ σ : Equiv.Perm (Fin 8), σ ∈ alternatingGroup (Fin 8) ∧ σ a = a' ∧ σ b = b' := by
  have hex : ∀ a b : Fin 8, a ≠ b → ∃ c : Fin 8, a ≠ c ∧ b ≠ c := by decide
  obtain ⟨c, hac, hbc⟩ := hex a b hab
  obtain ⟨c', hac', hbc'⟩ := hex a' b' hab'
  obtain ⟨σ, hσ, h1, h2, -⟩ := exists_alt_three hab hac hbc hab' hac' hbc'
  exact ⟨σ, hσ, h1, h2⟩

structure Data (U : Type) [AddCommGroup U] [Module (ZMod 2) U] (H' : Subgroup (GLV U)) where
  φ : ↥H' ≃* ↥(alternatingGroup (Fin 8))
  β : ↥(permCore 8) →ₗ[ZMod 2] U
  surj : Function.Surjective β
  ker : ∀ u : ↥(permCore 8), β u = 0 ↔
    (u = 0 ∨ (Even 8 ∧ ∀ i, (u : Fin 8 → ZMod 2) i = 1))
  equ : ∀ (γ : ↥H') (u u' : ↥(permCore 8)), (u' : Fin 8 → ZMod 2) =
    permAct ((φ γ : ↥(alternatingGroup (Fin 8))) : Equiv.Perm (Fin 8)) (u : Fin 8 → ZMod 2) →
      β u' = (γ : GLV U) (β u)

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U] {H' : Subgroup (GLV U)}

theorem Data.of_isPermCoreModule (h : IsPermCoreModule H' (alternatingGroup (Fin 8))) :
    Nonempty (Data U H') := by
  obtain ⟨φ, β, hs, hk, he⟩ := h
  exact ⟨⟨φ, β, hs, hk, he⟩⟩

namespace Data

variable (D : Data U H')

@[expose] noncomputable def sec : U →ₗ[ZMod 2] ↥(permCore 8) :=
  (LinearMap.exists_rightInverse_of_surjective D.β (LinearMap.range_eq_top.2 D.surj)).choose

theorem β_sec (u : U) : D.β (D.sec u) = u := by
  have h := (LinearMap.exists_rightInverse_of_surjective D.β
    (LinearMap.range_eq_top.2 D.surj)).choose_spec
  exact LinearMap.congr_fun h u

@[expose] noncomputable def B0 : LinearMap.BilinForm (ZMod 2) U :=
  LinearMap.mk₂ (ZMod 2)
    (fun u v => (D.sec u : Fin 8 → ZMod 2) ⬝ᵥ (D.sec v : Fin 8 → ZMod 2))
    (by intro u u' v; simp [add_dotProduct])
    (by intro c u v; simp [smul_dotProduct])
    (by intro u v v'; simp [dotProduct_add])
    (by intro c u v; simp [dotProduct_smul])

theorem B0_apply (u v : U) :
    D.B0 u v = (D.sec u : Fin 8 → ZMod 2) ⬝ᵥ (D.sec v : Fin 8 → ZMod 2) := rfl

theorem add_self_permCore (x : ↥(permCore 8)) : x + x = 0 := by
  apply Subtype.ext
  funext i
  have : ∀ a : ZMod 2, a + a = 0 := by decide
  exact this _

theorem sec_β (x : ↥(permCore 8)) :
    ∃ z : ↥(permCore 8), (z = 0 ∨ ∀ i, (z : Fin 8 → ZMod 2) i = 1) ∧ D.sec (D.β x) = x + z := by
  have hu : ∀ u : U, u + u = 0 := fun u => by
    have h2 : (2 : ZMod 2) = 0 := by decide
    rw [← two_smul (ZMod 2) u, h2, zero_smul]
  refine ⟨D.sec (D.β x) + x, ?_, ?_⟩
  · have h : D.β (D.sec (D.β x) + x) = 0 := by rw [map_add, D.β_sec]; exact hu _
    rcases (D.ker _).1 h with h0 | ⟨-, h1⟩
    · exact Or.inl h0
    · exact Or.inr h1
  · rw [add_comm (D.sec (D.β x)) x, ← add_assoc, add_self_permCore, zero_add]

theorem B0_β (x y : ↥(permCore 8)) :
    D.B0 (D.β x) (D.β y) = (x : Fin 8 → ZMod 2) ⬝ᵥ (y : Fin 8 → ZMod 2) := by
  obtain ⟨z, hz, hx⟩ := D.sec_β x
  obtain ⟨z', hz', hy⟩ := D.sec_β y
  rw [B0_apply, hx, hy]
  simp only [Submodule.coe_add, add_dotProduct, dotProduct_add]
  have h1 := dot_of_zero_or_ones hz y
  have h2 := dot_of_zero_or_ones hz z'
  have h3 := dot_of_zero_or_ones hz' x
  rw [dotProduct_comm] at h3
  rw [h1, h2, h3]
  simp

theorem B0_symm (u v : U) : D.B0 u v = D.B0 v u := by
  rw [B0_apply, B0_apply, dotProduct_comm]

theorem B0_alt (u : U) : D.B0 u u = 0 := by
  obtain ⟨x, rfl⟩ := D.surj u
  rw [B0_β]
  have hsq : ∀ a : ZMod 2, a * a = a := by decide
  have hx : ∑ i, (x : Fin 8 → ZMod 2) i = 0 := x.2
  simp only [dotProduct, hsq]
  exact hx

theorem B0_left_sep (u : U) (h : ∀ v, D.B0 u v = 0) : u = 0 := by
  obtain ⟨x, rfl⟩ := D.surj u
  have hm : ∀ m : Fin 8, (x : Fin 8 → ZMod 2) m = (x : Fin 8 → ZMod 2) 0 := by
    intro m
    have h1 := h (D.β ⟨pairVec 0 m, pairVec_mem 0 m⟩)
    rw [B0_β] at h1
    simp only [dot_pairVec] at h1
    have : ∀ a b : ZMod 2, a + b = 0 → b = a := by decide
    exact this _ _ h1
  apply (D.ker x).2
  by_cases h0 : (x : Fin 8 → ZMod 2) 0 = 0
  · left
    apply Subtype.ext
    funext m
    rw [hm m]
    exact h0
  · right
    refine ⟨by decide, fun i => ?_⟩
    rw [hm i]
    have : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
    exact this _ h0

theorem apply_β (γ : ↥H') (x : ↥(permCore 8)) :
    (γ : GLV U) (D.β x) = D.β ⟨permAct ((D.φ γ : ↥(alternatingGroup (Fin 8))) :
      Equiv.Perm (Fin 8)) x, permAct_mem _ x.2⟩ := (D.equ γ x _ rfl).symm

@[expose] noncomputable def w (i j : Fin 8) : U := D.β ⟨pairVec i j, pairVec_mem i j⟩

theorem w_self (i : Fin 8) : D.w i i = 0 := by
  unfold w
  have : (⟨pairVec i i, pairVec_mem i i⟩ : ↥(permCore 8)) = 0 := Subtype.ext (pairVec_self i)
  rw [this, map_zero]

theorem w_add (i j k : Fin 8) : D.w i j + D.w j k = D.w i k := by
  unfold w
  rw [← map_add]
  have : (⟨pairVec i j, pairVec_mem i j⟩ + ⟨pairVec j k, pairVec_mem j k⟩ : ↥(permCore 8)) =
      ⟨pairVec i k, pairVec_mem i k⟩ := Subtype.ext (pairVec_add i j k)
  rw [this]

theorem B0_w (a b : Fin 8) (ha : a ≠ 0) (hb : b ≠ 0) :
    D.B0 (D.w 0 a) (D.w 0 b) = if a = b then 0 else 1 := by
  unfold w
  rw [B0_β]
  exact dot_pairVec_pairVec a b ha hb

theorem w_ne_zero : D.w 0 1 ≠ 0 := by
  intro h
  have h1 := D.B0_w 1 2 (by decide) (by decide)
  rw [h, map_zero] at h1
  simp at h1

theorem w_inv (σ : Equiv.Perm (Fin 8)) (hσ : σ ∈ alternatingGroup (Fin 8)) :
    ∃ γ : ↥H', ∀ i j, (γ : GLV U) (D.w i j) = D.w (σ i) (σ j) := by
  refine ⟨D.φ.symm ⟨σ, hσ⟩, fun i j => ?_⟩
  unfold w
  rw [apply_β]
  have : (⟨permAct ((D.φ (D.φ.symm ⟨σ, hσ⟩) : ↥(alternatingGroup (Fin 8))) :
      Equiv.Perm (Fin 8)) (pairVec i j), permAct_mem _ (pairVec_mem i j)⟩ : ↥(permCore 8)) =
      ⟨pairVec (σ i) (σ j), pairVec_mem _ _⟩ := by
    apply Subtype.ext
    simp only [MulEquiv.apply_symm_apply]
    exact permAct_pairVec σ i j
  rw [this]

theorem span_w : Submodule.span (ZMod 2) (Set.range fun a : Fin 8 => D.w 0 a) = ⊤ := by
  rw [eq_top_iff]
  rintro u -
  obtain ⟨x, rfl⟩ := D.surj u
  have hx : x = ∑ a : Fin 8, (x : Fin 8 → ZMod 2) a •
      (⟨pairVec 0 a, pairVec_mem 0 a⟩ : ↥(permCore 8)) := by
    apply Subtype.ext
    funext m
    have hsum : ∑ i, (x : Fin 8 → ZMod 2) i = 0 := x.2
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, pairVec,
      Pi.add_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib, Pi.single_apply]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
    by_cases hm : m = 0
    · simp [hm, hsum]
    · simp [hm]
  rw [hx, map_sum]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem eq_smul_B0 (B : LinearMap.BilinForm (ZMod 2) U) (hB0 : ∀ u, B u u = 0)
    (hB : ∀ γ : ↥H', ∀ u v, B ((γ : GLV U) u) ((γ : GLV U) v) = B u v) :
    ∃ c : ZMod 2, B = c • D.B0 := by
  have key : ∀ a b c a' b' c' : Fin 8, a ≠ b → a ≠ c → b ≠ c → a' ≠ b' → a' ≠ c' → b' ≠ c' →
      B (D.w a b) (D.w a c) = B (D.w a' b') (D.w a' c') := by
    intro a b c a' b' c' hab hac hbc hab' hac' hbc'
    obtain ⟨σ, hσ, h1, h2, h3⟩ := exists_alt_three hab hac hbc hab' hac' hbc'
    obtain ⟨γ, hγ⟩ := D.w_inv σ hσ
    rw [← hB γ, hγ, hγ, h1, h2, h3]
  set c : ZMod 2 := B (D.w 0 1) (D.w 0 2) with hc
  have hdist : ∀ a b : Fin 8, a ≠ 0 → b ≠ 0 → a ≠ b → B (D.w 0 a) (D.w 0 b) = c := by
    intro a b ha hb hab
    exact key 0 a b 0 1 2 (Ne.symm ha) (Ne.symm hb) hab (by decide) (by decide) (by decide)
  refine ⟨c, ?_⟩
  apply LinearMap.ext_on D.span_w
  intro x hx
  obtain ⟨a, rfl⟩ := hx
  apply LinearMap.ext_on D.span_w
  intro y hy
  obtain ⟨b, rfl⟩ := hy
  simp only [LinearMap.smul_apply, smul_eq_mul]
  by_cases ha : a = 0
  · subst ha
    rw [D.w_self]
    simp
  by_cases hb : b = 0
  · subst hb
    rw [D.w_self]
    simp
  rw [D.B0_w a b ha hb]
  by_cases hab : a = b
  · subst hab
    simp [hB0]
  · simp [hab, hdist a b ha hb hab]

end Data

end P3Ortho

end G11

end CFSG.Quasithin
