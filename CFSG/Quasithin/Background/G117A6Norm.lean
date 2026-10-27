module

public import CFSG.Quasithin.Background.G117Inputs
public import CFSG.LocalAnalysis.ComponentInitial.BinaryOddQuadraticFiveOrthogonalGroup

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open Matrix

namespace CFSG.Quasithin

namespace G11

namespace G117

namespace A6Norm

def pairVec (i j : Fin 6) : Fin 6 → ZMod 2 := Pi.single i 1 + Pi.single j 1

theorem sum_pairVec (i j : Fin 6) : ∑ m, pairVec i j m = 0 := by
  simp only [pairVec, Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single']
  simp only [Finset.mem_univ, ite_true]
  decide

theorem pairVec_mem (i j : Fin 6) : pairVec i j ∈ permCore 6 := sum_pairVec i j

theorem pairVec_comm (i j : Fin 6) : pairVec i j = pairVec j i := add_comm _ _

theorem pairVec_self (i : Fin 6) : pairVec i i = 0 := by
  funext m
  simp only [pairVec, Pi.add_apply, Pi.zero_apply, Pi.single_apply]
  split_ifs <;> decide

theorem pairVec_add (i j k : Fin 6) : pairVec i j + pairVec j k = pairVec i k := by
  funext m
  simp only [pairVec, Pi.add_apply, Pi.single_apply]
  split_ifs <;> rfl

theorem permAct_single (σ : Equiv.Perm (Fin 6)) (i : Fin 6) :
    permAct σ (Pi.single i (1 : ZMod 2)) = Pi.single (σ i) 1 := by
  funext m
  simp only [permAct, Pi.single_apply]
  by_cases h : m = σ i
  · subst h
    simp
  · have h' : ¬ σ.symm m = i := fun h' => h (by rw [← h']; simp)
    simp [h, h']

theorem permAct_pairVec (σ : Equiv.Perm (Fin 6)) (i j : Fin 6) :
    permAct σ (pairVec i j) = pairVec (σ i) (σ j) := by
  simp only [pairVec, ← permAct_single]
  rfl

theorem permAct_mem (σ : Equiv.Perm (Fin 6)) {x : Fin 6 → ZMod 2} (hx : x ∈ permCore 6) :
    permAct σ x ∈ permCore 6 := by
  have h : ∑ i, x i = 0 := hx
  show ∑ i, permAct σ x i = 0
  simp only [permAct]
  rw [Equiv.sum_comp σ⁻¹ x]
  exact h

theorem dot_permAct (σ : Equiv.Perm (Fin 6)) (x y : Fin 6 → ZMod 2) :
    permAct σ x ⬝ᵥ permAct σ y = x ⬝ᵥ y := by
  simp only [dotProduct, permAct]
  exact Equiv.sum_comp σ⁻¹ (fun m => x m * y m)

theorem ones_dot {y : Fin 6 → ZMod 2} (hy : y ∈ permCore 6) :
    (fun _ : Fin 6 => (1 : ZMod 2)) ⬝ᵥ y = 0 := by
  have h : ∑ i, y i = 0 := hy
  simp [dotProduct, h]

theorem dot_pairVec (x : Fin 6 → ZMod 2) (i j : Fin 6) : x ⬝ᵥ pairVec i j = x i + x j := by
  simp [pairVec, dotProduct_add, dotProduct_single]

theorem dot_pairVec_pairVec (a b : Fin 6) (ha : a ≠ 0) (hb : b ≠ 0) :
    pairVec 0 a ⬝ᵥ pairVec 0 b = if a = b then 0 else 1 := by
  revert a b
  decide


theorem dot_of_zero_or_ones {z : ↥(permCore 6)}
    (hz : z = 0 ∨ ∀ i, (z : Fin 6 → ZMod 2) i = 1) (w : ↥(permCore 6)) :
    (z : Fin 6 → ZMod 2) ⬝ᵥ (w : Fin 6 → ZMod 2) = 0 := by
  rcases hz with rfl | h
  · simp
  · have : (z : Fin 6 → ZMod 2) = fun _ => 1 := funext h
    rw [this]
    exact ones_dot w.2

theorem exists_alt_three {a b c a' b' c' : Fin 6} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hab' : a' ≠ b') (hac' : a' ≠ c') (hbc' : b' ≠ c') :
    ∃ σ : Equiv.Perm (Fin 6), σ ∈ alternatingGroup (Fin 6) ∧ σ a = a' ∧ σ b = b' ∧ σ c = c' := by
  have h4 : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 6)) (Fin 6) 4 := by
    simpa using alternatingGroup.isMultiplyPretransitive (Fin 6)
  have h3 : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 6)) (Fin 6) 3 :=
    MulAction.isMultiplyPretransitive_of_le (n := 4) (by norm_num) (by simp)
  let f : Fin 3 ↪ Fin 6 :=
    ⟨![a, b, c], by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all⟩
  let g : Fin 3 ↪ Fin 6 :=
    ⟨![a', b', c'], by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all⟩
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 6)) f g
  have hk : ∀ i, (σ : Equiv.Perm (Fin 6)) (f i) = g i := fun i => by
    have := congrArg (fun e : Fin 3 ↪ Fin 6 => e i) hσ
    simpa [Function.Embedding.smul_apply, Subgroup.smul_def, Equiv.Perm.smul_def] using this
  exact ⟨σ, σ.2, hk 0, hk 1, hk 2⟩

structure Data (U : Type) [AddCommGroup U] [Module (ZMod 2) U] (H' : Subgroup (GLV U)) where
  φ : ↥H' ≃* ↥(alternatingGroup (Fin 6))
  β : ↥(permCore 6) →ₗ[ZMod 2] U
  surj : Function.Surjective β
  ker : ∀ u : ↥(permCore 6), β u = 0 ↔
    (u = 0 ∨ (Even 6 ∧ ∀ i, (u : Fin 6 → ZMod 2) i = 1))
  equ : ∀ (γ : ↥H') (u u' : ↥(permCore 6)), (u' : Fin 6 → ZMod 2) =
    permAct ((φ γ : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6)) (u : Fin 6 → ZMod 2) →
      β u' = (γ : GLV U) (β u)

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U] {H' : Subgroup (GLV U)}

theorem Data.of_isPermCoreModule (h : IsPermCoreModule H' (alternatingGroup (Fin 6))) :
    Nonempty (Data U H') := by
  obtain ⟨φ, β, hs, hk, he⟩ := h
  exact ⟨⟨φ, β, hs, hk, he⟩⟩

namespace Data

variable (D : Data U H')

noncomputable def sec : U →ₗ[ZMod 2] ↥(permCore 6) :=
  (LinearMap.exists_rightInverse_of_surjective D.β (LinearMap.range_eq_top.2 D.surj)).choose

theorem β_sec (u : U) : D.β (D.sec u) = u := by
  have h := (LinearMap.exists_rightInverse_of_surjective D.β
    (LinearMap.range_eq_top.2 D.surj)).choose_spec
  exact LinearMap.congr_fun h u

@[expose] noncomputable def B0 : LinearMap.BilinForm (ZMod 2) U :=
  LinearMap.mk₂ (ZMod 2)
    (fun u v => (D.sec u : Fin 6 → ZMod 2) ⬝ᵥ (D.sec v : Fin 6 → ZMod 2))
    (by intro u u' v; simp [add_dotProduct])
    (by intro c u v; simp [smul_dotProduct])
    (by intro u v v'; simp [dotProduct_add])
    (by intro c u v; simp [dotProduct_smul])

theorem B0_apply (u v : U) :
    D.B0 u v = (D.sec u : Fin 6 → ZMod 2) ⬝ᵥ (D.sec v : Fin 6 → ZMod 2) := rfl

theorem add_self_permCore (x : ↥(permCore 6)) : x + x = 0 := by
  apply Subtype.ext
  funext i
  have : ∀ a : ZMod 2, a + a = 0 := by decide
  exact this _

theorem sec_β (x : ↥(permCore 6)) :
    ∃ z : ↥(permCore 6), (z = 0 ∨ ∀ i, (z : Fin 6 → ZMod 2) i = 1) ∧ D.sec (D.β x) = x + z := by
  have hu : ∀ u : U, u + u = 0 := fun u => by
    have h2 : (2 : ZMod 2) = 0 := by decide
    rw [← two_smul (ZMod 2) u, h2, zero_smul]
  refine ⟨D.sec (D.β x) + x, ?_, ?_⟩
  · have h : D.β (D.sec (D.β x) + x) = 0 := by rw [map_add, D.β_sec]; exact hu _
    rcases (D.ker _).1 h with h0 | ⟨-, h1⟩
    · exact Or.inl h0
    · exact Or.inr h1
  · rw [add_comm (D.sec (D.β x)) x, ← add_assoc, add_self_permCore, zero_add]

theorem B0_β (x y : ↥(permCore 6)) :
    D.B0 (D.β x) (D.β y) = (x : Fin 6 → ZMod 2) ⬝ᵥ (y : Fin 6 → ZMod 2) := by
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
  have hx : ∑ i, (x : Fin 6 → ZMod 2) i = 0 := x.2
  simp only [dotProduct, hsq]
  exact hx

theorem B0_left_sep (u : U) (h : ∀ v, D.B0 u v = 0) : u = 0 := by
  obtain ⟨x, rfl⟩ := D.surj u
  have hm : ∀ m : Fin 6, (x : Fin 6 → ZMod 2) m = (x : Fin 6 → ZMod 2) 0 := by
    intro m
    have h1 := h (D.β ⟨pairVec 0 m, pairVec_mem 0 m⟩)
    rw [B0_β] at h1
    simp only [dot_pairVec] at h1
    have : ∀ a b : ZMod 2, a + b = 0 → b = a := by decide
    exact this _ _ h1
  apply (D.ker x).2
  by_cases h0 : (x : Fin 6 → ZMod 2) 0 = 0
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

theorem B0_nondegenerate : D.B0.Nondegenerate :=
  ⟨fun u hu => D.B0_left_sep u hu, fun v hv => D.B0_left_sep v (fun u => by
    rw [B0_symm]
    exact hv u)⟩

theorem B0_isAlt : D.B0.IsAlt := fun u => D.B0_alt u

theorem apply_β (γ : ↥H') (x : ↥(permCore 6)) :
    (γ : GLV U) (D.β x) = D.β ⟨permAct ((D.φ γ : ↥(alternatingGroup (Fin 6))) :
      Equiv.Perm (Fin 6)) x, permAct_mem _ x.2⟩ := (D.equ γ x _ rfl).symm

theorem B0_inv (γ : ↥H') (u v : U) : D.B0 ((γ : GLV U) u) ((γ : GLV U) v) = D.B0 u v := by
  obtain ⟨x, rfl⟩ := D.surj u
  obtain ⟨y, rfl⟩ := D.surj v
  rw [apply_β, apply_β, B0_β, B0_β]
  exact dot_permAct _ _ _

noncomputable def w (i j : Fin 6) : U := D.β ⟨pairVec i j, pairVec_mem i j⟩

theorem w_comm (i j : Fin 6) : D.w i j = D.w j i := by
  unfold w
  have : (⟨pairVec i j, pairVec_mem i j⟩ : ↥(permCore 6)) = ⟨pairVec j i, pairVec_mem j i⟩ :=
    Subtype.ext (pairVec_comm i j)
  rw [this]

theorem w_self (i : Fin 6) : D.w i i = 0 := by
  unfold w
  have : (⟨pairVec i i, pairVec_mem i i⟩ : ↥(permCore 6)) = 0 := Subtype.ext (pairVec_self i)
  rw [this, map_zero]

theorem w_add (i j k : Fin 6) : D.w i j + D.w j k = D.w i k := by
  unfold w
  rw [← map_add]
  have : (⟨pairVec i j, pairVec_mem i j⟩ + ⟨pairVec j k, pairVec_mem j k⟩ : ↥(permCore 6)) =
      ⟨pairVec i k, pairVec_mem i k⟩ := Subtype.ext (pairVec_add i j k)
  rw [this]

theorem B0_w (a b : Fin 6) (ha : a ≠ 0) (hb : b ≠ 0) :
    D.B0 (D.w 0 a) (D.w 0 b) = if a = b then 0 else 1 := by
  unfold w
  rw [B0_β]
  exact dot_pairVec_pairVec a b ha hb

theorem w_ne_zero : D.w 0 1 ≠ 0 := by
  intro h
  have h1 := D.B0_w 1 2 (by decide) (by decide)
  rw [h, map_zero] at h1
  simp at h1

theorem w_inv (σ : Equiv.Perm (Fin 6)) (hσ : σ ∈ alternatingGroup (Fin 6)) :
    ∃ γ : ↥H', ∀ i j, (γ : GLV U) (D.w i j) = D.w (σ i) (σ j) := by
  refine ⟨D.φ.symm ⟨σ, hσ⟩, fun i j => ?_⟩
  unfold w
  rw [apply_β]
  have : (⟨permAct ((D.φ (D.φ.symm ⟨σ, hσ⟩) : ↥(alternatingGroup (Fin 6))) :
      Equiv.Perm (Fin 6)) (pairVec i j), permAct_mem _ (pairVec_mem i j)⟩ : ↥(permCore 6)) =
      ⟨pairVec (σ i) (σ j), pairVec_mem _ _⟩ := by
    apply Subtype.ext
    simp only [MulEquiv.apply_symm_apply]
    exact permAct_pairVec σ i j
  rw [this]

theorem span_w : Submodule.span (ZMod 2) (Set.range fun a : Fin 6 => D.w 0 a) = ⊤ := by
  rw [eq_top_iff]
  rintro u -
  obtain ⟨x, rfl⟩ := D.surj u
  have hx : x = ∑ a : Fin 6, (x : Fin 6 → ZMod 2) a •
      (⟨pairVec 0 a, pairVec_mem 0 a⟩ : ↥(permCore 6)) := by
    apply Subtype.ext
    funext m
    have hsum : ∑ i, (x : Fin 6 → ZMod 2) i = 0 := x.2
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


theorem eq_smul_B0 (B : LinearMap.BilinForm (ZMod 2) U)
    (hB : ∀ γ : ↥H', ∀ u v, B ((γ : GLV U) u) ((γ : GLV U) v) = B u v) :
    ∃ c : ZMod 2, B = c • D.B0 := by
  have key : ∀ a b c a' b' c' : Fin 6, a ≠ b → a ≠ c → b ≠ c → a' ≠ b' → a' ≠ c' → b' ≠ c' →
      B (D.w a b) (D.w a c) = B (D.w a' b') (D.w a' c') := by
    intro a b c a' b' c' hab hac hbc hab' hac' hbc'
    obtain ⟨σ, hσ, h1, h2, h3⟩ := exists_alt_three hab hac hbc hab' hac' hbc'
    obtain ⟨γ, hγ⟩ := D.w_inv σ hσ
    rw [← hB γ, hγ, hγ, h1, h2, h3]
  set c : ZMod 2 := B (D.w 0 1) (D.w 0 2) with hc
  have hdist : ∀ a b : Fin 6, a ≠ 0 → b ≠ 0 → a ≠ b → B (D.w 0 a) (D.w 0 b) = c := by
    intro a b ha hb hab
    exact key 0 a b 0 1 2 (Ne.symm ha) (Ne.symm hb) hab (by decide) (by decide) (by decide)
  have hsame : ∀ a : Fin 6, a ≠ 0 → B (D.w 0 a) (D.w 0 a) = 0 := by
    intro a ha
    obtain ⟨b, hb0, hba⟩ : ∃ b : Fin 6, b ≠ 0 ∧ b ≠ a := by
      by_cases h1 : a = 1
      · exact ⟨2, by decide, by rw [h1]; decide⟩
      · exact ⟨1, by decide, fun h => h1 h.symm⟩
    have e1 : D.w 0 a = D.w 0 b + D.w b a := (D.w_add 0 b a).symm
    have e2 : B (D.w 0 a) (D.w 0 b) = c := hdist a b ha hb0 (Ne.symm hba)
    have e3 : B (D.w 0 a) (D.w b a) = c := by
      rw [D.w_comm 0 a, D.w_comm b a]
      exact key a 0 b 0 1 2 ha (Ne.symm hba) (Ne.symm hb0) (by decide) (by decide) (by decide)
    have hcc : ∀ x : ZMod 2, x + x = 0 := by decide
    calc B (D.w 0 a) (D.w 0 a) = B (D.w 0 a) (D.w 0 b + D.w b a) := by rw [← e1]
      _ = B (D.w 0 a) (D.w 0 b) + B (D.w 0 a) (D.w b a) := map_add (B (D.w 0 a)) _ _
      _ = c + c := by rw [e2, e3]
      _ = 0 := hcc c
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
    simp [hsame a ha]
  · simp [hab, hdist a b ha hb hab]


include D in
theorem finrank_eq : Module.finrank (ZMod 2) U = 4 := by
  have hP : Module.finrank (ZMod 2) ↥(permCore 6) = 5 := by
    let s : (Fin 6 → ZMod 2) →ₗ[ZMod 2] ZMod 2 := ∑ i : Fin 6, LinearMap.proj i
    have hs : ∀ x, s x = ∑ i, x i := fun x => by simp [s]
    have hker : permCore 6 = LinearMap.ker s := by
      ext x
      rw [LinearMap.mem_ker, hs]
      exact Iff.rfl
    have hsurj : Function.Surjective s := fun c => by
      refine ⟨Pi.single 0 c, ?_⟩
      rw [hs]
      simp
    have h := LinearMap.finrank_range_add_finrank_ker s
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
      Module.finrank_fin_fun] at h
    rw [hker]
    omega
  have hK : Module.finrank (ZMod 2) ↥(LinearMap.ker D.β) = 1 := by
    let onev : ↥(permCore 6) := ⟨fun _ => 1, by show ∑ _i : Fin 6, (1 : ZMod 2) = 0; decide⟩
    have hker : LinearMap.ker D.β = Submodule.span (ZMod 2) {onev} := by
      ext z
      rw [LinearMap.mem_ker, D.ker, Submodule.mem_span_singleton]
      constructor
      · rintro (h | ⟨-, h⟩)
        · exact ⟨0, by rw [zero_smul, h]⟩
        · refine ⟨1, ?_⟩
          rw [one_smul]
          apply Subtype.ext
          funext i
          exact (h i).symm
      · rintro ⟨c, rfl⟩
        have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
        rcases hc c with rfl | rfl
        · left
          rw [zero_smul]
        · right
          refine ⟨by decide, fun i => ?_⟩
          rw [one_smul]
    rw [hker]
    refine finrank_span_singleton ?_
    intro h
    have := congrArg (fun z : ↥(permCore 6) => (z : Fin 6 → ZMod 2) 0) h
    simp [onev] at this
  have h := LinearMap.finrank_range_add_finrank_ker D.β
  rw [LinearMap.range_eq_top.2 D.surj, finrank_top, hP, hK] at h
  omega

theorem isometry (R : Subgroup (GLV U))
    (hnorm : ∀ r ∈ R, ∀ h ∈ H', r * h * r⁻¹ ∈ H') {r : GLV U} (hr : r ∈ R) (u v : U) :
    D.B0 (r u) (r v) = D.B0 u v := by
  let B : LinearMap.BilinForm (ZMod 2) U :=
    D.B0.compl₁₂ (r : U →ₗ[ZMod 2] U) (r : U →ₗ[ZMod 2] U)
  have hBapp : ∀ u v, B u v = D.B0 (r u) (r v) := fun u v => rfl
  have hB : ∀ γ : ↥H', ∀ u v, B ((γ : GLV U) u) ((γ : GLV U) v) = B u v := by
    intro γ u v
    have hγ : r * (γ : GLV U) * r⁻¹ ∈ H' := hnorm r hr γ γ.2
    have h1 := D.B0_inv ⟨r * (γ : GLV U) * r⁻¹, hγ⟩ (r u) (r v)
    have e : ∀ x : U, ((r * (γ : GLV U) * r⁻¹ : GLV U)) (r x) = r ((γ : GLV U) x) := by
      intro x
      simp
    simp only [hBapp]
    simpa [e] using h1
  obtain ⟨c, hc⟩ := D.eq_smul_B0 B hB
  have hc1 : c = 1 := by
    by_contra hne
    have h0 : c = 0 := by
      have : ∀ c : ZMod 2, c ≠ 1 → c = 0 := by decide
      exact this c hne
    have hz : ∀ x y, D.B0 (r x) (r y) = 0 := fun x y => by
      have := LinearMap.congr_fun₂ hc x y
      simpa [hBapp, h0] using this
    obtain ⟨u, hu⟩ : ∃ u : U, u ≠ 0 := ⟨D.w 0 1, D.w_ne_zero⟩
    apply hu
    have h2 : r u = 0 := D.B0_left_sep (r u) (fun y => by
      obtain ⟨x, rfl⟩ := r.surjective y
      exact hz u x)
    exact r.injective (by rw [h2, map_zero])
  rw [hc1, one_smul] at hc
  have := LinearMap.congr_fun₂ hc u v
  simpa [hBapp] using this

theorem card_le (R : Subgroup (GLV U))
    (hnorm : ∀ r ∈ R, ∀ h ∈ H', r * h * r⁻¹ ∈ H')
    (hSp : Nat.card (CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup D.B0) = 720) :
    Nat.card R ≤ 720 := by
  have : Finite (CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup D.B0) :=
    Nat.finite_of_card_ne_zero (by rw [hSp]; norm_num)
  let e := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) U
  let f : R → CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup D.B0 := fun r =>
    ⟨e.symm r.1, CFSG.LocalAnalysis.ComponentInitial.mem_bilinIsometryGroup.2 fun x y =>
      D.isometry R hnorm r.2 x y⟩
  have hf : Function.Injective f := by
    intro r r' h
    apply Subtype.ext
    exact e.symm.injective (congrArg Subtype.val h)
  calc Nat.card R ≤ Nat.card (CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup D.B0) :=
        Nat.card_le_card_of_injective f hf
    _ = 720 := hSp

end Data

end A6Norm

theorem a6NormalizerBound : A6NormalizerBound := by
  intro U _ _ _ H' R hperm hnorm
  obtain ⟨D⟩ := A6Norm.Data.of_isPermCoreModule hperm
  have : FiniteDimensional (ZMod 2) U := Module.Finite.of_finite
  exact D.card_le R hnorm
    (CFSG.LocalAnalysis.ComponentInitial.OddQuadraticFive.Orth.card_bilinIsometryGroup
      D.finrank_eq D.B0_isAlt D.B0_nondegenerate)

end G117

end G11

end CFSG.Quasithin
