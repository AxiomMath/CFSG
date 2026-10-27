module

public import CFSG.OddTranspositions.PartFour.ThirteenListFiveForm

public section

namespace CFSG.OddTranspositions.PartFour.ListFive

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.OddTranspositions.PartFour.TableE1Five Matrix

variable {n : ℕ} {b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5)}

private theorem exists_sq_add_sq (a d t : ZMod 5) (ha : a ≠ 0) (hd : d ≠ 0) (ht : t ≠ 0) :
    ∃ l m : ZMod 5, l * l * a + m * m * d = t := by
  revert a d t
  decide

private theorem exists_norm_eq_of_aniso (hsym : ∀ x y, b x y = b y x) {z₁ z₂ : Fin n → ZMod 5}
    (h₁ : b z₁ z₁ ≠ 0) (h₂ : b z₂ z₂ ≠ 0) (h₂₁ : b z₂ z₁ = 0) {c : ZMod 5} (hc : c ≠ 0) :
    ∃ l m : ZMod 5, b (l • z₁ + m • z₂) (l • z₁ + m • z₂) = c := by
  obtain ⟨l, m, hlm⟩ := exists_sq_add_sq _ _ _ h₁ h₂ hc
  refine ⟨l, m, ?_⟩
  simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, h₂₁, hsym z₁ z₂]
  rw [← hlm]
  ring

private theorem exists_norm_eq_perp₂ (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 4 ≤ n) {u₁ u₂ : Fin n → ZMod 5}
    (h₁ : b u₁ u₁ ≠ 0) (h₂ : b u₂ u₂ ≠ 0) (h₁₂ : b u₁ u₂ = 0) {c : ZMod 5} (hc : c ≠ 0) :
    ∃ x, b x u₁ = 0 ∧ b x u₂ = 0 ∧ b x x = c := by
  obtain ⟨z₁, hz₁u₁, hz₁u₂, hz₁⟩ := exists_aniso_perp₂ hsym hnd (by omega) h₁ h₂ h₁₂
  obtain ⟨z₂, hz₂u₁, hz₂u₂, hz₂z₁, hz₂⟩ := exists_aniso_perp₃ hsym hnd hn h₁ h₂ hz₁ h₁₂
    (by rw [hsym]; exact hz₁u₁) (by rw [hsym]; exact hz₁u₂)
  obtain ⟨l, m, hlm⟩ := exists_norm_eq_of_aniso hsym hz₁ hz₂ hz₂z₁ hc
  refine ⟨l • z₁ + m • z₂, ?_, ?_, hlm⟩ <;>
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hz₁u₁, hz₁u₂,
      hz₂u₁, hz₂u₂, mul_zero, add_zero]

private theorem exists_norm_eq_perp₃ (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 5 ≤ n) {u₁ u₂ u₃ : Fin n → ZMod 5}
    (h₁ : b u₁ u₁ ≠ 0) (h₂ : b u₂ u₂ ≠ 0) (h₃ : b u₃ u₃ ≠ 0) (h₁₂ : b u₁ u₂ = 0)
    (h₁₃ : b u₁ u₃ = 0) (h₂₃ : b u₂ u₃ = 0) {c : ZMod 5} (hc : c ≠ 0) :
    ∃ x, b x u₁ = 0 ∧ b x u₂ = 0 ∧ b x u₃ = 0 ∧ b x x = c := by
  have h₂₁ : b u₂ u₁ = 0 := by rw [hsym]; exact h₁₂
  have h₃₁ : b u₃ u₁ = 0 := by rw [hsym]; exact h₁₃
  have h₃₂ : b u₃ u₂ = 0 := by rw [hsym]; exact h₂₃
  obtain ⟨z₁, hz₁u₁, hz₁u₂, hz₁u₃, hz₁⟩ :=
    exists_aniso_perp₃ hsym hnd (by omega) h₁ h₂ h₃ h₁₂ h₁₃ h₂₃
  have hu₁z₁ : b u₁ z₁ = 0 := by rw [hsym]; exact hz₁u₁
  have hu₂z₁ : b u₂ z₁ = 0 := by rw [hsym]; exact hz₁u₂
  have hu₃z₁ : b u₃ z₁ = 0 := by rw [hsym]; exact hz₁u₃
  obtain ⟨z₂, hz₂, hz₂z₂⟩ := exists_aniso_perp hsym hnd (k := 4) (by omega) ![u₁, u₂, u₃, z₁]
    (fun i j hij => by
      fin_cases i <;> fin_cases j
      all_goals first
        | exact absurd rfl hij
        | simp [h₁₂, h₂₁, h₁₃, h₃₁, h₂₃, h₃₂, hz₁u₁, hz₁u₂, hz₁u₃, hu₁z₁, hu₂z₁, hu₃z₁])
    (fun i => by fin_cases i <;> simp [h₁, h₂, h₃, hz₁])
  have hz₂u₁ : b z₂ u₁ = 0 := by simpa using hz₂ 0
  have hz₂u₂ : b z₂ u₂ = 0 := by simpa using hz₂ 1
  have hz₂u₃ : b z₂ u₃ = 0 := by simpa using hz₂ 2
  have hz₂z₁ : b z₂ z₁ = 0 := by simpa using hz₂ 3
  obtain ⟨l, m, hlm⟩ := exists_norm_eq_of_aniso hsym hz₁ hz₂z₂ hz₂z₁ hc
  refine ⟨l • z₁ + m • z₂, ?_, ?_, ?_, hlm⟩ <;>
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hz₁u₁, hz₁u₂,
      hz₁u₃, hz₂u₁, hz₂u₂, hz₂u₃, mul_zero, add_zero]

@[expose] def minusCoeff : Fin 4 → ZMod 5 := ![1, 1, 1, -2]

@[expose] def minusCoeffInv : Fin 4 → ZMod 5 := ![1, 1, 1, 2]

theorem minusCoeffInv_mul (i : Fin 4) : minusCoeffInv i * minusCoeff i = 1 := by
  fin_cases i <;> decide

theorem minusBilin_eq_sum (x y : Fin 4 → ZMod 5) :
    minusBilin x y = ∑ i, minusCoeff i * x i * y i := by
  rw [minusBilin_apply, Fin.sum_univ_four]
  simp only [minusCoeff, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

theorem exists_minusFrame (hsym : ∀ x y, b x y = b y x) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hn : 5 ≤ n) {v : Fin n → ZMod 5} (hv : b v v = 1) :
    ∃ u : Fin 4 → Fin n → ZMod 5, u 0 = v ∧
      ∀ i j, b (u i) (u j) = if i = j then minusCoeff i else 0 := by
  have h1 : (1 : ZMod 5) ≠ 0 := by decide
  have hm2 : (-2 : ZMod 5) ≠ 0 := by decide
  have hv0 : b v v ≠ 0 := by rw [hv]; exact h1
  obtain ⟨u₁, hu₁v, hu₁⟩ := exists_norm_eq_perp hsym hnd (by omega) hv0 h1
  have hu₁0 : b u₁ u₁ ≠ 0 := by rw [hu₁]; exact h1
  have hvu₁ : b v u₁ = 0 := by rw [hsym]; exact hu₁v
  obtain ⟨u₂, hu₂v, hu₂u₁, hu₂⟩ := exists_norm_eq_perp₂ hsym hnd (by omega) hv0 hu₁0 hvu₁ h1
  have hu₂0 : b u₂ u₂ ≠ 0 := by rw [hu₂]; exact h1
  have hvu₂ : b v u₂ = 0 := by rw [hsym]; exact hu₂v
  have hu₁u₂ : b u₁ u₂ = 0 := by rw [hsym]; exact hu₂u₁
  obtain ⟨u₃, hu₃v, hu₃u₁, hu₃u₂, hu₃⟩ :=
    exists_norm_eq_perp₃ hsym hnd hn hv0 hu₁0 hu₂0 hvu₁ hvu₂ hu₁u₂ hm2
  have hvu₃ : b v u₃ = 0 := by rw [hsym]; exact hu₃v
  have hu₁u₃ : b u₁ u₃ = 0 := by rw [hsym]; exact hu₃u₁
  have hu₂u₃ : b u₂ u₃ = 0 := by rw [hsym]; exact hu₃u₂
  have key : ∀ i : Fin 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
  refine ⟨![v, u₁, u₂, u₃], rfl, fun i j => ?_⟩
  rcases key i with rfl | rfl | rfl | rfl <;> rcases key j with rfl | rfl | rfl | rfl <;>
    simp [minusCoeff, hv, hu₁, hu₂, hu₃, hu₁v, hu₂v, hu₃v, hvu₁, hvu₂, hvu₃, hu₂u₁, hu₁u₂,
      hu₃u₁, hu₁u₃, hu₃u₂, hu₂u₃]

@[expose] noncomputable def frameEmbed (u : Fin 4 → Fin n → ZMod 5) :
    (Fin 4 → ZMod 5) →ₗ[ZMod 5] (Fin n → ZMod 5) where
  toFun y := ∑ i, y i • u i
  map_add' y y' := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c y := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, Finset.smul_sum]

variable (b) in
@[expose] noncomputable def frameProj (u : Fin 4 → Fin n → ZMod 5) :
    (Fin n → ZMod 5) →ₗ[ZMod 5] (Fin 4 → ZMod 5) where
  toFun x i := minusCoeffInv i * b x (u i)
  map_add' x x' := by
    funext i
    simp only [LinearMap.BilinForm.add_left, Pi.add_apply, mul_add]
  map_smul' c x := by
    funext i
    simp only [LinearMap.BilinForm.smul_left, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem frameEmbed_apply (u : Fin 4 → Fin n → ZMod 5) (y : Fin 4 → ZMod 5) :
    frameEmbed u y = ∑ i, y i • u i :=
  rfl

theorem frameProj_apply (u : Fin 4 → Fin n → ZMod 5) (x : Fin n → ZMod 5) (i : Fin 4) :
    frameProj b u x i = minusCoeffInv i * b x (u i) :=
  rfl

theorem frameEmbed_single (u : Fin 4 → Fin n → ZMod 5) (i : Fin 4) :
    frameEmbed u (Pi.single i 1) = u i := by
  rw [frameEmbed_apply, Finset.sum_eq_single i (fun j _ hj => by
    rw [Pi.single_eq_of_ne hj, zero_smul]) (fun h => absurd (Finset.mem_univ i) h),
    Pi.single_eq_same, one_smul]

section Frame

variable {u : Fin 4 → Fin n → ZMod 5}
  (hu : ∀ i j, b (u i) (u j) = if i = j then minusCoeff i else 0)
include hu

private theorem bilin_frameEmbed_right (x : Fin n → ZMod 5) (y : Fin 4 → ZMod 5) :
    b x (frameEmbed u y) = ∑ j, y j * b x (u j) := by
  rw [frameEmbed_apply, LinearMap.BilinForm.sum_right]
  simp only [LinearMap.BilinForm.smul_right]

theorem frameProj_frameEmbed (y : Fin 4 → ZMod 5) : frameProj b u (frameEmbed u y) = y := by
  funext i
  rw [frameProj_apply, frameEmbed_apply, LinearMap.BilinForm.sum_left]
  simp only [LinearMap.BilinForm.smul_left, hu, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  linear_combination y i * minusCoeffInv_mul i

theorem minusBilin_frameProj (x : Fin n → ZMod 5) (y : Fin 4 → ZMod 5) :
    minusBilin (frameProj b u x) y = b x (frameEmbed u y) := by
  rw [minusBilin_eq_sum, bilin_frameEmbed_right hu]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [frameProj_apply]
  linear_combination (y j * b x (u j)) * minusCoeffInv_mul j

theorem bilin_frameEmbed (y y' : Fin 4 → ZMod 5) :
    b (frameEmbed u y) (frameEmbed u y') = minusBilin y y' := by
  rw [← minusBilin_frameProj hu, frameProj_frameEmbed hu]

theorem toMatrix'_frameProj_mul :
    LinearMap.toMatrix' (frameProj b u) * LinearMap.toMatrix' (frameEmbed u) = 1 := by
  rw [← LinearMap.toMatrix'_comp,
    show frameProj b u ∘ₗ frameEmbed u = LinearMap.id from
      LinearMap.ext (frameProj_frameEmbed hu), LinearMap.toMatrix'_id]

theorem frameMat_mul (g h : Matrix (Fin 4) (Fin 4) (ZMod 5)) :
    (1 + LinearMap.toMatrix' (frameEmbed u) * (g - 1) * LinearMap.toMatrix' (frameProj b u)) *
        (1 + LinearMap.toMatrix' (frameEmbed u) * (h - 1) * LinearMap.toMatrix' (frameProj b u)) =
      1 + LinearMap.toMatrix' (frameEmbed u) * (g * h - 1) *
        LinearMap.toMatrix' (frameProj b u) := by
  set A := LinearMap.toMatrix' (frameEmbed u)
  set B := LinearMap.toMatrix' (frameProj b u)
  have hBA : B * A = 1 := toMatrix'_frameProj_mul hu
  have e : A * (g - 1) * B * (A * (h - 1) * B) = A * ((g - 1) * (h - 1)) * B := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc B A, hBA, Matrix.one_mul]
  have e' : g * h - 1 = (g - 1) + (h - 1) + (g - 1) * (h - 1) := by noncomm_ring
  rw [add_mul, one_mul, mul_add, mul_one, e, e', Matrix.mul_add, Matrix.mul_add, Matrix.add_mul,
    Matrix.add_mul]
  abel

variable (b u) in
@[expose] noncomputable def frameMonoidHom :
    Matrix (Fin 4) (Fin 4) (ZMod 5) →* Matrix (Fin n) (Fin n) (ZMod 5) where
  toFun g := 1 + LinearMap.toMatrix' (frameEmbed u) * (g - 1) * LinearMap.toMatrix' (frameProj b u)
  map_one' := by rw [sub_self, Matrix.mul_zero, Matrix.zero_mul, add_zero]
  map_mul' g h := (frameMat_mul hu g h).symm

theorem frameMonoidHom_apply (g : Matrix (Fin 4) (Fin 4) (ZMod 5)) :
    frameMonoidHom b u hu g =
      1 + LinearMap.toMatrix' (frameEmbed u) * (g - 1) * LinearMap.toMatrix' (frameProj b u) := by
  simp only [frameMonoidHom, MonoidHom.coe_mk, OneHom.coe_mk]

variable (b u) in
@[expose] noncomputable def frameHom : GL (Fin 4) (ZMod 5) →* GL (Fin n) (ZMod 5) :=
  Units.map (frameMonoidHom b u hu)

theorem act_frameHom (g : GL (Fin 4) (ZMod 5)) (x : Fin n → ZMod 5) :
    act (frameHom b u hu g) x =
      x + frameEmbed u (((g : Matrix (Fin 4) (Fin 4) (ZMod 5)) - 1) *ᵥ frameProj b u x) := by
  rw [act, frameHom, Units.coe_map, frameMonoidHom_apply, Matrix.add_mulVec, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec,
    LinearMap.toMatrix'_mulVec]

theorem act_frameHom_of_frameProj_eq_zero (g : GL (Fin 4) (ZMod 5)) {x : Fin n → ZMod 5}
    (hx : frameProj b u x = 0) : act (frameHom b u hu g) x = x := by
  rw [act_frameHom, hx, Matrix.mulVec_zero, map_zero, add_zero]

theorem frameHom_refl (hsym : ∀ x y, b x y = b y x) (y : Fin 4 → ZMod 5) :
    frameHom b u hu (refl minusBilin y) = refl b (frameEmbed u y) := by
  have hn : b (frameEmbed u y) (frameEmbed u y) = minusBilin y y := bilin_frameEmbed hu y y
  by_cases hy : minusBilin y y = 1
  · refine gl_ext fun x => ?_
    rw [act_frameHom, act_refl (hn.trans hy), Matrix.sub_mulVec, Matrix.one_mulVec, ← act,
      act_refl hy, add_sub_cancel_left, map_smul, minusBilin_frameProj hu]
  · rw [refl_of_ne hy, refl_of_ne (hn ▸ hy), map_one]

theorem frameHom_injective : Function.Injective (frameHom b u hu) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  set A := LinearMap.toMatrix' (frameEmbed u)
  set B := LinearMap.toMatrix' (frameProj b u)
  have hBA : B * A = 1 := toMatrix'_frameProj_mul hu
  have h0 : A * ((g : Matrix (Fin 4) (Fin 4) (ZMod 5)) - 1) * B = 0 := by
    have h1 := congrArg (fun k : GL (Fin n) (ZMod 5) => (k : Matrix (Fin n) (Fin n) (ZMod 5))) hg
    simp only [frameHom, Units.coe_map, Units.val_one] at h1
    rw [frameMonoidHom_apply] at h1
    exact add_eq_left.mp h1
  have h2 : (g : Matrix (Fin 4) (Fin 4) (ZMod 5)) - 1 = 0 := by
    calc (g : Matrix (Fin 4) (Fin 4) (ZMod 5)) - 1
        = B * A * ((g : Matrix (Fin 4) (Fin 4) (ZMod 5)) - 1) * (B * A) := by
          rw [hBA, Matrix.one_mul, Matrix.mul_one]
      _ = B * (A * ((g : Matrix (Fin 4) (Fin 4) (ZMod 5)) - 1) * B) * A := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h0, Matrix.mul_zero, Matrix.zero_mul]
  exact Units.ext (sub_eq_zero.mp h2)

theorem map_reflGroup_frameHom_le (hsym : ∀ x y, b x y = b y x) :
    (reflGroup minusBilin).map (frameHom b u hu) ≤ reflGroup b := by
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨r, hr, rfl⟩
  obtain ⟨y, -, rfl⟩ := mem_reflSet_iff.mp hr
  rw [frameHom_refl hu hsym]
  exact refl_mem_reflGroup _

end Frame

private theorem eq_zero_of_eq_neg' (a : ZMod 5) (h : a = -a) : a = 0 := by
  revert a
  decide

theorem exists_injective_reflGroup_minusBilin (hsym : ∀ x y, b x y = b y x)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hn : 5 ≤ n) {v : Fin n → ZMod 5} (hv : b v v = 1) :
    ∃ ψ : reflGroup minusBilin →* reflGroup b ⧸ Subgroup.center (reflGroup b),
      Function.Injective ψ ∧
        ψ ⟨refl minusBilin (Pi.single 0 1), refl_mem_reflGroup _⟩ =
          QuotientGroup.mk ⟨refl b v, refl_mem_reflGroup v⟩ := by
  obtain ⟨u, hu0, hu⟩ := exists_minusFrame hsym hnd hn hv
  have hle := map_reflGroup_frameHom_le hu hsym
  let ψ₁ : reflGroup minusBilin →* reflGroup b :=
    ((frameHom b u hu).comp (reflGroup minusBilin).subtype).codRestrict (reflGroup b)
      fun g => hle ⟨g, g.2, rfl⟩
  have hψ₁ : ∀ g, (ψ₁ g : GL (Fin n) (ZMod 5)) = frameHom b u hu g := fun g => rfl
  refine ⟨(QuotientGroup.mk' _).comp ψ₁, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro g hg
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hg
    rcases coe_eq_of_mem_center hsym hnd (by omega) hv hg with h | h
    · rw [hψ₁] at h
      exact Subtype.ext (frameHom_injective hu (h.trans (map_one _).symm))
    · exfalso
      obtain ⟨y, hy0, hyu⟩ := exists_ne_zero_perp (b := b) (k := 4) (by omega) u
      have hπ : frameProj b u y = 0 := funext fun i => by
        rw [frameProj_apply, hyu i, mul_zero, Pi.zero_apply]
      have h1 := act_frameHom_of_frameProj_eq_zero hu (g : GL (Fin 4) (ZMod 5)) hπ
      rw [← hψ₁, h, neg_act, act_one] at h1
      exact hy0 (funext fun i => eq_zero_of_eq_neg' (y i) (congrFun h1 i).symm)
  · rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    congr 1
    apply Subtype.ext
    rw [hψ₁]
    change frameHom b u hu (refl minusBilin (Pi.single 0 1)) = refl b v
    rw [frameHom_refl hu hsym, frameEmbed_single, hu0]

end CFSG.OddTranspositions.PartFour.ListFive
