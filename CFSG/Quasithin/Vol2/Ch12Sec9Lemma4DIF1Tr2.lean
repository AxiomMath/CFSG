module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF1Borel
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF2

public section

namespace CFSG.Quasithin.H13.C1294

open Module

abbrev V4 : Type := Fin (3 + 1) → ZMod 2

noncomputable def sl4Lin (g : Matrix.SpecialLinearGroup (Fin (3 + 1)) (ZMod 2)) :
    V4 ≃ₗ[ZMod 2] V4 :=
  LinearEquiv.ofLinear (Matrix.toLin' (g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)))
    (Matrix.toLin' ((g⁻¹ : Matrix.SpecialLinearGroup (Fin (3 + 1)) (ZMod 2)) :
      Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)))
    (by
      rw [← Matrix.toLin'_mul]
      have h : ((g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)) *
          ((g⁻¹ : Matrix.SpecialLinearGroup (Fin (3 + 1)) (ZMod 2)) :
            Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2))) = 1 := by
        rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.mul_adjugate,
          Matrix.SpecialLinearGroup.det_coe, one_smul]
      rw [h, Matrix.toLin'_one])
    (by
      rw [← Matrix.toLin'_mul]
      have h : (((g⁻¹ : Matrix.SpecialLinearGroup (Fin (3 + 1)) (ZMod 2)) :
          Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)) *
          (g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2))) = 1 := by
        rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_mul,
          Matrix.SpecialLinearGroup.det_coe, one_smul]
      rw [h, Matrix.toLin'_one])

theorem sl4Lin_apply (g : Matrix.SpecialLinearGroup (Fin (3 + 1)) (ZMod 2)) (x : V4) :
    sl4Lin g x = Matrix.mulVec (g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)) x := by
  simp only [sl4Lin, LinearEquiv.ofLinear_apply]
  exact Matrix.toLin'_apply _ _

noncomputable def Psi0 : Matrix.SpecialLinearGroup (Fin (3 + 1)) (ZMod 2) →*
    (V4 ≃ₗ[ZMod 2] V4) where
  toFun := sl4Lin
  map_one' := LinearEquiv.ext fun x => by
    rw [sl4Lin_apply, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    rfl
  map_mul' g h := LinearEquiv.ext fun x => by
    rw [LinearEquiv.mul_apply, sl4Lin_apply, sl4Lin_apply, sl4Lin_apply,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec]

noncomputable def conjE {I : Type} [AddCommGroup I] [Module (ZMod 2) I]
    (e : V4 ≃ₗ[ZMod 2] I) : (V4 ≃ₗ[ZMod 2] V4) →* (I ≃ₗ[ZMod 2] I) where
  toFun f := e.symm.trans (f.trans e)
  map_one' := LinearEquiv.ext fun x => by simp
  map_mul' f g := LinearEquiv.ext fun x => by simp

noncomputable def PsiE {I : Type} [AddCommGroup I] [Module (ZMod 2) I]
    (e : V4 ≃ₗ[ZMod 2] I) : Matrix.SpecialLinearGroup (Fin (3 + 1)) (ZMod 2) →* (I ≃ₗ[ZMod 2] I) :=
  (conjE e).comp Psi0

theorem PsiE_apply {I : Type} [AddCommGroup I] [Module (ZMod 2) I] (e : V4 ≃ₗ[ZMod 2] I)
    (g : Matrix.SpecialLinearGroup (Fin (3 + 1)) (ZMod 2)) (x : I) :
    PsiE e g x = e (Matrix.mulVec (g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)) (e.symm x)) := by
  show e (sl4Lin g (e.symm x)) = _
  rw [sl4Lin_apply]

theorem PsiE_injective {I : Type} [AddCommGroup I] [Module (ZMod 2) I] (e : V4 ≃ₗ[ZMod 2] I) :
    Function.Injective (PsiE e) := by
  intro g h hgh
  have hx : ∀ x : V4, Matrix.mulVec (g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)) x =
      Matrix.mulVec (h : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)) x := by
    intro x
    have hk := congrArg (fun k : I ≃ₗ[ZMod 2] I => k (e x)) hgh
    simp only [PsiE_apply, LinearEquiv.symm_apply_apply] at hk
    exact e.injective hk
  apply Subtype.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  exact hx x

theorem PsiE_surjective {I : Type} [AddCommGroup I] [Module (ZMod 2) I] (e : V4 ≃ₗ[ZMod 2] I) :
    Function.Surjective (PsiE e) := by
  intro h
  let f : V4 ≃ₗ[ZMod 2] V4 := e.trans (h.trans e.symm)
  have hdet : (LinearMap.toMatrix' (f : V4 →ₗ[ZMod 2] V4)).det = 1 := by
    have hB : LinearMap.toMatrix' ((f.symm : V4 ≃ₗ[ZMod 2] V4) : V4 →ₗ[ZMod 2] V4) *
        LinearMap.toMatrix' (f : V4 →ₗ[ZMod 2] V4) = 1 := by
      rw [← LinearMap.toMatrix'_comp]
      have hid : ((f.symm : V4 ≃ₗ[ZMod 2] V4) : V4 →ₗ[ZMod 2] V4).comp (f : V4 →ₗ[ZMod 2] V4) =
          LinearMap.id := LinearMap.ext fun x => by simp
      rw [hid, LinearMap.toMatrix'_id]
    have hu := Matrix.isUnit_det_of_left_inverse hB
    exact (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) _ hu.ne_zero
  let M : Matrix.SpecialLinearGroup (Fin (3 + 1)) (ZMod 2) :=
    ⟨LinearMap.toMatrix' (f : V4 →ₗ[ZMod 2] V4), hdet⟩
  refine ⟨M, ?_⟩
  apply LinearEquiv.ext
  intro x
  have hf : Matrix.toLin' (LinearMap.toMatrix' (f : V4 →ₗ[ZMod 2] V4)) =
      (f : V4 →ₗ[ZMod 2] V4) := Matrix.toLin'_toMatrix' _
  have hsl : Matrix.mulVec (M : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)) (e.symm x) =
      f (e.symm x) := by
    show Matrix.mulVec (LinearMap.toMatrix' (f : V4 →ₗ[ZMod 2] V4)) (e.symm x) = f (e.symm x)
    rw [← Matrix.toLin'_apply, hf]
    rfl
  rw [PsiE_apply, hsl]
  simp [f]

theorem PsiE_bijective {I : Type} [AddCommGroup I] [Module (ZMod 2) I] (e : V4 ≃ₗ[ZMod 2] I) :
    Function.Bijective (PsiE e) :=
  ⟨PsiE_injective e, PsiE_surjective e⟩

@[expose] def Wc (k : ℕ) : Submodule (ZMod 2) V4 where
  carrier := {x | ∀ i : Fin (3 + 1), k < i.val → x i = 0}
  add_mem' := fun {x y} hx hy i hi => by
    show x i + y i = 0
    rw [hx i hi, hy i hi, add_zero]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun c x hx i hi => by
    show c * x i = 0
    rw [hx i hi, mul_zero]

theorem natCard_Wc (k : ℕ) (hk : k ≤ 2) : Nat.card (Wc k) = 2 ^ (k + 1) := by
  interval_cases k
  · show Nat.card {x : V4 // ∀ i : Fin (3 + 1), 0 < i.val → x i = 0} = _
    rw [Nat.card_eq_fintype_card]
    decide
  · show Nat.card {x : V4 // ∀ i : Fin (3 + 1), 1 < i.val → x i = 0} = _
    rw [Nat.card_eq_fintype_card]
    decide
  · show Nat.card {x : V4 // ∀ i : Fin (3 + 1), 2 < i.val → x i = 0} = _
    rw [Nat.card_eq_fintype_card]
    decide


@[expose] noncomputable def flagI {I : Type} [AddCommGroup I] [Module (ZMod 2) I] (e : V4 ≃ₗ[ZMod 2] I)
    (k : ℕ) : Submodule (ZMod 2) I :=
  (Wc k).map (e : V4 →ₗ[ZMod 2] I)

theorem finrank_flagI {I : Type} [AddCommGroup I] [Module (ZMod 2) I] [Finite I]
    (e : V4 ≃ₗ[ZMod 2] I) (k : ℕ) (hk : k ≤ 2) : finrank (ZMod 2) (flagI e k) = k + 1 := by
  have h1 : Nat.card (flagI e k) = Nat.card (Wc k) :=
    (Nat.card_congr (Submodule.equivMapOfInjective (e : V4 →ₗ[ZMod 2] I) e.injective (Wc k)).toEquiv).symm
  have h2 := natCard_submodule_eq (flagI e k)
  rw [h1, natCard_Wc k hk] at h2
  exact (Nat.pow_right_injective (le_refl 2) h2).symm

@[expose] noncomputable def Bstd {I : Type} [AddCommGroup I] [Module (ZMod 2) I] (e : V4 ≃ₗ[ZMod 2] I) :
    Subgroup (I ≃ₗ[ZMod 2] I) :=
  stabS (flagI e 0) ⊓ stabS (flagI e 1) ⊓ stabS (flagI e 2)

theorem PsiE_mem_stabS_flagI_iff {I : Type} [AddCommGroup I] [Module (ZMod 2) I]
    (e : V4 ≃ₗ[ZMod 2] I) (g : Matrix.SpecialLinearGroup (Fin (3 + 1)) (ZMod 2)) (k : ℕ) :
    PsiE e g ∈ stabS (flagI e k) ↔
      ∀ x : V4, x ∈ Wc k ↔ Matrix.mulVec (g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)) x ∈ Wc k := by
  have hstab : PsiE e g ∈ stabS (flagI e k) ↔ ∀ y : I, y ∈ flagI e k ↔ PsiE e g y ∈ flagI e k :=
    Iff.rfl
  rw [hstab]
  have hm : ∀ z : I, z ∈ flagI e k ↔ e.symm z ∈ Wc k := fun z => by
    rw [flagI, Submodule.mem_map_equiv]
  constructor
  · intro h x
    have hx := h (e x)
    simp only [hm, PsiE_apply, LinearEquiv.symm_apply_apply] at hx
    exact hx
  · intro h y
    simp only [hm, PsiE_apply, LinearEquiv.symm_apply_apply]
    exact h (e.symm y)

theorem mulVec_mem_Wc_of_upper {g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)}
    (hg : ∀ i j : Fin (3 + 1), j < i → g i j = 0) {k : ℕ} {x : V4} (hx : x ∈ Wc k) :
    Matrix.mulVec g x ∈ Wc k := by
  intro i hi
  show ∑ j, g i j * x j = 0
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : j.val ≤ k
  · have hlt : j < i := by
      rw [Fin.lt_def]
      omega
    rw [hg i j hlt, zero_mul]
  · rw [hx j (by omega), mul_zero]

theorem mem_upperSub_iff_Wc (g : Matrix.SpecialLinearGroup (Fin (3 + 1)) (ZMod 2)) :
    g ∈ upperSub ↔ ∀ k : ℕ, k ≤ 2 → ∀ x : V4,
      x ∈ Wc k ↔ Matrix.mulVec (g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)) x ∈ Wc k := by
  constructor
  · intro hg k _ x
    have hginvU : (g⁻¹ : Matrix.SpecialLinearGroup (Fin (3 + 1)) (ZMod 2)) ∈ upperSub :=
      upperSub.inv_mem hg
    have hcancel : ∀ y : V4, Matrix.mulVec
        ((g⁻¹ : Matrix.SpecialLinearGroup (Fin (3 + 1)) (ZMod 2)) :
          Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2))
        (Matrix.mulVec (g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)) y) = y := by
      intro y
      rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    constructor
    · intro hx
      exact mulVec_mem_Wc_of_upper hg hx
    · intro hx
      have hkey := mulVec_mem_Wc_of_upper (g := ((g⁻¹ : Matrix.SpecialLinearGroup (Fin (3 + 1)) (ZMod 2)) :
          Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2))) (fun i j hji => hginvU i j hji) hx
      rw [hcancel x] at hkey
      exact hkey
  · intro h
    show ∀ i j : Fin (3 + 1), j < i → (g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)) i j = 0
    intro i j hji
    have hj2 : j.val ≤ 2 := by
      have := i.isLt
      rw [Fin.lt_def] at hji
      omega
    have hx : (Pi.single j 1 : V4) ∈ Wc j.val := by
      intro i' hi'
      have hne : i' ≠ j := by
        intro heq
        rw [heq] at hi'
        omega
      exact Pi.single_eq_of_ne hne _
    have hmem := (h j.val hj2 (Pi.single j 1)).1 hx
    have hi := hmem i (by rw [Fin.lt_def] at hji; exact hji)
    rw [Matrix.mulVec_single_one] at hi
    exact hi


theorem mem_upperSub_iff_Bstd {I : Type} [AddCommGroup I] [Module (ZMod 2) I] [Finite I]
    (e : V4 ≃ₗ[ZMod 2] I) (g : Matrix.SpecialLinearGroup (Fin (3 + 1)) (ZMod 2)) :
    g ∈ upperSub ↔ PsiE e g ∈ Bstd e := by
  unfold Bstd
  rw [Subgroup.mem_inf, Subgroup.mem_inf, PsiE_mem_stabS_flagI_iff, PsiE_mem_stabS_flagI_iff,
    PsiE_mem_stabS_flagI_iff, mem_upperSub_iff_Wc]
  constructor
  · intro h
    exact ⟨⟨h 0 (by norm_num), h 1 (by norm_num)⟩, h 2 (by norm_num)⟩
  · rintro ⟨⟨h0, h1⟩, h2⟩ k hk
    interval_cases k
    · exact h0
    · exact h1
    · exact h2

theorem map_upperSub_eq_Bstd {I : Type} [AddCommGroup I] [Module (ZMod 2) I] [Finite I]
    (e : V4 ≃ₗ[ZMod 2] I) : upperSub.map (PsiE e) = Bstd e := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (mem_upperSub_iff_Bstd e g).1 hg
  · intro hx
    obtain ⟨g, rfl⟩ := PsiE_surjective e x
    exact ⟨g, (mem_upperSub_iff_Bstd e g).2 hx, rfl⟩

end CFSG.Quasithin.H13.C1294
