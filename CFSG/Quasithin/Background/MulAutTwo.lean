module

public import CFSG.Quasithin.Background.G10FourGL
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
import CFSG.GroupTheory.GLnTwoSplitting.Transvection

public section

namespace CFSG.Quasithin.MulAutTwo

open Module CFSG.GroupTheory.GLnTwoSplitting

noncomputable def slEquivGL (n : ℕ) :
    Matrix.SpecialLinearGroup (Fin n) (ZMod 2) ≃* GL (Fin n) (ZMod 2) :=
  MulEquiv.ofBijective
    (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin n) (ZMod 2) →* _)
    ⟨Matrix.SpecialLinearGroup.toGL_injective, fun A => by
      have hdet : (A : Matrix (Fin n) (Fin n) (ZMod 2)).det = 1 := by
        have h1 : Matrix.GeneralLinearGroup.det A = 1 := Subsingleton.elim _ _
        have h2 := congrArg (fun u : (ZMod 2)ˣ => (u : ZMod 2)) h1
        simpa using h2
      refine ⟨⟨(A : Matrix (Fin n) (Fin n) (ZMod 2)), hdet⟩, ?_⟩
      apply Units.ext
      rfl⟩

theorem center_SL_eq_bot {n : ℕ} (hn : 1 ≤ n) :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) = ⊥ := by
  refine eq_bot_iff.2 fun A hA => ?_
  obtain ⟨r, hr, hA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  have hr1 : r = 1 := by
    rw [Fintype.card_fin] at hr
    rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) r with h | h
    · rw [h, zero_pow (by omega)] at hr
      exact absurd hr zero_ne_one
    · exact h
  rw [Subgroup.mem_bot]
  ext i j
  rw [← hA, hr1]
  simp

@[expose] def conjAut {W W' : Type} [AddCommMonoid W] [Module (ZMod 2) W] [AddCommMonoid W']
    [Module (ZMod 2) W'] (e : W ≃ₗ[ZMod 2] W') : (W ≃ₗ[ZMod 2] W) ≃* (W' ≃ₗ[ZMod 2] W') where
  toFun f := e.symm.trans (f.trans e)
  invFun f := e.trans (f.trans e.symm)
  left_inv f := LinearEquiv.ext fun v => by simp
  right_inv f := LinearEquiv.ext fun v => by simp
  map_mul' f g := LinearEquiv.ext fun v => by simp [LinearEquiv.mul_apply]

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

noncomputable def glEquiv [Finite W] :
    (W ≃ₗ[ZMod 2] W) ≃* GL (Fin (finrank (ZMod 2) W)) (ZMod 2) :=
  (conjAut (LinearEquiv.ofFinrankEq W (Fin (finrank (ZMod 2) W) → ZMod 2) (by simp))).trans
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2)
      (Fin (finrank (ZMod 2) W) → ZMod 2)).symm.trans Matrix.GeneralLinearGroup.toLin.symm)

theorem isSimpleGroup_linearEquiv [Finite W] (h3 : 3 ≤ finrank (ZMod 2) W) :
    IsSimpleGroup (W ≃ₗ[ZMod 2] W) := by
  set n := finrank (ZMod 2) W with hn
  have hs := (CFSG.LinearGroups.linear_projective_simple (K := ZMod 2) (n := n) (by omega)
    (Or.inl h3)).2.1
  have hc := center_SL_eq_bot (n := n) (by omega)
  let eP : Matrix.SpecialLinearGroup (Fin n) (ZMod 2) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hc.symm)
  exact (MulEquiv.isSimpleGroup_congr (glEquiv.trans ((slEquivGL n).symm.trans eP))).mpr hs

theorem card_linearEquiv [Finite W] :
    Nat.card (W ≃ₗ[ZMod 2] W) =
      ∏ i : Fin (finrank (ZMod 2) W), (2 ^ finrank (ZMod 2) W - 2 ^ (i : ℕ)) := by
  rw [Nat.card_congr glEquiv.toEquiv, Matrix.card_GL_field, ZMod.card]

variable {V : Type} [CommGroup V]

@[expose] def linEquiv [Module (ZMod 2) (Additive V)] :
    MulAut V ≃* (Additive V ≃ₗ[ZMod 2] Additive V) where
  toFun g := (MulEquiv.toAdditive g).toLinearEquiv (ZMod.map_smul (MulEquiv.toAdditive g))
  invFun f := MulEquiv.toAdditive.symm f.toAddEquiv
  left_inv g := by ext v; rfl
  right_inv f := by ext v; rfl
  map_mul' g h := by ext v; rfl

theorem linEquiv_apply [Module (ZMod 2) (Additive V)] (g : MulAut V) (w : Additive V) :
    linEquiv g w = Additive.ofMul (g (Additive.toMul w)) :=
  rfl

noncomputable abbrev zmod2Module (hV : ∀ v : V, v * v = 1) :
    Module (ZMod 2) (Additive V) :=
  AddCommGroup.zmodModule fun x => by
    rw [two_nsmul]
    exact hV (Additive.toMul x)

theorem card_eq_pow_finrank [Finite V] [Module (ZMod 2) (Additive V)] :
    Nat.card V = 2 ^ finrank (ZMod 2) (Additive V) := by
  have : Module.Finite (ZMod 2) (Additive V) := Module.Finite.of_finite
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
  rw [Nat.card_zmod] at h
  exact h

theorem isSimpleGroup_mulAut [Finite V] (hV : ∀ v : V, v * v = 1) (h8 : 8 ≤ Nat.card V) :
    IsSimpleGroup (MulAut V) := by
  let _ := zmod2Module hV
  have hcard := card_eq_pow_finrank (V := V)
  have h3 : 3 ≤ finrank (ZMod 2) (Additive V) := by
    by_contra h
    have h4 : 2 ^ finrank (ZMod 2) (Additive V) ≤ 2 ^ 2 :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have := isSimpleGroup_linearEquiv (W := Additive V) h3
  exact (MulEquiv.isSimpleGroup_congr linEquiv).mpr this

theorem card_mulAut [Finite V] (hV : ∀ v : V, v * v = 1) {n : ℕ} (hn : Nat.card V = 2 ^ n) :
    Nat.card (MulAut V) = ∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ)) := by
  let _ := zmod2Module hV
  have hcard := card_eq_pow_finrank (V := V)
  have hn' : finrank (ZMod 2) (Additive V) = n :=
    Nat.pow_right_injective le_rfl (hcard.symm.trans hn)
  rw [Nat.card_congr linEquiv.toEquiv, card_linearEquiv, hn']

noncomputable def transv (hV : ∀ v : V, v * v = 1) {A : Subgroup V} (hA : A.index = 2) {c : V}
    (hc : c ∈ A) : MulAut V := by
  classical
  have hinv : ∀ v : V, (if (if v ∈ A then v else v * c) ∈ A then (if v ∈ A then v else v * c)
      else (if v ∈ A then v else v * c) * c) = v := by
    intro v
    by_cases hv : v ∈ A
    · simp [hv]
    · have h1 : v * c ∉ A := fun h => hv (by simpa using A.mul_mem h (A.inv_mem hc))
      simp [hv, h1, mul_assoc, hV c]
  exact
  { toFun := fun v => if v ∈ A then v else v * c
    invFun := fun v => if v ∈ A then v else v * c
    left_inv := hinv
    right_inv := hinv
    map_mul' := fun u v => by
      have huv := Subgroup.mul_mem_iff_of_index_two hA (a := u) (b := v)
      by_cases hu : u ∈ A <;> by_cases hv : v ∈ A
      · simp [hu, hv, huv.mpr (iff_of_true hu hv)]
      · have h1 : u * v ∉ A := fun h => hv ((huv.mp h).mp hu)
        simp [hu, hv, h1, mul_assoc]
      · have h1 : u * v ∉ A := fun h => hu ((huv.mp h).mpr hv)
        simp only [hu, hv, h1, ite_false, ite_true]
        rw [mul_assoc, mul_comm v c, ← mul_assoc]
      · have h1 : u * v ∈ A := huv.mpr (iff_of_false hu hv)
        simp only [hu, hv, h1, ite_false, ite_true]
        rw [mul_mul_mul_comm, hV c, mul_one] }

theorem transv_of_mem (hV : ∀ v : V, v * v = 1) {A : Subgroup V} (hA : A.index = 2) {c : V}
    (hc : c ∈ A) {v : V} (hv : v ∈ A) : transv hV hA hc v = v := by
  classical
  show (if v ∈ A then v else v * c) = v
  rw [ite_eq_left hv]

theorem transv_of_not_mem (hV : ∀ v : V, v * v = 1) {A : Subgroup V} (hA : A.index = 2) {c : V}
    (hc : c ∈ A) {v : V} (hv : v ∉ A) : transv hV hA hc v = v * c := by
  classical
  show (if v ∈ A then v else v * c) = v * c
  rw [ite_eq_right hv]

theorem transv_mul_inv_mem (hV : ∀ v : V, v * v = 1) {A : Subgroup V} (hA : A.index = 2) {c : V}
    (hc : c ∈ A) (v : V) : transv hV hA hc v * v⁻¹ ∈ A := by
  by_cases hv : v ∈ A
  · rw [transv_of_mem hV hA hc hv, mul_inv_cancel]
    exact A.one_mem
  · rw [transv_of_not_mem hV hA hc hv, mul_comm v c, mul_assoc, mul_inv_cancel, mul_one]
    exact hc

noncomputable def axisForm [Module (ZMod 2) (Additive V)] (A : Subgroup V) (hA : A.index = 2) :
    Additive V →ₗ[ZMod 2] ZMod 2 := by
  classical
  exact
  { toFun := fun w => if Additive.toMul w ∈ A then 0 else 1
    map_add' := fun x y => by
      have hxy := Subgroup.mul_mem_iff_of_index_two hA (a := Additive.toMul x)
        (b := Additive.toMul y)
      simp only [toMul_add]
      by_cases hx : Additive.toMul x ∈ A <;> by_cases hy : Additive.toMul y ∈ A
      · rw [ite_eq_left (hxy.mpr (iff_of_true hx hy)), ite_eq_left hx, ite_eq_left hy,
          add_zero]
      · rw [ite_eq_right (fun h' => hy ((hxy.mp h').mp hx)), ite_eq_left hx, ite_eq_right hy,
          zero_add]
      · rw [ite_eq_right (fun h' => hx ((hxy.mp h').mpr hy)), ite_eq_right hx, ite_eq_left hy,
          add_zero]
      · rw [ite_eq_left (hxy.mpr (iff_of_false hx hy)), ite_eq_right hx, ite_eq_right hy]
        decide
    map_smul' := fun c w => by
      rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) c with rfl | rfl
      · simp [A.one_mem]
      · simp }

theorem axisForm_eq_zero [Module (ZMod 2) (Additive V)] (A : Subgroup V) (hA : A.index = 2)
    (w : Additive V) : axisForm A hA w = 0 ↔ Additive.toMul w ∈ A := by
  classical
  show (if Additive.toMul w ∈ A then 0 else 1 : ZMod 2) = 0 ↔ _
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h0 => absurd h0 one_ne_zero, fun h0 => absurd h0 h⟩

theorem eq_top_of_transv [Finite V] (hV : ∀ v : V, v * v = 1) (H : Subgroup (MulAut V))
    (hirr : ∀ U : Subgroup V, (∀ h ∈ H, ∀ u ∈ U, h u ∈ U) → U = ⊥ ∨ U = ⊤)
    (A : Subgroup V) (hA : A.index = 2)
    (hX : ∀ σ : MulAut V, (∀ a ∈ A, σ a = a) → (∀ v, σ v * v⁻¹ ∈ A) → σ ∈ H) : H = ⊤ := by
  classical
  let _ := zmod2Module hV
  set K : Subgroup (Additive V ≃ₗ[ZMod 2] Additive V) := H.map linEquiv.toMonoidHom with hK
  set α₀ := axisForm A hA with hα₀
  set α : (⊤ : Submodule (ZMod 2) (Additive V)) →ₗ[ZMod 2] ZMod 2 :=
    α₀ ∘ₗ (⊤ : Submodule (ZMod 2) (Additive V)).subtype with hα
  have hirrK : G11.IsIrr K ⊤ := by
    refine ⟨fun k _ u _ => Submodule.mem_top, ?_, ?_⟩
    · rw [bot_lt_iff_ne_bot]
      intro h0
      have hA1 : A ≠ ⊤ := by
        intro h1
        rw [h1, Subgroup.index_top] at hA
        exact absurd hA (by norm_num)
      obtain ⟨v, -, hv⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr hA1)
      have : Additive.ofMul v ∈ (⊤ : Submodule (ZMod 2) (Additive V)) := Submodule.mem_top
      rw [h0, Submodule.mem_bot] at this
      exact hv (by rw [show v = 1 from Additive.ofMul.injective this]; exact A.one_mem)
    · intro J hJ _ _
      let U : Subgroup V :=
        { carrier := {v | Additive.ofMul v ∈ J}
          one_mem' := J.zero_mem
          mul_mem' := fun {a b} ha hb => by
            show Additive.ofMul a + Additive.ofMul b ∈ J
            exact J.add_mem ha hb
          inv_mem' := fun {a} ha => by
            show -Additive.ofMul a ∈ J
            exact J.neg_mem ha }
      have hU : ∀ h ∈ H, ∀ u ∈ U, h u ∈ U := fun h hh u hu =>
        hJ (linEquiv h) ⟨h, hh, rfl⟩ _ hu
      rcases hirr U hU with h0 | h0
      · left
        rw [eq_bot_iff]
        intro w hw
        have : Additive.toMul w ∈ U := hw
        rw [h0, Subgroup.mem_bot] at this
        rw [Submodule.mem_bot]
        exact Additive.toMul.injective this
      · right
        rw [eq_top_iff]
        intro w _
        have : Additive.toMul w ∈ U := by rw [h0]; exact Subgroup.mem_top _
        exact this
  have hα0 : α ≠ 0 := by
    intro h0
    have hA1 : A ≠ ⊤ := by
      intro h1
      rw [h1, Subgroup.index_top] at hA
      exact absurd hA (by norm_num)
    obtain ⟨v, -, hv⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr hA1)
    apply hv
    have h1 : α₀ (Additive.ofMul v) = 0 :=
      LinearMap.congr_fun h0 ⟨Additive.ofMul v, Submodule.mem_top⟩
    exact (axisForm_eq_zero A hA (Additive.ofMul v)).mp h1
  have hfull : ∀ a : (⊤ : Submodule (ZMod 2) (Additive V)), α a = 0 →
      ∃ k ∈ K, ∀ u : (⊤ : Submodule (ZMod 2) (Additive V)),
        k (u : Additive V) = (u : Additive V) + α u • (a : Additive V) := by
    intro a ha
    have ha' : α₀ (a : Additive V) = 0 := ha
    have haA : Additive.toMul (a : Additive V) ∈ A := (axisForm_eq_zero A hA _).mp ha'
    let t : Additive V ≃ₗ[ZMod 2] Additive V := LinearEquiv.transvection ha'
    refine ⟨t, ⟨linEquiv.symm t, hX _ ?_ ?_, by simp⟩, fun u => rfl⟩
    · intro b hb
      show Additive.toMul (t (Additive.ofMul b)) = b
      have h0 : α₀ (Additive.ofMul b) = 0 := (axisForm_eq_zero A hA _).mpr hb
      rw [transvection_apply, h0, zero_smul, add_zero]
      rfl
    · intro v
      show Additive.toMul (t (Additive.ofMul v)) * v⁻¹ ∈ A
      rw [transvection_apply]
      by_cases hv : v ∈ A
      · have h0 : α₀ (Additive.ofMul v) = 0 := (axisForm_eq_zero A hA _).mpr hv
        rw [h0, zero_smul, add_zero]
        simp [A.one_mem]
      · have h1 : α₀ (Additive.ofMul v) = 1 := by
          rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (α₀ (Additive.ofMul v)) with h | h
          · exact absurd ((axisForm_eq_zero A hA _).mp h) hv
          · exact h
        rw [h1, one_smul]
        simpa [mul_comm] using haA
  have hall := G11.autAll_of_fullTransvections K ⊤ hirrK α hα0 hfull
  rw [eq_top_iff]
  intro g _
  obtain ⟨k, hk, hkg⟩ := hall ((LinearEquiv.ofTop ⊤ rfl).trans
    ((linEquiv g).trans (LinearEquiv.ofTop ⊤ rfl).symm))
  have hkeq : k = linEquiv g := LinearEquiv.ext fun w => by
    have := hkg ⟨w, Submodule.mem_top⟩
    rw [this]
    rfl
  obtain ⟨h, hh, hhk⟩ := hk
  have : h = g := linEquiv.injective (by rw [← hkeq, ← hhk]; rfl)
  rw [← this]
  exact hh

end CFSG.Quasithin.MulAutTwo
