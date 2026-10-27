module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem11C
public import CFSG.Quasithin.Vol2.Ch10SecDTL
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13

variable {E : Type*} [CommGroup E] [Finite E]

theorem exists_hom_sep_ch611 (hE : ∀ u : E, u ^ 2 = 1) {W : Subgroup E} {x : E} (hx : x ∉ W) :
    ∃ f : E →* Multiplicative (ZMod 2), (∀ w ∈ W, f w = 1) ∧ f x ≠ 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : ∀ y : Additive E, (2 : ℕ) • y = 0 := fun y => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, hE]
    rfl
  let _ : Module (ZMod 2) (Additive E) := AddCommGroup.zmodModule hA
  set p : Submodule (ZMod 2) (Additive E) :=
    { carrier := {y | Additive.toMul y ∈ W}
      add_mem' := fun ha hb => W.mul_mem ha hb
      zero_mem' := W.one_mem
      smul_mem' := fun c y hy => by
        have h2 : ∀ k : ℕ, Additive.toMul ((k : ZMod 2) • y) ∈ W := by
          intro k
          induction k with
          | zero => simp
          | succ k ih =>
            rw [Nat.cast_succ, add_smul, one_smul]
            exact W.mul_mem ih hy
        have := h2 c.val
        rwa [ZMod.natCast_zmod_val] at this } with hp
  have hxp : Additive.ofMul x ∉ p := hx
  obtain ⟨f, hf, hfp⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hxp inferInstance
  refine ⟨AddMonoidHom.toMultiplicativeRight f.toAddMonoidHom, fun w hw => ?_, ?_⟩
  · have : f (Additive.ofMul w) ∈ p.map f := ⟨Additive.ofMul w, hw, rfl⟩
    rw [hfp, Submodule.mem_bot] at this
    exact congrArg Multiplicative.ofAdd this
  · intro h1
    apply hf
    exact congrArg Multiplicative.toAdd h1

@[expose] noncomputable def transvAutCh611 (hE : ∀ u : E, u ^ 2 = 1)
    (f : E →* Multiplicative (ZMod 2)) {c : E} (hc : f c = 1) : MulAut E :=
  have hcc : c * c = 1 := by rw [← pow_two, hE]
  have hval : ∀ u : E, f u = 1 ∨ f u = Multiplicative.ofAdd 1 := by
    intro u
    rcases Fin.exists_fin_two.mp ⟨Multiplicative.toAdd (f u), rfl⟩ with h | h
    · left
      exact congrArg Multiplicative.ofAdd h
    · right
      exact congrArg Multiplicative.ofAdd h
  have hone : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
  let g : E → E := fun u => if f u = 1 then u else u * c
  have hgmul : ∀ u v, g (u * v) = g u * g v := by
    intro u v
    have hm : f (u * v) = f u * f v := map_mul f u v
    rcases hval u with hu | hu <;> rcases hval v with hv | hv
    · have : f (u * v) = 1 := by rw [hm, hu, hv, mul_one]
      simp only [g, this, hu, hv, ite_true]
    · have : f (u * v) ≠ 1 := by rw [hm, hu, hv, one_mul]; exact hone
      simp only [g, this, hu, hv, hone, ite_true, ite_false]
      rw [mul_assoc]
    · have : f (u * v) ≠ 1 := by rw [hm, hu, hv, mul_one]; exact hone
      simp only [g, this, hu, hv, hone, ite_true, ite_false]
      rw [mul_right_comm]
    · have : f (u * v) = 1 := by rw [hm, hu, hv]; decide
      simp only [g, this, hu, hv, hone, ite_true, ite_false]
      calc u * v = u * v * (c * c) := by rw [hcc, mul_one]
        _ = u * c * (v * c) := by rw [mul_mul_mul_comm]
  have hgg : ∀ u, g (g u) = u := by
    intro u
    rcases hval u with hu | hu
    · simp only [g, hu, ite_true]
    · have h1 : f (u * c) ≠ 1 := by rw [map_mul, hu, hc, mul_one]; exact hone
      simp only [g, hu, hone, ite_false, h1]
      rw [mul_assoc, hcc, mul_one]
  { toFun := g
    invFun := g
    left_inv := hgg
    right_inv := hgg
    map_mul' := hgmul }

omit [Finite E] in
theorem transvAutCh611_of_eq (hE : ∀ u : E, u ^ 2 = 1) (f : E →* Multiplicative (ZMod 2))
    {c : E} (hc : f c = 1) {u : E} (hu : f u = 1) : transvAutCh611 hE f hc u = u := by
  show (if f u = 1 then u else u * c) = u
  simp [hu]

omit [Finite E] in
theorem transvAutCh611_of_ne (hE : ∀ u : E, u ^ 2 = 1) (f : E →* Multiplicative (ZMod 2))
    {c : E} (hc : f c = 1) {u : E} (hu : f u ≠ 1) : transvAutCh611 hE f hc u = u * c := by
  show (if f u = 1 then u else u * c) = u * c
  simp [hu]

omit [Finite E] in
theorem isTransv_transvAutCh611 (hE : ∀ u : E, u ^ 2 = 1) (f : E →* Multiplicative (ZMod 2))
    {c : E} (hc : f c = 1) : IsTransvCh611 c (transvAutCh611 hE f hc) := by
  intro u
  by_cases hu : f u = 1
  · left
    rw [transvAutCh611_of_eq hE f hc hu, mul_inv_cancel]
  · right
    rw [transvAutCh611_of_ne hE f hc hu, mul_comm u c, mul_inv_cancel_right]

theorem exists_mulAut_apply_eq_ch611 (hE : ∀ u : E, u ^ 2 = 1) {x y : E} (hx : x ≠ 1)
    (hy : y ≠ 1) : ∃ φ : MulAut E, φ x = y := by
  by_cases hxy : x = y
  · exact ⟨1, hxy⟩
  have hxyc : x ∉ Subgroup.zpowers (x * y) := by
    intro h
    rcases (CFSG.Quasithin.Vol2.Ch10.SecD.mem_zpowers_iff_of_sq (hE (x * y))).mp h with h1 | h1
    · exact hx h1
    · apply hy
      have := congrArg (x⁻¹ * ·) h1
      simpa using this.symm
  obtain ⟨f, hf, hfx⟩ := exists_hom_sep_ch611 hE hxyc
  have hc : f (x * y) = 1 := hf _ (Subgroup.mem_zpowers _)
  refine ⟨transvAutCh611 hE f hc, ?_⟩
  rw [transvAutCh611_of_ne hE f hc hfx, ← mul_assoc, ← pow_two, hE, one_mul]

theorem exists_transv_move_ch611 (hE : ∀ u : E, u ^ 2 = 1) {x u : E} (hx : x ≠ 1)
    (hu : u ∉ Subgroup.zpowers x) :
    ∃ τ : MulAut E, IsTransvCh611 x τ ∧ τ u ≠ u := by
  obtain ⟨f, hf, hfu⟩ := exists_hom_sep_ch611 hE hu
  have hc : f x = 1 := hf x (Subgroup.mem_zpowers x)
  refine ⟨transvAutCh611 hE f hc, isTransv_transvAutCh611 hE f hc, ?_⟩
  rw [transvAutCh611_of_ne hE f hc hfu]
  intro h
  exact hx (by simpa using h)

theorem isTransv_of_comm_ch611 (hE : ∀ u : E, u ^ 2 = 1) {x : E} (hx : x ≠ 1) {g : MulAut E}
    (hg : ∀ τ : MulAut E, IsTransvCh611 x τ → g * τ = τ * g) : IsTransvCh611 x g := by
  intro u
  by_contra hcon
  push Not at hcon
  have hw : g u * u⁻¹ ∉ Subgroup.zpowers x := by
    intro h
    rcases (CFSG.Quasithin.Vol2.Ch10.SecD.mem_zpowers_iff_of_sq (hE x)).mp h with h1 | h1
    · exact hcon.1 h1
    · exact hcon.2 h1
  obtain ⟨f, hf, hfw⟩ := exists_hom_sep_ch611 hE hw
  have hc : f x = 1 := hf x (Subgroup.mem_zpowers x)
  set τ := transvAutCh611 hE f hc with hτ
  have h1 := congrArg (fun φ : MulAut E => φ u) (hg τ (isTransv_transvAutCh611 hE f hc))
  simp only [MulAut.mul_apply] at h1
  have hone : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
  have hval : ∀ v : E, f v = 1 ∨ f v = Multiplicative.ofAdd 1 := by
    intro v
    rcases Fin.exists_fin_two.mp ⟨Multiplicative.toAdd (f v), rfl⟩ with h | h
    · left
      exact congrArg Multiplicative.ofAdd h
    · right
      exact congrArg Multiplicative.ofAdd h
  have hfgu : f (g u) = f (g u * u⁻¹) * f u := by rw [← map_mul, inv_mul_cancel_right]
  have hx1 : g x ≠ 1 := fun h => hx (g.injective (h.trans (map_one g).symm))
  rcases hval u with hu | hu
  ·
    have hgu : f (g u) ≠ 1 := by rw [hfgu, hu, mul_one]; exact hfw
    rw [transvAutCh611_of_eq hE f hc hu, transvAutCh611_of_ne hE f hc hgu] at h1
    exact hx (by simpa using h1.symm)
  ·
    have hgu : f (g u) = 1 := by
      rcases hval (g u * u⁻¹) with h2 | h2
      · exact absurd h2 hfw
      · rw [hfgu, h2, hu]; decide
    rw [transvAutCh611_of_ne hE f hc (by rw [hu]; exact hone), transvAutCh611_of_eq hE f hc hgu,
      map_mul] at h1
    exact hx1 (by simpa using h1)

end CFSG.Quasithin.H13
