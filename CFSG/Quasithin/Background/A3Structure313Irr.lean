module

public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.A313

open Matrix

def upperTri (p : ℕ) : Subgroup (SpecialLinearGroup (Fin 2) (ZMod p)) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two] at ha hb ⊢
    rw [ha, hb]
    ring
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] at ha ⊢
    simp [ha]

theorem mem_upperTri {p : ℕ} {g : SpecialLinearGroup (Fin 2) (ZMod p)} :
    g ∈ upperTri p ↔ (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0 := Iff.rfl

variable {p : ℕ}

theorem mul_diag_eq_one {g : SpecialLinearGroup (Fin 2) (ZMod p)} (hg : g ∈ upperTri p) :
    (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 * (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1 = 1 := by
  have h := g.2
  rw [Matrix.det_fin_two, mem_upperTri.mp hg] at h
  simpa using h

def diagChar (p : ℕ) : ↥(upperTri p) →* (ZMod p)ˣ where
  toFun g := ⟨(g.1 : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0,
    (g.1 : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1,
    mul_diag_eq_one g.2, by rw [mul_comm]; exact mul_diag_eq_one g.2⟩
  map_one' := by
    apply Units.ext
    simp
  map_mul' := by
    intro a b
    apply Units.ext
    have hb := mem_upperTri.mp b.2
    simp [Matrix.mul_apply, Fin.sum_univ_two, hb]

theorem isSolvable_upperTri : Group.IsSolvable ↥(upperTri p) := by
  have hker : ∀ a b : ↥(diagChar p).ker, a * b = b * a := by
    intro a b
    have ha := (MonoidHom.mem_ker.mp a.2)
    have hb := (MonoidHom.mem_ker.mp b.2)
    have ha1 := congrArg Units.val ha
    have hb1 := congrArg Units.val hb
    simp only [diagChar, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_one] at ha1 hb1
    have ha2 : (a.1.1 : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1 = 1 := by
      have := mul_diag_eq_one a.1.2
      rw [ha1] at this
      simpa using this
    have hb2 : (b.1.1 : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1 = 1 := by
      have := mul_diag_eq_one b.1.2
      rw [hb1] at this
      simpa using this
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    have h10a := mem_upperTri.mp a.1.2
    have h10b := mem_upperTri.mp b.1.2
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ha1, hb1, ha2, hb2, h10a, h10b, add_comm]
  have h1 : Group.IsSolvable ↥(diagChar p).ker := Group.isSolvable_of_comm hker
  have h2 : Group.IsSolvable (ZMod p)ˣ := Group.isSolvable_of_comm (fun a b => mul_comm a b)
  exact Group.isSolvable_of_ker_le_range (diagChar p).ker.subtype (diagChar p) (by
    intro x hx
    exact ⟨⟨x, hx⟩, rfl⟩)

theorem exists_mulVec_single_eq [Fact p.Prime] {w : Fin 2 → ZMod p} (hw : w ≠ 0) :
    ∃ s : SpecialLinearGroup (Fin 2) (ZMod p),
      (s : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ (Pi.single 0 1 : Fin 2 → ZMod p) = w := by
  by_cases h0 : w 0 = 0
  · have h1 : w 1 ≠ 0 := by
      intro h1
      apply hw
      ext i
      fin_cases i <;> simp [h0, h1]
    refine ⟨⟨!![w 0, -(w 1)⁻¹; w 1, 0], ?_⟩, ?_⟩
    · rw [Matrix.det_fin_two]
      simp [h0]
      field_simp
    · ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · refine ⟨⟨!![w 0, 0; w 1, (w 0)⁻¹], ?_⟩, ?_⟩
    · rw [Matrix.det_fin_two]
      simp [h0]
    · ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem isSolvable_of_stabilizes [Fact p.Prime] (M : Subgroup (SpecialLinearGroup (Fin 2) (ZMod p)))
    {w : Fin 2 → ZMod p} (hw : w ≠ 0)
    (h : ∀ g ∈ M, ∃ c : ZMod p, (g : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ w = c • w) :
    Group.IsSolvable ↥M := by
  obtain ⟨s, hs⟩ := exists_mulVec_single_eq hw
  have hmem : ∀ g : ↥M, s⁻¹ * (g : SpecialLinearGroup (Fin 2) (ZMod p)) * s ∈ upperTri p := by
    intro g
    obtain ⟨c, hc⟩ := h g g.2
    rw [mem_upperTri]
    have h1 : ((s⁻¹ * (g : SpecialLinearGroup (Fin 2) (ZMod p)) * s : SpecialLinearGroup (Fin 2)
        (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ (Pi.single 0 1 : Fin 2 → ZMod p) =
        c • (Pi.single 0 1 : Fin 2 → ZMod p) := by
      simp only [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
      rw [hs, hc, Matrix.mulVec_smul]
      have : ((s⁻¹ : SpecialLinearGroup (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ w =
          (Pi.single 0 1 : Fin 2 → ZMod p) := by
        rw [← hs, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
          Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
      rw [this]
    have h2 := congrFun h1 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h2
  let φ : ↥M →* ↥(upperTri p) :=
    (((MulAut.conj s⁻¹ : MulAut (SpecialLinearGroup (Fin 2) (ZMod p)))).toMonoidHom.comp
      M.subtype).codRestrict (upperTri p) (by
        intro g
        have := hmem g
        simpa [MulAut.conj_apply, mul_assoc] using this)
  have hinj : Function.Injective φ := by
    intro a b hab
    have : s⁻¹ * (a : SpecialLinearGroup (Fin 2) (ZMod p)) * s⁻¹⁻¹ =
        s⁻¹ * (b : SpecialLinearGroup (Fin 2) (ZMod p)) * s⁻¹⁻¹ := congrArg Subtype.val hab
    apply Subtype.ext
    simpa using this
  have := isSolvable_upperTri (p := p)
  exact Group.isSolvable_of_isSolvable_injective hinj

theorem eq_bot_or_eq_of_natural [Fact p.Prime] {Λ : Type} [Group Λ] (F : Subgroup Λ) [F.Normal]
    (e : F ≃* Multiplicative (Fin 2 → ZMod p))
    (ψ : Λ →* SpecialLinearGroup (Fin 2) (ZMod p))
    (hact : ∀ (x : Λ) (f : F), e (MulAut.conjNormal x f) =
      Multiplicative.ofAdd ((ψ x : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ
        Multiplicative.toAdd (e f)))
    (H K : Subgroup Λ) (hKF : K ≤ F) (hHK : H ≤ Subgroup.normalizer (K : Set Λ))
    (hsolv : ¬ Group.IsSolvable ↥(H.map ψ)) : K = ⊥ ∨ K = F := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hKbot, hKF'⟩ := hcon
  let S : Set (Fin 2 → ZMod p) := {v | ∃ k : F, (k : Λ) ∈ K ∧ e k = Multiplicative.ofAdd v}
  have hS0 : (0 : Fin 2 → ZMod p) ∈ S := ⟨1, K.one_mem, by simp⟩
  have hSadd : ∀ v ∈ S, ∀ w ∈ S, v + w ∈ S := by
    rintro v ⟨k, hk, hkv⟩ w ⟨l, hl, hlw⟩
    refine ⟨k * l, K.mul_mem hk hl, ?_⟩
    rw [map_mul, hkv, hlw]
    rfl
  have hSneg : ∀ v ∈ S, -v ∈ S := by
    rintro v ⟨k, hk, hkv⟩
    refine ⟨k⁻¹, K.inv_mem hk, ?_⟩
    rw [map_inv, hkv]
    rfl
  have hSnsmul : ∀ (n : ℕ), ∀ v ∈ S, n • v ∈ S := by
    intro n
    induction n with
    | zero => intro v _; simpa using hS0
    | succ n ih =>
      intro v hv
      rw [succ_nsmul]
      exact hSadd _ (ih v hv) v hv
  have hSsmul : ∀ (c : ZMod p), ∀ v ∈ S, c • v ∈ S := by
    intro c v hv
    have : c • v = c.val • v := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod p) c.val, ZMod.natCast_zmod_val]
    rw [this]
    exact hSnsmul _ v hv
  obtain ⟨k, hkK, hk1⟩ : ∃ k ∈ K, k ≠ 1 := by
    by_contra hc
    push Not at hc
    exact hKbot (Subgroup.eq_bot_iff_forall K |>.mpr hc)
  obtain ⟨f, hfF, hfK⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hKF hKF')
  have hwS : Multiplicative.toAdd (e ⟨k, hKF hkK⟩) ∈ S :=
    ⟨⟨k, hKF hkK⟩, hkK, by simp⟩
  have hw0 : Multiplicative.toAdd (e ⟨k, hKF hkK⟩) ≠ 0 := by
    intro h0
    apply hk1
    have : e ⟨k, hKF hkK⟩ = 1 := by
      have := congrArg Multiplicative.ofAdd h0
      simpa using this
    have h2 : (⟨k, hKF hkK⟩ : F) = 1 := (MulEquiv.map_eq_one_iff e).mp this
    exact congrArg Subtype.val h2
  have huS : Multiplicative.toAdd (e ⟨f, hfF⟩) ∉ S := by
    rintro ⟨l, hl, hle⟩
    apply hfK
    have : l = ⟨f, hfF⟩ := e.injective (by simpa using hle)
    have h2 : (l : Λ) = f := congrArg Subtype.val this
    rw [h2] at hl
    exact hl
  set w := Multiplicative.toAdd (e ⟨k, hKF hkK⟩) with hw
  set u := Multiplicative.toAdd (e ⟨f, hfF⟩) with hu
  have hinv : ∀ h ∈ H, ∀ v ∈ S, (ψ h : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ v ∈ S := by
    intro h hh v hv
    obtain ⟨l, hl, hlv⟩ := hv
    refine ⟨MulAut.conjNormal h l, ?_, ?_⟩
    · have h1 : (h * (l : Λ) * h⁻¹) ∈ K := (Subgroup.mem_normalizer_iff.mp (hHK hh) l).mp hl
      simpa [MulAut.conjNormal_apply] using h1
    · rw [hact, hlv]
      simp
  have hline : ∀ s ∈ S, ∃ c : ZMod p, s = c • w := by
    intro s hs
    by_contra hnot
    push Not at hnot
    have hD : w 0 * s 1 - w 1 * s 0 ≠ 0 := by
      intro hD
      by_cases hw0' : w 0 = 0
      · have hw1 : w 1 ≠ 0 := by
          intro hw1
          apply hw0
          ext i
          fin_cases i <;> simp [hw0', hw1]
        have hs0 : s 0 = 0 := by
          rw [hw0'] at hD
          have : w 1 * s 0 = 0 := by linear_combination -hD
          exact (mul_eq_zero.mp this).resolve_left hw1
        refine hnot (s 1 / w 1) ?_
        ext i
        fin_cases i <;> simp [hs0, hw0', hw1]
      · refine hnot (s 0 / w 0) ?_
        ext i
        fin_cases i
        · simp [hw0']
        · have : w 0 * s 1 = w 1 * s 0 := by linear_combination hD
          simp
          field_simp
          linear_combination this
    apply huS
    have e0 : u 0 = ((u 0 * s 1 - u 1 * s 0) / (w 0 * s 1 - w 1 * s 0)) * w 0 +
        ((w 0 * u 1 - w 1 * u 0) / (w 0 * s 1 - w 1 * s 0)) * s 0 := by
      rw [show ((u 0 * s 1 - u 1 * s 0) / (w 0 * s 1 - w 1 * s 0)) * w 0 +
        ((w 0 * u 1 - w 1 * u 0) / (w 0 * s 1 - w 1 * s 0)) * s 0 =
        ((u 0 * s 1 - u 1 * s 0) * w 0 + (w 0 * u 1 - w 1 * u 0) * s 0) /
          (w 0 * s 1 - w 1 * s 0) by ring, eq_div_iff hD]
      ring
    have e1 : u 1 = ((u 0 * s 1 - u 1 * s 0) / (w 0 * s 1 - w 1 * s 0)) * w 1 +
        ((w 0 * u 1 - w 1 * u 0) / (w 0 * s 1 - w 1 * s 0)) * s 1 := by
      rw [show ((u 0 * s 1 - u 1 * s 0) / (w 0 * s 1 - w 1 * s 0)) * w 1 +
        ((w 0 * u 1 - w 1 * u 0) / (w 0 * s 1 - w 1 * s 0)) * s 1 =
        ((u 0 * s 1 - u 1 * s 0) * w 1 + (w 0 * u 1 - w 1 * u 0) * s 1) /
          (w 0 * s 1 - w 1 * s 0) by ring, eq_div_iff hD]
      ring
    have hid : u = ((u 0 * s 1 - u 1 * s 0) / (w 0 * s 1 - w 1 * s 0)) • w +
        ((w 0 * u 1 - w 1 * u 0) / (w 0 * s 1 - w 1 * s 0)) • s := by
      ext i
      fin_cases i
      · simpa using e0
      · simpa using e1
    rw [hid]
    exact hSadd _ (hSsmul _ _ hwS) _ (hSsmul _ _ hs)
  refine hsolv (isSolvable_of_stabilizes (H.map ψ) hw0 ?_)
  rintro g ⟨h, hh, rfl⟩
  obtain ⟨c, hc⟩ := hline _ (hinv h hh w hwS)
  exact ⟨c, hc⟩

end CFSG.Quasithin.A313
