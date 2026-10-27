module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthPathsDefs
import CFSG.LocalAnalysis.StandardType.GGOrthRk1AllPairs

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.StandardType.OrthTorus

section Moves

variable {p r : ℕ}

@[expose] def omSupp (x : OmPlusIdx r) : Finset (Fin r) := {x.1.1.1, x.1.1.2}

theorem omSupp_eq_iff {x y : OmPlusIdx r} : omSupp x = omSupp y ↔ x.1 = y.1 := by
  constructor
  · intro h
    rcases x with ⟨⟨⟨a, b⟩, hab⟩, s⟩
    rcases y with ⟨⟨⟨c, d⟩, hcd⟩, t⟩
    have ha : a = c ∨ a = d := by
      have hmem : a ∈ omSupp (⟨⟨(c, d), hcd⟩, t⟩ : OmPlusIdx r) := by
        rw [← h]; simp [omSupp]
      simpa [omSupp] using hmem
    have hb : b = c ∨ b = d := by
      have hmem : b ∈ omSupp (⟨⟨(c, d), hcd⟩, t⟩ : OmPlusIdx r) := by
        rw [← h]; simp [omSupp]
      simpa [omSupp] using hmem
    have hc : c = a ∨ c = b := by
      have hmem : c ∈ omSupp (⟨⟨(a, b), hab⟩, s⟩ : OmPlusIdx r) := by
        rw [h]; simp [omSupp]
      simpa [omSupp] using hmem
    have hac : a = c := by
      rcases ha with h1 | h1
      · exact h1
      · rcases hc with h2 | h2
        · exact absurd (h2.trans h1) (ne_of_lt hcd)
        · exact absurd (by
            calc a < b := hab
              _ = c := h2.symm
              _ < d := hcd
              _ = a := h1.symm) (lt_irrefl a)
    have hbd : b = d := by
      rcases hb with h1 | h1
      · exact absurd (hac.trans h1.symm) (ne_of_lt hab)
      · exact h1
    exact Subtype.ext (Prod.ext hac hbd)
  · intro h
    cases x with
    | mk xp xs =>
      cases y with
      | mk yp ys =>
        simp only at h
        subst h
        rfl

theorem omPlusIdx_ext {x y : OmPlusIdx r} (hs : omSupp x = omSupp y) (hb : x.2 = y.2) :
    x = y := by
  exact Prod.ext (omSupp_eq_iff.mp hs) hb

@[expose] def omPerm (σ : Equiv.Perm (Fin r)) (x : OmPlusIdx r) : OmPlusIdx r :=
  if h : σ x.1.1.1 < σ x.1.1.2 then (⟨(σ x.1.1.1, σ x.1.1.2), h⟩, x.2)
  else (⟨(σ x.1.1.2, σ x.1.1.1), lt_of_le_of_ne (not_lt.mp h)
      (fun h' => ne_of_lt x.1.2 (σ.injective h'.symm))⟩, x.2)

theorem omSupp_omPerm (σ : Equiv.Perm (Fin r)) (x : OmPlusIdx r) :
    omSupp (omPerm σ x) = (omSupp x).image σ := by
  rcases x with ⟨⟨⟨a, b⟩, hab⟩, s⟩
  unfold omPerm
  split_ifs with h
  · simp only [omSupp, Finset.image_insert, Finset.image_singleton]
  · simp only [omSupp, Finset.image_insert, Finset.image_singleton]
    exact Finset.pair_comm (σ b) (σ a)

theorem omPerm_sign (σ : Equiv.Perm (Fin r)) (x : OmPlusIdx r) : (omPerm σ x).2 = x.2 := by
  unfold omPerm
  split_ifs <;> rfl

theorem omPerm_refl (σ : Equiv.Perm (Fin r)) (x : OmPlusIdx r) :
    omPlusRefl p (omPerm σ x) =
      SpCoord.permAut σ * omPlusRefl p x * (SpCoord.permAut σ)⁻¹ := by
  rcases x with ⟨⟨⟨a, b⟩, hab⟩, s⟩
  refine MulEquiv.ext fun f => funext fun k => ?_
  rw [MulAut.mul_apply, MulAut.mul_apply, SpCoord.permAut_apply, SpCoord.permAut_inv_apply]
  simp only [Function.comp_apply]
  by_cases h : σ a < σ b
  · rw [omPerm, dif_pos h]
    simp only [omPlusRefl_apply_coord, Equiv.Perm.coe_inv, Equiv.symm_apply_eq,
      Equiv.apply_symm_apply, Function.comp_apply]
  · rw [omPerm, dif_neg h]
    simp only [omPlusRefl_apply_coord, Equiv.Perm.coe_inv, Equiv.symm_apply_eq,
      Equiv.apply_symm_apply, Function.comp_apply]
    have habne : a ≠ b := ne_of_lt hab
    by_cases hka : k = σ a
    · subst hka
      have hne : σ a ≠ σ b := fun h' => habne (σ.injective h')
      simp [hne]
    · by_cases hkb : k = σ b
      · subst hkb
        simp [hka]
      · simp [hka, hkb]

@[expose] def omTog (i : Fin r) (x : OmPlusIdx r) : OmPlusIdx r :=
  (x.1, Bool.xor x.2 (decide (i ∈ omSupp x)))

theorem omSupp_omTog (i : Fin r) (x : OmPlusIdx r) : omSupp (omTog i x) = omSupp x := rfl

theorem omTog_sign (i : Fin r) (x : OmPlusIdx r) :
    (omTog i x).2 = Bool.xor x.2 (decide (i ∈ omSupp x)) := rfl

theorem omTog_refl (i : Fin r) (x : OmPlusIdx r) :
    omPlusRefl p (omTog i x) =
      SpCoord.sgnAut i * omPlusRefl p x * (SpCoord.sgnAut i)⁻¹ := by
  have hinv : (SpCoord.sgnAut i : MulAut (Fin r → Multiplicative (ZMod p)))⁻¹
      = SpCoord.sgnAut i := by
    have h := SpCoord.sgnAut_sq (p := p) i
    rw [pow_two] at h
    exact inv_eq_of_mul_eq_one_right h
  rw [hinv]
  rcases x with ⟨⟨⟨a, b⟩, hab⟩, s⟩
  have habne : a ≠ b := ne_of_lt hab
  refine MulEquiv.ext fun f => funext fun k => ?_
  simp only [omTog, omSupp, Finset.mem_insert, Finset.mem_singleton, MulAut.mul_apply,
    SpCoord.sgnAut_apply, Function.update_apply, omPlusRefl_apply_coord]
  rcases em (i = a) with hia | hia
  · rcases em (i = b) with hib | hib
    · exact absurd (hia ▸ hib) habne
    · cases s <;> rcases em (k = a) with hka | hka <;> rcases em (k = b) with hkb | hkb <;>
        simp_all [hia, habne.symm, hka, hkb, Bool.xor_true, Bool.xor_false, Bool.true_xor,
          Bool.false_xor]
  · rcases em (i = b) with hib | hib
    · cases s <;> rcases em (k = a) with hka | hka <;> rcases em (k = b) with hkb | hkb <;>
        simp_all [hib, habne, hka, hkb, Bool.xor_true, Bool.xor_false, Bool.true_xor,
          Bool.false_xor]
    · have hai : a ≠ i := fun h => hia h.symm
      have hbi : b ≠ i := fun h => hib h.symm
      cases s <;> rcases em (k = a) with hka | hka <;> rcases em (k = b) with hkb | hkb <;>
        rcases em (k = i) with hki | hki <;>
        simp_all [hai, hbi, hia, hib, hka, hkb, hki, Bool.xor_true, Bool.xor_false,
          Bool.true_xor, Bool.false_xor]

structure OmMove (p r : ℕ) where
  w : MulAut (Fin r → Multiplicative (ZMod p))
  f : OmPlusIdx r → OmPlusIdx r
  hw : w ∈ omSigned p r
  hf : ∀ x, omPlusRefl p (f x) = w * omPlusRefl p x * w⁻¹

namespace OmMove

@[expose] def id : OmMove p r where
  w := 1
  f := _root_.id
  hw := (omSigned p r).one_mem
  hf x := by simp

@[expose] def comp (m' m : OmMove p r) : OmMove p r where
  w := m'.w * m.w
  f := m'.f ∘ m.f
  hw := (omSigned p r).mul_mem m'.hw m.hw
  hf x := by
    simp only [Function.comp_apply, m'.hf, m.hf, mul_inv_rev, mul_assoc]

@[expose] def perm (σ : Equiv.Perm (Fin r)) : OmMove p r where
  w := SpCoord.permAut σ
  f := omPerm σ
  hw := Subgroup.subset_closure (Or.inl ⟨σ, rfl⟩)
  hf := omPerm_refl σ

@[expose] def tog (i : Fin r) : OmMove p r where
  w := SpCoord.sgnAut i
  f := omTog i
  hw := Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)
  hf := omTog_refl i

@[expose] def togIf (b : Bool) (i : Fin r) : OmMove p r :=
  if b then tog i else id

theorem comp_f (m' m : OmMove p r) (x : OmPlusIdx r) : (comp m' m).f x = m'.f (m.f x) := rfl

theorem perm_f (σ : Equiv.Perm (Fin r)) (x : OmPlusIdx r) :
    (perm (p := p) σ).f x = omPerm σ x := rfl

theorem omSupp_togIf_f (b : Bool) (i : Fin r) (x : OmPlusIdx r) :
    omSupp ((togIf (p := p) b i).f x) = omSupp x := by
  cases b
  · rfl
  · exact omSupp_omTog i x

theorem togIf_f_sign (b : Bool) (i : Fin r) (x : OmPlusIdx r) :
    ((togIf (p := p) b i).f x).2 = Bool.xor x.2 (b && decide (i ∈ omSupp x)) := by
  cases b
  · show x.2 = Bool.xor x.2 (false && decide (i ∈ omSupp x))
    simp
  · show (omTog i x).2 = Bool.xor x.2 (true && decide (i ∈ omSupp x))
    rw [omTog_sign]
    simp

end OmMove

end Moves

section Std

variable {r : ℕ}

theorem omSupp_omStd_chain (hr : 2 ≤ r) {k : Fin r} (h : k.val + 1 < r) :
    omSupp (omStd r hr k) = {k, ⟨k.val + 1, h⟩} := by
  unfold omStd
  rw [dif_pos h]
  rfl

theorem omStd_sign_chain (hr : 2 ≤ r) {k : Fin r} (h : k.val + 1 < r) :
    (omStd r hr k).2 = false := by
  unfold omStd
  rw [dif_pos h]

theorem omSupp_omStd_last (hr : 2 ≤ r) {k : Fin r} (h : ¬ k.val + 1 < r) :
    omSupp (omStd r hr k) = {⟨r - 2, by omega⟩, ⟨r - 1, by omega⟩} := by
  unfold omStd
  rw [dif_neg h]
  rfl

theorem omStd_sign_last (hr : 2 ≤ r) {k : Fin r} (h : ¬ k.val + 1 < r) :
    (omStd r hr k).2 = true := by
  unfold omStd
  rw [dif_neg h]

end Std

end CFSG.StandardType.QTwo

end
