module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H8

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Matrix

variable {n : ℕ}

@[expose] def matOf (F : (Fin n → ZMod 2) → (Fin n → ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  Matrix.of fun i j => F (Pi.single j 1) i

theorem matOf_mulVec {F : (Fin n → ZMod 2) → (Fin n → ZMod 2)}
    (hF : ∀ x y, F (x + y) = F x + F y) (x : Fin n → ZMod 2) : matOf F *ᵥ x = F x := by
  have hF0 : F 0 = 0 := by
    have h := hF 0 0
    rw [add_zero] at h
    calc F 0 = F 0 + F 0 + F 0 := by rw [add_assoc, add_self_vec, add_zero]
      _ = 0 := by rw [← h, add_self_vec]
  set Fh : (Fin n → ZMod 2) →+ (Fin n → ZMod 2) := AddMonoidHom.mk' F hF with hFh
  have hx : x = ∑ j, x j • Pi.single j (1 : ZMod 2) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hsc : ∀ j, F (x j • Pi.single j (1 : ZMod 2)) = x j • F (Pi.single j 1) := fun j => by
    rcases zmod2_cases (x j) with h | h <;> rw [h]
    · rw [zero_smul, zero_smul, hF0]
    · rw [one_smul, one_smul]
  have h1 : F x = ∑ j, x j • F (Pi.single j 1) := by
    conv_lhs => rw [hx]
    rw [show F (∑ j, x j • Pi.single j (1 : ZMod 2)) = Fh (∑ j, x j • Pi.single j (1 : ZMod 2))
      from rfl, map_sum]
    exact Finset.sum_congr rfl fun j _ => hsc j
  rw [h1]
  ext i
  simp [matOf, mulVec, dotProduct, Finset.sum_apply, mul_comm]

variable {v₀ : Fin n → ZMod 2}

theorem mem_stabV_of_map (α : MulAut (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)))
    (hα : ∀ x ∈ stabV v₀, α x ∈ stabV v₀) {x : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)}
    (hx : α x ∈ stabV v₀) : x ∈ stabV v₀ := by
  have hle : (stabV v₀).map α.toMonoidHom ≤ stabV v₀ := by
    rintro _ ⟨y, hy, rfl⟩
    exact hα y hy
  have heq : (stabV v₀).map α.toMonoidHom = stabV v₀ :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective α.injective])
  rw [← heq] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  rwa [← α.injective hyx]

@[expose] noncomputable def autVec (hv₀ : v₀ ≠ 0)
    (α : MulAut (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) (v : Fin n → ZMod 2) :
    Fin n → ZMod 2 :=
  if hv : v = 0 then 0 else α (Classical.choose (exists_mulVec_eq hv₀ hv)) • v₀

section Aut

variable {hv₀ : v₀ ≠ 0} {α : MulAut (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))}

theorem autVec_zero : autVec hv₀ α 0 = 0 := by
  simp [autVec]

theorem autVec_of_ne {v : Fin n → ZMod 2} (hv : v ≠ 0) :
    autVec hv₀ α v = α (Classical.choose (exists_mulVec_eq hv₀ hv)) • v₀ := by
  simp [autVec, hv]

theorem autVec_smul (hα : ∀ x ∈ stabV v₀, α x ∈ stabV v₀)
    (g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) : autVec hv₀ α (g • v₀) = α g • v₀ := by
  have hv : g • v₀ ≠ 0 := mulVec_ne_zero g hv₀
  rw [autVec_of_ne hv]
  set g' := Classical.choose (exists_mulVec_eq hv₀ hv)
  have hg' : g' • v₀ = g • v₀ := Classical.choose_spec (exists_mulVec_eq hv₀ hv)
  have hs : g⁻¹ * g' ∈ stabV v₀ := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, hg', inv_smul_smul]
  have hs' := MulAction.mem_stabilizer_iff.mp (hα _ hs)
  rw [map_mul, map_inv, mul_smul, inv_smul_eq_iff] at hs'
  exact hs'

theorem autVec_equivariant (hα : ∀ x ∈ stabV v₀, α x ∈ stabV v₀)
    (h : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) (v : Fin n → ZMod 2) :
    autVec hv₀ α (h • v) = α h • autVec hv₀ α v := by
  by_cases hv : v = 0
  · rw [hv, smul_zero, autVec_zero, smul_zero]
  obtain ⟨g, hg⟩ := exists_mulVec_eq hv₀ hv
  have hg' : g • v₀ = v := hg
  rw [← hg', smul_smul, autVec_smul hα, autVec_smul hα, map_mul, mul_smul]

theorem autVec_ne_zero {v : Fin n → ZMod 2} (hv : v ≠ 0) : autVec hv₀ α v ≠ 0 := by
  rw [autVec_of_ne hv]
  exact mulVec_ne_zero _ hv₀

theorem autVec_injective (hα : ∀ x ∈ stabV v₀, α x ∈ stabV v₀) :
    Function.Injective (autVec hv₀ α) := by
  intro v w hvw
  by_cases hv : v = 0
  · by_contra hne
    rw [hv, autVec_zero] at hvw
    exact autVec_ne_zero (fun hw => hne (hv.trans hw.symm)) hvw.symm
  by_cases hw : w = 0
  · rw [hw, autVec_zero] at hvw
    exact absurd hvw (autVec_ne_zero hv)
  obtain ⟨g, hg⟩ := exists_mulVec_eq hv₀ hv
  obtain ⟨g', hg'⟩ := exists_mulVec_eq hv₀ hw
  have e1 : g • v₀ = v := hg
  have e2 : g' • v₀ = w := hg'
  rw [← e1, ← e2, autVec_smul hα, autVec_smul hα] at hvw
  have hs : α (g⁻¹ * g') ∈ stabV v₀ := by
    rw [MulAction.mem_stabilizer_iff, map_mul, map_inv, mul_smul, ← hvw, inv_smul_smul]
  have hs' := MulAction.mem_stabilizer_iff.mp (mem_stabV_of_map α hα hs)
  rw [mul_smul, inv_smul_eq_iff] at hs'
  rw [← e1, ← e2, hs']

theorem autVec_add (hα : ∀ x ∈ stabV v₀, α x ∈ stabV v₀) (a b : Fin n → ZMod 2) :
    autVec hv₀ α (a + b) = autVec hv₀ α a + autVec hv₀ α b := by
  by_cases ha : a = 0
  · rw [ha, zero_add, autVec_zero, zero_add]
  by_cases hb : b = 0
  · rw [hb, add_zero, autVec_zero, add_zero]
  by_cases hab : a = b
  · rw [hab, add_self_vec, autVec_zero, add_self_vec]
  by_contra hne
  have hab0 : a + b ≠ 0 := fun h => hab (eq_of_add_eq_zero_vec h)
  have hCA : autVec hv₀ α (a + b) ≠ autVec hv₀ α a := fun h => hb (by
    have h' := autVec_injective hα h
    calc b = a + b + a := by rw [add_comm a b, add_assoc, add_self_vec, add_zero]
      _ = 0 := by rw [h', add_self_vec])
  have hCB : autVec hv₀ α (a + b) ≠ autVec hv₀ α b := fun h => ha (by
    have h' := autVec_injective hα h
    calc a = a + b + b := by rw [add_assoc, add_self_vec, add_zero]
      _ = 0 := by rw [h', add_self_vec])
  obtain ⟨h', h1, h2, h3⟩ := exists_fix_fix_move (autVec_ne_zero ha) (autVec_ne_zero hab0) hCA
    hCB hne
  have hαh : α (α.symm h') = h' := α.apply_symm_apply h'
  have hfa : α.symm h' • a = a :=
    autVec_injective hα (by rw [autVec_equivariant hα, hαh]; exact h1)
  have hfb : α.symm h' • b = b :=
    autVec_injective hα (by rw [autVec_equivariant hα, hαh]; exact h2)
  apply h3
  have := autVec_equivariant (hv₀ := hv₀) hα (α.symm h') (a + b)
  rw [smul_add, hfa, hfb, hαh] at this
  exact this.symm

end Aut

theorem mat_ext_mulVec {M N : Matrix (Fin n) (Fin n) (ZMod 2)} (h : ∀ x, M *ᵥ x = N *ᵥ x) :
    M = N := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [mulVec_single_one] using this

theorem eq_conj_of_stabV (hv₀ : v₀ ≠ 0) (α : MulAut (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)))
    (hα : ∀ x ∈ stabV v₀, α x ∈ stabV v₀) :
    ∃ g ∈ stabV v₀, ∀ x, α x = g * x * g⁻¹ := by
  have hadd := autVec_add (hv₀ := hv₀) hα
  have hbij : Function.Bijective (autVec hv₀ α) := (autVec_injective hα).bijective_of_finite
  have hinv : ∀ x, autVec hv₀ α (Function.invFun (autVec hv₀ α) x) = x :=
    Function.rightInverse_invFun hbij.2
  have hinv_add : ∀ x y, Function.invFun (autVec hv₀ α) (x + y) =
      Function.invFun (autVec hv₀ α) x + Function.invFun (autVec hv₀ α) y := fun x y =>
    hbij.1 (by rw [hinv, hadd, hinv, hinv])
  have hG := matOf_mulVec hadd
  have hG' := matOf_mulVec hinv_add
  have hGG' : matOf (autVec hv₀ α) * matOf (Function.invFun (autVec hv₀ α)) = 1 :=
    mat_ext_mulVec fun x => by rw [← mulVec_mulVec, hG', hG, hinv, one_mulVec]
  have hdet : (matOf (autVec hv₀ α)).det = 1 := by
    have h := congrArg Matrix.det hGG'
    rw [det_mul, det_one] at h
    rcases zmod2_cases (matOf (autVec hv₀ α)).det with h0 | h1
    · rw [h0, zero_mul] at h
      exact absurd h zero_ne_one
    · exact h1
  set g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2) := ⟨matOf (autVec hv₀ α), hdet⟩ with hg
  have hgv : ∀ x, g • x = autVec hv₀ α x := hG
  refine ⟨g, ?_, fun x => ?_⟩
  · rw [MulAction.mem_stabilizer_iff, hgv]
    have h1 := autVec_smul (hv₀ := hv₀) hα 1
    rwa [one_smul, map_one, one_smul] at h1
  · have hc : α x * g = g * x := ext_mulVec fun y => by
      show (α x * g) • y = (g * x) • y
      rw [mul_smul, mul_smul, hgv, hgv, autVec_equivariant hα]
    calc α x = α x * g * g⁻¹ := by group
      _ = g * x * g⁻¹ := by rw [hc]

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
