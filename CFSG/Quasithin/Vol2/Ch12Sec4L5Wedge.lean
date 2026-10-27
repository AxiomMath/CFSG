module

public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitL52Rep
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitCount

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.JonesParshall.Curtis
open Orbit
open scoped Matrix Pointwise

@[expose] def Indep3 (x y z : Fin 10 → ZMod 2) : Prop :=
  x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ x + y ≠ 0 ∧ x + z ≠ 0 ∧ y + z ≠ 0 ∧ x + y + z ≠ 0

instance (x y z : Fin 10 → ZMod 2) : Decidable (Indep3 x y z) := by
  unfold Indep3
  infer_instance

theorem linearIndependent_of_indep3 {x y z : Fin 10 → ZMod 2} (h : Indep3 x y z) :
    LinearIndependent (ZMod 2) ![x, y, z] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_three] at hg
  change g 0 • x + g 1 • y + g 2 • z = 0 at hg
  have hcases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  obtain ⟨hx, hy, hz, hxy, hxz, hyz, hxyz⟩ := h
  rcases hcases (g 0) with h0 | h0 <;> rcases hcases (g 1) with h1 | h1 <;>
    rcases hcases (g 2) with h2 | h2 <;>
    simp only [h0, h1, h2, zero_smul, one_smul, zero_add, add_zero] at hg
  · intro i
    fin_cases i <;> simp [h0, h1, h2]
  · exact absurd hg hz
  · exact absurd hg hy
  · exact absurd hg hyz
  · exact absurd hg hx
  · exact absurd hg hxz
  · exact absurd hg hxy
  · exact absurd hg hxyz

theorem mulVec_single_one' (A : Matrix (Fin 10) (Fin 10) (ZMod 2)) (i : Fin 10) :
    A *ᵥ Pi.single i 1 = fun r => A r i := by
  ext r
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem card_fix_le_of_indep3 (M : Matrix (Fin 10) (Fin 10) (ZMod 2)) {i j k : Fin 10}
    (h : Indep3 (fun r => (M - 1) r i) (fun r => (M - 1) r j) (fun r => (M - 1) r k)) :
    Nat.card {w : Fin 10 → ZMod 2 // M *ᵥ w = w} ≤ 2 ^ 7 := by
  set f := Matrix.mulVecLin (M - 1) with hf
  have hfx : ∀ l : Fin 10, (fun r => (M - 1) r l) ∈ LinearMap.range f := fun l =>
    ⟨Pi.single l 1, by rw [hf, Matrix.mulVecLin_apply, mulVec_single_one']⟩
  have e : {w : Fin 10 → ZMod 2 // M *ᵥ w = w} ≃ ↥(LinearMap.ker f) :=
    { toFun := fun w => ⟨w.1, by
        rw [LinearMap.mem_ker, hf, Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec,
          w.2, sub_self]⟩
      invFun := fun w => ⟨w.1, by
        have h1 : (M - 1) *ᵥ (w.1 : Fin 10 → ZMod 2) = 0 := LinearMap.mem_ker.1 w.2
        rw [Matrix.sub_mulVec, Matrix.one_mulVec] at h1
        exact sub_eq_zero.1 h1⟩
      left_inv := fun w => rfl
      right_inv := fun w => rfl }
  rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hli := linearIndependent_of_indep3 h
  have hspan : Submodule.span (ZMod 2) (Set.range ![(fun r => (M - 1) r i),
      (fun r => (M - 1) r j), (fun r => (M - 1) r k)]) ≤ LinearMap.range f := by
    rw [Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    fin_cases l
    · exact hfx i
    · exact hfx j
    · exact hfx k
  have h3 := (finrank_span_eq_card hli).symm.trans_le (Submodule.finrank_mono hspan)
  rw [Fintype.card_fin] at h3
  have hsum := LinearMap.finrank_range_add_finrank_ker f
  rw [Module.finrank_fin_fun] at hsum
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem upU_wedge_cert : ∀ c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ : ZMod 2,
    upMat c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ * upMat c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ = 1 →
    upMat c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ ≠ 1 →
    ∃ i j k : Fin 10,
      Indep3 (fun r => (wedgeMat (upMat c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉) - 1) r i)
        (fun r => (wedgeMat (upMat c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉) - 1) r j)
        (fun r => (wedgeMat (upMat c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉) - 1) r k) := by
  decide +kernel

theorem wedgeRep_apply' (g : G5) (w : Fin 10 → ZMod 2) :
    wedgeRep g w = wedgeMat (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ w :=
  muW_apply (ZMod 2) g w

theorem card_fix_wedgeRep_le {g : G5} (hg1 : g ≠ 1) (hg2 : g * g = 1) :
    Nat.card {w : Fin 10 → ZMod 2 // wedgeRep g w = w} ≤ 2 ^ 7 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf g = 2 := orderOf_eq_prime (by rw [pow_two, hg2]) hg1
  have hQp : IsPGroup 2 (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  obtain ⟨P, hP⟩ := hQp.exists_le_sylow
  have hUi : ¬ 2 ∣ Ugrp.index := by
    have h := Ugrp.index_mul_card
    rw [card_Ugrp, card_G5] at h
    generalize Ugrp.index = n at h ⊢
    have h' : n * 1024 = 9999360 := by rw [← h]; norm_num
    have h9765 : n = 9765 := by omega
    subst h9765
    decide
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G5 P (isPGroup_Ugrp.toSylow hUi)
  have h1 : MulAut.conj h • (P : Subgroup G5) = Ugrp :=
    congrArg (fun P : Sylow 2 G5 => (P : Subgroup G5)) hh
  have hu : h * g * h⁻¹ ∈ Ugrp := by
    rw [← h1]
    have h2 := Subgroup.smul_mem_pointwise_smul g (MulAut.conj h) (P : Subgroup G5)
      (hP (Subgroup.mem_zpowers g))
    rwa [MulAut.smul_def, MulAut.conj_apply] at h2
  set u := h * g * h⁻¹ with hudef
  have hu1 : u ≠ 1 := fun h0 => hg1 (by
    calc g = h⁻¹ * (h * g * h⁻¹) * h := by group
      _ = 1 := by rw [← hudef, h0]; group)
  have hu2 : u * u = 1 := by
    calc u * u = h * (g * g) * h⁻¹ := by rw [hudef]; group
      _ = 1 := by rw [hg2]; group
  have hU : IsUpU (u : Matrix (Fin 5) (Fin 5) (ZMod 2)) := hu
  have hmat := eq_upMat hU
  have hu1' : (u : Matrix (Fin 5) (Fin 5) (ZMod 2)) ≠ 1 := fun h0 =>
    hu1 (Subtype.ext h0)
  have hu2' :
      (u : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (u : Matrix (Fin 5) (Fin 5) (ZMod 2)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hu2, Matrix.SpecialLinearGroup.coe_one]
  rw [hmat] at hu1' hu2'
  obtain ⟨i, j, k, hijk⟩ := upU_wedge_cert _ _ _ _ _ _ _ _ _ _ hu2' hu1'
  rw [← hmat] at hijk
  have hfixu := card_fix_le_of_indep3 _ hijk
  have hconj : ∀ v : Fin 10 → ZMod 2,
      wedgeRep g (wedgeRep h⁻¹ v) = wedgeRep h⁻¹ (wedgeRep u v) := by
    intro v
    rw [hudef, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
      ← Module.End.mul_apply (wedgeRep h⁻¹) (wedgeRep h), ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply]
  have e : {w : Fin 10 → ZMod 2 // wedgeRep g w = w} ≃
      {w : Fin 10 → ZMod 2 // wedgeMat (u : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ w = w} :=
    { toFun := fun w => ⟨wedgeRep h w.1, by
        rw [← wedgeRep_apply', hudef, map_mul, map_mul, Module.End.mul_apply,
          Module.End.mul_apply, ← Module.End.mul_apply (wedgeRep h⁻¹), ← map_mul, inv_mul_cancel,
          map_one, Module.End.one_apply, w.2]⟩
      invFun := fun w => ⟨wedgeRep h⁻¹ w.1, by
        have h2 : wedgeRep u w.1 = w.1 := by rw [wedgeRep_apply']; exact w.2
        rw [hconj, h2]⟩
      left_inv := fun w => Subtype.ext (by
        show wedgeRep h⁻¹ (wedgeRep h w.1) = w.1
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply])
      right_inv := fun w => Subtype.ext (by
        show wedgeRep h (wedgeRep h⁻¹ w.1) = w.1
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]) }
  rw [Nat.card_congr e]
  exact hfixu

theorem card_fixV_le_of_sl5
    {V : Type} [CommGroup V] [Finite V] (h2 : ∀ v : V, v ^ 2 = 1)
    (hcard : Nat.card V = 2 ^ 10) {H : Subgroup (MulAut V)} (φ : ↥H ≃* G5)
    (hirr : ∀ W : Subgroup V, (∀ h ∈ H, ∀ w ∈ W, (h : MulAut V) w ∈ W) → W = ⊥ ∨ W = ⊤)
    {x : MulAut V} (hx : x ∈ H) (hx1 : x ≠ 1) (hx2 : x * x = 1) :
    Nat.card (fixV (Subgroup.zpowers x)) ≤ 2 ^ 7 := by
  obtain ⟨e, γ, -, he⟩ := exists_wedge_coords h2 hcard φ hirr
  set g : G5 := γ ⟨x, hx⟩ with hg
  have hg1 : g ≠ 1 := fun h0 => hx1 (by
    have h1 : (⟨x, hx⟩ : ↥H) = 1 := γ.injective (by rw [map_one]; exact h0)
    exact congrArg Subtype.val h1)
  have hg2 : g * g = 1 := by
    rw [hg, ← map_mul]
    have h1 : (⟨x, hx⟩ : ↥H) * ⟨x, hx⟩ = 1 := Subtype.ext hx2
    rw [h1, map_one]
  have hle := card_fix_wedgeRep_le hg1 hg2
  have e' : ↥(fixV (Subgroup.zpowers x)) ≃ {w : Fin 10 → ZMod 2 // wedgeRep g w = w} :=
    { toFun := fun v => ⟨e v.1, by
        have h1 : x v.1 = v.1 := mem_fixV_zpowers.1 v.2
        have h3 := he ⟨x, hx⟩ v.1
        exact h3.symm.trans (congrArg e h1)⟩
      invFun := fun w => ⟨e.symm w.1, mem_fixV_zpowers.2 (by
        apply e.injective
        have h3 := he ⟨x, hx⟩ (e.symm w.1)
        rw [Equiv.apply_symm_apply] at h3
        rw [Equiv.apply_symm_apply]
        exact h3.trans w.2)⟩
      left_inv := fun v => Subtype.ext (e.symm_apply_apply v.1)
      right_inv := fun w => Subtype.ext (e.apply_symm_apply w.1) }
  rw [Nat.card_congr e']
  exact hle

end CFSG.Quasithin.H13
