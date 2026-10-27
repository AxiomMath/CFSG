module

public import CFSG.LocalAnalysis.SteinbergCDEvenOrderFourTools
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFour

public section

namespace CFSG.LocalAnalysis.SteinbergCD

open Matrix CFSG.Assembly.LowTwoRank

section Symplectic

variable {k : Type} [Field k] {r : ℕ}

@[expose] def spA (i₀ i₁ : Fin r) : Matrix (Fin r) (Fin r) k := 1 + vecMulVec (bvec i₀) (bvec i₁)

@[expose] def spS (i₁ : Fin r) : Matrix (Fin r) (Fin r) k := vecMulVec (bvec i₁) (bvec i₁)

@[expose] def spM (i₀ i₁ : Fin r) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k :=
  fromBlocks (spA i₀ i₁) (spA i₀ i₁ * spS i₁) 0 (spA i₀ i₁)ᵀ

section Facts

variable {i₀ i₁ : Fin r} (h2 : (2 : k) = 0) (h01 : i₀ ≠ i₁)

include h2 h01 in
theorem spA_mul_spA : spA (k := k) i₀ i₁ * spA i₀ i₁ = 1 := by
  simp only [spA, add_mul, mul_add, one_mul, mul_one, vecMulVec_mul_vecMulVec, bvec_dot_bvec,
    Ne.symm h01, ↓reduceIte, zero_smul, vecMulVec_zero, add_zero]
  rw [add_assoc, add_self_of_two_eq_zero h2, add_zero]

include h2 h01 in
theorem spA_transpose_mul : (spA (k := k) i₀ i₁)ᵀ * (spA i₀ i₁)ᵀ = 1 := by
  rw [← transpose_mul, spA_mul_spA h2 h01, transpose_one]

theorem spS_transpose : (spS (k := k) i₁)ᵀ = spS i₁ := by
  rw [spS, transpose_vecMulVec]

theorem spASA : spA (k := k) i₀ i₁ * spS i₁ * (spA i₀ i₁)ᵀ =
    vecMulVec (bvec i₁) (bvec i₁) + vecMulVec (bvec i₀) (bvec i₁) +
      (vecMulVec (bvec i₁) (bvec i₀) + vecMulVec (bvec i₀) (bvec i₀)) := by
  simp only [spA, spS, transpose_add, transpose_one, transpose_vecMulVec, add_mul, mul_add,
    one_mul, mul_one, vecMulVec_mul_vecMulVec, bvec_dot_bvec, ↓reduceIte, one_smul]

include h01 in
theorem spX_apply :
    (spS (k := k) i₁ + spA i₀ i₁ * spS i₁ * (spA i₀ i₁)ᵀ : Matrix (Fin r) (Fin r) k) i₀ i₀ = 1 := by
  rw [spASA]
  simp [spS, Matrix.add_apply, vecMulVec_apply, bvec, h01]

include h2 h01 in
theorem spM_symplectic :
    (spM (k := k) i₀ i₁)ᵀ * fromBlocks 0 1 (-1) 0 * spM i₀ i₁ = fromBlocks 0 1 (-1) 0 := by
  rw [spM, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [transpose_zero, transpose_transpose, transpose_mul, spS_transpose, zero_mul,
    mul_zero, add_zero, zero_add, mul_one, mul_neg, neg_mul]
  rw [spA_transpose_mul h2 h01, ← mul_assoc, spA_mul_spA h2 h01, one_mul, mul_assoc,
    spA_transpose_mul h2 h01, mul_one, neg_add_cancel]
  simp only [neg_zero, zero_add]

include h2 h01 in
theorem spM_sq : spM (k := k) i₀ i₁ ^ 2 =
    fromBlocks 1 (spS i₁ + spA i₀ i₁ * spS i₁ * (spA i₀ i₁)ᵀ) 0 1 := by
  rw [sq, spM, fromBlocks_multiply]
  simp only [mul_zero, add_zero, zero_mul, zero_add]
  rw [spA_mul_spA h2 h01, spA_transpose_mul h2 h01, ← mul_assoc, spA_mul_spA h2 h01, one_mul]

include h2 h01 in
theorem spM_pow_four : spM (k := k) i₀ i₁ ^ 4 = 1 := by
  rw [show 4 = 2 * 2 by norm_num, pow_mul, spM_sq h2 h01, sq, fromBlocks_multiply]
  simp only [mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add]
  rw [add_self_of_two_eq_zero h2, fromBlocks_one]

end Facts

theorem exists_orderOf_eq_four_statedSp (h2 : (2 : k) = 0) (hr : 2 ≤ r) :
    ∃ g : StatedSp r k, orderOf g = 4 ∧ orderOf (g : StatedProj (StatedSp r k)) = 4 := by
  set i₀ : Fin r := ⟨0, by omega⟩
  set i₁ : Fin r := ⟨1, by omega⟩
  have h01 : i₀ ≠ i₁ := Fin.ne_of_val_ne (by simp [i₀, i₁])
  set M := spM (k := k) i₀ i₁
  have hM4 : M ^ 4 = 1 := spM_pow_four h2 h01
  set u : GL (Fin r ⊕ Fin r) k := ⟨M, M ^ 3, by rw [← pow_succ', hM4], by rw [← pow_succ, hM4]⟩
  have hu : (u : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) = M := rfl
  have hmem : u ∈ StatedSp r k := Subgroup.subset_closure (by
    show (u : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k)ᵀ * _ * _ = _
    rw [hu]
    exact spM_symplectic h2 h01)
  set g : StatedSp r k := ⟨u, hmem⟩
  have hg4 : g ^ 4 = 1 := Subtype.ext (Units.ext (by
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hu, hM4, Subgroup.coe_one, Units.val_one]))
  have hg2 : (((g ^ 2 : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) =
        fromBlocks 1 (spS i₁ + spA i₀ i₁ * spS i₁ * (spA i₀ i₁)ᵀ) 0 1 := by
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hu, spM_sq h2 h01]
  have hnot : g ^ 2 ∉ (StatedScalars (Fin r ⊕ Fin r) k).subgroupOf (StatedSp r k) := by
    intro hmem2
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hmem2
    have h1 := congrArg (fun x : GL (Fin r ⊕ Fin r) k =>
      (x : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) (Sum.inl i₀) (Sum.inr i₀)) hc
    simp only [GeneralLinearGroup.coe_scalar, hg2, fromBlocks_apply₁₂] at h1
    rw [spX_apply h01] at h1
    simp at h1
  exact ⟨g, orderOf_eq_four hg4 fun h => hnot (h ▸ one_mem _), orderOf_mk_eq_four hg4 hnot⟩

end Symplectic

section Orthogonal

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] {Q : QuadraticForm k V}

theorem orthElementaryMap_apply_of_singular {u v : V} (hv : Q v = 0) (x : V) :
    orthElementaryMap Q u v x = x + polar Q x u • v - polar Q x v • u := by
  rw [orthElementaryMap_apply, hv, zero_mul, zero_smul, sub_zero]

theorem elementary_comp_apply {P₁ P₂ P₃ : HypPair Q} (h12 : P₁.Orth P₂) (h13 : P₁.Orth P₃)
    (h23 : P₂.Orth P₃) (x : V) :
    orthElementaryMap Q P₁.e P₂.f (orthElementaryMap Q P₂.e P₃.f x) =
      x + polar Q x P₂.e • P₃.f - polar Q x P₃.f • P₂.e + polar Q x P₁.e • P₂.f -
        (polar Q x P₂.f - polar Q x P₃.f) • P₁.e := by
  have hB : ∀ y z : V, polar Q y z = polar Q z y := fun y z => polar_comm _ y z
  simp only [orthElementaryMap_apply_of_singular P₂.Q_f, orthElementaryMap_apply_of_singular P₃.Q_f,
    polar_add_left, polar_sub_left, polar_smul_left, smul_eq_mul, hB P₃.f P₁.e, hB P₂.e P₁.e,
    hB P₃.f P₂.f, h13.ef, h12.ee, h23.ff, P₂.polar_ef, mul_zero, mul_one, add_zero, sub_zero]

theorem elementary_comp_sq [CharP k 2] {P₁ P₂ P₃ : HypPair Q} (h12 : P₁.Orth P₂)
    (h13 : P₁.Orth P₃) (h23 : P₂.Orth P₃) (x : V) :
    orthElementaryMap Q P₁.e P₂.f (orthElementaryMap Q P₂.e P₃.f
      (orthElementaryMap Q P₁.e P₂.f (orthElementaryMap Q P₂.e P₃.f x))) =
      orthElementaryMap Q P₁.e P₃.f x := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hB : ∀ y z : V, polar Q y z = polar Q z y := fun y z => polar_comm _ y z
  have hee1 : polar Q P₁.e P₁.e = 0 := by rw [polar_self, P₁.Q_e, smul_zero]
  have hee2 : polar Q P₂.e P₂.e = 0 := by rw [polar_self, P₂.Q_e, smul_zero]
  have hff2 : polar Q P₂.f P₂.f = 0 := by rw [polar_self, P₂.Q_f, smul_zero]
  have hff3 : polar Q P₃.f P₃.f = 0 := by rw [polar_self, P₃.Q_f, smul_zero]
  rw [elementary_comp_apply h12 h13 h23, elementary_comp_apply h12 h13 h23,
    orthElementaryMap_apply_of_singular P₃.Q_f]
  simp only [polar_add_left, polar_sub_left, polar_smul_left, smul_eq_mul, hB P₃.f P₁.e,
    hB P₂.e P₁.e, hB P₃.f P₂.f, hB P₃.f P₂.e, hB P₂.f P₁.e, hB P₂.f P₂.e, h13.ef, h12.ee, h12.ef,
    h23.ff, h23.ef, P₂.polar_ef, hee1, hee2, hff2, hff3, mul_zero, mul_one, add_zero, sub_zero]
  set a := polar Q x P₁.e
  set c := polar Q x P₂.e
  set d₂ := polar Q x P₂.f
  set d₃ := polar Q x P₃.f
  rw [show x + a • P₃.f - d₃ • P₁.e = x + a • P₃.f - d₃ • P₁.e +
      (2 : k) • (c • P₃.f - d₃ • P₂.e + a • P₂.f - d₂ • P₁.e + (2 * d₃) • P₁.e) by
    rw [h2, zero_smul, add_zero]]
  module

theorem exists_orderOf_eq_four_orthogonal [CharP k 2] [FiniteDimensional k V]
    (hQ : (polarBilin Q).Nondegenerate) {P : ℕ → HypPair Q} {r : ℕ}
    (hP : ∀ i j, i < r → j < r → i ≠ j → (P i).Orth (P j)) (hr : 3 ≤ r)
    (hA : ∀ x ∈ tailSpace P r, Q x = 0 → x = 0)
    (hdim : Module.finrank k (tailSpace P r) = 0 ∨ Module.finrank k (tailSpace P r) = 2) :
    ∃ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆,
      orderOf g = 4 := by
  have h12 : (P 0).Orth (P 1) := hP 0 1 (by omega) (by omega) (by omega)
  have h13 : (P 0).Orth (P 2) := hP 0 2 (by omega) (by omega) (by omega)
  have h23 : (P 1).Orth (P 2) := hP 1 2 (by omega) (by omega) (by omega)
  obtain ⟨g₁, hg₁, hg₁'⟩ := mem_orthElementaryGroup_gen Q (P 0).Q_e h12.ef
  obtain ⟨g₂, hg₂, hg₂'⟩ := mem_orthElementaryGroup_gen Q (P 1).Q_e h23.ef
  have hE := orthogonal_char_two_derived_elementary hQ hP hr hA hdim
  set g := g₁ * g₂
  have hgE : g ∈ orthElementaryGroup Q := mul_mem hg₁ hg₂
  have hg : ∀ x, g x = orthElementaryMap Q (P 0).e (P 1).f
      (orthElementaryMap Q (P 1).e (P 2).f x) := fun x => by
    have h1 := LinearMap.congr_fun hg₁' (g₂ x)
    have h2' := LinearMap.congr_fun hg₂' x
    simp only [LinearEquiv.coe_coe] at h1 h2'
    rw [LinearEquiv.mul_apply, h1, h2']
  have hg2 : ∀ x, (g ^ 2) x = orthElementaryMap Q (P 0).e (P 2).f x := fun x => by
    rw [pow_two, LinearEquiv.mul_apply, hg, hg, elementary_comp_sq h12 h13 h23]
  have hR : ∀ x, orthElementaryMap Q (P 0).e (P 2).f (orthElementaryMap Q (P 0).e (P 2).f x) = x :=
    fun x => by
      have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
      have h := (orthogonal_elementary_addition Q (P 0).Q_e h13.ef h13.ef).2.1
      have h' := LinearMap.congr_fun h x
      rw [LinearMap.comp_apply] at h'
      rw [h', ← two_smul k (P 2).f, h2, zero_smul, (orthogonal_elementary_addition Q (P 0).Q_e
        h13.ef h13.ef).1, LinearMap.id_apply]
  have hg4 : g ^ 4 = 1 := LinearEquiv.ext fun x => by
    rw [show 4 = 2 + 2 by norm_num, pow_add, LinearEquiv.mul_apply, hg2, hg2, hR]
    rfl
  have hg2' : g ^ 2 ≠ 1 := by
    intro h
    have hx := hg2 (P 0).f
    rw [h, orthElementaryMap_apply_of_singular (P 2).Q_f, polar_comm _ (P 0).f (P 0).e,
      (P 0).polar_ef, h13.ff, zero_smul, sub_zero, one_smul] at hx
    have hf : (P 2).f = 0 := by
      have h' : (P 0).f = (P 0).f + (P 2).f := hx
      exact (add_eq_left.1 h'.symm)
    have h1 := (P 2).polar_ef
    rw [hf, polar_zero_right] at h1
    exact zero_ne_one h1
  refine ⟨g, hE ▸ hgE, orderOf_eq_four hg4 hg2'⟩

end Orthogonal

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ClassicalGroups.UnitaryFlag CFSG.ClassicalGroups.Orthogonal

end CFSG.LocalAnalysis.SteinbergCD
