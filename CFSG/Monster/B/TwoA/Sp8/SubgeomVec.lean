
module

public import CFSG.Monster.B.TwoA.Sp8.SubgeomVecBase

public import CFSG.Monster.B.TwoA.Sp8.QuadCosetC
public import CFSG.Monster.B.TwoA.Base.Incidence
public import CFSG.Monster.B.TwoA.Sp8.Normalizer

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open Module Submodule CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

theorem Psi_zero_eq :
    Psi 0 = 1 := map_one PsiHom

theorem Psi_neg
    (v : V8) : Psi (-v) = (Psi v)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← Psi_add, neg_add_cancel, Psi_zero_eq]

theorem Psi_inj
    {v w : V8} (h : Psi v = Psi w) : v = w :=
  Multiplicative.ofAdd.injective (PsiHom_injective h)

theorem exists_Psi_eq
    {x : Dfull} (hx : x ∈ A8) : ∃ v, Psi v = x := by
  rw [← range_PsiHom] at hx
  obtain ⟨v, rfl⟩ := hx
  exact ⟨v.toAdd, rfl⟩

theorem Psi_conj
    (x : Xgrp) (v : V8) : (x : Dfull) * Psi v * (x : Dfull)⁻¹ = Psi (rhoX x v) := by
  have h := aEquiv_rhoX x v
  rw [coe_aEquiv, coe_aEquiv, toAdd_ofAdd, toAdd_ofAdd] at h
  exact h.symm

@[expose] def a8Vec
    (A : Subgroup Dfull) : Submodule (ZMod 2) V8 where
  carrier := {v | Psi v ∈ A}
  add_mem' {v w} hv hw := by
    show Psi (v + w) ∈ A
    rw [Psi_add]
    exact A.mul_mem hv hw
  zero_mem' := by
    show Psi 0 ∈ A
    rw [Psi_zero_eq]
    exact A.one_mem
  smul_mem' c v hv := by
    show Psi (c • v) ∈ A
    rcases zmod2_cases c with rfl | rfl
    · rw [zero_smul, Psi_zero_eq]
      exact A.one_mem
    · rwa [one_smul]

theorem mem_a8Vec
    {A : Subgroup Dfull} {v : V8} : v ∈ a8Vec A ↔ Psi v ∈ A := Iff.rfl

@[expose] def a8Grp
    (W : Submodule (ZMod 2) V8) : Subgroup Dfull where
  carrier := Psi '' W
  mul_mem' := by
    rintro _ _ ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩
    exact ⟨v + w, W.add_mem hv hw, Psi_add v w⟩
  one_mem' := ⟨0, W.zero_mem, Psi_zero_eq⟩
  inv_mem' := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨-v, W.neg_mem hv, Psi_neg v⟩

theorem mem_a8Grp
    {W : Submodule (ZMod 2) V8} {x : Dfull} :
    x ∈ a8Grp W ↔ ∃ v ∈ W, Psi v = x := Iff.rfl

theorem Psi_mem_a8Grp
    {W : Submodule (ZMod 2) V8} {v : V8} (hv : v ∈ W) : Psi v ∈ a8Grp W :=
  ⟨v, hv, rfl⟩

theorem a8Grp_le_A8
    (W : Submodule (ZMod 2) V8) : a8Grp W ≤ A8 := by
  rintro _ ⟨v, -, rfl⟩
  exact Psi_mem_A8 v

theorem a8Vec_a8Grp
    (W : Submodule (ZMod 2) V8) : a8Vec (a8Grp W) = W := by
  ext v
  rw [mem_a8Vec]
  constructor
  · rintro ⟨w, hw, e⟩
    rwa [← Psi_inj e]
  · intro hv
    exact ⟨v, hv, rfl⟩

theorem a8Grp_a8Vec
    {A : Subgroup Dfull} (hA : A ≤ A8) : a8Grp (a8Vec A) = A := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact hv
  · intro hx
    obtain ⟨v, rfl⟩ := exists_Psi_eq (hA hx)
    exact ⟨v, hx, rfl⟩

theorem a8Vec_mono
    {A B : Subgroup Dfull} (h : A ≤ B) : a8Vec A ≤ a8Vec B := fun _ hv => h hv

theorem a8Grp_mono
    {W W' : Submodule (ZMod 2) V8} (h : W ≤ W') : a8Grp W ≤ a8Grp W' := by
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨v, h hv, rfl⟩

theorem a8Vec_le_iff
    {A B : Subgroup Dfull} (hA : A ≤ A8) (hB : B ≤ A8) :
    a8Vec A ≤ a8Vec B ↔ A ≤ B := by
  refine ⟨fun h => ?_, a8Vec_mono⟩
  rw [← a8Grp_a8Vec hA, ← a8Grp_a8Vec hB]
  exact a8Grp_mono h

theorem a8Vec_injective
    {A B : Subgroup Dfull} (hA : A ≤ A8) (hB : B ≤ A8)
    (h : a8Vec A = a8Vec B) : A = B := by
  rw [← a8Grp_a8Vec hA, ← a8Grp_a8Vec hB, h]

theorem natCard_a8Grp
    (W : Submodule (ZMod 2) V8) : Nat.card (a8Grp W) = Nat.card W := by
  refine (Nat.card_congr (Equiv.ofBijective
    (fun v : W => (⟨Psi v, Psi_mem_a8Grp v.2⟩ : a8Grp W)) ⟨fun v w h => ?_, ?_⟩)).symm
  · exact Subtype.ext (Psi_inj (congrArg Subtype.val h))
  · rintro ⟨_, v, hv, rfl⟩
    exact ⟨⟨v, hv⟩, rfl⟩

theorem natCard_a8Grp_eq_pow
    (W : Submodule (ZMod 2) V8) :
    Nat.card (a8Grp W) = 2 ^ finrank (ZMod 2) W := by
  rw [natCard_a8Grp, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

theorem natCard_a8Vec
    {A : Subgroup Dfull} (hA : A ≤ A8) : Nat.card (a8Vec A) = Nat.card A := by
  conv_rhs => rw [← a8Grp_a8Vec hA]
  exact (natCard_a8Grp _).symm

theorem finrank_a8Vec
    {A : Subgroup Dfull} (hA : A ≤ A8) {i : ℕ} (hc : Nat.card A = 2 ^ i) :
    finrank (ZMod 2) (a8Vec A) = i := by
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := a8Vec A)
  rw [natCard_a8Vec hA, hc, Nat.card_zmod] at h
  exact (Nat.pow_right_injective le_rfl h).symm

theorem conjSub_a8Grp
    (x : Xgrp) (W : Submodule (ZMod 2) V8) :
    conjSub (x : Dfull) (a8Grp W) = a8Grp (W.map (rhoX x : V8 →ₗ[ZMod 2] V8)) := by
  ext y
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨rhoX x v, ⟨v, hv, rfl⟩, (Psi_conj x v).symm⟩
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨Psi v, ⟨v, hv, rfl⟩, Psi_conj x v⟩

theorem conjSub_le_A8
    {x : Dfull} (hx : x ∈ Xgrp) {A : Subgroup Dfull} (hA : A ≤ A8) :
    conjSub x A ≤ A8 := by
  have h := conjSub_mono (g := x) hA
  rwa [conjSub_eq_self_iff.2 (Xgrp_le_normalizer hx)] at h

theorem a8Vec_conjSub
    (x : Xgrp) {A : Subgroup Dfull} (hA : A ≤ A8) :
    a8Vec (conjSub (x : Dfull) A) = (a8Vec A).map (rhoX x : V8 →ₗ[ZMod 2] V8) := by
  conv_lhs => rw [← a8Grp_a8Vec hA]
  rw [conjSub_a8Grp, a8Vec_a8Grp]

theorem Psi_bvec_two :
    Psi (bvec 8 2) = yhat := by rw [bvec_std.2.1, Psi_single]; rfl

theorem Psi_bvec_four :
    Psi (bvec 8 4) = zhat := by rw [bvec_std.2.2.1, Psi_single]; rfl

theorem Psi_bvec_24 :
    Psi (bvec 8 24) = dhat 4 5 := by
  rw [bvec_std.2.2.2, Psi_add_single, dhat_45]
  rfl

theorem Echain_le_a8Grp_stdVec :
    ∀ i : ℕ, 1 ≤ i → i ≤ 4 → Echain i ≤ a8Grp (a8StdVec i) := by
  have h3 : E3 ≤ a8Grp (a8StdVec 3) := by
    rw [E3, Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact ⟨_, subset_span (by simp), Psi_bvec_one⟩
    · exact ⟨_, subset_span (by simp), Psi_bvec_two⟩
    · exact ⟨_, subset_span (by simp), Psi_bvec_four⟩
  intro i h1 h4
  interval_cases i
  · show Subgroup.zpowers xhat ≤ _
    rw [Subgroup.zpowers_le]
    exact ⟨_, subset_span (by simp), Psi_bvec_one⟩
  · show Vhat ≤ _
    intro y hy
    rcases (mem_Vhat_iff y).1 hy with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact ⟨_, subset_span (by simp), Psi_bvec_one⟩
    · rw [← Psi_bvec_one, ← Psi_bvec_two, ← Psi_add]
      exact Psi_mem_a8Grp (add_mem (subset_span (by simp)) (subset_span (by simp)))
    · exact ⟨_, subset_span (by simp), Psi_bvec_two⟩
  · exact h3
  · show E4 ≤ _
    rw [E4, Subgroup.closure_le]
    rintro y (rfl | hy)
    · exact ⟨_, subset_span (by simp), Psi_bvec_24⟩
    · refine a8Grp_mono (span_mono ?_) (h3 hy)
      intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv ⊢
      tauto

theorem stdVec_le_a8Vec_Echain :
    ∀ i : ℕ, 1 ≤ i → i ≤ 4 → a8StdVec i ≤ a8Vec (Echain i) := by
  intro i h1 h4
  interval_cases i
  · show span (ZMod 2) {bvec 8 1} ≤ a8Vec (Subgroup.zpowers xhat)
    rw [span_le, Set.singleton_subset_iff]
    rw [SetLike.mem_coe, mem_a8Vec, Psi_bvec_one]
    exact Subgroup.mem_zpowers _
  · show span (ZMod 2) {bvec 8 1, bvec 8 2} ≤ a8Vec Vhat
    rw [span_le]
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · rw [SetLike.mem_coe, mem_a8Vec, Psi_bvec_one]
      exact xhat_mem_Vhat
    · rw [SetLike.mem_coe, mem_a8Vec, Psi_bvec_two]
      exact yhat_mem_Vhat
  · show span (ZMod 2) {bvec 8 1, bvec 8 2, bvec 8 4} ≤ a8Vec E3
    rw [span_le]
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl
    · rw [SetLike.mem_coe, mem_a8Vec, Psi_bvec_one]
      exact xhat_mem_E3
    · rw [SetLike.mem_coe, mem_a8Vec, Psi_bvec_two]
      exact yhat_mem_E3
    · rw [SetLike.mem_coe, mem_a8Vec, Psi_bvec_four]
      exact zhat_mem_E3
  · show span (ZMod 2) {bvec 8 1, bvec 8 2, bvec 8 4, bvec 8 24} ≤ a8Vec E4
    rw [span_le]
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · rw [SetLike.mem_coe, mem_a8Vec, Psi_bvec_one]
      exact xhat_mem_E4
    · rw [SetLike.mem_coe, mem_a8Vec, Psi_bvec_two]
      exact E3_le_E4 yhat_mem_E3
    · rw [SetLike.mem_coe, mem_a8Vec, Psi_bvec_four]
      exact E3_le_E4 zhat_mem_E3
    · rw [SetLike.mem_coe, mem_a8Vec, Psi_bvec_24]
      exact d45_mem_E4

theorem Echain_le_A8
    {i : ℕ} (h1 : 1 ≤ i) (h4 : i ≤ 4) : Echain i ≤ A8 :=
  (Echain_le_a8Grp_stdVec i h1 h4).trans (a8Grp_le_A8 _)

theorem a8Vec_Echain
    {i : ℕ} (h1 : 1 ≤ i) (h4 : i ≤ 4) : a8Vec (Echain i) = a8StdVec i := by
  refine le_antisymm ?_ (stdVec_le_a8Vec_Echain i h1 h4)
  have h := a8Vec_mono (Echain_le_a8Grp_stdVec i h1 h4)
  rwa [a8Vec_a8Grp] at h

theorem finrank_a8Vec_Echain
    {i : ℕ} (h1 : 1 ≤ i) (h4 : i ≤ 4) :
    finrank (ZMod 2) (a8Vec (Echain i)) = i :=
  finrank_a8Vec (Echain_le_A8 h1 h4) (natCard_Echain i h1 (by omega))

theorem isotropic_a8Vec_Echain
    {i : ℕ} (h1 : 1 ≤ i) (h4 : i ≤ 4) :
    IsTotallyIsotropic b0 (a8Vec (Echain i)) := by
  have h : a8Vec (Echain i) ≤ a8StdVec 4 := by
    rw [← a8Vec_Echain (i := 4) (by norm_num) le_rfl]
    exact a8Vec_mono (Echain_mono h1 h4 (by norm_num))
  exact stdVec_four_isotropic.mono h

theorem rhoX_mem_isometryGroup
    (x : Xgrp) :
    (rhoX x : V8 ≃ₗ[ZMod 2] V8) ∈ TauCeti.BilinForm.isometryGroup b0 := rhoX_mem_Sp x

theorem a8Vec_conjSub_Echain
    (x : Xgrp) {i : ℕ} (h1 : 1 ≤ i) (h4 : i ≤ 4) :
    a8Vec (conjSub (x : Dfull) (Echain i)) =
      (a8Vec (Echain i)).map (rhoX x : V8 →ₗ[ZMod 2] V8) :=
  a8Vec_conjSub x (Echain_le_A8 h1 h4)

theorem isotropic_a8Vec_conjSub
    (x : Xgrp) {i : ℕ} (h1 : 1 ≤ i) (h4 : i ≤ 4) :
    IsTotallyIsotropic b0 (a8Vec (conjSub (x : Dfull) (Echain i))) ∧
      finrank (ZMod 2) (a8Vec (conjSub (x : Dfull) (Echain i))) = i := by
  rw [a8Vec_conjSub_Echain x h1 h4]
  exact ⟨isTotallyIsotropic_map_isometry (rhoX_mem_isometryGroup x)
    (isotropic_a8Vec_Echain h1 h4),
    (LinearEquiv.finrank_map_eq _ _).trans (finrank_a8Vec_Echain h1 h4)⟩

theorem exists_conj_eq_a8Grp
    {W : Submodule (ZMod 2) V8} (hW : IsTotallyIsotropic b0 W)
    {i : ℕ} (h1 : 1 ≤ i) (h4 : i ≤ 4) (hd : finrank (ZMod 2) W = i) :
    ∃ x : Xgrp, conjSub (x : Dfull) (Echain i) = a8Grp W := by
  obtain ⟨g, hg, hgW⟩ := exists_isometry_map_eq b0_isAlt b0_nondegenerate finrank_V8
    (isotropic_a8Vec_Echain h1 h4) hW ((finrank_a8Vec_Echain h1 h4).trans hd.symm)
  obtain ⟨x, hx⟩ := rhoXSp_surjective ⟨g, hg⟩
  have hxg : rhoX x = g := by
    rw [← coe_rhoXSp, hx]
  refine ⟨x, ?_⟩
  conv_lhs => rw [← a8Grp_a8Vec (Echain_le_A8 h1 h4)]
  rw [conjSub_a8Grp, hxg, hgW]

end CFSG.Monster.B.TwoA.Sp8
