module

public import CFSG.LocalAnalysis.StandardType.GGTwE6RootKillWeyl

public section

namespace CFSG.StandardType.TwE6FieldCore

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.StandardType.TwE6RootKill

theorem twE6Perm_symm_symm (k : Fin TwistTag.E6.tag.rank) :
    TwistTag.E6.perm.symm (TwistTag.E6.perm.symm k) = k := by
  revert k
  decide

theorem permLattice_permLattice_twE6 (x : Fin TwistTag.E6.tag.rank → ℤ) :
    permLattice TwistTag.E6.perm (permLattice TwistTag.E6.perm x) = x := by
  funext k
  simp only [permLattice, Function.comp_apply, twE6Perm_symm_symm]

theorem iform_permLattice_left_twE6 (x y : Fin TwistTag.E6.tag.rank → ℤ) :
    iform (permLattice TwistTag.E6.perm x) y = iform x (permLattice TwistTag.E6.perm y) := by
  conv_lhs => rw [← permLattice_permLattice_twE6 y]
  exact iform_permLattice_E6 x _

theorem wkMatrix_eq_add (w : WeylGroup TwistTag.E6.tag) (j : Fin TwistTag.E6.tag.rank) :
    wkMatrix w j = Pi.single j 1 +
      permLattice TwistTag.E6.perm (w • (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ)) := by
  funext k
  have hk : TwistTag.E6.perm.symm k = TwistTag.E6.perm k := by
    revert k
    decide
  simp only [wkMatrix, Pi.add_apply, Pi.single_apply, permLattice, Function.comp_apply, hk]
  rcases eq_or_ne j k with rfl | h
  · simp
  · simp [h, Ne.symm h]

section Rows


theorem iform_self_of_isRoot_twE6 {β : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : IsRoot TwistTag.E6.tag β) : iform β β = 2 := by
  obtain ⟨w, k, rfl⟩ := isRoot_iff_exists_smul_single.1 hβ
  rw [iform_smul, iform_single_single, show TwistTag.E6.tag.symmetrizer = 1 from rfl,
    Matrix.one_apply_eq, mul_one]

theorem iform_neg_right_twE6 (x y : Fin TwistTag.E6.tag.rank → ℤ) :
    iform x (-y) = -iform x y := by
  rw [← neg_one_smul ℤ y, iform_smul_right, neg_one_mul]

theorem wkMatrix_rootReflection_mul {β : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : IsRoot TwistTag.E6.tag β) (w : WeylGroup TwistTag.E6.tag)
    (j : Fin TwistTag.E6.tag.rank) :
    wkMatrix (rootReflection (permLattice TwistTag.E6.perm β) * w) j = wkMatrix w j -
      corootPair (permLattice TwistTag.E6.perm β)
        (w • (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ)) • β := by
  rw [wkMatrix_eq_add, wkMatrix_eq_add, mul_smul,
    rootReflection_smul (hβ.permLattice TwistTag.E6.cartan_perm)]
  funext k
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, permLattice,
    Function.comp_apply, twE6Perm_symm_symm]
  ring

theorem corootPair_eq_zero_of_wkMatrix_eq_zero {w : WeylGroup TwistTag.E6.tag}
    {i j : Fin TwistTag.E6.tag.rank} (hj : wkMatrix w j = 0) :
    corootPair (permLattice TwistTag.E6.perm (wkMatrix w i))
      (w • (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ)) = 0 := by
  rw [wkMatrix_eq_add] at hj
  have hwj : w • (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) =
      -permLattice TwistTag.E6.perm (Pi.single j 1) := by
    have h := congrArg (permLattice TwistTag.E6.perm) (eq_neg_of_add_eq_zero_right hj)
    rw [permLattice_permLattice_twE6] at h
    exact h
  have h0 : iform (permLattice TwistTag.E6.perm (wkMatrix w i))
      (w • (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ)) = 0 := by
    rw [hwj, iform_neg_right_twE6, iform_permLattice_E6, wkMatrix_eq_add, iform_add_left,
      iform_permLattice_left_twE6, ← neg_neg (permLattice TwistTag.E6.perm (Pi.single j 1)),
      ← hwj, iform_neg_right_twE6, iform_smul, add_neg_cancel, neg_zero]
  rw [corootPair, h0, mul_zero, Int.zero_ediv]

theorem corootPair_wkMatrix_self {w : WeylGroup TwistTag.E6.tag} {i : Fin TwistTag.E6.tag.rank}
    (hβ : IsRoot TwistTag.E6.tag (wkMatrix w i)) :
    corootPair (permLattice TwistTag.E6.perm (wkMatrix w i))
      (w • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ)) = 1 := by
  have h2 := iform_self_of_isRoot_twE6 hβ
  have hγ : iform (permLattice TwistTag.E6.perm (wkMatrix w i))
      (permLattice TwistTag.E6.perm (wkMatrix w i)) = 2 := by
    rw [iform_permLattice_E6, h2]
  rw [wkMatrix_eq_add] at h2 hγ ⊢
  have hee : iform (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) (Pi.single i 1) = 2 := by
    rw [iform_single_single, show TwistTag.E6.tag.symmetrizer = 1 from rfl,
      Matrix.one_apply_eq, mul_one]
  have hxx : iform (permLattice TwistTag.E6.perm
      (w • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ)))
      (permLattice TwistTag.E6.perm (w • Pi.single i 1)) = 2 := by
    rw [iform_permLattice_E6, iform_smul, hee]
  rw [iform_add_left, iform_add_right, iform_add_right, hee, hxx,
    iform_comm (permLattice TwistTag.E6.perm _) (Pi.single i 1)] at h2
  have hX : iform (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ)
      (permLattice TwistTag.E6.perm (w • Pi.single i 1)) = -1 := by
    linarith
  have h1 : iform (permLattice TwistTag.E6.perm (Pi.single i 1 + permLattice TwistTag.E6.perm
      (w • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ)))) (w • Pi.single i 1) = 1 := by
    rw [iform_permLattice_left_twE6, iform_add_left, hX, hxx]
    norm_num
  rw [corootPair, h1, hγ]
  norm_num

theorem mem_closure_rootReflection_of_wkMatrix {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {Y : Set (Fin TwistTag.E6.tag.rank → ZMod p)}
    (hY : p ^ 4 ≤ Nat.card Y) {u : WeylGroup TwistTag.E6.tag}
    (hu : ∀ x, u • permLattice TwistTag.E6.perm x = -x) (v : WeylGroup TwistTag.E6.tag)
    (hv : ∀ y ∈ Y, ∀ i, ∑ k, ((wkMatrix v⁻¹ i k : ℤ) : ZMod p) * y k = 0) :
    v * u⁻¹ ∈ Subgroup.closure (rootReflection '' {β | IsRoot TwistTag.E6.tag β ∧
      ∀ y ∈ Y, ∑ k, y k * ((β k : ℤ) : ZMod p) = 0}) := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : Set (Fin TwistTag.E6.tag.rank → ℤ), S = {β | IsRoot TwistTag.E6.tag β ∧
      ∀ y ∈ Y, ∑ k, y k * ((β k : ℤ) : ZMod p) = 0} := ⟨_, rfl⟩
  rw [← hS]
  suffices h : ∀ (m : ℕ) (w : WeylGroup TwistTag.E6.tag),
      (Finset.univ.filter fun j => wkMatrix w j ≠ 0).card = m →
      (∀ y ∈ Y, ∀ i, ∑ k, ((wkMatrix w i k : ℤ) : ZMod p) * y k = 0) →
      w⁻¹ * u⁻¹ ∈ Subgroup.closure (rootReflection '' S) by
    simpa only [inv_inv] using h _ v⁻¹ rfl hv
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro w hm hw
  rcases Certificates.certificate830101 w with
    ⟨i, hi⟩ | hz | ⟨R, C, hdet⟩
  ·
    have hrow := wkMatrix_rootReflection_mul hi w
    have hβS : wkMatrix w i ∈ S := by
      rw [hS]
      refine ⟨hi, fun y hy => ?_⟩
      rw [← hw y hy i]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    have hw' : ∀ y ∈ Y, ∀ j, ∑ k, ((wkMatrix (rootReflection
        (permLattice TwistTag.E6.perm (wkMatrix w i)) * w) j k : ℤ) : ZMod p) * y k = 0 := by
      intro y hy j
      simp only [hrow j, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sub, Int.cast_mul,
        sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, hw y hy j, hw y hy i,
        mul_zero, sub_zero]
    have hsub : (Finset.univ.filter fun j => wkMatrix (rootReflection
        (permLattice TwistTag.E6.perm (wkMatrix w i)) * w) j ≠ 0) ⊆
        Finset.univ.filter fun j => wkMatrix w j ≠ 0 := by
      intro j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro hj hj0
      exact hj (by rw [hrow j, corootPair_eq_zero_of_wkMatrix_eq_zero hj0, zero_smul, sub_zero,
        hj0])
    have hlt := Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).2 ⟨i,
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hi.ne_zero⟩, by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, not_not]
        rw [hrow i, corootPair_wkMatrix_self hi, one_smul, sub_self]⟩)
    rw [hm] at hlt
    have hγ := hi.permLattice TwistTag.E6.cartan_perm
    have e : w⁻¹ * u⁻¹ = (rootReflection (permLattice TwistTag.E6.perm (wkMatrix w i)) * w)⁻¹ *
        u⁻¹ * (u * rootReflection (permLattice TwistTag.E6.perm (wkMatrix w i)) * u⁻¹) := by
      group
    rw [e, ← rootReflection_smul_root u hγ, hu, rootReflection_neg hi]
    exact mul_mem (ih _ hlt _ rfl hw') (Subgroup.subset_closure ⟨_, hβS, rfl⟩)
  ·
    have hu' : ∀ x, u⁻¹ • x = -permLattice TwistTag.E6.perm x := fun x => by
      have h := congrArg (u⁻¹ • ·) (hu x)
      simp only [inv_smul_smul, smul_neg] at h
      rw [h, neg_neg]
    have hw0 : w = u⁻¹ := ext_single fun j => by
      have hj : wkMatrix w j = 0 := by
        rw [hz]
        rfl
      rw [wkMatrix_eq_add] at hj
      have h := congrArg (permLattice TwistTag.E6.perm) (eq_neg_of_add_eq_zero_right hj)
      rw [permLattice_permLattice_twE6] at h
      rw [h, hu']
      rfl
    rw [hw0, inv_inv, mul_inv_cancel]
    exact one_mem _
  ·
    exfalso
    have hker := card_ker_le_of_isUnit_minor (p := p) (wkMatrix w) R C
      (isUnit_intCast_of_mem_wk hp2 hdet)
    have hle : Nat.card Y ≤ Nat.card {y : Fin TwistTag.E6.tag.rank → ZMod p //
        Matrix.mulVec ((wkMatrix w).map (Int.cast : ℤ → ZMod p)) y = 0} :=
      Nat.card_le_card_of_injective (fun y => ⟨y.1, funext fun i => by
        simpa [Matrix.mulVec, dotProduct] using hw y.1 y.2 i⟩)
        fun y y' h => by
          have h' := congrArg Subtype.val h
          exact Subtype.ext h'
    have h34 : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by norm_num)
    exact absurd (hY.trans (hle.trans hker)) (not_le.2 h34)

end Rows

end CFSG.StandardType.TwE6FieldCore

end
