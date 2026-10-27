module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitSymplecticGeometry

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup Matrix Module CFSG.Open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups
open CFSG.ComponentClassification.AS81.Sec2

@[expose] def linearFrameBlock (F : Type) [Field F] (m : ℕ) (k : Fin (m + 1))
    (tail : ℕ := 0) : Subgroup SL(2 * m + 1 + 1 + tail, F) :=
  (blockSL F (2 * m + 1 + 1 + tail) 2 (2 * k.val) (by omega)).range

@[expose] def linearFrameInvolution (F : Type) [Field F] (m : ℕ) (k : Fin (m + 1))
    (tail : ℕ := 0) : SL(2 * m + 1 + 1 + tail, F) :=
  blockSL F (2 * m + 1 + 1 + tail) 2 (2 * k.val) (by omega) (-1)

theorem isLongRootSL2_linearFrameBlock
    {F : Type} [Field F] {m : ℕ} (h2 : (2 : F) ≠ 0) (k : Fin (m + 1))
    (tail : ℕ := 0) :
    IsLongRootSL2 (show 2 ≤ 2 * m + 1 + 1 + tail from by have := k.isLt; omega)
      (linearFrameBlock F m k tail) (linearFrameInvolution F m k tail) := by
  exact isLongRootSL2_range_blockSL h2 (by omega : 2 * k.val + 2 ≤ 2 * m + 1 + 1 + tail)

theorem mem_minusSpace_linearFrameInvolution
    {F : Type} [Field F] {m tail : ℕ} (h2 : (2 : F) ≠ 0) (k : Fin (m + 1))
    {v : Fin (2 * m + 1 + 1 + tail) → F} :
    v ∈ minusSpace (linearFrameInvolution F m k tail) ↔
      ∀ a : Fin (2 * m + 1 + 1 + tail), ¬ (2 * k.val ≤ a.val ∧ a.val < 2 * k.val + 2) → v a = 0 := by
  change v ∈ eigSpace (linearFrameInvolution F m k tail : Matrix (Fin (2 * m + 1 + 1 + tail)) (Fin (2 * m + 1 + 1 + tail)) F) (-1) ↔ _
  rw [linearFrameInvolution, coe_blockSL_neg_one]
  exact mem_eigSpace_negBlock_neg_one_iff h2 _

theorem mem_fixSpace_linearFrameInvolution
    {F : Type} [Field F] {m tail : ℕ} (h2 : (2 : F) ≠ 0) (k : Fin (m + 1))
    {v : Fin (2 * m + 1 + 1 + tail) → F} :
    v ∈ fixSpace (linearFrameInvolution F m k tail) ↔
      ∀ a : Fin (2 * m + 1 + 1 + tail), 2 * k.val ≤ a.val → a.val < 2 * k.val + 2 → v a = 0 := by
  change v ∈ eigSpace (linearFrameInvolution F m k tail : Matrix (Fin (2 * m + 1 + 1 + tail)) (Fin (2 * m + 1 + 1 + tail)) F) 1 ↔ _
  rw [linearFrameInvolution, coe_blockSL_neg_one]
  exact (mem_eigSpace_negBlock_one_iff h2 _).trans (by aesop)

theorem commutes_linearFrameBlock
    {F : Type} [Field F] {m tail : ℕ} {k j : Fin (m + 1)} (hkj : k ≠ j) :
    Commutes (linearFrameBlock F m k tail) (linearFrameBlock F m j tail) := by
  rintro a ⟨A, rfl⟩ b ⟨B, rfl⟩
  exact blockSL_comm (by omega) (by omega) (by
    have hval : k.val ≠ j.val := fun h => hkj (Fin.ext h)
    omega) A B

theorem mulVec_sub_mem_minusSpace_of_mem_longRoot
    {F : Type} [Field F] {n : ℕ} (h2 : (2 : F) ≠ 0)
    {L : Subgroup SL(n, F)} {z : SL(n, F)} {hn : 2 ≤ n}
    (hL : IsLongRootSL2 hn L z) {x : SL(n, F)} (hx : x ∈ L)
    (v : Fin n → F) : (x : Matrix (Fin n) (Fin n) F) *ᵥ v - v ∈ minusSpace z := by
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp
    ((hL.isCompl h2).sup_eq_top ▸ (Submodule.mem_top : v ∈ ⊤))
  have h := (hL.mem_iff_vec h2).mp hx
  have heq : (x : Matrix (Fin n) (Fin n) F) *ᵥ (u + w) - (u + w) =
      (x : Matrix (Fin n) (Fin n) F) *ᵥ u - u := by
    rw [Matrix.mulVec_add, h.1 w hw]
    abel
  rw [heq]
  exact (minusSpace z).sub_mem (h.2 u hu) hu

theorem eigenspaces_of_commutes_linearFrameBlock
    {F : Type} [Field F] {m tail : ℕ} (h2 : (2 : F) ≠ 0)
    (hn3 : 3 ≤ 2 * m + 1 + 1 + tail)
    {L : Subgroup SL(2 * m + 1 + 1 + tail, F)}
    {z : SL(2 * m + 1 + 1 + tail, F)}
    (hL : IsLongRootSL2 (by omega) L z) (j : Fin (m + 1))
    (hc : Commutes L (linearFrameBlock F m j tail)) :
    minusSpace z ≤ fixSpace (linearFrameInvolution F m j tail) ∧
      minusSpace (linearFrameInvolution F m j tail) ≤ fixSpace z := by
  have hne : L ≠ linearFrameBlock F m j tail := by
    intro heq
    rw [heq] at hc
    have e : linearFrameBlock F m j tail ≃* SL(2, F) :=
      (MonoidHom.ofInjective (blockSL_injective (by omega))).symm
    obtain ⟨a, ha, b, hb, hab⟩ := F14.exists_noncommuting_map_of_equiv_sl2
      (MonoidHom.id _) (by simp) e
    exact hab (hc a ha b hb)
  have h := CFSG.ClassicalInvolution.RouteD.Exotic.le_of_commutes h2 hn3
    hL (isLongRootSL2_linearFrameBlock h2 j tail) hne hc
  exact ⟨h.1, h.2.1⟩

@[expose] def linearFrameTriple (m : ℕ) (k : Fin (m + 1)) :
    Finset (Fin (2 * m + 1 + 1 + 1)) :=
  {⟨2 * k.val, by omega⟩, ⟨2 * k.val + 1, by omega⟩, Fin.last (2 * m + 1 + 1)}

theorem mem_linearFrameTriple {m : ℕ} (k : Fin (m + 1))
    (a : Fin (2 * m + 1 + 1 + 1)) :
    a ∈ linearFrameTriple m k ↔
      (2 * k.val ≤ a.val ∧ a.val < 2 * k.val + 2) ∨ a.val = 2 * m + 1 + 1 := by
  simp only [linearFrameTriple, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff,
    Fin.val_last]
  omega

theorem card_linearFrameTriple {m : ℕ} (k : Fin (m + 1)) :
    (linearFrameTriple m k).card = 3 := by
  have h1 : (⟨2 * k.val, by omega⟩ : Fin (2 * m + 1 + 1 + 1)) ≠
      ⟨2 * k.val + 1, by omega⟩ := by
    intro h
    have hh : 2 * k.val = 2 * k.val + 1 := congrArg Fin.val h
    omega
  have h2 : (⟨2 * k.val, by omega⟩ : Fin (2 * m + 1 + 1 + 1)) ≠
      Fin.last (2 * m + 1 + 1) := by
    intro h
    have hh : 2 * k.val = 2 * m + 1 + 1 := congrArg Fin.val h
    omega
  have h3 : (⟨2 * k.val + 1, by omega⟩ : Fin (2 * m + 1 + 1 + 1)) ≠
      Fin.last (2 * m + 1 + 1) := by
    intro h
    have hh : 2 * k.val + 1 = 2 * m + 1 + 1 := congrArg Fin.val h
    omega
  simp [linearFrameTriple, h1, h2, h3]

theorem le_tripleBlock_of_commutes_other_linearFrameBlocks
    {F : Type} [Field F] {m : ℕ} (h2 : (2 : F) ≠ 0)
    {L : Subgroup SL(2 * m + 1 + 1 + 1, F)} {z : SL(2 * m + 1 + 1 + 1, F)}
    (hL : IsLongRootSL2 (by omega) L z) (k : Fin (m + 1))
    (hc : ∀ j : Fin (m + 1), j ≠ k → Commutes L (linearFrameBlock F m j 1)) :
    L ≤ CFSG.SeitzReduction.LinearPilot.blockSpecialLinear (linearFrameTriple m k) := by
  have hspaces := fun j hj => eigenspaces_of_commutes_linearFrameBlock h2 (by omega) hL j (hc j hj)
  have hsupport : ∀ v ∈ minusSpace z, ∀ a : Fin (2 * m + 1 + 1 + 1),
      a ∉ linearFrameTriple m k → v a = 0 := by
    intro v hv a ha
    have ha' := (mem_linearFrameTriple k a).not.mp ha
    let j : Fin (m + 1) := ⟨a.val / 2, by omega⟩
    have hj : j ≠ k := by intro h; have := congrArg Fin.val h; dsimp [j] at this; omega
    exact (mem_fixSpace_linearFrameInvolution h2 j).mp ((hspaces j hj).1 hv) a
      (by dsimp [j]; omega) (by dsimp [j]; omega)
  have hfixed : ∀ a : Fin (2 * m + 1 + 1 + 1), a ∉ linearFrameTriple m k →
      (Pi.single a 1 : Fin (2 * m + 1 + 1 + 1) → F) ∈ fixSpace z := by
    intro a ha
    have ha' := (mem_linearFrameTriple k a).not.mp ha
    let j : Fin (m + 1) := ⟨a.val / 2, by omega⟩
    have hj : j ≠ k := by intro h; have := congrArg Fin.val h; dsimp [j] at this; omega
    apply (hspaces j hj).2
    rw [mem_minusSpace_linearFrameInvolution h2]
    intro b hb
    have hba : b ≠ a := by intro h; subst b; dsimp [j] at hb; omega
    simp [hba]
  intro x hx i j hij
  rcases hij with hi | hj
  · have h := hsupport _ (mulVec_sub_mem_minusSpace_of_mem_longRoot h2 hL hx (Pi.single j 1)) i hi
    simpa [Matrix.mulVec_single_one, Pi.single_apply, eq_comm, Matrix.one_apply] using sub_eq_zero.mp h
  · have h := congrFun (((hL.mem_iff_vec h2).mp hx).1 _ (hfixed j hj)) i
    simpa [Matrix.mulVec_single_one, Pi.single_apply, eq_comm, Matrix.one_apply] using h

theorem not_commutes_all_linearFrameBlocks_odd
    {F : Type} [Field F] {m : ℕ} (h2 : (2 : F) ≠ 0)
    {L : Subgroup SL(2 * m + 1 + 1 + 1, F)} {z : SL(2 * m + 1 + 1 + 1, F)}
    (hL : IsLongRootSL2 (by omega) L z)
    (hc : ∀ j : Fin (m + 1), Commutes L (linearFrameBlock F m j 1)) : False := by
  have hspaces := fun j => eigenspaces_of_commutes_linearFrameBlock h2 (by omega) hL j (hc j)
  let v₀ : Fin (2 * m + 1 + 1 + 1) → F := Pi.single (Fin.last (2 * m + 1 + 1)) 1
  have hline : minusSpace z ≤ Submodule.span F ({v₀} : Set (Fin (2 * m + 1 + 1 + 1) → F)) := by
    intro v hv
    rw [Submodule.mem_span_singleton]
    refine ⟨v (Fin.last (2 * m + 1 + 1)), ?_⟩
    ext a
    by_cases ha : a = Fin.last (2 * m + 1 + 1)
    · subst a
      simp [v₀]
    · have halast : a.val ≠ 2 * m + 1 + 1 := by
        intro h
        exact ha (Fin.ext h)
      let j : Fin (m + 1) := ⟨a.val / 2, by omega⟩
      have hv0 := (mem_fixSpace_linearFrameInvolution h2 j).mp ((hspaces j).1 hv) a
        (by dsimp [j]; omega) (by dsimp [j]; omega)
      simp [v₀, ha, hv0]
  have hv₀ : v₀ ≠ 0 := by
    intro h
    have := congrFun h (Fin.last (2 * m + 1 + 1))
    simp [v₀] at this
  have hdim := Submodule.finrank_mono hline
  rw [hL.finrank_minusSpace h2, finrank_span_singleton hv₀] at hdim
  omega

theorem Lc_eq_blockSpecialLinear
    {F : Type} [Field F] {n : ℕ} (h2 : (2 : F) ≠ 0) (T : Pair n) :
    Lc F T = CFSG.SeitzReduction.LinearPilot.blockSpecialLinear T.1 := by
  ext x
  rw [mem_Lc, CFSG.SeitzReduction.LinearPilot.mem_blockSpecialLinear]
  have hdiag : (1 : Matrix (Fin n) (Fin n) F) + zMat F n T.1 =
      Matrix.diagonal (fun a => if a ∈ T.1 then 0 else 2) := by
    rw [zMat, ← Matrix.diagonal_one, Matrix.diagonal_add]
    congr 1
    ext a
    split_ifs <;> ring
  constructor
  · rintro ⟨hcomm, hfix⟩ i j hij
    rw [hdiag] at hfix
    have hfixij := congrFun (congrFun hfix i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_apply] at hfixij
    by_cases hj : j ∈ T.1
    · have hi : i ∉ T.1 := by rcases hij with hi | h; exact hi; exact False.elim (h hj)
      have hne : i ≠ j := fun h => hi (h ▸ hj)
      rw [Matrix.one_apply_ne hne]
      have hcommij := congrFun (congrFun hcomm i) j
      simp only [zMat, Matrix.mul_diagonal, Matrix.diagonal_mul, hj, hi, ite_true,
        ite_false, mul_neg, mul_one, one_mul] at hcommij
      have hzero : (2 : F) * (x : Matrix (Fin n) (Fin n) F) i j = 0 := by
        linear_combination -hcommij
      exact (mul_eq_zero.mp hzero).resolve_left h2
    · by_cases hne : i = j
      · subst j
        rw [Matrix.one_apply_eq]
        simp only [hj, ite_false, ite_true] at hfixij
        have hzero : (2 : F) * ((x : Matrix (Fin n) (Fin n) F) i i - 1) = 0 := by
          linear_combination hfixij
        exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left h2)
      · rw [Matrix.one_apply_ne hne]
        simp only [hj, ite_false, hne] at hfixij
        exact (mul_eq_zero.mp (by simpa [mul_comm] using hfixij)).resolve_left h2
  · intro hx
    constructor
    · ext i j
      simp only [zMat, Matrix.mul_diagonal, Matrix.diagonal_mul]
      by_cases hi : i ∈ T.1 <;> by_cases hj : j ∈ T.1
      · simp [hi, hj, mul_comm]
      · rw [hx i j (Or.inr hj)]
        have hne : i ≠ j := fun h => hj (h ▸ hi)
        simp [hi, hj, Matrix.one_apply_ne hne]
      · rw [hx i j (Or.inl hi)]
        have hne : i ≠ j := fun h => hi (h ▸ hj)
        simp [hi, hj, Matrix.one_apply_ne hne]
      · simp [hi, hj]
    · rw [hdiag]
      ext i j
      simp only [Matrix.mul_diagonal, Matrix.diagonal_apply]
      by_cases hj : j ∈ T.1
      · by_cases hne : i = j
        · subst j
          simp [hj]
        · simp [hj, hne]
      · rw [hx i j (Or.inr hj)]
        by_cases hne : i = j
        · subst j
          simp [hj]
        · simp [hj, hne]

theorem linearFrameBlock_eq_blockSpecialLinear
    {F : Type} [Field F] {m tail : ℕ} (h2 : (2 : F) ≠ 0) (k : Fin (m + 1)) :
    linearFrameBlock F m k tail = CFSG.SeitzReduction.LinearPilot.blockSpecialLinear
      {⟨2 * k.val, by omega⟩, ⟨2 * k.val + 1, by omega⟩} := by
  have hab : (⟨2 * k.val, by omega⟩ : Fin (2 * m + 1 + 1 + tail)) ≠
      ⟨2 * k.val + 1, by omega⟩ := by
    intro h
    have hh : 2 * k.val = 2 * k.val + 1 := congrArg Fin.val h
    omega
  let T : Pair (2 * m + 1 + 1 + tail) :=
    ⟨{⟨2 * k.val, by omega⟩, ⟨2 * k.val + 1, by omega⟩}, Finset.card_pair hab⟩
  rw [linearFrameBlock, range_blockSL_eq_longRootGroup h2,
    negBlock_eq_zMat (by omega : 2 * k.val + 2 ≤ 2 * m + 1 + 1 + tail)]
  exact Lc_eq_blockSpecialLinear h2 T

theorem disjoint_linearFrameTriple_pair {m : ℕ} {k j : Fin (m + 1)} (hjk : j ≠ k) :
    Disjoint (linearFrameTriple m k)
      ({⟨2 * j.val, by omega⟩, ⟨2 * j.val + 1, by omega⟩} : Finset (Fin (2 * m + 1 + 1 + 1))) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  rw [mem_linearFrameTriple] at ha
  simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff] at hb
  have hne : j.val ≠ k.val := fun h => hjk (Fin.ext h)
  omega

theorem commutes_tripleBlock_linearFrameBlock
    {F : Type} [Field F] {m : ℕ} (h2 : (2 : F) ≠ 0) {k j : Fin (m + 1)} (hjk : j ≠ k) :
    Commutes (CFSG.SeitzReduction.LinearPilot.blockSpecialLinear (K := F) (linearFrameTriple m k))
      (linearFrameBlock F m j 1) := by
  rw [linearFrameBlock_eq_blockSpecialLinear h2]
  intro x hx y hy
  exact (CFSG.SeitzReduction.LinearPilot.commute_blockSpecialLinear_of_disjoint
    (disjoint_linearFrameTriple_pair hjk) hx hy).eq

theorem eq_linearFrameBlock_of_commutes_other_blocks
    {F : Type} [Field F] {m : ℕ} (hm : 1 ≤ m) (h2 : (2 : F) ≠ 0)
    {L : Subgroup SL(2 * m + 1 + 1, F)} {z : SL(2 * m + 1 + 1, F)}
    (hL : IsLongRootSL2 (by omega) L z) (k : Fin (m + 1))
    (hc : ∀ j : Fin (m + 1), j ≠ k → Commutes L (linearFrameBlock F m j)) :
    L = linearFrameBlock F m k := by
  have hspaces : ∀ j : Fin (m + 1), j ≠ k →
      minusSpace z ≤ fixSpace (linearFrameInvolution F m j) ∧
        minusSpace (linearFrameInvolution F m j) ≤ fixSpace z := by
    intro j hj
    have hne : L ≠ linearFrameBlock F m j := by
      intro heq
      have hcomm := hc j hj
      rw [heq] at hcomm
      have e : linearFrameBlock F m j ≃* SL(2, F) :=
        (MonoidHom.ofInjective (blockSL_injective (by omega))).symm
      obtain ⟨a, ha, b, hb, hab⟩ := F14.exists_noncommuting_map_of_equiv_sl2
        (MonoidHom.id _) (by simp) e
      exact hab (hcomm a ha b hb)
    have h := CFSG.ClassicalInvolution.RouteD.Exotic.le_of_commutes h2 (by omega)
      hL (isLongRootSL2_linearFrameBlock h2 j) hne (hc j hj)
    exact ⟨h.1, h.2.1⟩
  have hminus : minusSpace z ≤ minusSpace (linearFrameInvolution F m k) := by
    intro v hv
    rw [mem_minusSpace_linearFrameInvolution h2]
    intro a ha
    let j : Fin (m + 1) := ⟨a.val / 2, by omega⟩
    have hj : j ≠ k := by intro h; have := congrArg Fin.val h; simp [j] at this; omega
    exact (mem_fixSpace_linearFrameInvolution h2 j).mp ((hspaces j hj).1 hv) a
      (by dsimp [j]; omega) (by dsimp [j]; omega)
  have hminusEq : minusSpace z = minusSpace (linearFrameInvolution F m k) :=
    Submodule.eq_of_le_of_finrank_eq hminus
      ((hL.finrank_minusSpace h2).trans
        ((isLongRootSL2_linearFrameBlock h2 k).finrank_minusSpace h2).symm)
  have hfix : fixSpace (linearFrameInvolution F m k) ≤ fixSpace z := by
    intro v hv
    have hsum : v = ∑ a : Fin (2 * m + 1 + 1), v a • Pi.single a 1 := by
      ext b
      simp [Pi.single_apply]
    rw [hsum]
    apply Submodule.sum_mem
    intro a _
    by_cases ha : 2 * k.val ≤ a.val ∧ a.val < 2 * k.val + 2
    · rw [(mem_fixSpace_linearFrameInvolution h2 k).mp hv a ha.1 ha.2, zero_smul]
      exact (fixSpace z).zero_mem
    · let j : Fin (m + 1) := ⟨a.val / 2, by omega⟩
      have hj : j ≠ k := by intro h; have := congrArg Fin.val h; simp [j] at this; omega
      apply (fixSpace z).smul_mem
      apply (hspaces j hj).2
      rw [mem_minusSpace_linearFrameInvolution h2]
      intro b hb
      have hba : b ≠ a := by intro h; subst b; dsimp [j] at hb; omega
      simp [hba]
  have hfixEq : fixSpace z = fixSpace (linearFrameInvolution F m k) := by
    apply (Submodule.eq_of_le_of_finrank_eq hfix ?_).symm
    have h := Submodule.finrank_add_eq_of_isCompl (hL.isCompl h2)
    have h' := Submodule.finrank_add_eq_of_isCompl
      ((isLongRootSL2_linearFrameBlock h2 k).isCompl h2)
    rw [hminusEq] at h
    have hdim : finrank F (Fin (2 * m + 1 + 1 + 0) → F) =
        finrank F (Fin (2 * m + 1 + 1) → F) := rfl
    rw [hdim] at h'
    exact Nat.add_left_cancel (h'.trans h.symm)
  exact CFSG.ClassicalInvolution.RouteD.isLongRootSL2_eq_of_involution_eq h2 hL
    (isLongRootSL2_linearFrameBlock h2 k)
    (CFSG.ClassicalInvolution.RouteD.involution_eq_of_eigenspaces h2 hL hminusEq hfixEq)

@[expose] def linearFramePerm {m : ℕ} (σ : Equiv.Perm (Fin (m + 1))) : Equiv.Perm (Fin (2 * m + 1 + 1)) :=
  let e : Fin (m + 1) × Fin 2 ≃ Fin (2 * m + 1 + 1) :=
    finProdFinEquiv.trans (finCongr (by omega : (m + 1) * 2 = 2 * m + 1 + 1))
  e.symm.trans ((Equiv.prodCongr σ (Equiv.refl (Fin 2))).trans e)

theorem linearFramePerm_pair_first {m : ℕ} (σ : Equiv.Perm (Fin (m + 1))) (k : Fin (m + 1)) :
    linearFramePerm σ ⟨2 * k.val, by omega⟩ = ⟨2 * (σ k).val, by omega⟩ := by
  let e : Fin (m + 1) × Fin 2 ≃ Fin (2 * m + 1 + 1) :=
    finProdFinEquiv.trans (finCongr (by omega : (m + 1) * 2 = 2 * m + 1 + 1))
  have he : e (k, 0) = ⟨2 * k.val, by omega⟩ := by
    apply Fin.ext
    simp [e, finProdFinEquiv, Nat.mul_comm]
  rw [← he]
  change e ((Equiv.prodCongr σ (Equiv.refl (Fin 2))) (e.symm (e (k, 0)))) = _
  rw [e.symm_apply_apply]
  apply Fin.ext
  simp [e, finProdFinEquiv, Nat.mul_comm]

theorem linearFramePerm_pair_second {m : ℕ} (σ : Equiv.Perm (Fin (m + 1))) (k : Fin (m + 1)) :
    linearFramePerm σ ⟨2 * k.val + 1, by omega⟩ = ⟨2 * (σ k).val + 1, by omega⟩ := by
  let e : Fin (m + 1) × Fin 2 ≃ Fin (2 * m + 1 + 1) :=
    finProdFinEquiv.trans (finCongr (by omega : (m + 1) * 2 = 2 * m + 1 + 1))
  have he : e (k, 1) = ⟨2 * k.val + 1, by omega⟩ := by
    apply Fin.ext
    simp [e, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  rw [← he]
  change e ((Equiv.prodCongr σ (Equiv.refl (Fin 2))) (e.symm (e (k, 1)))) = _
  rw [e.symm_apply_apply]
  apply Fin.ext
  simp [e, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

theorem exists_conj_linearFrameBlock_permutation
    {F : Type} [Field F] {m : ℕ} (hm : 1 ≤ m) (h2 : (2 : F) ≠ 0)
    (σ : Equiv.Perm (Fin (m + 1))) : ∃ g : SL(2 * m + 1 + 1, F), ∀ k : Fin (m + 1),
      (linearFrameBlock F m k).map (MulAut.conj g).toMonoidHom =
        linearFrameBlock F m (σ k) := by
  let τ : Equiv.Perm (Fin (2 * m + 1 + 1)) := linearFramePerm σ
  let g : SL(2 * m + 1 + 1, F) := ⟨monoMat F τ, det_monoMat (by omega) τ⟩
  have hg : IsMonomialFor (g : Matrix (Fin (2 * m + 1 + 1)) (Fin (2 * m + 1 + 1)) F) τ :=
    isMonomialFor_monoMat τ
  refine ⟨g, fun k => ?_⟩
  let a : Fin (2 * m + 1 + 1) := ⟨2 * (σ k).val, by omega⟩
  let b : Fin (2 * m + 1 + 1) := ⟨2 * (σ k).val + 1, by omega⟩
  have hab : a ≠ b := by intro h; have := congrArg Fin.val h; dsimp [a, b] at this; omega
  let T : Pair (2 * m + 1 + 1) :=
    ⟨{a, b}, Finset.card_pair hab⟩
  have hT : T.1 = {τ ⟨2 * k.val, by omega⟩, τ ⟨2 * k.val + 1, by omega⟩} := by
    rw [show τ ⟨2 * k.val, by omega⟩ = ⟨2 * (σ k).val, by omega⟩ from
      linearFramePerm_pair_first σ k]
    rw [show τ ⟨2 * k.val + 1, by omega⟩ = ⟨2 * (σ k).val + 1, by omega⟩ from
      linearFramePerm_pair_second σ k]
  have hLc : Lc F T = linearFrameBlock F m (σ k) := by
    rw [linearFrameBlock, range_blockSL_eq_longRootGroup h2]
    have hneg := negBlock_eq_zMat (K := F) (by omega : 2 * (σ k).val + 2 ≤ 2 * m + 1 + 1)
    change longRootGroup (zMat F (2 * m + 1 + 1) T.1) = _
    rw [hneg]
  exact (Lc_eq_map_conj h2 hg (by omega) hT).symm.trans hLc

@[expose] def oddLinearFramePerm {m : ℕ} (σ : Equiv.Perm (Fin (m + 1))) :
    Equiv.Perm (Fin (2 * m + 1 + 1 + 1)) :=
  let e : Fin (2 * m + 1 + 1) ⊕ Fin 1 ≃ Fin (2 * m + 1 + 1 + 1) := finSumFinEquiv
  e.symm.trans ((Equiv.sumCongr (linearFramePerm σ) (Equiv.refl (Fin 1))).trans e)

theorem oddLinearFramePerm_pair_first {m : ℕ} (σ : Equiv.Perm (Fin (m + 1)))
    (k : Fin (m + 1)) :
    oddLinearFramePerm σ ⟨2 * k.val, by omega⟩ = ⟨2 * (σ k).val, by omega⟩ := by
  let e : Fin (2 * m + 1 + 1) ⊕ Fin 1 ≃ Fin (2 * m + 1 + 1 + 1) := finSumFinEquiv
  have he : e (Sum.inl ⟨2 * k.val, by omega⟩) = ⟨2 * k.val, by omega⟩ := by
    apply Fin.ext
    simp [e, finSumFinEquiv]
  rw [← he]
  change e ((Equiv.sumCongr (linearFramePerm σ) (Equiv.refl (Fin 1)))
    (e.symm (e (Sum.inl ⟨2 * k.val, by omega⟩)))) = _
  rw [e.symm_apply_apply]
  simp only [Equiv.sumCongr_apply, Sum.map_inl, linearFramePerm_pair_first]
  apply Fin.ext
  simp [e, finSumFinEquiv]

theorem oddLinearFramePerm_pair_second {m : ℕ} (σ : Equiv.Perm (Fin (m + 1)))
    (k : Fin (m + 1)) :
    oddLinearFramePerm σ ⟨2 * k.val + 1, by omega⟩ = ⟨2 * (σ k).val + 1, by omega⟩ := by
  let e : Fin (2 * m + 1 + 1) ⊕ Fin 1 ≃ Fin (2 * m + 1 + 1 + 1) := finSumFinEquiv
  have he : e (Sum.inl ⟨2 * k.val + 1, by omega⟩) = ⟨2 * k.val + 1, by omega⟩ := by
    apply Fin.ext
    simp [e, finSumFinEquiv]
  rw [← he]
  change e ((Equiv.sumCongr (linearFramePerm σ) (Equiv.refl (Fin 1)))
    (e.symm (e (Sum.inl ⟨2 * k.val + 1, by omega⟩)))) = _
  rw [e.symm_apply_apply]
  simp only [Equiv.sumCongr_apply, Sum.map_inl, linearFramePerm_pair_second]
  apply Fin.ext
  simp [e, finSumFinEquiv]

theorem exists_conj_oddLinearFrameBlock_permutation
    {F : Type} [Field F] {m : ℕ} (h2 : (2 : F) ≠ 0)
    (σ : Equiv.Perm (Fin (m + 1))) :
    ∃ g : SL(2 * m + 1 + 1 + 1, F), ∀ k : Fin (m + 1),
      (linearFrameBlock F m k 1).map (MulAut.conj g).toMonoidHom =
        linearFrameBlock F m (σ k) 1 := by
  let τ : Equiv.Perm (Fin (2 * m + 1 + 1 + 1)) := oddLinearFramePerm σ
  let g : SL(2 * m + 1 + 1 + 1, F) := ⟨monoMat F τ, det_monoMat (by omega) τ⟩
  have hg : IsMonomialFor (g : Matrix (Fin (2 * m + 1 + 1 + 1)) (Fin (2 * m + 1 + 1 + 1)) F) τ :=
    isMonomialFor_monoMat τ
  refine ⟨g, fun k => ?_⟩
  let a : Fin (2 * m + 1 + 1 + 1) := ⟨2 * (σ k).val, by omega⟩
  let b : Fin (2 * m + 1 + 1 + 1) := ⟨2 * (σ k).val + 1, by omega⟩
  have hab : a ≠ b := by
    intro h
    have hh : 2 * (σ k).val = 2 * (σ k).val + 1 := congrArg Fin.val h
    omega
  let T : Pair (2 * m + 1 + 1 + 1) := ⟨{a, b}, Finset.card_pair hab⟩
  have hT : T.1 = {τ ⟨2 * k.val, by omega⟩, τ ⟨2 * k.val + 1, by omega⟩} := by
    rw [show τ ⟨2 * k.val, by omega⟩ = ⟨2 * (σ k).val, by omega⟩ from
      oddLinearFramePerm_pair_first σ k]
    rw [show τ ⟨2 * k.val + 1, by omega⟩ = ⟨2 * (σ k).val + 1, by omega⟩ from
      oddLinearFramePerm_pair_second σ k]
  have hLc : Lc F T = linearFrameBlock F m (σ k) 1 := by
    rw [linearFrameBlock, range_blockSL_eq_longRootGroup h2]
    have hneg := negBlock_eq_zMat (K := F)
      (by omega : 2 * (σ k).val + 2 ≤ 2 * m + 1 + 1 + 1)
    change longRootGroup (zMat F (2 * m + 1 + 1 + 1) T.1) = _
    rw [hneg]
  exact (Lc_eq_map_conj h2 hg (by omega) hT).symm.trans hLc

theorem lieModel_tripleBlock_map_quotient
    {X : Type} [Group X] {p f m : ℕ} [hp : Fact p.Prime] (hf : 1 ≤ f)
    (ψ : SL(2 * m + 1 + 1 + 1, GaloisField p f) →* X) (k : Fin (m + 1))
    (hne : (CFSG.SeitzReduction.LinearPilot.blockSpecialLinear
      (K := GaloisField p f) (linearFrameTriple m k)).map ψ ≠ ⊥) :
    CFSG.Blueprint.LieModel
      (((CFSG.SeitzReduction.LinearPilot.blockSpecialLinear
        (K := GaloisField p f) (linearFrameTriple m k)).map ψ) ⧸
        center ((CFSG.SeitzReduction.LinearPilot.blockSpecialLinear
          (K := GaloisField p f) (linearFrameTriple m k)).map ψ)) .PSL 3 p f := by
  classical
  let F := GaloisField p f
  let I := linearFrameTriple m k
  let D := CFSG.SeitzReduction.LinearPilot.blockSpecialLinear (K := F) I
  let eI : Fin 3 ≃ I :=
    (finCongr (card_linearFrameTriple k).symm).trans I.equivFin.symm
  let φ : SL(3, F) →* SL(2 * m + 1 + 1 + 1, F) :=
    (CFSG.SeitzReduction.LinearPilot.blockEmbed I).comp
      (CFSG.SeitzReduction.LinearPilot.reindexSpecialLinear (K := F) eI).toMonoidHom
  have hφ : φ.range = D := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr
      (CFSG.SeitzReduction.LinearPilot.reindexSpecialLinear (K := F) eI).surjective,
      ← MonoidHom.range_eq_map, CFSG.SeitzReduction.LinearPilot.range_blockEmbed]
  let η : SL(3, F) →* X := ψ.comp φ
  have hη : η.range = D.map ψ := by rw [MonoidHom.range_comp, hφ]
  have hηne : η.range ≠ ⊥ := by rwa [hη]
  have hnt : ∃ x, η.rangeRestrict x ≠ 1 := by
    obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hηne
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, fun h => hy1 h⟩
  have hQ : CFSG.IsQuasisimple SL(3, F) :=
    CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 F (by omega)
  have hmodel := CFSG.Timmesfeld.lieModel_SL3_quotient hp.out hf
    (GaloisField.card p f (by omega))
  have hmodel' := CFSG.Timmesfeld.lieModel_quotient_of_surjective hQ hmodel
    η.rangeRestrict_surjective hnt
  exact CFSG.Blueprint.LieModel.quotient_center_of_mulEquiv
    (MulEquiv.subgroupCongr hη) hmodel'


theorem linearFrameBlock_mem_fundamentalSubgroups
    {p f m : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (k : Fin (m + 1)) :
    linearFrameBlock (GaloisField p f) m k ∈
      fundamentalSubgroups .PSL (modelUniv .PSL (2 * m + 1 + 1) p f hp.out).D := by
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.RouteD.two_ne_zero_galoisField hp2
  have hR : linearFrameBlock (GaloisField p f) m k ∈
      longRootSet (K := GaloisField p f) (by omega : 2 ≤ (2 * m + 1) + 1) :=
    ⟨linearFrameInvolution (GaloisField p f) m k, isLongRootSL2_linearFrameBlock h2 k⟩
  have h := CFSG.ClassicalInvolution.RouteD.longRootSet_subset_fundamentalSubgroups_psl
    (m := 2 * m + 1) (by omega : 2 ≤ (2 * m + 1) + 1) hR
  change linearFrameBlock (GaloisField p f) m k ∈ fundamentalSubgroups .PSL
    (CFSG.LieType.Universal.SpecialLinear.rootDatum (2 * m + 1) (GaloisField p f))
  exact h

theorem Lc_mem_fundamentalSubgroups_psl_odd
    {p f m : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (T : Pair (2 * m + 1 + 1 + 1)) :
    Lc (GaloisField p f) T ∈ fundamentalSubgroups .PSL
      (modelUniv .PSL (2 * m + 1 + 1 + 1) p f hp.out).D := by
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.RouteD.two_ne_zero_galoisField hp2
  have hR := Lc_mem_longRootSet h2 (by omega : 2 ≤ 2 * m + 1 + 1 + 1) T
  have h := CFSG.ClassicalInvolution.RouteD.longRootSet_subset_fundamentalSubgroups_psl
    (m := 2 * m + 1 + 1) (by omega : 2 ≤ (2 * m + 1 + 1) + 1) hR
  change Lc (GaloisField p f) T ∈ fundamentalSubgroups .PSL
    (CFSG.LieType.Universal.SpecialLinear.rootDatum (2 * m + 1 + 1) (GaloisField p f))
  exact h

theorem oddLinearFrameBlock_mem_fundamentalSubgroups
    {p f m : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (k : Fin (m + 1)) :
    linearFrameBlock (GaloisField p f) m k 1 ∈ fundamentalSubgroups .PSL
      (modelUniv .PSL (2 * m + 1 + 1 + 1) p f hp.out).D := by
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.RouteD.two_ne_zero_galoisField hp2
  have hR : linearFrameBlock (GaloisField p f) m k 1 ∈
      longRootSet (K := GaloisField p f) (by omega : 2 ≤ (2 * m + 1 + 1) + 1) :=
    ⟨linearFrameInvolution (GaloisField p f) m k 1, isLongRootSL2_linearFrameBlock h2 k 1⟩
  have h := CFSG.ClassicalInvolution.RouteD.longRootSet_subset_fundamentalSubgroups_psl
    (m := 2 * m + 1 + 1) (by omega : 2 ≤ (2 * m + 1 + 1) + 1) hR
  change linearFrameBlock (GaloisField p f) m k 1 ∈ fundamentalSubgroups .PSL
    (CFSG.LieType.Universal.SpecialLinear.rootDatum (2 * m + 1 + 1) (GaloisField p f))
  exact h

theorem map_linear_fundamental_eq_of_commutes_other_coordinates
    {X : Type} [Group X] {p f m : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hm : 1 ≤ m) (hadm : StatedLieAdmissible .PSL (2 * m + 1 + 1) p f)
    (ψ : SL(2 * m + 1 + 1, GaloisField p f) →* X)
    (hker : ψ.ker ≤ center SL(2 * m + 1 + 1, GaloisField p f))
    {R : Subgroup SL(2 * m + 1 + 1, GaloisField p f)}
    (hR : R ∈ fundamentalSubgroups .PSL (modelUniv .PSL (2 * m + 1 + 1) p f hp.out).D)
    (k : Fin (m + 1)) (hc : ∀ j : Fin (m + 1), j ≠ k →
      Commutes (R.map ψ) ((linearFrameBlock (GaloisField p f) m j).map ψ)) :
    R.map ψ = (linearFrameBlock (GaloisField p f) m k).map ψ := by
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.RouteD.two_ne_zero_galoisField hp2
  change R ∈ fundamentalSubgroups .PSL
    (CFSG.LieType.Universal.SpecialLinear.rootDatum (2 * m + 1) (GaloisField p f)) at hR
  have hRlong := CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset
    (m := 2 * m + 1) (by omega : 2 ≤ (2 * m + 1) + 1)
    hR
  obtain ⟨z, hz⟩ := hRlong
  have hcR : ∀ j : Fin (m + 1), j ≠ k → Commutes R (linearFrameBlock (GaloisField p f) m j) :=
    fun j hj => commutes_modelFund_of_commutes_map hp2 (by trivial) hadm ψ hker hR (hc j hj)
  rw [eq_linearFrameBlock_of_commutes_other_blocks hm h2 hz k hcR]


theorem exists_full_coordinate_frame_funSet_psl_even
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p m f : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (hadm : StatedLieAdmissible .PSL (2 * m + 1 + 1) p f) (hX : CFSG.Blueprint.LieModel X .PSL (2 * m + 1 + 1) p f)
    (ψ : SL(2 * m + 1 + 1, GaloisField p f) →* X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ center SL(2 * m + 1 + 1, GaloisField p f)) (P : Sylow 2 X) :
    ∃ c : X,
      F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X) =
        Set.range (fun k : Fin (m + 1) =>
          ((linearFrameBlock (GaloisField p f) m k).map ψ).map (MulAut.conj c).toMonoidHom) := by
  let F := GaloisField p f
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.RouteD.two_ne_zero_galoisField hp2
  have hmodel : ∀ k : Fin (m + 1), linearFrameBlock F m k ∈
      fundamentalSubgroups .PSL (modelUniv .PSL (2 * m + 1 + 1) p f hp.out).D := fun k =>
    linearFrameBlock_mem_fundamentalSubgroups hp2 hm k
  let A : Fin (m + 1) → Subgroup X := fun k => (linearFrameBlock F m k).map ψ
  have hA : ∀ k, IsFundamentalOver (p ^ f) (A k) := fun k =>
    ⟨.PSL, 2 * m + 1 + 1, p, f, hp.out, hp2, rfl, trivial, hadm, ψ, hψ, hker,
      linearFrameBlock F m k, hmodel k, rfl⟩
  have hblockcomm : ∀ {k j : Fin (m + 1)}, k ≠ j →
      Commutes (linearFrameBlock F m k) (linearFrameBlock F m j) := fun h => commutes_linearFrameBlock h
  have hcomm : ∀ k j, k ≠ j → Commutes (A k) (A j) := by
    intro k j hkj a ha b hb
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.mp hb
    simpa only [map_mul] using congrArg ψ (hblockcomm hkj a₀ ha₀ b₀ hb₀)
  have hnorm : ∀ k j, A j ≤ normalizer (A k : Set X) := by
    intro k j
    by_cases hkj : k = j
    · rw [hkj]
      exact Subgroup.le_normalizer
    · have hc : A j ≤ centralizer (A k : Set X) := by
        intro a ha
        exact Subgroup.mem_centralizer_iff.mpr fun b hb => hcomm k j hkj b hb a ha
      exact hc.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨c, hc⟩ := F14.exists_conj_family_mem_funSet (𝔉 := fundPred (p ^ f))
    (fun g _ h => isFundamentalOver_map_mulEquiv (MulAut.conj g) h) A hA hnorm P
  let ψc : SL(2 * m + 1 + 1, F) →* X := (MulAut.conj c).toMonoidHom.comp ψ
  have hψc : Function.Surjective ψc := (MulAut.conj c).surjective.comp hψ
  have hkerC : ψc.ker ≤ center SL(2 * m + 1 + 1, F) := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact (MulAut.conj c).injective (by simpa [ψc] using hx)
  have hc' : ∀ k, (linearFrameBlock F m k).map ψc ∈
      F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X) := by
    intro k
    simpa [A, ψc, Subgroup.map_map] using hc k
  let k0 : Fin (m + 1) := 0
  obtain ⟨hZ, _, hL2, hΩ⟩ := fundamental_ambient_of_lieModel hp.out hp2 hadm hX
    (by simp; omega) (hc' k0).1
  have hdesc : ∃ (t : StatedLieTag) (n e : ℕ), StatedLieAdmissible t n p e ∧
      p ^ f = p ^ e ∧ CFSG.Blueprint.LieModel (X ⧸ center X) t n p e :=
    ⟨.PSL, 2 * m + 1 + 1, f, hadm, rfl, hX.quotient_center hZ⟩
  refine ⟨c, ?_⟩
  ext L
  constructor
  · intro hL
    by_contra hnot
    have hne : ∀ k, L ≠ (linearFrameBlock F m k).map ψc := by
      intro k heq
      apply hnot
      exact ⟨k, by simpa [A, ψc, Subgroup.map_map] using heq.symm⟩
    obtain ⟨R, hR, hLR, _⟩ := exists_mem_fundamentalSubgroups_of_isFundamentalOver_general
      hp.out hp2 hadm hX (by trivial) (by simp; omega) hL2 ψc hψc hkerC hL.1
    let R' : Subgroup SL(2 * m + 1 + 1, F) := R
    have hR' : R' ∈ fundamentalSubgroups .PSL (modelUniv .PSL (2 * m + 1 + 1) p f hp.out).D := hR
    have hLR' : L = R'.map ψc := hLR
    have hcR : ∀ k, Commutes (R'.map ψc) ((linearFrameBlock F m k).map ψc) := by
      intro k
      rw [← hLR']
      have h := CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.funSet_commute_of_lieModel
        hp.out hp2 hdesc hL2 P hL (hc' k) (hne k)
      exact fun a ha b hb => (Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h ha) b hb).symm
    have heq := map_linear_fundamental_eq_of_commutes_other_coordinates
      hp2 hm hadm ψc hkerC hR' k0 (fun j _ => hcR j)
    exact hne k0 (hLR'.trans heq)
  · rintro ⟨k, rfl⟩
    exact hc k


theorem nonempty_equiv_perm_funSet_psl_even
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p m f : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (hadm : StatedLieAdmissible .PSL (2 * m + 1 + 1) p f) (hX : CFSG.Blueprint.LieModel X .PSL (2 * m + 1 + 1) p f)
    (P : Sylow 2 X) :
    let Δ := F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X)
    Nonempty ((conjPermHom (le_refl (conjSetStab Δ))).range ≃* Equiv.Perm (Fin (m + 1))) := by
  obtain ⟨ψ0, hψ0, hker0⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    .PSL (2 * m + 1 + 1) p f hp.out hp2 (by trivial) hadm X hX
  let ψ : SL(2 * m + 1 + 1, GaloisField p f) →* X := ψ0
  have hψ : Function.Surjective ψ := hψ0
  have hker : ψ.ker ≤ center SL(2 * m + 1 + 1, GaloisField p f) := hker0
  obtain ⟨c, hfull⟩ := exists_full_coordinate_frame_funSet_psl_even hp2 hm hadm hX ψ hψ hker P
  let ψc : SL(2 * m + 1 + 1, GaloisField p f) →* X := (MulAut.conj c).toMonoidHom.comp ψ
  have hkerC : ψc.ker ≤ center SL(2 * m + 1 + 1, GaloisField p f) := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact (MulAut.conj c).injective (by simpa [ψc] using hx)
  have hfull' : F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X) =
      Set.range (fun k : Fin (m + 1) => (linearFrameBlock (GaloisField p f) m k).map ψc) := by
    simpa [ψc, Subgroup.map_map] using hfull
  rw [hfull']
  classical
  let Δ := Set.range (fun k : Fin (m + 1) => (linearFrameBlock (GaloisField p f) m k).map ψc)
  let d : Fin (m + 1) → Δ := fun k => ⟨(linearFrameBlock (GaloisField p f) m k).map ψc, ⟨k, rfl⟩⟩
  have hd : Function.Bijective d := by
    constructor
    · intro i j heq
      by_contra hij
      exact F14.map_ne_of_commuting_of_equiv_sl2 ψc hkerC
        ((MonoidHom.ofInjective (blockSL_injective (by omega : 2 * i.val + 2 ≤ 2 * m + 1 + 1))).symm)
        (fun a ha b hb => commutes_linearFrameBlock (tail := 0) hij a ha b hb) (congrArg Subtype.val heq)
    · rintro ⟨L, k, rfl⟩
      exact ⟨k, rfl⟩
  let e : Fin (m + 1) ≃ Δ := Equiv.ofBijective d hd
  have hρ : Function.Surjective (conjPermHom (le_refl (conjSetStab Δ))) :=
    surjective_conjPermHom_of_indexed_conjugations e fun σ => by
      obtain ⟨g, hg⟩ := exists_conj_linearFrameBlock_permutation hm
        (CFSG.ClassicalInvolution.RouteD.two_ne_zero_galoisField hp2) σ
      refine ⟨ψc g, fun k => ?_⟩
      change ((linearFrameBlock (GaloisField p f) m k).map ψc).map
        (MulAut.conj (ψc g)).toMonoidHom =
          (linearFrameBlock (GaloisField p f) m (σ k)).map ψc
      have hhom : (MulAut.conj (ψc g)).toMonoidHom.comp ψc =
          ψc.comp (MulAut.conj g).toMonoidHom := by
        ext x
        simp [MulAut.conj_apply]
      rw [Subgroup.map_map, hhom, ← Subgroup.map_map, hg]
  have htop := MonoidHom.range_eq_top.mpr hρ
  exact ⟨(MulEquiv.subgroupCongr htop).trans
    (Subgroup.topEquiv.trans e.symm.permCongrHom)⟩

theorem centralizingLayer_funSet_eq_of_psl_even
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p m f : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (hadm : StatedLieAdmissible .PSL (2 * m + 1 + 1) p f) (hX : CFSG.Blueprint.LieModel X .PSL (2 * m + 1 + 1) p f)
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X)) :
    centralizingLayer {L : Subgroup X | IsFundamentalOver (p ^ f) L}
      {x : X | ∃ L ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X),
        L ≠ K ∧ x ∈ L} = K := by
  obtain ⟨ψ0, hψ0, hker0⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    .PSL (2 * m + 1 + 1) p f hp.out hp2 (by trivial) hadm X hX
  let ψ : SL(2 * m + 1 + 1, GaloisField p f) →* X := ψ0
  have hψ : Function.Surjective ψ := hψ0
  have hker : ψ.ker ≤ center SL(2 * m + 1 + 1, GaloisField p f) := hker0
  obtain ⟨c, hfull⟩ := exists_full_coordinate_frame_funSet_psl_even hp2 hm hadm hX ψ hψ hker P
  let F := GaloisField p f
  let ψc : SL(2 * m + 1 + 1, F) →* X := (MulAut.conj c).toMonoidHom.comp ψ
  have hψc : Function.Surjective ψc := (MulAut.conj c).surjective.comp hψ
  have hkerC : ψc.ker ≤ center SL(2 * m + 1 + 1, F) := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact (MulAut.conj c).injective (by simpa [ψc] using hx)
  have hfull' : F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X) =
      Set.range (fun k : Fin (m + 1) => (linearFrameBlock F m k).map ψc) := by
    simpa [ψc, Subgroup.map_map] using hfull
  have hKrange : K ∈ Set.range (fun k : Fin (m + 1) => (linearFrameBlock F m k).map ψc) := hfull' ▸ hK
  obtain ⟨k, rfl⟩ := hKrange
  have hinj : Function.Injective (fun j : Fin (m + 1) => (linearFrameBlock F m j).map ψc) := by
    intro i j heq
    by_contra hij
    exact F14.map_ne_of_commuting_of_equiv_sl2 ψc hkerC
      ((MonoidHom.ofInjective (blockSL_injective (by omega : 2 * i.val + 2 ≤ 2 * m + 1 + 1))).symm)
      (fun a ha b hb => commutes_linearFrameBlock (tail := 0) hij a ha b hb) heq
  have hΓ : {x : X | ∃ L ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X),
      L ≠ (linearFrameBlock F m k).map ψc ∧ x ∈ L} =
      {x : X | ∃ j : Fin (m + 1), j ≠ k ∧ x ∈ (linearFrameBlock F m j).map ψc} := by
    ext x
    constructor
    · rintro ⟨L, hL, hne, hx⟩
      rw [hfull'] at hL
      obtain ⟨j, rfl⟩ := hL
      exact ⟨j, fun h => hne (h ▸ rfl), hx⟩
    · rintro ⟨j, hne, hx⟩
      exact ⟨(linearFrameBlock F m j).map ψc, hfull'.symm ▸ ⟨j, rfl⟩,
        fun h => hne (hinj h), hx⟩
  obtain ⟨_, _, hL2, _⟩ := fundamental_ambient_of_lieModel hp.out hp2 hadm hX
    (by simp; omega) hK.1
  have hreal : ∀ L ∈ {L : Subgroup X | IsFundamentalOver (p ^ f) L},
      ∃ R ∈ fundamentalSubgroups .PSL (modelUniv .PSL (2 * m + 1 + 1) p f hp.out).D, L = R.map ψc := by
    intro L hL
    obtain ⟨R, hR, heq, _⟩ := exists_mem_fundamentalSubgroups_of_isFundamentalOver_general
      hp.out hp2 hadm hX (by trivial) (by simp; omega) hL2 ψc hψc hkerC hL
    exact ⟨R, hR, heq⟩
  have hΩ : ∀ j : Fin (m + 1), (linearFrameBlock F m j).map ψc ∈
      {L : Subgroup X | IsFundamentalOver (p ^ f) L} := fun j =>
    (show (linearFrameBlock F m j).map ψc ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X) from
      hfull'.symm ▸ ⟨j, rfl⟩).1
  rw [hΓ]
  let Γ := {x : X | ∃ j : Fin (m + 1), j ≠ k ∧ x ∈ (linearFrameBlock F m j).map ψc}
  apply le_antisymm
  · refine iSup₂_le fun L hL => ?_
    obtain ⟨R, hR, rfl⟩ := hreal L hL.1
    let R' : Subgroup SL(2 * m + 1 + 1, F) := R
    have hR' : R' ∈ fundamentalSubgroups .PSL (modelUniv .PSL (2 * m + 1 + 1) p f hp.out).D := hR
    have hcR : ∀ j : Fin (m + 1), j ≠ k →
        Commutes (R'.map ψc) ((linearFrameBlock F m j).map ψc) := by
      intro j hj a ha b hb
      exact (Subgroup.mem_centralizer_iff.mp (hL.2 ha) b ⟨j, hj, hb⟩).symm
    have heq := map_linear_fundamental_eq_of_commutes_other_coordinates
      hp2 hm hadm ψc hkerC hR' k hcR
    exact heq.le
  · have hcentral : (linearFrameBlock F m k).map ψc ≤ centralizer Γ := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      rintro b ⟨j, hj, hb⟩
      obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.mp hb
      simpa only [map_mul] using (congrArg ψc (commutes_linearFrameBlock (tail := 0) hj.symm a₀ ha₀ b₀ hb₀)).symm
    exact le_centralizingLayer ⟨hΩ k, hcentral⟩

theorem exists_full_coordinate_frame_funSet_psl_odd
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p m f : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (hadm : StatedLieAdmissible .PSL (2 * m + 1 + 1 + 1) p f) (hX : CFSG.Blueprint.LieModel X .PSL (2 * m + 1 + 1 + 1) p f)
    (ψ : SL(2 * m + 1 + 1 + 1, GaloisField p f) →* X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ center SL(2 * m + 1 + 1 + 1, GaloisField p f)) (P : Sylow 2 X) :
    ∃ c : X,
      F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X) =
        Set.range (fun k : Fin (m + 1) =>
          ((linearFrameBlock (GaloisField p f) m k 1).map ψ).map (MulAut.conj c).toMonoidHom) := by
  let F := GaloisField p f
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.RouteD.two_ne_zero_galoisField hp2
  have hmodel : ∀ k : Fin (m + 1), linearFrameBlock F m k 1 ∈
      fundamentalSubgroups .PSL (modelUniv .PSL (2 * m + 1 + 1 + 1) p f hp.out).D := fun k =>
    oddLinearFrameBlock_mem_fundamentalSubgroups hp2 k
  let A : Fin (m + 1) → Subgroup X := fun k => (linearFrameBlock F m k 1).map ψ
  have hA : ∀ k, IsFundamentalOver (p ^ f) (A k) := fun k =>
    ⟨.PSL, 2 * m + 1 + 1 + 1, p, f, hp.out, hp2, rfl, trivial, hadm, ψ, hψ, hker,
      linearFrameBlock F m k 1, hmodel k, rfl⟩
  have hblockcomm : ∀ {k j : Fin (m + 1)}, k ≠ j →
      Commutes (linearFrameBlock F m k 1) (linearFrameBlock F m j 1) := fun h => commutes_linearFrameBlock (tail := 1) h
  have hcomm : ∀ k j, k ≠ j → Commutes (A k) (A j) := by
    intro k j hkj a ha b hb
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.mp hb
    simpa only [map_mul] using congrArg ψ (hblockcomm hkj a₀ ha₀ b₀ hb₀)
  have hnorm : ∀ k j, A j ≤ normalizer (A k : Set X) := by
    intro k j
    by_cases hkj : k = j
    · rw [hkj]
      exact Subgroup.le_normalizer
    · have hc : A j ≤ centralizer (A k : Set X) := by
        intro a ha
        exact Subgroup.mem_centralizer_iff.mpr fun b hb => hcomm k j hkj b hb a ha
      exact hc.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨c, hc⟩ := F14.exists_conj_family_mem_funSet (𝔉 := fundPred (p ^ f))
    (fun g _ h => isFundamentalOver_map_mulEquiv (MulAut.conj g) h) A hA hnorm P
  let ψc : SL(2 * m + 1 + 1 + 1, F) →* X := (MulAut.conj c).toMonoidHom.comp ψ
  have hψc : Function.Surjective ψc := (MulAut.conj c).surjective.comp hψ
  have hkerC : ψc.ker ≤ center SL(2 * m + 1 + 1 + 1, F) := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact (MulAut.conj c).injective (by simpa [ψc] using hx)
  have hc' : ∀ k, (linearFrameBlock F m k 1).map ψc ∈
      F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X) := by
    intro k
    simpa [A, ψc, Subgroup.map_map] using hc k
  let k0 : Fin (m + 1) := 0
  obtain ⟨hZ, _, hL2, hΩ⟩ := fundamental_ambient_of_lieModel hp.out hp2 hadm hX
    (by simp) (hc' k0).1
  have hdesc : ∃ (t : StatedLieTag) (n e : ℕ), StatedLieAdmissible t n p e ∧
      p ^ f = p ^ e ∧ CFSG.Blueprint.LieModel (X ⧸ center X) t n p e :=
    ⟨.PSL, 2 * m + 1 + 1 + 1, f, hadm, rfl, hX.quotient_center hZ⟩
  refine ⟨c, ?_⟩
  ext L
  constructor
  · intro hL
    by_contra hnot
    have hne : ∀ k, L ≠ (linearFrameBlock F m k 1).map ψc := by
      intro k heq
      apply hnot
      exact ⟨k, by simpa [A, ψc, Subgroup.map_map] using heq.symm⟩
    obtain ⟨R, hR, hLR, _⟩ := exists_mem_fundamentalSubgroups_of_isFundamentalOver_general
      hp.out hp2 hadm hX (by trivial) (by simp) hL2 ψc hψc hkerC hL.1
    let R' : Subgroup SL(2 * m + 1 + 1 + 1, F) := R
    have hR' : R' ∈ fundamentalSubgroups .PSL (modelUniv .PSL (2 * m + 1 + 1 + 1) p f hp.out).D := hR
    have hLR' : L = R'.map ψc := hLR
    have hcR : ∀ k, Commutes (R'.map ψc) ((linearFrameBlock F m k 1).map ψc) := by
      intro k
      rw [← hLR']
      have h := CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.funSet_commute_of_lieModel
        hp.out hp2 hdesc hL2 P hL (hc' k) (hne k)
      exact fun a ha b hb => (Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h ha) b hb).symm
    have hcR' : ∀ k, Commutes R' (linearFrameBlock F m k 1) := fun k =>
      commutes_modelFund_of_commutes_map hp2 (by trivial) hadm ψc hkerC hR' (hcR k)
    change R' ∈ fundamentalSubgroups .PSL
      (CFSG.LieType.Universal.SpecialLinear.rootDatum (2 * m + 1 + 1) F) at hR'
    obtain ⟨z, hz⟩ := CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset
      (m := 2 * m + 1 + 1) (by omega : 2 ≤ (2 * m + 1 + 1) + 1) hR'
    exact not_commutes_all_linearFrameBlocks_odd h2 hz hcR'
  · rintro ⟨k, rfl⟩
    exact hc k


theorem nonempty_equiv_perm_funSet_psl_odd
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p m f : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (hadm : StatedLieAdmissible .PSL (2 * m + 1 + 1 + 1) p f) (hX : CFSG.Blueprint.LieModel X .PSL (2 * m + 1 + 1 + 1) p f)
    (P : Sylow 2 X) :
    let Δ := F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X)
    Nonempty ((conjPermHom (le_refl (conjSetStab Δ))).range ≃* Equiv.Perm (Fin (m + 1))) := by
  obtain ⟨ψ0, hψ0, hker0⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    .PSL (2 * m + 1 + 1 + 1) p f hp.out hp2 (by trivial) hadm X hX
  let ψ : SL(2 * m + 1 + 1 + 1, GaloisField p f) →* X := ψ0
  have hψ : Function.Surjective ψ := hψ0
  have hker : ψ.ker ≤ center SL(2 * m + 1 + 1 + 1, GaloisField p f) := hker0
  obtain ⟨c, hfull⟩ := exists_full_coordinate_frame_funSet_psl_odd hp2 hm hadm hX ψ hψ hker P
  let ψc : SL(2 * m + 1 + 1 + 1, GaloisField p f) →* X := (MulAut.conj c).toMonoidHom.comp ψ
  have hkerC : ψc.ker ≤ center SL(2 * m + 1 + 1 + 1, GaloisField p f) := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact (MulAut.conj c).injective (by simpa [ψc] using hx)
  have hfull' : F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X) =
      Set.range (fun k : Fin (m + 1) => (linearFrameBlock (GaloisField p f) m k 1).map ψc) := by
    simpa [ψc, Subgroup.map_map] using hfull
  rw [hfull']
  classical
  let Δ := Set.range (fun k : Fin (m + 1) => (linearFrameBlock (GaloisField p f) m k 1).map ψc)
  let d : Fin (m + 1) → Δ := fun k => ⟨(linearFrameBlock (GaloisField p f) m k 1).map ψc, ⟨k, rfl⟩⟩
  have hd : Function.Bijective d := by
    constructor
    · intro i j heq
      by_contra hij
      exact F14.map_ne_of_commuting_of_equiv_sl2 ψc hkerC
        ((MonoidHom.ofInjective (blockSL_injective (by omega : 2 * i.val + 2 ≤ 2 * m + 1 + 1 + 1))).symm)
        (fun a ha b hb => commutes_linearFrameBlock (tail := 1) hij a ha b hb) (congrArg Subtype.val heq)
    · rintro ⟨L, k, rfl⟩
      exact ⟨k, rfl⟩
  let e : Fin (m + 1) ≃ Δ := Equiv.ofBijective d hd
  have hρ : Function.Surjective (conjPermHom (le_refl (conjSetStab Δ))) :=
    surjective_conjPermHom_of_indexed_conjugations e fun σ => by
      obtain ⟨g, hg⟩ := exists_conj_oddLinearFrameBlock_permutation
        (CFSG.ClassicalInvolution.RouteD.two_ne_zero_galoisField hp2) σ
      refine ⟨ψc g, fun k => ?_⟩
      change ((linearFrameBlock (GaloisField p f) m k 1).map ψc).map
        (MulAut.conj (ψc g)).toMonoidHom =
          (linearFrameBlock (GaloisField p f) m (σ k) 1).map ψc
      have hhom : (MulAut.conj (ψc g)).toMonoidHom.comp ψc =
          ψc.comp (MulAut.conj g).toMonoidHom := by
        ext x
        simp [MulAut.conj_apply]
      rw [Subgroup.map_map, hhom, ← Subgroup.map_map, hg]
  have htop := MonoidHom.range_eq_top.mpr hρ
  exact ⟨(MulEquiv.subgroupCongr htop).trans
    (Subgroup.topEquiv.trans e.symm.permCongrHom)⟩


theorem centralizingLayer_funSet_eq_triple_map_of_psl_odd
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p m f : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (hadm : StatedLieAdmissible .PSL (2 * m + 1 + 1 + 1) p f) (hX : CFSG.Blueprint.LieModel X .PSL (2 * m + 1 + 1 + 1) p f)
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X)) :
    ∃ (ψ : SL(2 * m + 1 + 1 + 1, GaloisField p f) →* X)
      (k : Fin (m + 1)),
      ψ.ker ≤ center SL(2 * m + 1 + 1 + 1, GaloisField p f) ∧
      centralizingLayer {L : Subgroup X | IsFundamentalOver (p ^ f) L}
        {x : X | ∃ L ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X),
          L ≠ K ∧ x ∈ L} =
        (CFSG.SeitzReduction.LinearPilot.blockSpecialLinear
          (K := GaloisField p f) (linearFrameTriple m k)).map ψ := by
  obtain ⟨ψ0, hψ0, hker0⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    .PSL (2 * m + 1 + 1 + 1) p f hp.out hp2 (by trivial) hadm X hX
  let ψ : SL(2 * m + 1 + 1 + 1, GaloisField p f) →* X := ψ0
  have hψ : Function.Surjective ψ := hψ0
  have hker : ψ.ker ≤ center SL(2 * m + 1 + 1 + 1, GaloisField p f) := hker0
  obtain ⟨c, hfull⟩ := exists_full_coordinate_frame_funSet_psl_odd hp2 hm hadm hX ψ hψ hker P
  let F := GaloisField p f
  let ψc : SL(2 * m + 1 + 1 + 1, F) →* X := (MulAut.conj c).toMonoidHom.comp ψ
  have hψc : Function.Surjective ψc := (MulAut.conj c).surjective.comp hψ
  have hkerC : ψc.ker ≤ center SL(2 * m + 1 + 1 + 1, F) := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact (MulAut.conj c).injective (by simpa [ψc] using hx)
  have hfull' : F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X) =
      Set.range (fun k : Fin (m + 1) => (linearFrameBlock F m k 1).map ψc) := by
    simpa [ψc, Subgroup.map_map] using hfull
  have hKrange : K ∈ Set.range (fun k : Fin (m + 1) => (linearFrameBlock F m k 1).map ψc) := hfull' ▸ hK
  obtain ⟨k, rfl⟩ := hKrange
  have hinj : Function.Injective (fun j : Fin (m + 1) => (linearFrameBlock F m j 1).map ψc) := by
    intro i j heq
    by_contra hij
    exact F14.map_ne_of_commuting_of_equiv_sl2 ψc hkerC
      ((MonoidHom.ofInjective (blockSL_injective (by omega : 2 * i.val + 2 ≤ 2 * m + 1 + 1 + 1))).symm)
      (fun a ha b hb => commutes_linearFrameBlock (tail := 1) hij a ha b hb) heq
  have hΓ : {x : X | ∃ L ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X),
      L ≠ (linearFrameBlock F m k 1).map ψc ∧ x ∈ L} =
      {x : X | ∃ j : Fin (m + 1), j ≠ k ∧ x ∈ (linearFrameBlock F m j 1).map ψc} := by
    ext x
    constructor
    · rintro ⟨L, hL, hne, hx⟩
      rw [hfull'] at hL
      obtain ⟨j, rfl⟩ := hL
      exact ⟨j, fun h => hne (h ▸ rfl), hx⟩
    · rintro ⟨j, hne, hx⟩
      exact ⟨(linearFrameBlock F m j 1).map ψc, hfull'.symm ▸ ⟨j, rfl⟩,
        fun h => hne (hinj h), hx⟩
  obtain ⟨_, _, hL2, _⟩ := fundamental_ambient_of_lieModel hp.out hp2 hadm hX
    (by simp) hK.1
  have hreal : ∀ L ∈ {L : Subgroup X | IsFundamentalOver (p ^ f) L},
      ∃ R ∈ fundamentalSubgroups .PSL (modelUniv .PSL (2 * m + 1 + 1 + 1) p f hp.out).D, L = R.map ψc := by
    intro L hL
    obtain ⟨R, hR, heq, _⟩ := exists_mem_fundamentalSubgroups_of_isFundamentalOver_general
      hp.out hp2 hadm hX (by trivial) (by simp) hL2 ψc hψc hkerC hL
    exact ⟨R, hR, heq⟩
  refine ⟨ψc, k, hkerC, ?_⟩
  rw [hΓ]
  let Γ := {x : X | ∃ j : Fin (m + 1), j ≠ k ∧ x ∈ (linearFrameBlock F m j 1).map ψc}
  let D := CFSG.SeitzReduction.LinearPilot.blockSpecialLinear (K := F) (linearFrameTriple m k)
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.RouteD.two_ne_zero_galoisField hp2
  apply le_antisymm
  · refine iSup₂_le fun L hL => ?_
    obtain ⟨R, hR, rfl⟩ := hreal L hL.1
    let R' : Subgroup SL(2 * m + 1 + 1 + 1, F) := R
    have hR' : R' ∈ fundamentalSubgroups .PSL (modelUniv .PSL (2 * m + 1 + 1 + 1) p f hp.out).D := hR
    have hcR : ∀ j : Fin (m + 1), j ≠ k → Commutes R' (linearFrameBlock F m j 1) := by
      intro j hj
      apply commutes_modelFund_of_commutes_map hp2 (by trivial) hadm ψc hkerC hR'
      intro a ha b hb
      exact (Subgroup.mem_centralizer_iff.mp (hL.2 ha) b ⟨j, hj, hb⟩).symm
    change R' ∈ fundamentalSubgroups .PSL
      (CFSG.LieType.Universal.SpecialLinear.rootDatum (2 * m + 1 + 1) F) at hR'
    obtain ⟨z, hz⟩ := CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset
      (m := 2 * m + 1 + 1) (by omega : 2 ≤ (2 * m + 1 + 1) + 1) hR'
    exact Subgroup.map_mono (le_tripleBlock_of_commutes_other_linearFrameBlocks h2 hz k hcR)
  · change D.map ψc ≤ centralizingLayer {L : Subgroup X | IsFundamentalOver (p ^ f) L} Γ
    dsimp only [D]
    rw [CFSG.SeitzReduction.LinearPilot.blockSpecialLinear_eq_closure, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨g, ⟨a, b, hab, u, ha, hb, rfl⟩, rfl⟩
    let T : Pair (2 * m + 1 + 1 + 1) := ⟨{a, b}, Finset.card_pair hab⟩
    have hT : T.1 ⊆ linearFrameTriple m k := by
      intro i hi
      simp only [T, Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact ha
      · exact hb
    have hLc : Lc F T ≤ D := by
      rw [Lc_eq_blockSpecialLinear h2]
      exact CFSG.SeitzReduction.LinearPilot.blockSpecialLinear_mono hT
    have hmodel : Lc F T ∈ fundamentalSubgroups .PSL
        (modelUniv .PSL (2 * m + 1 + 1 + 1) p f hp.out).D :=
      Lc_mem_fundamentalSubgroups_psl_odd hp2 T
    have hΩ : IsFundamentalOver (p ^ f) ((Lc F T).map ψc) :=
      ⟨.PSL, 2 * m + 1 + 1 + 1, p, f, hp.out, hp2, rfl, trivial, hadm, ψc, hψc,
        hkerC, Lc F T, hmodel, rfl⟩
    have hcent : (Lc F T).map ψc ≤ centralizer Γ := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      rintro y ⟨j, hj, hy⟩
      obtain ⟨x₀, hx₀, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨y₀, hy₀, rfl⟩ := Subgroup.mem_map.mp hy
      simpa only [map_mul] using (congrArg ψc (commutes_tripleBlock_linearFrameBlock h2 hj
        x₀ (hLc hx₀) y₀ hy₀)).symm
    apply le_centralizingLayer ⟨hΩ, hcent⟩
    apply Subgroup.mem_map.mpr
    refine ⟨SpecialLinearGroup.transvection hab u, ?_, rfl⟩
    rw [Lc_eq_blockSpecialLinear h2]
    exact CFSG.SeitzReduction.LinearPilot.transvection_mem_blockSpecialLinear hab
      (by simp [T]) (by simp [T]) u


theorem lieModel_centralizingLayer_quotient_of_psl_odd
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p m f : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (hadm : StatedLieAdmissible .PSL (2 * m + 1 + 1 + 1) p f)
    (hX : CFSG.Blueprint.LieModel X .PSL (2 * m + 1 + 1 + 1) p f)
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X)) :
    let A := centralizingLayer {L : Subgroup X | IsFundamentalOver (p ^ f) L}
      {x : X | ∃ L ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X),
        L ≠ K ∧ x ∈ L}
    CFSG.Blueprint.LieModel (A ⧸ center A) .PSL 3 p f := by
  let A := centralizingLayer {L : Subgroup X | IsFundamentalOver (p ^ f) L}
    {x : X | ∃ L ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X),
      L ≠ K ∧ x ∈ L}
  obtain ⟨hZ, _, hL2, _⟩ := fundamental_ambient_of_lieModel hp.out hp2 hadm hX (by simp) hK.1
  have hdesc : ∃ (t : StatedLieTag) (n e : ℕ), StatedLieAdmissible t n p e ∧
      p ^ f = p ^ e ∧ CFSG.Blueprint.LieModel (X ⧸ center X) t n p e :=
    ⟨.PSL, 2 * m + 1 + 1 + 1, f, hadm, rfl, hX.quotient_center hZ⟩
  have hKle : K ≤ A := by
    apply le_centralizingLayer
    refine ⟨hK.1, ?_⟩
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    rintro y ⟨L, hL, hne, hy⟩
    have hcomm := CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.funSet_commute_of_lieModel
      hp.out hp2 hdesc hL2 P hK hL hne.symm
    exact Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hx) y hy
  have hAne : A ≠ ⊥ := by
    intro h
    exact hK.1.ne_bot (le_bot_iff.mp (h ▸ hKle))
  obtain ⟨ψ, k, _, heq⟩ := centralizingLayer_funSet_eq_triple_map_of_psl_odd hp2 hm hadm hX P hK
  have hne : (CFSG.SeitzReduction.LinearPilot.blockSpecialLinear
      (K := GaloisField p f) (linearFrameTriple m k)).map ψ ≠ ⊥ := by
    simpa only [← heq] using hAne
  have hmodel := lieModel_tripleBlock_map_quotient (by have := hadm.2.1; omega) ψ k hne
  exact CFSG.Blueprint.LieModel.quotient_center_of_mulEquiv
    (MulEquiv.subgroupCongr heq.symm) hmodel

end CFSG.LocalAnalysis.UniquenessCase.UC22
