module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCFrame
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameInd
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.WeakCT.StandardPair
public import CFSG.LieType.CurtisTits.SpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear

public section

namespace CFSG.StandardType

namespace WitSpBlk

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)

variable {K : Type} [Field K] {n : ℕ}

structure IsSpFamily {m : ℕ} (u w : Fin m → Fin n ⊕ Fin n → K) : Prop where
  pair : ∀ i j, form (u i) (w j) = if i = j then 1 else 0
  uu : ∀ i j, form (u i) (u j) = 0
  ww : ∀ i j, form (w i) (w j) = 0

namespace IsSpFamily

variable {m : ℕ} {u w : Fin m → Fin n ⊕ Fin n → K}

theorem pair_symm (h : IsSpFamily u w) (i j : Fin m) :
    form (w i) (u j) = if i = j then -1 else 0 := by
  rw [form_antisymm, h.pair j i]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij, Ne.symm hij]

theorem form_sum_w (h : IsSpFamily u w) (c : Fin m ⊕ Fin m → K) (j : Fin m) :
    form (∑ x, c x • Sum.elim u w x) (w j) = c (Sum.inl j) := by
  rw [form_sum_left, Fintype.sum_sum_type]
  simp [form_smul_left, h.pair, h.ww]

theorem form_sum_u (h : IsSpFamily u w) (c : Fin m ⊕ Fin m → K) (j : Fin m) :
    form (∑ x, c x • Sum.elim u w x) (u j) = -c (Sum.inr j) := by
  rw [form_sum_left, Fintype.sum_sum_type]
  simp [form_smul_left, h.uu, h.pair_symm]

theorem linearIndependent (h : IsSpFamily u w) : LinearIndependent K (Sum.elim u w) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc x
  rcases x with j | j
  · have := h.form_sum_w c j
    rwa [hc, form_zero_left, eq_comm] at this
  · have := h.form_sum_u c j
    rw [hc, form_zero_left, eq_comm, neg_eq_zero] at this
    exact this

end IsSpFamily

theorem toBilin'_J_isRefl : (Matrix.toBilin' (Matrix.J (Fin n) K)).IsRefl :=
  isAlt_toBilin'_J.isRefl

theorem restrict_span_nondegenerate {m : ℕ} {u w : Fin m → Fin n ⊕ Fin n → K}
    (h : IsSpFamily u w) :
    ((Matrix.toBilin' (Matrix.J (Fin n) K)).restrict
      (Submodule.span K (Set.range (Sum.elim u w)))).Nondegenerate := by
  set B := Matrix.toBilin' (Matrix.J (Fin n) K) with hB
  have hrefl : B.IsRefl := toBilin'_J_isRefl
  have hrefl' : (B.restrict (Submodule.span K (Set.range (Sum.elim u w)))).IsRefl :=
    fun a b hab => hrefl a b hab
  refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft hrefl').2 fun s hs => ?_
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp s.2
  have hmem : ∀ x, Sum.elim u w x ∈ Submodule.span K (Set.range (Sum.elim u w)) :=
    fun x => Submodule.subset_span ⟨x, rfl⟩
  have hcoef : ∀ x, c x = 0 := by
    intro x
    rcases x with j | j
    · have h1 := hs ⟨w j, hmem (Sum.inr j)⟩
      simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply] at h1
      rw [hB, toBilin'_J_apply, neg_eq_zero, ← hc, h.form_sum_w] at h1
      exact h1
    · have h1 := hs ⟨u j, hmem (Sum.inl j)⟩
      simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply] at h1
      rw [hB, toBilin'_J_apply, neg_eq_zero, ← hc, h.form_sum_u, neg_eq_zero] at h1
      exact h1
  apply Subtype.ext
  rw [← hc]
  simp [hcoef]

theorem exists_sp_of_family {m : ℕ} (hm : m ≤ n) {u w : Fin m → Fin n ⊕ Fin n → K}
    (h : IsSpFamily u w) : ∃ g : StatedSp n K, ∀ i : Fin m,
      mat n K g *ᵥ Pi.single (Sum.inl (Fin.castLE hm i)) 1 = u i ∧
        mat n K g *ᵥ Pi.single (Sum.inr (Fin.castLE hm i)) 1 = w i := by
  classical
  set B := Matrix.toBilin' (Matrix.J (Fin n) K) with hB
  set S := Submodule.span K (Set.range (Sum.elim u w)) with hS
  have hrefl : B.IsRefl := toBilin'_J_isRefl
  have hcompl : IsCompl S (B.orthogonal S) :=
    LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hrefl
      (restrict_span_nondegenerate h)
  have hQnd : (B.restrict (B.orthogonal S)).Nondegenerate :=
    SpNS.restrict_nondegenerate_orthogonal hrefl nondegenerate_toBilin'_J hcompl
  have halt : B.IsAlt := isAlt_toBilin'_J
  have hQalt : (B.restrict (B.orthogonal S)).IsAlt := fun z => halt z
  obtain ⟨m', c, hc⟩ := hQalt.exists_basis_toMatrix_eq_J hQnd
  have hcf : ∀ x y, form (c x : Fin n ⊕ Fin n → K) (c y) = -Matrix.J (Fin m') K x y := by
    intro x y
    have h1 := congrFun (congrFun hc x) y
    rw [LinearMap.BilinForm.toMatrix_apply, LinearMap.BilinForm.restrict_apply,
      LinearMap.domRestrict_apply] at h1
    have h2 : B (c x : Fin n ⊕ Fin n → K) (c y) = -form (c x : Fin n ⊕ Fin n → K) (c y) :=
      toBilin'_J_apply _ _
    rw [← h1, h2, neg_neg]
  have hSmem : ∀ x, Sum.elim u w x ∈ S := fun x => Submodule.subset_span ⟨x, rfl⟩
  have horth : ∀ x y, form (Sum.elim u w x) (c y : Fin n ⊕ Fin n → K) = 0 := by
    intro x y
    have h1 : B (Sum.elim u w x) (c y) = 0 :=
      LinearMap.BilinForm.mem_orthogonal_iff.mp (c y).2 _ (hSmem x)
    have h2 : B (Sum.elim u w x) (c y : Fin n ⊕ Fin n → K) =
        -form (Sum.elim u w x) (c y : Fin n ⊕ Fin n → K) := toBilin'_J_apply _ _
    rw [h2, neg_eq_zero] at h1
    exact h1
  have horth' : ∀ x y, form (c y : Fin n ⊕ Fin n → K) (Sum.elim u w x) = 0 := fun x y => by
    rw [form_antisymm, horth, neg_zero]
  have hdim : m + m' = n := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hcompl
    rw [hS, finrank_span_eq_card h.linearIndependent, Module.finrank_eq_card_basis c,
      Module.finrank_fintype_fun_eq_card] at h1
    simp only [Fintype.card_sum, Fintype.card_fin] at h1
    omega
  set U : Fin n → Fin n ⊕ Fin n → K := fun k =>
    if hk : (k : ℕ) < m then u ⟨k, hk⟩
    else (c (Sum.inl ⟨k - m, by have := k.isLt; omega⟩) : Fin n ⊕ Fin n → K) with hU
  set W : Fin n → Fin n ⊕ Fin n → K := fun k =>
    if hk : (k : ℕ) < m then w ⟨k, hk⟩
    else (c (Sum.inr ⟨k - m, by have := k.isLt; omega⟩) : Fin n ⊕ Fin n → K) with hW
  have hframe : IsPlaneFrame U W := by
    refine ⟨fun k l => ?_, fun k l => ?_, fun k l => ?_⟩
    · by_cases hk : (k : ℕ) < m <;> by_cases hl : (l : ℕ) < m
      · simp only [hU, hW, dite_eq_left hk, dite_eq_left hl, h.pair, Fin.ext_iff]
      · have hkl : k ≠ l := fun h' => hl (h' ▸ hk)
        simp only [hU, hW, dite_eq_left hk, dite_eq_right hl, ite_eq_right hkl]
        exact horth (Sum.inl _) _
      · have hkl : k ≠ l := fun h' => hk (h' ▸ hl)
        simp only [hU, hW, dite_eq_right hk, dite_eq_left hl, ite_eq_right hkl]
        exact horth' (Sum.inr _) _
      · simp only [hU, hW, dite_eq_right hk, dite_eq_right hl, hcf, Matrix.J,
          Matrix.fromBlocks_apply₁₂,
          Matrix.neg_apply, neg_neg, Matrix.one_apply, Fin.ext_iff]
        by_cases hkl : (k : ℕ) = l
        · rw [ite_eq_left (by omega), ite_eq_left hkl]
        · rw [ite_eq_right (by omega), ite_eq_right hkl]
    · by_cases hk : (k : ℕ) < m <;> by_cases hl : (l : ℕ) < m
      · simp only [hU, dite_eq_left hk, dite_eq_left hl, h.uu]
      · simp only [hU, dite_eq_left hk, dite_eq_right hl]
        exact horth (Sum.inl _) _
      · simp only [hU, dite_eq_right hk, dite_eq_left hl]
        exact horth' (Sum.inl _) _
      · simp only [hU, dite_eq_right hk, dite_eq_right hl, hcf, Matrix.J, Matrix.fromBlocks_apply₁₁,
          Matrix.zero_apply, neg_zero]
    · by_cases hk : (k : ℕ) < m <;> by_cases hl : (l : ℕ) < m
      · simp only [hW, dite_eq_left hk, dite_eq_left hl, h.ww]
      · simp only [hW, dite_eq_left hk, dite_eq_right hl]
        exact horth (Sum.inr _) _
      · simp only [hW, dite_eq_right hk, dite_eq_left hl]
        exact horth' (Sum.inr _) _
      · simp only [hW, dite_eq_right hk, dite_eq_right hl, hcf, Matrix.J, Matrix.fromBlocks_apply₂₂,
          Matrix.zero_apply, neg_zero]
  obtain ⟨g, hg⟩ := hframe.exists_sp_apply
  refine ⟨g, fun i => ⟨?_, ?_⟩⟩
  · rw [(hg (Fin.castLE hm i)).1, hU]
    simp only [Fin.val_castLE, dite_eq_left i.isLt]
  · rw [(hg (Fin.castLE hm i)).2, hW]
    simp only [Fin.val_castLE, dite_eq_left i.isLt]

end WitSpBlk

end CFSG.StandardType
