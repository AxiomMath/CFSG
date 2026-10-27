module

public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentSplit
public import CFSG.LocalAnalysis.ComponentInitial.QuadraticLowDimension

public section

namespace CFSG.RankThree.PartOne.KCOrthogonalDescent

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.LocalAnalysis.ComponentInitial

variable {F W : Type} [Field F] [AddCommGroup W] [Module F W]

namespace HypSplit

@[expose] noncomputable def ofPairs [FiniteDimensional F W] (Q : QuadraticForm F W) {m : ℕ}
    (P : Fin m → HypPair Q) (hP : ∀ i j, i ≠ j → (P i).Orth (P j))
    (han : ∀ w : W, (∀ i, w ∈ (P i).perp) → Q w = 0 → w = 0) :
    HypSplit Q m (finrank F (⨅ i, (P i).perp : Submodule F W)) := by
  classical
  set A : Submodule F W := ⨅ i, (P i).perp with hA
  set tb := Module.finBasis F A
  let t : Fin (finrank F A) → W := fun j => (tb j : W)
  have ht : ∀ j i, t j ∈ (P i).perp := fun j i => (Submodule.mem_iInf _).1 (tb j).2 i
  have hw : ∀ z : Fin (finrank F A) → F, ∀ i, (∑ j, z j • t j) ∈ (P i).perp := fun z i =>
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (ht j i)
  let v : Fin m ⊕ Fin m ⊕ Fin (finrank F A) → W :=
    Sum.elim (fun i => (P i).e) (Sum.elim (fun i => (P i).f) t)
  have hli : LinearIndependent F v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at hg
    simp only [v, Sum.elim_inl, Sum.elim_inr] at hg
    have hg' : ∑ i, g (.inl i) • (P i).e + ∑ i, g (.inr (.inl i)) • (P i).f +
        ∑ j, g (.inr (.inr j)) • t j = 0 := by
      rw [← hg]
      abel
    have hα : ∀ j, g (.inl j) = 0 := fun j => by
      have := polar_sum_add_f hP (fun i => g (.inl i)) (fun i => g (.inr (.inl i)))
        (hw fun j => g (.inr (.inr j))) j
      rwa [hg', polar_zero_left, eq_comm] at this
    have hβ : ∀ j, g (.inr (.inl j)) = 0 := fun j => by
      have := polar_sum_add_e hP (fun i => g (.inl i)) (fun i => g (.inr (.inl i)))
        (hw fun j => g (.inr (.inr j))) j
      rwa [hg', polar_zero_left, eq_comm] at this
    have hγ : ∑ j, g (.inr (.inr j)) • tb j = 0 := by
      apply Subtype.ext
      simp only [hα, hβ, zero_smul, Finset.sum_const_zero, zero_add] at hg'
      simpa [t] using hg'
    have := Fintype.linearIndependent_iff.mp tb.linearIndependent _ hγ
    rintro (i | i | j)
    · exact hα i
    · exact hβ i
    · exact this j
  have hsp : ⊤ ≤ Submodule.span F (Set.range v) := by
    intro x _
    set u : W := ∑ i, polar Q x (P i).f • (P i).e + ∑ i, polar Q x (P i).e • (P i).f with hu
    have hxu : x - u ∈ A := (Submodule.mem_iInf _).2 (sub_sum_mem_perp hP x)
    have hx : x = u + (x - u) := by abel
    rw [hx]
    refine add_mem (add_mem (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨.inl i, rfl⟩)) (Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨.inr (.inl i), rfl⟩))) ?_
    have h := tb.sum_repr ⟨x - u, hxu⟩
    have h2 : x - u = ∑ j, tb.repr ⟨x - u, hxu⟩ j • t j := by
      have h3 := congrArg Subtype.val h
      rw [Submodule.coe_sum] at h3
      simp only [Submodule.coe_smul] at h3
      exact h3.symm
    rw [h2]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨.inr (.inr j), rfl⟩)
  refine ⟨Basis.mk hli hsp, fun x y z => ?_, fun z hz => ?_⟩
  · simp only [Basis.mk_apply, v, Sum.elim_inl, Sum.elim_inr]
    rw [QuadraticMap.map_add (⇑Q), map_sum_hyp hP x y, polar_sum_hyp_eq_zero x y (hw z)]
    ring
  · simp only [Basis.mk_apply, v, Sum.elim_inr] at hz
    have h0 := han _ (hw z) hz
    have hγ : ∑ j, z j • tb j = 0 := by
      apply Subtype.ext
      simpa [t] using h0
    funext j
    exact Fintype.linearIndependent_iff.mp tb.linearIndependent _ hγ j

@[expose] noncomputable def ofIsometry {W' : Type} [AddCommGroup W'] [Module F W']
    {Q : QuadraticForm F W} {Q' : QuadraticForm F W'} {m δ : ℕ} (e : Q.IsometryEquiv Q')
    (H : HypSplit Q m δ) :
    HypSplit Q' m δ where
  b := H.b.map e.toLinearEquiv
  eval x y z := by
    have hv : ∑ i, x i • (H.b.map e.toLinearEquiv) (.inl i) +
        ∑ i, y i • (H.b.map e.toLinearEquiv) (.inr (.inl i)) +
        ∑ j, z j • (H.b.map e.toLinearEquiv) (.inr (.inr j)) =
        e (∑ i, x i • H.b (.inl i) + ∑ i, y i • H.b (.inr (.inl i)) +
          ∑ j, z j • H.b (.inr (.inr j))) := by
      simp [Basis.map_apply, map_add, map_sum, map_smul]
    have ht : ∑ j, z j • (H.b.map e.toLinearEquiv) (.inr (.inr j)) =
        e (∑ j, z j • H.b (.inr (.inr j))) := by
      simp [Basis.map_apply, map_sum, map_smul]
    rw [hv, ht, e.map_app, e.map_app]
    exact H.eval x y z
  aniso z hz := by
    have ht : ∑ j, z j • (H.b.map e.toLinearEquiv) (.inr (.inr j)) =
        e (∑ j, z j • H.b (.inr (.inr j))) := by
      simp [Basis.map_apply, map_sum, map_smul]
    rw [ht, e.map_app] at hz
    exact H.aniso z hz

end HypSplit

theorem exists_regular_split [Finite F] [FiniteDimensional F W] (Q : QuadraticForm F W)
    (hQ : (polarBilin Q).Nondegenerate) :
    ∃ m δ : ℕ, δ ≤ 2 ∧ Nonempty (HypSplit Q m δ) := by
  have : Fintype F := Fintype.ofFinite F
  by_cases h2 : ringChar F = 2
  · have : CharP F 2 := h2 ▸ ringChar.charP F
    obtain ⟨-, -, -, ⟨m, P, hPo, han⟩, h5, -⟩ := finite_even_regular_quadratic_normal_forms Q hQ
    refine ⟨m, _, ?_, ⟨HypSplit.ofPairs Q P hPo han⟩⟩
    rcases h5 m P hPo han with h | h <;> omega
  · have hodd : Odd (Nat.card F) := by
      rw [Nat.card_eq_fintype_card]
      exact Nat.not_even_iff_odd.mp fun h =>
        h2 (FiniteField.even_card_iff_char_two.mpr (Nat.even_iff.mp h))
    obtain ⟨m, P, A, hPo, -, -, hA, -, -, hani, hdim, -, -⟩ :=
      (finite_odd_quadratic_low_Witt_dimension_bound hodd Q hQ).2.1
    have han : ∀ w : W, (∀ i, w ∈ (P i).perp) → Q w = 0 → w = 0 := by
      intro w hw hQw
      have hwA : w ∈ A := by
        rw [hA]
        exact (Submodule.mem_iInf _).2 hw
      have := hani ⟨w, hwA⟩ hQw
      exact congrArg Subtype.val this
    refine ⟨m, _, ?_, ⟨HypSplit.ofPairs Q P hPo han⟩⟩
    rw [← hA]
    exact hdim

end CFSG.RankThree.PartOne.KCOrthogonalDescent
