module

public import CFSG.LocalAnalysis.WeakClosure81.Orth6Minus.Defs
import CFSG.ClassicalGroups.Orthogonal.SumSquaresSigns

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Orth6Minus

open CFSG.ClassicalGroups.Orthogonal
open Matrix

private lemma card_six : Fintype.card Six = 6 := by
  simp [Six]

private lemma card_six_ne_four {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) :
    (Fintype.card Six : K) ≠ 4 := by
  rw [card_six]
  intro h
  apply h2
  linear_combination h

private theorem exists_diagGL_of_mem_orthogonalGroup_sumSqForm {ι K : Type*} [Fintype ι]
    [DecidableEq ι] [Field K] {g : GL ι K}
    (hg : g ∈ CFSG.PGLModel.orthogonalGroup (sumSqForm (ι := ι) (K := K)))
    (hd : ∀ i j : ι, i ≠ j → (g : Matrix ι ι K) i j = 0) :
    ∃ d : ι → Kˣ, g = TauCeti.diagGL d ∧ ∀ i, (d i : K) ^ 2 = 1 := by
  have hne : ∀ i, (g : Matrix ι ι K) i i ≠ 0 := by
    intro i hi
    have hsq := sq_apply_self_eq_one_of_mem hg hd i
    rw [hi] at hsq
    norm_num at hsq
  refine ⟨fun i => Units.mk0 ((g : Matrix ι ι K) i i) (hne i), ?_, ?_⟩
  · apply Units.ext
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [TauCeti.diagGL_apply]
    · simp [TauCeti.diagGL_apply, hij, hd i j hij]
  · intro i
    simpa using sq_apply_self_eq_one_of_mem hg hd i

private lemma exists_mul_scalar_of_commute_permutationGL {K : Type*} [Field K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ι → Kˣ} {σ : Equiv.Perm ι}
    (hcomm : Matrix.ProjGenLinGroup.mk (TauCeti.diagGL d) *
        Matrix.ProjGenLinGroup.mk (TauCeti.permutationGL (k := K) σ) =
      Matrix.ProjGenLinGroup.mk (TauCeti.permutationGL (k := K) σ) *
        Matrix.ProjGenLinGroup.mk (TauCeti.diagGL d)) :
    ∃ u : Kˣ, ∀ i, d (σ i) = d i * u := by
  classical
  set P : GL ι K := TauCeti.permutationGL (k := K) σ
  have hconj : Matrix.ProjGenLinGroup.mk (P⁻¹ * TauCeti.diagGL d * P) =
      Matrix.ProjGenLinGroup.mk (TauCeti.diagGL d) := by
    have h1 : (Matrix.ProjGenLinGroup.mk P)⁻¹ *
        Matrix.ProjGenLinGroup.mk (TauCeti.diagGL d) * Matrix.ProjGenLinGroup.mk P =
        Matrix.ProjGenLinGroup.mk (TauCeti.diagGL d) := by
      calc (Matrix.ProjGenLinGroup.mk P)⁻¹ *
            Matrix.ProjGenLinGroup.mk (TauCeti.diagGL d) * Matrix.ProjGenLinGroup.mk P
          = (Matrix.ProjGenLinGroup.mk P)⁻¹ *
              (Matrix.ProjGenLinGroup.mk (TauCeti.diagGL d) * Matrix.ProjGenLinGroup.mk P) := by
            group
        _ = (Matrix.ProjGenLinGroup.mk P)⁻¹ *
              (Matrix.ProjGenLinGroup.mk P * Matrix.ProjGenLinGroup.mk (TauCeti.diagGL d)) := by
            rw [hcomm]
        _ = Matrix.ProjGenLinGroup.mk (TauCeti.diagGL d) := by group
    rw [map_mul, map_mul, map_inv]
    exact h1
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hconj.symm
  have hL : TauCeti.diagGL d * Matrix.GeneralLinearGroup.scalar ι u =
      TauCeti.diagGL (fun i => d i * u) := by
    rw [← TauCeti.diagGL_const (a := u), ← map_mul]
    rfl
  have hR : P⁻¹ * TauCeti.diagGL d * P = TauCeti.diagGL (d ∘ σ) := by
    have hPinv : ((P⁻¹ : GL ι K) : Matrix ι ι K) = σ.permMatrix K := by
      rw [show P = TauCeti.permutationGL (k := K) σ from rfl, ← map_inv,
        TauCeti.permutationGL_coe, inv_inv]
    calc P⁻¹ * TauCeti.diagGL d * P
        = TauCeti.diagGL (d ∘ σ) * P⁻¹ * P := by
          rw [TauCeti.mul_diagGL_of_coe_eq_permMatrix P⁻¹ σ hPinv d]
      _ = TauCeti.diagGL (d ∘ σ) := by group
  have hfun : (fun i => d i * u) = d ∘ σ := by
    apply TauCeti.diagGL_injective
    rw [← hL, ← hR]
    exact hu
  exact ⟨u, fun i => (congrFun hfun i).symm⟩

private theorem diagGL_apply_perm_eq_of_commute_permutationGL {K : Type*} [Field K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ι → Kˣ} {σ : Equiv.Perm ι}
    (hcomm : Matrix.ProjGenLinGroup.mk (TauCeti.diagGL d) *
        Matrix.ProjGenLinGroup.mk (TauCeti.permutationGL (k := K) σ) =
      Matrix.ProjGenLinGroup.mk (TauCeti.permutationGL (k := K) σ) *
        Matrix.ProjGenLinGroup.mk (TauCeti.diagGL d))
    {j : ι} (hj : σ j = j) (i : ι) : d (σ i) = d i := by
  obtain ⟨u, hu⟩ := exists_mul_scalar_of_commute_permutationGL hcomm
  have hi : d (σ i) = d i * u := hu i
  have hui : u = 1 := by
    have hji : d j * u = d j := by
      have := (hu j).symm
      rwa [hj] at this
    have hval : (d j : K) * (u : K) = (d j : K) * 1 := by
      simpa using congrArg (fun x : Kˣ => (x : K)) hji
    exact Units.ext (mul_left_cancel₀ (Units.ne_zero (d j)) hval)
  rw [hui] at hi
  simpa using hi

private lemma diagGL_relations {K : Type*} [Field K] {d : Six → Kˣ}
    (hA : Matrix.ProjGenLinGroup.mk (TauCeti.diagGL d) *
        Matrix.ProjGenLinGroup.mk (TauCeti.permutationGL (k := K) permA) =
      Matrix.ProjGenLinGroup.mk (TauCeti.permutationGL (k := K) permA) *
        Matrix.ProjGenLinGroup.mk (TauCeti.diagGL d))
    (hC : Matrix.ProjGenLinGroup.mk (TauCeti.diagGL d) *
        Matrix.ProjGenLinGroup.mk (TauCeti.permutationGL (k := K) permC) =
      Matrix.ProjGenLinGroup.mk (TauCeti.permutationGL (k := K) permC) *
        Matrix.ProjGenLinGroup.mk (TauCeti.diagGL d)) :
    d (coord 1) = d (coord 0) ∧ d (coord 3) = d (coord 2) ∧
      d (coord 4) = d (coord 2) ∧ d (coord 5) = d (coord 3) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := diagGL_apply_perm_eq_of_commute_permutationGL hA
      (j := coord 4) (by decide) (coord 0)
    simpa [show permA (coord 0) = coord 1 by decide] using h
  · have h := diagGL_apply_perm_eq_of_commute_permutationGL hA
      (j := coord 4) (by decide) (coord 2)
    simpa [show permA (coord 2) = coord 3 by decide] using h
  · have h := diagGL_apply_perm_eq_of_commute_permutationGL hC
      (j := coord 0) (by decide) (coord 2)
    simpa [show permC (coord 2) = coord 4 by decide] using h
  · have h := diagGL_apply_perm_eq_of_commute_permutationGL hC
      (j := coord 0) (by decide) (coord 3)
    simpa [show permC (coord 3) = coord 5 by decide] using h

private lemma unit_eq_neg_of_sq_eq_one {K : Type*} [Field K] {a b : Kˣ}
    (ha : (a : K) ^ 2 = 1) (hb : (b : K) ^ 2 = 1) (hne : a ≠ b) : (a : K) = -(b : K) := by
  have hne' : (a : K) ≠ (b : K) := fun h => hne (Units.ext h)
  have hprod : ((a : K) - (b : K)) * ((a : K) + (b : K)) = 0 := by
    linear_combination ha - hb
  rcases mul_eq_zero.mp hprod with h | h
  · exact absurd (sub_eq_zero.mp h) hne'
  · exact eq_neg_iff_add_eq_zero.mpr h

private lemma diagGL_eq_const_of_relations {K : Type*} [Field K] {d : Six → Kˣ}
    (h01 : d (coord 1) = d (coord 0)) (h32 : d (coord 3) = d (coord 2))
    (h42 : d (coord 4) = d (coord 2)) (h53 : d (coord 5) = d (coord 3))
    (hαβ : d (coord 0) = d (coord 2)) : d = fun _ => d (coord 2) := by
  have h01' : d (Sum.inl 1) = d (Sum.inl 0) := by simpa [coord] using h01
  have h32' : d (Sum.inr (Sum.inl 1)) = d (Sum.inr (Sum.inl 0)) := by
    simpa [coord] using h32
  have h42' : d (Sum.inr (Sum.inr 0)) = d (Sum.inr (Sum.inl 0)) := by
    simpa [coord] using h42
  have h53' : d (Sum.inr (Sum.inr 1)) = d (Sum.inr (Sum.inl 1)) := by
    simpa [coord] using h53
  have hαβ' : d (Sum.inl 0) = d (Sum.inr (Sum.inl 0)) := by simpa [coord] using hαβ
  funext i
  fin_cases i <;> simp [coord, h01', h32', h42', h53', hαβ']

private lemma diagGL_eq_ite_of_relations {K : Type*} [Field K] {d : Six → Kˣ}
    (ha0 : (d (coord 0) : K) ^ 2 = 1) (ha2 : (d (coord 2) : K) ^ 2 = 1)
    (h01 : d (coord 1) = d (coord 0)) (h32 : d (coord 3) = d (coord 2))
    (h42 : d (coord 4) = d (coord 2)) (h53 : d (coord 5) = d (coord 3))
    (hαβ : d (coord 0) ≠ d (coord 2)) :
    d = fun i => if i ∈ ({coord 0, coord 1} : Finset Six) then -(d (coord 2)) else d (coord 2) := by
  have hneg : d (coord 0) = -(d (coord 2)) :=
    Units.ext (unit_eq_neg_of_sq_eq_one ha0 ha2 hαβ)
  have h01' : d (Sum.inl 1) = d (Sum.inl 0) := by simpa [coord] using h01
  have h32' : d (Sum.inr (Sum.inl 1)) = d (Sum.inr (Sum.inl 0)) := by
    simpa [coord] using h32
  have h42' : d (Sum.inr (Sum.inr 0)) = d (Sum.inr (Sum.inl 0)) := by
    simpa [coord] using h42
  have h53' : d (Sum.inr (Sum.inr 1)) = d (Sum.inr (Sum.inl 1)) := by
    simpa [coord] using h53
  have hneg' : d (Sum.inl 0) = -(d (Sum.inr (Sum.inl 0))) := by simpa [coord] using hneg
  funext i
  fin_cases i <;> simp [coord, h01', h32', h42', h53', hneg']

private lemma diagGL_ite_eq_negCoordGL_mul_scalar {K : Type*} [Field K] (s : Finset Six)
    (b : Kˣ) :
    TauCeti.diagGL (fun i => if i ∈ s then -b else b) =
      negCoordGL s * Matrix.GeneralLinearGroup.scalar Six b := by
  rw [negCoordGL, ← TauCeti.diagGL_const (a := b), ← map_mul]
  congr 1
  funext i
  by_cases hi : i ∈ s <;> simp [hi]

private lemma mk_diagGL_eq_one_of_relations {K : Type*} [Field K] {d : Six → Kˣ}
    (h01 : d (coord 1) = d (coord 0)) (h32 : d (coord 3) = d (coord 2))
    (h42 : d (coord 4) = d (coord 2)) (h53 : d (coord 5) = d (coord 3))
    (hαβ : d (coord 0) = d (coord 2)) :
    Matrix.ProjGenLinGroup.mk (TauCeti.diagGL d) = 1 := by
  have hconst := diagGL_eq_const_of_relations h01 h32 h42 h53 hαβ
  have hg_scalar : TauCeti.diagGL d =
      Matrix.GeneralLinearGroup.scalar Six (d (coord 2)) := by
    rw [hconst, TauCeti.diagGL_const]
  rw [hg_scalar, Matrix.ProjGenLinGroup.mk_scalar]

private lemma mk_diagGL_eq_mk_tGL_of_relations {K : Type*} [Field K] {d : Six → Kˣ}
    (hsq : ∀ i, (d i : K) ^ 2 = 1)
    (h01 : d (coord 1) = d (coord 0)) (h32 : d (coord 3) = d (coord 2))
    (h42 : d (coord 4) = d (coord 2)) (h53 : d (coord 5) = d (coord 3))
    (hαβ : d (coord 0) ≠ d (coord 2)) :
    Matrix.ProjGenLinGroup.mk (TauCeti.diagGL d) =
      Matrix.ProjGenLinGroup.mk (tGL K) := by
  have hite := diagGL_eq_ite_of_relations (hsq (coord 0)) (hsq (coord 2))
    h01 h32 h42 h53 hαβ
  have hg_eq : TauCeti.diagGL d =
      tGL K * Matrix.GeneralLinearGroup.scalar Six (d (coord 2)) := by
    rw [hite, diagGL_ite_eq_negCoordGL_mul_scalar]
    rfl
  calc Matrix.ProjGenLinGroup.mk (TauCeti.diagGL d)
      = Matrix.ProjGenLinGroup.mk
          (tGL K * Matrix.GeneralLinearGroup.scalar Six (d (coord 2))) := by rw [hg_eq]
    _ = Matrix.ProjGenLinGroup.mk (tGL K) *
          Matrix.ProjGenLinGroup.mk
            (Matrix.GeneralLinearGroup.scalar Six (d (coord 2))) := by rw [map_mul]
    _ = Matrix.ProjGenLinGroup.mk (tGL K) := by
          rw [Matrix.ProjGenLinGroup.mk_scalar, mul_one]

theorem mk_eq_one_or_eq_mk_tGL {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {g : GL Six K}
    (hg : g ∈ orthSix K)
    (hc : ∀ s ∈ gens K, Matrix.ProjGenLinGroup.mk g * Matrix.ProjGenLinGroup.mk s =
      Matrix.ProjGenLinGroup.mk s * Matrix.ProjGenLinGroup.mk g) :
    Matrix.ProjGenLinGroup.mk g = 1 ∨
      Matrix.ProjGenLinGroup.mk g = Matrix.ProjGenLinGroup.mk (tGL K) := by
  classical
  have hdiag : ∀ i j : Six, i ≠ j → (g : Matrix Six Six K) i j = 0 := by
    intro i j hij
    exact apply_eq_zero_of_commute_negCoordGL h2 (card_six_ne_four h2)
      (by rw [card_six]; norm_num)
      (fun r s hrs => hc (negCoordGL {r, s}) (Or.inl ⟨r, s, hrs, rfl⟩)) hij
  obtain ⟨d, hgd, hsq⟩ := exists_diagGL_of_mem_orthogonalGroup_sumSqForm hg hdiag
  have hmemA : TauCeti.permutationGL (k := K) permA ∈ gens K := Or.inr (by simp)
  have hmemC : TauCeti.permutationGL (k := K) permC ∈ gens K := Or.inr (by simp)
  have hcommA : Matrix.ProjGenLinGroup.mk (TauCeti.diagGL d) *
      Matrix.ProjGenLinGroup.mk (TauCeti.permutationGL (k := K) permA) =
      Matrix.ProjGenLinGroup.mk (TauCeti.permutationGL (k := K) permA) *
        Matrix.ProjGenLinGroup.mk (TauCeti.diagGL d) := by
    rw [← hgd]
    exact hc _ hmemA
  have hcommC : Matrix.ProjGenLinGroup.mk (TauCeti.diagGL d) *
      Matrix.ProjGenLinGroup.mk (TauCeti.permutationGL (k := K) permC) =
      Matrix.ProjGenLinGroup.mk (TauCeti.permutationGL (k := K) permC) *
        Matrix.ProjGenLinGroup.mk (TauCeti.diagGL d) := by
    rw [← hgd]
    exact hc _ hmemC
  obtain ⟨h01, h32, h42, h53⟩ := diagGL_relations hcommA hcommC
  by_cases hαβ : d (coord 0) = d (coord 2)
  · left
    rw [hgd]
    exact mk_diagGL_eq_one_of_relations h01 h32 h42 h53 hαβ
  · right
    rw [hgd]
    exact mk_diagGL_eq_mk_tGL_of_relations hsq h01 h32 h42 h53 hαβ

end CFSG.LocalAnalysis.WeakClosure81.Orth6Minus
