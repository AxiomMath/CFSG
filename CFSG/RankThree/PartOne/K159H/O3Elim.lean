module

public import CFSG.RankThree.PartOne.K159H.O3Class

public noncomputable section

namespace CFSG.RankThree.PartOne.K159H

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal.Spin Matrix Matrix.Pivot

variable {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A] {r : ℕ}

def ActsOn (I : Finset (Fin r ⊕ Fin r)) (g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A))
    (M : Matrix I I K) : Prop :=
  ∀ i : I, g (hypVec K A i.1) = ∑ i' : I, M i' i • hypVec K A i'.1

variable {I : Finset (Fin r ⊕ Fin r)}

theorem ActsOn.apply {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)} {M : Matrix I I K}
    (h : ActsOn I g M) (i : I) : g (hypVec K A i.1) = ∑ i' : I, M i' i • hypVec K A i'.1 := h i

theorem ActsOn.mul {g h : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)} {M N : Matrix I I K}
    (hg : ActsOn I g M) (hh : ActsOn I h N) : ActsOn I (g * h) (M * N) := by
  intro i
  have hg' : ∀ i' : I, g (hypVec K A i'.1) = ∑ i'' : I, M i'' i' • hypVec K A i''.1 := hg
  rw [LinearEquiv.mul_apply, hh i, map_sum]
  have e1 : ∀ i' : I, g (N i' i • hypVec K A i'.1) = ∑ i'' : I, (N i' i * M i'' i') • hypVec K A i''.1 := by
    intro i'
    rw [map_smul, hg' i', Finset.smul_sum]
    exact Finset.sum_congr rfl fun i'' _ => by rw [smul_smul]
  rw [Finset.sum_congr rfl fun i' _ => e1 i', Finset.sum_comm]
  refine Finset.sum_congr rfl fun i'' _ => ?_
  rw [← Finset.sum_smul]
  refine congrArg (· • hypVec K A i''.1) ?_
  rw [Matrix.mul_apply]
  exact Finset.sum_congr rfl fun i' _ => mul_comm _ _

theorem ActsOn.one (I : Finset (Fin r ⊕ Fin r)) :
    ActsOn I (1 : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) 1 := by
  intro i
  simp [Matrix.one_apply]

theorem sum_coord (a : I → K) (i'' : I) :
    (∑ i' : I, a i' • hypVec K A i'.1).1 i''.1 = a i'' := by
  rw [Prod.fst_sum, Finset.sum_apply]
  simp only [Prod.smul_fst, Pi.smul_apply, hypVec_fst, smul_eq_mul]
  rw [Finset.sum_eq_single i'']
  · simp
  · intro i' _ hne
    have : i''.1 ≠ i'.1 := fun h => hne (Subtype.ext h.symm)
    simp [this]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem ActsOn.unique {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)} {M M' : Matrix I I K}
    (h : ActsOn I g M) (h' : ActsOn I g M') : M = M' := by
  ext i'' i
  have := (h i).symm.trans (h' i)
  have h2 := congrArg (fun v => v.1 i''.1) this
  simpa only [sum_coord] using h2

theorem sum_transvection_smul (x y : I) (t : K) (i : I) :
    ∑ i' : I, (Matrix.transvection x y t) i' i • hypVec K A i'.1 =
      hypVec K A i.1 + (if i = y then t else 0) • hypVec K A x.1 := by
  simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, add_smul,
    Finset.sum_add_distrib]
  congr 1
  · simp
  · by_cases hi : i = y
    · simp [hi]
    · have hi' : ¬ y = i := fun h => hi h.symm
      simp [hi, hi']

variable (qA : QuadraticForm K A)

theorem ActsOn_rEl {x y : I} (hfst : coordIdx x.1 ≠ coordIdx y.1) (hswap : ∀ i : I, x.1.swap ≠ i.1) (t : K) :
    ActsOn I (rEl qA t x.1 y.1) (Matrix.transvection x y t) := by
  intro i
  rw [rEl_apply_hypVec qA hfst t i.1, sum_transvection_smul]
  have h2 : (if i.1 = x.1.swap then t else 0) = 0 := by
    rw [ite_eq_right_iff]
    intro h
    exact absurd h.symm (hswap i)
  rw [h2, zero_smul, sub_zero]
  have : (if i.1 = y.1 then t else 0) = (if i = y then t else 0) := by
    by_cases h : i = y
    · simp [h]
    · have : i.1 ≠ y.1 := fun h' => h (Subtype.ext h')
      simp [h, this]
  rw [this]

theorem ActsOn_tor {d : Fin r → Kˣ} {D : I → K} (hD : ∀ i : I, (wt d i.1 : K) = D i) :
    ActsOn I (torH K A r d) (Matrix.diagonal D) := by
  intro i
  rw [torH_hypVec, hD i]
  simp [Matrix.diagonal_apply]

variable (S : Subgroup (Fin r → Kˣ))

open _root_.Classical in
@[expose] def cls (j₀ : Fin r ⊕ Fin r) : Finset (Fin r ⊕ Fin r) :=
  Finset.univ.filter fun j => SimOn S j j₀

variable {S}

theorem mem_cls {j₀ j : Fin r ⊕ Fin r} : j ∈ cls S j₀ ↔ SimOn S j j₀ := by
  simp [cls]

theorem cls_nontriv {j₀ i : Fin r ⊕ Fin r} (hj₀ : ¬ TrivOn S j₀) (hi : i ∈ cls S j₀) : ¬ TrivOn S i :=
  fun h => hj₀ (TrivOn.of_sim S (mem_cls.1 hi) h)

theorem cls_sim {j₀ i i' : Fin r ⊕ Fin r} (hi : i ∈ cls S j₀) (hi' : i' ∈ cls S j₀) : SimOn S i i' :=
  (mem_cls.1 hi).trans S (mem_cls.1 hi').symm

theorem cls_coordIdx_ne [CharP K 2] {j₀ i i' : Fin r ⊕ Fin r} (hj₀ : ¬ TrivOn S j₀) (hi : i ∈ cls S j₀)
    (hi' : i' ∈ cls S j₀) (hne : i ≠ i') : coordIdx i ≠ coordIdx i' :=
  coordIdx_ne_of_sim S (cls_nontriv hj₀ hi) (cls_sim hi hi') hne

theorem cls_swap_not_mem [CharP K 2] {j₀ i : Fin r ⊕ Fin r} (hj₀ : ¬ TrivOn S j₀) (hi : i ∈ cls S j₀) :
    i.swap ∉ cls S j₀ := fun h => not_sim_swap S (cls_nontriv hj₀ hi) (cls_sim hi h)

@[expose] def matOf (g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) (I : Finset (Fin r ⊕ Fin r)) :
    Matrix I I K := fun i' i => (g (hypVec K A i.1)).1 i'.1

theorem actsOn_matOf {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)}
    (hg : ∀ d ∈ S, g * torH K A r d = torH K A r d * g) {j₀ : Fin r ⊕ Fin r} (hj₀ : ¬ TrivOn S j₀) :
    ActsOn (cls S j₀) g (matOf (A := A) g (cls S j₀)) := by
  classical
  intro i
  set w := g (hypVec K A i.1) with hw
  have h2 : w.2 = 0 := entry_snd_eq_zero hg (cls_nontriv hj₀ i.2)
  have h1 : ∀ j, j ∉ cls S j₀ → w.1 j = 0 := by
    intro j hj
    refine entry_coord_eq_zero hg fun hs => hj (mem_cls.2 ?_)
    exact hs.trans S (mem_cls.1 i.2)
  have hexp := vec_expand w
  rw [h2] at hexp
  have hsub : ∑ j : Fin r ⊕ Fin r, w.1 j • hypVec K A j = ∑ j ∈ cls S j₀, w.1 j • hypVec K A j := by
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_
    rw [h1 j hj, zero_smul]
  have hz : ((0 : Fin r ⊕ Fin r → K), (0 : A)) = (0 : (Fin r ⊕ Fin r → K) × A) := rfl
  rw [hz, add_zero, hsub] at hexp
  rw [hexp, ← Finset.sum_coe_sort (cls S j₀)]
  rfl

end CFSG.RankThree.PartOne.K159H
