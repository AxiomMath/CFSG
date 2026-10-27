module

public import CFSG.Open.StatedDefs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Transvection

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open Matrix

theorem statedSL_zmod_two_eq_top (m : ℕ) :
    CFSG.Open.StatedSL m (ZMod 2) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hu : IsUnit (g : Matrix (Fin m) (Fin m) (ZMod 2)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
  have hdet : (g : Matrix (Fin m) (Fin m) (ZMod 2)).det = 1 := by
    have hne : (g : Matrix (Fin m) (Fin m) (ZMod 2)).det ≠ 0 := isUnit_iff_ne_zero.mp hu
    clear hu
    revert hne
    generalize (g : Matrix (Fin m) (Fin m) (ZMod 2)).det = d
    revert d
    decide
  have hmem : g ∈ {A : GL (Fin m) (ZMod 2) | (A : Matrix (Fin m) (Fin m) (ZMod 2)).det = 1} :=
    hdet
  exact Subgroup.subset_closure hmem

private theorem transvection_mulVec_zmod_two {m : ℕ} (i j : Fin m) (w : Fin m → ZMod 2) :
    (Matrix.transvection i j (1 : ZMod 2)).mulVec w = w + Pi.single i (w j) := by
  funext l
  simp [Matrix.transvection, Matrix.add_mulVec, Matrix.single_mulVec, Pi.single_apply,
    Function.update_apply]

private theorem transvection_isUnit_det_zmod_two {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    IsUnit (Matrix.transvection i j (1 : ZMod 2)).det := by
  have h : (Matrix.transvection i j (1 : ZMod 2)).det = 1 :=
    Matrix.det_transvection_of_ne i j hij 1
  rw [h]
  exact isUnit_one

theorem invariant_subspace_gl (m : ℕ) (W : Submodule (ZMod 2) (Fin m → ZMod 2))
    (hW : ∀ g : GL (Fin m) (ZMod 2), ∀ w ∈ W,
      (g : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec w ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  by_cases h0 : W = ⊥
  · exact Or.inl h0
  refine Or.inr ?_
  obtain ⟨w, hwW, hw0⟩ := (Submodule.ne_bot_iff W).mp h0
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hw0 (funext hc)
  have hwj : w j = 1 := by
    have key : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
    exact key _ hj
  have hei : ∀ i, i ≠ j → (Pi.single i (1 : ZMod 2) : Fin m → ZMod 2) ∈ W := by
    intro i hij
    let g : GL (Fin m) (ZMod 2) :=
      Matrix.GeneralLinearGroup.mk'' (Matrix.transvection i j (1 : ZMod 2))
        (transvection_isUnit_det_zmod_two hij)
    have hg : (Matrix.transvection i j (1 : ZMod 2)).mulVec w ∈ W := hW g w hwW
    rw [transvection_mulVec_zmod_two, hwj] at hg
    exact (W.add_mem_iff_right hwW).mp hg
  have hej : (Pi.single j (1 : ZMod 2) : Fin m → ZMod 2) ∈ W := by
    have hS : (∑ l ∈ Finset.univ.erase j,
        w l • (Pi.single l (1 : ZMod 2) : Fin m → ZMod 2)) ∈ W :=
      W.sum_mem fun l hl => W.smul_mem _ (hei l (Finset.ne_of_mem_erase hl))
    have heq : (Pi.single j (1 : ZMod 2) : Fin m → ZMod 2) +
        ∑ l ∈ Finset.univ.erase j, w l • (Pi.single l (1 : ZMod 2) : Fin m → ZMod 2) = w := by
      funext l
      by_cases hl : l = j
      · subst hl
        simp [hwj, Finset.sum_apply, Pi.single_apply]
      · simp [hl, Finset.sum_apply, Pi.single_apply]
    have hmem : (Pi.single j (1 : ZMod 2) : Fin m → ZMod 2) +
        ∑ l ∈ Finset.univ.erase j, w l • (Pi.single l (1 : ZMod 2) : Fin m → ZMod 2) ∈ W := by
      rw [heq]
      exact hwW
    exact (W.add_mem_iff_left hS).mp hmem
  have hall : ∀ i, (Pi.single i (1 : ZMod 2) : Fin m → ZMod 2) ∈ W := by
    intro i
    by_cases hij : i = j
    · rw [hij]
      exact hej
    · exact hei i hij
  rw [eq_top_iff]
  intro v _
  have hv : v = ∑ i, v i • (Pi.single i (1 : ZMod 2) : Fin m → ZMod 2) := by
    funext l
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hv]
  exact W.sum_mem fun i _ => W.smul_mem _ (hall i)

private theorem zmod_two_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by
  decide

theorem natural_twist {X : Type*} [Group X] {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (ρ ρ' : X →* GL (Fin m) (ZMod 2)) (hρ : Function.Surjective ρ)
    (Φ : (Fin k → Fin m → ZMod 2) ≃+ (Fin k → Fin m → ZMod 2))
    (hΦ : ∀ (x : X) (u : Fin k → Fin m → ZMod 2) (i : Fin k),
      Φ (fun j => (ρ x : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec (u j)) i =
        (ρ' x : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec (Φ u i)) :
    ∃ P : GL (Fin m) (ZMod 2), ∀ x : X, ρ' x = P * ρ x * P⁻¹ := by
  let Φl : (Fin k → Fin m → ZMod 2) →ₗ[ZMod 2] (Fin k → Fin m → ZMod 2) :=
    { toFun := fun u => Φ u
      map_add' := fun u v => Φ.map_add u v
      map_smul' := fun c u => by
        rcases zmod_two_cases c with rfl | rfl <;> simp }
  let Ψ : Fin k → Fin k → (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) := fun i j =>
    (LinearMap.proj i).comp
      (Φl.comp (LinearMap.single (ZMod 2) (fun _ : Fin k => Fin m → ZMod 2) j))
  have hΨ : ∀ (i j : Fin k) (u : Fin m → ZMod 2), Ψ i j u = Φ (Pi.single j u) i :=
    fun i j u => rfl
  have hblock : ∀ (x : X) (i j : Fin k) (u : Fin m → ZMod 2),
      Ψ i j ((ρ x : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec u) =
        (ρ' x : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec (Ψ i j u) := by
    intro x i j u
    have hsingle : (fun j' => (ρ x : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec
        ((Pi.single j u : Fin k → Fin m → ZMod 2) j')) =
        (Pi.single j ((ρ x : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec u) :
          Fin k → Fin m → ZMod 2) := by
      funext j'
      by_cases h : j' = j
      · subst h
        simp
      · simp [Pi.single_eq_of_ne h]
    have h := hΦ x (Pi.single j u) i
    rw [hsingle] at h
    simp only [hΨ]
    exact h
  have hsome : ∃ i j, Ψ i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hvan : ∀ (j : Fin k) (v : Fin m → ZMod 2),
        Φ (Pi.single j v : Fin k → Fin m → ZMod 2) = 0 := by
      intro j v
      funext i
      have h0 := congrArg (fun L => L v) (hcon i j)
      simp only [LinearMap.zero_apply] at h0
      rw [hΨ] at h0
      exact h0
    have hu0 : (Pi.single (⟨0, hk⟩ : Fin k)
        (Pi.single (⟨0, hm⟩ : Fin m) (1 : ZMod 2) : Fin m → ZMod 2) :
        Fin k → Fin m → ZMod 2) = 0 := by
      apply Φ.injective
      rw [map_zero]
      exact hvan _ _
    have h1 := congrFun (congrFun hu0 ⟨0, hk⟩) ⟨0, hm⟩
    simp at h1
  obtain ⟨i0, j0, hne⟩ := hsome
  have hker : LinearMap.ker (Ψ i0 j0) = ⊥ ∨ LinearMap.ker (Ψ i0 j0) = ⊤ := by
    apply invariant_subspace_gl m
    intro g w hw
    obtain ⟨x, rfl⟩ := hρ g
    rw [LinearMap.mem_ker] at hw ⊢
    rw [hblock x i0 j0 w, hw, Matrix.mulVec_zero]
  have hbij : Function.Bijective (Ψ i0 j0) := by
    rcases hker with hbot | htop
    · have hinj : Function.Injective (Ψ i0 j0) := by
        intro x y hxy
        have h0 : Ψ i0 j0 (x - y) = 0 := by
          rw [map_sub, hxy]
          exact sub_self _
        exact sub_eq_zero.mp ((LinearMap.ker_eq_bot'.mp hbot) (x - y) h0)
      exact Finite.injective_iff_bijective.mp hinj
    · exfalso
      apply hne
      apply LinearMap.ext
      intro u
      have hu : u ∈ LinearMap.ker (Ψ i0 j0) := by
        rw [htop]
        exact Submodule.mem_top
      simpa using hu
  obtain ⟨e, he⟩ : ∃ e : (Fin m → ZMod 2) ≃ₗ[ZMod 2] (Fin m → ZMod 2),
      ∀ v, e v = Ψ i0 j0 v :=
    ⟨LinearEquiv.ofBijective (Ψ i0 j0) hbij, fun v => rfl⟩
  obtain ⟨Pm, hPm⟩ : ∃ Pm : Matrix (Fin m) (Fin m) (ZMod 2), ∀ v, Pm.mulVec v = Ψ i0 j0 v :=
    ⟨LinearMap.toMatrix' (Ψ i0 j0), fun v => LinearMap.toMatrix'_mulVec _ v⟩
  obtain ⟨Qm, hQm⟩ : ∃ Qm : Matrix (Fin m) (Fin m) (ZMod 2), ∀ v, Qm.mulVec v = e.symm v :=
    ⟨LinearMap.toMatrix' (e.symm : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2)),
      fun v => LinearMap.toMatrix'_mulVec _ v⟩
  have hPQ : Pm * Qm = 1 := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hQm, hPm, Matrix.one_mulVec, ← he,
      LinearEquiv.apply_symm_apply]
  have hQP : Qm * Pm = 1 := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hQm, hPm, Matrix.one_mulVec, ← he,
      LinearEquiv.symm_apply_apply]
  have hcomm : ∀ x : X, Pm * (ρ x : Matrix (Fin m) (Fin m) (ZMod 2)) =
      (ρ' x : Matrix (Fin m) (Fin m) (ZMod 2)) * Pm := by
    intro x
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hPm]
    exact hblock x i0 j0 v
  refine ⟨⟨Pm, Qm, hPQ, hQP⟩, fun x => ?_⟩
  apply Units.ext
  show (ρ' x : Matrix (Fin m) (Fin m) (ZMod 2)) =
    Pm * (ρ x : Matrix (Fin m) (Fin m) (ZMod 2)) * Qm
  rw [hcomm x, Matrix.mul_assoc, hPQ, Matrix.mul_one]

end CFSG.Quasithin.H13.Ch4.NSB
