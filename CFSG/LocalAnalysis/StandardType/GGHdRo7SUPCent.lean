module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SULinDefs

public section

namespace CFSG.StandardType.HdRo7SU

open CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem su_pCent_holds : SUPCentLeaf := by
  intro p _hp h3 m hm _h3m V _hVadd _hVmod b T hcomm
  classical
  let i0 : Fin m := ⟨0, by omega⟩
  let i1 : Fin m := ⟨1, by omega⟩
  have hi0 : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    simp [i0, i1] at this
  let t : Fin m → Fin m → ZMod p := fun i j => b.repr (T (b j)) i
  have ht : ∀ (σ : Equiv.Perm (Fin m)) (i j : Fin m), t (σ i) (σ j) = t i j := by
    intro σ i j
    have hσ : SUPerm p b (b.equiv b σ) :=
      ⟨σ, fun k => by rw [Module.Basis.equiv_apply]⟩
    have h := LinearMap.congr_fun (hcomm (b.equiv b σ) hσ) (b j)
    simp only [LinearMap.comp_apply] at h
    simp only [LinearEquiv.coe_toLinearMap, Module.Basis.equiv_apply] at h
    have hh : T (b (σ j)) = ∑ k, t k j • b (σ k) := by
      rw [h, ← b.sum_repr (T (b j))]
      simp only [t, map_sum, map_smul, LinearEquiv.coe_toLinearMap, Module.Basis.equiv_apply]
    have hc := congrArg (fun w => b.repr w (σ i)) hh
    have hc' : b.repr (∑ k, t k j • b (σ k)) (σ i) = t i j := by
      simp only [map_sum, map_smul, Finsupp.finset_sum_apply, Module.Basis.repr_self_apply,
        Finsupp.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hk
        have hki : σ k ≠ σ i := fun h => hk (σ.injective h)
        simp [hki]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    change t (σ i) (σ j) = b.repr (∑ k, t k j • b (σ k)) (σ i) at hc
    rw [hc'] at hc
    exact hc
  have hdiag : ∀ i : Fin m, t i i = t i0 i0 := by
    intro i
    have h := ht (Equiv.swap i i0) i i
    simpa using h.symm
  have hoff : ∀ i j : Fin m, i ≠ j → t i j = t i0 i1 := by
    intro i j hij
    let τ : Equiv.Perm (Fin m) := Equiv.swap i i0
    let ρ : Equiv.Perm (Fin m) := Equiv.swap j (τ i1)
    let σ : Equiv.Perm (Fin m) := τ * ρ
    have hτi1 : i ≠ τ i1 := by
      dsimp [τ]
      by_cases h1 : i1 = i
      · rw [h1, Equiv.swap_apply_left]
        rw [← h1]
        exact hi0.symm
      · by_cases h2 : i1 = i0
        · exact absurd h2.symm hi0
        · have hτ : τ i1 = i1 := by
            show Equiv.swap i i0 i1 = i1
            exact Equiv.swap_apply_of_ne_of_ne h1 h2
          rw [hτ]
          exact Ne.symm h1
    have hρi : ρ i = i := by
      dsimp [ρ]
      exact Equiv.swap_apply_of_ne_of_ne hij hτi1
    have hσi : σ i = i0 := by
      dsimp [σ]
      rw [hρi]
      dsimp [τ]
      exact Equiv.swap_apply_left i i0
    have hρj : ρ j = τ i1 := by
      dsimp [ρ]
      exact Equiv.swap_apply_left j (τ i1)
    have hττ : τ (τ i1) = i1 := by
      dsimp [τ]
      exact Equiv.swap_apply_self i i0 i1
    have hσj : σ j = i1 := by
      dsimp [σ]
      rw [hρj, hττ]
    have h := ht σ i j
    rw [hσi, hσj] at h
    exact h.symm
  have hTbasis : ∀ j : Fin m,
      T (b j) = (t i0 i0 - t i0 i1) • b j + t i0 i1 • SUOnes p b := by
    intro j
    rw [← b.sum_repr (T (b j))]
    have hsplit : ∑ i, t i j • b i
        = t j j • b j + ∑ i ∈ Finset.univ.erase j, t i j • b i := by
      rw [Finset.add_sum_erase Finset.univ (fun i => t i j • b i) (Finset.mem_univ j)]
    rw [hsplit, hdiag j]
    have hsum : ∑ i ∈ Finset.univ.erase j, t i j • b i
        = t i0 i1 • ∑ i ∈ Finset.univ.erase j, b i := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hoff i j (Finset.ne_of_mem_erase hi)]
    rw [hsum]
    have hU : SUOnes p b = b j + ∑ i ∈ Finset.univ.erase j, b i := by
      unfold SUOnes
      rw [Finset.add_sum_erase Finset.univ (fun i => b i) (Finset.mem_univ j)]
    rw [hU, smul_add, sub_smul]
    abel
  let J : V →ₗ[ZMod p] V := b.constr (ZMod p) (fun _ => SUOnes p b)
  have hJbasis : ∀ i, J (b i) = SUOnes p b := by
    intro i
    dsimp [J]
    rw [Module.Basis.constr_basis]
  have hJapply : ∀ v, J v = (∑ i, b.repr v i) • SUOnes p b := by
    intro v
    conv_lhs => rw [← b.sum_repr v]
    dsimp [J]
    simp only [map_sum, map_smul, Module.Basis.constr_basis]
    rw [Finset.sum_smul]
  have hTeq : T = (t i0 i0 - t i0 i1) • LinearMap.id + t i0 i1 • J := by
    apply b.ext
    intro j
    rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.id_apply,
      hJbasis j]
    exact hTbasis j
  refine ⟨t i0 i0 - t i0 i1, t i0 i1, fun v => ?_⟩
  rw [hTeq]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, hJapply]
  rw [smul_smul]

end CFSG.StandardType.HdRo7SU
