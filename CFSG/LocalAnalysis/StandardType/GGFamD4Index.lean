module

public import CFSG.LocalAnalysis.StandardType.GGFamD4IndexAux
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4ULang

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

theorem image_componentRoots_eq_of_d4_family
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hp2 : p ≠ 2)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hχp : ∀ γ, IsRoot τ γ → χ (Multiplicative.ofAdd γ) ^ p = 1)
    (hχ1 : ∃ γ, IsRoot τ γ ∧ χ (Multiplicative.ofAdd γ) ≠ 1)
    (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ) (i : KernelComponent χ)
    (hr : compRank (componentRoots χ i) = 4) (hc : (componentRoots χ i).ncard = 24) :
    S.ρ '' componentRoots χ i = componentRoots χ i := by
  classical
  set Ψ := componentRoots χ i with hΨdef
  by_contra hne
  obtain ⟨j, hj⟩ := exists_image_component_of_stable χ hρ S.frob.iform_eq i
  have hj' : S.ρ '' Ψ = componentRoots χ j := hj
  have hij : i ≠ j := by
    rintro rfl
    exact hne hj
  have hΨc : IsRootComponent Ψ := isRootComponent_componentRoots (χ := χ) i
  have hfin : Module.finrank ℤ (Submodule.span ℤ (componentRoots χ j)) =
      Module.finrank ℤ (Submodule.span ℤ Ψ) := by
    have hΛ' : Submodule.span ℤ (componentRoots χ j) =
        Submodule.map (rhoLinMap S) (Submodule.span ℤ Ψ) := by
      rw [← hj', Submodule.map_span]; rfl
    rw [hΛ']
    exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
      (fun x y hxy => S.ρ.injective hxy) _)).symm
  have horth : ∀ u ∈ Submodule.span ℤ Ψ, ∀ v ∈ Submodule.span ℤ (componentRoots χ j),
      iform u v = 0 := fun u hu v hv =>
    iform_eq_zero_of_mem_span (fun x hx y hy => iform_eq_zero_of_mem_componentRoots' hij hx hy)
      hu hv
  have hle := finrank_add_finrank_le_of_orth (τ := τ) horth
  have hfΨ : Module.finrank ℤ (Submodule.span ℤ Ψ) = 4 := by
    rw [famD4Index_finrank_span_eq_compRank hΨc, hr]
  rw [hfΨ, hfin] at hle
  have h8 : τ.rank = 8 := le_antisymm (rank_le_eight τ) (by omega)
  have hτE8 : τ = .E8 := by
    rcases hτ with h | h | h
    · rw [h] at h8; simp [Tag.rank] at h8
    · rw [h] at h8; simp [Tag.rank] at h8
    · exact h
  subst hτE8
  have hcard4 : (simpleRoots Ψ).card = 4 := by rw [← compRank_eq_card hΨc, hr]
  let e : simpleRoots Ψ ≃ Fin 4 :=
    Fintype.equivFinOfCardEq (by simpa [Fintype.card_coe] using hcard4)
  let e8 : Fin Tag.E8.rank ≃ Fin 4 ⊕ Fin 4 :=
    (finCongr h8).trans (finSumFinEquiv (m := 4) (n := 4)).symm
  let D₁ : Fin 4 → Fin Tag.E8.rank → ℤ := fun a => (e.symm a : Fin Tag.E8.rank → ℤ)
  let D₂ : Fin 4 → Fin Tag.E8.rank → ℤ := fun a => S.ρ (D₁ a)
  let D' : Fin 4 ⊕ Fin 4 → Fin Tag.E8.rank → ℤ := Sum.elim D₁ D₂
  let D : Fin Tag.E8.rank → Fin Tag.E8.rank → ℤ := fun k => D' (e8 k)
  let Dstd : Fin Tag.E8.rank → Fin Tag.E8.rank → ℤ := fun j => Pi.single j 1
  let M : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ := fun k j => D k j
  have hM : ∀ k, D k = ∑ j, M k j • Dstd j := by
    intro k; ext m
    simp [M, Dstd, Finset.sum_apply, Pi.single_apply]
  have hAdet : (Matrix.of fun a b : Fin 4 => iform (D₁ a) (D₁ b)).det = 4 := by
    have hAsub : (Matrix.of fun a b : Fin 4 => iform (D₁ a) (D₁ b)) =
        (Matrix.of fun β γ : simpleRoots Ψ => iform (β : Fin Tag.E8.rank → ℤ) γ).submatrix
          e.symm e.symm := by
      ext a b
      simp [D₁]
    rw [hAsub, Matrix.det_submatrix_equiv_self e.symm]
    exact famD4Index_det_gram_simpleRoots hτ hΨc hr hc
  have hblock : (Matrix.of fun a b : Fin 4 ⊕ Fin 4 => iform (D' a) (D' b)) =
      Matrix.fromBlocks (Matrix.of fun a b : Fin 4 => iform (D₁ a) (D₁ b)) 0 0
        (Matrix.of fun a b : Fin 4 => iform (D₁ a) (D₁ b)) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b
    · rfl
    · show iform (D₁ a) (D₂ b) = 0
      have hmem : D₂ b ∈ componentRoots χ j := by
        rw [← hj']
        exact ⟨D₁ b, simpleRoots_subset (e.symm b).2, rfl⟩
      exact iform_eq_zero_of_mem_componentRoots' hij (simpleRoots_subset (e.symm a).2) hmem
    · show iform (D₂ a) (D₁ b) = 0
      have hmem : D₂ a ∈ componentRoots χ j := by
        rw [← hj']
        exact ⟨D₁ a, simpleRoots_subset (e.symm a).2, rfl⟩
      exact iform_eq_zero_of_mem_componentRoots' (Ne.symm hij) hmem
        (simpleRoots_subset (e.symm b).2)
    · show iform (D₂ a) (D₂ b) = iform (D₁ a) (D₁ b)
      exact S.frob.iform_eq (D₁ a) (D₁ b)
  have hGD : (Matrix.of fun k l : Fin Tag.E8.rank => iform (D k) (D l)) =
      (Matrix.of fun a b : Fin 4 ⊕ Fin 4 => iform (D' a) (D' b)).submatrix e8 e8 := by
    ext k l; simp [D]
  have hdetGD : (Matrix.of fun k l : Fin Tag.E8.rank => iform (D k) (D l)).det = 16 := by
    rw [hGD, Matrix.det_submatrix_equiv_self e8, hblock, Matrix.det_fromBlocks_zero₁₂, hAdet]
    ring
  have hdetGstd : (Matrix.of fun k l : Fin Tag.E8.rank => iform (Dstd k) (Dstd l)).det = 1 := by
    rw [show (Matrix.of fun k l : Fin Tag.E8.rank => iform (Dstd k) (Dstd l)) =
        Tag.symmetrizedCartan Tag.E8 from by
      rw [famD4Index_gram_std]]
    exact famD4Index_det_std_E8
  have hdetM : M.det ^ 2 = 16 := by
    have h := det_gram_eq_det_sq_mul D Dstd M hM
    rw [hdetGD, hdetGstd, mul_one] at h
    exact h.symm
  have hMdet : M.det = 4 ∨ M.det = -4 := by
    have hfac : (M.det - 4) * (M.det + 4) = 0 := by nlinarith
    rcases mul_eq_zero.1 hfac with h | h
    · left; omega
    · right; omega
  let L : AddSubgroup (Fin Tag.E8.rank → ℤ) :=
    AddSubgroup.closure (Ψ ∪ componentRoots χ j)
  have hDL : ∀ k, D k ∈ L := by
    intro k
    rcases hh : e8 k with a | a
    · have hDk : D k = D₁ a := by simp [D, D', hh]
      rw [hDk]
      exact AddSubgroup.subset_closure (Or.inl (simpleRoots_subset (e.symm a).2))
    · have hDk : D k = D₂ a := by simp [D, D', hh]
      rw [hDk]
      refine AddSubgroup.subset_closure (Or.inr ?_)
      rw [← hj']
      exact ⟨D₁ a, simpleRoots_subset (e.symm a).2, rfl⟩
  have hmem : ∀ k, M.det • Dstd k ∈ L := by
    intro k
    rw [det_smul_eq_sum_adjugate D Dstd M hM k]
    exact AddSubgroup.sum_mem _ fun i _ => AddSubgroup.zsmul_mem _ (hDL i) _
  have h4mem : ∀ k, (4:ℤ) • Dstd k ∈ L := by
    intro k
    rcases hMdet with h4 | h4
    · have h := hmem k
      rwa [h4] at h
    · have h' : (4:ℤ) • Dstd k = -(M.det • Dstd k) := by rw [h4]; simp
      rw [h']; exact AddSubgroup.neg_mem _ (hmem k)
  have hχL : ∀ y ∈ L, χ (Multiplicative.ofAdd y) = 1 := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      rcases hz with hz | hz
      · exact hz.1.2
      · exact hz.1.2
    | zero => simp
    | add x y hx hy ihx ihy => rw [ofAdd_add, map_mul, ihx, ihy, one_mul]
    | neg x hx ih => rw [ofAdd_neg, map_inv, ih, inv_one]
  obtain ⟨γ, hγroot, hγne⟩ := hχ1
  have hγ4 : (4:ℤ) • γ ∈ L := by
    have hγe : γ = ∑ k, γ k • Dstd k := by
      ext m; simp [Dstd, Finset.sum_apply, Pi.single_apply]
    rw [hγe, Finset.smul_sum]
    refine AddSubgroup.sum_mem _ fun k _ => ?_
    rw [smul_comm]
    exact AddSubgroup.zsmul_mem _ (h4mem k) _
  have h4pow : χ (Multiplicative.ofAdd γ) ^ (4:ℕ) = 1 := by
    rw [← map_pow, ← zpow_natCast, ← ofAdd_zsmul]
    exact hχL _ hγ4
  have hppow : χ (Multiplicative.ofAdd γ) ^ p = 1 := hχp γ hγroot
  have hcop : Nat.Coprime 4 p := by
    have hodd : Odd p := hp.odd_of_ne_two hp2
    have h2 : Nat.Coprime 2 p := Nat.coprime_comm.2 ((Nat.coprime_two_right).2 hodd)
    rw [show (4:ℕ) = 2 * 2 by norm_num]
    exact h2.mul_left h2
  have hone : χ (Multiplicative.ofAdd γ) = 1 := by
    have := (pow_gcd_eq_one (a := χ (Multiplicative.ofAdd γ)) (m := 4) (n := p)).2 ⟨h4pow, hppow⟩
    rwa [hcop.gcd_eq_one, pow_one] at this
  exact hγne hone

end CFSG.StandardType.TableCRes
