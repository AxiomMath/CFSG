module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.LeviCopies
import CFSG.LieType.Chevalley.ToralCentralizerQuotient

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
open CFSG.LieType.Steinberg.Adjoint (iform)

section Pairs

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V]

theorem le_finrank_range_sub_one_of_pairs [Module.Finite k V] (A : Module.End k V) {R : ℕ}
    (a b : Fin R → V) (hli : LinearIndependent k (Sum.elim a b)) (c : Fin R → k)
    (hab : ∀ i, A (a i) = c i • b i) :
    R ≤ Module.finrank k (LinearMap.range (A - 1)) := by
  let u : Fin R → V := fun i => (A - 1) (a i)
  have hu_li : LinearIndependent k u := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hsum : ∑ x : Fin R ⊕ Fin R,
        (Sum.elim (fun i => -g i) (fun i => g i * c i)) x • (Sum.elim a b) x = 0 := by
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, neg_smul]
      have h_eq : ∑ i, g i • u i = ∑ i, (g i * c i) • b i - ∑ i, g i • a i := by
        calc
          ∑ i, g i • u i = ∑ i, g i • ((A - 1) (a i)) := by simp [u]
          _ = ∑ i, g i • (A (a i) - a i) := by
            simp only [LinearMap.sub_apply, Module.End.one_apply]
          _ = ∑ i, g i • (c i • b i - a i) := by simp only [hab]
          _ = ∑ i, ((g i * c i) • b i - g i • a i) := by
            simp only [smul_sub, smul_smul]
          _ = ∑ i, (g i * c i) • b i - ∑ i, g i • a i := by
            rw [Finset.sum_sub_distrib]
      have h0 : ∑ i, (g i * c i) • b i - ∑ i, g i • a i = 0 := by
        rw [← h_eq]
        exact hg
      rw [Finset.sum_neg_distrib]
      rw [← sub_eq_neg_add]
      exact h0
    have hzero := (Fintype.linearIndependent_iff.mp hli)
      (Sum.elim (fun i => -g i) (fun i => g i * c i)) hsum
    intro i
    have := hzero (Sum.inl i)
    simpa using this
  have hfin : Module.finrank k (Submodule.span k (Set.range u)) = R := by
    rw [finrank_span_eq_card hu_li]
    simp
  have hle : Submodule.span k (Set.range u) ≤ LinearMap.range (A - 1) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact LinearMap.mem_range_self (A - 1) (a i)
  calc
    R = Module.finrank k (Submodule.span k (Set.range u)) := hfin.symm
    _ ≤ Module.finrank k (LinearMap.range (A - 1)) := Submodule.finrank_mono hle

end Pairs


variable {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]
  {hw : ∃ w₁ : WeylGroup τ, ∀ α : Fin τ.rank → ℤ, w₁ • α = -α}
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {V : Type} [AddCommGroup V] [Module k V]

omit [Algebra K k] [CharP k 2] in
theorem exists_smul_translate_of_monomial {ρ : Representation k (adjointGroup τ K) V} {y : V}
    {χ : adjointGroup τ K → k} {J : Finset (Fin τ.rank)} (ht : IsChevType τ K 2 hw ρ y χ J)
    (z : adjointGroup τ K) (hz : (z : ModGL τ K) ∈ monomialSubgroup τ K) (w : WeylGroup τ) :
    ∃ c : k, ρ z (ρ (nWC τ K w) y) = c • ρ (nWC τ K (weylQuotientHom τ K ⟨z, hz⟩ * w)) y := by
  let σ : WeylGroup τ := weylQuotientHom τ K ⟨z, hz⟩
  let h : adjointGroup τ K := (nWC τ K (σ * w))⁻¹ * z * nWC τ K w
  have hw_mem : (nWC τ K w : ModGL τ K) ∈ monomialSubgroup τ K := by
    simpa [nWC] using canonicalRep_mem_monomialSubgroup (τ := τ) K w
  have hσw_mem : (nWC τ K (σ * w) : ModGL τ K) ∈ monomialSubgroup τ K := by
    simpa [nWC] using canonicalRep_mem_monomialSubgroup (τ := τ) K (σ * w)
  have hh_mem : (h : ModGL τ K) ∈ monomialSubgroup τ K := by
    dsimp [h]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hσw_mem) hz) hw_mem
  have hw_maps : MapsRootLines (nWC τ K w : ModGL τ K) w := by
    simpa [nWC] using mapsRootLines_canonicalRep (τ := τ) (R := K) w
  have hσw_maps : MapsRootLines (nWC τ K (σ * w) : ModGL τ K) (σ * w) := by
    simpa [nWC] using mapsRootLines_canonicalRep (τ := τ) (R := K) (σ * w)
  have hz_maps : MapsRootLines (z : ModGL τ K) σ := by
    simpa [σ] using mapsRootLines_weylQuotientHom (τ := τ) (R := K) ⟨z, hz⟩
  have h_maps : MapsRootLines (h : ModGL τ K) 1 := by
    have hmul : MapsRootLines (((nWC τ K (σ * w) : ModGL τ K)⁻¹ * (z : ModGL τ K)) *
        (nWC τ K w : ModGL τ K)) (((σ * w)⁻¹ * σ) * w) :=
      (hσw_maps.inv.mul hz_maps).mul hw_maps
    rw [show (σ * w)⁻¹ * σ * w = 1 by group] at hmul
    simpa [h] using hmul
  have h_torus : (h : ModGL τ K) ∈ torusGroup τ K :=
    mem_torusGroup_of_mapsRootLines_one hh_mem h_maps
  have hH : h ∈ (chevDatum τ K 2 hw).H := by
    change (h : ModGL τ K) ∈ torusGroup τ K
    exact h_torus
  have hchi : ρ h y = χ h • y := ht.2.2.1 h hH
  refine ⟨χ h, ?_⟩
  have hz_split : z * nWC τ K w = nWC τ K (σ * w) * h := by
    dsimp [h]
    group
  calc
    ρ z (ρ (nWC τ K w) y) = ρ (z * nWC τ K w) y := by
      rw [map_mul, Module.End.mul_apply]
    _ = ρ (nWC τ K (σ * w) * h) y := by rw [hz_split]
    _ = ρ (nWC τ K (σ * w)) (ρ h y) := by
      rw [map_mul, Module.End.mul_apply]
    _ = ρ (nWC τ K (σ * w)) (χ h • y) := by rw [hchi]
    _ = χ h • ρ (nWC τ K (σ * w)) y := by
      rw [map_smul]

theorem le_finrank_range_sub_one_of_monomial [Module.Finite k V]
    {ρ : Representation k (adjointGroup τ K) V} (hρ : IsSimpleRep ρ) {y : V}
    {χ : adjointGroup τ K → k} {J : Finset (Fin τ.rank)} (ht : IsChevType τ K 2 hw ρ y χ J)
    {v₀ : Fin τ.rank → ℤ} (hv : ∀ j ∈ J, reflect τ j v₀ = v₀) (z : adjointGroup τ K)
    (hz : (z : ModGL τ K) ∈ monomialSubgroup τ K) {R : ℕ} (w : Fin R → WeylGroup τ)
    (hinj : Function.Injective (Sum.elim (fun i => w i • v₀)
      (fun i => (weylQuotientHom τ K ⟨z, hz⟩ * w i) • v₀))) :
    R ≤ Module.finrank k (LinearMap.range (ρ z - 1)) := by
  let σ : WeylGroup τ := weylQuotientHom τ K ⟨z, hz⟩
  let a : Fin R → V := fun i => ρ (nWC τ K (w i)) y
  let b : Fin R → V := fun i => ρ (nWC τ K (σ * w i)) y
  let w' : Fin (R + R) → WeylGroup τ := fun i =>
    Sum.elim w (fun j => σ * w j) (finSumFinEquiv.symm i)
  have hw'_apply : ∀ x : Fin R ⊕ Fin R,
      (Sum.elim w (fun j => σ * w j) x) • v₀ =
      (Sum.elim (fun k => w k • v₀) (fun k => (σ * w k) • v₀)) x := by
    intro x
    cases x <;> rfl
  have hw'_inj : ∀ i j, i ≠ j → w' i • v₀ ≠ w' j • v₀ := by
    intro i j hij h
    apply hij
    apply finSumFinEquiv.symm.injective
    apply hinj
    rw [← hw'_apply (finSumFinEquiv.symm i), ← hw'_apply (finSumFinEquiv.symm j)]
    exact h
  have hli' : LinearIndependent k (fun i : Fin (R + R) => ρ (nWC τ K (w' i)) y) :=
    linearIndependent_translates_of_isChevType_mem hρ ht hv w' hw'_inj
  have hfun : ((fun i : Fin (R + R) => ρ (nWC τ K (w' i)) y) ∘ finSumFinEquiv) =
      Sum.elim a b := by
    funext x
    cases x with
    | inl k =>
      simp [a, w', Sum.elim, finSumFinEquiv_symm_apply_castAdd]
    | inr k =>
      have hk : finSumFinEquiv.symm (k.addNat R) = Sum.inr k := by
        rw [← Fin.natAdd_eq_addNat]
        exact finSumFinEquiv_symm_apply_natAdd k
      simp [b, w', Sum.elim, hk]
  have hli : LinearIndependent k (Sum.elim a b) := by
    have hcomp := hli'.comp finSumFinEquiv finSumFinEquiv.injective
    rwa [hfun] at hcomp
  have hc : ∀ i : Fin R, ∃ c : k, ρ z (a i) = c • b i := by
    intro i
    simpa [a, b, σ] using exists_smul_translate_of_monomial ht z hz (w i)
  choose c hc' using hc
  exact le_finrank_range_sub_one_of_pairs (ρ z) a b hli c hc'

end CFSG.LocalAnalysis.WeakClosure81
