module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2ExcFrame
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.Copies
import CFSG.LieType.Chevalley.ToralCentralizerQuotient
import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.TopRank

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
open CFSG.LieType.Steinberg.Adjoint (iform)


variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {V : Type} [AddCommGroup V] [Module k V]

omit [Algebra K k] [CharP k 2] in
theorem e6_exists_smul_translate_of_monomial_cover
    {ρ : Representation k ↥(e6Data_valid.minGroup K) V} {y : V}
    {χ : ↥(e6Data_valid.minGroup K) → k} {J : Finset (Fin Tag.E6.rank)}
    (ht : IsCoverType (e6CoverRankOne K) ρ y χ J) (z : ↥(e6Data_valid.minGroup K))
    (hz : ((Isogeny.e6Isogeny K z : ↥(adjointGroup .E6 K)) : ModGL .E6 K) ∈
      monomialSubgroup .E6 K) (w : WeylGroup .E6) :
    ∃ c : k, ρ z (ρ (canonMin K w) y) =
      c • ρ (canonMin K (weylQuotientHom .E6 K ⟨_, hz⟩ * w)) y := by
  let σ : WeylGroup .E6 := weylQuotientHom .E6 K ⟨_, hz⟩
  let ĥ : ↥(e6Data_valid.minGroup K) := (canonMin K (σ * w))⁻¹ * z * canonMin K w
  have hcoe : ((Isogeny.e6Isogeny K ĥ : ↥(adjointGroup .E6 K)) : ModGL .E6 K) =
      (canonicalRep (coxeterSystem Tag.E6) K (σ * w))⁻¹ *
        ((Isogeny.e6Isogeny K z : ↥(adjointGroup .E6 K)) : ModGL .E6 K) *
        canonicalRep (coxeterSystem Tag.E6) K w := by
    have hsplit : (Isogeny.e6Isogeny K ĥ : ↥(adjointGroup .E6 K)) =
        (Isogeny.e6Isogeny K (canonMin K (σ * w)))⁻¹ * Isogeny.e6Isogeny K z *
          Isogeny.e6Isogeny K (canonMin K w) := by
      rw [show ĥ = (canonMin K (σ * w))⁻¹ * z * canonMin K w from rfl, map_mul, map_mul,
        map_inv]
    rw [hsplit, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e6Isogeny_canonMin (k := K) (σ * w)]
    rw [e6Isogeny_canonMin (k := K) w]
  have hh_mem : ((Isogeny.e6Isogeny K ĥ : ↥(adjointGroup .E6 K)) : ModGL .E6 K) ∈
      monomialSubgroup .E6 K := by
    rw [hcoe]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.inv_mem _ (canonicalRep_mem_monomialSubgroup (τ := .E6) K (σ * w))) hz)
      (canonicalRep_mem_monomialSubgroup (τ := .E6) K w)
  have hz_maps : MapsRootLines (((Isogeny.e6Isogeny K z : ↥(adjointGroup .E6 K)) :
      ModGL .E6 K)) σ := by
    simpa [σ] using mapsRootLines_weylQuotientHom (τ := .E6) (R := K) ⟨_, hz⟩
  have hσw_maps : MapsRootLines (canonicalRep (coxeterSystem Tag.E6) K (σ * w)) (σ * w) :=
    mapsRootLines_canonicalRep (τ := .E6) (R := K) (σ * w)
  have hw_maps : MapsRootLines (canonicalRep (coxeterSystem Tag.E6) K w) w :=
    mapsRootLines_canonicalRep (τ := .E6) (R := K) w
  have h_maps : MapsRootLines (((Isogeny.e6Isogeny K ĥ : ↥(adjointGroup .E6 K)) :
      ModGL .E6 K)) 1 := by
    rw [hcoe]
    have hmul := (hσw_maps.inv.mul hz_maps).mul hw_maps
    rw [show (σ * w)⁻¹ * σ * w = 1 by group] at hmul
    exact hmul
  have h_torus : ((Isogeny.e6Isogeny K ĥ : ↥(adjointGroup .E6 K)) : ModGL .E6 K) ∈
      torusGroup .E6 K :=
    mem_torusGroup_of_mapsRootLines_one hh_mem h_maps
  have hH : ĥ ∈ (chevDatumLD TwistTag.E6 K 2 e6LongestData).H.comap
      (Isogeny.e6IsogenyT K) := by
    refine Subgroup.mem_comap.2 (Subgroup.mem_subgroupOf.2 ?_)
    exact h_torus
  have hchi : ρ ĥ y = χ ĥ • y := ht.2.2.1 ĥ hH
  refine ⟨χ ĥ, ?_⟩
  have hz_split : z * canonMin K w = canonMin K (σ * w) * ĥ := by
    dsimp [ĥ]
    group
  calc
    ρ z (ρ (canonMin K w) y) = ρ (z * canonMin K w) y := by
      rw [map_mul, Module.End.mul_apply]
    _ = ρ (canonMin K (σ * w) * ĥ) y := by rw [hz_split]
    _ = ρ (canonMin K (σ * w)) (ρ ĥ y) := by
      rw [map_mul, Module.End.mul_apply]
    _ = ρ (canonMin K (σ * w)) (χ ĥ • y) := by rw [hchi]
    _ = χ ĥ • ρ (canonMin K (σ * w)) y := by rw [map_smul]

theorem e6_le_finrank_range_sub_one_of_monomial_cover [Module.Finite k V]
    {ρ : Representation k ↥(e6Data_valid.minGroup K) V} (hρ : IsSimpleRep ρ) {y : V}
    {χ : ↥(e6Data_valid.minGroup K) → k} {J : Finset (Fin Tag.E6.rank)}
    (ht : IsCoverType (e6CoverRankOne K) ρ y χ J) {v₀ : Fin Tag.E6.rank → ℤ}
    (hv : ∀ j ∈ J, reflect .E6 j v₀ = v₀) (z : ↥(e6Data_valid.minGroup K))
    (hz : ((Isogeny.e6Isogeny K z : ↥(adjointGroup .E6 K)) : ModGL .E6 K) ∈
      monomialSubgroup .E6 K) {R : ℕ} (w : Fin R → WeylGroup .E6)
    (hinj : Function.Injective (Sum.elim (fun i => w i • v₀)
      (fun i => (weylQuotientHom .E6 K ⟨_, hz⟩ * w i) • v₀))) :
    R ≤ Module.finrank k (LinearMap.range (ρ z - 1)) := by
  let σ : WeylGroup .E6 := weylQuotientHom .E6 K ⟨_, hz⟩
  let a : Fin R → V := fun i => ρ (canonMin K (w i)) y
  let b : Fin R → V := fun i => ρ (canonMin K (σ * w i)) y
  let w' : Fin (R + R) → WeylGroup .E6 := fun i =>
    Sum.elim w (fun j => σ * w j) (finSumFinEquiv.symm i)
  have hv' : ∀ j, reflect Tag.E6 j v₀ ≠ v₀ → j ∉ J := fun j hj hJ => hj (hv j hJ)
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
  have hli' : LinearIndependent k (fun i : Fin (R + R) => ρ (canonMin K (w' i)) y) :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.linearIndependent_translates_support
      hρ ht hv' w' hw'_inj
  have hfun : ((fun i : Fin (R + R) => ρ (canonMin K (w' i)) y) ∘ finSumFinEquiv) =
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
    simpa [a, b, σ] using e6_exists_smul_translate_of_monomial_cover ht z hz (w i)
  choose c hc' using hc
  exact le_finrank_range_sub_one_of_pairs (ρ z) a b hli c hc'

theorem e6_le_finrank_range_frame_sub_one_cover [Module.Finite k V]
    {ρ : Representation k ↥(e6Data_valid.minGroup K) V} (hρ : IsSimpleRep ρ) {y : V}
    {χ : ↥(e6Data_valid.minGroup K) → k} {J : Finset (Fin Tag.E6.rank)}
    (ht : IsCoverType (e6CoverRankOne K) ρ y χ J) {v₀ : Fin Tag.E6.rank → ℤ}
    (hv : ∀ j ∈ J, reflect .E6 j v₀ = v₀) {F : List (Fin Tag.E6.rank → ℤ)}
    (hF : ∀ β ∈ F, IsRoot .E6 β)
    (horth : F.Pairwise fun β γ => iform β γ = 0 ∧ ¬ IsRoot .E6 (β + γ) ∧ ¬ IsRoot .E6 (β - γ))
    (c : (Fin Tag.E6.rank → ℤ) → Kˣ) (z : ↥(e6Data_valid.minGroup K))
    (hz : ((Isogeny.e6Isogeny K z : ↥(adjointGroup .E6 K)) : ModGL .E6 K) =
      (F.map fun β => pinnedX .E6 K β (c β)).prod) {R : ℕ} (w : Fin R → WeylGroup .E6)
    (hinj : Function.Injective (Sum.elim (fun i => w i • v₀)
      (fun i => (reflectionWordProd F * w i) • v₀))) :
    R ≤ Module.finrank k (LinearMap.range (ρ z - 1)) := by
  obtain ⟨g, hm, hσ⟩ := exists_conj_frame_mem_monomialSubgroup (τ := .E6) (K := K) hF horth
    c (Isogeny.e6Isogeny K z) hz
  obtain ⟨ĝ, hĝ⟩ := Isogeny.e6Isogeny_surjective K g
  have hφconj : Isogeny.e6Isogeny K (ĝ * z * ĝ⁻¹) =
      g * Isogeny.e6Isogeny K z * g⁻¹ := by
    rw [map_mul, map_mul, map_inv, hĝ]
  have hz' : ((Isogeny.e6Isogeny K (ĝ * z * ĝ⁻¹) : ↥(adjointGroup .E6 K)) :
      ModGL .E6 K) ∈ monomialSubgroup .E6 K := by
    rw [hφconj]
    exact hm
  have hsub : (⟨_, hz'⟩ : monomialSubgroup .E6 K) = ⟨_, hm⟩ :=
    Subtype.ext (congrArg (fun x : ↥(adjointGroup .E6 K) => (x : ModGL .E6 K)) hφconj)
  have hσ' : weylQuotientHom .E6 K ⟨_, hz'⟩ = reflectionWordProd F := by
    rw [hsub]
    exact hσ
  have hinj' : Function.Injective (Sum.elim (fun i => w i • v₀)
      (fun i => (weylQuotientHom .E6 K ⟨_, hz'⟩ * w i) • v₀)) := by
    simpa only [hσ'] using hinj
  have h := e6_le_finrank_range_sub_one_of_monomial_cover hρ ht hv (ĝ * z * ĝ⁻¹) hz'
    w hinj'
  rwa [CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.finrank_range_rep_conj_sub_one
    ρ ĝ z] at h

end CFSG.LocalAnalysis.WeakClosure81
