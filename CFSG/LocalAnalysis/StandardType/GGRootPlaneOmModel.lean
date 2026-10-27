module

public import CFSG.LocalAnalysis.StandardType.GGRootPlaneOmCore
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaModel

public section

namespace CFSG.StandardType

namespace RootPlaneOm

open Module QuadraticMap Multiplicative NoOffOm CFSG.Assembly CFSG.LieType.Universal.Spin
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.ClassicalGroups.Orthogonal

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ}

omit [Fintype ι] [DecidableEq ι] in
theorem reindex_apply (e : ι ≃ Fin d) (Q₀ : QuadraticForm K (ι → K)) (v : ι → K) :
    reindexQuadraticForm e Q₀ (reindexVectorEquiv e v) = Q₀ v := by
  rw [reindexQuadraticForm, QuadraticMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]

omit [Fintype ι] [DecidableEq ι] in
theorem polar_reindex (e : ι ≃ Fin d) (Q₀ : QuadraticForm K (ι → K)) (v w : ι → K) :
    polar (reindexQuadraticForm e Q₀) (reindexVectorEquiv e v) (reindexVectorEquiv e w) =
      polar Q₀ v w := by
  rw [polar, polar, ← map_add, reindex_apply, reindex_apply, reindex_apply]

theorem glin_spinModel_longRoot (e : ι ≃ Fin d) {Q₀ : QuadraticForm K (ι → K)}
    (hR : (spinMatrix Q₀).range = CFSG.Assembly.LowTwoRank.StatedOmega ⇑Q₀) {N : ℕ}
    (F : HypFrame Q₀ N) {i j : Fin N} (hij : i ≠ j) (s t : Bool) (c : K) (y : Fin d → K) :
    glin ((AutOm.spinModel e Q₀ hR (F.longRoot hij s t (.ofAdd c)) : matrixDerived _) :
        GL (Fin d) K) y =
      y + (c * polar (reindexQuadraticForm e Q₀) y (reindexVectorEquiv e (F.vec j t))) •
          reindexVectorEquiv e (F.vec i s) -
        (c * polar (reindexQuadraticForm e Q₀) y (reindexVectorEquiv e (F.vec i s))) •
          reindexVectorEquiv e (F.vec j t) := by
  obtain ⟨y', rfl⟩ := (reindexVectorEquiv (K := K) e).surjective y
  rw [glin_apply, AutOm.spinModel_mulVec, F.spinAction_longRoot, map_sub, map_add,
    LinearEquiv.map_smul, LinearEquiv.map_smul, polar_reindex, polar_reindex]

section Spin

variable [Finite K] [CharP K 2]

theorem exists_rootPlane_spin (e : ι ≃ Fin d) {Q₀ : QuadraticForm K (ι → K)}
    (hR : (spinMatrix Q₀).range = CFSG.Assembly.LowTwoRank.StatedOmega ⇑Q₀)
    (hπ : Function.Bijective (AutOm.spinModel e Q₀ hR))
    (hnd : (reindexQuadraticForm e Q₀).polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), finrank K T = 3 ∧
      ∀ x ∈ T, reindexQuadraticForm e Q₀ x = 0)
    (hd : 9 ≤ d) {N : ℕ} (F : HypFrame Q₀ N) {i j : Fin N} (hij : i ≠ j) (s t : Bool)
    {G : Type} [Group G] {ψ : spinGroup Q₀ →* G} (hψ : Function.Injective ψ) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {Bs : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hcard : p ^ 4 ≤ Nat.card Bs) (hBψ : Bs ≤ ψ.range) :
    ∃ (E : Subgroup G) (u : spinGroup Q₀), E ≤ Bs ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      E ≤ Subgroup.centralizer ((((F.longRoot hij s t).range.map
        (MulAut.conj u).toMonoidHom).map ψ : Subgroup G) : Set G) ∧
      orderOf (ψ (u * F.longRoot hij s t (.ofAdd 1) * u⁻¹)) = 2 ∧
      ∀ e ∈ E, e ≠ 1 → ∃ L₁ : Subgroup G,
        IsComponentOf L₁ (ψ.range ⊓ Subgroup.centralizer {e}) ∧
          Nat.card (Bs ⊓ Subgroup.centralizer (L₁ : Set G) : Subgroup G) ≤ p ^ 2 := by
  set π := AutOm.spinModel e Q₀ hR with hπdef
  set πe := MulEquiv.ofBijective π hπ with hπe
  set φ : matrixDerived (reindexQuadraticForm e Q₀) →* G := ψ.comp πe.symm.toMonoidHom with hφ
  have hφinj : Function.Injective φ := hψ.comp πe.symm.injective
  have hφπ : ∀ x, φ (π x) = ψ x := fun x => by
    simp only [hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact congrArg ψ (πe.symm_apply_apply x)
  have hφrange : φ.range = ψ.range := by
    ext y
    constructor
    · rintro ⟨X, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨π x, hφπ x⟩
  set R := reindexVectorEquiv (K := K) e with hRdef
  obtain ⟨a, hQa, haux⟩ := F.exists_aux i j
  have hai : LinearIndependent K ![R (F.vec i s), R (F.vec j t)] := by
    have h := (F.linearIndependent_vec_pair hij s t).map' R.toLinearMap R.ker
    convert h using 1
    funext k
    fin_cases k <;> rfl
  obtain ⟨E, g, hEB, hEel, hEcard, hcent, hcomp⟩ := exists_rootPlane_core hnd hT hd hp hp2 hBs
    hSC hcard hφinj (hφrange ▸ hBψ) (a₀ := R (F.vec i s)) (a₁ := R (F.vec j t)) (w := R a)
    (by rw [reindex_apply, F.map_vec]) (by rw [reindex_apply, F.map_vec])
    (by rw [polar_reindex, F.polar_vec_of_ne hij]) hai
    (by rw [reindex_apply]; exact hQa.ne_zero)
    (by rw [polar_reindex, QuadraticMap.polar_comm]; exact (haux s).1)
    (by rw [polar_reindex, QuadraticMap.polar_comm]; exact (haux t).2)
  set u := πe.symm g with hu
  have hπu : π u = g := πe.apply_symm_apply g
  have hψconj : ∀ z, ψ (u * z * u⁻¹) = φ (g * π z * g⁻¹) := fun z => by
    rw [← hφπ (u * z * u⁻¹), map_mul π, map_mul π, map_inv π, hπu]
  refine ⟨E, u, hEB, hEel, hEcard, ?_, ?_, ?_⟩
  · intro y hy
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨_, ⟨_, ⟨c, rfl⟩, rfl⟩, rfl⟩
    change ψ (u * F.longRoot hij s t c * u⁻¹) * y = y * ψ (u * F.longRoot hij s t c * u⁻¹)
    rw [hψconj]
    exact (hcent y hy (π (F.longRoot hij s t c))
      ⟨toAdd c, glin_spinModel_longRoot e hR F hij s t (toAdd c)⟩).symm
  · rw [orderOf_injective ψ hψ, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    refine orderOf_eq_prime ?_ ?_
    · rw [_root_.sq, ← map_mul, ← ofAdd_add, CharTwo.add_self_eq_zero, ofAdd_zero, map_one]
    · intro h1
      have h2 := congrArg (fun z => spinAction Q₀ z (F.vec j (!t))) h1
      simp only [map_one, LinearEquiv.coe_one, id_eq] at h2
      rw [F.spinAction_longRoot, F.polar_not_vec, F.polar_vec_of_ne hij.symm, mul_zero,
        zero_smul, sub_zero, one_mul, one_smul, add_eq_left] at h2
      have h3 := F.polar_vec_not i s
      rw [h2, QuadraticMap.polar_zero_left] at h3
      exact zero_ne_one h3
  · intro y hy hy1
    obtain ⟨L₁, hL₁, hL₁c⟩ := hcomp y hy hy1
    exact ⟨L₁, hφrange ▸ hL₁, hL₁c⟩

omit [CharP K 2] in
theorem exists_genMax_spin (e : ι ≃ Fin d) {Q₀ : QuadraticForm K (ι → K)}
    (hR : (spinMatrix Q₀).range = CFSG.Assembly.LowTwoRank.StatedOmega ⇑Q₀)
    (hπ : Function.Bijective (AutOm.spinModel e Q₀ hR))
    (hnd : (reindexQuadraticForm e Q₀).polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), finrank K T = 3 ∧
      ∀ x ∈ T, reindexQuadraticForm e Q₀ x = 0)
    {G : Type} [Group G] {ψ : spinGroup Q₀ →* G} (hψ : Function.Injective ψ) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {Bs : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) (hBψ : Bs ≤ ψ.range) :
    ∃ A : Subgroup (GL (Fin d) K),
      GenMax (polB (reindexQuadraticForm e Q₀)) (matrixDerived (reindexQuadraticForm e Q₀)) p A ∧
        Nat.card A = Nat.card Bs := by
  set π := AutOm.spinModel e Q₀ hR with hπdef
  set πe := MulEquiv.ofBijective π hπ with hπe
  set φ : matrixDerived (reindexQuadraticForm e Q₀) →* G := ψ.comp πe.symm.toMonoidHom with hφ
  have hφinj : Function.Injective φ := hψ.comp πe.symm.injective
  have hφrange : φ.range = ψ.range := by
    ext y
    constructor
    · rintro ⟨X, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨x, rfl⟩
      refine ⟨π x, ?_⟩
      simp only [hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      exact congrArg ψ (πe.symm_apply_apply x)
  have hBφ : Bs ≤ φ.range := hφrange ▸ hBψ
  refine ⟨_, genMax_of_orth hnd hT hp hp2 hBs hSC φ hφinj hBφ, ?_⟩
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
    ← Subgroup.card_map_of_injective hφinj, Subgroup.map_comap_eq_self hBφ]

end Spin

end RootPlaneOm

end CFSG.StandardType
