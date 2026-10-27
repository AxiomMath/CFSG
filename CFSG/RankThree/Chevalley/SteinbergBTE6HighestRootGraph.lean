module

public import CFSG.RankThree.Chevalley.SteinbergBTEvenTwistedE6SixTorus
public import CFSG.RankThree.E6.RootLatticeTools
public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedUnipotent

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint (iform)

abbrev e6HRIdx (i : Fin 6) : Fin TwistTag.E6.tag.rank := i

@[expose] def e6HRw : WeylGroup TwistTag.E6.tag :=
  simple _ (e6HRIdx 0) * simple _ (e6HRIdx 2) * simple _ (e6HRIdx 3) * simple _ (e6HRIdx 4)

@[expose] def e6HRReflProd : WeylGroup TwistTag.E6.tag :=
  rootReflection (sixTorusRoot 0) * rootReflection (sixTorusRoot 1) *
    rootReflection (sixTorusRoot 2) * rootReflection (sixTorusRoot 3)

theorem sixTorusRoot_three : sixTorusRoot 3 = e6HighestRoot := rfl

theorem e6HR_iform_orth : ∀ i j : Fin 4, i ≠ j → iform (sixTorusRoot i) (sixTorusRoot j) = 0 := by
  decide +kernel

@[expose] def e6HRRefl (β v : Fin TwistTag.E6.tag.rank → ℤ) : Fin TwistTag.E6.tag.rank → ℤ :=
  v - (2 * iform β v / iform β β) • β

theorem e6HR_refl_single : ∀ k : Fin TwistTag.E6.tag.rank,
    e6HRRefl (sixTorusRoot 0) (e6HRRefl (sixTorusRoot 1) (e6HRRefl (sixTorusRoot 2)
      (e6HRRefl (sixTorusRoot 3) (Pi.single k 1)))) = -Pi.single (TwistTag.E6.perm k) 1 := by
  decide +kernel

theorem rootReflection_smul_eq_e6HRRefl {β : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : IsRoot TwistTag.E6.tag β) (v : Fin TwistTag.E6.tag.rank → ℤ) :
    rootReflection β • v = e6HRRefl β v :=
  ((exceptional_Lang_root_rank_one_torus_transport TwistTag.E6.tag ℚ hβ).2.2.2.1 v).1

theorem smul_eq_neg_permLattice {g : WeylGroup TwistTag.E6.tag}
    (h : ∀ k, g • (Pi.single k 1 : Fin TwistTag.E6.tag.rank → ℤ) =
      -Pi.single (TwistTag.E6.perm k) 1) (x : Fin TwistTag.E6.tag.rank → ℤ) :
    g • x = -permLattice TwistTag.E6.perm x := by
  rw [← CFSG.RankThree.E6.weylMatrix_mulVec]
  funext i
  simp only [Matrix.mulVec, dotProduct, CFSG.RankThree.E6.weylMatrix_apply, h, Pi.neg_apply,
    permLattice, Function.comp_apply, neg_mul, Finset.sum_neg_distrib, neg_inj]
  rw [Finset.sum_eq_single (TwistTag.E6.perm.symm i)]
  · rw [Equiv.apply_symm_apply, Pi.single_eq_same, one_mul]
  · intro j _ hj
    rw [Pi.single_eq_of_ne, zero_mul]
    intro e
    exact hj (by rw [e, Equiv.symm_apply_apply])
  · intro h'
    exact absurd (Finset.mem_univ _) h'

theorem e6HRReflProd_smul (x : Fin TwistTag.E6.tag.rank → ℤ) :
    e6HRReflProd • x = -permLattice TwistTag.E6.perm x := by
  refine smul_eq_neg_permLattice (fun k => ?_) x
  rw [e6HRReflProd, mul_smul, mul_smul, mul_smul,
    rootReflection_smul_eq_e6HRRefl (sixTorus_isRoot 3),
    rootReflection_smul_eq_e6HRRefl (sixTorus_isRoot 2),
    rootReflection_smul_eq_e6HRRefl (sixTorus_isRoot 1),
    rootReflection_smul_eq_e6HRRefl (sixTorus_isRoot 0)]
  exact e6HR_refl_single k

@[expose] def e6HRRootVec (m : Fin 72) : Fin TwistTag.E6.tag.rank → ℤ :=
  CFSG.RankThree.E6.e6RootVec m

theorem e6HR_not_isRoot {v : Fin TwistTag.E6.tag.rank → ℤ}
    (h : ∀ m : Fin 72, e6HRRootVec m ≠ v) : ¬IsRoot TwistTag.E6.tag v := by
  intro hv
  obtain ⟨m, hm⟩ := CFSG.RankThree.E6.isRoot_iff_exists_e6RootVec.1 hv
  exact h m hm

theorem e6HR_simple_orth : ∀ i : Fin 6, (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) →
    iform (Pi.single (e6HRIdx i) 1) e6HighestRoot = 0 ∧
      (∀ m : Fin 72, e6HRRootVec m ≠ Pi.single (e6HRIdx i) 1 + e6HighestRoot) ∧
      ∀ m : Fin 72, e6HRRootVec m ≠ Pi.single (e6HRIdx i) 1 - e6HighestRoot := by
  decide +kernel

theorem e6HR_beta_orth : ∀ j : Fin 4, j ≠ 3 →
    iform (sixTorusRoot j) e6HighestRoot = 0 ∧
      (∀ m : Fin 72, e6HRRootVec m ≠ sixTorusRoot j + e6HighestRoot) ∧
      ∀ m : Fin 72, e6HRRootVec m ≠ sixTorusRoot j - e6HighestRoot := by
  decide +kernel

section Group

variable (K : Type) [Field K]

@[expose] def e6HRm : ModGL TwistTag.E6.tag K :=
  weylElt _ K (e6HRIdx 0) 1 * weylElt _ K (e6HRIdx 2) 1 * weylElt _ K (e6HRIdx 3) 1 *
    weylElt _ K (e6HRIdx 4) 1

@[expose] def e6HRn0 : ModGL TwistTag.E6.tag K :=
  rootSL2 _ K (sixTorusRoot 0) WSL * rootSL2 _ K (sixTorusRoot 1) WSL *
    rootSL2 _ K (sixTorusRoot 2) WSL * rootSL2 _ K e6HighestRoot WSL

@[expose] def e6HRn : ModGL TwistTag.E6.tag K := e6HRm K * e6HRn0 K

@[expose] def e6HRTwist (σ : K ≃+* K) (g : ModGL TwistTag.E6.tag K) : ModGL TwistTag.E6.tag K :=
  e6HRn K * diagramMap TwistTag.E6 K * Units.map (entrywiseHom σ.toRingHom) g *
    (diagramMap TwistTag.E6 K)⁻¹ * (e6HRn K)⁻¹

variable {K}

theorem e6HR_weylElt_mem_rootRankOneGroup (i : Fin TwistTag.E6.tag.rank) :
    weylElt TwistTag.E6.tag K i 1 ∈ rootRankOneGroup TwistTag.E6.tag K (Pi.single i 1) := by
  rw [(exceptional_Lang_root_rank_one_torus_transport TwistTag.E6.tag K
    (isRoot_single TwistTag.E6.tag i)).1, weylElt_eq_xUnit_mul]
  refine mul_mem (mul_mem (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ?_))
    (Subgroup.mem_sup_left ?_)
  · rw [← pinnedX_single]
    exact Subgroup.subset_closure ⟨_, rfl⟩
  · rw [← pinnedX_neg_single]
    exact Subgroup.subset_closure ⟨_, rfl⟩
  · rw [← pinnedX_single]
    exact Subgroup.subset_closure ⟨_, rfl⟩

theorem commute_of_strongly_orth {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : IsRoot TwistTag.E6.tag β)
    (h0 : iform β e6HighestRoot = 0)
    (hp : ∀ m : Fin 72, e6HRRootVec m ≠ β + e6HighestRoot)
    (hm : ∀ m : Fin 72, e6HRRootVec m ≠ β - e6HighestRoot)
    {g h : ModGL TwistTag.E6.tag K} (hg : g ∈ rootRankOneGroup TwistTag.E6.tag K β)
    (hh : h ∈ rootRankOneGroup TwistTag.E6.tag K e6HighestRoot) : g * h = h * g :=
  exceptional_Lang_strongly_orthogonal_root_rank_one_commutation TwistTag.E6.tag K hβ
    isRoot_e6HighestRoot h0 (e6HR_not_isRoot hp) (e6HR_not_isRoot hm) g hg h hh

theorem e6HRm_commute {h : ModGL TwistTag.E6.tag K}
    (hh : h ∈ rootRankOneGroup TwistTag.E6.tag K e6HighestRoot) : e6HRm K * h = h * e6HRm K := by
  have hc : ∀ i : Fin 6, (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) →
      weylElt TwistTag.E6.tag K (e6HRIdx i) 1 * h = h * weylElt TwistTag.E6.tag K (e6HRIdx i) 1 :=
    fun i hi => by
      obtain ⟨h0, hp, hm⟩ := e6HR_simple_orth i hi
      exact commute_of_strongly_orth (isRoot_single _ _) h0 hp hm
        (e6HR_weylElt_mem_rootRankOneGroup _) hh
  exact (((Commute.mul_left (hc 0 (by decide)) (hc 2 (by decide))).mul_left
    (hc 3 (by decide))).mul_left (hc 4 (by decide))).eq

theorem e6HR_nbeta_commute {h : ModGL TwistTag.E6.tag K}
    (hh : h ∈ rootRankOneGroup TwistTag.E6.tag K e6HighestRoot) (j : Fin 4) (hj : j ≠ 3) :
    rootSL2 _ K (sixTorusRoot j) WSL * h = h * rootSL2 _ K (sixTorusRoot j) WSL := by
  obtain ⟨h0, hp, hm⟩ := e6HR_beta_orth j hj
  exact commute_of_strongly_orth (sixTorus_isRoot j) h0 hp hm ⟨_, rfl⟩ hh

theorem diagramMap_conj_eq_twistHom (g : ModGL TwistTag.E6.tag K) :
    diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹ =
      twistHom TwistTag.E6 K (RingHom.id K) g := by
  rw [← conj_diagramMap_eq_twistHom]
  rfl

theorem diagramMap_fix_e4 {g : ModGL TwistTag.E6.tag K}
    (hg : g ∈ rootSubgroup TwistTag.E6.tag K (Pi.single (e6HRIdx 3) 1) ⊔
      rootSubgroup TwistTag.E6.tag K (-Pi.single (e6HRIdx 3) 1)) :
    diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹ = g := by
  have hp3 : TwistTag.E6.perm (e6HRIdx 3) = e6HRIdx 3 := by decide
  have hle : rootSubgroup TwistTag.E6.tag K (Pi.single (e6HRIdx 3) 1) ⊔
      rootSubgroup TwistTag.E6.tag K (-Pi.single (e6HRIdx 3) 1) ≤
        Subgroup.centralizer {diagramMap TwistTag.E6 K} := by
    rw [sup_le_iff, rootSubgroup, rootSubgroup, Subgroup.closure_le, Subgroup.closure_le]
    constructor
    · rintro _ ⟨c, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, pinnedX_single]
      have h := diagramMap_conj_eq_twistHom (K := K) (xUnit TwistTag.E6.tag K (e6HRIdx 3) c)
      rw [twistHom_xUnit, hp3, RingHom.id_apply] at h
      calc xUnit TwistTag.E6.tag K (e6HRIdx 3) c * diagramMap TwistTag.E6 K =
            (diagramMap TwistTag.E6 K * xUnit TwistTag.E6.tag K (e6HRIdx 3) c *
              (diagramMap TwistTag.E6 K)⁻¹) * diagramMap TwistTag.E6 K := by rw [h]
        _ = _ := by group
    · rintro _ ⟨c, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, pinnedX_neg_single]
      have h := diagramMap_conj_eq_twistHom (K := K) (yUnit TwistTag.E6.tag K (e6HRIdx 3) c)
      rw [twistHom_yUnit, hp3, RingHom.id_apply] at h
      calc yUnit TwistTag.E6.tag K (e6HRIdx 3) c * diagramMap TwistTag.E6 K =
            (diagramMap TwistTag.E6 K * yUnit TwistTag.E6.tag K (e6HRIdx 3) c *
              (diagramMap TwistTag.E6 K)⁻¹) * diagramMap TwistTag.E6 K := by rw [h]
        _ = _ := by group
  have h := Subgroup.mem_centralizer_singleton_iff.1 (hle hg)
  rw [← h]
  group

theorem diagramMap_fix_theta {g : ModGL TwistTag.E6.tag K}
    (hg : g ∈ rootSubgroup TwistTag.E6.tag K e6HighestRoot ⊔
      rootSubgroup TwistTag.E6.tag K (-e6HighestRoot)) :
    diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹ = g := by
  set W := ((sixTorusWord 3).map fun i => weylElt TwistTag.E6.tag K i 1).prod with hWdef
  have hWe : (coxeterSystem TwistTag.E6.tag).wordProd (sixTorusWord 3) •
      (Pi.single (e6HRIdx 3) 1 : Fin TwistTag.E6.tag.rank → ℤ) = e6HighestRoot := by
    rw [wordProd_smul]
    exact (sixTorus_foldr_root 3).1
  have hWn : (coxeterSystem TwistTag.E6.tag).wordProd (sixTorusWord 3) •
      (-Pi.single (e6HRIdx 3) 1 : Fin TwistTag.E6.tag.rank → ℤ) = -e6HighestRoot := by
    rw [smul_neg, hWe]
  have hθ : rootSubgroup TwistTag.E6.tag K e6HighestRoot ⊔
      rootSubgroup TwistTag.E6.tag K (-e6HighestRoot) =
        (rootSubgroup TwistTag.E6.tag K (Pi.single (e6HRIdx 3) 1) ⊔
          rootSubgroup TwistTag.E6.tag K (-Pi.single (e6HRIdx 3) 1)).map
            (MulAut.conj W).toMonoidHom := by
    rw [Subgroup.map_sup, map_conj_prod_weylElt_rootSubgroup K _ (isRoot_single _ _),
      map_conj_prod_weylElt_rootSubgroup K _ (IsRoot.neg (isRoot_single _ _)), hWe, hWn]
  rw [hθ] at hg
  obtain ⟨h, hh, rfl⟩ := hg
  have hPW : diagramMap TwistTag.E6 K * W * (diagramMap TwistTag.E6 K)⁻¹ = W := by
    rw [diagramMap_conj_eq_twistHom, hWdef, ← sixTorusH_eq]
    exact twistHom_sixTorusH (RingHom.id K) 3
  have hPh := diagramMap_fix_e4 hh
  change diagramMap TwistTag.E6 K * (W * h * W⁻¹) * (diagramMap TwistTag.E6 K)⁻¹ = W * h * W⁻¹
  calc diagramMap TwistTag.E6 K * (W * h * W⁻¹) * (diagramMap TwistTag.E6 K)⁻¹ =
        (diagramMap TwistTag.E6 K * W * (diagramMap TwistTag.E6 K)⁻¹) *
          (diagramMap TwistTag.E6 K * h * (diagramMap TwistTag.E6 K)⁻¹) *
            (diagramMap TwistTag.E6 K * W * (diagramMap TwistTag.E6 K)⁻¹)⁻¹ := by group
    _ = W * h * W⁻¹ := by rw [hPW, hPh]

theorem rootSL2_WSL_mem_monomial {β : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : IsRoot TwistTag.E6.tag β) :
    rootSL2 TwistTag.E6.tag K β WSL ∈ monomialSubgroup TwistTag.E6.tag K ∧
      MapsRootLines (rootSL2 TwistTag.E6.tag K β WSL) (rootReflection β) := by
  obtain ⟨hn, hπ⟩ := (exceptional_Lang_root_rank_one_torus_transport TwistTag.E6.tag K hβ).2.2.1 1
  have e : rootWeylSL2 TwistTag.E6.tag K β 1 = rootSL2 TwistTag.E6.tag K β WSL := by
    rw [rootWeylSL2, nSL_one]
  rw [e] at hn
  refine ⟨hn, ?_⟩
  have h := mapsRootLines_weylQuotientHom (⟨_, hn⟩ : monomialSubgroup TwistTag.E6.tag K)
  have hπ' : weylQuotientHom TwistTag.E6.tag K ⟨_, hn⟩ = rootReflection β := by
    rw [← hπ]
    congr 1
  rw [hπ'] at h
  exact h

theorem e6HRn_mem_monomial : e6HRn K ∈ monomialSubgroup TwistTag.E6.tag K ∧
    MapsRootLines (e6HRn K) (e6HRw * e6HRReflProd) := by
  have h0 := rootSL2_WSL_mem_monomial (K := K) (sixTorus_isRoot 0)
  have h1 := rootSL2_WSL_mem_monomial (K := K) (sixTorus_isRoot 1)
  have h2 := rootSL2_WSL_mem_monomial (K := K) (sixTorus_isRoot 2)
  have h3 := rootSL2_WSL_mem_monomial (K := K) (sixTorus_isRoot 3)
  refine ⟨mul_mem (mul_mem (mul_mem (mul_mem (weylElt_mem_monomialSubgroup _)
      (weylElt_mem_monomialSubgroup _)) (weylElt_mem_monomialSubgroup _))
      (weylElt_mem_monomialSubgroup _))
    (mul_mem (mul_mem (mul_mem h0.1 h1.1) h2.1) h3.1), ?_⟩
  rw [e6HRn, e6HRm, e6HRn0, e6HRw, e6HRReflProd, ← sixTorusRoot_three]
  exact ((((mapsRootLines_weylElt _).mul (mapsRootLines_weylElt _)).mul
    (mapsRootLines_weylElt _)).mul (mapsRootLines_weylElt _)).mul
    (((h0.2.mul h1.2).mul h2.2).mul h3.2)

end Group

theorem E6_highest_root_graph_fixed_and_signed_order_five_descent (K : Type) [Field K] :
    (∀ j, IsRoot TwistTag.E6.tag (sixTorusRoot j)) ∧ sixTorusRoot 3 = e6HighestRoot ∧
    (∀ i j : Fin 4, i ≠ j → iform (sixTorusRoot i) (sixTorusRoot j) = 0) ∧
    (∀ x, e6HRReflProd • x = -permLattice TwistTag.E6.perm x) ∧
    (rootSL2 TwistTag.E6.tag K e6HighestRoot).range =
      rootSubgroup TwistTag.E6.tag K e6HighestRoot ⊔
        rootSubgroup TwistTag.E6.tag K (-e6HighestRoot) ∧
    (∀ g ∈ rootSubgroup TwistTag.E6.tag K e6HighestRoot ⊔
        rootSubgroup TwistTag.E6.tag K (-e6HighestRoot),
      diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹ = g) ∧
    (∃ hn : e6HRn K ∈ monomialSubgroup TwistTag.E6.tag K,
      weylQuotientHom TwistTag.E6.tag K ⟨_, hn⟩ = e6HRw * e6HRReflProd ∧
      (∀ x, weylQuotientHom TwistTag.E6.tag K ⟨_, hn⟩ • x =
        e6HRw • -permLattice TwistTag.E6.perm x) ∧
      ∀ x, weylQuotientHom TwistTag.E6.tag K ⟨_, hn⟩ • permLattice TwistTag.E6.perm x =
        -(e6HRw • x)) ∧
    (∀ (σ : K ≃+* K) (B : SL2 K), e6HRTwist K σ (rootSL2 TwistTag.E6.tag K e6HighestRoot B) =
      rootSL2 TwistTag.E6.tag K e6HighestRoot
        (WSL * Matrix.SpecialLinearGroup.map σ.toRingHom B * WSL⁻¹)) ∧
    ∀ (σ : K ≃+* K), ∀ g ∈ rootSubgroup TwistTag.E6.tag K e6HighestRoot ⊔
        rootSubgroup TwistTag.E6.tag K (-e6HighestRoot),
      e6HRTwist K σ (e6HRTwist K σ g) = Units.map (entrywiseHom (σ * σ).toRingHom) g := by
  have hrange : (rootSL2 TwistTag.E6.tag K e6HighestRoot).range =
      rootSubgroup TwistTag.E6.tag K e6HighestRoot ⊔
        rootSubgroup TwistTag.E6.tag K (-e6HighestRoot) :=
    (exceptional_Lang_root_rank_one_torus_transport TwistTag.E6.tag K isRoot_e6HighestRoot).1
  obtain ⟨hn, hmaps⟩ := e6HRn_mem_monomial (K := K)
  have hπ : weylQuotientHom TwistTag.E6.tag K ⟨_, hn⟩ = e6HRw * e6HRReflProd :=
    weylQuotientHom_eq hmaps
  have htw : ∀ (σ : K ≃+* K) (B : SL2 K),
      e6HRTwist K σ (rootSL2 TwistTag.E6.tag K e6HighestRoot B) =
        rootSL2 TwistTag.E6.tag K e6HighestRoot
          (WSL * Matrix.SpecialLinearGroup.map σ.toRingHom B * WSL⁻¹) := by
    intro σ B
    set C := Matrix.SpecialLinearGroup.map σ.toRingHom B
    have hX : rootSL2 TwistTag.E6.tag K e6HighestRoot C ∈
        rootSubgroup TwistTag.E6.tag K e6HighestRoot ⊔
          rootSubgroup TwistTag.E6.tag K (-e6HighestRoot) := by
      rw [← hrange]
      exact ⟨C, rfl⟩
    have hY : rootSL2 TwistTag.E6.tag K e6HighestRoot (WSL * C * WSL⁻¹) ∈
        rootRankOneGroup TwistTag.E6.tag K e6HighestRoot := ⟨_, rfl⟩
    have hθY : rootSL2 TwistTag.E6.tag K e6HighestRoot WSL *
        rootSL2 TwistTag.E6.tag K e6HighestRoot C *
          (rootSL2 TwistTag.E6.tag K e6HighestRoot WSL)⁻¹ =
        rootSL2 TwistTag.E6.tag K e6HighestRoot (WSL * C * WSL⁻¹) := by
      rw [map_mul, map_mul, map_inv]
    have hcomm : Commute (e6HRm K * rootSL2 _ K (sixTorusRoot 0) WSL *
        rootSL2 _ K (sixTorusRoot 1) WSL * rootSL2 _ K (sixTorusRoot 2) WSL)
        (rootSL2 TwistTag.E6.tag K e6HighestRoot (WSL * C * WSL⁻¹)) :=
      Commute.mul_left (Commute.mul_left (Commute.mul_left (e6HRm_commute hY)
        (e6HR_nbeta_commute hY 0 (by decide))) (e6HR_nbeta_commute hY 1 (by decide)))
          (e6HR_nbeta_commute hY 2 (by decide))
    rw [e6HRTwist, OrthogonalSemilinearFixedRootDatum.entrywise_rootSL2 σ.toRingHom
      isRoot_e6HighestRoot B]
    calc e6HRn K * diagramMap TwistTag.E6 K * rootSL2 TwistTag.E6.tag K e6HighestRoot C *
          (diagramMap TwistTag.E6 K)⁻¹ * (e6HRn K)⁻¹ =
        e6HRn K * (diagramMap TwistTag.E6 K * rootSL2 TwistTag.E6.tag K e6HighestRoot C *
          (diagramMap TwistTag.E6 K)⁻¹) * (e6HRn K)⁻¹ := by group
      _ = e6HRn K * rootSL2 TwistTag.E6.tag K e6HighestRoot C * (e6HRn K)⁻¹ := by
          rw [diagramMap_fix_theta hX]
      _ = (e6HRm K * rootSL2 _ K (sixTorusRoot 0) WSL * rootSL2 _ K (sixTorusRoot 1) WSL *
            rootSL2 _ K (sixTorusRoot 2) WSL) *
          (rootSL2 TwistTag.E6.tag K e6HighestRoot WSL *
            rootSL2 TwistTag.E6.tag K e6HighestRoot C *
              (rootSL2 TwistTag.E6.tag K e6HighestRoot WSL)⁻¹) *
          (e6HRm K * rootSL2 _ K (sixTorusRoot 0) WSL * rootSL2 _ K (sixTorusRoot 1) WSL *
            rootSL2 _ K (sixTorusRoot 2) WSL)⁻¹ := by
          rw [e6HRn, e6HRn0]
          group
      _ = rootSL2 TwistTag.E6.tag K e6HighestRoot (WSL * C * WSL⁻¹) := by
          rw [hθY, hcomm.eq, mul_inv_cancel_right]
  refine ⟨sixTorus_isRoot, sixTorusRoot_three, e6HR_iform_orth, e6HRReflProd_smul, hrange,
    fun g hg => diagramMap_fix_theta hg, ⟨hn, hπ, fun x => ?_, fun x => ?_⟩, htw, ?_⟩
  · rw [hπ, mul_smul, e6HRReflProd_smul]
  · have hρρ : permLattice TwistTag.E6.perm (permLattice TwistTag.E6.perm x) = x := by
      funext i
      change x (TwistTag.E6.perm.symm (TwistTag.E6.perm.symm i)) = x i
      congr 1
      revert i
      decide
    rw [hπ, mul_smul, e6HRReflProd_smul, hρρ, smul_neg]
  ·
    intro σ g hg
    rw [← hrange] at hg
    obtain ⟨B, rfl⟩ := hg
    have hJ : Matrix.SpecialLinearGroup.map σ.toRingHom (WSL : SL2 K) = WSL := by
      ext i j
      simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
      fin_cases i <;> fin_cases j <;> simp [WSL]
    have hJ2 : ((WSL : SL2 K) : Matrix (Fin 2) (Fin 2) K) * (WSL : SL2 K) = -1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [WSL, Matrix.mul_apply, Fin.sum_univ_two]
    rw [htw, htw, OrthogonalSemilinearFixedRootDatum.entrywise_rootSL2 _ isRoot_e6HighestRoot]
    refine congrArg (rootSL2 TwistTag.E6.tag K e6HighestRoot) ?_
    rw [map_mul, map_mul, map_inv, hJ]
    have hc : ∀ A : SL2 K, (WSL * WSL) * A = A * (WSL * WSL) := fun A => by
      apply Subtype.ext
      simp only [Matrix.SpecialLinearGroup.coe_mul]
      rw [hJ2, neg_one_mul, mul_neg_one]
    calc WSL * (WSL * Matrix.SpecialLinearGroup.map σ.toRingHom
          (Matrix.SpecialLinearGroup.map σ.toRingHom B) * WSL⁻¹) * WSL⁻¹ =
        (WSL * WSL) * Matrix.SpecialLinearGroup.map σ.toRingHom
          (Matrix.SpecialLinearGroup.map σ.toRingHom B) * (WSL * WSL)⁻¹ := by group
      _ = _ := by
        rw [hc, mul_assoc, mul_inv_cancel, mul_one]
        rfl

end CFSG.RankThree.Chevalley
