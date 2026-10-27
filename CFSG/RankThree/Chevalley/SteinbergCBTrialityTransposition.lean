module

public import CFSG.RankThree.Chevalley.SteinbergCBTrialityPermModule
public import CFSG.LieType.Chevalley.TrialityFullAmbientFixedGroup
public import CFSG.LieType.Chevalley.TrialityAllCharTorusCoordinates
public import CFSG.LieType.Chevalley.GraphFixedCompatibleDiagonal
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def trialityKappa : Equiv.Perm (Fin TwistTag.D4.tag.rank) :=
  Equiv.swap ⟨1, by decide⟩ ⟨3, by decide⟩

theorem trialityKappa_cartan_submatrix :
    TwistTag.D4.tag.cartan.submatrix trialityKappa trialityKappa = TwistTag.D4.tag.cartan := by
  decide

theorem trialityKappa_cartan (i j : Fin TwistTag.D4.tag.rank) :
    TwistTag.D4.tag.cartan (trialityKappa i) (trialityKappa j) = TwistTag.D4.tag.cartan i j :=
  congrFun (congrFun trialityKappa_cartan_submatrix i) j

theorem trialityKappa_mul_self : trialityKappa * trialityKappa = 1 := by
  decide

theorem trialityKappa_mul_perm_mul : trialityKappa * TwistTag.D4.perm * trialityKappa =
    TwistTag.D4.perm.symm := by
  decide

theorem cartan_perm_mul {τ : Tag} {π π' : Equiv.Perm (Fin τ.rank)}
    (hπ : ∀ i j, τ.cartan (π i) (π j) = τ.cartan i j)
    (hπ' : ∀ i j, τ.cartan (π' i) (π' j) = τ.cartan i j) (i j : Fin τ.rank) :
    τ.cartan ((π * π') i) ((π * π') j) = τ.cartan i j := by
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hπ, hπ']

variable (K : Type) [Field K]

@[expose] def trialityTransposition : ModGL TwistTag.D4.tag K :=
  permModuleMap trialityKappa_cartan K

@[expose] def trialityTranspositionAut : MulAut (ModGL TwistTag.D4.tag K) :=
  MulAut.conj (trialityTransposition K)

variable {K}

theorem trialityTranspositionAut_apply (g : ModGL TwistTag.D4.tag K) :
    trialityTranspositionAut K g =
      trialityTransposition K * g * (trialityTransposition K)⁻¹ :=
  rfl

theorem trialityTransposition_mul_self :
    trialityTransposition K * trialityTransposition K = 1 := by
  rw [trialityTransposition, permModuleMap_mul trialityKappa_cartan K trialityKappa_cartan
      (cartan_perm_mul trialityKappa_cartan trialityKappa_cartan)]
  exact (permModuleMap_congr _ K trialityKappa_mul_self fun i j => rfl).trans
    (permModuleMap_one K _)

theorem trialityTransposition_inv :
    (trialityTransposition K)⁻¹ = trialityTransposition K :=
  inv_eq_of_mul_eq_one_right trialityTransposition_mul_self

theorem trialityTranspositionAut_apply_apply (g : ModGL TwistTag.D4.tag K) :
    trialityTranspositionAut K (trialityTranspositionAut K g) = g := by
  rw [trialityTranspositionAut_apply, trialityTranspositionAut_apply, trialityTransposition_inv]
  calc trialityTransposition K * (trialityTransposition K * g * trialityTransposition K) *
        trialityTransposition K =
      (trialityTransposition K * trialityTransposition K) * g *
        (trialityTransposition K * trialityTransposition K) := by group
    _ = g := by rw [trialityTransposition_mul_self, one_mul, mul_one]

theorem trialityTranspositionAut_symm_apply (g : ModGL TwistTag.D4.tag K) :
    (trialityTranspositionAut K).symm g = trialityTranspositionAut K g := by
  rw [MulEquiv.symm_apply_eq, trialityTranspositionAut_apply_apply]

theorem trialityTranspositionAut_diagramMap :
    trialityTranspositionAut K (diagramMap TwistTag.D4 K) = (diagramMap TwistTag.D4 K)⁻¹ := by
  have hρ := cartan_perm_symm TwistTag.D4.cartan_perm
  have h1 : trialityTransposition K * diagramMap TwistTag.D4 K * trialityTransposition K =
      permModuleMap hρ K := by
    rw [trialityTransposition, diagramMap_eq_permModuleMap,
      permModuleMap_mul trialityKappa_cartan K TwistTag.D4.cartan_perm
        (cartan_perm_mul trialityKappa_cartan TwistTag.D4.cartan_perm),
      permModuleMap_mul _ K trialityKappa_cartan
        (cartan_perm_mul (cartan_perm_mul trialityKappa_cartan TwistTag.D4.cartan_perm)
          trialityKappa_cartan)]
    exact permModuleMap_congr _ K trialityKappa_mul_perm_mul hρ
  have h2 : diagramMap TwistTag.D4 K * permModuleMap hρ K = 1 := by
    rw [diagramMap_eq_permModuleMap, permModuleMap_mul TwistTag.D4.cartan_perm K hρ
        (cartan_perm_mul TwistTag.D4.cartan_perm hρ)]
    exact (permModuleMap_congr _ K (mul_inv_cancel TwistTag.D4.perm) fun i j => rfl).trans
      (permModuleMap_one K _)
  rw [trialityTranspositionAut_apply, trialityTransposition_inv, h1]
  exact (inv_eq_of_mul_eq_one_right h2).symm

theorem diagramMap_D4_inv_eq_sq :
    (diagramMap TwistTag.D4 K)⁻¹ = diagramMap TwistTag.D4 K ^ 2 := by
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  rw [← pow_succ]
  exact diagramMap_pow_order TwistTag.D4 K

theorem trialityTransposition_twistHom (σ : K →+* K) (g : ModGL TwistTag.D4.tag K) :
    trialityTranspositionAut K (twistHom TwistTag.D4 K σ g) =
      diagramMap TwistTag.D4 K ^ 2 * Units.map (entrywiseHom σ) (trialityTranspositionAut K g) *
        (diagramMap TwistTag.D4 K ^ 2)⁻¹ := by
  rw [twistHom_apply, map_mul, map_mul, map_inv, trialityTranspositionAut_diagramMap,
    diagramMap_D4_inv_eq_sq, trialityTranspositionAut, trialityTransposition,
    ← units_map_entrywiseHom_conj_permModuleMap]

theorem map_trialityTranspositionAut_adjointGroup :
    (adjointGroup TwistTag.D4.tag K).map (trialityTranspositionAut K).toMonoidHom =
      adjointGroup TwistTag.D4.tag K :=
  map_conj_permModuleMap_adjointGroup trialityKappa_cartan K

theorem trialityTranspositionAut_mem_adjointGroup_iff (g : ModGL TwistTag.D4.tag K) :
    trialityTranspositionAut K g ∈ adjointGroup TwistTag.D4.tag K ↔
      g ∈ adjointGroup TwistTag.D4.tag K := by
  rw [← trialityTranspositionAut_symm_apply, ← Subgroup.mem_map_equiv,
    map_trialityTranspositionAut_adjointGroup]

theorem map_trialityTranspositionAut_twistedFixedGroup (σ : K ≃+* K) :
    (twistedFixedGroup TwistTag.D4 K σ.toRingHom).map (trialityTranspositionAut K).toMonoidHom =
      twistedFixedGroup TwistTag.D4 K σ.symm.toRingHom := by
  ext g
  rw [Subgroup.mem_map_equiv, trialityTranspositionAut_symm_apply,
    mem_twistedFixedGroup_iff_twistHom, mem_twistedFixedGroup_iff_twistHom,
    trialityTranspositionAut_mem_adjointGroup_iff, ← (trialityTranspositionAut K).injective.eq_iff,
    trialityTransposition_twistHom, trialityTranspositionAut_apply_apply,
    diagramMap_sq_conj_eq_iff σ g]

theorem symm_eq_sq_of_pow_three (σ : K ≃+* K) (hσ : σ ^ 3 = 1) : σ.symm = σ ^ 2 := by
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  rw [← pow_succ]
  exact hσ

theorem map_trialityTranspositionAut_graphFixedPosUnipotent (σ : K ≃+* K) :
    (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).map
        (trialityTranspositionAut K).toMonoidHom =
      graphFixedPosUnipotent TwistTag.D4 K σ.symm.toRingHom := by
  rw [graphFixedPosUnipotent, graphFixedPosUnipotent,
    Subgroup.map_inf _ _ _ (trialityTranspositionAut K).injective,
    map_trialityTranspositionAut_twistedFixedGroup]
  exact congrArg (· ⊓ _) (map_conj_permModuleMap_posUnipotent trialityKappa_cartan K)

theorem map_trialityTranspositionAut_graphFixedNegUnipotent (σ : K ≃+* K) :
    (graphFixedNegUnipotent TwistTag.D4 K σ.toRingHom).map
        (trialityTranspositionAut K).toMonoidHom =
      graphFixedNegUnipotent TwistTag.D4 K σ.symm.toRingHom := by
  rw [graphFixedNegUnipotent, graphFixedNegUnipotent,
    Subgroup.map_inf _ _ _ (trialityTranspositionAut K).injective,
    map_trialityTranspositionAut_twistedFixedGroup]
  exact congrArg (· ⊓ _) (map_conj_permModuleMap_negUnipotent trialityKappa_cartan K)

theorem map_trialityTranspositionAut_graphFixedRootGroup (σ : K ≃+* K) :
    (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).map (trialityTranspositionAut K).toMonoidHom =
      graphFixedRootGroup TwistTag.D4 K σ.symm.toRingHom := by
  rw [graphFixedRootGroup, graphFixedRootGroup, Subgroup.map_sup,
    map_trialityTranspositionAut_graphFixedPosUnipotent,
    map_trialityTranspositionAut_graphFixedNegUnipotent]

theorem map_trialityTranspositionAut_graphFixedRootTorus (σ : K ≃+* K) :
    (graphFixedRootTorus TwistTag.D4 K σ.toRingHom).map (trialityTranspositionAut K).toMonoidHom =
      graphFixedRootTorus TwistTag.D4 K σ.symm.toRingHom := by
  rw [graphFixedRootTorus, graphFixedRootTorus, graphFixedTorus, graphFixedTorus,
    Subgroup.map_inf _ _ _ (trialityTranspositionAut K).injective,
    Subgroup.map_inf _ _ _ (trialityTranspositionAut K).injective,
    map_trialityTranspositionAut_twistedFixedGroup,
    map_trialityTranspositionAut_graphFixedRootGroup]
  exact congrArg (· ⊓ _ ⊓ _) (map_conj_permModuleMap_torusGroup trialityKappa_cartan K)

theorem trialityTranspositionAut_torusElt (i : Fin TwistTag.D4.tag.rank) (u : Kˣ) :
    trialityTranspositionAut K (torusElt TwistTag.D4.tag K i u) =
      torusElt TwistTag.D4.tag K (trialityKappa i) u :=
  conj_permModuleMap_torusElt trialityKappa_cartan K i u

theorem trialityTranspositionAut_weylElt (i : Fin TwistTag.D4.tag.rank) (u : Kˣ) :
    trialityTranspositionAut K (weylElt TwistTag.D4.tag K i u) =
      weylElt TwistTag.D4.tag K (trialityKappa i) u :=
  conj_permModuleMap_weylElt trialityKappa_cartan K i u

theorem trialityTranspositionAut_xUnit (i : Fin TwistTag.D4.tag.rank) (c : K) :
    trialityTranspositionAut K (xUnit TwistTag.D4.tag K i c) =
      xUnit TwistTag.D4.tag K (trialityKappa i) c :=
  conj_permModuleMap_xUnit trialityKappa_cartan K i c

theorem trialityTranspositionAut_yUnit (i : Fin TwistTag.D4.tag.rank) (c : K) :
    trialityTranspositionAut K (yUnit TwistTag.D4.tag K i c) =
      yUnit TwistTag.D4.tag K (trialityKappa i) c :=
  conj_permModuleMap_yUnit trialityKappa_cartan K i c

theorem trialityTranspositionAut_trialityOuterTorus (σ : K ≃+* K) (hσ : σ ^ 3 = 1) (a : Kˣ) :
    trialityTranspositionAut K (trialityOuterTorus K σ a) = trialityOuterTorus K (σ ^ 2) a := by
  have h3 : ∀ x : K, σ (σ (σ x)) = x := fun x => by
    rw [← ringEquiv_pow_three_apply, hσ]
    rfl
  have h4 : Units.map (σ ^ 2).toRingHom.toMonoidHom (Units.map (σ ^ 2).toRingHom.toMonoidHom a) =
      Units.map σ.toRingHom.toMonoidHom a := Units.ext (by
    change σ (σ (σ (σ (a : K)))) = σ a
    rw [h3])
  have h2 : Units.map (σ ^ 2).toRingHom.toMonoidHom a =
      Units.map σ.toRingHom.toMonoidHom (Units.map σ.toRingHom.toMonoidHom a) := Units.ext rfl
  rw [trialityOuterTorus_eq, trialityOuterTorus_eq, map_mul, map_mul,
    trialityTranspositionAut_torusElt, trialityTranspositionAut_torusElt,
    trialityTranspositionAut_torusElt, h4, h2, mul_assoc, mul_assoc,
    (commute_torusElt _ _ _ _).eq]
  rfl

theorem trialityTranspositionAut_trialityMiddleTorus (σ : K ≃+* K)
    (b : (trialityFixedField K σ.toRingHom)ˣ) :
    trialityTranspositionAut K (trialityMiddleTorus K σ b) = trialityMiddleTorus K σ b := by
  rw [trialityMiddleTorus, trialityTranspositionAut_torusElt]
  rfl

theorem trialityTranspositionAut_trialityOuterRep :
    trialityTranspositionAut K (trialityOuterRep K) = trialityOuterRep K := by
  rw [trialityOuterRep_eq, map_mul, map_mul, trialityTranspositionAut_weylElt,
    trialityTranspositionAut_weylElt, trialityTranspositionAut_weylElt]
  have h := commute_weylElt_weylElt (t := TwistTag.D4) K (a := ⟨0, by decide⟩)
    (l := ⟨3, by decide⟩) (j := ⟨1, by decide⟩) (by decide) (by decide) (by decide) 1 1
  exact congrArg (weylElt TwistTag.D4.tag K ⟨0, by decide⟩ 1 * ·) h.eq

theorem trialityTranspositionAut_trialityMiddleRep :
    trialityTranspositionAut K (trialityMiddleRep K) = trialityMiddleRep K := by
  rw [trialityMiddleRep_eq, trialityTranspositionAut_weylElt]
  rfl

theorem mem_orbitField_sq_iff (σ : K ≃+* K) (hσ : σ ^ 3 = 1) (a : Fin TwistTag.D4.foldedTag.rank)
    (c : K) :
    c ∈ orbitField TwistTag.D4 K (σ ^ 2).toRingHom a ↔
      c ∈ orbitField TwistTag.D4 K σ.toRingHom a := by
  have h3 : ∀ x : K, σ (σ (σ x)) = x := fun x => by
    rw [← ringEquiv_pow_three_apply, hσ]
    rfl
  obtain ⟨n, hn⟩ := a
  have hn' : n < 2 := hn
  interval_cases n
  · rw [orbitField_D4_zero_eq_top σ h3]
    have h3' : ∀ x : K, (σ ^ 2) ((σ ^ 2) ((σ ^ 2) x)) = x := fun x => by
      change σ (σ (σ (σ (σ (σ x))))) = x
      rw [h3, h3]
    rw [orbitField_D4_zero_eq_top (σ ^ 2) h3']
  · rw [mem_orbitField_D4_one, mem_orbitField_D4_one]
    change σ (σ c) = c ↔ σ c = c
    constructor
    · intro h
      calc σ c = σ (σ (σ (σ c))) := by rw [h3]
        _ = c := by rw [h, h]
    · intro h
      rw [h, h]

theorem orbitField_sq_eq (σ : K ≃+* K) (hσ : σ ^ 3 = 1) (a : Fin TwistTag.D4.foldedTag.rank) :
    orbitField TwistTag.D4 K (σ ^ 2).toRingHom a = orbitField TwistTag.D4 K σ.toRingHom a :=
  SetLike.ext fun c => mem_orbitField_sq_iff σ hσ a c

theorem trialityTranspositionAut_orbitX (σ : K ≃+* K) (hσ : σ ^ 3 = 1)
    (a : Fin TwistTag.D4.foldedTag.rank) (c : K) (hc : c ∈ orbitField TwistTag.D4 K σ.toRingHom a)
    (hc' : c ∈ orbitField TwistTag.D4 K (σ ^ 2).toRingHom a) :
    trialityTranspositionAut K (orbitX TwistTag.D4 K σ.toRingHom a ⟨c, hc⟩) =
      orbitX TwistTag.D4 K (σ ^ 2).toRingHom a ⟨c, hc'⟩ := by
  have h3 : ∀ x : K, σ (σ (σ x)) = x := fun x => by
    rw [← ringEquiv_pow_three_apply, hσ]
    rfl
  rw [coe_orbitX, coe_orbitX, map_list_prod, List.map_map]
  obtain ⟨n, hn⟩ := a
  have hn' : n < 2 := hn
  interval_cases n
  · have hcard : (TwistTag.D4.orbit ⟨0, by decide⟩).card = 3 := by decide
    have hm : TwistTag.D4.orbitMin ⟨0, by decide⟩ = ⟨0, by decide⟩ := by decide
    have e1 : (TwistTag.D4.perm ^ 1) ⟨0, by decide⟩ = ⟨1, by decide⟩ := by decide
    have e2 : (TwistTag.D4.perm ^ 2) ⟨0, by decide⟩ = ⟨3, by decide⟩ := by decide
    have e0 : (TwistTag.D4.perm ^ 0) ⟨0, by decide⟩ = ⟨0, by decide⟩ := rfl
    have k1 : trialityKappa ⟨1, by decide⟩ = ⟨3, by decide⟩ := by decide
    have k3 : trialityKappa ⟨3, by decide⟩ = ⟨1, by decide⟩ := by decide
    have k0 : trialityKappa ⟨0, by decide⟩ = ⟨0, by decide⟩ := by decide
    have s0 : ∀ τ' : K →+* K, (τ' ^ 0) c = c := fun _ => rfl
    have s1 : ∀ τ' : K →+* K, (τ' ^ 1) c = τ' c := fun _ => rfl
    have s2 : ∀ τ' : K →+* K, (τ' ^ 2) c = τ' (τ' c) := fun _ => rfl
    have q1 : (σ ^ 2).toRingHom c = σ (σ c) := rfl
    have q2 : (σ ^ 2).toRingHom (σ (σ c)) = σ c := by
      change σ (σ (σ (σ c))) = σ c
      rw [h3]
    simp only [hcard, hm, List.range_succ, List.range_zero, List.nil_append, List.map_append,
      List.map_cons, List.map_nil, List.prod_append, List.prod_cons, List.prod_nil, mul_one, e0,
      e1, e2, Function.comp_apply, trialityTranspositionAut_xUnit, k0, k1, k3, s0, s1, s2, q1, q2]
    rw [mul_assoc, mul_assoc, (commute_xUnit_xUnit (t := TwistTag.D4) K (a := ⟨0, by decide⟩)
      (i := ⟨3, by decide⟩) (j := ⟨1, by decide⟩) (by decide) (by decide) _ _).eq]
    rfl
  · have hcard : (TwistTag.D4.orbit ⟨1, by decide⟩).card = 1 := by decide
    have hm : TwistTag.D4.orbitMin ⟨1, by decide⟩ = ⟨2, by decide⟩ := by decide
    simp only [hcard, hm, List.range_one, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, Function.comp_apply, pow_zero, trialityTranspositionAut_xUnit]
    rfl

theorem trialityTranspositionAut_orbitY (σ : K ≃+* K) (hσ : σ ^ 3 = 1)
    (a : Fin TwistTag.D4.foldedTag.rank) (c : K) (hc : c ∈ orbitField TwistTag.D4 K σ.toRingHom a)
    (hc' : c ∈ orbitField TwistTag.D4 K (σ ^ 2).toRingHom a) :
    trialityTranspositionAut K (orbitY TwistTag.D4 K σ.toRingHom a ⟨c, hc⟩) =
      orbitY TwistTag.D4 K (σ ^ 2).toRingHom a ⟨c, hc'⟩ := by
  have h3 : ∀ x : K, σ (σ (σ x)) = x := fun x => by
    rw [← ringEquiv_pow_three_apply, hσ]
    rfl
  rw [coe_orbitY, coe_orbitY, map_list_prod, List.map_map]
  obtain ⟨n, hn⟩ := a
  have hn' : n < 2 := hn
  interval_cases n
  · have hcard : (TwistTag.D4.orbit ⟨0, by decide⟩).card = 3 := by decide
    have hm : TwistTag.D4.orbitMin ⟨0, by decide⟩ = ⟨0, by decide⟩ := by decide
    have e1 : (TwistTag.D4.perm ^ 1) ⟨0, by decide⟩ = ⟨1, by decide⟩ := by decide
    have e2 : (TwistTag.D4.perm ^ 2) ⟨0, by decide⟩ = ⟨3, by decide⟩ := by decide
    have e0 : (TwistTag.D4.perm ^ 0) ⟨0, by decide⟩ = ⟨0, by decide⟩ := rfl
    have k1 : trialityKappa ⟨1, by decide⟩ = ⟨3, by decide⟩ := by decide
    have k3 : trialityKappa ⟨3, by decide⟩ = ⟨1, by decide⟩ := by decide
    have k0 : trialityKappa ⟨0, by decide⟩ = ⟨0, by decide⟩ := by decide
    have s0 : ∀ τ' : K →+* K, (τ' ^ 0) c = c := fun _ => rfl
    have s1 : ∀ τ' : K →+* K, (τ' ^ 1) c = τ' c := fun _ => rfl
    have s2 : ∀ τ' : K →+* K, (τ' ^ 2) c = τ' (τ' c) := fun _ => rfl
    have q1 : (σ ^ 2).toRingHom c = σ (σ c) := rfl
    have q2 : (σ ^ 2).toRingHom (σ (σ c)) = σ c := by
      change σ (σ (σ (σ c))) = σ c
      rw [h3]
    simp only [hcard, hm, List.range_succ, List.range_zero, List.nil_append, List.map_append,
      List.map_cons, List.map_nil, List.prod_append, List.prod_cons, List.prod_nil, mul_one, e0,
      e1, e2, Function.comp_apply, trialityTranspositionAut_yUnit, k0, k1, k3, s0, s1, s2, q1, q2]
    rw [mul_assoc, mul_assoc, (commute_yUnit_yUnit (t := TwistTag.D4) K (a := ⟨0, by decide⟩)
      (i := ⟨3, by decide⟩) (j := ⟨1, by decide⟩) (by decide) (by decide) (by decide) _ _).eq]
    rfl
  · have hcard : (TwistTag.D4.orbit ⟨1, by decide⟩).card = 1 := by decide
    have hm : TwistTag.D4.orbitMin ⟨1, by decide⟩ = ⟨2, by decide⟩ := by decide
    simp only [hcard, hm, List.range_one, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, Function.comp_apply, pow_zero, trialityTranspositionAut_yUnit]
    rfl

theorem exists_mulEquiv_of_map_eq {G : Type*} [Group G] (e : MulAut G) {H H' : Subgroup G}
    (h : H.map e.toMonoidHom = H') : ∃ f : H ≃* H', ∀ g : H, (f g : G) = e g :=
  ⟨(e.subgroupMap H).trans (MulEquiv.subgroupCongr h), fun _ => rfl⟩

theorem triality_diagram_transposition_exchanges_field_orientations (K : Type) [Field K]
    (σ : K ≃+* K) (hσ : σ ^ 3 = 1) :
    (∀ i j, TwistTag.D4.tag.cartan (trialityKappa i) (trialityKappa j) =
      TwistTag.D4.tag.cartan i j) ∧
    (∀ i, (trialityTransposition K : Module.End K (RootModule TwistTag.D4.tag K))
      (hVec TwistTag.D4.tag K i) = hVec TwistTag.D4.tag K (trialityKappa i)) ∧
    (∀ α, IsRoot TwistTag.D4.tag α → IsRoot TwistTag.D4.tag (permLattice trialityKappa α) ∧
      (trialityTransposition K : Module.End K (RootModule TwistTag.D4.tag K))
        (rootVec TwistTag.D4.tag K α) = rootVec TwistTag.D4.tag K (permLattice trialityKappa α)) ∧
    trialityTransposition K * trialityTransposition K = 1 ∧
    (adjointGroup TwistTag.D4.tag K).map (trialityTranspositionAut K).toMonoidHom =
      adjointGroup TwistTag.D4.tag K ∧
    (∀ g, trialityTranspositionAut K (trialityTranspositionAut K g) = g) ∧
    (∀ (f : K →+* K) (g : ModGL TwistTag.D4.tag K),
      Units.map (entrywiseHom f) (trialityTranspositionAut K g) =
        trialityTranspositionAut K (Units.map (entrywiseHom f) g)) ∧
    (twistedFixedGroup TwistTag.D4 K σ.toRingHom).map (trialityTranspositionAut K).toMonoidHom =
      twistedFixedGroup TwistTag.D4 K (σ ^ 2).toRingHom ∧
    (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).map (trialityTranspositionAut K).toMonoidHom =
      graphFixedRootGroup TwistTag.D4 K (σ ^ 2).toRingHom ∧
    (graphFixedRootTorus TwistTag.D4 K σ.toRingHom).map (trialityTranspositionAut K).toMonoidHom =
      graphFixedRootTorus TwistTag.D4 K (σ ^ 2).toRingHom ∧
    (∃ e : twistedFixedGroup TwistTag.D4 K σ.toRingHom ≃*
        twistedFixedGroup TwistTag.D4 K (σ ^ 2).toRingHom,
      ∀ g, (e g : ModGL TwistTag.D4.tag K) = trialityTranspositionAut K g) ∧
    (∃ e : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃*
        graphFixedRootGroup TwistTag.D4 K (σ ^ 2).toRingHom,
      ∀ g, (e g : ModGL TwistTag.D4.tag K) = trialityTranspositionAut K g) ∧
    (∃ e : graphFixedRootTorus TwistTag.D4 K σ.toRingHom ≃*
        graphFixedRootTorus TwistTag.D4 K (σ ^ 2).toRingHom,
      ∀ g, (e g : ModGL TwistTag.D4.tag K) = trialityTranspositionAut K g) ∧
    (∀ a : Kˣ, trialityTranspositionAut K (trialityOuterTorus K σ a) =
      trialityOuterTorus K (σ ^ 2) a) ∧
    (∀ b : (trialityFixedField K σ.toRingHom)ˣ,
      trialityTranspositionAut K (trialityMiddleTorus K σ b) = trialityMiddleTorus K σ b) ∧
    trialityTranspositionAut K (trialityOuterRep K) = trialityOuterRep K ∧
    trialityTranspositionAut K (trialityMiddleRep K) = trialityMiddleRep K ∧
    (∀ a, orbitField TwistTag.D4 K (σ ^ 2).toRingHom a = orbitField TwistTag.D4 K σ.toRingHom a) ∧
    ∀ (a : Fin TwistTag.D4.foldedTag.rank) (c : K)
      (hc : c ∈ orbitField TwistTag.D4 K σ.toRingHom a)
      (hc' : c ∈ orbitField TwistTag.D4 K (σ ^ 2).toRingHom a),
      trialityTranspositionAut K (orbitX TwistTag.D4 K σ.toRingHom a ⟨c, hc⟩) =
          orbitX TwistTag.D4 K (σ ^ 2).toRingHom a ⟨c, hc'⟩ ∧
        trialityTranspositionAut K (orbitY TwistTag.D4 K σ.toRingHom a ⟨c, hc⟩) =
          orbitY TwistTag.D4 K (σ ^ 2).toRingHom a ⟨c, hc'⟩ := by
  have hs := symm_eq_sq_of_pow_three σ hσ
  have hΓ := map_trialityTranspositionAut_twistedFixedGroup (K := K) σ
  have hC := map_trialityTranspositionAut_graphFixedRootGroup (K := K) σ
  have hH := map_trialityTranspositionAut_graphFixedRootTorus (K := K) σ
  rw [hs] at hΓ hC hH
  exact ⟨trialityKappa_cartan, permModuleMap_hVec trialityKappa_cartan K,
    fun α hα => ⟨hα.permLattice trialityKappa_cartan,
      permModuleMap_rootVec trialityKappa_cartan K α hα⟩,
    trialityTransposition_mul_self, map_trialityTranspositionAut_adjointGroup,
    trialityTranspositionAut_apply_apply,
    fun f g => units_map_entrywiseHom_conj_permModuleMap trialityKappa_cartan K f g, hΓ, hC, hH,
    exists_mulEquiv_of_map_eq _ hΓ, exists_mulEquiv_of_map_eq _ hC, exists_mulEquiv_of_map_eq _ hH,
    trialityTranspositionAut_trialityOuterTorus σ hσ,
    trialityTranspositionAut_trialityMiddleTorus σ,
    trialityTranspositionAut_trialityOuterRep, trialityTranspositionAut_trialityMiddleRep,
    orbitField_sq_eq σ hσ, fun a c hc hc' => ⟨trialityTranspositionAut_orbitX σ hσ a c hc hc',
      trialityTranspositionAut_orbitY σ hσ a c hc hc'⟩⟩

end CFSG.RankThree.Chevalley
