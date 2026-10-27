module

public import CFSG.RankThree.Chevalley.SteinbergCFTrialityCommutingSL2
public import CFSG.RankThree.Chevalley.SteinbergCFOddG2QPlusTorus
public import CFSG.LieType.Chevalley.OddDiagramFrobeniusFixedDerived
public import CFSG.LieType.Chevalley.OddF4CosetDescent
public import CFSG.LieType.Chevalley.GraphFixedMonomialQuotient
public import CFSG.LieType.Chevalley.Braid
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
public import Certificates.Certificate117
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Defs

variable (K : Type) [Field K]

@[expose] def trialityOppositionShift : ModGL TwistTag.D4.tag K :=
  trialityMiddleRep K * trialityOuterRep K

@[expose] def trialityOpposition : ModGL TwistTag.D4.tag K :=
  trialityOuterRep K * (trialityOppositionShift K * trialityMiddleRep K *
    (trialityOppositionShift K)⁻¹)

@[expose] def trialityOppositionWeyl : WeylGroup TwistTag.D4.tag :=
  TwistTag.D4.orbitReflection ⟨0, by decide⟩ *
    (TwistTag.D4.orbitReflection ⟨1, by decide⟩ * TwistTag.D4.orbitReflection ⟨0, by decide⟩ *
      TwistTag.D4.orbitReflection ⟨1, by decide⟩ *
      (TwistTag.D4.orbitReflection ⟨1, by decide⟩ * TwistTag.D4.orbitReflection ⟨0, by decide⟩)⁻¹)

end Defs

variable {K : Type} [Field K]

theorem baseChangeGL_trialityOpposition {L : Type} [Field L] (ι : K →+* L) :
    baseChangeGL ι (trialityOpposition K) = trialityOpposition L := by
  simp only [trialityOpposition, trialityOppositionShift, trialityOuterRep, trialityMiddleRep,
    map_mul, map_inv, baseChangeGL_canonicalRep]

theorem units_map_entrywiseHom_trialityOpposition (f : K →+* K) :
    Units.map (entrywiseHom f) (trialityOpposition K) = trialityOpposition K := by
  rw [units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_trialityOpposition]

theorem trialityOpposition_apply_mem_bot (b b' : Label TwistTag.D4.tag) :
    ((trialityOpposition K : Module.End K (RootModule TwistTag.D4.tag K))
      (Finsupp.single b 1)) b' ∈ (⊥ : Subfield K) := by
  rw [← baseChangeGL_trialityOpposition (⊥ : Subfield K).subtype, baseChangeGL_apply_single,
    Finsupp.mapRange_apply]
  exact Subtype.mem _

theorem trialityOuterRep_mem_graphFixedRootGroup (σ : K →+* K) :
    trialityOuterRep K ∈ graphFixedRootGroup TwistTag.D4 K σ := by
  rw [trialityOuterRep, canonicalRep_orbitReflection_eq_orbitN TwistTag.D4 σ]
  exact orbitN_mem_graphFixedRootGroup _ σ _ 1

theorem trialityMiddleRep_mem_graphFixedRootGroup (σ : K →+* K) :
    trialityMiddleRep K ∈ graphFixedRootGroup TwistTag.D4 K σ := by
  rw [trialityMiddleRep, canonicalRep_orbitReflection_eq_orbitN TwistTag.D4 σ]
  exact orbitN_mem_graphFixedRootGroup _ σ _ 1

theorem trialityOpposition_mem_graphFixedRootGroup (σ : K →+* K) :
    trialityOpposition K ∈ graphFixedRootGroup TwistTag.D4 K σ := by
  have ho := trialityOuterRep_mem_graphFixedRootGroup (K := K) σ
  have hm := trialityMiddleRep_mem_graphFixedRootGroup (K := K) σ
  have ha : trialityOppositionShift K ∈ graphFixedRootGroup TwistTag.D4 K σ := mul_mem hm ho
  exact mul_mem ho (mul_mem (mul_mem ha hm) (inv_mem ha))

theorem weylElt_one_mem_rootSubgroup_sup_neg {τ : Tag} (i : Fin τ.rank) :
    weylElt τ K i 1 ∈ rootSubgroup τ K (Pi.single i 1) ⊔ rootSubgroup τ K (-Pi.single i 1) := by
  have hx : xUnit τ K i 1 ∈ rootSubgroup τ K (Pi.single i 1) ⊔
      rootSubgroup τ K (-Pi.single i 1) := by
    rw [← pinnedX_single]
    exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨_, rfl⟩)
  rw [weylElt_eq_xUnit_mul]
  refine mul_mem (mul_mem hx ?_) hx
  rw [← pinnedX_neg_single]
  exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨_, rfl⟩)

theorem trialityOppositionShift_conj_mem :
    trialityOppositionShift K * trialityMiddleRep K * (trialityOppositionShift K)⁻¹ ∈
      rootSubgroup TwistTag.D4.tag K (d4Vec ![1, 1, 2, 1]) ⊔
        rootSubgroup TwistTag.D4.tag K (-d4Vec ![1, 1, 2, 1]) := by
  rw [← d4_fold_root, ← map_conj_orbitN_list_rootPair TwistTag.D4 (RingHom.id K)
    [⟨0, by decide⟩, ⟨1, by decide⟩] (isRoot_single _ _)]
  refine ⟨trialityMiddleRep K, ?_, ?_⟩
  · rw [trialityMiddleRep_eq]
    exact weylElt_one_mem_rootSubgroup_sup_neg _
  · simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.prod_cons, List.prod_nil, mul_one, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, ← canonicalRep_orbitReflection_eq_orbitN]
    rfl

theorem commute_trialityOuterRep :
    Commute (trialityOuterRep K)
      (trialityOppositionShift K * trialityMiddleRep K * (trialityOppositionShift K)⁻¹) := by
  obtain ⟨hθ, hcheck⟩ := d4_outer_theta_check
  have hc : ∀ i : Fin TwistTag.D4.tag.rank, i ≠ ⟨2, by decide⟩ →
      Commute (weylElt TwistTag.D4.tag K i 1)
        (trialityOppositionShift K * trialityMiddleRep K * (trialityOppositionShift K)⁻¹) :=
    fun i hi => by
      obtain ⟨hi1, h0, hp, hm⟩ := hcheck i hi
      exact commute_of_mem_rootPair_of_check hi1 hθ h0 hp hm
        (weylElt_one_mem_rootSubgroup_sup_neg i) trialityOppositionShift_conj_mem
  rw [trialityOuterRep_eq]
  exact (hc _ (by decide)).mul_left ((hc _ (by decide)).mul_left (hc _ (by decide)))

theorem trialityOuterRep_sq :
    trialityOuterRep K ^ 2 = torusElt TwistTag.D4.tag K ⟨0, by decide⟩ (-1) *
      (torusElt TwistTag.D4.tag K ⟨1, by decide⟩ (-1) *
        torusElt TwistTag.D4.tag K ⟨3, by decide⟩ (-1)) := by
  have h01 := commute_weylElt_weylElt (t := TwistTag.D4) K (a := ⟨0, by decide⟩)
    (l := ⟨0, by decide⟩) (j := ⟨1, by decide⟩) (by decide) (by decide) (by decide) 1 1
  have h03 := commute_weylElt_weylElt (t := TwistTag.D4) K (a := ⟨0, by decide⟩)
    (l := ⟨0, by decide⟩) (j := ⟨3, by decide⟩) (by decide) (by decide) (by decide) 1 1
  have h13 := commute_weylElt_weylElt (t := TwistTag.D4) K (a := ⟨0, by decide⟩)
    (l := ⟨1, by decide⟩) (j := ⟨3, by decide⟩) (by decide) (by decide) (by decide) 1 1
  rw [trialityOuterRep_eq, (h01.mul_right h03).mul_pow, h13.mul_pow, weylElt_one_sq,
    weylElt_one_sq, weylElt_one_sq]

theorem conj_nested_four {G : Type*} [Group G] (x₀ x₁ x₂ x₃ g : G) :
    x₂ * (x₀ * (x₁ * x₃)) * g * (x₂ * (x₀ * (x₁ * x₃)))⁻¹ =
      x₂ * (x₀ * (x₁ * (x₃ * g * x₃⁻¹) * x₁⁻¹) * x₀⁻¹) * x₂⁻¹ := by
  group

local macro "units_sign_arith" : tactic => `(tactic| (
  refine Units.ext ?_
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, Units.val_neg,
    Units.val_one, Units.val_pow_eq_pow_val]
  norm_num))

theorem trialityOpposition_sq : trialityOpposition K ^ 2 = 1 := by
  have hsq : trialityOpposition K ^ 2 = trialityOuterRep K ^ 2 *
      (trialityOppositionShift K * torusElt TwistTag.D4.tag K ⟨2, by decide⟩ (-1) *
        (trialityOppositionShift K)⁻¹) := by
    rw [trialityOpposition, commute_trialityOuterRep.mul_pow, conj_pow, trialityMiddleRep_eq,
      weylElt_one_sq]
  rw [hsq, trialityOuterRep_sq, trialityOppositionShift, trialityMiddleRep_eq,
    trialityOuterRep_eq, conj_nested_four, torusElt_D4_two, weylElt_conj_D4_three,
    weylElt_conj_D4_one, weylElt_conj_D4_zero, weylElt_conj_D4_two, torusElt_D4_zero,
    torusElt_D4_one, torusElt_D4_three, ← rootDiagUnit_mul, ← rootDiagUnit_mul,
    ← rootDiagUnit_mul, vec4_mul, vec4_mul, vec4_mul, ← rootDiagUnit_one, ← vec4_one]
  refine congrArg _ (vec4_eq ?_ ?_ ?_ ?_) <;> units_sign_arith

theorem trialityOppositionWeyl_smul (v : Fin TwistTag.D4.tag.rank → ℤ) :
    trialityOppositionWeyl • v = -v := by
  have hs : ∀ k : Fin TwistTag.D4.tag.rank,
      trialityOppositionWeyl • (Pi.single k 1 : Fin TwistTag.D4.tag.rank → ℤ) =
        -Pi.single k 1 := by
    intro k
    rw [trialityOppositionWeyl, mul_inv_rev, TwistTag.orbitReflection_inv,
      TwistTag.orbitReflection_inv]
    simp only [mul_smul, TwistTag.orbitReflection_smul]
    revert k
    decide +kernel
  have hv : v = ∑ k, v k • (Pi.single k 1 : Fin TwistTag.D4.tag.rank → ℤ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hv, Finset.smul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_comm, hs k, smul_neg]

theorem mapsRootLines_trialityOpposition :
    MapsRootLines (trialityOpposition K) trialityOppositionWeyl := by
  have h₁ := mapsRootLines_canonicalRep (R := K) (TwistTag.D4.orbitReflection ⟨0, by decide⟩)
  have h₂ := mapsRootLines_canonicalRep (R := K) (TwistTag.D4.orbitReflection ⟨1, by decide⟩)
  exact h₁.mul (((h₂.mul h₁).mul h₂).mul (h₂.mul h₁).inv)

theorem trialityOpposition_mem_monomialSubgroup :
    trialityOpposition K ∈ monomialSubgroup TwistTag.D4.tag K := by
  have h₁ : trialityOuterRep K ∈ monomialSubgroup TwistTag.D4.tag K :=
    canonicalRep_mem_monomialSubgroup K _
  have h₂ : trialityMiddleRep K ∈ monomialSubgroup TwistTag.D4.tag K :=
    canonicalRep_mem_monomialSubgroup K _
  have ha : trialityOppositionShift K ∈ monomialSubgroup TwistTag.D4.tag K := mul_mem h₂ h₁
  exact mul_mem h₁ (mul_mem (mul_mem ha h₂) (inv_mem ha))

theorem weylQuotientHom_trialityOpposition_smul (v : Fin TwistTag.D4.tag.rank → ℤ) :
    weylQuotientHom TwistTag.D4.tag K ⟨_, trialityOpposition_mem_monomialSubgroup⟩ • v = -v := by
  rw [weylQuotientHom_eq mapsRootLines_trialityOpposition]
  exact trialityOppositionWeyl_smul v

theorem trialityOpposition_ne_one : trialityOpposition K ≠ 1 := fun h => by
  have h₁ := (mapsRootLines_trialityOpposition (K := K)).unique (w' := 1) (by
    rw [h]
    exact mapsRootLines_one)
  have h₂ := trialityOppositionWeyl_smul (Pi.single ⟨0, by decide⟩ 1)
  rw [h₁, one_smul] at h₂
  have h₃ := congrFun h₂ ⟨0, by decide⟩
  simp at h₃

theorem trialityOpposition_conj_torus {h : ModGL TwistTag.D4.tag K}
    (hh : h ∈ torusGroup TwistTag.D4.tag K) :
    trialityOpposition K * h * (trialityOpposition K)⁻¹ = h⁻¹ := by
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  rw [conj_rootDiagUnit_of_smul_eq_neg trialityOpposition_mem_monomialSubgroup
    weylQuotientHom_trialityOpposition_smul, rootDiagUnit_inv]

theorem map_conj_trialityOpposition_rootSubgroup {α : Fin TwistTag.D4.tag.rank → ℤ}
    (hα : IsRoot TwistTag.D4.tag α) :
    (rootSubgroup TwistTag.D4.tag K α).map (MulAut.conj (trialityOpposition K)).toMonoidHom =
      rootSubgroup TwistTag.D4.tag K (-α) := by
  obtain ⟨μ, hμ⟩ := conj_pinnedX_of_smul_eq_neg (trialityOpposition_mem_monomialSubgroup (K := K))
    weylQuotientHom_trialityOpposition_smul hα
  rw [rootSubgroup, rootSubgroup, MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨μ * c, (hμ c).symm⟩
  · rintro ⟨c, rfl⟩
    refine ⟨_, ⟨((μ⁻¹ : Kˣ) : K) * c, rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hμ, Units.mul_inv_cancel_left]

theorem triality_prime_field_opposition_involution (K : Type) [Field K] (σ : K ≃+* K) :
    trialityOpposition K ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom ∧
    trialityOpposition K ^ 2 = 1 ∧ trialityOpposition K ≠ 1 ∧
    orderOf (trialityOpposition K) = 2 ∧
    (∀ b b' : Label TwistTag.D4.tag,
      ((trialityOpposition K : Module.End K (RootModule TwistTag.D4.tag K))
        (Finsupp.single b 1)) b' ∈ (⊥ : Subfield K)) ∧
    (∃ hz : trialityOpposition K ∈ monomialSubgroup TwistTag.D4.tag K,
      ∀ v : Fin TwistTag.D4.tag.rank → ℤ, weylQuotientHom TwistTag.D4.tag K ⟨_, hz⟩ • v = -v) ∧
    (∀ h ∈ torusGroup TwistTag.D4.tag K,
      trialityOpposition K * h * (trialityOpposition K)⁻¹ = h⁻¹) ∧
    (∀ α : Fin TwistTag.D4.tag.rank → ℤ, IsRoot TwistTag.D4.tag α →
      (rootSubgroup TwistTag.D4.tag K α).map (MulAut.conj (trialityOpposition K)).toMonoidHom =
        rootSubgroup TwistTag.D4.tag K (-α)) ∧
    (∀ f : K →+* K, Units.map (entrywiseHom f) (trialityOpposition K) = trialityOpposition K) ∧
    ∀ σ' : K →+* K, trialityOpposition K ∈ graphFixedRootGroup TwistTag.D4 K σ' :=
  ⟨trialityOpposition_mem_graphFixedRootGroup _, trialityOpposition_sq,
    trialityOpposition_ne_one, orderOf_eq_prime trialityOpposition_sq trialityOpposition_ne_one,
    trialityOpposition_apply_mem_bot, ⟨_, weylQuotientHom_trialityOpposition_smul⟩,
    fun _ hh => trialityOpposition_conj_torus hh,
    fun _ hα => map_conj_trialityOpposition_rootSubgroup hα,
    units_map_entrywiseHom_trialityOpposition, trialityOpposition_mem_graphFixedRootGroup⟩

end CFSG.RankThree.Chevalley
