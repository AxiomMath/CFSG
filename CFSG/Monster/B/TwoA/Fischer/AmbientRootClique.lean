module

public import CFSG.Monster.B.TwoA.Fischer.AmbientRootFixed
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
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3017
public import Certificates.Certificate3029
public import Certificates.Certificate3030
public import Certificates.Certificate3031
public import Certificates.Certificate3067
public import Certificates.Certificate3033
public import Certificates.Certificate3034
public import Certificates.Certificate3035
public import Certificates.Certificate3036
public import Certificates.Certificate3065
public import Certificates.Certificate3066
public import Certificates.Certificate16010
public import Certificates.Certificate16023
public import Certificates.Certificate1953
public import Certificates.Certificate1954

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent AddSubgroupClass.instZModModule

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.Fischer CFSG.Monster.B.TwoA CFSG.Monster.B.Classical.Mog22
  CFSG.Sporadic.SmallF2
open CFSG.Monster.B.E6.FixedE6 CFSG.Monster.B.E6.FixedE6Root CFSG.Monster.B.E6.StdF4
  CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open scoped Matrix IsMulCommutative

theorem ncard_rootClass :
    rootClass.ncard = 3968055 := by
  obtain ⟨q, hq, hcov, hsize, -⟩ := fiveOrbits_rootInv
  have hfin : ∀ i, (conjOrbit (Subgroup.centralizer {rootInv}) (q i)).Finite := fun i =>
    Set.finite_of_ncard_ne_zero (by rw [hsize i]; fin_cases i <;> decide)
  have hdisj : Pairwise (Function.onFun Disjoint fun i =>
      conjOrbit (Subgroup.centralizer {rootInv}) (q i)) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro z hzi hzj
    apply hij
    apply repSize_injective
    rw [← hsize i, ← hsize j, ← conjOrbit_eq_of_mem hzi, ← conjOrbit_eq_of_mem hzj]
  have hunion : rootClass = ⋃ i, conjOrbit (Subgroup.centralizer {rootInv}) (q i) := by
    ext y
    rw [Set.mem_iUnion]
    constructor
    · exact hcov y
    · rintro ⟨i, c, -, rfl⟩
      exact conj_mem_rootClass (hq i) c
  rw [hunion, Set.ncard_iUnion_of_finite hfin hdisj, finsum_eq_sum_of_fintype, Fin.sum_univ_five]
  simp only [hsize]
  rfl

theorem ncard_rootVecSet :
    rootVecSet.ncard = 3968055 := by
  rw [bijOn_rootVecOf.injOn.ncard_image, ncard_rootClass]

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

theorem ptStab_conj_mem {C : Set V} {f : S} (hf : f ∈ setStab act lab Y C) {r : S}
    (hr : r ∈ ptStab act lab Y C) : f⁻¹ * r * f ∈ ptStab act lab Y C := by
  refine ⟨(sliceGroup lab Y).mul_mem ((sliceGroup lab Y).mul_mem
    ((sliceGroup lab Y).inv_mem hf.1) hr.1) hf.1, fun c hc => ?_⟩
  rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hr.2 _ ((hf.2 c).2 hc),
    map_inv, Equiv.Perm.coe_inv, Equiv.symm_apply_apply]

theorem actH_mem_rootFix
    {C : Set V} {ρ : sliceGroup lab Y →* stdGroup}
    (f : setStab act lab Y C) {u : fixedL}
    (hu : u ∈ rootVecSet ∧ ∀ r : ptStab act lab Y C, actH ρ ⟨r, r.2.1⟩ u = u) :
    actH ρ ⟨f, f.2.1⟩ u ∈ rootVecSet ∧
      ∀ r : ptStab act lab Y C, actH ρ ⟨r, r.2.1⟩ (actH ρ ⟨f, f.2.1⟩ u) = actH ρ ⟨f, f.2.1⟩ u := by
  refine ⟨?_, fun r => ?_⟩
  · rw [actH_eq_gL]
    exact gL_mem_rootVecSet hu.1 _
  · have hc := ptStab_conj_mem f.2 r.2
    have e : (⟨r, r.2.1⟩ : sliceGroup lab Y) * ⟨f, f.2.1⟩ =
        ⟨f, f.2.1⟩ * ⟨(f : S)⁻¹ * r * f, hc.1⟩ :=
      Subtype.ext (by simp only [Subgroup.coe_mul, mul_assoc, mul_inv_cancel_left])
    rw [← Equiv.Perm.mul_apply, ← map_mul, e, map_mul, Equiv.Perm.mul_apply,
      hu.2 ⟨(f : S)⁻¹ * r * f, hc⟩]

theorem psi_mem_rootVecSet
    {ρ : sliceGroup lab Y →* stdGroup}
    (hroot : ∀ y : Y, ρ ⟨lab y, lab_mem_sliceGroup y.2⟩ ∈ rootClass)
    {Ψ : NcommQuot lab Y ≃ₗ[ZMod 2] fixedL} (hΨ : ∀ y : Y, Ψ (ncommVec lab Y y) = adjVec ρ y)
    (y : Y) : Ψ (ncommVec lab Y y) ∈ rootVecSet :=
  ⟨_, hroot y, (hΨ y).symm⟩

namespace FullIntertwinerHyp

variable {C : Set V} [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] {x : V}
  {η : C ≃ X₀}
  {θ : setStab act lab Y C ⧸ (ptStab act lab Y C).subgroupOf (setStab act lab Y C) ≃*
    CFSG.Blueprint.NativeSporadic.M22}
  {φ : Additive (Subgroup.closure (lab '' C)) ≃ₗ[ZMod 2] W₀} {α : setStab act lab Y C →* F₀}
  (H : FullIntertwinerHyp act lab Y C x η θ φ α)

include H in
theorem card_ptStab : Nat.card (ptStab act lab Y C) = 2 ^ 10 := by
  rw [H.ptStab_eq, Nat.card_congr (Additive.ofMul.trans φ.toEquiv), natCard_W₀]
  norm_num

variable {Φ : Y ≃ CFSG.Monster.B.Fischer.Y} (hΦ : IsCliqueIntertwiner act lab Y C x η φ α Φ)
  {ρ : sliceGroup lab Y →* stdGroup} (hρ : Function.Injective ρ)
  (hroot : ∀ y : Y, ρ ⟨lab y, lab_mem_sliceGroup y.2⟩ ∈ rootClass)
  {Ψ : NcommQuot lab Y ≃ₗ[ZMod 2] fixedL} (hΨ : ∀ y : Y, Ψ (ncommVec lab Y y) = adjVec ρ y)
include H hΦ

omit hΦ in
theorem odd_ncard_rootFix :
    Odd {u | u ∈ rootVecSet ∧ ∀ r : ptStab act lab Y C, actH ρ ⟨r, r.2.1⟩ u = u}.ncard := by
  have := finite_fixedL
  let _ : MulAction (ptStab act lab Y C) rootVecSet :=
    { smul := fun r u => ⟨actH ρ ⟨r, r.2.1⟩ u, by rw [actH_eq_gL]; exact gL_mem_rootVecSet u.2 _⟩
      one_smul := fun u => Subtype.ext (by
        change actH ρ ⟨(1 : ptStab act lab Y C), _⟩ u = u
        rw [show (⟨((1 : ptStab act lab Y C) : S), (1 : ptStab act lab Y C).2.1⟩ :
          sliceGroup lab Y) = 1 from rfl, map_one, Equiv.Perm.one_apply])
      mul_smul := fun r r' u => Subtype.ext (by
        change actH ρ ⟨((r * r' : ptStab act lab Y C) : S), _⟩ u =
          actH ρ ⟨r, r.2.1⟩ (actH ρ ⟨r', r'.2.1⟩ u)
        rw [show (⟨((r * r' : ptStab act lab Y C) : S), (r * r').2.1⟩ : sliceGroup lab Y) =
          ⟨r, r.2.1⟩ * ⟨r', r'.2.1⟩ from rfl, map_mul, Equiv.Perm.mul_apply]) }
  have hp : IsPGroup 2 (ptStab act lab Y C) := IsPGroup.of_card H.card_ptStab
  have hmod := hp.card_modEq_card_fixedPoints rootVecSet
  rw [Nat.card_coe_set_eq, ncard_rootVecSet] at hmod
  have hset : {u | u ∈ rootVecSet ∧ ∀ r : ptStab act lab Y C, actH ρ ⟨r, r.2.1⟩ u = u} =
      Subtype.val '' (MulAction.fixedPoints (ptStab act lab Y C) rootVecSet) := by
    ext u
    constructor
    · rintro ⟨hu, hr⟩
      exact ⟨⟨u, hu⟩, fun r => Subtype.ext (hr r), rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.2, fun r => congrArg Subtype.val (hu r)⟩
  rw [hset, Set.ncard_image_of_injective _ Subtype.val_injective, ← Nat.card_coe_set_eq,
    Nat.odd_iff]
  exact hmod.symm

include hroot hΨ in
theorem rank_of_mem_cliqueShift
    {u : fixedL} (hu : u ∈ (cliqueFixedVec Φ Ψ + ·) '' cliqueVecs Ψ C)
    (hρ : Function.Injective ρ) :
    Module.finrank (ZMod 2) (LinearMap.range (adL u)) = 22 := by
  rw [H.cliqueShift_eq_orbSet hΦ hroot hΨ] at hu
  obtain ⟨c, hc, rfl⟩ := hu
  rw [H.finrank_range_adL_coordEquiv hΦ hρ hroot hΨ, Cert.rank_orbSet hc]
  rfl

include hρ hroot hΨ in
theorem cliqueFixedVec_mem_rootVecSet :
    cliqueFixedVec Φ Ψ ∈ rootVecSet := by
  have := finite_fixedL
  set Fx := {u | u ∈ rootVecSet ∧ ∀ r : ptStab act lab Y C, actH ρ ⟨r, r.2.1⟩ u = u} with hFx
  set A := cliqueVecs Ψ C with hA
  set B := (cliqueFixedVec Φ Ψ + ·) '' cliqueVecs Ψ C with hB
  have hFR : ∀ u, (∀ r : ptStab act lab Y C, actH ρ ⟨r, r.2.1⟩ u = u) ↔
      u ∈ Submodule.span (ZMod 2) (cliqueVecs Ψ C) := fun u => by
    have h := Set.ext_iff.1 (H.fixed_ptStab_eq hΦ hroot hΨ) u
    exact h
  have hsub : Fx ⊆ A ∪ B ∪ {cliqueFixedVec Φ Ψ} := by
    rintro u ⟨hu, hr⟩
    rw [← H.rank22_eq hΦ hρ hroot hΨ]
    exact ⟨(hFR u).1 hr, finrank_range_adL_of_mem hu⟩
  have hA_sub : A ⊆ Fx := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨psi_mem_rootVecSet hroot hΨ y, (hFR _).2 (Submodule.subset_span ⟨y, hy, rfl⟩)⟩
  have hB_orbit : B = fOrbit act C ρ (gramVec Φ Ψ 437) := (H.fOrbit_six hΦ hroot hΨ).symm
  have hB_cases : (∀ u ∈ B, u ∉ Fx) ∨ B ⊆ Fx := by
    by_cases h : ∃ u ∈ B, u ∈ Fx
    · right
      obtain ⟨u₀, hu₀B, hu₀⟩ := h
      rw [hB_orbit] at hu₀B ⊢
      obtain ⟨f₀, rfl⟩ := hu₀B
      rintro _ ⟨f, rfl⟩
      have e : actStar (SemidirectProduct.inl (ρ ⟨f, f.2.1⟩)) (gramVec Φ Ψ 437) =
          actH ρ ⟨(f * f₀⁻¹ : setStab act lab Y C), (f * f₀⁻¹).2.1⟩
            (actStar (SemidirectProduct.inl (ρ ⟨f₀, f₀.2.1⟩)) (gramVec Φ Ψ 437)) := by
        change actH ρ ⟨f, f.2.1⟩ _ = actH ρ _ (actH ρ ⟨f₀, f₀.2.1⟩ _)
        rw [← Equiv.Perm.mul_apply, ← map_mul]
        congr 2
        exact Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right])
      rw [e]
      exact actH_mem_rootFix (f * f₀⁻¹) hu₀
    · left
      simp only [not_exists, not_and] at h
      exact h
  by_contra hz
  have hz' : cliqueFixedVec Φ Ψ ∉ Fx := fun h => hz h.1
  have hAcard : A.ncard = 22 := by
    rw [hA, H.cliqueVecs_eq_orbSet hΦ hroot hΨ,
      Set.ncard_image_of_injective _ (H.coordEquiv hΦ Ψ).injective, Cert.ncard_orbSet (by norm_num)]
    rfl
  have hBcard : B.ncard = 22 := by
    rw [hB, H.cliqueShift_eq_orbSet hΦ hroot hΨ,
      Set.ncard_image_of_injective _ (H.coordEquiv hΦ Ψ).injective, Cert.ncard_orbSet (by norm_num)]
    rfl
  have hodd : Odd Fx.ncard := H.odd_ncard_rootFix (ρ := ρ)
  rcases hB_cases with hB0 | hB1
  · have e : Fx = A := by
      refine Set.Subset.antisymm (fun u hu => ?_) hA_sub
      rcases hsub hu with (h | h) | h
      · exact h
      · exact absurd hu (hB0 u h)
      · rw [Set.mem_singleton_iff.1 h] at hu
        exact absurd hu hz'
    rw [e, hAcard] at hodd
    exact absurd hodd (by decide)
  · have e : Fx = A ∪ B := by
      refine Set.Subset.antisymm (fun u hu => ?_) (Set.union_subset hA_sub hB1)
      rcases hsub hu with h | h
      · exact h
      · rw [Set.mem_singleton_iff.1 h] at hu
        exact absurd hu hz'
    rw [e, Set.ncard_union_eq (H.disjoint_cliqueShift hΦ hroot hΨ), hAcard, hBcard] at hodd
    exact absurd hodd (by decide)

include hρ hroot hΨ in
theorem cliqueFixedVec_add_mem_rootVecSet
    {y : Y} (hy : (y : V) ∈ C) :
    cliqueFixedVec Φ Ψ + Ψ (ncommVec lab Y y) ∈ rootVecSet := by
  obtain ⟨q, hq, hqz⟩ := H.cliqueFixedVec_mem_rootVecSet hΦ hρ hroot hΨ
  have hrv : rootVecOf (ρ ⟨lab y, lab_mem_sliceGroup y.2⟩) = Ψ (ncommVec lab Y y) := (hΨ y).symm
  have hc : Commute q (ρ ⟨lab y, lab_mem_sliceGroup y.2⟩) :=
    (bracketL_eq_zero_iff_commute hq (hroot y)).1 (by
      rw [hqz, hrv]
      exact (H.bracketL_cliqueFixedVec_eq_zero_iff hΦ hρ hroot hΨ y).2 hy)
  have hne : rootVecOf q ≠ rootVecOf (ρ ⟨lab y, lab_mem_sliceGroup y.2⟩) := by
    rw [hqz, hrv]
    exact H.cliqueFixedVec_ne hΦ hΨ y
  have hmem := (finrank_range_adL_add_of_commute hq (hroot y) hne hc).2
  rw [hqz, hrv] at hmem
  exact hmem.2 (H.rank_of_mem_cliqueShift hΦ hroot hΨ ⟨_, ⟨y, hy, rfl⟩, rfl⟩ hρ)

include hρ hroot hΨ in
theorem rootFix_eq :
    {u | u ∈ rootVecSet ∧ ∀ r : ptStab act lab Y C,
        actStar (SemidirectProduct.inl (ρ ⟨r, r.2.1⟩)) u = u} =
      cliqueVecs Ψ C ∪ (cliqueFixedVec Φ Ψ + ·) '' cliqueVecs Ψ C ∪ {cliqueFixedVec Φ Ψ} := by
  have hFR : ∀ u, (∀ r : ptStab act lab Y C,
      actStar (SemidirectProduct.inl (ρ ⟨r, r.2.1⟩)) u = u) ↔
        u ∈ Submodule.span (ZMod 2) (cliqueVecs Ψ C) := fun u =>
    Set.ext_iff.1 (H.fixed_ptStab_eq hΦ hroot hΨ) u
  rw [← H.rank22_eq hΦ hρ hroot hΨ]
  ext u
  constructor
  · rintro ⟨hu, hr⟩
    exact ⟨(hFR u).1 hr, finrank_range_adL_of_mem hu⟩
  · intro hu
    refine ⟨?_, (hFR u).2 hu.1⟩
    rw [H.rank22_eq hΦ hρ hroot hΨ] at hu
    rcases hu with (⟨y, hy, rfl⟩ | ⟨_, ⟨y, hy, rfl⟩, rfl⟩) | hu
    · exact psi_mem_rootVecSet hroot hΨ y
    · exact H.cliqueFixedVec_add_mem_rootVecSet hΦ hρ hroot hΨ hy
    · rw [Set.mem_singleton_iff.1 hu]
      exact H.cliqueFixedVec_mem_rootVecSet hΦ hρ hroot hΨ

include hρ hroot hΨ in
theorem commute_cliqueFixedVec_iff
    {q : stdGroup} (hq : IsConj rootInv q)
    (hqz : rootVecOf q = cliqueFixedVec Φ Ψ) (y : Y) :
    Commute q (ρ ⟨lab y, lab_mem_sliceGroup y.2⟩) ↔ (y : V) ∈ C := by
  rw [← bracketL_eq_zero_iff_commute hq (hroot y), hqz,
    show rootVecOf (ρ ⟨lab y, lab_mem_sliceGroup y.2⟩) = Ψ (ncommVec lab Y y) from (hΨ y).symm]
  exact H.bracketL_cliqueFixedVec_eq_zero_iff hΦ hρ hroot hΨ y

include hρ hroot hΨ in
theorem commute_cliqueFixedVec_add_iff
    {y₀ : Y} (hy₀ : (y₀ : V) ∈ C) {q : stdGroup}
    (hq : IsConj rootInv q) (hqz : rootVecOf q = cliqueFixedVec Φ Ψ + Ψ (ncommVec lab Y y₀))
    (y : Y) : Commute q (ρ ⟨lab y, lab_mem_sliceGroup y.2⟩) ↔ (y : V) ∈ C := by
  rw [← bracketL_eq_zero_iff_commute hq (hroot y), hqz,
    show rootVecOf (ρ ⟨lab y, lab_mem_sliceGroup y.2⟩) = Ψ (ncommVec lab Y y) from (hΨ y).symm]
  exact H.bracketL_cliqueFixedVec_add_eq_zero_iff hΦ hρ hroot hΨ hy₀ y

omit hΦ in
theorem ncard_clique : {y : Y | (y : V) ∈ C}.ncard = 22 := by
  rw [← Nat.card_coe_set_eq]
  have e : {y : Y | (y : V) ∈ C} ≃ C :=
    { toFun := fun y => ⟨y.1, y.2⟩
      invFun := fun z => ⟨⟨z, H.clique.1.1 z.2⟩, z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr (e.trans η), Nat.card_eq_fintype_card, Fintype.card_coe, card_X₀]

end FullIntertwinerHyp

namespace IsFischerSlice

theorem clique_fixed_vector_is_ambient_root
    (hS : IsFischerSlice act lab Y) {C : Set V}
    (hC : IsSliceMaxClique lab Y C) [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))]
    {x : V} (hx : x ∈ hexadFiber lab Y C ∅) {η : C ≃ X₀}
    {θ : setStab act lab Y C ⧸ (ptStab act lab Y C).subgroupOf (setStab act lab Y C) ≃*
      CFSG.Blueprint.NativeSporadic.M22}
    (hη : ∀ T : Finset C, Subtype.val '' (T : Set C) ∈ cliqueBlocks lab C ↔
      T.image (fun z => (η z : Fin 24)) ∈ ℬ₀)
    (hθ : ∀ (f : setStab act lab Y C) (z : C),
      (η (setStabPerm act lab Y C f z) : Fin 24) = psiHom (θ f) (η z))
    {φ : Additive (Subgroup.closure (lab '' C)) ≃ₗ[ZMod 2] W₀}
    (hφ : ∀ z : C, φ (Additive.ofMul (cliqueGen z)) = K₀.mkQ (e (η z)))
    {α : setStab act lab Y C →* F₀}
    (hα : ∀ (r : Subgroup.closure (lab '' C)) (f k : setStab act lab Y C),
      (f : S) = r * k → act (k : S) x = x → α f = wF (φ (Additive.ofMul r)) * kF (θ k))
    {Φ : Y ≃ CFSG.Monster.B.Fischer.Y} (hΦ : IsCliqueIntertwiner act lab Y C x η φ α Φ)
    {ρ : sliceGroup lab Y →* stdGroup} (hρ : Function.Injective ρ)
    (hroot : ∀ y : Y, ρ ⟨lab y, lab_mem_sliceGroup y.2⟩ ∈ rootClass)
    {Ψ : NcommQuot lab Y ≃ₗ[ZMod 2] fixedL} (hΨ : ∀ y : Y, Ψ (ncommVec lab Y y) = adjVec ρ y) :
    cliqueFixedVec Φ Ψ ∈ rootVecOf '' {q : stdGroup | IsConj rootInv q} ∧
    (∀ y : Y, (y : V) ∈ C →
      cliqueFixedVec Φ Ψ + Ψ (ncommVec lab Y y) ∈ rootVecOf '' {q : stdGroup | IsConj rootInv q}) ∧
    {u | u ∈ rootVecOf '' {q : stdGroup | IsConj rootInv q} ∧ ∀ r : ptStab act lab Y C,
        actStar (SemidirectProduct.inl (ρ ⟨r, r.2.1⟩)) u = u} =
      cliqueVecs Ψ C ∪ (cliqueFixedVec Φ Ψ + ·) '' cliqueVecs Ψ C ∪ {cliqueFixedVec Φ Ψ} ∧
    Disjoint (cliqueVecs Ψ C) ((cliqueFixedVec Φ Ψ + ·) '' cliqueVecs Ψ C) ∧
    cliqueFixedVec Φ Ψ ∉ cliqueVecs Ψ C ∪ (cliqueFixedVec Φ Ψ + ·) '' cliqueVecs Ψ C ∧
    {u | u ∈ rootVecOf '' {q : stdGroup | IsConj rootInv q} ∧ ∀ r : ptStab act lab Y C,
        actStar (SemidirectProduct.inl (ρ ⟨r, r.2.1⟩)) u = u}.ncard = 45 ∧
    (∀ q : stdGroup, IsConj rootInv q → rootVecOf q = cliqueFixedVec Φ Ψ →
      {y : Y | Commute q (ρ ⟨lab y, lab_mem_sliceGroup y.2⟩)} = {y : Y | (y : V) ∈ C}) ∧
    (∀ y₀ : Y, (y₀ : V) ∈ C → ∀ q : stdGroup, IsConj rootInv q →
      rootVecOf q = cliqueFixedVec Φ Ψ + Ψ (ncommVec lab Y y₀) →
      {y : Y | Commute q (ρ ⟨lab y, lab_mem_sliceGroup y.2⟩)} = {y : Y | (y : V) ∈ C}) ∧
    {y : Y | (y : V) ∈ C}.ncard = 22 := by
  have H := FullIntertwinerHyp.mk hS hC hx hη hθ hφ hα
  refine ⟨H.cliqueFixedVec_mem_rootVecSet hΦ hρ hroot hΨ,
    fun y hy => H.cliqueFixedVec_add_mem_rootVecSet hΦ hρ hroot hΨ hy,
    H.rootFix_eq hΦ hρ hroot hΨ, H.disjoint_cliqueShift hΦ hroot hΨ,
    H.cliqueFixedVec_not_mem hΦ hroot hΨ, ?_, fun q hq hqz => ?_, fun y₀ hy₀ q hq hqz => ?_,
    H.ncard_clique⟩
  · rw [H.rootFix_eq hΦ hρ hroot hΨ]
    exact H.ncard_rank22 hΦ hroot hΨ
  · ext y
    exact H.commute_cliqueFixedVec_iff hΦ hρ hroot hΨ hq hqz y
  · ext y
    exact H.commute_cliqueFixedVec_add_iff hΦ hρ hroot hΨ hy₀ hq hqz y

end IsFischerSlice

end CFSG.Monster.B.TwoA.Fischer
