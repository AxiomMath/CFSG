module

public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.LieType.Ree.LargeReeInvolutionTCentralizer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6ReeResidual
public import CFSG.LocalAnalysis.SectionRank.SuzukiCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport
public import CFSG.Quasithin.SteinbergCDRankOneLeviOddCyclic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic

public section

namespace CFSG.Quasithin.SteinbergCD

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution CFSG.ABGLocalTools
  CFSG.QuasithinUnique.Setup.X6
open CFSG.LieType.Ree.LargeReeCover (pairedTorusHom f4i)

theorem isCyclic_of_mulEquiv_of_sylow_isCyclic {G H : Type*} [Group G] [Group H] {r : ℕ}
    [Fact r.Prime] (e : G ≃* H) (hS : ∀ S : Sylow r H, IsCyclic (S : Subgroup H))
    {P : Subgroup G} (hP : IsPGroup r P) : IsCyclic P := by
  obtain ⟨S, hPS⟩ := (hP.map e.toMonoidHom).exists_le_sylow
  have := hS S
  have : IsCyclic (P.map e.toMonoidHom) := Subgroup.isCyclic_of_le hPS
  have e' : P ≃* P.map e.toMonoidHom := P.equivMapOfInjective e.toMonoidHom e.injective
  exact isCyclic_of_surjective e'.symm.toMonoidHom e'.symm.surjective

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem isCyclic_of_le_rankOneGroupOne
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {r : ℕ}
    [Fact r.Prime] (hr2 : r ≠ 2) {P' : Subgroup (ModGL F4.tag K)}
    (hP'R : P' ≤ rankOneGroupOne K a) (hP' : IsPGroup r P') : IsCyclic P' := by
  have : CharP K 2 := ‹CharP K F4.prime›
  rw [rankOneGroupOne_eq_range hK] at hP'R
  refine isCyclic_of_le_range_of_ker_scalar (largeReeA1Hom K a) (fun g hg => ⟨1, ?_⟩) hr2 hP'R hP'
  rw [largeReeA1Hom_injective (hg.trans (map_one _).symm), one_smul]
  rfl

theorem isCyclic_of_le_rankOneGroupTwo
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {r : ℕ}
    [Fact r.Prime] (hr2 : r ≠ 2) {P' : Subgroup (ModGL F4.tag K)}
    (hP'R : P' ≤ rankOneGroupTwo K a) (hP' : IsPGroup r P') : IsCyclic P' := by
  have h : IsCyclic (P'.subgroupOf (rankOneGroupTwo K a)) :=
    isCyclic_of_mulEquiv_of_sylow_isCyclic ((rankOneEquivSuzuki K a ha hK).trans
        (CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hK))
      (fun S => CFSG.SectionRank.suzuki_sylow_isCyclic a (by omega) hr2 S)
      (hP'.comap_of_injective _ (rankOneGroupTwo K a).subtype_injective)
  have e := subgroupOfEquivOfLe hP'R
  exact isCyclic_of_surjective e.toMonoidHom e.surjective

theorem isCyclic_of_le_reeLocalParabolic_zero
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) {A : Subgroup (ModGL F4.tag K)}
    (hAX : A ≤ F4.reeLocalParabolic K a ⟨0, by decide⟩) (hA : Group.IsPerfect A)
    {P : Subgroup (ModGL F4.tag K)} (hPA : P ≤ A) (hP : IsPGroup r P) : IsCyclic P := by
  have hBX : F4.reeFixedBorel K a ≤ F4.reeLocalParabolic K a ⟨0, by decide⟩ :=
    reeFixedBorel_le_reeGamma_inf_parabolicSubgroup _
  have hHX := (reeFixedTorus_le_reeFixedBorel (t := F4) (K := K) (a := a)).trans hBX
  refine isCyclic_of_le_perfect_of_le_sup
    (Q := F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩) (R := rankOneGroupOne K a)
    (T := rankOneTorusTwo K a) (fun g hg => ?_) ?_ ((rankOneTorusTwo_le hK).trans hHX)
    (fun g hg => ?_) (rankOneTorusTwo_le_normalizer_rankOneGroupOne hK) ?_
    ((isPGroup_reeFixedPosUnipotent ha hK).to_le (reeFixedOrbitComplementUnipotent_le _))
    (complement_zero_inf_rankOneGroupOne hK) hr2
    (fun P' h hP' => isCyclic_of_le_rankOneGroupOne hK hr2 h hP') hAX hA hPA hP
  · obtain ⟨t, ht, s, hs, rfl⟩ := exists_mul_of_mem_reeLocalParabolic_zero hK hg
    exact mul_mem (mem_sup_right ht) (mem_sup_left hs)
  · rw [rankOneGroupOne, closure_le]
    rintro g ((hg | hg) | rfl)
    · exact hBX (reeFixedPosUnipotent_le_reeFixedBorel (reeFixedOrbitUnipotent_le _ hg))
    · exact hHX (rankOneTorusOne_le hK hg)
    · rw [SetLike.mem_coe, ← reeParabolic_singleton]
      exact F4.canonicalRep_mem_reeParabolic K a (Set.mem_singleton _)
  · obtain ⟨t, ht, s, hs, rfl⟩ := exists_mul_of_mem_reeLocalParabolic_zero hK hg
    exact mul_mem (reeFixedTorus_le_normalizer_complement _ (rankOneTorusTwo_le hK ht))
      (sup_le le_normalizer (rankOneGroupOne_le_normalizer_complement hK) hs)
  · rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    exact (rankOne_commute_pairedTorusHom 1 2 1 2 u v).eq

theorem isCyclic_of_le_reeLocalParabolic_one
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) {A : Subgroup (ModGL F4.tag K)}
    (hAX : A ≤ F4.reeLocalParabolic K a ⟨1, by decide⟩) (hA : Group.IsPerfect A)
    {P : Subgroup (ModGL F4.tag K)} (hPA : P ≤ A) (hP : IsPGroup r P) : IsCyclic P := by
  have hBX : F4.reeFixedBorel K a ≤ F4.reeLocalParabolic K a ⟨1, by decide⟩ :=
    reeFixedBorel_le_reeGamma_inf_parabolicSubgroup _
  have hHX := (reeFixedTorus_le_reeFixedBorel (t := F4) (K := K) (a := a)).trans hBX
  refine isCyclic_of_le_perfect_of_le_sup
    (Q := F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩) (R := rankOneGroupTwo K a)
    (T := rankOneTorusOne K a) (fun g hg => ?_) ?_ ((rankOneTorusOne_le hK).trans hHX)
    (fun g hg => ?_) (rankOneTorusOne_le_normalizer_rankOneGroupTwo hK) ?_
    ((isPGroup_reeFixedPosUnipotent ha hK).to_le (reeFixedOrbitComplementUnipotent_le _))
    (complement_inf_rankOneGroupTwo ha hK) hr2
    (fun P' h hP' => isCyclic_of_le_rankOneGroupTwo ha hK hr2 h hP') hAX hA hPA hP
  · obtain ⟨t, ht, s, hs, rfl⟩ := exists_mul_of_mem_reeLocalParabolic hK hg
    exact mul_mem (mem_sup_right ht) (mem_sup_left hs)
  · rw [rankOneGroupTwo, closure_le]
    rintro g ((hg | hg) | rfl)
    · exact hBX (reeFixedPosUnipotent_le_reeFixedBorel (reeFixedOrbitUnipotent_le _ hg))
    · exact hHX (rankOneTorusTwo_le hK hg)
    · rw [SetLike.mem_coe, ← reeParabolic_singleton]
      exact F4.canonicalRep_mem_reeParabolic K a (Set.mem_singleton _)
  · obtain ⟨t, ht, s, hs, rfl⟩ := exists_mul_of_mem_reeLocalParabolic hK hg
    exact mul_mem (reeFixedTorus_le_normalizer_complement _ (rankOneTorusOne_le hK ht))
      (centralizerZ_le_normalizer hK hs)
  · rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    exact (rankOne_commute_pairedTorusHom 0 3 0 3 u v).eq

theorem large_Ree_proper_sylow_overgroup_perfect_odd_cyclic
    (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {T A : Subgroup (ModGL F4.tag K)}
    (hT : IsSylowOf 2 T (F4.reeGamma K a)) (hA : Group.IsPerfect A)
    (hAT : A ⊔ T < F4.reeGamma K a) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {P : Subgroup (ModGL F4.tag K)} (hPA : P ≤ A) (hP : IsPGroup r P) : IsCyclic P := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_modGL (τ := F4.tag) (K := K)
  have hU : IsSylowOf 2 (F4.reeFixedPosUnipotent K a) (F4.reeGamma K a) := by
    obtain ⟨S, hS⟩ :=
      (CFSG.ComponentClassification.UnbalancedCatalog.large_Ree_Sylow_center a ha K hK).1
    exact ⟨S, by rw [hS, subgroupOf_map_subtype, inf_eq_left.2 reeFixedPosUnipotent_le_reeGamma]⟩
  obtain ⟨g, hgΓ, hgT⟩ := hU.exists_mem_conj hT
  set c := (MulAut.conj g⁻¹).toMonoidHom with hc
  have hcinj : Function.Injective c := (MulAut.conj g⁻¹).injective
  have hTU : T.map c = F4.reeFixedPosUnipotent K a := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h := (hgT y).1 hy
      rwa [hc, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    · intro hx
      refine ⟨g * x * g⁻¹, (hgT _).2 ?_, ?_⟩
      · rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group]
      · rw [hc, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        group
  have hΓ : (F4.reeGamma K a).map c = F4.reeGamma K a :=
    map_conj_eq_of_mem_normalizer (le_normalizer (inv_mem hgΓ))
  have hlt : A.map c ⊔ F4.reeFixedPosUnipotent K a < F4.reeGamma K a := by
    rw [← hTU, ← Subgroup.map_sup, ← hΓ]
    exact (map_lt_map_iff_of_injective hcinj).2 hAT
  obtain ⟨J, hJ, hMJ, -⟩ := (large_Ree_positive_root_overgroup_parabolic_containment hK
    hlt.le le_sup_right).2.2 hlt.ne
  obtain ⟨j, hj⟩ : ∃ j, j ∉ J := by
    by_contra h
    push Not at h
    exact hJ (Set.eq_univ_of_forall h)
  have key : ∀ j : Fin F4.fixedOrbitCount, ∃ k, ∀ i, i ≠ j → i = k := by decide
  obtain ⟨k, hk⟩ := key j
  have hJk : J ⊆ {k} := fun i hi => hk i fun h => hj (h ▸ hi)
  have hAk : A.map c ≤ F4.reeLocalParabolic K a k := by
    rw [← reeParabolic_singleton]
    exact le_sup_left.trans
      (hMJ.trans (sup_le_sup_left (Subgroup.closure_mono (Set.image_mono hJk)) _))
  have hA' : Group.IsPerfect (A.map c) := by
    rw [isPerfect_iff, ← map_commutator, isPerfect_iff.1 hA]
  have hP' : IsCyclic (P.map c) := by
    have hPA' : P.map c ≤ A.map c := map_mono hPA
    have hPr : IsPGroup r (P.map c) := hP.map c
    match k, hAk with
    | ⟨0, _⟩, hAk => exact isCyclic_of_le_reeLocalParabolic_zero ha hK hr2 hAk hA' hPA' hPr
    | ⟨1, _⟩, hAk => exact isCyclic_of_le_reeLocalParabolic_one ha hK hr2 hAk hA' hPA' hPr
  have e : P ≃* P.map c := P.equivMapOfInjective c hcinj
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

end CFSG.Quasithin.SteinbergCD
