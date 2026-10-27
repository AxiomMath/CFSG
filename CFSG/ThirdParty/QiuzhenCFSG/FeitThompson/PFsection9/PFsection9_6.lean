module

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_3
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Remaining
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.Basic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped IsMulCommutative commutatorElement

namespace CFSG.Section9

universe v
universe w
universe u

private theorem H0_subgroupOf_MF_isInvariant_under_U_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 : Subgroup G) [Subgroup.Normalizes U MF] :
    MF ≤ M →
      U ≤ M →
        (H0.subgroupOf M).Normal →
          U ≤ Subgroup.normalizer (MF : Set G) →
            IsInvariant U MF (H0.subgroupOf MF) := by
  exact subgroupOf_MF_isInvariant_of_subgroupOf_M_normal_sec9 M MF U H0

private def intermediateQuotientSubgroup_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF H0 : Subgroup G) [hnormal : (H0.subgroupOf MF).Normal]
    (N : Subgroup M)
    (hMF_le_M : MF ≤ M) : Subgroup (MF ⧸ H0.subgroupOf MF) :=
  (N.comap (Subgroup.inclusion hMF_le_M)).map (QuotientGroup.mk' (H0.subgroupOf MF))

public theorem quotientSubgroupNormalizedBy_of_isInvariant_sec9
    {G : Type u} [Group G] [Finite G]
    (MF H0 A : Subgroup G)
    [Subgroup.Normalizes A MF]
    [hnormal : (H0.subgroupOf MF).Normal]
    (hH0_inv : IsInvariant A MF (H0.subgroupOf MF))
    (Q : Subgroup (MF ⧸ H0.subgroupOf MF))
    (hQ :
      letI : MulAction.QuotientAction A (H0.subgroupOf MF) :=
        quotientAction_of_isInvariant (A := A) (G := MF) (H0.subgroupOf MF) hH0_inv
      letI : MulDistribMulAction A (MF ⧸ H0.subgroupOf MF) :=
        quotientMulDistribMulAction (A := A) (G := MF) (H0.subgroupOf MF) hH0_inv
      IsInvariant A (MF ⧸ H0.subgroupOf MF) Q) :
    quotientSubgroupNormalizedBy MF H0 A Q := by
  classical
  letI : MulAction.QuotientAction A (H0.subgroupOf MF) :=
    quotientAction_of_isInvariant (A := A) (G := MF) (H0.subgroupOf MF) hH0_inv
  letI : MulDistribMulAction A (MF ⧸ H0.subgroupOf MF) :=
    quotientMulDistribMulAction (A := A) (G := MF) (H0.subgroupOf MF) hH0_inv
  intro a
  let hconjMF : ∀ h : MF, (a : G)⁻¹ * (h : G) * (a : G) ∈ MF := by
    intro h
    have hsmulG :
        (((a⁻¹ : A) • h : MF) : G) = (a : G)⁻¹ * (h : G) * (a : G) := by
      simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
    exact hsmulG ▸ (((a⁻¹ : A) • h : MF).property)
  refine ⟨hconjMF, ?_⟩
  let action : MulAut (MF ⧸ H0.subgroupOf MF) :=
    MulDistribMulAction.toMulAut A (MF ⧸ H0.subgroupOf MF) (a⁻¹ : A)
  refine ⟨action, ?_, ?_⟩
  · intro h
    have hsmul_eq :
        ((a⁻¹ : A) • h : MF) =
          ⟨(a : G)⁻¹ * (h : G) * (a : G), hconjMF h⟩ := by
      apply Subtype.ext
      simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
    change action (QuotientGroup.mk' (H0.subgroupOf MF) h) =
      QuotientGroup.mk' (H0.subgroupOf MF)
        ⟨(a : G)⁻¹ * (h : G) * (a : G), hconjMF h⟩
    change (a⁻¹ : A) • QuotientGroup.mk' (H0.subgroupOf MF) h =
      QuotientGroup.mk' (H0.subgroupOf MF)
        ⟨(a : G)⁻¹ * (h : G) * (a : G), hconjMF h⟩
    have hsmul_mk :
        (a⁻¹ : A) • QuotientGroup.mk' (H0.subgroupOf MF) h =
          QuotientGroup.mk' (H0.subgroupOf MF) ((a⁻¹ : A) • h) := by
      simpa only [QuotientGroup.mk'_apply] using
        (MulAction.Quotient.smul_mk (H := H0.subgroupOf MF) (a⁻¹ : A) h)
    rw [hsmul_mk, hsmul_eq]
  · ext x
    constructor
    · intro hx
      refine ⟨action.symm x, ?_, ?_⟩
      · have hx' : (a⁻¹ : A) • (action.symm x) ∈ Q := by
          change action (action.symm x) ∈ Q
          simpa using hx
        exact (IsInvariant.invariant (A := A) (G := MF ⧸ H0.subgroupOf MF)
          (H := Q) (a⁻¹ : A) (action.symm x)).2 hx'
      · exact action.apply_symm_apply x
    · intro hx
      rcases hx with ⟨y, hy, rfl⟩
      change action y ∈ Q
      change (a⁻¹ : A) • y ∈ Q
      exact (IsInvariant.invariant (A := A) (G := MF ⧸ H0.subgroupOf MF)
        (H := Q) (a⁻¹ : A) y).1 hy

public theorem isInvariant_of_quotientSubgroupNormalizedBy_sec9
    {G : Type u} [Group G] [Finite G]
    (MF H0 A : Subgroup G)
    [Subgroup.Normalizes A MF]
    [hnormal : (H0.subgroupOf MF).Normal]
    (hH0_inv : IsInvariant A MF (H0.subgroupOf MF))
    (Q : Subgroup (MF ⧸ H0.subgroupOf MF)) :
    quotientSubgroupNormalizedBy MF H0 A Q →
      letI : MulAction.QuotientAction A (H0.subgroupOf MF) :=
        quotientAction_of_isInvariant (A := A) (G := MF) (H0.subgroupOf MF) hH0_inv
      letI : MulDistribMulAction A (MF ⧸ H0.subgroupOf MF) :=
        quotientMulDistribMulAction (A := A) (G := MF) (H0.subgroupOf MF) hH0_inv
      IsInvariant A (MF ⧸ H0.subgroupOf MF) Q := by
  classical
  intro hQnorm
  let H0MF : Subgroup MF := H0.subgroupOf MF
  haveI : H0MF.Normal := hnormal
  letI : MulAction.QuotientAction A H0MF :=
    quotientAction_of_isInvariant (A := A) (G := MF) H0MF hH0_inv
  letI : MulDistribMulAction A (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := A) (G := MF) H0MF hH0_inv
  have hforward : ∀ (a : A) (x : MF ⧸ H0MF), x ∈ Q → a • x ∈ Q := by
    intro a x hx
    rcases hQnorm (a⁻¹) with ⟨hconjMF, action, haction, hmap⟩
    have hx_action : action x ∈ Q := by
      have hx_map : action.toMonoidHom x ∈ Q.map action.toMonoidHom :=
        Subgroup.mem_map_of_mem action.toMonoidHom hx
      rw [hmap]
      simpa using hx_map
    have hsmul_action : a • x = action x := by
      rcases QuotientGroup.mk'_surjective H0MF x with ⟨h, rfl⟩
      rw [haction h]
      have hsmul_mk :
          a • QuotientGroup.mk' H0MF h =
            QuotientGroup.mk' H0MF (a • h) := by
        simpa only [QuotientGroup.mk'_apply] using
          (MulAction.Quotient.smul_mk (H := H0MF) a h)
      have hsmul_eq :
          (a • h : MF) =
            ⟨((a⁻¹ : A) : G)⁻¹ * (h : G) * ((a⁻¹ : A) : G),
              hconjMF h⟩ := by
        apply Subtype.ext
        simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc]
      rw [hsmul_mk, hsmul_eq]
    simpa [hsmul_action] using hx_action
  constructor
  intro a x
  constructor
  · exact hforward a x
  · intro hx
    have hx' : (a⁻¹ : A) • (a • x) ∈ Q := hforward a⁻¹ (a • x) hx
    simpa using hx'

private theorem quotient_isInvariant_sup_of_isInvariant_left_right_sec9
    {G : Type u} [Group G] [Finite G]
    (MF U W1 H0 : Subgroup G)
    [Subgroup.Normalizes U MF] [Subgroup.Normalizes W1 MF]
    [Subgroup.Normalizes (U ⊔ W1 : Subgroup G) MF]
    [hnormal : (H0.subgroupOf MF).Normal]
    (hH0_inv_U : IsInvariant U MF (H0.subgroupOf MF))
    (hH0_inv_W1 : IsInvariant W1 MF (H0.subgroupOf MF))
    (hH0_inv_UW1 : IsInvariant (U ⊔ W1 : Subgroup G) MF (H0.subgroupOf MF))
    (Q : Subgroup (MF ⧸ H0.subgroupOf MF)) :
    (letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
      quotientMulDistribMulAction (A := U) (G := MF)
        (H0.subgroupOf MF) hH0_inv_U;
      IsInvariant U (MF ⧸ H0.subgroupOf MF) Q) →
    (letI : MulDistribMulAction W1 (MF ⧸ H0.subgroupOf MF) :=
      quotientMulDistribMulAction (A := W1) (G := MF)
        (H0.subgroupOf MF) hH0_inv_W1;
      IsInvariant W1 (MF ⧸ H0.subgroupOf MF) Q) →
    (letI : MulDistribMulAction (U ⊔ W1 : Subgroup G) (MF ⧸ H0.subgroupOf MF) :=
      quotientMulDistribMulAction (A := (U ⊔ W1 : Subgroup G)) (G := MF)
        (H0.subgroupOf MF) hH0_inv_UW1;
      IsInvariant (U ⊔ W1 : Subgroup G) (MF ⧸ H0.subgroupOf MF) Q) := by
  classical
  intro hQ_inv_U hQ_inv_W1
  let H0MF : Subgroup MF := H0.subgroupOf MF
  let UW1 : Subgroup G := U ⊔ W1
  haveI : H0MF.Normal := hnormal
  letI : MulDistribMulAction U (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := U) (G := MF) H0MF hH0_inv_U
  letI : MulDistribMulAction W1 (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := W1) (G := MF) H0MF hH0_inv_W1
  letI : MulDistribMulAction UW1 (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := UW1) (G := MF) H0MF (by
      simpa [UW1] using hH0_inv_UW1)
  have hpreserve_closure :
      ∀ g : G, g ∈ Subgroup.closure ((U : Set G) ∪ (W1 : Set G)) →
        ∀ hgUW1 : g ∈ UW1, ∀ x : MF ⧸ H0MF,
          x ∈ Q ↔ (⟨g, hgUW1⟩ : UW1) • x ∈ Q := by
    intro g hg
    refine Subgroup.closure_induction
      (p := fun y _ =>
        ∀ hyUW1 : y ∈ UW1, ∀ x : MF ⧸ H0MF,
          x ∈ Q ↔ (⟨y, hyUW1⟩ : UW1) • x ∈ Q)
      ?mem ?one ?mul ?inv hg
    · intro y hy hyUW1 x
      rcases hy with hyU | hyW1
      · have hiff :=
          IsInvariant.invariant (A := U) (G := MF ⧸ H0MF) (H := Q)
            (a := ⟨y, hyU⟩) x
        change x ∈ Q ↔ (⟨y, hyUW1⟩ : UW1) • x ∈ Q at hiff
        exact hiff
      · have hiff :=
          IsInvariant.invariant (A := W1) (G := MF ⧸ H0MF) (H := Q)
            (a := ⟨y, hyW1⟩) x
        change x ∈ Q ↔ (⟨y, hyUW1⟩ : UW1) • x ∈ Q at hiff
        exact hiff
    · intro h1 x
      have hone : (⟨1, h1⟩ : UW1) = 1 := by
        ext
        rfl
      simp [hone]
    · intro x y hx hy hx_pres hy_pres hxyUW1 z
      have hxUW1 : x ∈ UW1 := by
        simpa [UW1, Subgroup.sup_eq_closure] using hx
      have hyUW1 : y ∈ UW1 := by
        simpa [UW1, Subgroup.sup_eq_closure] using hy
      calc
        z ∈ Q ↔ (⟨y, hyUW1⟩ : UW1) • z ∈ Q := hy_pres hyUW1 z
        _ ↔ (⟨x, hxUW1⟩ : UW1) • ((⟨y, hyUW1⟩ : UW1) • z) ∈ Q :=
          hx_pres hxUW1 ((⟨y, hyUW1⟩ : UW1) • z)
        _ ↔ (⟨x * y, hxyUW1⟩ : UW1) • z ∈ Q := by
          have hmul_eq : (⟨x, hxUW1⟩ : UW1) * ⟨y, hyUW1⟩ =
              ⟨x * y, hxyUW1⟩ := by
            ext
            rfl
          rw [← mul_smul, hmul_eq]
    · intro x hx hx_pres hxinvUW1 z
      have hxUW1 : x ∈ UW1 := by
        simpa [UW1, Subgroup.sup_eq_closure] using hx
      calc
        z ∈ Q ↔ (⟨x, hxUW1⟩ : UW1) • ((⟨x⁻¹, hxinvUW1⟩ : UW1) • z) ∈ Q := by
          have hmul_one : (⟨x, hxUW1⟩ : UW1) * ⟨x⁻¹, hxinvUW1⟩ = 1 := by
            ext
            simp
          have haction :
              (⟨x, hxUW1⟩ : UW1) • ((⟨x⁻¹, hxinvUW1⟩ : UW1) • z) = z := by
            rw [← mul_smul, hmul_one, one_smul]
          simp [haction]
        _ ↔ (⟨x⁻¹, hxinvUW1⟩ : UW1) • z ∈ Q :=
          (hx_pres hxUW1 ((⟨x⁻¹, hxinvUW1⟩ : UW1) • z)).symm
  constructor
  intro a x
  have ha_closure : (a : G) ∈ Subgroup.closure ((U : Set G) ∪ (W1 : Set G)) := by
    simpa [UW1, Subgroup.sup_eq_closure] using a.property
  exact hpreserve_closure (a : G) ha_closure a.property x

private theorem intermediateQuotientSubgroup_normalizedBy_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF A H0 : Subgroup G)
    [Subgroup.Normalizes A MF]
    [hnormal : (H0.subgroupOf MF).Normal]
    (hMF_le_M : MF ≤ M)
    (hA_le_M : A ≤ M)
    (hH0_normal_M : (H0.subgroupOf M).Normal)
    (N : Subgroup M)
    (hN_normal : N.Normal) :
    quotientSubgroupNormalizedBy MF H0 A
      (intermediateQuotientSubgroup_sec9 M MF H0 N hMF_le_M) := by
  classical
  have hH0_inv_A : IsInvariant A MF (H0.subgroupOf MF) :=
    H0_subgroupOf_MF_isInvariant_under_U_sec9 M MF A H0
      hMF_le_M hA_le_M hH0_normal_M
      (show A ≤ Subgroup.normalizer (MF : Set G) from
        Subgroup.Normalizes.le_normalizer)
  let H0MF : Subgroup MF := H0.subgroupOf MF
  haveI : H0MF.Normal := hnormal
  letI : MulAction.QuotientAction A H0MF :=
    quotientAction_of_isInvariant (A := A) (G := MF) H0MF hH0_inv_A
  letI : MulDistribMulAction A (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := A) (G := MF) H0MF hH0_inv_A
  let NMF : Subgroup MF := N.comap (Subgroup.inclusion hMF_le_M)
  let Q : Subgroup (MF ⧸ H0MF) := NMF.map (QuotientGroup.mk' H0MF)
  have hforwardMF : ∀ (a : A) (x : MF), x ∈ NMF → a • x ∈ NMF := by
    intro a x hx
    change (⟨((a • x : MF) : G), hMF_le_M (a • x).property⟩ : M) ∈ N
    have hxN : (⟨(x : G), hMF_le_M x.property⟩ : M) ∈ N := by
      simpa [NMF, Subgroup.mem_comap, Subgroup.inclusion] using hx
    let aM : M := ⟨(a : G), hA_le_M a.property⟩
    let xM : M := ⟨(x : G), hMF_le_M x.property⟩
    have hxM : xM ∈ N := by simpa [xM] using hxN
    have hconjN : aM * xM * aM⁻¹ ∈ N :=
      hN_normal.conj_mem xM hxM aM
    have hsmulG : ((a • x : MF) : G) = (a : G) * (x : G) * (a : G)⁻¹ := by
      simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
    have hsmulM :
        (⟨((a • x : MF) : G), hMF_le_M (a • x).property⟩ : M) =
          aM * xM * aM⁻¹ := by
      apply M.subtype_injective
      simp [aM, xM, hsmulG]
    rw [hsmulM]
    exact hconjN
  have hforwardQ : ∀ (a : A) {x : MF ⧸ H0MF}, x ∈ Q → a • x ∈ Q := by
    intro a x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    refine Subgroup.mem_map.mpr ⟨a • y, hforwardMF a y hy, ?_⟩
    exact (MulAction.Quotient.smul_mk (H := H0MF) a y).symm
  have hQinv : IsInvariant A (MF ⧸ H0MF) Q := by
    constructor
    intro a x
    constructor
    · exact hforwardQ a
    · intro hx
      have hx' : (a⁻¹ : A) • (a • x) ∈ Q := hforwardQ a⁻¹ hx
      simpa using hx'
  simpa [Q, NMF, H0MF, intermediateQuotientSubgroup_sec9] using
    quotientSubgroupNormalizedBy_of_isInvariant_sec9 MF H0 A hH0_inv_A Q hQinv

private theorem quotientCentralizedBy_of_quotient_U_fixed_top_sec9
    {G : Type u} [Group G] [Finite G]
    (MF U H0 : Subgroup G) [Subgroup.Normalizes U MF]
    (hH0_inv : IsInvariant U MF (H0.subgroupOf MF))
    (hnormal : (H0.subgroupOf MF).Normal) :
    (letI : (H0.subgroupOf MF).Normal := hnormal;
      letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
        quotientMulDistribMulAction (A := U) (G := MF) (H0.subgroupOf MF) hH0_inv;
      fixedPointSubgroup U (MF ⧸ H0.subgroupOf MF) = ⊤) →
      quotientCentralizedBy MF H0 U := by
  classical
  intro htop u huU h hhMF
  let H0MF : Subgroup MF := H0.subgroupOf MF
  haveI : H0MF.Normal := hnormal
  letI : MulDistribMulAction U (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := U) (G := MF) H0MF hH0_inv
  let uU : U := ⟨u, huU⟩
  let hMF : MF := ⟨h, hhMF⟩
  have htop' : fixedPointSubgroup U (MF ⧸ H0MF) = ⊤ := by
    simpa [H0MF] using htop
  have hq_fixed : QuotientGroup.mk' H0MF hMF ∈
      fixedPointSubgroup U (MF ⧸ H0MF) := by
    rw [htop']
    exact Subgroup.mem_top _
  have hfixed_eq : uU • QuotientGroup.mk' H0MF hMF = QuotientGroup.mk' H0MF hMF :=
    hq_fixed uU
  have hq : QuotientGroup.mk' H0MF (uU • hMF) = QuotientGroup.mk' H0MF hMF := by
    simpa using hfixed_eq
  have hcommH0MF : ((uU • hMF : MF) / hMF) ∈ H0MF :=
    QuotientGroup.eq_iff_div_mem.mp hq
  have hval : ((((uU • hMF : MF) / hMF : MF) : G) = ⁅u, h⁆) := by
    simp [hMF, uU, div_eq_mul_inv, commutatorElement_def,
      Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc]
  simpa [H0MF, Subgroup.mem_subgroupOf, hval] using hcommH0MF

private theorem quotient_U_fixed_ne_top_of_not_quotientCentralizedBy_sec9
    {G : Type u} [Group G] [Finite G]
    (MF U H0 : Subgroup G) [Subgroup.Normalizes U MF]
    (hH0_inv : IsInvariant U MF (H0.subgroupOf MF))
    (hnormal : (H0.subgroupOf MF).Normal) :
    ¬ quotientCentralizedBy MF H0 U →
      (letI : (H0.subgroupOf MF).Normal := hnormal;
        letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
          quotientMulDistribMulAction (A := U) (G := MF) (H0.subgroupOf MF) hH0_inv;
        fixedPointSubgroup U (MF ⧸ H0.subgroupOf MF) ≠ ⊤) := by
  intro hnon htop
  exact hnon
    (quotientCentralizedBy_of_quotient_U_fixed_top_sec9 MF U H0
      hH0_inv hnormal htop)

public theorem quotient_W1_fixedPointSubgroup_card_eq_barW2_subtype_sec9
    {G : Type u} [Group G] [Finite G]
    (MF W1 H0 : Subgroup G) [Subgroup.Normalizes W1 MF]
    (hH0_inv : IsInvariant W1 MF (H0.subgroupOf MF))
    (hnormal : (H0.subgroupOf MF).Normal) :
    (letI : (H0.subgroupOf MF).Normal := hnormal;
      letI : MulDistribMulAction W1 (MF ⧸ H0.subgroupOf MF) :=
        quotientMulDistribMulAction (A := W1) (G := MF) (H0.subgroupOf MF) hH0_inv;
      Nat.card {x : MF ⧸ H0.subgroupOf MF //
        ∀ h : MF, QuotientGroup.mk' (H0.subgroupOf MF) h = x →
          ∀ w : G, w ∈ W1 → ⁅w, (h : G)⁆ ∈ H0} =
        Nat.card (fixedPointSubgroup W1 (MF ⧸ H0.subgroupOf MF))) := by
  classical
  let H0MF : Subgroup MF := H0.subgroupOf MF
  haveI : H0MF.Normal := hnormal
  letI : MulDistribMulAction W1 (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := W1) (G := MF) H0MF hH0_inv
  have hiff : ∀ x : MF ⧸ H0MF,
      (∀ h : MF, QuotientGroup.mk' H0MF h = x →
        ∀ w : G, w ∈ W1 → ⁅w, (h : G)⁆ ∈ H0) ↔
        x ∈ fixedPointSubgroup W1 (MF ⧸ H0MF) := by
    intro x
    constructor
    · intro hx
      change ∀ w : W1, w • x = x
      intro w
      revert hx
      refine QuotientGroup.induction_on x ?_
      intro h hx
      have hcommH0 : ⁅(w : G), (h : G)⁆ ∈ H0 :=
        hx h rfl (w : G) w.property
      apply QuotientGroup.eq_iff_div_mem.mpr
      have hcommH0MF : ((w • h : MF) / h) ∈ H0MF := by
        have hval : ((((w • h : MF) / h : MF) : G) = ⁅(w : G), (h : G)⁆) := by
          simp [div_eq_mul_inv, commutatorElement_def,
            Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc]
        simpa [H0MF, Subgroup.mem_subgroupOf, hval] using hcommH0
      simpa [div_eq_mul_inv] using hcommH0MF
    · intro hx h hh w hw
      let wW1 : W1 := ⟨w, hw⟩
      have hfixed : wW1 • x = x := by
        change ∀ w : W1, w • x = x at hx
        exact hx wW1
      have hfixed_mk :
          wW1 • QuotientGroup.mk' H0MF h = QuotientGroup.mk' H0MF h := by
        simpa [hh] using hfixed
      have hq : QuotientGroup.mk' H0MF (wW1 • h) = QuotientGroup.mk' H0MF h := by
        simpa using hfixed_mk
      have hcommH0MF : ((wW1 • h : MF) / h) ∈ H0MF :=
        QuotientGroup.eq_iff_div_mem.mp hq
      have hval : ((((wW1 • h : MF) / h : MF) : G) = ⁅w, (h : G)⁆) := by
        simp [wW1, div_eq_mul_inv, commutatorElement_def,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc]
      simpa [H0MF, Subgroup.mem_subgroupOf, hval] using hcommH0MF
  simpa [H0MF] using (Nat.card_congr (Equiv.subtypeEquivRight hiff))

private theorem quotient_U_fixedPointSubgroup_subgroupOf_eq_bot_sec9
    {G : Type u} [Group G] [Finite G]
    (MF U W1 H0 : Subgroup G)
    [Subgroup.Normalizes U MF] [Subgroup.Normalizes (U ⊔ W1 : Subgroup G) MF]
    (hnormal : (H0.subgroupOf MF).Normal)
    (hH0_inv_U : IsInvariant U MF (H0.subgroupOf MF))
    (hH0_inv_UW1 : IsInvariant (U ⊔ W1 : Subgroup G) MF (H0.subgroupOf MF)) :
    (letI : (H0.subgroupOf MF).Normal := hnormal;
      letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
        quotientMulDistribMulAction (A := U) (G := MF)
          (H0.subgroupOf MF) hH0_inv_U;
      fixedPointSubgroup U (MF ⧸ H0.subgroupOf MF) = ⊥) →
    (letI : (H0.subgroupOf MF).Normal := hnormal;
      letI : MulDistribMulAction (U ⊔ W1 : Subgroup G) (MF ⧸ H0.subgroupOf MF) :=
        quotientMulDistribMulAction (A := (U ⊔ W1 : Subgroup G)) (G := MF)
          (H0.subgroupOf MF) hH0_inv_UW1;
      fixedPointSubgroup (↥(U.subgroupOf (U ⊔ W1 : Subgroup G)))
        (MF ⧸ H0.subgroupOf MF) = ⊥) := by
  classical
  intro hUbot
  let H0MF : Subgroup MF := H0.subgroupOf MF
  haveI : H0MF.Normal := hnormal
  letI : MulDistribMulAction U (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := U) (G := MF) H0MF hH0_inv_U
  letI : MulDistribMulAction (U ⊔ W1 : Subgroup G) (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := (U ⊔ W1 : Subgroup G)) (G := MF)
      H0MF hH0_inv_UW1
  apply le_antisymm
  · intro x hx
    have hxU : x ∈ fixedPointSubgroup U (MF ⧸ H0MF) := by
      change ∀ u : U, u • x = x
      intro u
      have hsub :
          (⟨(u : G), (le_sup_left : U ≤ U ⊔ W1) u.property⟩ :
            (U ⊔ W1 : Subgroup G)) • x = x := by
        exact hx ⟨⟨(u : G), (le_sup_left : U ≤ U ⊔ W1) u.property⟩,
          by
            change (u : G) ∈ U
            exact u.property⟩
      change u • x = x at hsub
      exact hsub
    have hxbot : x ∈ (⊥ : Subgroup (MF ⧸ H0MF)) := by
      rw [← hUbot]
      exact hxU
    simpa using hxbot
  · exact bot_le

private theorem quotient_W1_subgroupOf_fixedPointSubgroup_card_eq_sec9
    {G : Type u} [Group G] [Finite G]
    (MF U W1 H0 : Subgroup G)
    [Subgroup.Normalizes W1 MF] [Subgroup.Normalizes (U ⊔ W1 : Subgroup G) MF]
    (hnormal : (H0.subgroupOf MF).Normal)
    (hH0_inv_W1 : IsInvariant W1 MF (H0.subgroupOf MF))
    (hH0_inv_UW1 : IsInvariant (U ⊔ W1 : Subgroup G) MF (H0.subgroupOf MF)) :
    (letI : (H0.subgroupOf MF).Normal := hnormal;
      letI : MulDistribMulAction (U ⊔ W1 : Subgroup G) (MF ⧸ H0.subgroupOf MF) :=
        quotientMulDistribMulAction (A := (U ⊔ W1 : Subgroup G)) (G := MF)
          (H0.subgroupOf MF) hH0_inv_UW1;
      Nat.card (fixedPointSubgroup (↥(W1.subgroupOf (U ⊔ W1 : Subgroup G)))
        (MF ⧸ H0.subgroupOf MF))) =
    (letI : (H0.subgroupOf MF).Normal := hnormal;
      letI : MulDistribMulAction W1 (MF ⧸ H0.subgroupOf MF) :=
        quotientMulDistribMulAction (A := W1) (G := MF)
          (H0.subgroupOf MF) hH0_inv_W1;
      Nat.card (fixedPointSubgroup W1 (MF ⧸ H0.subgroupOf MF))) := by
  classical
  let H0MF : Subgroup MF := H0.subgroupOf MF
  haveI : H0MF.Normal := hnormal
  letI : MulDistribMulAction (U ⊔ W1 : Subgroup G) (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := (U ⊔ W1 : Subgroup G)) (G := MF)
      H0MF hH0_inv_UW1
  letI : MulDistribMulAction W1 (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := W1) (G := MF) H0MF hH0_inv_W1
  change
    Nat.card (fixedPointSubgroup (↥(W1.subgroupOf (U ⊔ W1 : Subgroup G)))
      (MF ⧸ H0MF)) =
    Nat.card (fixedPointSubgroup W1 (MF ⧸ H0MF))
  have heq :
      fixedPointSubgroup (↥(W1.subgroupOf (U ⊔ W1 : Subgroup G)))
        (MF ⧸ H0MF) =
      fixedPointSubgroup W1 (MF ⧸ H0MF) := by
    ext x
    constructor
    · intro hx
      change ∀ w : W1, w • x = x
      intro w
      have hsub :
          (⟨(w : G), (le_sup_right : W1 ≤ U ⊔ W1) w.property⟩ :
            (U ⊔ W1 : Subgroup G)) • x = x := by
        exact hx ⟨⟨(w : G), (le_sup_right : W1 ≤ U ⊔ W1) w.property⟩,
          by
            change (w : G) ∈ W1
            exact w.property⟩
      change w • x = x at hsub
      exact hsub
    · intro hx
      change ∀ w : W1.subgroupOf (U ⊔ W1 : Subgroup G), w • x = x
      intro w
      have hwW1 : ((w : (U ⊔ W1 : Subgroup G)) : G) ∈ W1 := w.property
      let wW1 : W1 := ⟨((w : (U ⊔ W1 : Subgroup G)) : G), hwW1⟩
      have hfix : wW1 • x = x := by
        change ∀ w : W1, w • x = x at hx
        exact hx wW1
      change w • x = x at hfix
      exact hfix
  rw [heq]

private theorem fixedPointSubgroup_quotient_normalizedBy_self_sec9
    {G : Type u} [Group G] [Finite G]
    (MF U H0 : Subgroup G) [Subgroup.Normalizes U MF]
    (hnormal : (H0.subgroupOf MF).Normal)
    (hH0_inv_U : IsInvariant U MF (H0.subgroupOf MF)) :
    (letI : (H0.subgroupOf MF).Normal := hnormal;
      letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
        quotientMulDistribMulAction (A := U) (G := MF)
          (H0.subgroupOf MF) hH0_inv_U;
      quotientSubgroupNormalizedBy MF H0 U
        (fixedPointSubgroup U (MF ⧸ H0.subgroupOf MF))) := by
  classical
  let H0MF : Subgroup MF := H0.subgroupOf MF
  haveI : H0MF.Normal := hnormal
  letI : MulDistribMulAction U (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := U) (G := MF) H0MF hH0_inv_U
  intro a
  refine ⟨?_, ?_⟩
  · intro h
    have hU_norm_MF : U ≤ Subgroup.normalizer (MF : Set G) :=
      Subgroup.Normalizes.le_normalizer
    have ha_norm : (a : G) ∈ Subgroup.normalizer (MF : Set G) :=
      hU_norm_MF a.property
    have hainv_norm : (a : G)⁻¹ ∈ Subgroup.normalizer (MF : Set G) :=
      (Subgroup.normalizer (MF : Set G)).inv_mem ha_norm
    simpa [mul_assoc] using
      (Subgroup.mem_normalizer_iff.mp hainv_norm (h : G)).1 h.property
  · refine ⟨MulDistribMulAction.toMulAut U (MF ⧸ H0MF) a⁻¹, ?_, ?_⟩
    · intro h
      apply congrArg (QuotientGroup.mk' H0MF)
      ext
      simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc]
    · apply le_antisymm
      · intro x hx
        have hfix : (a⁻¹ : U) • x = x := by
          change ∀ u : U, u • x = x at hx
          exact hx a⁻¹
        exact Subgroup.mem_map.mpr
          ⟨x, hx, by
            change (a⁻¹ : U) • x = x
            exact hfix⟩
      · intro x hx
        rcases Subgroup.mem_map.mp hx with ⟨y, hy, hxy⟩
        have hfix : (a⁻¹ : U) • y = y := by
          change ∀ u : U, u • y = y at hy
          exact hy a⁻¹
        have hmapy :
            (MulDistribMulAction.toMulAut U (MF ⧸ H0MF) a⁻¹) y = y := by
          change (a⁻¹ : U) • y = y
          exact hfix
        have hxy' : x = y := hxy.symm.trans hmapy
        simpa [hxy'] using hy

private def quotientSubgroupPreimageInAmbient_sec9
    {G : Type u} [Group G] [Finite G]
    (MF H0 : Subgroup G) [hnormal : (H0.subgroupOf MF).Normal]
    (Q : Subgroup (MF ⧸ H0.subgroupOf MF)) : Subgroup G :=
  (Q.comap (QuotientGroup.mk' (H0.subgroupOf MF))).map MF.subtype

private theorem quotientSubgroupPreimageInAmbient_le_sec9
    {G : Type u} [Group G] [Finite G]
    (MF H0 : Subgroup G) [hnormal : (H0.subgroupOf MF).Normal]
    (Q : Subgroup (MF ⧸ H0.subgroupOf MF)) :
    quotientSubgroupPreimageInAmbient_sec9 MF H0 Q ≤ MF := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
  exact y.property

private theorem H0_le_quotientSubgroupPreimageInAmbient_sec9
    {G : Type u} [Group G] [Finite G]
    (MF H0 : Subgroup G) [hnormal : (H0.subgroupOf MF).Normal]
    (hH0_le_MF : H0 ≤ MF)
    (Q : Subgroup (MF ⧸ H0.subgroupOf MF)) :
    H0 ≤ quotientSubgroupPreimageInAmbient_sec9 MF H0 Q := by
  intro x hxH0
  let H0MF : Subgroup MF := H0.subgroupOf MF
  let xMF : MF := ⟨x, hH0_le_MF hxH0⟩
  refine Subgroup.mem_map.mpr ⟨xMF, ?_, rfl⟩
  change QuotientGroup.mk' H0MF xMF ∈ Q
  have hxH0MF : xMF ∈ H0MF := by
    simpa [xMF, H0MF, Subgroup.mem_subgroupOf] using hxH0
  have hx_one : QuotientGroup.mk' H0MF xMF = 1 :=
    (QuotientGroup.eq_one_iff (N := H0MF) (x := xMF)).2 hxH0MF
  simp [hx_one]

private theorem quotientSubgroupPreimageInAmbient_le_normalizer_of_normalizedBy_sec9
    {G : Type u} [Group G] [Finite G]
    (MF H0 A : Subgroup G) [hnormal : (H0.subgroupOf MF).Normal]
    (Q : Subgroup (MF ⧸ H0.subgroupOf MF)) :
    quotientSubgroupNormalizedBy MF H0 A Q →
      A ≤ Subgroup.normalizer
        (quotientSubgroupPreimageInAmbient_sec9 MF H0 Q : Set G) := by
  classical
  intro hQnorm a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    let H0MF : Subgroup MF := H0.subgroupOf MF
    rcases Subgroup.mem_map.mp hx with ⟨y, hyQ, rfl⟩
    change QuotientGroup.mk' H0MF y ∈ Q at hyQ
    rcases hQnorm ⟨a⁻¹, A.inv_mem ha⟩ with ⟨hconjMF, action, haction, hmap⟩
    have hyQ' :
        action (QuotientGroup.mk' H0MF y) ∈ Q := by
      have hy_map :
          action.toMonoidHom (QuotientGroup.mk' H0MF y) ∈ Q.map action.toMonoidHom :=
        Subgroup.mem_map_of_mem action.toMonoidHom hyQ
      rw [hmap]
      exact hy_map
    let y' : MF := ⟨(a⁻¹)⁻¹ * (y : G) * a⁻¹, hconjMF y⟩
    have hy'_val : (y' : G) = a * (y : G) * a⁻¹ := by
      simp [y']
    refine Subgroup.mem_map.mpr ⟨y', ?_, hy'_val⟩
    change QuotientGroup.mk' H0MF y' ∈ Q
    have haction_y : action (QuotientGroup.mk' H0MF y) = QuotientGroup.mk' H0MF y' := by
      have h := haction y
      change action (QuotientGroup.mk' H0MF y) = QuotientGroup.mk' H0MF y' at h
      exact h
    simpa [← haction_y] using hyQ'
  · intro hx
    let H0MF : Subgroup MF := H0.subgroupOf MF
    rcases Subgroup.mem_map.mp hx with ⟨y, hyQ, hyx⟩
    change QuotientGroup.mk' H0MF y ∈ Q at hyQ
    rcases hQnorm ⟨a, ha⟩ with ⟨hconjMF, action, haction, hmap⟩
    have hyQ' :
        action (QuotientGroup.mk' H0MF y) ∈ Q := by
      have hy_map :
          action.toMonoidHom (QuotientGroup.mk' H0MF y) ∈ Q.map action.toMonoidHom :=
        Subgroup.mem_map_of_mem action.toMonoidHom hyQ
      rw [hmap]
      exact hy_map
    let y' : MF := ⟨a⁻¹ * (y : G) * a, by
      simpa using hconjMF y⟩
    have hy'_val : (y' : G) = x := by
      dsimp [y']
      calc
        a⁻¹ * (y : G) * a = a⁻¹ * (a * x * a⁻¹) * a := by
          rw [show (y : G) = a * x * a⁻¹ from hyx]
        _ = x := by simp [mul_assoc]
    refine Subgroup.mem_map.mpr ⟨y', ?_, hy'_val⟩
    change QuotientGroup.mk' H0MF y' ∈ Q
    have haction_y : action (QuotientGroup.mk' H0MF y) = QuotientGroup.mk' H0MF y' := by
      have h := haction y
      change action (QuotientGroup.mk' H0MF y) = QuotientGroup.mk' H0MF y' at h
      exact h
    simpa [← haction_y] using hyQ'

private theorem quotientSubgroupPreimageInAmbient_le_normalizer_of_commutative_sec9
    {G : Type u} [Group G] [Finite G]
    (MF H0 : Subgroup G) [hnormal : (H0.subgroupOf MF).Normal]
    (Q : Subgroup (MF ⧸ H0.subgroupOf MF)) :
    IsMulCommutative (MF ⧸ H0.subgroupOf MF) →
      MF ≤ Subgroup.normalizer
        (quotientSubgroupPreimageInAmbient_sec9 MF H0 Q : Set G) := by
  classical
  intro hcomm a haMF
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    let H0MF : Subgroup MF := H0.subgroupOf MF
    haveI : IsMulCommutative (MF ⧸ H0MF) := by
      simpa [H0MF] using hcomm
    rcases Subgroup.mem_map.mp hx with ⟨y, hyQ, rfl⟩
    change QuotientGroup.mk' H0MF y ∈ Q at hyQ
    let aMF : MF := ⟨a, haMF⟩
    let y' : MF := ⟨a * (y : G) * a⁻¹, by
      exact MF.mul_mem (MF.mul_mem haMF y.property) (MF.inv_mem haMF)⟩
    have hqeq : QuotientGroup.mk' H0MF y' = QuotientGroup.mk' H0MF y := by
      change QuotientGroup.mk' H0MF (aMF * y * aMF⁻¹) = QuotientGroup.mk' H0MF y
      simp [mul_assoc, mul_comm, mul_left_comm]
    refine Subgroup.mem_map.mpr ⟨y', ?_, rfl⟩
    change QuotientGroup.mk' H0MF y' ∈ Q
    simpa [hqeq] using hyQ
  · intro hx
    let H0MF : Subgroup MF := H0.subgroupOf MF
    haveI : IsMulCommutative (MF ⧸ H0MF) := by
      simpa [H0MF] using hcomm
    rcases Subgroup.mem_map.mp hx with ⟨y, hyQ, hyx⟩
    change QuotientGroup.mk' H0MF y ∈ Q at hyQ
    let aMF : MF := ⟨a, haMF⟩
    let y' : MF := ⟨a⁻¹ * (y : G) * a, by
      exact MF.mul_mem (MF.mul_mem (MF.inv_mem haMF) y.property) haMF⟩
    have hy'_val : (y' : G) = x := by
      dsimp [y']
      calc
        a⁻¹ * (y : G) * a = a⁻¹ * (a * x * a⁻¹) * a := by
          rw [show (y : G) = a * x * a⁻¹ from hyx]
        _ = x := by simp [mul_assoc]
    have hqeq : QuotientGroup.mk' H0MF y' = QuotientGroup.mk' H0MF y := by
      change QuotientGroup.mk' H0MF (aMF⁻¹ * y * aMF) = QuotientGroup.mk' H0MF y
      simp [mul_assoc, mul_comm]
    refine Subgroup.mem_map.mpr ⟨y', ?_, hy'_val⟩
    change QuotientGroup.mk' H0MF y' ∈ Q
    simpa [hqeq] using hyQ

private theorem fixedPointSubgroup_quotient_normalizedBy_of_normalizes_sec9
    {G : Type u} [Group G] [Finite G]
    (MF U A H0 : Subgroup G) [Subgroup.Normalizes U MF] [Subgroup.Normalizes A MF]
    (hA_norm_U : A ≤ Subgroup.normalizer (U : Set G))
    (hnormal : (H0.subgroupOf MF).Normal)
    (hH0_inv_U : IsInvariant U MF (H0.subgroupOf MF))
    (hH0_inv_A : IsInvariant A MF (H0.subgroupOf MF)) :
    (letI : (H0.subgroupOf MF).Normal := hnormal;
      letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
        quotientMulDistribMulAction (A := U) (G := MF)
          (H0.subgroupOf MF) hH0_inv_U;
      quotientSubgroupNormalizedBy MF H0 A
        (fixedPointSubgroup U (MF ⧸ H0.subgroupOf MF))) := by
  classical
  let H0MF : Subgroup MF := H0.subgroupOf MF
  haveI : H0MF.Normal := hnormal
  letI : MulDistribMulAction U (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := U) (G := MF) H0MF hH0_inv_U
  letI : MulDistribMulAction A (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := A) (G := MF) H0MF hH0_inv_A
  have hpreserve :
      ∀ b : A, ∀ x : MF ⧸ H0MF,
        x ∈ fixedPointSubgroup U (MF ⧸ H0MF) →
          (MulDistribMulAction.toMulAut A (MF ⧸ H0MF) b) x ∈
            fixedPointSubgroup U (MF ⧸ H0MF) := by
    intro b x hx
    rcases QuotientGroup.mk'_surjective H0MF x with ⟨h, rfl⟩
    change ∀ u : U,
      u • ((MulDistribMulAction.toMulAut A (MF ⧸ H0MF) b)
          (QuotientGroup.mk' H0MF h)) =
        (MulDistribMulAction.toMulAut A (MF ⧸ H0MF) b)
          (QuotientGroup.mk' H0MF h)
    intro u
    have hb_norm_U : (b : G) ∈ Subgroup.normalizer (U : Set G) :=
      hA_norm_U b.property
    have hbinv_norm_U : (b : G)⁻¹ ∈ Subgroup.normalizer (U : Set G) :=
      (Subgroup.normalizer (U : Set G)).inv_mem hb_norm_U
    have hu' : (b : G)⁻¹ * (u : G) * (b : G) ∈ U := by
      simpa using (Subgroup.mem_normalizer_iff.mp hbinv_norm_U (u : G)).1 u.property
    let u' : U := ⟨(b : G)⁻¹ * (u : G) * (b : G), hu'⟩
    have hfix := hx u'
    have hcommute :
        u • ((MulDistribMulAction.toMulAut A (MF ⧸ H0MF) b)
            (QuotientGroup.mk' H0MF h)) =
          (MulDistribMulAction.toMulAut A (MF ⧸ H0MF) b)
            (u' • QuotientGroup.mk' H0MF h) := by
      apply congrArg (QuotientGroup.mk' H0MF)
      ext
      simp [u', Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
        mul_assoc]
    calc
      u • ((MulDistribMulAction.toMulAut A (MF ⧸ H0MF) b)
          (QuotientGroup.mk' H0MF h)) =
          (MulDistribMulAction.toMulAut A (MF ⧸ H0MF) b)
            (u' • QuotientGroup.mk' H0MF h) := hcommute
      _ = (MulDistribMulAction.toMulAut A (MF ⧸ H0MF) b)
            (QuotientGroup.mk' H0MF h) := by rw [hfix]
  intro a
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hA_norm_MF : A ≤ Subgroup.normalizer (MF : Set G) :=
      Subgroup.Normalizes.le_normalizer
    have ha_norm : (a : G) ∈ Subgroup.normalizer (MF : Set G) :=
      hA_norm_MF a.property
    have hainv_norm : (a : G)⁻¹ ∈ Subgroup.normalizer (MF : Set G) :=
      (Subgroup.normalizer (MF : Set G)).inv_mem ha_norm
    simpa [mul_assoc] using
      (Subgroup.mem_normalizer_iff.mp hainv_norm (h : G)).1 h.property
  · exact MulDistribMulAction.toMulAut A (MF ⧸ H0MF) a⁻¹
  · constructor
    · intro h
      apply congrArg (QuotientGroup.mk' H0MF)
      ext
      simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc]
    · apply le_antisymm
      · intro x hx
        refine Subgroup.mem_map.mpr
          ⟨(MulDistribMulAction.toMulAut A (MF ⧸ H0MF) a) x,
            hpreserve a x hx, ?_⟩
        change (a⁻¹ : A) • (a • x) = x
        exact inv_smul_smul a x
      · intro x hx
        rcases Subgroup.mem_map.mp hx with ⟨y, hy, hxy⟩
        have hy' :
            (MulDistribMulAction.toMulAut A (MF ⧸ H0MF) a⁻¹) y ∈
              fixedPointSubgroup U (MF ⧸ H0MF) :=
          hpreserve a⁻¹ y hy
        rw [← hxy]
        exact hy'

private theorem quotientSubgroup_dichotomy_of_chief_factor_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 H0 : Subgroup G) [Subgroup.Normalizes U MF] [Subgroup.Normalizes W1 MF]
    (hnormal : (H0.subgroupOf MF).Normal)
    (Q : Subgroup (MF ⧸ H0.subgroupOf MF)) :
    H0 ≤ MF →
      MF ≤ M →
        IsChiefFactor (H0.subgroupOf M) (MF.subgroupOf M) →
          IsMulCommutative (MF ⧸ H0.subgroupOf MF) →
            M = (MF ⊔ U) ⊔ W1 →
              quotientSubgroupNormalizedBy MF H0 U Q →
                quotientSubgroupNormalizedBy MF H0 W1 Q →
                  Q = ⊥ ∨ Q = ⊤ := by
  classical
  intro hH0_le_MF hMF_le_M hchief hquot_comm hM_eq hQnormU hQnormW1
  let H0MF : Subgroup MF := H0.subgroupOf MF
  haveI : H0MF.Normal := hnormal
  let N : Subgroup G := quotientSubgroupPreimageInAmbient_sec9 MF H0 Q
  have hN_le_MF : N ≤ MF := by
    simpa [N] using quotientSubgroupPreimageInAmbient_le_sec9 MF H0 Q
  have hN_le_M : N ≤ M := hN_le_MF.trans hMF_le_M
  have hH0_le_N : H0 ≤ N := by
    simpa [N] using H0_le_quotientSubgroupPreimageInAmbient_sec9 MF H0 hH0_le_MF Q
  have hMF_norm_N : MF ≤ Subgroup.normalizer (N : Set G) := by
    simpa [N] using
      quotientSubgroupPreimageInAmbient_le_normalizer_of_commutative_sec9
        MF H0 Q hquot_comm
  have hU_norm_N : U ≤ Subgroup.normalizer (N : Set G) := by
    simpa [N] using
      quotientSubgroupPreimageInAmbient_le_normalizer_of_normalizedBy_sec9
        MF H0 U Q hQnormU
  have hW1_norm_N : W1 ≤ Subgroup.normalizer (N : Set G) := by
    simpa [N] using
      quotientSubgroupPreimageInAmbient_le_normalizer_of_normalizedBy_sec9
        MF H0 W1 Q hQnormW1
  have hM_norm_N : M ≤ Subgroup.normalizer (N : Set G) := by
    intro x hxM
    have hxgen : x ∈ (MF ⊔ U) ⊔ W1 := by
      simpa [hM_eq] using hxM
    exact (sup_le (sup_le hMF_norm_N hU_norm_N) hW1_norm_N) hxgen
  have hN_normal_M : (N.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN_le_M).2 hM_norm_N
  have hH0M_le_NM : H0.subgroupOf M ≤ N.subgroupOf M := by
    intro x hx
    change (x : G) ∈ N
    exact hH0_le_N (by
      simpa [Subgroup.mem_subgroupOf] using hx)
  have hNM_le_MFM : N.subgroupOf M ≤ MF.subgroupOf M := by
    intro x hx
    change (x : G) ∈ MF
    exact hN_le_MF (by
      simpa [Subgroup.mem_subgroupOf] using hx)
  rcases hchief.is_maximal (N.subgroupOf M) hN_normal_M hH0M_le_NM hNM_le_MFM with
    hNsub_eq_H0 | hNsub_eq_MF
  · have hN_eq_H0 : N = H0 := by
      apply le_antisymm
      · intro x hxN
        let xM : M := ⟨x, hN_le_M hxN⟩
        have hxNsub : xM ∈ N.subgroupOf M := by
          simpa [xM, Subgroup.mem_subgroupOf] using hxN
        have hxH0M : xM ∈ H0.subgroupOf M := by
          simpa [hNsub_eq_H0] using hxNsub
        simpa [xM, Subgroup.mem_subgroupOf] using hxH0M
      · exact hH0_le_N
    left
    ext x
    constructor
    · intro hxQ
      rcases QuotientGroup.mk'_surjective H0MF x with ⟨y, rfl⟩
      have hyN : (y : G) ∈ N := by
        refine Subgroup.mem_map.mpr ⟨y, ?_, rfl⟩
        change QuotientGroup.mk' H0MF y ∈ Q
        exact hxQ
      have hyH0 : (y : G) ∈ H0 := by
        simpa [hN_eq_H0] using hyN
      have hyH0MF : y ∈ H0MF := by
        simpa [H0MF, Subgroup.mem_subgroupOf] using hyH0
      have hy_one : QuotientGroup.mk' H0MF y = 1 :=
        (QuotientGroup.eq_one_iff (N := H0MF) (x := y)).2 hyH0MF
      simp [hy_one]
    · intro hxbot
      have hx_one : x = 1 := by
        simpa using hxbot
      simp [hx_one]
  · have hN_eq_MF : N = MF := by
      apply le_antisymm hN_le_MF
      intro x hxMF
      let xM : M := ⟨x, hMF_le_M hxMF⟩
      have hxMFsub : xM ∈ MF.subgroupOf M := by
        simpa [xM, Subgroup.mem_subgroupOf] using hxMF
      have hxNsub : xM ∈ N.subgroupOf M := by
        simpa [hNsub_eq_MF] using hxMFsub
      simpa [xM, Subgroup.mem_subgroupOf] using hxNsub
    right
    ext x
    constructor
    · intro _hx
      exact Subgroup.mem_top x
    · intro _hx
      rcases QuotientGroup.mk'_surjective H0MF x with ⟨y, rfl⟩
      have hyN : (y : G) ∈ N := by
        simp [hN_eq_MF, y.property]
      rcases Subgroup.mem_map.mp hyN with ⟨z, hzQ, hzy⟩
      change QuotientGroup.mk' H0MF y ∈ Q
      change QuotientGroup.mk' H0MF z ∈ Q at hzQ
      have hzy' : z = y := Subtype.ext hzy
      simpa [hzy'] using hzQ

public theorem quotientSubgroup_dichotomy_of_quotientChiefFactorData_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 : Subgroup G)
    (q : ℕ) (p : Nat.Primes) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      hoReductionData M MF U W2 H0 p →
        quotientChiefFactorData_9_6 M MF H0 W1 p →
          (hnormal : (H0.subgroupOf MF).Normal) →
            letI : (H0.subgroupOf MF).Normal := hnormal
            ∀ Q : Subgroup (MF ⧸ H0.subgroupOf MF),
              quotientSubgroupNormalizedBy MF H0 U Q →
                quotientSubgroupNormalizedBy MF H0 W1 Q →
                  Q = ⊥ ∨ Q = ⊤ := by
  classical
  intro h92 hpData h96 hnormal Q hQnormU hQnormW1
  have h92Full : hypothesis_9_2_statement M MF U W1 W2 q := h92
  have hPsource := h92.typePDefinitionData
  rcases hPsource with
    ⟨_hMFsource, _hW1cyc, _hW1ne, ⟨hW1_le_M, _hW1hall⟩,
      hcompMW1, hUleD, _hUnil, _hW1normU, hcompDU, _hMFnotcyc,
      _hM2le, _hFitEq, _hFitLeD, _hW2le, _hW2cyc, _hW2ne,
      _hcentW1, _hnormX⟩
  rcases hpData with
    ⟨_hH0_le_MF_hp, _hMF_le_M_hp, _hH0_normal_M_hp, _hH0_normal_MF_hp,
      _hH0lt_hp, helem, _htypeIIIIVData_hp⟩
  rcases h96 with ⟨hH0_le_MF, hMF_le_M, _hnormalH0, hchief, _hWbar, _hcard⟩
  rcases theorem_9_3_action_normalizes_and_solvable_sec9
      M MF U W1 W2 q h92Full with
    ⟨hUW1_norm_MF, _hsolvMF⟩
  have hU_norm_MF : U ≤ Subgroup.normalizer (MF : Set G) :=
    le_sup_left.trans hUW1_norm_MF
  have hW1_norm_MF : W1 ≤ Subgroup.normalizer (MF : Set G) :=
    le_sup_right.trans hUW1_norm_MF
  letI : Subgroup.Normalizes U MF := ⟨hU_norm_MF⟩
  letI : Subgroup.Normalizes W1 MF := ⟨hW1_norm_MF⟩
  have hU_le_M : U ≤ M :=
    hUleD.trans (section12_ambientDerivedSubgroup_le (G := G) (E := M))
  have hM_eq : M = (MF ⊔ U) ⊔ W1 := by
    calc
      M = ambientDerivedSubgroup M ⊔ W1 := hcompMW1.2.2.1
      _ = (MF ⊔ U) ⊔ W1 := by rw [hcompDU.2.2.1]
  let H0MF : Subgroup MF := H0.subgroupOf MF
  haveI : H0MF.Normal := hnormal
  have hquot_comm : IsMulCommutative (MF ⧸ H0MF) := by
    rcases helem with ⟨_hnormal_elem, helemQ⟩
    have helemQ' : IsElementaryAbelian p.val (MF ⧸ H0MF) := by
      simpa [H0MF] using helemQ
    exact helemQ'.toIsMulCommutative
  simpa [H0MF] using
    quotientSubgroup_dichotomy_of_chief_factor_sec9
      M MF U W1 H0 hnormal Q
      hH0_le_MF hMF_le_M hchief hquot_comm hM_eq hQnormU hQnormW1

public theorem quotientSubgroup_not_W1_normalized_of_proper_U_normalized_quotientChiefFactorData_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 : Subgroup G)
    (q : ℕ) (p : Nat.Primes) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      hoReductionData M MF U W2 H0 p →
        quotientChiefFactorData_9_6 M MF H0 W1 p →
          (hnormal : (H0.subgroupOf MF).Normal) →
            letI : (H0.subgroupOf MF).Normal := hnormal
            ∀ Q : Subgroup (MF ⧸ H0.subgroupOf MF),
              quotientSubgroupNormalizedBy MF H0 U Q →
                Q ≠ ⊥ →
                  Q ≠ ⊤ →
                    ¬ quotientSubgroupNormalizedBy MF H0 W1 Q := by
  intro h92 hpData h96 hnormal Q hQnormU hQneBot hQneTop hQnormW1
  have hcases :
      Q = ⊥ ∨ Q = ⊤ :=
    quotientSubgroup_dichotomy_of_quotientChiefFactorData_sec9
      M MF U W1 W2 H0 q p h92 hpData h96 hnormal Q hQnormU hQnormW1
  rcases hcases with hQbot | hQtop
  · exact hQneBot hQbot
  · exact hQneTop hQtop

private theorem quotient_U_fixed_eq_bot_of_fixedPointSubgroup_dichotomy_sec9
    {G : Type u} [Group G] [Finite G]
    (MF U H0 : Subgroup G) [Subgroup.Normalizes U MF]
    (hnormal : (H0.subgroupOf MF).Normal)
    (hH0_inv_U : IsInvariant U MF (H0.subgroupOf MF)) :
    (letI : (H0.subgroupOf MF).Normal := hnormal;
      letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
        quotientMulDistribMulAction (A := U) (G := MF)
          (H0.subgroupOf MF) hH0_inv_U;
      fixedPointSubgroup U (MF ⧸ H0.subgroupOf MF) = ⊥ ∨
        fixedPointSubgroup U (MF ⧸ H0.subgroupOf MF) = ⊤) →
      (letI : (H0.subgroupOf MF).Normal := hnormal;
        letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
          quotientMulDistribMulAction (A := U) (G := MF)
            (H0.subgroupOf MF) hH0_inv_U;
        fixedPointSubgroup U (MF ⧸ H0.subgroupOf MF) ≠ ⊤) →
      (letI : (H0.subgroupOf MF).Normal := hnormal;
        letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
          quotientMulDistribMulAction (A := U) (G := MF)
            (H0.subgroupOf MF) hH0_inv_U;
        fixedPointSubgroup U (MF ⧸ H0.subgroupOf MF) = ⊥) := by
  classical
  intro hcases hnotTop
  let H0MF : Subgroup MF := H0.subgroupOf MF
  haveI : H0MF.Normal := hnormal
  letI : MulDistribMulAction U (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := U) (G := MF) H0MF hH0_inv_U
  let Q : Subgroup (MF ⧸ H0MF) := fixedPointSubgroup U (MF ⧸ H0MF)
  rcases hcases with hbot | htop
  · simpa [Q, H0MF] using hbot
  · exfalso
    exact hnotTop (by simpa [Q, H0MF] using htop)

private theorem solvable_of_nilpotent_frobenius_kernel_cyclic_complement_sec9
    {G : Type u} [Group G] [Finite G]
    (U W1 : Subgroup G)
    (hUnil : Group.IsNilpotent U)
    (hW1cyc : IsCyclic W1)
    (hfrob : section12FrobeniusJoinWithKernel U W1) :
    IsSolvable (U ⊔ W1 : Subgroup G) := by
  classical
  let S : Subgroup G := U ⊔ W1
  let Usub : Subgroup S := U.subgroupOf S
  let W1sub : Subgroup S := W1.subgroupOf S
  have hUnil_sub : Group.IsNilpotent Usub := by
    haveI : Group.IsNilpotent U := hUnil
    exact Group.nilpotent_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (H := U) (K := S)
        (by
          change U ≤ U ⊔ W1
          exact le_sup_left)).symm
  have hUsolv : Group.IsSolvable Usub := by
    letI : Group.IsNilpotent Usub := hUnil_sub
    exact IsNilpotent.to_isSolvable
  have hnormal : Usub.Normal := by
    simpa [section12FrobeniusJoinWithKernel, S, Usub, W1sub] using
      (IsFrobeniusGroupWithKernelComplement.normal hfrob)
  have hcompl : Usub.IsComplement' W1sub := by
    simpa [section12FrobeniusJoinWithKernel, S, Usub, W1sub] using
      (IsFrobeniusGroupWithKernelComplement.isComplement' hfrob)
  have hW1sub_cyc : IsCyclic W1sub := by
    exact (Subgroup.subgroupOfEquivOfLe (H := W1) (K := S)
      (by
        change W1 ≤ U ⊔ W1
        exact le_sup_right)).isCyclic.mpr hW1cyc
  have hquot_solv : Group.IsSolvable (S ⧸ Usub) := by
    haveI : Usub.Normal := hnormal
    haveI : IsCyclic W1sub := hW1sub_cyc
    haveI : CommGroup W1sub := IsCyclic.commGroup
    haveI : Group.IsSolvable W1sub := by infer_instance
    exact Group.isSolvable_of_isSolvable_injective
      (f := hcompl.symm.QuotientMulEquiv.toMonoidHom)
      hcompl.symm.QuotientMulEquiv.injective
  haveI : Usub.Normal := hnormal
  letI : Group.IsSolvable Usub := hUsolv
  letI : Group.IsSolvable (S ⧸ Usub) := hquot_solv
  exact
    Group.isSolvable_of_ker_le_range
      Usub.subtype
      (QuotientGroup.mk' Usub)
      (by
        intro x hx
        refine ⟨⟨x, ?_⟩, rfl⟩
        exact (QuotientGroup.eq_one_iff (N := Usub) (x := x)).1 hx)

private theorem cyclic_subgroup_card_eq_prime_of_elementaryAbelian_sec9
    {p : Nat.Primes} {Q : Type u} [Group Q] [Finite Q]
    [IsElementaryAbelian p.val Q]
    (K : Subgroup Q) :
    IsCyclic K →
      Nat.card K ≠ 1 →
        Nat.card K = p.val := by
  intro hcyc hne_one
  have hcard_dvd : Nat.card K ∣ p.val := by
    rw [← hcyc.exponent_eq_card]
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    intro x
    apply Subtype.ext
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p.val Q) (x : Q)
  rcases (Nat.dvd_prime p.property).1 hcard_dvd with hcard_one | hcard_prime
  · exact False.elim (hne_one hcard_one)
  · exact hcard_prime

private theorem theorem_9_6_typeII_quotient_fixed_points_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (T : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (S : Finset (Section1.ClassFunction M))
    (p : Nat.Primes) :
    notation_9_5_data M MF U W1 W2 H0 C Cprime T S →
      hoReductionData M MF U W2 H0 p →
        section16TypeII M MF →
          (hnormal : (H0.subgroupOf MF).Normal) →
            ∀ h : G, h ∈ MF →
              (∀ u : G, u ∈ U → ⁅u, h⁆ ∈ H0) → h ∈ H0 := by
  classical
  intro h95 hp hII hnormal h hhMF hfixed
  rcases h95 with
    ⟨h92, _hp95, _hC, _hBarU, _hCprimeC, _hCprimeEq, _hDade, _hS⟩
  rcases hp with
    ⟨hH0_le_MF, hMF_le_M, hH0_normal_M, _hH0_normal_MF, _hH0lt,
      _helem, _htypeIIIIVData⟩
  rcases theorem_9_3_source_action_and_branch_facts_sec9
      M MF U W1 W2 (Nat.card W1) h92 with
    ⟨haction, hII_CU, _hIIIIV⟩
  rcases haction with ⟨_hcomp, _hfrob, hUW1_norm_MF, hsolvMF, hcopUW1⟩
  have hU_norm_MF : U ≤ Subgroup.normalizer (MF : Set G) :=
    le_sup_left.trans hUW1_norm_MF
  letI : Subgroup.Normalizes U MF := ⟨hU_norm_MF⟩
  have hU_dvd_UW1 : Nat.card U ∣ Nat.card (U ⊔ W1 : Subgroup G) :=
    Subgroup.card_dvd_of_le le_sup_left
  have hcopU : Nat.Coprime (Nat.card U) (Nat.card MF) :=
    (Nat.Coprime.coprime_dvd_right hU_dvd_UW1 hcopUW1).symm
  have hfixMF_bot : fixedPointSubgroup U MF = ⊥ := by
    have hfix_eq :=
      fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn MF U hU_norm_MF
    simpa [hII_CU hII] using hfix_eq
  have hsource : Section8.typePDefinitionData M MF U W1 W2 := h92.typePDefinitionData
  rcases hsource with
    ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, hUleD,
      _hUnil, _hW1normU, _hcompDU, _hMFnotcyc, _hM2le, _hFitEq, _hFitLeD,
      _hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
  have hU_le_M : U ≤ M :=
    hUleD.trans (section12_ambientDerivedSubgroup_le (G := G) (E := M))
  let H0MF : Subgroup MF := H0.subgroupOf MF
  haveI : H0MF.Normal := hnormal
  have hH0_inv : IsInvariant U MF H0MF :=
    H0_subgroupOf_MF_isInvariant_under_U_sec9 M MF U H0
      hMF_le_M hU_le_M hH0_normal_M hU_norm_MF
  letI : MulDistribMulAction U (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := U) (G := MF) H0MF hH0_inv
  have hquot_fixed_eq :
      fixedPointSubgroup U (MF ⧸ H0MF) =
        (fixedPointSubgroup U MF).map (QuotientGroup.mk' H0MF) :=
    proposition_1_5_d (G := MF) (A := U) hsolvMF hcopU Set.univ H0MF hH0_inv
  let hMF : MF := ⟨h, hhMF⟩
  have hq_fixed : QuotientGroup.mk' H0MF hMF ∈ fixedPointSubgroup U (MF ⧸ H0MF) := by
    change ∀ u : U, u • QuotientGroup.mk' H0MF hMF = QuotientGroup.mk' H0MF hMF
    intro u
    calc
      u • QuotientGroup.mk' H0MF hMF =
          QuotientGroup.mk' H0MF (u • hMF) := by
            simp
      _ = QuotientGroup.mk' H0MF hMF := by
            apply QuotientGroup.eq_iff_div_mem.mpr
            have hcommH0 : ⁅(u : G), h⁆ ∈ H0 := hfixed (u : G) u.property
            have hcommH0MF : ((u • hMF : MF) / hMF) ∈ H0MF := by
              have hval :
                  (((u • hMF : MF) / hMF : MF) : G) = ⁅(u : G), h⁆ := by
                simp [hMF, div_eq_mul_inv, commutatorElement_def,
                  Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc]
              simpa [H0MF, Subgroup.mem_subgroupOf, hval] using hcommH0
            simpa [div_eq_mul_inv] using hcommH0MF
  have hq_mem_image :
      QuotientGroup.mk' H0MF hMF ∈
        (fixedPointSubgroup U MF).map (QuotientGroup.mk' H0MF) := by
    simpa [hquot_fixed_eq] using hq_fixed
  have hq_one : QuotientGroup.mk' H0MF hMF = 1 := by
    simpa [hfixMF_bot] using hq_mem_image
  have hhH0MF : hMF ∈ H0MF :=
    (QuotientGroup.eq_one_iff (N := H0MF) (x := hMF)).1 hq_one
  simpa [H0MF, Subgroup.mem_subgroupOf, hMF] using hhH0MF

private theorem theorem_9_6_typeII_quotient_U_fixed_eq_bot_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    [Subgroup.Normalizes U MF]
    (T : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (S : Finset (Section1.ClassFunction M))
    (p : Nat.Primes) :
    notation_9_5_data M MF U W1 W2 H0 C Cprime T S →
      hoReductionData M MF U W2 H0 p →
        section16TypeII M MF →
          (hnormal : (H0.subgroupOf MF).Normal) →
            (hH0_inv_U : IsInvariant U MF (H0.subgroupOf MF)) →
              (letI : (H0.subgroupOf MF).Normal := hnormal;
                letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
                  quotientMulDistribMulAction (A := U) (G := MF)
                    (H0.subgroupOf MF) hH0_inv_U;
                fixedPointSubgroup U (MF ⧸ H0.subgroupOf MF) = ⊥) := by
  classical
  intro h95 hp hII hnormal hH0_inv_U
  let H0MF : Subgroup MF := H0.subgroupOf MF
  haveI : H0MF.Normal := hnormal
  letI : MulDistribMulAction U (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := U) (G := MF) H0MF hH0_inv_U
  have hfixed_point :=
    theorem_9_6_typeII_quotient_fixed_points_sec9
      M MF U W1 W2 H0 C Cprime T S p h95 hp hII hnormal
  apply le_antisymm
  · intro x hx
    rcases QuotientGroup.mk'_surjective H0MF x with ⟨h, rfl⟩
    have hcommH0 : ∀ u : G, u ∈ U → ⁅u, (h : G)⁆ ∈ H0 := by
      intro u huU
      let uU : U := ⟨u, huU⟩
      have hfixed_mk :
          uU • QuotientGroup.mk' H0MF h = QuotientGroup.mk' H0MF h := by
        exact hx uU
      have hq : QuotientGroup.mk' H0MF (uU • h) = QuotientGroup.mk' H0MF h := by
        simpa using hfixed_mk
      have hcommH0MF : ((uU • h : MF) / h) ∈ H0MF :=
        QuotientGroup.eq_iff_div_mem.mp hq
      have hval : ((((uU • h : MF) / h : MF) : G) = ⁅u, (h : G)⁆) := by
        simp [uU, div_eq_mul_inv, commutatorElement_def,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc]
      simpa [H0MF, Subgroup.mem_subgroupOf, hval] using hcommH0MF
    have hhH0 : (h : G) ∈ H0 :=
      hfixed_point (h : G) h.property hcommH0
    have hhH0MF : h ∈ H0MF := by
      simpa [H0MF, Subgroup.mem_subgroupOf] using hhH0
    have hmk_one : QuotientGroup.mk' H0MF h = 1 :=
      (QuotientGroup.eq_one_iff (N := H0MF) (x := h)).2 hhH0MF
    simp [hmk_one]
  · exact bot_le

private theorem theorem_9_6_quotient_cardinality_formula_of_U_fixed_bot_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 : Subgroup G)
    [Subgroup.Normalizes U MF] [Subgroup.Normalizes W1 MF]
    (p : Nat.Primes) :
    hypothesis_9_2_statement M MF U W1 W2 (Nat.card W1) →
      hoReductionData M MF U W2 H0 p →
        (hnormal : (H0.subgroupOf MF).Normal) →
          (hH0_inv_U : IsInvariant U MF (H0.subgroupOf MF)) →
            (hH0_inv_W1 : IsInvariant W1 MF (H0.subgroupOf MF)) →
              (letI : (H0.subgroupOf MF).Normal := hnormal;
                letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
                  quotientMulDistribMulAction (A := U) (G := MF)
                    (H0.subgroupOf MF) hH0_inv_U;
                fixedPointSubgroup U (MF ⧸ H0.subgroupOf MF) = ⊥) →
              (letI : (H0.subgroupOf MF).Normal := hnormal;
                letI : MulDistribMulAction W1 (MF ⧸ H0.subgroupOf MF) :=
                  quotientMulDistribMulAction (A := W1) (G := MF)
                    (H0.subgroupOf MF) hH0_inv_W1;
                Nat.card (MF ⧸ H0.subgroupOf MF) =
                  Nat.card (fixedPointSubgroup W1 (MF ⧸ H0.subgroupOf MF)) ^
                    Nat.card W1) := by
  classical
  intro h92 hp hnormal hH0_inv_U hH0_inv_W1 hU_fixed_bot
  rcases hp with
    ⟨hH0_le_MF, hMF_le_M, hH0_normal_M, _hH0_normal_MF, hH0lt,
      _helem, _htypeIIIIVData⟩
  have h92Full := h92
  have hMF := h92.mf
  have hPsource := h92.typePDefinitionData
  have hIItoIVSource := h92.typeIIToIVSourceCondition
  rcases hPsource with
    ⟨hMFsource, hW1cyc, _hW1ne, hW1hall, _hcompMW1, hUleD,
      hUnil, _hW1normU, _hcompDU, _hMFnotcyc, _hM2le, _hFitEq, _hFitLeD,
      _hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
  rcases hMFsource with ⟨hMFhall, _hMFmax⟩
  rcases hMFhall with ⟨_hMF_le_M_source, _hMF_normal_M_source, hMFnil, _hMFhall⟩
  rcases hW1hall with ⟨hW1_le_M, _hW1hall⟩
  rcases hIItoIVSource with ⟨_hU_ne, hW1primeOrder, _hTI⟩
  rcases theorem_9_3_source_action_and_branch_facts_sec9
      M MF U W1 W2 (Nat.card W1) h92Full with
    ⟨haction, _hII, _hIIIIV⟩
  rcases haction with ⟨_hcomp, hfrob, hUW1_norm_MF, _hsolvMF, hcopUW1⟩
  let H0MF : Subgroup MF := H0.subgroupOf MF
  let UW1 : Subgroup G := U ⊔ W1
  haveI : H0MF.Normal := hnormal
  have hH0MF_ne_top : H0MF ≠ ⊤ := by
    intro htop
    have hMF_le_H0 : MF ≤ H0 := by
      intro x hxMF
      let xMF : MF := ⟨x, hxMF⟩
      have hxH0MF : xMF ∈ H0MF := by
        simp [htop]
      simpa [H0MF, xMF, Subgroup.mem_subgroupOf] using hxH0MF
    exact (not_le_of_gt hH0lt) hMF_le_H0
  haveI : Nontrivial (MF ⧸ H0MF) :=
    (QuotientGroup.nontrivial_iff (N := H0MF)).2 hH0MF_ne_top
  letI : Subgroup.Normalizes UW1 MF := ⟨by simpa [UW1] using hUW1_norm_MF⟩
  letI : MulDistribMulAction U (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := U) (G := MF) H0MF hH0_inv_U
  letI : MulDistribMulAction W1 (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := W1) (G := MF) H0MF hH0_inv_W1
  have hU_le_M : U ≤ M :=
    hUleD.trans (section12_ambientDerivedSubgroup_le (G := G) (E := M))
  have hUW1_le_M : UW1 ≤ M := by
    dsimp [UW1]
    exact sup_le hU_le_M hW1_le_M
  have hH0_inv_UW1 : IsInvariant UW1 MF H0MF :=
    H0_subgroupOf_MF_isInvariant_under_U_sec9 M MF UW1 H0
      hMF_le_M hUW1_le_M hH0_normal_M (by simpa [UW1] using hUW1_norm_MF)
  letI : MulDistribMulAction UW1 (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := UW1) (G := MF) H0MF hH0_inv_UW1
  have hU_fixed_bot' :
      fixedPointSubgroup U (MF ⧸ H0MF) = ⊥ := by
    simpa [H0MF] using hU_fixed_bot
  have hK_fixed_bot :
      fixedPointSubgroup (↥(U.subgroupOf UW1)) (MF ⧸ H0MF) = ⊥ := by
    simpa [H0MF, UW1] using
      quotient_U_fixedPointSubgroup_subgroupOf_eq_bot_sec9
        MF U W1 H0 hnormal hH0_inv_U hH0_inv_UW1 hU_fixed_bot'
  have hUW1_solv : IsSolvable UW1 := by
    simpa [UW1] using
      solvable_of_nilpotent_frobenius_kernel_cyclic_complement_sec9
        U W1 hUnil hW1cyc hfrob
  have hquot_nil : Group.IsNilpotent (MF ⧸ H0MF) := by
    haveI : Group.IsNilpotent MF := hMFnil
    exact Group.nilpotent_of_surjective
      (QuotientGroup.mk' H0MF) (QuotientGroup.mk'_surjective H0MF)
  have hquot_dvd_MF : Nat.card (MF ⧸ H0MF) ∣ Nat.card MF :=
    Subgroup.card_quotient_dvd_card H0MF
  have hcop :
      Nat.Coprime (Nat.card UW1) (Nat.card (MF ⧸ H0MF)) :=
    Nat.Coprime.coprime_dvd_right hquot_dvd_MF (by
      simpa [UW1] using hcopUW1.symm)
  let W1sub : Subgroup UW1 := W1.subgroupOf UW1
  have hW1sub_card : Nat.card W1sub = Nat.card W1 :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := W1) (K := UW1)
        (by
          change W1 ≤ U ⊔ W1
          exact le_sup_right)).toEquiv
  have hW1_prime : Nat.Prime (Nat.card W1) := by
    rcases hW1primeOrder with ⟨q, hq⟩
    simpa [hq] using q.property
  have hW1sub_prime : Nat.Prime (Nat.card W1sub) := by
    simpa [hW1sub_card] using hW1_prime
  have hfixR :
      ∀ x : W1sub, x ≠ 1 →
        fixedPointSubgroup (↥(Subgroup.zpowers (x : UW1))) (MF ⧸ H0MF) =
          fixedPointSubgroup (↥W1sub) (MF ⧸ H0MF) := by
    intro x hx
    have hx_top : Subgroup.zpowers x = (⊤ : Subgroup W1sub) :=
      zpowers_eq_top_of_prime_card_of_ne_one hW1sub_prime hx
    have hmap_zpow :
        (Subgroup.zpowers x).map W1sub.subtype =
          Subgroup.zpowers (x : UW1) := by
      simp
    have htop_map : (⊤ : Subgroup W1sub).map W1sub.subtype = W1sub := by
      ext y
      constructor
      · intro hy
        rcases Subgroup.mem_map.mp hy with ⟨z, _hz, rfl⟩
        exact z.property
      · intro hy
        exact Subgroup.mem_map.mpr ⟨⟨y, hy⟩, by simp, rfl⟩
    have hzpow_eq : Subgroup.zpowers (x : UW1) = W1sub := by
      calc
        Subgroup.zpowers (x : UW1) =
            (Subgroup.zpowers x).map W1sub.subtype := hmap_zpow.symm
        _ = (⊤ : Subgroup W1sub).map W1sub.subtype := by rw [hx_top]
        _ = W1sub := htop_map
    rw [hzpow_eq]
  have hmain :
      Nat.card (MF ⧸ H0MF) =
        Nat.card (fixedPointSubgroup (↥W1sub) (MF ⧸ H0MF)) ^ Nat.card W1sub := by
    exact
      theorem_3_10_b (G := UW1) (K := U.subgroupOf UW1) (R := W1sub)
        (M := MF ⧸ H0MF)
        (by simpa [section12FrobeniusJoinWithKernel, UW1, W1sub] using hfrob)
        hUW1_solv hquot_nil hcop hK_fixed_bot hfixR
  have hW1sub_fixed_card :
      Nat.card (fixedPointSubgroup (↥W1sub) (MF ⧸ H0MF)) =
        Nat.card (fixedPointSubgroup W1 (MF ⧸ H0MF)) := by
    simpa [H0MF, UW1, W1sub] using
      quotient_W1_subgroupOf_fixedPointSubgroup_card_eq_sec9
        MF U W1 H0 hnormal hH0_inv_W1 hH0_inv_UW1
  have hfinal :
      Nat.card (MF ⧸ H0MF) =
        Nat.card (fixedPointSubgroup W1 (MF ⧸ H0MF)) ^ Nat.card W1 := by
    calc
      Nat.card (MF ⧸ H0MF) =
          Nat.card (fixedPointSubgroup (↥W1sub) (MF ⧸ H0MF)) ^ Nat.card W1sub :=
        hmain
      _ = Nat.card (fixedPointSubgroup W1 (MF ⧸ H0MF)) ^ Nat.card W1 := by
        rw [hW1sub_fixed_card, hW1sub_card]
  simpa [H0MF] using hfinal

public theorem quotient_W1_fixedPointSubgroup_eq_W2_map_of_hypothesis_9_2_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 : Subgroup G)
    [Subgroup.Normalizes W1 MF]
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (hnormal : (H0.subgroupOf MF).Normal) →
        (hH0_inv_W1 : IsInvariant W1 MF (H0.subgroupOf MF)) →
          letI : (H0.subgroupOf MF).Normal := hnormal
          letI : MulDistribMulAction W1 (MF ⧸ H0.subgroupOf MF) :=
            quotientMulDistribMulAction (A := W1) (G := MF)
              (H0.subgroupOf MF) hH0_inv_W1
          fixedPointSubgroup W1 (MF ⧸ H0.subgroupOf MF) =
            (W2.subgroupOf MF).map (QuotientGroup.mk' (H0.subgroupOf MF)) := by
  intro h92 hnormal hH0_inv_W1
  have h92Full := h92
  rcases theorem_9_3_source_action_and_branch_facts_sec9 M MF U W1 W2 q h92 with
    ⟨haction, _hII, _hIIIIV⟩
  rcases haction with ⟨_hcompUW1, _hfrob, hUW1_norm_MF, hsolvMF, hcopUW1⟩
  let H0MF : Subgroup MF := H0.subgroupOf MF
  haveI : H0MF.Normal := hnormal
  letI : MulDistribMulAction W1 (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := W1) (G := MF) H0MF hH0_inv_W1
  have hW1_norm_MF : W1 ≤ Subgroup.normalizer (MF : Set G) :=
    le_sup_right.trans hUW1_norm_MF
  have hW1_dvd_UW1 : Nat.card W1 ∣ Nat.card (U ⊔ W1 : Subgroup G) :=
    Subgroup.card_dvd_of_le le_sup_right
  have hcopW1 : Nat.Coprime (Nat.card W1) (Nat.card MF) :=
    (Nat.Coprime.coprime_dvd_right hW1_dvd_UW1 hcopUW1).symm
  have hquot_fixed_eq :
      fixedPointSubgroup W1 (MF ⧸ H0MF) =
        (fixedPointSubgroup W1 MF).map (QuotientGroup.mk' H0MF) := by
    simpa [H0MF] using
      proposition_1_5_d (G := MF) (A := W1) hsolvMF hcopW1 Set.univ H0MF hH0_inv_W1
  have hCW1 : subgroupCentralizerIn MF W1 = W2 :=
    subgroupCentralizerIn_W1_eq_W2_of_hypothesis_9_2_sec9
      M MF U W1 W2 q h92Full
  have hfixMF_eq :
      fixedPointSubgroup W1 MF = W2.subgroupOf MF := by
    have hfix_eq :=
      fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn MF W1 hW1_norm_MF
    simpa [hCW1] using hfix_eq
  simpa [H0MF] using hquot_fixed_eq.trans (by rw [hfixMF_eq])


private theorem theorem_9_6_typeII_cardinality_of_chief_factor_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (T : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (S : Finset (Section1.ClassFunction M))
    (p : Nat.Primes) :
    notation_9_5_data M MF U W1 W2 H0 C Cprime T S →
      hoReductionData M MF U W2 H0 p →
        section16TypeII M MF →
          (hnormal : (H0.subgroupOf MF).Normal) →
            IsChiefFactor (H0.subgroupOf M) (MF.subgroupOf M) →
              (letI : (H0.subgroupOf MF).Normal := hnormal;
                Nat.card {x : MF ⧸ H0.subgroupOf MF //
                  ∀ h : MF, QuotientGroup.mk' (H0.subgroupOf MF) h = x →
                    ∀ w : G, w ∈ W1 → ⁅w, (h : G)⁆ ∈ H0} = p.val) ∧
              Nat.card (MF ⧸ H0.subgroupOf MF) = p.val ^ Nat.card W1 := by
  classical
  intro h95 hp hII hnormal _hchief
  have h95Full := h95
  have hpFull := hp
  rcases h95 with
    ⟨h92, _hp95, _hC, _hBarU, _hCprimeC, _hCprimeEq, _hDade, _hS⟩
  have h92Full : hypothesis_9_2_statement M MF U W1 W2 (Nat.card W1) := h92
  rcases hp with
    ⟨hH0_le_MF, hMF_le_M, hH0_normal_M, _hH0_normal_MF, hH0lt,
      helem, _htypeIIIIVData⟩
  have hPsource := h92.typePDefinitionData
  rcases hPsource with
    ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, hUleD,
      _hUnil, _hW1normU, _hcompDU, _hMFnotcyc, _hM2le, _hFitEq, _hFitLeD,
      hW2le, hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
  rcases theorem_9_3_source_action_and_branch_facts_sec9
      M MF U W1 W2 (Nat.card W1) h92Full with
    ⟨haction, _hIIcentralizer, _hIIIIV⟩
  rcases haction with ⟨_hcomp, _hfrob, hUW1_norm_MF, hsolvMF, hcopUW1⟩
  have hU_norm_MF : U ≤ Subgroup.normalizer (MF : Set G) :=
    le_sup_left.trans hUW1_norm_MF
  have hW1_norm_MF : W1 ≤ Subgroup.normalizer (MF : Set G) :=
    le_sup_right.trans hUW1_norm_MF
  letI : Subgroup.Normalizes U MF := ⟨hU_norm_MF⟩
  letI : Subgroup.Normalizes W1 MF := ⟨hW1_norm_MF⟩
  have hU_le_M : U ≤ M :=
    hUleD.trans (section12_ambientDerivedSubgroup_le (G := G) (E := M))
  have hH0_inv_U : IsInvariant U MF (H0.subgroupOf MF) :=
    H0_subgroupOf_MF_isInvariant_under_U_sec9 M MF U H0
      hMF_le_M hU_le_M hH0_normal_M hU_norm_MF
  rcases h92Full.typePDefinitionData with
    ⟨_hMFsource, _hW1cyc, _hW1ne, ⟨hW1_le_M, _hW1hall⟩,
      _hcompMW1, _hUleD, _hUnil, _hW1normU, _hcompDU, _hMFnotcyc,
      _hM2le, _hFitEq, _hFitLeD, _hW2le', _hW2cyc', _hW2ne,
      _hcentW1, _hnormX⟩
  have hH0_inv_W1 : IsInvariant W1 MF (H0.subgroupOf MF) :=
    H0_subgroupOf_MF_isInvariant_under_U_sec9 M MF W1 H0
      hMF_le_M hW1_le_M hH0_normal_M hW1_norm_MF
  let H0MF : Subgroup MF := H0.subgroupOf MF
  haveI : H0MF.Normal := hnormal
  letI : MulDistribMulAction W1 (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := W1) (G := MF) H0MF hH0_inv_W1
  have hU_fixed_bot :
      fixedPointSubgroup U (MF ⧸ H0MF) = ⊥ := by
    simpa [H0MF] using
      theorem_9_6_typeII_quotient_U_fixed_eq_bot_sec9
        M MF U W1 W2 H0 C Cprime T S p h95Full hpFull hII
        hnormal hH0_inv_U
  have hquot_formula :
      Nat.card (MF ⧸ H0MF) =
        Nat.card (fixedPointSubgroup W1 (MF ⧸ H0MF)) ^ Nat.card W1 := by
    simpa [H0MF] using
      theorem_9_6_quotient_cardinality_formula_of_U_fixed_bot_sec9
        M MF U W1 W2 H0 p h92Full hpFull hnormal
        hH0_inv_U hH0_inv_W1 (by simpa [H0MF] using hU_fixed_bot)
  have hW1_dvd_UW1 : Nat.card W1 ∣ Nat.card (U ⊔ W1 : Subgroup G) :=
    Subgroup.card_dvd_of_le le_sup_right
  have hcopW1 : Nat.Coprime (Nat.card W1) (Nat.card MF) :=
    (Nat.Coprime.coprime_dvd_right hW1_dvd_UW1 hcopUW1).symm
  have hquot_fixed_eq :
      fixedPointSubgroup W1 (MF ⧸ H0MF) =
        (W2.subgroupOf MF).map (QuotientGroup.mk' H0MF) := by
    simpa [H0MF] using
      quotient_W1_fixedPointSubgroup_eq_W2_map_of_hypothesis_9_2_sec9
        M MF U W1 W2 H0 (Nat.card W1) h92Full hnormal hH0_inv_W1
  have hW2_le_MF : W2 ≤ MF := hW2le.trans inf_le_left
  have hW2sub_cyclic : IsCyclic (W2.subgroupOf MF) :=
    (Subgroup.subgroupOfEquivOfLe (H := W2) (K := MF) hW2_le_MF).isCyclic.mpr hW2cyc
  have hfixed_cyclic : IsCyclic (fixedPointSubgroup W1 (MF ⧸ H0MF)) := by
    letI : IsCyclic (W2.subgroupOf MF) := hW2sub_cyclic
    rw [hquot_fixed_eq]
    exact isCyclic_of_surjective
      (f := (QuotientGroup.mk' H0MF).subgroupMap (W2.subgroupOf MF))
      (MonoidHom.subgroupMap_surjective (QuotientGroup.mk' H0MF) (W2.subgroupOf MF))
  have hH0MF_ne_top : H0MF ≠ ⊤ := by
    intro htop
    have hMF_le_H0 : MF ≤ H0 := by
      intro x hxMF
      let xMF : MF := ⟨x, hxMF⟩
      have hxH0MF : xMF ∈ H0MF := by
        simp [htop]
      simpa [H0MF, xMF, Subgroup.mem_subgroupOf] using hxH0MF
    exact (not_le_of_gt hH0lt) hMF_le_H0
  haveI : Nontrivial (MF ⧸ H0MF) :=
    (QuotientGroup.nontrivial_iff (N := H0MF)).2 hH0MF_ne_top
  have hquot_gt_one : 1 < Nat.card (MF ⧸ H0MF) :=
    Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  have hfixed_ne_one :
      Nat.card (fixedPointSubgroup W1 (MF ⧸ H0MF)) ≠ 1 := by
    intro hfixed_one
    have hquot_one : Nat.card (MF ⧸ H0MF) = 1 := by
      rw [hquot_formula, hfixed_one]
      simp
    exact (Nat.ne_of_gt hquot_gt_one) hquot_one
  haveI : IsElementaryAbelian p.val (MF ⧸ H0MF) := by
    rcases helem with ⟨_hnormal_elem, helemQ⟩
    simpa [H0MF] using helemQ
  have hfixed_card :
      Nat.card (fixedPointSubgroup W1 (MF ⧸ H0MF)) = p.val :=
    cyclic_subgroup_card_eq_prime_of_elementaryAbelian_sec9
      (p := p) (fixedPointSubgroup W1 (MF ⧸ H0MF))
      hfixed_cyclic hfixed_ne_one
  have hWbar2 :
      Nat.card {x : MF ⧸ H0MF //
        ∀ h : MF, QuotientGroup.mk' H0MF h = x →
          ∀ w : G, w ∈ W1 → ⁅w, (h : G)⁆ ∈ H0} = p.val := by
    calc
      Nat.card {x : MF ⧸ H0MF //
          ∀ h : MF, QuotientGroup.mk' H0MF h = x →
            ∀ w : G, w ∈ W1 → ⁅w, (h : G)⁆ ∈ H0} =
            Nat.card (fixedPointSubgroup W1 (MF ⧸ H0MF)) := by
          simpa [H0MF] using
            quotient_W1_fixedPointSubgroup_card_eq_barW2_subtype_sec9
              MF W1 H0 hH0_inv_W1 hnormal
        _ = p.val := hfixed_card
  have hquot_card : Nat.card (MF ⧸ H0MF) = p.val ^ Nat.card W1 := by
    rw [hquot_formula, hfixed_card]
  exact ⟨by simpa [H0MF] using hWbar2, by simpa [H0MF] using hquot_card⟩

public theorem theorem_9_6_typeII_quotient_cardinality_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 : Subgroup G)
    (p : Nat.Primes) :
    hypothesis_9_2_statement M MF U W1 W2 (Nat.card W1) →
      hoReductionData M MF U W2 H0 p →
        section16TypeII M MF →
          Nat.card (MF ⧸ H0.subgroupOf MF) = p.val ^ Nat.card W1 := by
  classical
  intro h92 hp hII
  have h92Full : hypothesis_9_2_statement M MF U W1 W2 (Nat.card W1) := h92
  have hpFull : hoReductionData M MF U W2 H0 p := hp
  rcases hp with
    ⟨_hH0_le_MF, hMF_le_M, hH0_normal_M, hnormal, hH0lt,
      helem, _htypeIIIIVData⟩
  rcases h92.typePDefinitionData with
    ⟨_hMFsource, _hW1cyc, _hW1ne, ⟨hW1_le_M, _hW1hall⟩,
      _hcompMW1, hUleD, _hUnil, _hW1normU, _hcompDU, _hMFnotcyc,
      _hM2le, _hFitEq, _hFitLeD, hW2le, hW2cyc, _hW2ne,
      _hcentW1, _hnormX⟩
  rcases theorem_9_3_source_action_and_branch_facts_sec9
      M MF U W1 W2 (Nat.card W1) h92Full with
    ⟨haction, hII_CU, _hIIIIV⟩
  rcases haction with ⟨_hcomp, _hfrob, hUW1_norm_MF, hsolvMF, hcopUW1⟩
  have hU_norm_MF : U ≤ Subgroup.normalizer (MF : Set G) :=
    le_sup_left.trans hUW1_norm_MF
  have hW1_norm_MF : W1 ≤ Subgroup.normalizer (MF : Set G) :=
    le_sup_right.trans hUW1_norm_MF
  letI : Subgroup.Normalizes U MF := ⟨hU_norm_MF⟩
  letI : Subgroup.Normalizes W1 MF := ⟨hW1_norm_MF⟩
  have hU_le_M : U ≤ M :=
    hUleD.trans (section12_ambientDerivedSubgroup_le (G := G) (E := M))
  let H0MF : Subgroup MF := H0.subgroupOf MF
  haveI : H0MF.Normal := hnormal
  have hH0_inv_U : IsInvariant U MF H0MF :=
    H0_subgroupOf_MF_isInvariant_under_U_sec9 M MF U H0
      hMF_le_M hU_le_M hH0_normal_M hU_norm_MF
  have hH0_inv_W1 : IsInvariant W1 MF H0MF :=
    H0_subgroupOf_MF_isInvariant_under_U_sec9 M MF W1 H0
      hMF_le_M hW1_le_M hH0_normal_M hW1_norm_MF
  letI : MulDistribMulAction U (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := U) (G := MF) H0MF hH0_inv_U
  letI : MulDistribMulAction W1 (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := W1) (G := MF) H0MF hH0_inv_W1
  have hfixed_point :
      ∀ h : G, h ∈ MF →
        (∀ u : G, u ∈ U → ⁅u, h⁆ ∈ H0) → h ∈ H0 := by
    intro h hhMF hfixed
    have hU_dvd_UW1 : Nat.card U ∣ Nat.card (U ⊔ W1 : Subgroup G) :=
      Subgroup.card_dvd_of_le le_sup_left
    have hcopU : Nat.Coprime (Nat.card U) (Nat.card MF) :=
      (Nat.Coprime.coprime_dvd_right hU_dvd_UW1 hcopUW1).symm
    have hfixMF_bot : fixedPointSubgroup U MF = ⊥ := by
      have hfix_eq :=
        fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn MF U hU_norm_MF
      simpa [hII_CU hII] using hfix_eq
    have hquot_fixed_eq :
        fixedPointSubgroup U (MF ⧸ H0MF) =
          (fixedPointSubgroup U MF).map (QuotientGroup.mk' H0MF) :=
      proposition_1_5_d (G := MF) (A := U) hsolvMF hcopU Set.univ H0MF hH0_inv_U
    let hMF : MF := ⟨h, hhMF⟩
    have hq_fixed : QuotientGroup.mk' H0MF hMF ∈
        fixedPointSubgroup U (MF ⧸ H0MF) := by
      change ∀ u : U, u • QuotientGroup.mk' H0MF hMF =
        QuotientGroup.mk' H0MF hMF
      intro u
      calc
        u • QuotientGroup.mk' H0MF hMF =
            QuotientGroup.mk' H0MF (u • hMF) := by
              simp
        _ = QuotientGroup.mk' H0MF hMF := by
              apply QuotientGroup.eq_iff_div_mem.mpr
              have hcommH0 : ⁅(u : G), h⁆ ∈ H0 := hfixed (u : G) u.property
              have hcommH0MF : ((u • hMF : MF) / hMF) ∈ H0MF := by
                have hval :
                    (((u • hMF : MF) / hMF : MF) : G) = ⁅(u : G), h⁆ := by
                  simp [hMF, div_eq_mul_inv, commutatorElement_def,
                    Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc]
                simpa [H0MF, Subgroup.mem_subgroupOf, hval] using hcommH0
              simpa [div_eq_mul_inv] using hcommH0MF
    have hq_mem_image :
        QuotientGroup.mk' H0MF hMF ∈
          (fixedPointSubgroup U MF).map (QuotientGroup.mk' H0MF) := by
      simpa [hquot_fixed_eq] using hq_fixed
    have hq_one : QuotientGroup.mk' H0MF hMF = 1 := by
      simpa [hfixMF_bot] using hq_mem_image
    have hhH0MF : hMF ∈ H0MF :=
      (QuotientGroup.eq_one_iff (N := H0MF) (x := hMF)).1 hq_one
    simpa [H0MF, Subgroup.mem_subgroupOf, hMF] using hhH0MF
  have hU_fixed_bot : fixedPointSubgroup U (MF ⧸ H0MF) = ⊥ := by
    apply le_antisymm
    · intro x hx
      rcases QuotientGroup.mk'_surjective H0MF x with ⟨h, rfl⟩
      have hcommH0 : ∀ u : G, u ∈ U → ⁅u, (h : G)⁆ ∈ H0 := by
        intro u huU
        let uU : U := ⟨u, huU⟩
        have hfixed_mk :
            uU • QuotientGroup.mk' H0MF h = QuotientGroup.mk' H0MF h := hx uU
        have hq : QuotientGroup.mk' H0MF (uU • h) = QuotientGroup.mk' H0MF h := by
          simpa using hfixed_mk
        have hcommH0MF : ((uU • h : MF) / h) ∈ H0MF :=
          QuotientGroup.eq_iff_div_mem.mp hq
        have hval : ((((uU • h : MF) / h : MF) : G) = ⁅u, (h : G)⁆) := by
          simp [uU, div_eq_mul_inv, commutatorElement_def,
            Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc]
        simpa [H0MF, Subgroup.mem_subgroupOf, hval] using hcommH0MF
      have hhH0 : (h : G) ∈ H0 :=
        hfixed_point (h : G) h.property hcommH0
      have hhH0MF : h ∈ H0MF := by
        simpa [H0MF, Subgroup.mem_subgroupOf] using hhH0
      have hmk_one : QuotientGroup.mk' H0MF h = 1 :=
        (QuotientGroup.eq_one_iff (N := H0MF) (x := h)).2 hhH0MF
      simp [hmk_one]
    · exact bot_le
  have hquot_formula :
      Nat.card (MF ⧸ H0MF) =
        Nat.card (fixedPointSubgroup W1 (MF ⧸ H0MF)) ^ Nat.card W1 := by
    simpa [H0MF] using
      theorem_9_6_quotient_cardinality_formula_of_U_fixed_bot_sec9
        M MF U W1 W2 H0 p h92Full hpFull hnormal
        hH0_inv_U hH0_inv_W1 (by simpa [H0MF] using hU_fixed_bot)
  have hquot_fixed_eq :
      fixedPointSubgroup W1 (MF ⧸ H0MF) =
        (W2.subgroupOf MF).map (QuotientGroup.mk' H0MF) := by
    simpa [H0MF] using
      quotient_W1_fixedPointSubgroup_eq_W2_map_of_hypothesis_9_2_sec9
        M MF U W1 W2 H0 (Nat.card W1) h92Full hnormal hH0_inv_W1
  have hW2_le_MF : W2 ≤ MF := hW2le.trans inf_le_left
  have hW2sub_cyclic : IsCyclic (W2.subgroupOf MF) :=
    (Subgroup.subgroupOfEquivOfLe (H := W2) (K := MF) hW2_le_MF).isCyclic.mpr
      hW2cyc
  have hfixed_cyclic : IsCyclic (fixedPointSubgroup W1 (MF ⧸ H0MF)) := by
    letI : IsCyclic (W2.subgroupOf MF) := hW2sub_cyclic
    rw [hquot_fixed_eq]
    exact isCyclic_of_surjective
      (f := (QuotientGroup.mk' H0MF).subgroupMap (W2.subgroupOf MF))
      (MonoidHom.subgroupMap_surjective (QuotientGroup.mk' H0MF)
        (W2.subgroupOf MF))
  have hH0MF_ne_top : H0MF ≠ ⊤ := by
    intro htop
    have hMF_le_H0 : MF ≤ H0 := by
      intro x hxMF
      let xMF : MF := ⟨x, hxMF⟩
      have hxH0MF : xMF ∈ H0MF := by
        simp [htop]
      simpa [H0MF, xMF, Subgroup.mem_subgroupOf] using hxH0MF
    exact (not_le_of_gt hH0lt) hMF_le_H0
  haveI : Nontrivial (MF ⧸ H0MF) :=
    (QuotientGroup.nontrivial_iff (N := H0MF)).2 hH0MF_ne_top
  have hquot_gt_one : 1 < Nat.card (MF ⧸ H0MF) :=
    Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  have hfixed_ne_one :
      Nat.card (fixedPointSubgroup W1 (MF ⧸ H0MF)) ≠ 1 := by
    intro hfixed_one
    have hquot_one : Nat.card (MF ⧸ H0MF) = 1 := by
      rw [hquot_formula, hfixed_one]
      simp
    exact (Nat.ne_of_gt hquot_gt_one) hquot_one
  haveI : IsElementaryAbelian p.val (MF ⧸ H0MF) := by
    rcases helem with ⟨_hnormal_elem, helemQ⟩
    simpa [H0MF] using helemQ
  have hfixed_card :
      Nat.card (fixedPointSubgroup W1 (MF ⧸ H0MF)) = p.val :=
    cyclic_subgroup_card_eq_prime_of_elementaryAbelian_sec9
      (p := p) (fixedPointSubgroup W1 (MF ⧸ H0MF))
      hfixed_cyclic hfixed_ne_one
  rw [hquot_formula, hfixed_card]

private theorem theorem_9_6_typeII_factor_fixed_bottom_contradiction_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    [Subgroup.Normalizes U MF] [Subgroup.Normalizes W1 MF]
    [Subgroup.Normalizes (U ⊔ W1 : Subgroup G) MF]
    (T : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (S : Finset (Section1.ClassFunction M))
    (p : Nat.Primes) :
    notation_9_5_data M MF U W1 W2 H0 C Cprime T S →
      hoReductionData M MF U W2 H0 p →
        section16TypeII M MF →
          (hnormal : (H0.subgroupOf MF).Normal) →
            (hH0_inv_U : IsInvariant U MF (H0.subgroupOf MF)) →
              (hH0_inv_W1 : IsInvariant W1 MF (H0.subgroupOf MF)) →
                (hH0_inv_UW1 :
                  IsInvariant (U ⊔ W1 : Subgroup G) MF (H0.subgroupOf MF)) →
                  letI : (H0.subgroupOf MF).Normal := hnormal
                  letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
                    quotientMulDistribMulAction (A := U) (G := MF)
                      (H0.subgroupOf MF) hH0_inv_U
                  letI : MulDistribMulAction W1 (MF ⧸ H0.subgroupOf MF) :=
                    quotientMulDistribMulAction (A := W1) (G := MF)
                      (H0.subgroupOf MF) hH0_inv_W1
                  letI : MulDistribMulAction (U ⊔ W1 : Subgroup G)
                      (MF ⧸ H0.subgroupOf MF) :=
                    quotientMulDistribMulAction (A := (U ⊔ W1 : Subgroup G)) (G := MF)
                      (H0.subgroupOf MF) hH0_inv_UW1
                  ∀ L : Subgroup (MF ⧸ H0.subgroupOf MF),
                    (hL_inv_UW1 :
                      IsInvariant (U ⊔ W1 : Subgroup G)
                        (MF ⧸ H0.subgroupOf MF) L) →
                      (hL_inv_W1 : IsInvariant W1 (MF ⧸ H0.subgroupOf MF) L) →
                        letI : IsInvariant (U ⊔ W1 : Subgroup G)
                            (MF ⧸ H0.subgroupOf MF) L := hL_inv_UW1
                        letI : IsInvariant W1 (MF ⧸ H0.subgroupOf MF) L := hL_inv_W1
                        fixedPointSubgroup W1 L = ⊥ →
                          fixedPointSubgroup U (MF ⧸ H0.subgroupOf MF) = ⊥ →
                            L ≠ ⊥ →
                              False := by
  classical
  intro h95 hp _hII hnormal hH0_inv_U hH0_inv_W1 hH0_inv_UW1
    L hL_inv_UW1 hL_inv_W1 hL_W1_fixed_bot hU_fixed_bot hL_ne_bot
  have h95Full : notation_9_5_data M MF U W1 W2 H0 C Cprime T S := h95
  rcases h95 with
    ⟨h92, _hp95, _hC, _hBarU, _hCprimeC, _hCprimeEq, _hDade, _hS⟩
  have h92Full : hypothesis_9_2_statement M MF U W1 W2 (Nat.card W1) := h92
  have hPsource := h92.typePDefinitionData
  have hIItoIVSource := h92.typeIIToIVSourceCondition
  rcases hPsource with
    ⟨_hMFsource, hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD,
      hUnil, _hW1normU, _hcompDU, _hMFnotcyc, _hM2le, _hFitEq, _hFitLeD,
      _hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
  rcases hIItoIVSource with ⟨_hU_ne, hW1primeOrder, _hTI⟩
  rcases hp with
    ⟨_hH0_le_MF, _hMF_le_M, _hH0_normal_M, _hH0_normal_MF, _hH0lt,
      helem, _htypeIIIIVData⟩
  rcases theorem_9_3_source_action_and_branch_facts_sec9
      M MF U W1 W2 (Nat.card W1) h92Full with
    ⟨haction, _hIIbranch, _hIIIIVbranch⟩
  rcases haction with ⟨_hcompUW1, hfrob, _hUW1_norm_MF, _hsolvMF, hcopUW1⟩
  let H0MF : Subgroup MF := H0.subgroupOf MF
  let K : Type u := MF ⧸ H0MF
  let UW1 : Subgroup G := U ⊔ W1
  let W1sub : Subgroup UW1 := W1.subgroupOf UW1
  haveI : H0MF.Normal := hnormal
  letI : MulDistribMulAction U K :=
    quotientMulDistribMulAction (A := U) (G := MF) H0MF hH0_inv_U
  letI : MulDistribMulAction W1 K :=
    quotientMulDistribMulAction (A := W1) (G := MF) H0MF hH0_inv_W1
  letI : MulDistribMulAction UW1 K :=
    quotientMulDistribMulAction (A := UW1) (G := MF) H0MF (by
      simpa [UW1, H0MF] using hH0_inv_UW1)
  letI : IsInvariant UW1 K L := by
    simpa [K, UW1, H0MF] using hL_inv_UW1
  letI : IsInvariant W1 K L := by
    simpa [K, H0MF] using hL_inv_W1
  have hL_W1sub_fixed_eq :
      fixedPointSubgroup (↥W1sub) L = fixedPointSubgroup W1 L := by
    ext x
    constructor
    · intro hx w
      let wUW1 : UW1 := ⟨(w : G), by
        change (w : G) ∈ U ⊔ W1
        exact (le_sup_right : W1 ≤ U ⊔ W1) w.property⟩
      let wSub : W1sub := ⟨wUW1, by
        change wUW1 ∈ W1.subgroupOf UW1
        exact Subgroup.mem_subgroupOf.mpr w.property⟩
      have hx' : wSub • x = x := hx wSub
      change w • x = x at hx'
      exact hx'
    · intro hx wSub
      have hwSub : (wSub : UW1) ∈ W1.subgroupOf UW1 := by
        change (wSub : UW1) ∈ W1sub
        exact wSub.property
      let w : W1 := ⟨((wSub : UW1) : G), Subgroup.mem_subgroupOf.mp hwSub⟩
      have hx' : w • x = x := hx w
      change wSub • x = x at hx'
      exact hx'
  have hL_W1sub_fixed_bot :
      fixedPointSubgroup (↥W1sub) L = ⊥ := by
    simpa [hL_W1sub_fixed_eq] using hL_W1_fixed_bot
  have hUsub_fixed_bot_K :
      fixedPointSubgroup (↥(U.subgroupOf UW1)) K = ⊥ := by
    simpa [K, H0MF, UW1] using
      quotient_U_fixedPointSubgroup_subgroupOf_eq_bot_sec9
        MF U W1 H0 hnormal hH0_inv_U
        (by simpa [UW1, H0MF] using hH0_inv_UW1)
        (by simpa [K, H0MF] using hU_fixed_bot)
  have hUsub_fixed_bot_L :
      fixedPointSubgroup (↥(U.subgroupOf UW1)) L = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hxK : ((x : L) : K) ∈ fixedPointSubgroup (↥(U.subgroupOf UW1)) K := by
        intro u
        have hx' : u • x = x := hx u
        exact congrArg Subtype.val hx'
      have hxK_bot : ((x : L) : K) ∈ (⊥ : Subgroup K) := by
        rw [← hUsub_fixed_bot_K]
        exact hxK
      have hxK_one : ((x : L) : K) = 1 :=
        Subgroup.mem_bot.mp hxK_bot
      exact Subgroup.mem_bot.mpr (Subtype.ext hxK_one)
    · exact bot_le
  have hUW1_solv : IsSolvable UW1 := by
    simpa [UW1] using
      solvable_of_nilpotent_frobenius_kernel_cyclic_complement_sec9
        U W1 hUnil hW1cyc hfrob
  have hW1sub_card : Nat.card W1sub = Nat.card W1 :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := W1) (K := UW1)
        (by
          change W1 ≤ U ⊔ W1
          exact le_sup_right)).toEquiv
  have hW1_prime : Nat.Prime (Nat.card W1) := by
    rcases hW1primeOrder with ⟨q, hq⟩
    simpa [hq] using q.property
  have hW1sub_prime : Nat.Prime (Nat.card W1sub) := by
    simpa [hW1sub_card] using hW1_prime
  have hfixR :
      ∀ x : W1sub, x ≠ 1 →
        fixedPointSubgroup (↥(Subgroup.zpowers (x : UW1))) L =
          fixedPointSubgroup (↥W1sub) L := by
    intro x hx
    have hx_top : Subgroup.zpowers x = (⊤ : Subgroup W1sub) :=
      zpowers_eq_top_of_prime_card_of_ne_one hW1sub_prime hx
    have hmap_zpow :
        (Subgroup.zpowers x).map W1sub.subtype =
          Subgroup.zpowers (x : UW1) := by
      simp
    have htop_map : (⊤ : Subgroup W1sub).map W1sub.subtype = W1sub := by
      ext y
      constructor
      · intro hy
        rcases Subgroup.mem_map.mp hy with ⟨z, _hz, rfl⟩
        exact z.property
      · intro hy
        exact Subgroup.mem_map.mpr ⟨⟨y, hy⟩, by simp, rfl⟩
    have hzpow_eq : Subgroup.zpowers (x : UW1) = W1sub := by
      calc
        Subgroup.zpowers (x : UW1) =
            (Subgroup.zpowers x).map W1sub.subtype := hmap_zpow.symm
        _ = (⊤ : Subgroup W1sub).map W1sub.subtype := by rw [hx_top]
        _ = W1sub := htop_map
    rw [hzpow_eq]
  haveI : Fact p.val.Prime := ⟨p.property⟩
  have hK_elem : IsElementaryAbelian p.val K := by
    rcases helem with ⟨_hnormal_elem, helemQ⟩
    simpa [K, H0MF] using helemQ
  letI : IsElementaryAbelian p.val K := hK_elem
  have hK_nil : Group.IsNilpotent K := by infer_instance
  have hL_nil : Group.IsNilpotent L := by
    letI : Group.IsNilpotent K := hK_nil
    infer_instance
  have hfrob_sub :
      IsFrobeniusGroupWithKernelComplement (U.subgroupOf UW1) W1sub := by
    simpa [section12FrobeniusJoinWithKernel, UW1, W1sub] using hfrob
  have hquot_dvd_MF : Nat.card K ∣ Nat.card MF := by
    simpa [K, H0MF] using Subgroup.card_quotient_dvd_card H0MF
  have hL_dvd_K : Nat.card L ∣ Nat.card K :=
    Subgroup.card_subgroup_dvd_card L
  have hL_dvd_MF : Nat.card L ∣ Nat.card MF := hL_dvd_K.trans hquot_dvd_MF
  have hcopL : Nat.Coprime (Nat.card UW1) (Nat.card L) :=
    Nat.Coprime.coprime_dvd_right hL_dvd_MF (by
      simpa [UW1] using hcopUW1.symm)
  haveI : Nontrivial L :=
    (Subgroup.nontrivial_iff_ne_bot (H := L)).2 hL_ne_bot
  have hcard_formula :
      Nat.card L = Nat.card (fixedPointSubgroup (↥W1sub) L) ^ Nat.card W1sub :=
    theorem_3_10_b (G := UW1) (K := U.subgroupOf UW1) (R := W1sub) (M := L)
      hfrob_sub hUW1_solv hL_nil hcopL hUsub_fixed_bot_L hfixR
  have hcard_L_one : Nat.card L = 1 := by
    rw [hcard_formula, hL_W1sub_fixed_bot]
    simp
  exact hL_ne_bot ((Subgroup.card_eq_one (H := L)).1 hcard_L_one)

private theorem quotient_isInvariant_W1_of_isInvariant_UW1_sec9
    {G : Type u} [Group G] [Finite G]
    (MF U W1 H0 : Subgroup G)
    [Subgroup.Normalizes W1 MF]
    [Subgroup.Normalizes (U ⊔ W1 : Subgroup G) MF]
    [hnormal : (H0.subgroupOf MF).Normal]
    (hH0_inv_W1 : IsInvariant W1 MF (H0.subgroupOf MF))
    (hH0_inv_UW1 : IsInvariant (U ⊔ W1 : Subgroup G) MF (H0.subgroupOf MF))
    (Q : Subgroup (MF ⧸ H0.subgroupOf MF)) :
    (letI : MulDistribMulAction (U ⊔ W1 : Subgroup G)
        (MF ⧸ H0.subgroupOf MF) :=
      quotientMulDistribMulAction (A := (U ⊔ W1 : Subgroup G)) (G := MF)
        (H0.subgroupOf MF) hH0_inv_UW1;
      IsInvariant (U ⊔ W1 : Subgroup G) (MF ⧸ H0.subgroupOf MF) Q) →
    (letI : MulDistribMulAction W1 (MF ⧸ H0.subgroupOf MF) :=
      quotientMulDistribMulAction (A := W1) (G := MF)
        (H0.subgroupOf MF) hH0_inv_W1;
      IsInvariant W1 (MF ⧸ H0.subgroupOf MF) Q) := by
  classical
  intro hQ_inv_UW1
  let H0MF : Subgroup MF := H0.subgroupOf MF
  let UW1 : Subgroup G := U ⊔ W1
  haveI : H0MF.Normal := hnormal
  letI : MulDistribMulAction W1 (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := W1) (G := MF) H0MF hH0_inv_W1
  letI : MulDistribMulAction UW1 (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := UW1) (G := MF) H0MF (by
      simpa [UW1] using hH0_inv_UW1)
  letI : IsInvariant UW1 (MF ⧸ H0MF) Q := by
    simpa [H0MF, UW1] using hQ_inv_UW1
  constructor
  intro w x
  have hiff :=
    IsInvariant.invariant (A := UW1) (G := MF ⧸ H0MF) (H := Q)
      (a := ⟨(w : G), by
        change (w : G) ∈ U ⊔ W1
        exact (le_sup_right : W1 ≤ U ⊔ W1) w.property⟩) x
  change x ∈ Q ↔ w • x ∈ Q at hiff
  exact hiff

private theorem theorem_9_6_typeII_maschke_factor_fixed_choice_source_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    [Subgroup.Normalizes U MF] [Subgroup.Normalizes W1 MF]
    [Subgroup.Normalizes (U ⊔ W1 : Subgroup G) MF]
    (T : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (S : Finset (Section1.ClassFunction M))
    (p : Nat.Primes) :
    notation_9_5_data M MF U W1 W2 H0 C Cprime T S →
      hoReductionData M MF U W2 H0 p →
        section16TypeII M MF →
          (hnormal : (H0.subgroupOf MF).Normal) →
            (hH0_inv_U : IsInvariant U MF (H0.subgroupOf MF)) →
              (hH0_inv_W1 : IsInvariant W1 MF (H0.subgroupOf MF)) →
                (hH0_inv_UW1 :
                  IsInvariant (U ⊔ W1 : Subgroup G) MF (H0.subgroupOf MF)) →
                  letI : (H0.subgroupOf MF).Normal := hnormal
                  letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
                    quotientMulDistribMulAction (A := U) (G := MF)
                      (H0.subgroupOf MF) hH0_inv_U
                  letI : MulDistribMulAction W1 (MF ⧸ H0.subgroupOf MF) :=
                    quotientMulDistribMulAction (A := W1) (G := MF)
                      (H0.subgroupOf MF) hH0_inv_W1
                  letI : MulDistribMulAction (U ⊔ W1 : Subgroup G)
                      (MF ⧸ H0.subgroupOf MF) :=
                    quotientMulDistribMulAction (A := (U ⊔ W1 : Subgroup G)) (G := MF)
                      (H0.subgroupOf MF) hH0_inv_UW1
                  ∀ Q Qcompl : Subgroup (MF ⧸ H0.subgroupOf MF),
                    IsCompl Q Qcompl →
                      (hQ_inv_UW1 :
                        IsInvariant (U ⊔ W1 : Subgroup G)
                          (MF ⧸ H0.subgroupOf MF) Q) →
                        (hQcompl_inv_UW1 :
                          IsInvariant (U ⊔ W1 : Subgroup G)
                            (MF ⧸ H0.subgroupOf MF) Qcompl) →
                          (hQ_inv_W1 :
                            IsInvariant W1 (MF ⧸ H0.subgroupOf MF) Q) →
                            (hQcompl_inv_W1 :
                              IsInvariant W1 (MF ⧸ H0.subgroupOf MF) Qcompl) →
                              fixedPointSubgroup U (MF ⧸ H0.subgroupOf MF) = ⊥ →
                                Q ≠ ⊥ →
                                  Qcompl ≠ ⊥ →
                                    letI : IsInvariant W1
                                        (MF ⧸ H0.subgroupOf MF) Q := hQ_inv_W1
                                    letI : IsInvariant W1
                                        (MF ⧸ H0.subgroupOf MF) Qcompl := hQcompl_inv_W1
                                    fixedPointSubgroup W1 Q = ⊥ ∨
                                      fixedPointSubgroup W1 Qcompl = ⊥ := by
  classical
  intro h95 hp _hII hnormal hH0_inv_U hH0_inv_W1 hH0_inv_UW1
    Q Qcompl hQcompl _hQ_inv_UW1 _hQcompl_inv_UW1
    hQ_inv_W1 hQcompl_inv_W1 _hU_fixed_bot _hQ_ne_bot _hQcompl_ne_bot
  let H0MF : Subgroup MF := H0.subgroupOf MF
  let K : Type u := MF ⧸ H0MF
  haveI : H0MF.Normal := hnormal
  letI : MulDistribMulAction W1 K :=
    quotientMulDistribMulAction (A := W1) (G := MF) H0MF hH0_inv_W1
  letI : IsInvariant W1 K Q := by
    simpa [K, H0MF] using hQ_inv_W1
  letI : IsInvariant W1 K Qcompl := by
    simpa [K, H0MF] using hQcompl_inv_W1
  by_cases hQ_fixed_bot : fixedPointSubgroup W1 Q = ⊥
  · exact Or.inl hQ_fixed_bot
  by_cases hQcompl_fixed_bot : fixedPointSubgroup W1 Qcompl = ⊥
  · exact Or.inr hQcompl_fixed_bot
  exfalso
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp hQ_fixed_bot with ⟨x, hx_ne⟩
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp hQcompl_fixed_bot with ⟨y, hy_ne⟩
  have h92Full : hypothesis_9_2_statement M MF U W1 W2 (Nat.card W1) := h95.hypothesis92
  rcases h95 with
    ⟨h92, _hp95, _hC, _hBarU, _hCprimeC, _hCprimeEq, _hDade, _hS⟩
  have hPsource := h92.typePDefinitionData
  rcases hPsource with
    ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD,
      _hUnil, _hW1normU, _hcompDU, _hMFnotcyc, _hM2le, _hFitEq,
      _hFitLeD, hW2le, hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
  rcases hp with
    ⟨_hH0_le_MF, _hMF_le_M, _hH0_normal_M, _hH0_normal_MF, _hH0lt,
      helem, _htypeIIIIVData⟩
  rcases theorem_9_3_source_action_and_branch_facts_sec9
      M MF U W1 W2 (Nat.card W1) h92Full with
    ⟨haction, _hIIcentralizer, _hIIIIV⟩
  rcases haction with ⟨_hcomp, _hfrob, hUW1_norm_MF, hsolvMF, hcopUW1⟩
  have hW1_norm_MF : W1 ≤ Subgroup.normalizer (MF : Set G) :=
    le_sup_right.trans hUW1_norm_MF
  letI : Subgroup.Normalizes W1 MF := ⟨hW1_norm_MF⟩
  have hW1_dvd_UW1 : Nat.card W1 ∣ Nat.card (U ⊔ W1 : Subgroup G) :=
    Subgroup.card_dvd_of_le le_sup_right
  have hcopW1 : Nat.Coprime (Nat.card W1) (Nat.card MF) :=
    (Nat.Coprime.coprime_dvd_right hW1_dvd_UW1 hcopUW1).symm
  have hquot_fixed_eq :
      fixedPointSubgroup W1 K =
        (W2.subgroupOf MF).map (QuotientGroup.mk' H0MF) := by
    simpa [K, H0MF] using
      quotient_W1_fixedPointSubgroup_eq_W2_map_of_hypothesis_9_2_sec9
        M MF U W1 W2 H0 (Nat.card W1) h92Full hnormal hH0_inv_W1
  have hW2_le_MF : W2 ≤ MF := hW2le.trans inf_le_left
  have hW2sub_cyclic : IsCyclic (W2.subgroupOf MF) :=
    (Subgroup.subgroupOfEquivOfLe (H := W2) (K := MF) hW2_le_MF).isCyclic.mpr
      hW2cyc
  have htotal_fixed_cyclic : IsCyclic (fixedPointSubgroup W1 K) := by
    letI : IsCyclic (W2.subgroupOf MF) := hW2sub_cyclic
    change IsCyclic (fixedPointSubgroup W1 K)
    rw [hquot_fixed_eq]
    exact isCyclic_of_surjective
      (f := (QuotientGroup.mk' H0MF).subgroupMap (W2.subgroupOf MF))
      (MonoidHom.subgroupMap_surjective (QuotientGroup.mk' H0MF)
        (W2.subgroupOf MF))
  haveI : Fact p.val.Prime := ⟨p.property⟩
  have hK_elem : IsElementaryAbelian p.val K := by
    rcases helem with ⟨_hnormal_elem, helemQ⟩
    simpa [K, H0MF] using helemQ
  letI : IsElementaryAbelian p.val K := hK_elem
  let xK : K := ((x : fixedPointSubgroup W1 Q) : Q)
  have hxK_mem_fixed : xK ∈ fixedPointSubgroup W1 K := by
    change ∀ w : W1, w • xK = xK
    intro w
    have hxw : w • ((x : fixedPointSubgroup W1 Q) : Q) =
        ((x : fixedPointSubgroup W1 Q) : Q) := x.property w
    have hxwK :
        w • (((x : fixedPointSubgroup W1 Q) : Q) : K) =
          (((x : fixedPointSubgroup W1 Q) : Q) : K) := by
      exact congrArg (fun z : Q => (z : K)) hxw
    simpa [xK] using hxwK
  let xF : fixedPointSubgroup W1 K := ⟨xK, hxK_mem_fixed⟩
  have hxF_ne : xF ≠ 1 := by
    intro hxF
    apply hx_ne
    have hxK_one : xK = 1 := by
      simpa [xF] using
        congrArg (fun z : fixedPointSubgroup W1 K => (z : K)) hxF
    have hxQ_one : ((x : fixedPointSubgroup W1 Q) : Q) = 1 := by
      apply Subtype.ext
      simpa [xK] using hxK_one
    exact Subtype.ext hxQ_one
  have htotal_fixed_ne_bot : fixedPointSubgroup W1 K ≠ ⊥ :=
    Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨xF, hxF_ne⟩
  have htotal_fixed_ne_one : Nat.card (fixedPointSubgroup W1 K) ≠ 1 := by
    intro hcard
    exact htotal_fixed_ne_bot
      ((Subgroup.card_eq_one (H := fixedPointSubgroup W1 K)).1 hcard)
  have htotal_fixed_card :
      Nat.card (fixedPointSubgroup W1 K) = p.val :=
    cyclic_subgroup_card_eq_prime_of_elementaryAbelian_sec9
      (p := p) (fixedPointSubgroup W1 K) htotal_fixed_cyclic
      htotal_fixed_ne_one
  have htotal_fixed_prime : Nat.Prime (Nat.card (fixedPointSubgroup W1 K)) := by
    rw [htotal_fixed_card]
    exact p.property
  let yK : K := ((y : fixedPointSubgroup W1 Qcompl) : Qcompl)
  have hyK_mem_fixed : yK ∈ fixedPointSubgroup W1 K := by
    change ∀ w : W1, w • yK = yK
    intro w
    have hyw : w • ((y : fixedPointSubgroup W1 Qcompl) : Qcompl) =
        ((y : fixedPointSubgroup W1 Qcompl) : Qcompl) := y.property w
    have hywK :
        w • (((y : fixedPointSubgroup W1 Qcompl) : Qcompl) : K) =
          (((y : fixedPointSubgroup W1 Qcompl) : Qcompl) : K) := by
      exact congrArg (fun z : Qcompl => (z : K)) hyw
    simpa [yK] using hywK
  let yF : fixedPointSubgroup W1 K := ⟨yK, hyK_mem_fixed⟩
  have hxF_zpowers_top :
      Subgroup.zpowers xF = (⊤ : Subgroup (fixedPointSubgroup W1 K)) :=
    zpowers_eq_top_of_prime_card_of_ne_one htotal_fixed_prime hxF_ne
  have hyF_mem_zpowers : yF ∈ Subgroup.zpowers xF := by
    simp [hxF_zpowers_top]
  rcases Subgroup.mem_zpowers_iff.mp hyF_mem_zpowers with ⟨n, hyn⟩
  have hyK_eq : yK = xK ^ n := by
    have hval := congrArg (fun z : fixedPointSubgroup W1 K => (z : K)) hyn
    simpa [xF, yF, xK, yK] using hval.symm
  have hxK_mem_Q : xK ∈ Q := by
    simp [xK]
  have hyK_mem_Q : yK ∈ Q := by
    have hxpow_mem : xK ^ n ∈ Q := Q.zpow_mem hxK_mem_Q n
    simpa [hyK_eq] using hxpow_mem
  have hyK_mem_Qcompl : yK ∈ Qcompl := by
    simp [yK]
  have hyK_inf : yK ∈ Q ⊓ Qcompl := ⟨hyK_mem_Q, hyK_mem_Qcompl⟩
  have hyK_bot : yK ∈ (⊥ : Subgroup K) := by
    rw [← hQcompl.inf_eq_bot]
    exact hyK_inf
  have hyK_one : yK = 1 := Subgroup.mem_bot.mp hyK_bot
  apply hy_ne
  exact Subtype.ext (Subtype.ext hyK_one)

private theorem theorem_9_6_typeII_maschke_factor_contradiction_source_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    [Subgroup.Normalizes U MF] [Subgroup.Normalizes W1 MF]
    [Subgroup.Normalizes (U ⊔ W1 : Subgroup G) MF]
    (T : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (S : Finset (Section1.ClassFunction M))
    (p : Nat.Primes) :
    notation_9_5_data M MF U W1 W2 H0 C Cprime T S →
      hoReductionData M MF U W2 H0 p →
        section16TypeII M MF →
          (hnormal : (H0.subgroupOf MF).Normal) →
            (hH0_inv_U : IsInvariant U MF (H0.subgroupOf MF)) →
              (hH0_inv_W1 : IsInvariant W1 MF (H0.subgroupOf MF)) →
                (hH0_inv_UW1 :
                  IsInvariant (U ⊔ W1 : Subgroup G) MF (H0.subgroupOf MF)) →
                  letI : (H0.subgroupOf MF).Normal := hnormal
                  letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
                    quotientMulDistribMulAction (A := U) (G := MF)
                      (H0.subgroupOf MF) hH0_inv_U
                  letI : MulDistribMulAction (U ⊔ W1 : Subgroup G)
                      (MF ⧸ H0.subgroupOf MF) :=
                    quotientMulDistribMulAction (A := (U ⊔ W1 : Subgroup G)) (G := MF)
                      (H0.subgroupOf MF) hH0_inv_UW1
                  ∀ Q Qcompl : Subgroup (MF ⧸ H0.subgroupOf MF),
                    IsCompl Q Qcompl →
                      IsInvariant (U ⊔ W1 : Subgroup G) (MF ⧸ H0.subgroupOf MF) Q →
                        IsInvariant (U ⊔ W1 : Subgroup G)
                            (MF ⧸ H0.subgroupOf MF) Qcompl →
                          fixedPointSubgroup U (MF ⧸ H0.subgroupOf MF) = ⊥ →
                            Q ≠ ⊥ →
                            Qcompl ≠ ⊥ →
                                False := by
  classical
  intro h95 hp hII hnormal hH0_inv_U hH0_inv_W1 hH0_inv_UW1
    Q Qcompl hQcompl hQ_inv_UW1 hQcompl_inv_UW1 hU_fixed_bot hQ_ne_bot hQcompl_ne_bot
  let H0MF : Subgroup MF := H0.subgroupOf MF
  haveI : H0MF.Normal := hnormal
  letI : MulDistribMulAction U (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := U) (G := MF) H0MF hH0_inv_U
  letI : MulDistribMulAction W1 (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := W1) (G := MF) H0MF hH0_inv_W1
  letI : MulDistribMulAction (U ⊔ W1 : Subgroup G) (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := (U ⊔ W1 : Subgroup G)) (G := MF)
      H0MF hH0_inv_UW1
  have hQ_inv_W1 : IsInvariant W1 (MF ⧸ H0MF) Q := by
    simpa [H0MF] using
      quotient_isInvariant_W1_of_isInvariant_UW1_sec9 MF U W1 H0
        hH0_inv_W1 hH0_inv_UW1 Q
        (by simpa [H0MF] using hQ_inv_UW1)
  have hQcompl_inv_W1 : IsInvariant W1 (MF ⧸ H0MF) Qcompl := by
    simpa [H0MF] using
      quotient_isInvariant_W1_of_isInvariant_UW1_sec9 MF U W1 H0
        hH0_inv_W1 hH0_inv_UW1 Qcompl
        (by simpa [H0MF] using hQcompl_inv_UW1)
  rcases theorem_9_6_typeII_maschke_factor_fixed_choice_source_sec9
      M MF U W1 W2 H0 C Cprime T S p
      h95 hp hII hnormal hH0_inv_U hH0_inv_W1 hH0_inv_UW1
      Q Qcompl hQcompl hQ_inv_UW1 hQcompl_inv_UW1
      hQ_inv_W1 hQcompl_inv_W1 hU_fixed_bot hQ_ne_bot hQcompl_ne_bot with
    hQ_fixed_bot | hQcompl_fixed_bot
  · exact theorem_9_6_typeII_factor_fixed_bottom_contradiction_sec9
      M MF U W1 W2 H0 C Cprime T S p
      h95 hp hII hnormal hH0_inv_U hH0_inv_W1 hH0_inv_UW1
      Q hQ_inv_UW1 hQ_inv_W1 hQ_fixed_bot hU_fixed_bot hQ_ne_bot
  · exact theorem_9_6_typeII_factor_fixed_bottom_contradiction_sec9
      M MF U W1 W2 H0 C Cprime T S p
      h95 hp hII hnormal hH0_inv_U hH0_inv_W1 hH0_inv_UW1
      Qcompl hQcompl_inv_UW1 hQcompl_inv_W1 hQcompl_fixed_bot
      hU_fixed_bot hQcompl_ne_bot

private theorem theorem_9_6_typeII_quotient_subgroup_dichotomy_source_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (T : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (S : Finset (Section1.ClassFunction M))
    (p : Nat.Primes) :
    notation_9_5_data M MF U W1 W2 H0 C Cprime T S →
      hoReductionData M MF U W2 H0 p →
        section16TypeII M MF →
          (hnormal : (H0.subgroupOf MF).Normal) →
            letI : (H0.subgroupOf MF).Normal := hnormal
            ∀ Q : Subgroup (MF ⧸ H0.subgroupOf MF),
              quotientSubgroupNormalizedBy MF H0 U Q →
                quotientSubgroupNormalizedBy MF H0 W1 Q →
                  Q = ⊥ ∨ Q = ⊤ := by
  classical
  intro h95 hp hII hnormal Q hQ_norm_U hQ_norm_W1
  have h95Full : notation_9_5_data M MF U W1 W2 H0 C Cprime T S := h95
  have hpFull : hoReductionData M MF U W2 H0 p := hp
  rcases h95 with
    ⟨h92, _hp95, _hC, _hBarU, _hCprimeC, _hCprimeEq, _hDade, _hS⟩
  have h92Full : hypothesis_9_2_statement M MF U W1 W2 (Nat.card W1) := h92
  have hPsource := h92.typePDefinitionData
  rcases hPsource with
    ⟨_hMFsource, _hW1cyc, _hW1ne, ⟨hW1_le_M, _hW1hall⟩,
      _hcompMW1, hUleD, _hUnil, _hW1normU, _hcompDU, _hMFnotcyc,
      _hM2le, _hFitEq, _hFitLeD, _hW2le, _hW2cyc, _hW2ne,
      _hcentW1, _hnormX⟩
  rcases hp with
    ⟨_hH0_le_MF, hMF_le_M, hH0_normal_M, _hH0_normal_MF, _hH0lt,
      _helem, _htypeIIIIVData⟩
  rcases theorem_9_3_source_action_and_branch_facts_sec9
      M MF U W1 W2 (Nat.card W1) h92Full with
    ⟨haction, _hIIbranch, _hIIIIVbranch⟩
  rcases haction with ⟨_hcompUW1, _hfrobUW1, hUW1_norm_MF, _hsolvMF, _hcopUW1⟩
  have hU_norm_MF : U ≤ Subgroup.normalizer (MF : Set G) :=
    le_sup_left.trans hUW1_norm_MF
  have hW1_norm_MF : W1 ≤ Subgroup.normalizer (MF : Set G) :=
    le_sup_right.trans hUW1_norm_MF
  letI : Subgroup.Normalizes U MF := ⟨hU_norm_MF⟩
  letI : Subgroup.Normalizes W1 MF := ⟨hW1_norm_MF⟩
  have hU_le_M : U ≤ M :=
    hUleD.trans (section12_ambientDerivedSubgroup_le (G := G) (E := M))
  let UW1 : Subgroup G := U ⊔ W1
  letI : Subgroup.Normalizes UW1 MF := ⟨by simpa [UW1] using hUW1_norm_MF⟩
  have hUW1_le_M : UW1 ≤ M := by
    dsimp [UW1]
    exact sup_le hU_le_M hW1_le_M
  have hH0_inv_U : IsInvariant U MF (H0.subgroupOf MF) :=
    H0_subgroupOf_MF_isInvariant_under_U_sec9 M MF U H0
      hMF_le_M hU_le_M hH0_normal_M hU_norm_MF
  have hH0_inv_W1 : IsInvariant W1 MF (H0.subgroupOf MF) :=
    H0_subgroupOf_MF_isInvariant_under_U_sec9 M MF W1 H0
      hMF_le_M hW1_le_M hH0_normal_M hW1_norm_MF
  have hH0_inv_UW1 : IsInvariant UW1 MF (H0.subgroupOf MF) :=
    H0_subgroupOf_MF_isInvariant_under_U_sec9 M MF UW1 H0
      hMF_le_M hUW1_le_M hH0_normal_M (by simpa [UW1] using hUW1_norm_MF)
  let H0MF : Subgroup MF := H0.subgroupOf MF
  haveI : H0MF.Normal := hnormal
  letI : MulDistribMulAction U (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := U) (G := MF) H0MF hH0_inv_U
  letI : MulDistribMulAction W1 (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := W1) (G := MF) H0MF hH0_inv_W1
  letI : MulDistribMulAction UW1 (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := UW1) (G := MF) H0MF hH0_inv_UW1
  have hQ_inv_U : IsInvariant U (MF ⧸ H0MF) Q := by
    simpa [H0MF] using
      isInvariant_of_quotientSubgroupNormalizedBy_sec9 MF H0 U
        hH0_inv_U Q hQ_norm_U
  have hQ_inv_W1 : IsInvariant W1 (MF ⧸ H0MF) Q := by
    simpa [H0MF] using
      isInvariant_of_quotientSubgroupNormalizedBy_sec9 MF H0 W1
        hH0_inv_W1 Q hQ_norm_W1
  have hQ_inv_UW1 : IsInvariant UW1 (MF ⧸ H0MF) Q := by
    simpa [H0MF, UW1] using
      quotient_isInvariant_sup_of_isInvariant_left_right_sec9
        MF U W1 H0 hH0_inv_U hH0_inv_W1 hH0_inv_UW1 Q
        (by simpa [H0MF] using hQ_inv_U)
        (by simpa [H0MF] using hQ_inv_W1)
  have hU_fixed_bot : fixedPointSubgroup U (MF ⧸ H0MF) = ⊥ := by
    simpa [H0MF] using
      theorem_9_6_typeII_quotient_U_fixed_eq_bot_sec9
        M MF U W1 W2 H0 C Cprime T S p h95Full hpFull hII hnormal hH0_inv_U
  by_cases hQ_bot : Q = ⊥
  · exact Or.inl hQ_bot
  by_cases hQ_top : Q = ⊤
  · exact Or.inr hQ_top
  haveI : Fact p.val.Prime := ⟨p.property⟩
  have hK_elem : IsElementaryAbelian p.val (MF ⧸ H0MF) := by
    rcases _helem with ⟨_hnormal_elem, helemQ⟩
    simpa [H0MF] using helemQ
  letI : IsElementaryAbelian p.val (MF ⧸ H0MF) := hK_elem
  have hH0MF_ne_top : H0MF ≠ ⊤ := by
    intro htop
    have hMF_le_H0 : MF ≤ H0 := by
      intro x hxMF
      let xMF : MF := ⟨x, hxMF⟩
      have hxH0MF : xMF ∈ H0MF := by
        simp [htop]
      simpa [H0MF, xMF, Subgroup.mem_subgroupOf] using hxH0MF
    exact (not_le_of_gt _hH0lt) hMF_le_H0
  haveI : Nontrivial (MF ⧸ H0MF) :=
    (QuotientGroup.nontrivial_iff (N := H0MF)).2 hH0MF_ne_top
  obtain ⟨n, hncard⟩ :=
    (IsElementaryAbelian.isPGroup p.val (MF ⧸ H0MF)).exists_card_eq
  have hnpos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    have hcard_one : Nat.card (MF ⧸ H0MF) = 1 := by
      simpa [hn0] using hncard
    exact (Nat.ne_of_gt (Finite.one_lt_card_iff_nontrivial.mpr inferInstance)) hcard_one
  have hp_dvd_K : p.val ∣ Nat.card (MF ⧸ H0MF) := by
    rw [hncard]
    exact dvd_pow_self p.val hnpos.ne'
  have hquot_dvd_MF : Nat.card (MF ⧸ H0MF) ∣ Nat.card MF :=
    Subgroup.card_quotient_dvd_card H0MF
  have hp_dvd_MF : p.val ∣ Nat.card MF := hp_dvd_K.trans hquot_dvd_MF
  have hcop_p_UW1 : Nat.Coprime p.val (Nat.card UW1) :=
    Nat.Coprime.of_dvd_left hp_dvd_MF (by simpa [UW1] using _hcopUW1)
  letI : IsInvariant UW1 (MF ⧸ H0MF) Q := hQ_inv_UW1
  obtain ⟨Qcompl, hQcompl, hQcompl_inv⟩ :=
    exists_isCompl_isInvariant_of_elementaryAbelian_coprime
      (G := MF ⧸ H0MF) (A := UW1) (p := p.val) hcop_p_UW1 Q
  have hQcompl_ne_bot : Qcompl ≠ ⊥ := by
    intro hQcompl_bot
    exact hQ_top (by simpa [hQcompl_bot] using hQcompl.sup_eq_top)
  exact False.elim
    (theorem_9_6_typeII_maschke_factor_contradiction_source_sec9
      M MF U W1 W2 H0 C Cprime T S p
      h95Full hpFull hII hnormal hH0_inv_U hH0_inv_W1
      (by simpa [UW1] using hH0_inv_UW1)
      Q Qcompl hQcompl
      (by simpa [H0MF, UW1] using hQ_inv_UW1)
      (by simpa [H0MF, UW1] using hQcompl_inv)
      (by simpa [H0MF] using hU_fixed_bot)
      hQ_bot hQcompl_ne_bot)

private theorem theorem_9_6_typeII_chief_factor_maximal_source_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (T : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (S : Finset (Section1.ClassFunction M))
    (p : Nat.Primes) :
    notation_9_5_data M MF U W1 W2 H0 C Cprime T S →
      hoReductionData M MF U W2 H0 p →
        section16TypeII M MF →
          (hnormal : (H0.subgroupOf MF).Normal) →
            ∀ N : Subgroup M, N.Normal →
              H0.subgroupOf M ≤ N →
                N ≤ MF.subgroupOf M →
                  N = H0.subgroupOf M ∨ N = MF.subgroupOf M := by
  classical
  intro h95 hp hII hnormal N hN_normal hH0_le_N hN_le_MF
  have h95Full : notation_9_5_data M MF U W1 W2 H0 C Cprime T S := h95
  have hpFull : hoReductionData M MF U W2 H0 p := hp
  rcases h95 with
    ⟨h92, _hp95, _hC, _hBarU, _hCprimeC, _hCprimeEq, _hDade, _hS⟩
  have h92Full : hypothesis_9_2_statement M MF U W1 W2 (Nat.card W1) := h92
  have hMFsource := h92.mf
  have hPdata := h92.typeP
  have hPsource := h92.typePDefinitionData
  have hIItoIVsource := h92.typeIIToIVSourceCondition
  have hIIsource := h92.typeIISource
  have hIIIsource := h92.typeIIISource
  have hIVsource := h92.typeIVSource
  rcases hMFsource with
    ⟨⟨_hMF_le_M_source, _hMF_normal_M, _hMFnil, _hMFhall⟩, _hMFmax⟩
  rcases hp with
    ⟨hH0_le_MF, hMF_le_M, hH0_normal_M, _hH0_normal_MF, _hH0lt,
      _helem, _htypeIIIIVData⟩
  rcases hPsource with
    ⟨_hMFsourceP, _hW1cyc, _hW1ne, ⟨hW1_le_M, _hW1hall⟩,
      _hcompMW1, hUleD, _hUnil, hW1normU, _hcompDU, _hMFnotcyc,
      _hM2le, _hFitEq, _hFitLeD, _hW2le, _hW2cyc, _hW2ne,
      _hcentW1, _hnormX⟩
  let H0MF : Subgroup MF := H0.subgroupOf MF
  haveI : H0MF.Normal := hnormal
  let Q : Subgroup (MF ⧸ H0MF) :=
    intermediateQuotientSubgroup_sec9 M MF H0 N hMF_le_M
  have hU_le_M : U ≤ M :=
    hUleD.trans (section12_ambientDerivedSubgroup_le (G := G) (E := M))
  rcases theorem_9_3_source_action_and_branch_facts_sec9
      M MF U W1 W2 (Nat.card W1) h92Full with
    ⟨haction, _hIIbranch, _hIIIIVbranch⟩
  rcases haction with ⟨_hcompUW1, _hfrobUW1, hUW1_norm_MF, _hsolvMF, _hcopUW1⟩
  have hU_norm_MF : U ≤ Subgroup.normalizer (MF : Set G) :=
    le_sup_left.trans hUW1_norm_MF
  have hW1_norm_MF : W1 ≤ Subgroup.normalizer (MF : Set G) :=
    le_sup_right.trans hUW1_norm_MF
  letI : Subgroup.Normalizes U MF := ⟨hU_norm_MF⟩
  letI : Subgroup.Normalizes W1 MF := ⟨hW1_norm_MF⟩
  have hQ_norm_U : quotientSubgroupNormalizedBy MF H0 U Q := by
    simpa [Q, H0MF] using
      intermediateQuotientSubgroup_normalizedBy_sec9
        M MF U H0 hMF_le_M hU_le_M hH0_normal_M N hN_normal
  have hQ_norm_W1 : quotientSubgroupNormalizedBy MF H0 W1 Q := by
    simpa [Q, H0MF] using
      intermediateQuotientSubgroup_normalizedBy_sec9
        M MF W1 H0 hMF_le_M hW1_le_M hH0_normal_M N hN_normal
  have hQ_cases : Q = ⊥ ∨ Q = ⊤ :=
    theorem_9_6_typeII_quotient_subgroup_dichotomy_source_sec9
      M MF U W1 W2 H0 C Cprime T S p
      h95Full hpFull hII hnormal Q hQ_norm_U hQ_norm_W1
  rcases hQ_cases with hQ_bot | hQ_top
  · left
    apply le_antisymm
    · intro x hxN
      have hxMF : (x : G) ∈ MF := by
        exact hN_le_MF hxN
      let xMF : MF := ⟨(x : G), hxMF⟩
      have hxQ : QuotientGroup.mk' H0MF xMF ∈ Q := by
        refine Subgroup.mem_map.mpr ⟨xMF, ?_, rfl⟩
        simpa [Q, H0MF, intermediateQuotientSubgroup_sec9,
          Subgroup.mem_comap, Subgroup.inclusion, xMF] using hxN
      have hxQbot : QuotientGroup.mk' H0MF xMF ∈ (⊥ : Subgroup (MF ⧸ H0MF)) := by
        simpa [hQ_bot] using hxQ
      have hx_one : QuotientGroup.mk' H0MF xMF = 1 := by
        simpa using hxQbot
      have hxH0MF : xMF ∈ H0MF :=
        (QuotientGroup.eq_one_iff (N := H0MF) (x := xMF)).1 hx_one
      simpa [xMF, H0MF, Subgroup.mem_subgroupOf] using hxH0MF
    · exact hH0_le_N
  · right
    apply le_antisymm hN_le_MF
    intro x hxMFsub
    have hxMF : (x : G) ∈ MF := by
      simpa [Subgroup.mem_subgroupOf] using hxMFsub
    let xMF : MF := ⟨(x : G), hxMF⟩
    have hxQtop : QuotientGroup.mk' H0MF xMF ∈ Q := by
      have hxTop : QuotientGroup.mk' H0MF xMF ∈ (⊤ : Subgroup (MF ⧸ H0MF)) :=
        Subgroup.mem_top _
      rw [hQ_top]
      exact hxTop
    rcases Subgroup.mem_map.mp hxQtop with ⟨yMF, hyNMF, hy_eq_x⟩
    have hyN : (⟨(yMF : G), hMF_le_M yMF.property⟩ : M) ∈ N := by
      simpa [Q, H0MF, intermediateQuotientSubgroup_sec9,
        Subgroup.mem_comap, Subgroup.inclusion] using hyNMF
    have hxyH0MF : xMF / yMF ∈ H0MF :=
      QuotientGroup.eq_iff_div_mem.mp hy_eq_x.symm
    have hxyN : (⟨((xMF / yMF : MF) : G), hMF_le_M (xMF / yMF).property⟩ : M) ∈ N :=
      hH0_le_N (by
        simpa [H0MF, Subgroup.mem_subgroupOf] using hxyH0MF)
    have hx_eq : x = (⟨((xMF / yMF : MF) : G), hMF_le_M (xMF / yMF).property⟩ : M) *
        ⟨(yMF : G), hMF_le_M yMF.property⟩ := by
      apply Subtype.ext
      simp [xMF, div_eq_mul_inv, mul_assoc]
    rw [hx_eq]
    exact N.mul_mem hxyN hyN

private theorem theorem_9_6_typeII_chief_factor_source_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (T : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (S : Finset (Section1.ClassFunction M))
    (p : Nat.Primes) :
    notation_9_5_data M MF U W1 W2 H0 C Cprime T S →
      hoReductionData M MF U W2 H0 p →
        section16TypeII M MF →
            (hnormal : (H0.subgroupOf MF).Normal) →
              IsChiefFactor (H0.subgroupOf M) (MF.subgroupOf M) := by
  intro h95 hp hII hnormal
  have h95Full : notation_9_5_data M MF U W1 W2 H0 C Cprime T S := h95
  rcases h95 with
    ⟨h92, _hp95, _hC, _hBarU, _hCprimeC, _hCprimeEq, _hDade, _hS⟩
  have hMF := h92.mf
  rcases hMF with
    ⟨⟨_hMF_le_M_source, hMF_normal_M, _hMFnil, _hMFhall⟩, _hMFmax⟩
  rcases hp with
    ⟨hH0_le_MF, hMF_le_M, hH0_normal_M, _hH0_normal_MF, hH0lt,
      _helem, _htypeIIIIVData⟩
  refine
    { normal_K := hH0_normal_M
      normal_H := hMF_normal_M
      lt := ?_
      is_maximal :=
        theorem_9_6_typeII_chief_factor_maximal_source_sec9
          M MF U W1 W2 H0 C Cprime T S p
          h95Full
          ⟨hH0_le_MF, hMF_le_M, hH0_normal_M, _hH0_normal_MF, hH0lt,
            _helem, _htypeIIIIVData⟩ hII hnormal }
  refine lt_iff_le_not_ge.2 ⟨?_, ?_⟩
  · intro x hx
    exact hH0_le_MF hx
  · intro hle
    have hMF_le_H0 : MF ≤ H0 := by
      intro x hxMF
      let xM : M := ⟨x, hMF_le_M hxMF⟩
      have hxMFsub : xM ∈ MF.subgroupOf M := by
        simpa [xM, Subgroup.mem_subgroupOf] using hxMF
      have hxH0sub : xM ∈ H0.subgroupOf M := hle hxMFsub
      simpa [xM, Subgroup.mem_subgroupOf] using hxH0sub
    exact (not_le_of_gt hH0lt) hMF_le_H0

private theorem theorem_9_6_typeII_chief_cardinality_payload_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (T : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (S : Finset (Section1.ClassFunction M))
    (p : Nat.Primes) :
    notation_9_5_data M MF U W1 W2 H0 C Cprime T S →
      hoReductionData M MF U W2 H0 p →
        section16TypeII M MF →
          (hnormal : (H0.subgroupOf MF).Normal) →
            IsChiefFactor (H0.subgroupOf M) (MF.subgroupOf M) ∧
            (letI : (H0.subgroupOf MF).Normal := hnormal;
              Nat.card {x : MF ⧸ H0.subgroupOf MF //
                ∀ h : MF, QuotientGroup.mk' (H0.subgroupOf MF) h = x →
                  ∀ w : G, w ∈ W1 → ⁅w, (h : G)⁆ ∈ H0} = p.val) ∧
            Nat.card (MF ⧸ H0.subgroupOf MF) = p.val ^ Nat.card W1 := by
  intro h95 hp hII hnormal
  have hchief :=
    theorem_9_6_typeII_chief_factor_source_sec9
      M MF U W1 W2 H0 C Cprime T S p h95 hp hII hnormal
  rcases theorem_9_6_typeII_cardinality_of_chief_factor_sec9
      M MF U W1 W2 H0 C Cprime T S p h95 hp hII hnormal hchief with
    ⟨hWbar2, hcard⟩
  exact ⟨hchief, hWbar2, hcard⟩

public theorem quotientChiefFactorData_9_6_of_source_facts
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 : Subgroup G)
    (p : Nat.Primes) :
    hypothesis_9_2_statement M MF U W1 W2 (Nat.card W1) →
      hoReductionData M MF U W2 H0 p →
        IsChiefFactor (H0.subgroupOf M) (MF.subgroupOf M) →
          (∃ hnormal : (H0.subgroupOf MF).Normal,
            letI : (H0.subgroupOf MF).Normal := hnormal
            Nat.card {x : MF ⧸ H0.subgroupOf MF //
              ∀ h : MF, QuotientGroup.mk' (H0.subgroupOf MF) h = x →
                ∀ w : G, w ∈ W1 → ⁅w, (h : G)⁆ ∈ H0} = p.val) →
              Nat.card (MF ⧸ H0.subgroupOf MF) = p.val ^ Nat.card W1 →
                quotientChiefFactorData_9_6 M MF H0 W1 p := by
  intro h92 hp hchief hWbar2 hcard
  have hMF := h92.mf
  rcases hMF.1 with ⟨hMF_le_M, _hMF_normal, _hMF_nilpotent, _hMF_hall⟩
  rcases hp with
    ⟨hH0_le_MF, _hMF_le_M', _hH0_normal_M, hH0_normal_MF, _hH0lt,
      _helem, _htypeIIIIV⟩
  exact ⟨hH0_le_MF, hMF_le_M, hH0_normal_MF, hchief, hWbar2, hcard⟩

private theorem theorem_9_6_typeII_source_payload_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (T : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (S : Finset (Section1.ClassFunction M))
    (p : Nat.Primes) :
    notation_9_5_data M MF U W1 W2 H0 C Cprime T S →
      hoReductionData M MF U W2 H0 p →
        section16TypeII M MF →
          (hnormal : (H0.subgroupOf MF).Normal) →
            (∀ h : G, h ∈ MF →
              (∀ u : G, u ∈ U → ⁅u, h⁆ ∈ H0) → h ∈ H0) ∧
            IsChiefFactor (H0.subgroupOf M) (MF.subgroupOf M) ∧
            (letI : (H0.subgroupOf MF).Normal := hnormal;
              Nat.card {x : MF ⧸ H0.subgroupOf MF //
                ∀ h : MF, QuotientGroup.mk' (H0.subgroupOf MF) h = x →
                  ∀ w : G, w ∈ W1 → ⁅w, (h : G)⁆ ∈ H0} = p.val) ∧
            Nat.card (MF ⧸ H0.subgroupOf MF) = p.val ^ Nat.card W1 := by
  intro h95 hp hII hnormal
  have hfixed :=
    theorem_9_6_typeII_quotient_fixed_points_sec9 M MF U W1 W2 H0 C Cprime T S p
      h95 hp hII hnormal
  rcases theorem_9_6_typeII_chief_cardinality_payload_sec9
      M MF U W1 W2 H0 C Cprime T S p h95 hp hII hnormal with
    ⟨hchief, hWbar2, hcard⟩
  exact ⟨hfixed, hchief, hWbar2, hcard⟩

private theorem theorem_9_6_typeII_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (T : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (S : Finset (Section1.ClassFunction M))
    (p : Nat.Primes) :
    notation_9_5_data M MF U W1 W2 H0 C Cprime T S →
      hoReductionData M MF U W2 H0 p →
        section16TypeII M MF →
          (∀ h : G, h ∈ MF →
            (∀ u : G, u ∈ U → ⁅u, h⁆ ∈ H0) → h ∈ H0) ∧
            IsChiefFactor (H0.subgroupOf M) (MF.subgroupOf M) ∧
            (∃ hnormal : (H0.subgroupOf MF).Normal,
              letI : (H0.subgroupOf MF).Normal := hnormal
              Nat.card {x : MF ⧸ H0.subgroupOf MF //
                ∀ h : MF, QuotientGroup.mk' (H0.subgroupOf MF) h = x →
                  ∀ w : G, w ∈ W1 → ⁅w, (h : G)⁆ ∈ H0} = p.val) ∧
            Nat.card (MF ⧸ H0.subgroupOf MF) = p.val ^ Nat.card W1 := by
  intro h95 hp hII
  rcases hp with
    ⟨hH0_le_MF, hMF_le_M, hH0_normal_M, hH0_normal_MF, hH0lt,
      helem, htypeIIIIVData⟩
  rcases theorem_9_6_typeII_source_payload_sec9 M MF U W1 W2 H0 C Cprime T S p
      h95
      ⟨hH0_le_MF, hMF_le_M, hH0_normal_M, hH0_normal_MF, hH0lt,
        helem, htypeIIIIVData⟩ hII hH0_normal_MF with
    ⟨hfixed, hchief, hWbar2, hcard⟩
  exact ⟨hfixed, hchief, ⟨hH0_normal_MF, hWbar2⟩, hcard⟩

private theorem theorem_9_6_typeII_U_ne_C_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (T : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (S : Finset (Section1.ClassFunction M))
    (p : Nat.Primes) :
    notation_9_5_data M MF U W1 W2 H0 C Cprime T S →
      hoReductionData M MF U W2 H0 p →
        (∀ h : G, h ∈ MF →
          (∀ u : G, u ∈ U → ⁅u, h⁆ ∈ H0) → h ∈ H0) →
          U ≠ C := by
  intro h95 hp hfixed
  rcases h95 with
    ⟨_h92, _hp95, hC, _hBarU, _hCprimeC, _hCprimeEq, _hDade, _hS⟩
  rcases hp with
    ⟨_hH0_le_MF, _hMF_le_M, _hH0_normal_M, _hH0_normal_MF, hH0lt,
      _helem, _htypeIIIIVData⟩
  apply ne_of_not_quotientCentralizedBy_quotientCentralizerIn_sec9 hC
  intro hcent
  have hMF_le_H0 : MF ≤ H0 := by
    intro h hhMF
    exact hfixed h hhMF (fun u huU => hcent u huU h hhMF)
  exact (not_le_of_gt hH0lt) hMF_le_H0

public theorem theorem_9_6_typeIIIIV_U_ne_C_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (T : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (S : Finset (Section1.ClassFunction M))
    (p : Nat.Primes) :
    notation_9_5_data M MF U W1 W2 H0 C Cprime T S →
      hoReductionData M MF U W2 H0 p →
        (section16TypeIII M MF ∨ section16TypeIV M MF) →
          U ≠ C := by
  intro h95 hp htypeIIIIV
  rcases h95 with
    ⟨_h92, _hp95, hC, _hBarU, _hCprimeC, _hCprimeEq, _hDade, _hS⟩
  rcases hp with
    ⟨_hH0_le_MF, _hMF_le_M, _hH0_normal_M, _hH0_normal_MF, _hH0lt,
      _helem, htypeIIIIVData⟩
  exact ne_of_not_quotientCentralizedBy_quotientCentralizerIn_sec9 hC
    (htypeIIIIVData htypeIIIIV).2.2

private theorem theorem_9_6_typeIIIIV_quotient_U_fixed_dichotomy_source_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 : Subgroup G)
    [Subgroup.Normalizes U MF]
    (p : Nat.Primes) :
    hypothesis_9_2_statement M MF U W1 W2 (Nat.card W1) →
      hoReductionData M MF U W2 H0 p →
        (section16TypeIII M MF ∨ section16TypeIV M MF) →
          (hnormal : (H0.subgroupOf MF).Normal) →
            (hH0_inv_U : IsInvariant U MF (H0.subgroupOf MF)) →
              (letI : (H0.subgroupOf MF).Normal := hnormal;
                letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
                  quotientMulDistribMulAction (A := U) (G := MF)
                    (H0.subgroupOf MF) hH0_inv_U;
                quotientSubgroupNormalizedBy MF H0 U
                  (fixedPointSubgroup U (MF ⧸ H0.subgroupOf MF))) →
              (letI : (H0.subgroupOf MF).Normal := hnormal;
                letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
                  quotientMulDistribMulAction (A := U) (G := MF)
                    (H0.subgroupOf MF) hH0_inv_U;
                fixedPointSubgroup U (MF ⧸ H0.subgroupOf MF) = ⊥ ∨
                  fixedPointSubgroup U (MF ⧸ H0.subgroupOf MF) = ⊤) := by
  classical
  intro h92 hp hIIIIV hnormal hH0_inv_U hQnorm
  rcases hp with
    ⟨hH0_le_MF, hMF_le_M, hH0_normal_M, _hH0_normal_MF, _hH0lt,
      helem, htypeIIIIVData⟩
  have hPsource := h92.typePDefinitionData
  rcases hPsource with
    ⟨_hMFsource, _hW1cyc, _hW1ne, hW1hall, hcompMW1, _hUleD,
      _hUnil, hW1normU, hcompDU, _hMFnotcyc, _hM2le, _hFitEq, _hFitLeD,
      _hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
  rcases hW1hall with ⟨hW1_le_M, _hW1hall⟩
  rcases theorem_9_3_source_action_and_branch_facts_sec9
      M MF U W1 W2 (Nat.card W1) h92 with
    ⟨haction, _hII, _hIIIIV⟩
  rcases haction with ⟨_hcomp, _hfrob, hUW1_norm_MF, _hsolvMF, _hcopUW1⟩
  have hW1_norm_MF : W1 ≤ Subgroup.normalizer (MF : Set G) :=
    le_sup_right.trans hUW1_norm_MF
  letI : Subgroup.Normalizes W1 MF := ⟨hW1_norm_MF⟩
  have hH0_inv_W1 : IsInvariant W1 MF (H0.subgroupOf MF) :=
    H0_subgroupOf_MF_isInvariant_under_U_sec9 M MF W1 H0
      hMF_le_M hW1_le_M hH0_normal_M hW1_norm_MF
  have hW1_norm_U : W1 ≤ Subgroup.normalizer (U : Set G) := by
    intro w hw
    exact (mem_subgroupNormalizerIn.mp (hW1normU hw)).1
  have hM_eq : M = (MF ⊔ U) ⊔ W1 := by
    calc
      M = ambientDerivedSubgroup M ⊔ W1 := hcompMW1.2.2.1
      _ = (MF ⊔ U) ⊔ W1 := by rw [hcompDU.2.2.1]
  let H0MF : Subgroup MF := H0.subgroupOf MF
  haveI : H0MF.Normal := hnormal
  letI : MulDistribMulAction U (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := U) (G := MF) H0MF hH0_inv_U
  have hquot_comm : IsMulCommutative (MF ⧸ H0MF) := by
    rcases helem with ⟨_hnormal_elem, helemQ⟩
    have helemQ' : IsElementaryAbelian p.val (MF ⧸ H0MF) := by
      simpa [H0MF] using helemQ
    exact helemQ'.toIsMulCommutative
  have hQnormU :
      quotientSubgroupNormalizedBy MF H0 U
        (fixedPointSubgroup U (MF ⧸ H0MF)) := by
    simpa [H0MF] using hQnorm
  have hQnormW1 :
      quotientSubgroupNormalizedBy MF H0 W1
        (fixedPointSubgroup U (MF ⧸ H0MF)) := by
    simpa [H0MF] using
      fixedPointSubgroup_quotient_normalizedBy_of_normalizes_sec9
        MF U W1 H0 hW1_norm_U hnormal hH0_inv_U hH0_inv_W1
  have hchief : IsChiefFactor (H0.subgroupOf M) (MF.subgroupOf M) :=
    (htypeIIIIVData hIIIIV).2.1
  simpa [H0MF] using
    quotientSubgroup_dichotomy_of_chief_factor_sec9
      M MF U W1 H0 hnormal
      (fixedPointSubgroup U (MF ⧸ H0MF))
      hH0_le_MF hMF_le_M hchief hquot_comm hM_eq hQnormU hQnormW1

private theorem theorem_9_6_typeII_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (T : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (S : Finset (Section1.ClassFunction M))
    (p : Nat.Primes) :
    notation_9_5_data M MF U W1 W2 H0 C Cprime T S →
      hoReductionData M MF U W2 H0 p →
        section16TypeII M MF →
          U ≠ C ∧
            IsChiefFactor (H0.subgroupOf M) (MF.subgroupOf M) ∧
            (∃ hnormal : (H0.subgroupOf MF).Normal,
              letI : (H0.subgroupOf MF).Normal := hnormal
              Nat.card {x : MF ⧸ H0.subgroupOf MF //
                ∀ h : MF, QuotientGroup.mk' (H0.subgroupOf MF) h = x →
                  ∀ w : G, w ∈ W1 → ⁅w, (h : G)⁆ ∈ H0} = p.val) ∧
            Nat.card (MF ⧸ H0.subgroupOf MF) = p.val ^ Nat.card W1 := by
  intro h95 hp hII
  rcases theorem_9_6_typeII_source_bridge_sec9
      M MF U W1 W2 H0 C Cprime T S p h95 hp hII with
    ⟨hfixed, hchief, hWbar2, hcard⟩
  exact ⟨theorem_9_6_typeII_U_ne_C_sec9
      M MF U W1 W2 H0 C Cprime T S p h95 hp hfixed,
    hchief, hWbar2, hcard⟩

private theorem theorem_9_6_typeIIIIV_quotient_U_fixed_eq_bot_of_fixed_proper_source_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 : Subgroup G)
    [Subgroup.Normalizes U MF]
    (p : Nat.Primes) :
    hypothesis_9_2_statement M MF U W1 W2 (Nat.card W1) →
      hoReductionData M MF U W2 H0 p →
        (section16TypeIII M MF ∨ section16TypeIV M MF) →
          (hnormal : (H0.subgroupOf MF).Normal) →
            (hH0_inv_U : IsInvariant U MF (H0.subgroupOf MF)) →
              (letI : (H0.subgroupOf MF).Normal := hnormal;
                letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
                  quotientMulDistribMulAction (A := U) (G := MF)
                    (H0.subgroupOf MF) hH0_inv_U;
                fixedPointSubgroup U (MF ⧸ H0.subgroupOf MF) ≠ ⊤) →
              (letI : (H0.subgroupOf MF).Normal := hnormal;
                letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
                  quotientMulDistribMulAction (A := U) (G := MF)
                    (H0.subgroupOf MF) hH0_inv_U;
                fixedPointSubgroup U (MF ⧸ H0.subgroupOf MF) = ⊥) := by
  intro h92 hp hIIIIV hnormal hH0_inv_U hnotTop
  have hQnorm :
      (letI : (H0.subgroupOf MF).Normal := hnormal;
        letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
          quotientMulDistribMulAction (A := U) (G := MF)
            (H0.subgroupOf MF) hH0_inv_U;
        quotientSubgroupNormalizedBy MF H0 U
          (fixedPointSubgroup U (MF ⧸ H0.subgroupOf MF))) :=
    fixedPointSubgroup_quotient_normalizedBy_self_sec9 MF U H0 hnormal hH0_inv_U
  have hcases :=
    theorem_9_6_typeIIIIV_quotient_U_fixed_dichotomy_source_sec9
      M MF U W1 W2 H0 p h92 hp hIIIIV
      hnormal hH0_inv_U hQnorm
  exact quotient_U_fixed_eq_bot_of_fixedPointSubgroup_dichotomy_sec9 MF U H0
    hnormal hH0_inv_U hcases hnotTop

private theorem theorem_9_6_typeIIIIV_quotient_cardinality_formula_of_U_fixed_proper_source_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 : Subgroup G)
    [Subgroup.Normalizes U MF] [Subgroup.Normalizes W1 MF]
    (p : Nat.Primes) :
    hypothesis_9_2_statement M MF U W1 W2 (Nat.card W1) →
      hoReductionData M MF U W2 H0 p →
        (section16TypeIII M MF ∨ section16TypeIV M MF) →
          (hnormal : (H0.subgroupOf MF).Normal) →
            (hH0_inv_U : IsInvariant U MF (H0.subgroupOf MF)) →
              (hH0_inv_W1 : IsInvariant W1 MF (H0.subgroupOf MF)) →
                (letI : (H0.subgroupOf MF).Normal := hnormal;
                  letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
                    quotientMulDistribMulAction (A := U) (G := MF)
                      (H0.subgroupOf MF) hH0_inv_U;
                  fixedPointSubgroup U (MF ⧸ H0.subgroupOf MF) ≠ ⊤) →
                (letI : (H0.subgroupOf MF).Normal := hnormal;
                  letI : MulDistribMulAction W1 (MF ⧸ H0.subgroupOf MF) :=
                    quotientMulDistribMulAction (A := W1) (G := MF)
                      (H0.subgroupOf MF) hH0_inv_W1;
                  Nat.card (MF ⧸ H0.subgroupOf MF) =
                    Nat.card (fixedPointSubgroup W1 (MF ⧸ H0.subgroupOf MF)) ^
                      Nat.card W1) := by
  classical
  intro h92 hp hIIIIV hnormal hH0_inv_U hH0_inv_W1 hnotTop
  have hpFull := hp
  rcases hp with
    ⟨hH0_le_MF, hMF_le_M, hH0_normal_M, hH0_normal_MF, hH0lt,
      helem, htypeIIIIVData⟩
  have h92Full := h92
  have hMF := h92.mf
  have hPsource := h92.typePDefinitionData
  have hIItoIVSource := h92.typeIIToIVSourceCondition
  rcases hPsource with
    ⟨hMFsource, hW1cyc, _hW1ne, hW1hall, _hcompMW1, hUleD,
      hUnil, _hW1normU, _hcompDU, _hMFnotcyc, _hM2le, _hFitEq, _hFitLeD,
      _hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
  rcases hMFsource with ⟨hMFhall, _hMFmax⟩
  rcases hMFhall with ⟨_hMF_le_M_source, _hMF_normal_M_source, hMFnil, _hMFhall⟩
  rcases hW1hall with ⟨hW1_le_M, _hW1hall⟩
  rcases hIItoIVSource with ⟨_hU_ne, hW1primeOrder, _hTI⟩
  rcases theorem_9_3_source_action_and_branch_facts_sec9
      M MF U W1 W2 (Nat.card W1) h92Full with
    ⟨haction, _hII, _hIIIIV⟩
  rcases haction with ⟨_hcomp, hfrob, hUW1_norm_MF, _hsolvMF, hcopUW1⟩
  let H0MF : Subgroup MF := H0.subgroupOf MF
  let UW1 : Subgroup G := U ⊔ W1
  haveI : H0MF.Normal := hnormal
  have hH0MF_ne_top : H0MF ≠ ⊤ := by
    intro htop
    have hMF_le_H0 : MF ≤ H0 := by
      intro x hxMF
      let xMF : MF := ⟨x, hxMF⟩
      have hxH0MF : xMF ∈ H0MF := by
        simp [htop]
      simpa [H0MF, xMF, Subgroup.mem_subgroupOf] using hxH0MF
    exact (not_le_of_gt hH0lt) hMF_le_H0
  haveI : Nontrivial (MF ⧸ H0MF) :=
    (QuotientGroup.nontrivial_iff (N := H0MF)).2 hH0MF_ne_top
  letI : Subgroup.Normalizes UW1 MF := ⟨by simpa [UW1] using hUW1_norm_MF⟩
  letI : MulDistribMulAction U (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := U) (G := MF) H0MF hH0_inv_U
  letI : MulDistribMulAction W1 (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := W1) (G := MF) H0MF hH0_inv_W1
  have hU_le_M : U ≤ M :=
    hUleD.trans (section12_ambientDerivedSubgroup_le (G := G) (E := M))
  have hUW1_le_M : UW1 ≤ M := by
    dsimp [UW1]
    exact sup_le hU_le_M hW1_le_M
  have hH0_inv_UW1 : IsInvariant UW1 MF H0MF :=
    H0_subgroupOf_MF_isInvariant_under_U_sec9 M MF UW1 H0
      hMF_le_M hUW1_le_M hH0_normal_M (by simpa [UW1] using hUW1_norm_MF)
  letI : MulDistribMulAction UW1 (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := UW1) (G := MF) H0MF hH0_inv_UW1
  have hU_fixed_bot :
      fixedPointSubgroup U (MF ⧸ H0MF) = ⊥ := by
    simpa [H0MF] using
      theorem_9_6_typeIIIIV_quotient_U_fixed_eq_bot_of_fixed_proper_source_sec9
        M MF U W1 W2 H0 p h92Full hpFull hIIIIV
        hnormal hH0_inv_U hnotTop
  have hK_fixed_bot :
      fixedPointSubgroup (↥(U.subgroupOf UW1)) (MF ⧸ H0MF) = ⊥ := by
    simpa [H0MF, UW1] using
      quotient_U_fixedPointSubgroup_subgroupOf_eq_bot_sec9
        MF U W1 H0 hnormal hH0_inv_U hH0_inv_UW1 hU_fixed_bot
  have hUW1_solv : IsSolvable UW1 := by
    simpa [UW1] using
      solvable_of_nilpotent_frobenius_kernel_cyclic_complement_sec9
        U W1 hUnil hW1cyc hfrob
  have hquot_nil : Group.IsNilpotent (MF ⧸ H0MF) := by
    haveI : Group.IsNilpotent MF := hMFnil
    exact Group.nilpotent_of_surjective
      (QuotientGroup.mk' H0MF) (QuotientGroup.mk'_surjective H0MF)
  have hquot_dvd_MF : Nat.card (MF ⧸ H0MF) ∣ Nat.card MF :=
    Subgroup.card_quotient_dvd_card H0MF
  have hcop :
      Nat.Coprime (Nat.card UW1) (Nat.card (MF ⧸ H0MF)) :=
    Nat.Coprime.coprime_dvd_right hquot_dvd_MF (by
      simpa [UW1] using hcopUW1.symm)
  let W1sub : Subgroup UW1 := W1.subgroupOf UW1
  have hW1sub_card : Nat.card W1sub = Nat.card W1 :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := W1) (K := UW1)
        (by
          change W1 ≤ U ⊔ W1
          exact le_sup_right)).toEquiv
  have hW1_prime : Nat.Prime (Nat.card W1) := by
    rcases hW1primeOrder with ⟨q, hq⟩
    simpa [hq] using q.property
  have hW1sub_prime : Nat.Prime (Nat.card W1sub) := by
    simpa [hW1sub_card] using hW1_prime
  have hfixR :
      ∀ x : W1sub, x ≠ 1 →
        fixedPointSubgroup (↥(Subgroup.zpowers (x : UW1))) (MF ⧸ H0MF) =
          fixedPointSubgroup (↥W1sub) (MF ⧸ H0MF) := by
    intro x hx
    have hx_top : Subgroup.zpowers x = (⊤ : Subgroup W1sub) :=
      zpowers_eq_top_of_prime_card_of_ne_one hW1sub_prime hx
    have hmap_zpow :
        (Subgroup.zpowers x).map W1sub.subtype =
          Subgroup.zpowers (x : UW1) := by
      simp
    have htop_map : (⊤ : Subgroup W1sub).map W1sub.subtype = W1sub := by
      ext y
      constructor
      · intro hy
        rcases Subgroup.mem_map.mp hy with ⟨z, _hz, rfl⟩
        exact z.property
      · intro hy
        exact Subgroup.mem_map.mpr ⟨⟨y, hy⟩, by simp, rfl⟩
    have hzpow_eq : Subgroup.zpowers (x : UW1) = W1sub := by
      calc
        Subgroup.zpowers (x : UW1) =
            (Subgroup.zpowers x).map W1sub.subtype := hmap_zpow.symm
        _ = (⊤ : Subgroup W1sub).map W1sub.subtype := by rw [hx_top]
        _ = W1sub := htop_map
    rw [hzpow_eq]
  have hmain :
      Nat.card (MF ⧸ H0MF) =
        Nat.card (fixedPointSubgroup (↥W1sub) (MF ⧸ H0MF)) ^ Nat.card W1sub := by
    exact
      theorem_3_10_b (G := UW1) (K := U.subgroupOf UW1) (R := W1sub)
        (M := MF ⧸ H0MF)
        (by simpa [section12FrobeniusJoinWithKernel, UW1, W1sub] using hfrob)
        hUW1_solv hquot_nil hcop hK_fixed_bot hfixR
  have hW1sub_fixed_card :
      Nat.card (fixedPointSubgroup (↥W1sub) (MF ⧸ H0MF)) =
        Nat.card (fixedPointSubgroup W1 (MF ⧸ H0MF)) := by
    simpa [H0MF, UW1, W1sub] using
      quotient_W1_subgroupOf_fixedPointSubgroup_card_eq_sec9
        MF U W1 H0 hnormal hH0_inv_W1 hH0_inv_UW1
  have hfinal :
      Nat.card (MF ⧸ H0MF) =
        Nat.card (fixedPointSubgroup W1 (MF ⧸ H0MF)) ^ Nat.card W1 := by
    calc
      Nat.card (MF ⧸ H0MF) =
          Nat.card (fixedPointSubgroup (↥W1sub) (MF ⧸ H0MF)) ^ Nat.card W1sub :=
        hmain
      _ = Nat.card (fixedPointSubgroup W1 (MF ⧸ H0MF)) ^ Nat.card W1 := by
        rw [hW1sub_fixed_card, hW1sub_card]
  simpa [H0MF] using hfinal

private theorem theorem_9_6_typeIIIIV_W1_fixed_cardinality_of_U_fixed_proper_source_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 : Subgroup G)
    [Subgroup.Normalizes U MF] [Subgroup.Normalizes W1 MF]
    (p : Nat.Primes) :
    hypothesis_9_2_statement M MF U W1 W2 (Nat.card W1) →
      hoReductionData M MF U W2 H0 p →
        (section16TypeIII M MF ∨ section16TypeIV M MF) →
          (hnormal : (H0.subgroupOf MF).Normal) →
            (hH0_inv_U : IsInvariant U MF (H0.subgroupOf MF)) →
              (hH0_inv_W1 : IsInvariant W1 MF (H0.subgroupOf MF)) →
                (letI : (H0.subgroupOf MF).Normal := hnormal;
                  letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
                    quotientMulDistribMulAction (A := U) (G := MF)
                      (H0.subgroupOf MF) hH0_inv_U;
                  fixedPointSubgroup U (MF ⧸ H0.subgroupOf MF) ≠ ⊤) →
                (letI : (H0.subgroupOf MF).Normal := hnormal;
                  letI : MulDistribMulAction W1 (MF ⧸ H0.subgroupOf MF) :=
                    quotientMulDistribMulAction (A := W1) (G := MF)
                      (H0.subgroupOf MF) hH0_inv_W1;
                  Nat.card (fixedPointSubgroup W1 (MF ⧸ H0.subgroupOf MF)) =
                    Nat.card W2) ∧
                Nat.card (MF ⧸ H0.subgroupOf MF) = Nat.card W2 ^ Nat.card W1 := by
  classical
  intro h92 hp hIIIIV hnormal hH0_inv_U hH0_inv_W1 hnotTop
  rcases hp with
    ⟨hH0_le_MF, hMF_le_M, hH0_normal_M, hH0_normal_MF, hH0lt,
      helem, htypeIIIIVData⟩
  rcases theorem_9_3_source_action_and_branch_facts_sec9
      M MF U W1 W2 (Nat.card W1) h92 with
    ⟨haction, _hII, _hIIIIV⟩
  rcases haction with ⟨_hcomp, _hfrob, hUW1_norm_MF, hsolvMF, hcopUW1⟩
  have hW1_norm_MF : W1 ≤ Subgroup.normalizer (MF : Set G) :=
    le_sup_right.trans hUW1_norm_MF
  letI : Subgroup.Normalizes W1 MF := ⟨hW1_norm_MF⟩
  have hW1_dvd_UW1 : Nat.card W1 ∣ Nat.card (U ⊔ W1 : Subgroup G) :=
    Subgroup.card_dvd_of_le le_sup_right
  have hcopW1 : Nat.Coprime (Nat.card W1) (Nat.card MF) :=
    (Nat.Coprime.coprime_dvd_right hW1_dvd_UW1 hcopUW1).symm
  let H0MF : Subgroup MF := H0.subgroupOf MF
  haveI : H0MF.Normal := hnormal
  letI : MulDistribMulAction W1 (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := W1) (G := MF) H0MF hH0_inv_W1
  have hquot_formula :
      Nat.card (MF ⧸ H0MF) =
        Nat.card (fixedPointSubgroup W1 (MF ⧸ H0MF)) ^ Nat.card W1 := by
    simpa [H0MF] using
      theorem_9_6_typeIIIIV_quotient_cardinality_formula_of_U_fixed_proper_source_sec9
        M MF U W1 W2 H0 p h92
        ⟨hH0_le_MF, hMF_le_M, hH0_normal_M, hH0_normal_MF, hH0lt,
          helem, htypeIIIIVData⟩ hIIIIV hnormal hH0_inv_U hH0_inv_W1 hnotTop
  have hquot_fixed_eq :
      fixedPointSubgroup W1 (MF ⧸ H0MF) =
        (W2.subgroupOf MF).map (QuotientGroup.mk' H0MF) := by
    simpa [H0MF] using
      quotient_W1_fixedPointSubgroup_eq_W2_map_of_hypothesis_9_2_sec9
        M MF U W1 W2 H0 (Nat.card W1) h92 hnormal hH0_inv_W1
  have hsource : Section8.typePDefinitionData M MF U W1 W2 := h92.typePDefinitionData
  rcases hsource with
    ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD,
      _hUnil, _hW1normU, _hcompDU, _hMFnotcyc, _hM2le, _hFitEq, _hFitLeD,
      hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
  have hW2_le_MF : W2 ≤ MF := hW2le.trans inf_le_left
  have hfixed_dvd_W2 :
      Nat.card (fixedPointSubgroup W1 (MF ⧸ H0MF)) ∣ Nat.card W2 := by
    rw [hquot_fixed_eq]
    have hmap_dvd :
        Nat.card ((W2.subgroupOf MF).map (QuotientGroup.mk' H0MF)) ∣
          Nat.card (W2.subgroupOf MF) :=
      Subgroup.card_map_dvd (H := W2.subgroupOf MF) (QuotientGroup.mk' H0MF)
    simpa [natCard_subgroupOf_eq W2 MF hW2_le_MF] using hmap_dvd
  have hH0MF_ne_top : H0MF ≠ ⊤ := by
    intro htop
    have hMF_le_H0 : MF ≤ H0 := by
      intro x hxMF
      let xMF : MF := ⟨x, hxMF⟩
      have hxH0MF : xMF ∈ H0MF := by
        simp [htop]
      simpa [H0MF, xMF, Subgroup.mem_subgroupOf] using hxH0MF
    exact (not_le_of_gt hH0lt) hMF_le_H0
  haveI : Nontrivial (MF ⧸ H0MF) :=
    (QuotientGroup.nontrivial_iff (N := H0MF)).2 hH0MF_ne_top
  have hquot_gt_one : 1 < Nat.card (MF ⧸ H0MF) :=
    Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  have hfixed_ne_one :
      Nat.card (fixedPointSubgroup W1 (MF ⧸ H0MF)) ≠ 1 := by
    intro hfixed_one
    have hquot_one : Nat.card (MF ⧸ H0MF) = 1 := by
      rw [hquot_formula, hfixed_one]
      simp
    exact (Nat.ne_of_gt hquot_gt_one) hquot_one
  have hW2_prime : Nat.Prime (Nat.card W2) := by
    have hW2_card : Nat.card W2 = p.val := (htypeIIIIVData hIIIIV).1
    simpa [hW2_card] using p.property
  have hfixed_card :
      Nat.card (fixedPointSubgroup W1 (MF ⧸ H0MF)) = Nat.card W2 :=
    (hW2_prime.eq_one_or_self_of_dvd
      (Nat.card (fixedPointSubgroup W1 (MF ⧸ H0MF))) hfixed_dvd_W2).resolve_left
        hfixed_ne_one
  have hquot_card : Nat.card (MF ⧸ H0MF) = Nat.card W2 ^ Nat.card W1 := by
    rw [hquot_formula, hfixed_card]
  exact ⟨by simpa [H0MF] using hfixed_card,
    by simpa [H0MF] using hquot_card⟩

private theorem theorem_9_6_typeIIIIV_quotient_cardinality_of_fixed_proper_source_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 : Subgroup G)
    [Subgroup.Normalizes U MF]
    (p : Nat.Primes) :
    hypothesis_9_2_statement M MF U W1 W2 (Nat.card W1) →
      hoReductionData M MF U W2 H0 p →
        (section16TypeIII M MF ∨ section16TypeIV M MF) →
          (hnormal : (H0.subgroupOf MF).Normal) →
            (hH0_inv : IsInvariant U MF (H0.subgroupOf MF)) →
              (letI : (H0.subgroupOf MF).Normal := hnormal;
                letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
                  quotientMulDistribMulAction (A := U) (G := MF)
                    (H0.subgroupOf MF) hH0_inv;
                fixedPointSubgroup U (MF ⧸ H0.subgroupOf MF) ≠ ⊤) →
              (letI : (H0.subgroupOf MF).Normal := hnormal;
                Nat.card {x : MF ⧸ H0.subgroupOf MF //
                  ∀ h : MF, QuotientGroup.mk' (H0.subgroupOf MF) h = x →
                    ∀ w : G, w ∈ W1 → ⁅w, (h : G)⁆ ∈ H0} = Nat.card W2) ∧
              Nat.card (MF ⧸ H0.subgroupOf MF) = Nat.card W2 ^ Nat.card W1 := by
  classical
  intro h92 hp hIIIIV hnormal hH0_inv_U hnotTop
  rcases hp with
    ⟨hH0_le_MF, hMF_le_M, hH0_normal_M, hH0_normal_MF, hH0lt,
      helem, htypeIIIIVData⟩
  rcases theorem_9_3_source_action_and_branch_facts_sec9
      M MF U W1 W2 (Nat.card W1) h92 with
    ⟨haction, _hII, _hIIIIV⟩
  rcases haction with ⟨_hcomp, _hfrob, hUW1_norm_MF, _hsolvMF, _hcopUW1⟩
  have hW1_norm_MF : W1 ≤ Subgroup.normalizer (MF : Set G) :=
    le_sup_right.trans hUW1_norm_MF
  letI : Subgroup.Normalizes W1 MF := ⟨hW1_norm_MF⟩
  have hsource : Section8.typePDefinitionData M MF U W1 W2 := h92.typePDefinitionData
  rcases hsource with
    ⟨_hMFsource, _hW1cyc, _hW1ne, hW1hall, _hcompMW1, _hUleD,
      _hUnil, _hW1normU, _hcompDU, _hMFnotcyc, _hM2le, _hFitEq, _hFitLeD,
      _hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
  rcases hW1hall with ⟨hW1_le_M, _hW1hall'⟩
  have hH0_inv_W1 : IsInvariant W1 MF (H0.subgroupOf MF) :=
    H0_subgroupOf_MF_isInvariant_under_U_sec9 M MF W1 H0
      hMF_le_M hW1_le_M hH0_normal_M hW1_norm_MF
  haveI : (H0.subgroupOf MF).Normal := hnormal
  letI : MulDistribMulAction W1 (MF ⧸ H0.subgroupOf MF) :=
    quotientMulDistribMulAction (A := W1) (G := MF)
      (H0.subgroupOf MF) hH0_inv_W1
  rcases theorem_9_6_typeIIIIV_W1_fixed_cardinality_of_U_fixed_proper_source_sec9
      M MF U W1 W2 H0 p h92
      ⟨hH0_le_MF, hMF_le_M, hH0_normal_M, hH0_normal_MF, hH0lt,
        helem, htypeIIIIVData⟩ hIIIIV hnormal hH0_inv_U hH0_inv_W1 hnotTop with
    ⟨hW1fix_card, hquot_card⟩
  have hsubtype_card :
      Nat.card {x : MF ⧸ H0.subgroupOf MF //
        ∀ h : MF, QuotientGroup.mk' (H0.subgroupOf MF) h = x →
          ∀ w : G, w ∈ W1 → ⁅w, (h : G)⁆ ∈ H0} =
        Nat.card (fixedPointSubgroup W1 (MF ⧸ H0.subgroupOf MF)) := by
    simpa using
      quotient_W1_fixedPointSubgroup_card_eq_barW2_subtype_sec9
        MF W1 H0 hH0_inv_W1 hnormal
  exact ⟨hsubtype_card.trans hW1fix_card, hquot_card⟩

private theorem theorem_9_6_typeIIIIV_quotient_cardinality_payload_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 : Subgroup G)
    (p : Nat.Primes) :
    hypothesis_9_2_statement M MF U W1 W2 (Nat.card W1) →
      hoReductionData M MF U W2 H0 p →
        (section16TypeIII M MF ∨ section16TypeIV M MF) →
          (hnormal : (H0.subgroupOf MF).Normal) →
          (letI : (H0.subgroupOf MF).Normal := hnormal;
            Nat.card {x : MF ⧸ H0.subgroupOf MF //
              ∀ h : MF, QuotientGroup.mk' (H0.subgroupOf MF) h = x →
                ∀ w : G, w ∈ W1 → ⁅w, (h : G)⁆ ∈ H0} = Nat.card W2) ∧
          Nat.card (MF ⧸ H0.subgroupOf MF) = Nat.card W2 ^ Nat.card W1 := by
  classical
  intro h92 hp hIIIIV hnormal
  have h92Full := h92
  rcases hp with
    ⟨hH0_le_MF, hMF_le_M, hH0_normal_M, hH0_normal_MF, hH0lt,
      helem, htypeIIIIVData⟩
  rcases theorem_9_3_source_action_and_branch_facts_sec9
      M MF U W1 W2 (Nat.card W1) h92 with
    ⟨haction, _hII, _hIIIIV⟩
  rcases haction with ⟨_hcomp, _hfrob, hUW1_norm_MF, _hsolvMF, _hcopUW1⟩
  have hU_norm_MF : U ≤ Subgroup.normalizer (MF : Set G) :=
    le_sup_left.trans hUW1_norm_MF
  letI : Subgroup.Normalizes U MF := ⟨hU_norm_MF⟩
  have hPsource := h92.typePDefinitionData
  rcases hPsource with
    ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, hUleD,
      _hUnil, _hW1normU, _hcompDU, _hMFnotcyc, _hM2le, _hFitEq, _hFitLeD,
      _hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
  have hU_le_M : U ≤ M :=
    hUleD.trans (section12_ambientDerivedSubgroup_le (G := G) (E := M))
  have hH0_inv : IsInvariant U MF (H0.subgroupOf MF) :=
    H0_subgroupOf_MF_isInvariant_under_U_sec9 M MF U H0
      hMF_le_M hU_le_M hH0_normal_M hU_norm_MF
  have hnotTop :
      (letI : (H0.subgroupOf MF).Normal := hnormal;
        letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
          quotientMulDistribMulAction (A := U) (G := MF)
            (H0.subgroupOf MF) hH0_inv;
        fixedPointSubgroup U (MF ⧸ H0.subgroupOf MF) ≠ ⊤) :=
    quotient_U_fixed_ne_top_of_not_quotientCentralizedBy_sec9 MF U H0
      hH0_inv hnormal (htypeIIIIVData hIIIIV).2.2
  exact theorem_9_6_typeIIIIV_quotient_cardinality_of_fixed_proper_source_sec9
    M MF U W1 W2 H0 p h92Full
    ⟨hH0_le_MF, hMF_le_M, hH0_normal_M, hH0_normal_MF, hH0lt,
      helem, htypeIIIIVData⟩ hIIIIV hnormal hH0_inv hnotTop


public theorem theorem_9_6_typeIIIIV_cardinality_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 : Subgroup G)
    (p : Nat.Primes) :
    hypothesis_9_2_statement M MF U W1 W2 (Nat.card W1) →
      hoReductionData M MF U W2 H0 p →
        (section16TypeIII M MF ∨ section16TypeIV M MF) →
          (∃ hnormal : (H0.subgroupOf MF).Normal,
            letI : (H0.subgroupOf MF).Normal := hnormal
            Nat.card {x : MF ⧸ H0.subgroupOf MF //
                ∀ h : MF, QuotientGroup.mk' (H0.subgroupOf MF) h = x →
                  ∀ w : G, w ∈ W1 → ⁅w, (h : G)⁆ ∈ H0} = p.val) ∧
              Nat.card (MF ⧸ H0.subgroupOf MF) = p.val ^ Nat.card W1 := by
  intro h92 hp hIIIIV
  rcases hp with
    ⟨hH0_le_MF, hMF_le_M, hH0_normal_M, hH0_normal_MF, hH0lt,
      helem, htypeIIIIVData⟩
  have hpFull : hoReductionData M MF U W2 H0 p :=
    ⟨hH0_le_MF, hMF_le_M, hH0_normal_M, hH0_normal_MF, hH0lt,
      helem, htypeIIIIVData⟩
  have hW2_card : Nat.card W2 = p.val := (htypeIIIIVData hIIIIV).1
  rcases theorem_9_6_typeIIIIV_quotient_cardinality_payload_sec9
      M MF U W1 W2 H0 p h92 hpFull hIIIIV hH0_normal_MF with
    ⟨hWbar2, hHbar⟩
  exact ⟨⟨hH0_normal_MF, by simpa [hW2_card] using hWbar2⟩,
    by simpa [hW2_card] using hHbar⟩

public theorem theorem_9_6_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (T : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (S : Finset (Section1.ClassFunction M))
    (p : Nat.Primes) :
    notation_9_5_data M MF U W1 W2 H0 C Cprime T S →
      hoReductionData M MF U W2 H0 p →
        U ≠ C ∧
          IsChiefFactor (H0.subgroupOf M) (MF.subgroupOf M) ∧
          (∃ hnormal : (H0.subgroupOf MF).Normal,
            letI : (H0.subgroupOf MF).Normal := hnormal
            Nat.card {x : MF ⧸ H0.subgroupOf MF //
              ∀ h : MF, QuotientGroup.mk' (H0.subgroupOf MF) h = x →
                ∀ w : G, w ∈ W1 → ⁅w, (h : G)⁆ ∈ H0} = p.val) ∧
          Nat.card (MF ⧸ H0.subgroupOf MF) = p.val ^ Nat.card W1 := by
  intro h95 hp
  have h95Full := h95
  have hpFull := hp
  rcases h95 with
    ⟨h92, _hp95, _hC, _hBarU, _hCprimeC, _hCprimeEq, _hDade, _hS⟩
  have h92Full := h92
  have htypes := h92.typeCases
  have hfromIIIIV :
      (section16TypeIII M MF ∨ section16TypeIV M MF) →
        U ≠ C ∧
          IsChiefFactor (H0.subgroupOf M) (MF.subgroupOf M) ∧
          (∃ hnormal : (H0.subgroupOf MF).Normal,
            letI : (H0.subgroupOf MF).Normal := hnormal
            Nat.card {x : MF ⧸ H0.subgroupOf MF //
              ∀ h : MF, QuotientGroup.mk' (H0.subgroupOf MF) h = x →
                ∀ w : G, w ∈ W1 → ⁅w, (h : G)⁆ ∈ H0} = p.val) ∧
          Nat.card (MF ⧸ H0.subgroupOf MF) = p.val ^ Nat.card W1 := by
    intro hIIIIV
    have hUC : U ≠ C :=
      theorem_9_6_typeIIIIV_U_ne_C_sec9 M MF U W1 W2 H0 C Cprime T S p
        h95Full hpFull hIIIIV
    rcases hpFull with
      ⟨_hH0_le_MF, _hMF_le_M, _hH0_normal_M, _hH0_normal_MF, _hH0lt,
        _helem, htypeIIIIVData⟩
    have hchief : IsChiefFactor (H0.subgroupOf M) (MF.subgroupOf M) :=
      (htypeIIIIVData hIIIIV).2.1
    rcases theorem_9_6_typeIIIIV_cardinality_source_core_sec9
        M MF U W1 W2 H0 p h92Full hp hIIIIV with
      ⟨hWbar2, hcard⟩
    exact ⟨hUC, hchief, hWbar2, hcard⟩
  rcases htypes with hII | hIII | hIV
  · exact theorem_9_6_typeII_source_core_sec9
      M MF U W1 W2 H0 C Cprime T S p h95Full hp hII
  · exact hfromIIIIV (Or.inl hIII)
  · exact hfromIIIIV (Or.inr hIV)

public theorem theorem_9_6_source_interface
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (T : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (S : Finset (Section1.ClassFunction M)) :
    notation_9_5_data M MF U W1 W2 H0 C Cprime T S →
      U ≠ C ∧
        ∃ p : Nat.Primes,
          hoReductionData M MF U W2 H0 p ∧
            quotientChiefFactorData_9_6 M MF H0 W1 p := by
  intro h95
  have h95full := h95
  rcases h95 with
    ⟨h92, hp, _hC, _hBarU, _hCprimeC, _hCprimeEq, _hDade, _hS⟩
  rcases hp with ⟨p, hpdata⟩
  rcases theorem_9_6_source_core_sec9 M MF U W1 W2 H0 C Cprime T S p
      h95full hpdata with
    ⟨hUC, hchief, hWbar2, hcard⟩
  exact ⟨hUC, p, hpdata,
    quotientChiefFactorData_9_6_of_source_facts M MF U W1 W2 H0 p
      h92 hpdata hchief hWbar2 hcard⟩

public theorem theorem_9_6
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (T : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (S : Finset (Section1.ClassFunction M)) :
    notation_9_5_data M MF U W1 W2 H0 C Cprime T S →
      U ≠ C ∧
        ∃ p : Nat.Primes,
          hoReductionData M MF U W2 H0 p ∧
            quotientChiefFactorData_9_6 M MF H0 W1 p := by
  intro h95
  exact theorem_9_6_source_interface M MF U W1 W2 H0 C Cprime T S h95

end CFSG.Section9
