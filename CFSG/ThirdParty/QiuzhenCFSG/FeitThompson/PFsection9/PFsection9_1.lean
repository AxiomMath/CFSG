module

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Remaining
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Wielandt
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.Basic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped BigOperators IsMulCommutative

namespace CFSG.Section9

universe v
universe w
universe u

public theorem subgroupCentralizerIn_sup_le_left_sec9
    {G : Type u} [Group G]
    (H U E : Subgroup G) :
    subgroupCentralizerIn H (U ⊔ E) ≤ subgroupCentralizerIn H U := by
  intro x hx
  have hx' : x ∈ H ∧ x ∈ Subgroup.centralizer ((U ⊔ E : Subgroup G) : Set G) := by
    simpa [subgroupCentralizerIn] using hx
  have hxU : x ∈ Subgroup.centralizer (U : Set G) := by
    rw [Subgroup.mem_centralizer_iff] at hx' ⊢
    intro u hu
    exact hx'.2 u ((show U ≤ U ⊔ E from le_sup_left) hu)
  simpa [subgroupCentralizerIn] using And.intro hx'.1 hxU

public theorem subgroupCentralizerIn_sup_le_right_sec9
    {G : Type u} [Group G]
    (H U E : Subgroup G) :
    subgroupCentralizerIn H (U ⊔ E) ≤ subgroupCentralizerIn H E := by
  intro x hx
  have hx' : x ∈ H ∧ x ∈ Subgroup.centralizer ((U ⊔ E : Subgroup G) : Set G) := by
    simpa [subgroupCentralizerIn] using hx
  have hxE : x ∈ Subgroup.centralizer (E : Set G) := by
    rw [Subgroup.mem_centralizer_iff] at hx' ⊢
    intro e he
    exact hx'.2 e ((show E ≤ U ⊔ E from le_sup_right) he)
  simpa [subgroupCentralizerIn] using And.intro hx'.1 hxE

public theorem subgroupCentralizerIn_eq_left_of_card_eq_sec9
    {G : Type u} [Group G] [Finite G]
    (H S : Subgroup G) :
    Nat.card (subgroupCentralizerIn H S) = Nat.card H →
      subgroupCentralizerIn H S = H := by
  intro hcard
  let Csub : Subgroup H := (subgroupCentralizerIn H S).subgroupOf H
  have hCsub_card : Nat.card Csub = Nat.card H := by
    simpa [Csub] using
      (natCard_subgroupOf_eq (subgroupCentralizerIn H S) H inf_le_left).trans hcard
  have hCsub_top : Csub = ⊤ :=
    (Subgroup.card_eq_iff_eq_top (H := Csub)).1 hCsub_card
  apply le_antisymm
  · exact inf_le_left
  · intro x hxH
    have hxCsub : (⟨x, hxH⟩ : H) ∈ Csub := by
      simp [hCsub_top]
    simpa [Csub, Subgroup.mem_subgroupOf] using hxCsub

private theorem frobeniusActionData_nat_card_eq_mul_sec9
    {G : Type u} [Group G] [Finite G]
    (UE U E H : Subgroup G) :
    frobeniusActionData UE U E H →
      Nat.card UE = Nat.card U * Nat.card E := by
  classical
  intro h91
  rcases h91 with ⟨hcomp, hfrob, _hUE_norm_H, _hH_solv, _hcop⟩
  have hUnorm : (U.subgroupOf UE).Normal := by
    have hUnormSup : (U.subgroupOf (U ⊔ E)).Normal :=
      IsFrobeniusGroupWithKernelComplement.normal hfrob
    have hUEeq : UE = U ⊔ E := hcomp.2.2.1
    subst UE
    simpa using hUnormSup
  have hdisjSub : Disjoint (U.subgroupOf UE) (E.subgroupOf UE) := by
    have hdisj := hcomp.2.2.2
    rw [disjoint_iff] at hdisj ⊢
    apply le_antisymm
    · intro x hx
      have hxAmb : (x : G) ∈ U ⊓ E := by
        exact ⟨by simpa [Subgroup.mem_subgroupOf] using hx.1,
          by simpa [Subgroup.mem_subgroupOf] using hx.2⟩
      have hxBot : (x : G) ∈ (⊥ : Subgroup G) := by
        simpa [hdisj] using hxAmb
      ext
      simpa using hxBot
    · exact bot_le
  have hsupTop : U.subgroupOf UE ⊔ E.subgroupOf UE = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := U) (A' := E) (B := UE) hcomp.1 hcomp.2.1]
    rw [← hcomp.2.2.1]
    exact Subgroup.subgroupOf_eq_top.2 le_rfl
  have hcompSub : (U.subgroupOf UE).IsComplement' (E.subgroupOf UE) := by
    letI : (U.subgroupOf UE).Normal := hUnorm
    exact isComplement'_of_disjoint_sup_eq_top_of_normal
      (U.subgroupOf UE) (E.subgroupOf UE) hdisjSub hsupTop
  have hmul := hcompSub.card_mul
  simpa [natCard_subgroupOf_eq U UE hcomp.1,
    natCard_subgroupOf_eq E UE hcomp.2.1] using hmul.symm

private theorem subgroupCentralizerIn_conjBy_nat_card_eq_of_mem_normalizer_sec9
    {G : Type u} [Group G] [Finite G]
    (H E : Subgroup G) {g : G}
    (hgH : g ∈ Subgroup.normalizer (H : Set G)) :
    Nat.card (subgroupCentralizerIn H (E.conjBy g)) =
      Nat.card (subgroupCentralizerIn H E) := by
  rw [section11_subgroupCentralizerIn_conjBy_eq_self_of_mem_normalizer hgH]
  exact section11_card_conjBy (subgroupCentralizerIn H E) g

private noncomputable def theorem_9_1_conjugate_complement_product_sec9
    {G : Type u} [Group G] [Finite G]
    (U E H : Subgroup G) : ℕ :=
  letI : Fintype U := Fintype.ofFinite U
  ∏ u : U,
    Nat.card (subgroupCentralizerIn H (E.conjBy (u : G))) ^
      Nat.card (E.conjBy (u : G))

private theorem frobeniusActionData_conjugate_complement_product_eq_power_sec9
    {G : Type u} [Group G] [Finite G]
    (UE U E H : Subgroup G) :
    frobeniusActionData UE U E H →
      theorem_9_1_conjugate_complement_product_sec9 U E H =
        Nat.card (subgroupCentralizerIn H E) ^ (Nat.card E * Nat.card U) := by
  intro h91
  letI : Fintype U := Fintype.ofFinite U
  dsimp [theorem_9_1_conjugate_complement_product_sec9]
  rcases h91 with ⟨hcomp, _hfrob, hUE_norm_H, _hH_solv, _hcop⟩
  have hterm : ∀ u : U,
      Nat.card (subgroupCentralizerIn H (E.conjBy (u : G))) ^
          Nat.card (E.conjBy (u : G)) =
        Nat.card (subgroupCentralizerIn H E) ^ Nat.card E := by
    intro u
    have hu_norm : (u : G) ∈ Subgroup.normalizer (H : Set G) :=
      hUE_norm_H (hcomp.1 u.property)
    have hcent :=
      subgroupCentralizerIn_conjBy_nat_card_eq_of_mem_normalizer_sec9 H E hu_norm
    have hEcard : Nat.card (E.conjBy (u : G)) = Nat.card E :=
      section11_card_conjBy E (u : G)
    rw [hcent, hEcard]
  calc
    (∏ u : U,
        Nat.card (subgroupCentralizerIn H (E.conjBy (u : G))) ^
          Nat.card (E.conjBy (u : G)))
        = ∏ _u : U, Nat.card (subgroupCentralizerIn H E) ^ Nat.card E := by
          exact Finset.prod_congr rfl (fun u _hu => hterm u)
    _ = (Nat.card (subgroupCentralizerIn H E) ^ Nat.card E) ^ Nat.card U := by
      rw [Finset.prod_const]
      simp [Nat.card_eq_fintype_card]
    _ = Nat.card (subgroupCentralizerIn H E) ^ (Nat.card E * Nat.card U) := by
      rw [pow_mul]

private theorem fixedPointSubgroup_card_eq_subgroupCentralizerIn_sec9
    {G : Type u} [Group G] [Finite G]
    (H R : Subgroup G)
    (hRnormH : R ≤ Subgroup.normalizer (H : Set G)) :
    letI : Subgroup.Normalizes R H := ⟨hRnormH⟩
    Nat.card (fixedPointSubgroup (↥R) H) =
      Nat.card (subgroupCentralizerIn H R) := by
  letI : Subgroup.Normalizes R H := ⟨hRnormH⟩
  have hfix : fixedPointSubgroup (↥R) H =
      (subgroupCentralizerIn H R).subgroupOf H := by
    simpa using fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn H R hRnormH
  calc
    Nat.card (fixedPointSubgroup (↥R) H) =
        Nat.card ((subgroupCentralizerIn H R).subgroupOf H) := by
          rw [hfix]
    _ = Nat.card (subgroupCentralizerIn H R) := by
          exact natCard_subgroupOf_eq (subgroupCentralizerIn H R) H inf_le_left


private noncomputable def theorem_9_1_fixedPoint_conjugate_complement_product_sec9
    {G : Type u} [Group G] [Finite G]
    (U E H : Subgroup G)
    (hEnormH : ∀ u : U, E.conjBy (u : G) ≤ Subgroup.normalizer (H : Set G)) : ℕ :=
  letI : Fintype U := Fintype.ofFinite U
  ∏ u : U,
    letI : Subgroup.Normalizes (E.conjBy (u : G)) H := ⟨hEnormH u⟩
    Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) H) ^
      Nat.card (E.conjBy (u : G))

private theorem theorem_9_1_fixedPoint_conjugate_complement_product_eq_centralizer_product_sec9
    {G : Type u} [Group G] [Finite G]
    (U E H : Subgroup G)
    (hEnormH : ∀ u : U, E.conjBy (u : G) ≤ Subgroup.normalizer (H : Set G)) :
    theorem_9_1_fixedPoint_conjugate_complement_product_sec9 U E H hEnormH =
      theorem_9_1_conjugate_complement_product_sec9 U E H := by
  letI : Fintype U := Fintype.ofFinite U
  dsimp [theorem_9_1_fixedPoint_conjugate_complement_product_sec9,
    theorem_9_1_conjugate_complement_product_sec9]
  apply Finset.prod_congr rfl
  intro u _hu
  have hcard :=
    fixedPointSubgroup_card_eq_subgroupCentralizerIn_sec9 H
      (E.conjBy (u : G)) (hEnormH u)
  rw [hcard]


private noncomputable def theorem_9_1_fixedPoint_conjugate_action_product_sec9
    {G M : Type u} [Group G] [Finite G] [Group M] [Finite M]
    (U E : Subgroup G)
    (hEact : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) M) : ℕ :=
  letI : Fintype U := Fintype.ofFinite U
  ∏ u : U,
    letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
    Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) M) ^
      Nat.card (E.conjBy (u : G))


private theorem theorem_9_1_fixedPoint_conjugate_complement_product_eq_action_product_sec9
    {G : Type u} [Group G] [Finite G]
    (U E H : Subgroup G)
    (hEnormH : ∀ u : U, E.conjBy (u : G) ≤ Subgroup.normalizer (H : Set G)) :
    let hEact : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) H := fun u => by
      letI : Subgroup.Normalizes (E.conjBy (u : G)) H := ⟨hEnormH u⟩
      infer_instance
    theorem_9_1_fixedPoint_conjugate_complement_product_sec9 U E H hEnormH =
      theorem_9_1_fixedPoint_conjugate_action_product_sec9 U E hEact := by
  classical
  letI : Fintype U := Fintype.ofFinite U
  dsimp [theorem_9_1_fixedPoint_conjugate_complement_product_sec9,
    theorem_9_1_fixedPoint_conjugate_action_product_sec9]


private theorem section12ComplementIn_conj_complement_le_sec9
    {G : Type u} [Group G]
    (UE U E : Subgroup G) :
    section12ComplementIn UE U E →
      ∀ u : U, E.conjBy (u : G) ≤ UE := by
  intro hcomp u x hx
  rw [Subgroup.conjBy, Subgroup.mem_map] at hx
  rcases hx with ⟨e, heE, hxe⟩
  rw [← hxe]
  exact UE.mul_mem (UE.mul_mem (hcomp.1 u.property) (hcomp.2.1 heE))
    (UE.inv_mem (hcomp.1 u.property))


public theorem theorem_9_1_ofElementaryAbelianAction_irreducible_of_minimal_invariant_sec9
    {A M : Type u} [Group A] [Group M] [MulDistribMulAction A M]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p M] [Nontrivial M]
    (hminv : ∀ N : Subgroup M, N.Normal → IsInvariant A M N → N ≠ ⊥ → N = ⊤) :
    letI : CommGroup M := IsMulCommutative.instCommGroup
    Representation.IsIrreducible
      (Theory.Representation.ofElementaryAbelianAction (A := A) (G := M) (p := p) :
        Representation (ZMod p) A (Additive M)) := by
  letI : CommGroup M := IsMulCommutative.instCommGroup
  let ρ : Representation (ZMod p) A (Additive M) :=
    Theory.Representation.ofElementaryAbelianAction (A := A) (G := M) (p := p)
  refine
    { toNontrivial := inferInstance
      eq_bot_or_eq_top := ?_ }
  intro S
  let N : Subgroup M := S.toSubmodule.toAddSubgroup.toSubgroup'
  have hN_inv : IsInvariant A M N := by
    have hmap_mem (a : A) {x : M} (hx : x ∈ N) : a • x ∈ N := by
      change Additive.ofMul (a • x) ∈ S.toSubmodule
      have hx' : Additive.ofMul x ∈ S.toSubmodule := by
        change Additive.ofMul x ∈ S.toSubmodule at hx
        exact hx
      have hx'' := S.apply_mem_toSubmodule a hx'
      simpa [ρ, Theory.Representation.ofElementaryAbelianAction_apply_ofMul] using hx''
    refine { invariant := ?_ }
    intro a x
    constructor
    · intro hx
      exact hmap_mem a hx
    · intro hx
      have hx' : (a : A)⁻¹ • ((a : A) • x) ∈ N := hmap_mem (a : A)⁻¹ hx
      simpa [smul_smul] using hx'
  by_cases hN_bot : N = ⊥
  · left
    apply Subrepresentation.toSubmodule_injective
    ext x
    have hxN : Additive.toMul x ∈ N ↔ x ∈ S.toSubmodule := by
      simp [N]
    rw [← hxN, hN_bot]
    constructor
    · intro hx
      simpa [hx]
    · intro hx
      have hx' : x ∈ (⊥ : Submodule (ZMod p) (Additive M)) := by
        let Z : Subrepresentation
            (Theory.Representation.ofElementaryAbelianAction (A := A) (G := M) (p := p) :
              Representation (ZMod p) A (Additive M)) :=
          { toSubmodule := ⊥
            apply_mem_toSubmodule := by simp }
        have hxZ : x ∈ Z :=
          (show (⊥ : Subrepresentation
            (Theory.Representation.ofElementaryAbelianAction (A := A) (G := M) (p := p) :
              Representation (ZMod p) A (Additive M))) ≤ Z from bot_le) hx
        exact hxZ
      simpa using hx'
  · right
    have hN_top : N = ⊤ := hminv N inferInstance hN_inv hN_bot
    apply Subrepresentation.toSubmodule_injective
    ext x
    have hxN : Additive.toMul x ∈ N ↔ x ∈ S.toSubmodule := by
      simp [N]
    rw [← hxN, hN_top]
    constructor
    · intro _hx
      exact Submodule.mem_top
    · intro _hx
      simp


private theorem theorem_9_1_wielandt_fixedPoint_product_identity_action_source_bridge_sec9
    {G M : Type u} [Group G] [Finite G] [Group M] [Finite M]
    (UE U E : Subgroup G)
    [MulDistribMulAction UE M] [MulDistribMulAction U M]
    (hEact : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) M)
    (hcomp : section12ComplementIn UE U E)
    (hfrob : section12FrobeniusJoinWithKernel U E)
    (hsolvM : IsSolvable M)
    (hcop : Nat.Coprime (Nat.card M) (Nat.card UE))
    (hUcompat : ∀ (u : U) (m : M),
      u • m = (⟨(u : G), hcomp.1 u.2⟩ : UE) • m)
    (hEcompat : ∀ (u : U) (e : E.conjBy (u : G)) (m : M),
      letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      e • m =
        (⟨(e : G), section12ComplementIn_conj_complement_le_sec9 UE U E hcomp u e.2⟩ :
          UE) • m) :
    letI : Fintype U := Fintype.ofFinite U
    Nat.card (fixedPointSubgroup (↥UE) M) ^ Nat.card UE *
        Nat.card M ^ Nat.card U =
      theorem_9_1_fixedPoint_conjugate_action_product_sec9 U E hEact *
        Nat.card (fixedPointSubgroup (↥U) M) ^ Nat.card U := by
  classical
  have hEcompat' : ∀ (u : U) (e : E.conjBy (u : G)) (m : M),
      letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      e • m =
        (⟨(e : G), Wielandt.section12ComplementIn_conj_complement_le UE U E hcomp u e.2⟩ :
          UE) • m := by
    intro u e m
    simpa using hEcompat u e m
  have haction :=
    Wielandt.fixedPointSubgroup_product_identity_action
      (UE := UE) (U := U) (E := E) (M := M)
      hEact hcomp hfrob hsolvM hcop hUcompat hEcompat'
  rw [Wielandt.fixedPointSubgroup_conjBy_action_product_eq_prod U E hEact] at haction
  simpa [theorem_9_1_fixedPoint_conjugate_action_product_sec9] using haction

private theorem theorem_9_1_wielandt_fixedPoint_product_identity_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (UE U E H : Subgroup G)
    (h91 : frobeniusActionData UE U E H)
    (hUE_norm_H : UE ≤ Subgroup.normalizer (H : Set G))
    (hU_norm_H : U ≤ Subgroup.normalizer (H : Set G))
    (hEnormH : ∀ u : U, E.conjBy (u : G) ≤ Subgroup.normalizer (H : Set G)) :
    letI : Subgroup.Normalizes UE H := ⟨hUE_norm_H⟩
    letI : Subgroup.Normalizes U H := ⟨hU_norm_H⟩
    Nat.card (fixedPointSubgroup (↥UE) H) ^ Nat.card UE *
        Nat.card H ^ Nat.card U =
      theorem_9_1_fixedPoint_conjugate_complement_product_sec9 U E H hEnormH *
        Nat.card (fixedPointSubgroup (↥U) H) ^ Nat.card U := by
  classical
  rcases h91 with ⟨hcomp, hfrob, _hUE_norm_H', hsolvH, hcopHUE⟩
  letI : Subgroup.Normalizes UE H := ⟨hUE_norm_H⟩
  letI : Subgroup.Normalizes U H := ⟨hU_norm_H⟩
  let hEact : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) H := fun u => by
    letI : Subgroup.Normalizes (E.conjBy (u : G)) H := ⟨hEnormH u⟩
    infer_instance
  have hUcompat : ∀ (u : U) (h : H),
      u • h = (⟨(u : G), hcomp.1 u.2⟩ : UE) • h := by
    intro u h
    ext
    simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
  have hEcompat : ∀ (u : U) (e : E.conjBy (u : G)) (h : H),
      letI : MulDistribMulAction (↥(E.conjBy (u : G))) H := hEact u
      e • h =
        (⟨(e : G), section12ComplementIn_conj_complement_le_sec9 UE U E hcomp u e.2⟩ :
          UE) • h := by
    intro u e h
    ext
    simp [hEact, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
  have haction :=
    theorem_9_1_wielandt_fixedPoint_product_identity_action_source_bridge_sec9
      (UE := UE) (U := U) (E := E) (M := H) hEact hcomp hfrob hsolvH hcopHUE
      hUcompat hEcompat
  rw [theorem_9_1_fixedPoint_conjugate_complement_product_eq_action_product_sec9 U E H hEnormH]
  simpa [hEact] using haction

private theorem theorem_9_1_wielandt_conjugate_product_identity_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (UE U E H : Subgroup G) :
    frobeniusActionData UE U E H →
      Nat.card (subgroupCentralizerIn H UE) ^ Nat.card UE *
          Nat.card H ^ Nat.card U =
        theorem_9_1_conjugate_complement_product_sec9 U E H *
          Nat.card (subgroupCentralizerIn H U) ^ Nat.card U := by
  intro h91
  have h91_all : frobeniusActionData UE U E H := h91
  rcases h91 with ⟨hcomp, _hfrob, hUE_norm_H, _hH_solv, _hcop⟩
  have hU_norm_H : U ≤ Subgroup.normalizer (H : Set G) :=
    fun u hu => hUE_norm_H (hcomp.1 hu)
  have hEnormH :
      ∀ u : U, E.conjBy (u : G) ≤ Subgroup.normalizer (H : Set G) := by
    intro u x hx
    apply hUE_norm_H
    rw [Subgroup.conjBy, Subgroup.mem_map] at hx
    rcases hx with ⟨e, heE, hxe⟩
    rw [← hxe]
    exact UE.mul_mem (UE.mul_mem (hcomp.1 u.property) (hcomp.2.1 heE))
      (UE.inv_mem (hcomp.1 u.property))
  have hfixed :=
    theorem_9_1_wielandt_fixedPoint_product_identity_source_bridge_sec9
      UE U E H h91_all hUE_norm_H hU_norm_H hEnormH
  letI : Subgroup.Normalizes UE H := ⟨hUE_norm_H⟩
  letI : Subgroup.Normalizes U H := ⟨hU_norm_H⟩
  have hUEcard :=
    fixedPointSubgroup_card_eq_subgroupCentralizerIn_sec9 H UE hUE_norm_H
  have hUcard :=
    fixedPointSubgroup_card_eq_subgroupCentralizerIn_sec9 H U hU_norm_H
  have hprod :=
    theorem_9_1_fixedPoint_conjugate_complement_product_eq_centralizer_product_sec9
      U E H hEnormH
  rw [hUEcard, hUcard, hprod] at hfixed
  exact hfixed

private theorem theorem_9_1_wielandt_product_identity_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (UE U E H : Subgroup G) :
    frobeniusActionData UE U E H →
      Nat.card (subgroupCentralizerIn H UE) ^ Nat.card UE *
          Nat.card H ^ Nat.card U =
        Nat.card (subgroupCentralizerIn H E) ^ (Nat.card E * Nat.card U) *
          Nat.card (subgroupCentralizerIn H U) ^ Nat.card U := by
  intro h91
  have hprod :=
    theorem_9_1_wielandt_conjugate_product_identity_source_bridge_sec9 UE U E H h91
  rw [hprod]
  rw [frobeniusActionData_conjugate_complement_product_eq_power_sec9 UE U E H h91]

private theorem theorem_9_1_wielandt_power_identity_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (UE U E H : Subgroup G) :
    frobeniusActionData UE U E H →
      (Nat.card (subgroupCentralizerIn H (U ⊔ E)) ^ Nat.card E *
          Nat.card H) ^ Nat.card U =
        (Nat.card (subgroupCentralizerIn H E) ^ Nat.card E *
            Nat.card (subgroupCentralizerIn H U)) ^ Nat.card U := by
  intro h91
  rcases h91 with ⟨hcomp, hfrob, hUE_norm_H, hH_solv, hcop⟩
  have h91' : frobeniusActionData UE U E H :=
    ⟨hcomp, hfrob, hUE_norm_H, hH_solv, hcop⟩
  have hraw := theorem_9_1_wielandt_product_identity_source_bridge_sec9 UE U E H h91'
  have hcardUE := frobeniusActionData_nat_card_eq_mul_sec9 UE U E H h91'
  have hUEeq : UE = U ⊔ E := hcomp.2.2.1
  rw [hUEeq] at hraw hcardUE
  rw [mul_pow, mul_pow]
  rw [← pow_mul, ← pow_mul]
  rw [← hraw]
  rw [hcardUE, Nat.mul_comm (Nat.card U) (Nat.card E)]

public theorem theorem_9_1_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (UE U E H : Subgroup G) :
    frobeniusActionData UE U E H →
      Nat.card (subgroupCentralizerIn H (U ⊔ E)) ^ Nat.card E * Nat.card H =
        Nat.card (subgroupCentralizerIn H E) ^ Nat.card E *
          Nat.card (subgroupCentralizerIn H U) := by
  intro h91
  have hpow :=
    theorem_9_1_wielandt_power_identity_source_bridge_sec9 UE U E H h91
  exact Nat.pow_left_injective (Nat.card_pos (α := U)).ne' hpow

public theorem theorem_9_1_centralizes_of_fixed_points_trivial_sec9
    {G : Type u} [Group G] [Finite G]
    (U E H : Subgroup G)
    (hcard : Nat.card (subgroupCentralizerIn H (U ⊔ E)) ^ Nat.card E * Nat.card H =
      Nat.card (subgroupCentralizerIn H E) ^ Nat.card E *
        Nat.card (subgroupCentralizerIn H U)) :
    subgroupCentralizerIn H E = ⊥ → subgroupCentralizerIn H U = H := by
  intro hCE_bot
  have hCUE_bot : subgroupCentralizerIn H (U ⊔ E) = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hxE := subgroupCentralizerIn_sup_le_right_sec9 H U E hx
      simpa [hCE_bot] using hxE
    · exact bot_le
  have hCU_card : Nat.card (subgroupCentralizerIn H U) = Nat.card H := by
    have h := hcard.symm
    simpa [hCUE_bot, hCE_bot] using h
  exact subgroupCentralizerIn_eq_left_of_card_eq_sec9 H U hCU_card

public theorem theorem_9_1_card_eq_of_kernel_fixed_points_trivial_sec9
    {G : Type u} [Group G] [Finite G]
    (U E H : Subgroup G)
    (hcard : Nat.card (subgroupCentralizerIn H (U ⊔ E)) ^ Nat.card E * Nat.card H =
      Nat.card (subgroupCentralizerIn H E) ^ Nat.card E *
        Nat.card (subgroupCentralizerIn H U)) :
    subgroupCentralizerIn H U = ⊥ →
      Nat.card H = Nat.card (subgroupCentralizerIn H E) ^ Nat.card E := by
  intro hCU_bot
  have hCUE_bot : subgroupCentralizerIn H (U ⊔ E) = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hxU := subgroupCentralizerIn_sup_le_left_sec9 H U E hx
      simpa [hCU_bot] using hxU
    · exact bot_le
  simpa [hCUE_bot, hCU_bot] using hcard

public theorem theorem_9_1
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (UE U E H : Subgroup G) :
    frobeniusActionData UE U E H →
      Nat.card (subgroupCentralizerIn H (U ⊔ E)) ^ Nat.card E * Nat.card H =
        Nat.card (subgroupCentralizerIn H E) ^ Nat.card E *
          Nat.card (subgroupCentralizerIn H U) ∧
        (subgroupCentralizerIn H E = ⊥ → subgroupCentralizerIn H U = H) ∧
        (subgroupCentralizerIn H U = ⊥ →
          Nat.card H = Nat.card (subgroupCentralizerIn H E) ^ Nat.card E) := by
  intro h91
  have hcard := theorem_9_1_source_core_sec9 UE U E H h91
  exact ⟨hcard,
    theorem_9_1_centralizes_of_fixed_points_trivial_sec9 U E H hcard,
    theorem_9_1_card_eq_of_kernel_fixed_points_trivial_sec9 U E H hcard⟩

end CFSG.Section9
