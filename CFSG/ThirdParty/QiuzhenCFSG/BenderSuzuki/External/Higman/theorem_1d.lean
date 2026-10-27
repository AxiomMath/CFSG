module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.theorem_1b
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.lemma_12
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.InvariantComplement
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Quotient

namespace CFSG
end CFSG
open CFSG

/-!
# Higman's classification theorem for Suzuki 2-groups: extracted branch
-/

namespace CFSG.BenderSuzuki
namespace External
namespace Higman

open PFAppendixIII

universe u
/-- Theorem 1(d): in the order-q-cubed case the central quotient is the direct
sum of two K-invariant subgroups of order q. -/
public theorem theorem1_order_center_cube_two_summands
    {K P : Type u} [Group K] [Group P] [MulDistribMulAction K P]
    (hP : IsSuzukiTwoGroup P)
    (hKcyclic : IsCyclic K) (hKfaithful : FaithfulSMul K P)
    (hKregular : ActionRegularOn K P (involutions P))
    (hcard : Nat.card P = Nat.card (Subgroup.center P) ^ 3) :
    ∃ (quotientAction : MulDistribMulAction K (P ⧸ Subgroup.center P))
        (U V : Subgroup (P ⧸ Subgroup.center P)),
      (∀ k : K, ∀ p : P,
        @SMul.smul K (P ⧸ Subgroup.center P) quotientAction.toSMul k
            (QuotientGroup.mk' (Subgroup.center P) p) =
          QuotientGroup.mk' (Subgroup.center P) (k • p)) ∧
      IsXInvariantSubgroup K U ∧ IsXInvariantSubgroup K V ∧
      Nat.card U = Nat.card (Subgroup.center P) ∧
      Nat.card V = Nat.card (Subgroup.center P) ∧
      U ⊓ V = ⊥ ∧ U ⊔ V = ⊤ := by
  classical
  letI : Finite P := finite_of_isSuzukiTwoGroup hP
  letI : FaithfulSMul K P := hKfaithful
  have htoMulAut_injective :
      Function.Injective (MulDistribMulAction.toMulAut K P) := by
    intro x y hxy
    apply FaithfulSMul.eq_of_smul_eq_smul (α := P)
    intro p
    exact congrArg (fun f : MulAut P => f p) hxy
  letI : Finite K := Finite.of_injective
    (MulDistribMulAction.toMulAut K P) htoMulAut_injective
  letI : Fintype K := Fintype.ofFinite K
  letI : MulAction.QuotientAction K (Subgroup.center P) :=
    quotientAction_of_isInvariant (Subgroup.center P)
      ⟨isXInvariantSubgroup_center K P⟩
  let hquotient_action :
      MulDistribMulAction K (P ⧸ Subgroup.center P) :=
    quotientMulDistribMulAction (Subgroup.center P)
      ⟨isXInvariantSubgroup_center K P⟩
  letI : MulDistribMulAction K (P ⧸ Subgroup.center P) :=
    hquotient_action
  have hquotient_action_compatible :
      ∀ k : K, ∀ p : P,
        k • QuotientGroup.mk' (Subgroup.center P) p =
          QuotientGroup.mk' (Subgroup.center P) (k • p) := by
    intro k p
    exact MulAction.Quotient.smul_mk (Subgroup.center P) k p
  have hKtrans : ∀ a : P, a ∈ involutions P →
      ∀ b : P, b ∈ involutions P → ∃ k : K, b = k • a := by
    intro a ha b hb
    rcases hKregular.2 a ha b hb with ⟨k, hk, _huniq⟩
    exact ⟨k, hk⟩
  obtain ⟨x0, _y0, hx0, _hy0, _hxy0⟩ := hP.2.2.1
  let orbit : K → {x : P // x ∈ involutions P} :=
    fun k => ⟨k • x0, hKregular.1 x0 hx0 k⟩
  have horbit_injective : Function.Injective orbit := by
    intro k l hkl
    have heq : k • x0 = l • x0 := congrArg Subtype.val hkl
    rcases hKregular.2 x0 hx0 (k • x0)
        (hKregular.1 x0 hx0 k) with ⟨a, _ha, huniq⟩
    exact (huniq k rfl).trans (huniq l heq).symm
  have horbit_surjective : Function.Surjective orbit := by
    rintro ⟨y, hy⟩
    rcases hKregular.2 x0 hx0 y hy with ⟨k, hk, _huniq⟩
    exact ⟨k, Subtype.ext hk.symm⟩
  have hKcard_invol : Nat.card K =
      Nat.card {x : P // x ∈ involutions P} :=
    Nat.card_congr (Equiv.ofBijective orbit
      ⟨horbit_injective, horbit_surjective⟩)
  have hKprimeSupport : ∀ p : ℕ, p.Prime → p ∣ Nat.card K →
      p ∣ Nat.card {x : P // x ∈ involutions P} := by
    intro p _hp hp
    rw [← hKcard_invol]
    exact hp
  have hLen3 : OmegaLength K P 3 := by
    exact omegaLength_three_of_card_center_cube
      hP hKcyclic hKfaithful hKregular hcard
  rcases lemma12_length_three_typeBCD_summand_data
      hP hKcyclic hKfaithful hKtrans hKprimeSupport hLen3 with
    ⟨_hclassification, B, hdata⟩
  rcases hdata with
    ⟨n, q0, U, hn, hq0_ker, hq0_surj, hq0_equivariant,
      hU_invariant, hU_card, hB_card, hfactor0_card,
      hB_le_center, hinvolution_card⟩
  have hbase_odd : Odd (2 ^ n - 1) := by
    obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    refine ⟨2 ^ e - 1, ?_⟩
    rw [pow_succ]
    have he_pos : 0 < 2 ^ e := by positivity
    omega
  have hKodd : Odd (Fintype.card K) := by
    rw [← Nat.card_eq_fintype_card, hKcard_invol, hinvolution_card]
    exact hbase_odd
  let rho : Representation (ZMod 2) K
      (Additive (LowerCentralFactor P 0)) :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      ((lowerCentralFactorLinearAutHom (H := P) 0).comp
        (MulDistribMulAction.toMulAut K P))
  have hU_rho : ∀ k : K,
      ∀ v ∈ U, rho k v ∈ U := by
    intro k v hv
    change ((lowerCentralFactorLinearAutHom (H := P) 0)
      (MulDistribMulAction.toMulAut K P k)) v ∈ U
    change lowerCentralFactorLinearAut
      (MulDistribMulAction.toMulAut K P k) 0 v ∈ U
    exact hU_invariant k v hv
  obtain ⟨W, hUW, hW_rho⟩ :=
    exists_isCompl_invariant_of_odd_group hKodd rho U hU_rho
  have hW_invariant : ∀ k : K,
      ∀ v ∈ W,
        lowerCentralFactorLinearAut
          (MulDistribMulAction.toMulAut K P k) 0 v ∈ W := by
    intro k v hv
    have h := hW_rho k v hv
    change ((lowerCentralFactorLinearAutHom (H := P) 0)
      (MulDistribMulAction.toMulAut K P k)) v ∈ W at h
    change lowerCentralFactorLinearAut
      (MulDistribMulAction.toMulAut K P k) 0 v ∈ W at h
    exact h
  have hfactor0_card_UW :
      Nat.card (LowerCentralFactor P 0) = Nat.card U * Nat.card W := by
    change Nat.card (Additive (LowerCentralFactor P 0)) =
      Nat.card U * Nat.card W
    calc
      Nat.card (Additive (LowerCentralFactor P 0)) = Nat.card (U × W) := by
        exact (Nat.card_congr
          (Submodule.prodEquivOfIsCompl U W hUW).toEquiv).symm
      _ = Nat.card U * Nat.card W := Nat.card_prod U W
  have hW_card : Nat.card W = 2 ^ n := by
    have hmul : (2 ^ n) * Nat.card W = (2 ^ n) * (2 ^ n) := by
      calc
        (2 ^ n) * Nat.card W =
            Nat.card (LowerCentralFactor P 0) := by
          rw [← hU_card]
          exact hfactor0_card_UW.symm
        _ = (2 ^ n) ^ 2 := hfactor0_card
        _ = (2 ^ n) * (2 ^ n) := by ring
    exact Nat.mul_left_cancel (by positivity : 0 < 2 ^ n) hmul
  letI : B.Normal := by
    rw [← hq0_ker]
    infer_instance
  let eB : P ⧸ B ≃* LowerCentralFactor P 0 :=
    (QuotientGroup.quotientMulEquivOfEq hq0_ker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q0 hq0_surj)
  have hquotientB_card :
      Nat.card (P ⧸ B) = Nat.card (LowerCentralFactor P 0) :=
    Nat.card_congr eB.toEquiv
  have hP_card_n : Nat.card P = (2 ^ n) ^ 3 := by
    calc
      Nat.card P = Nat.card (P ⧸ B) * Nat.card B :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup B
      _ = (2 ^ n) ^ 3 := by
        rw [hquotientB_card, hfactor0_card, hB_card]
        ring
  have hcenter_card : Nat.card (Subgroup.center P) = 2 ^ n := by
    apply Nat.pow_left_injective (by norm_num : (3 : ℕ) ≠ 0)
    exact hcard.symm.trans hP_card_n
  have hB_eq_center : B = Subgroup.center P := by
    apply Subgroup.eq_of_le_of_card_ge hB_le_center
    rw [hB_card, hcenter_card]
  have hq0_ker_center : q0.ker = Subgroup.center P :=
    hq0_ker.trans hB_eq_center
  let eQ : P ⧸ Subgroup.center P ≃* LowerCentralFactor P 0 :=
    (QuotientGroup.quotientMulEquivOfEq hq0_ker_center.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q0 hq0_surj)
  have heQ_mk (p : P) :
      eQ (QuotientGroup.mk' (Subgroup.center P) p) = q0 p := by
    change QuotientGroup.kerLift q0
        (QuotientGroup.quotientMulEquivOfEq hq0_ker_center.symm
          (QuotientGroup.mk' (Subgroup.center P) p)) = q0 p
    calc
      QuotientGroup.kerLift q0
          (QuotientGroup.quotientMulEquivOfEq hq0_ker_center.symm
            (QuotientGroup.mk' (Subgroup.center P) p)) =
        QuotientGroup.kerLift q0
          (QuotientGroup.mk' q0.ker p) := by
            congr 1
      _ = q0 p := QuotientGroup.kerLift_mk q0 p
  let factorSubgroupEquiv : Subgroup (LowerCentralFactor P 0) ≃o
      Submodule (ZMod 2) (Additive (LowerCentralFactor P 0)) :=
    Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := 2))
  let UF : Subgroup (LowerCentralFactor P 0) := factorSubgroupEquiv.symm U
  let WF : Subgroup (LowerCentralFactor P 0) := factorSubgroupEquiv.symm W
  have hUFWF : IsCompl UF WF := by
    apply factorSubgroupEquiv.isCompl_iff.mpr
    simpa [UF, WF] using hUW
  let eUF : U ≃ UF :=
    { toFun := fun u => ⟨u.1.toMul, by
        change Additive.ofMul u.1.toMul ∈ U
        exact u.property⟩
      invFun := fun f => ⟨Additive.ofMul f.1, by
        have hf := f.property
        change Additive.ofMul f.1 ∈ U at hf
        exact hf⟩
      left_inv := by intro u; rfl
      right_inv := by intro f; rfl }
  let eWF : W ≃ WF :=
    { toFun := fun w => ⟨w.1.toMul, by
        change Additive.ofMul w.1.toMul ∈ W
        exact w.property⟩
      invFun := fun f => ⟨Additive.ofMul f.1, by
        have hf := f.property
        change Additive.ofMul f.1 ∈ W at hf
        exact hf⟩
      left_inv := by intro w; rfl
      right_inv := by intro f; rfl }
  let Uq : Subgroup (P ⧸ Subgroup.center P) :=
    UF.comap eQ.toMonoidHom
  let Vq : Subgroup (P ⧸ Subgroup.center P) :=
    WF.comap eQ.toMonoidHom
  have hUq_eq_map : Uq = (MulEquiv.mapSubgroup eQ.symm) UF := by
    exact Subgroup.comap_equiv_eq_map_symm eQ UF
  have hVq_eq_map : Vq = (MulEquiv.mapSubgroup eQ.symm) WF := by
    exact Subgroup.comap_equiv_eq_map_symm eQ WF
  have hUqVq : IsCompl Uq Vq := by
    rw [hUq_eq_map, hVq_eq_map]
    exact (MulEquiv.mapSubgroup eQ.symm).isCompl_iff.mp hUFWF
  have hUq_forward : ∀ k : K, ∀ q : P ⧸ Subgroup.center P,
      q ∈ Uq → k • q ∈ Uq := by
    intro k q hq
    obtain ⟨p, rfl⟩ :=
      QuotientGroup.mk'_surjective (Subgroup.center P) q
    have hpU : Additive.ofMul (q0 p) ∈ U := by
      have hmem : eQ (QuotientGroup.mk' (Subgroup.center P) p) ∈ UF := by
        simpa [Uq] using hq
      change Additive.ofMul
          (eQ (QuotientGroup.mk' (Subgroup.center P) p)) ∈ U at hmem
      rw [heQ_mk] at hmem
      exact hmem
    have hfactor : Additive.ofMul
        (eQ (k • QuotientGroup.mk' (Subgroup.center P) p)) ∈ U := by
      rw [hquotient_action_compatible, heQ_mk, hq0_equivariant]
      exact hU_invariant k _ hpU
    have hfactor' :
        eQ (k • QuotientGroup.mk' (Subgroup.center P) p) ∈ UF := by
      simpa [UF, factorSubgroupEquiv] using hfactor
    simpa [Uq] using hfactor'
  have hVq_forward : ∀ k : K, ∀ q : P ⧸ Subgroup.center P,
      q ∈ Vq → k • q ∈ Vq := by
    intro k q hq
    obtain ⟨p, rfl⟩ :=
      QuotientGroup.mk'_surjective (Subgroup.center P) q
    have hpW : Additive.ofMul (q0 p) ∈ W := by
      have hmem : eQ (QuotientGroup.mk' (Subgroup.center P) p) ∈ WF := by
        simpa [Vq] using hq
      change Additive.ofMul
          (eQ (QuotientGroup.mk' (Subgroup.center P) p)) ∈ W at hmem
      rw [heQ_mk] at hmem
      exact hmem
    have hfactor : Additive.ofMul
        (eQ (k • QuotientGroup.mk' (Subgroup.center P) p)) ∈ W := by
      rw [hquotient_action_compatible, heQ_mk, hq0_equivariant]
      exact hW_invariant k _ hpW
    have hfactor' :
        eQ (k • QuotientGroup.mk' (Subgroup.center P) p) ∈ WF := by
      simpa [WF, factorSubgroupEquiv] using hfactor
    simpa [Vq] using hfactor'
  have hUq_invariant : IsXInvariantSubgroup K Uq := by
    intro k q
    constructor
    · exact hUq_forward k q
    · intro hq
      have hback := hUq_forward k⁻¹ (k • q) hq
      simpa [smul_smul] using hback
  have hVq_invariant : IsXInvariantSubgroup K Vq := by
    intro k q
    constructor
    · exact hVq_forward k q
    · intro hq
      have hback := hVq_forward k⁻¹ (k • q) hq
      simpa [smul_smul] using hback
  have hUq_card : Nat.card Uq = Nat.card (Subgroup.center P) := by
    calc
      Nat.card Uq = Nat.card UF := by
        rw [hUq_eq_map]
        exact (Nat.card_congr (eQ.symm.subgroupMap UF).toEquiv).symm
      _ = Nat.card U := (Nat.card_congr eUF).symm
      _ = 2 ^ n := hU_card
      _ = Nat.card (Subgroup.center P) := hcenter_card.symm
  have hVq_card : Nat.card Vq = Nat.card (Subgroup.center P) := by
    calc
      Nat.card Vq = Nat.card WF := by
        rw [hVq_eq_map]
        exact (Nat.card_congr (eQ.symm.subgroupMap WF).toEquiv).symm
      _ = Nat.card W := (Nat.card_congr eWF).symm
      _ = 2 ^ n := hW_card
      _ = Nat.card (Subgroup.center P) := hcenter_card.symm
  exact ⟨hquotient_action, Uq, Vq, hquotient_action_compatible,
    hUq_invariant, hVq_invariant, hUq_card, hVq_card,
    hUqVq.inf_eq_bot, hUqVq.sup_eq_top⟩
end Higman
end External
end CFSG.BenderSuzuki
