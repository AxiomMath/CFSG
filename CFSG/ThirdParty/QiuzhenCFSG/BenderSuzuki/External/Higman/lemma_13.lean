module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.lemma_9
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.lemma_11
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.lemma_12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.InvariantComplement
import Mathlib.Order.RelSeries
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Commutator.Core
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Invariant
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Quotient

namespace CFSG
end CFSG
open CFSG

/-!
# Higman Lemma 13
-/

namespace CFSG.BenderSuzuki
namespace External
namespace Higman

open scoped IsMulCommutative commutatorElement

open PFAppendixIII

universe u

private theorem lemma13_no_four_step_abelian_exponent_four
    {X P : Type u} [Group X] [Group P] [MulDistribMulAction X P]
    (hP : IsSuzukiTwoGroup P)
    (hXtrans : ∀ x : P, x ∈ involutions P →
      ∀ y : P, y ∈ involutions P → ∃ k : X, y = k • x)
    {A B C : Subgroup P}
    (hAcomm : IsMulCommutative A) (hAX : IsXInvariantSubgroup X A)
    (hAexp : ∀ x : A, x ^ 4 = 1)
    (hBA : B < A) (hCB : C < B) (hCpos : (⊥ : Subgroup P) < C)
    (hBX : IsXInvariantSubgroup X B) (hCX : IsXInvariantSubgroup X C) :
    False := by
  classical
  rcases lemma1_abelian_invariant_homocyclic hP hXtrans hAcomm hAX with
    ⟨e, r, ⟨phi⟩, hpower⟩
  let : Nontrivial A :=
    (Subgroup.nontrivial_iff_ne_bot A).mpr
      (ne_of_gt (hCpos.trans (hCB.trans hBA)))
  have hr : 0 < r := by
    apply Nat.pos_of_ne_zero
    intro hr0
    subst r
    have htarget :
        Nontrivial (Multiplicative (Fin 0 → ZMod (2 ^ e))) :=
      (Equiv.nontrivial_congr phi.toEquiv).mp inferInstance
    exact (not_nontrivial_iff_subsingleton.mpr inferInstance) htarget
  have he : e ≤ 2 := by
    let i0 : Fin r := ⟨0, hr⟩
    let basis : Fin r → ZMod (2 ^ e) := Pi.single i0 1
    let x : A := phi.symm (Multiplicative.ofAdd basis)
    have hx4 : x ^ 4 = 1 := hAexp x
    have htarget : (Multiplicative.ofAdd basis) ^ 4 = 1 := by
      simpa [x] using congrArg phi hx4
    have hi := congrArg
      (fun z : Multiplicative (Fin r → ZMod (2 ^ e)) => z.toAdd i0)
      htarget
    have hcast : ((4 : ℕ) : ZMod (2 ^ e)) = 0 := by
      simpa [basis, Pi.single_eq_same, nsmul_eq_mul] using hi
    have hdvd : 2 ^ e ∣ 4 :=
      (ZMod.natCast_eq_zero_iff 4 (2 ^ e)).mp hcast
    have hdvd' : 2 ^ e ∣ 2 ^ 2 := by simpa using hdvd
    exact (Nat.pow_dvd_pow_iff_le_right' (b := 0)).mp hdvd'
  let Pow (s : ℕ) : Subgroup P := Subgroup.closure
    {x : P | ∃ a : A, (a : P) ^ (2 ^ s) = x}
  have hbotX : IsXInvariantSubgroup X (⊥ : Subgroup P) := by
    intro k x
    constructor
    · intro hx
      subst x
      simp
    · intro hx
      have hback := congrArg (fun y : P => k⁻¹ • y) hx
      simpa [smul_smul] using hback
  obtain ⟨sA, hsA_le, hsA⟩ := hpower A le_rfl hAX
  obtain ⟨sB, hsB_le, hsB⟩ := hpower B hBA.le hBX
  obtain ⟨sC, hsC_le, hsC⟩ :=
    hpower C (hCB.le.trans hBA.le) hCX
  obtain ⟨s0, hs0_le, hs0⟩ := hpower (⊥ : Subgroup P) bot_le hbotX
  have hsA' : A = Pow sA := by simpa [Pow] using hsA
  have hsB' : B = Pow sB := by simpa [Pow] using hsB
  have hsC' : C = Pow sC := by simpa [Pow] using hsC
  have hs0' : (⊥ : Subgroup P) = Pow s0 := by simpa [Pow] using hs0
  have hsAB : sA ≠ sB := by
    intro hs
    apply (ne_of_gt hBA)
    rw [hsA', hsB', hs]
  have hsAC : sA ≠ sC := by
    intro hs
    apply (ne_of_gt (hCB.trans hBA))
    rw [hsA', hsC', hs]
  have hsA0 : sA ≠ s0 := by
    intro hs
    apply (ne_of_gt (hCpos.trans (hCB.trans hBA)))
    rw [hsA', hs0', hs]
  have hsBC : sB ≠ sC := by
    intro hs
    apply (ne_of_gt hCB)
    rw [hsB', hsC', hs]
  have hsB0 : sB ≠ s0 := by
    intro hs
    apply (ne_of_gt (hCpos.trans hCB))
    rw [hsB', hs0', hs]
  have hsC0 : sC ≠ s0 := by
    intro hs
    apply (ne_of_gt hCpos)
    rw [hsC', hs0', hs]
  omega
private theorem lemma13_omegaLength_three_of_chain
    {X P : Type u} [Group X] [Group P] [MulDistribMulAction X P]
    {H : Subgroup P} [IsInvariant X P H]
    (Phi C : Subgroup H)
    (hPhi_lt : Phi < ⊤) (hC_lt : C < Phi) (hC_pos : ⊥ < C)
    (hPhiNormal : Phi.Normal) (hCNormal : C.Normal)
    (hPhiX : IsXInvariantSubgroup X Phi)
    (hCX : IsXInvariantSubgroup X C)
    (hTopCover : ∀ L : Subgroup H, L.Normal → IsXInvariantSubgroup X L →
      Phi ≤ L → L ≤ ⊤ → L = Phi ∨ L = ⊤)
    (hMidCover : ∀ L : Subgroup H, L.Normal → IsXInvariantSubgroup X L →
      C ≤ L → L ≤ Phi → L = C ∨ L = Phi)
    (hBotCover : ∀ L : Subgroup H, L.Normal → IsXInvariantSubgroup X L →
      ⊥ ≤ L → L ≤ C → L = ⊥ ∨ L = C) :
    OmegaLength X H 3 := by
  let chain : Fin 4 → Subgroup H := ![⊤, Phi, C, ⊥]
  have htopX : IsXInvariantSubgroup X (⊤ : Subgroup H) := by
    intro k x
    simp
  have hbotX : IsXInvariantSubgroup X (⊥ : Subgroup H) := by
    intro k x
    constructor
    · intro hx
      subst x
      simp
    · intro hx
      have hback := congrArg (fun y : H => k⁻¹ • y) hx
      simpa [smul_smul] using hback
  refine ⟨chain, rfl, rfl, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [chain, hPhi_lt.le, hC_lt.le]
  · intro i
    fin_cases i
    · simpa only [chain, Matrix.cons_val_zero, Matrix.cons_val_one] using
        ⟨hPhi_lt, (inferInstance : (⊤ : Subgroup H).Normal), hPhiNormal,
          htopX, hPhiX, hTopCover⟩
    · simpa only [chain, Matrix.cons_val_zero, Matrix.cons_val_one] using
        ⟨hC_lt, hPhiNormal, hCNormal, hPhiX, hCX, hMidCover⟩
    · simpa only [chain, Matrix.cons_val_zero, Matrix.cons_val_one] using
        ⟨hC_pos, hCNormal, (inferInstance : (⊥ : Subgroup H).Normal),
          hCX, hbotX, hBotCover⟩

private def Lemma13ThreeChainData
    {X H : Type u} [Group X] [Group H] [MulDistribMulAction X H]
    (Phi C : Subgroup H) : Prop :=
  (Phi < ⊤ ∧ (⊤ : Subgroup H).Normal ∧ Phi.Normal ∧
    IsXInvariantSubgroup X (⊤ : Subgroup H) ∧
    IsXInvariantSubgroup X Phi ∧
    ∀ L : Subgroup H, L.Normal → IsXInvariantSubgroup X L →
      Phi ≤ L → L ≤ ⊤ → L = Phi ∨ L = ⊤) ∧
  (C < Phi ∧ Phi.Normal ∧ C.Normal ∧
    IsXInvariantSubgroup X Phi ∧ IsXInvariantSubgroup X C ∧
    ∀ L : Subgroup H, L.Normal → IsXInvariantSubgroup X L →
      C ≤ L → L ≤ Phi → L = C ∨ L = Phi) ∧
  ((⊥ : Subgroup H) < C ∧ C.Normal ∧ (⊥ : Subgroup H).Normal ∧
    IsXInvariantSubgroup X C ∧
    IsXInvariantSubgroup X (⊥ : Subgroup H) ∧
    ∀ L : Subgroup H, L.Normal → IsXInvariantSubgroup X L →
      ⊥ ≤ L → L ≤ C → L = ⊥ ∨ L = C)

private theorem lemma13_three_chain_data_of_ambient_chain
    {X P : Type u} [Group X] [Group P] [MulDistribMulAction X P]
    {H Phi C : Subgroup P}
    [IsInvariant X P H] [IsInvariant X P Phi] [IsInvariant X P C]
    (hPhi_lt_H : Phi < H) (hC_lt_Phi : C < Phi)
    (hC_pos : (⊥ : Subgroup P) < C)
    (hPhiNormal : Phi.Normal) (hCNormal : C.Normal)
    (hNormal_of_Phi_le : ∀ L : Subgroup P, Phi ≤ L → L.Normal)
    (hTopCover : ∀ L : Subgroup P, L.Normal →
      IsXInvariantSubgroup X L → Phi ≤ L → L ≤ H →
        L = Phi ∨ L = H)
    (hMidCover : ∀ L : Subgroup P, IsXInvariantSubgroup X L →
      C ≤ L → L ≤ Phi → L = C ∨ L = Phi)
    (hBotCover : ∀ L : Subgroup P, IsXInvariantSubgroup X L →
      L ≤ C → L = ⊥ ∨ L = C) :
    Lemma13ThreeChainData (X := X) (Phi.subgroupOf H) (C.subgroupOf H) := by
  let PhiH : Subgroup H := Phi.subgroupOf H
  let CH : Subgroup H := C.subgroupOf H
  have hmapPhi : PhiH.map H.subtype = Phi := by
    dsimp [PhiH]
    exact Subgroup.map_subgroupOf_eq_of_le hPhi_lt_H.le
  have hmapC : CH.map H.subtype = C := by
    dsimp [CH]
    exact Subgroup.map_subgroupOf_eq_of_le
      (hC_lt_Phi.le.trans hPhi_lt_H.le)
  have hmapTop : (⊤ : Subgroup H).map H.subtype = H := by
    apply le_antisymm
    · rintro _ ⟨h, _hh, rfl⟩
      exact h.property
    · intro h hh
      exact ⟨⟨h, hh⟩, trivial, rfl⟩
  have hmapBot : (⊥ : Subgroup H).map H.subtype = (⊥ : Subgroup P) :=
    Subgroup.map_bot H.subtype
  have hPhiH_lt_top : PhiH < (⊤ : Subgroup H) := by
    apply lt_of_le_of_ne le_top
    intro hEq
    have hmapEq := congrArg (fun L : Subgroup H => L.map H.subtype) hEq
    change PhiH.map H.subtype = (⊤ : Subgroup H).map H.subtype at hmapEq
    exact hPhi_lt_H.ne (hmapPhi.symm.trans (hmapEq.trans hmapTop))
  have hCH_lt_PhiH : CH < PhiH := by
    apply lt_of_le_of_ne
    · intro c hc
      exact hC_lt_Phi.le hc
    · intro hEq
      have hmapEq := congrArg (fun L : Subgroup H => L.map H.subtype) hEq
      change CH.map H.subtype = PhiH.map H.subtype at hmapEq
      exact hC_lt_Phi.ne (hmapC.symm.trans (hmapEq.trans hmapPhi))
  have hCH_pos : (⊥ : Subgroup H) < CH := by
    apply lt_of_le_of_ne bot_le
    intro hEq
    have hmapEq := congrArg (fun L : Subgroup H => L.map H.subtype) hEq
    change (⊥ : Subgroup H).map H.subtype = CH.map H.subtype at hmapEq
    exact hC_pos.ne (hmapBot.symm.trans (hmapEq.trans hmapC))
  have hPhiHNormal : PhiH.Normal := by
    let : Phi.Normal := hPhiNormal
    dsimp [PhiH]
    infer_instance
  have hCHNormal : CH.Normal := by
    let : C.Normal := hCNormal
    dsimp [CH]
    infer_instance
  have hPhiHX : IsXInvariantSubgroup X PhiH :=
    (isInvariant_subgroupOf Phi H).invariant
  have hCHX : IsXInvariantSubgroup X CH :=
    (isInvariant_subgroupOf C H).invariant
  have hTopCoverH :
      ∀ L : Subgroup H, L.Normal → IsXInvariantSubgroup X L →
        PhiH ≤ L → L ≤ ⊤ → L = PhiH ∨ L = ⊤ := by
    intro L _hLnormal hLX hPhiL _hLtop
    let LM : Subgroup P := L.map H.subtype
    let : IsInvariant X H L := ⟨hLX⟩
    have hLMX : IsXInvariantSubgroup X LM := by
      dsimp [LM]
      exact (isInvariant_map_subtype H L).invariant
    have hPhiLM : Phi ≤ LM := by
      rw [← hmapPhi]
      exact Subgroup.map_mono hPhiL
    have hLMH : LM ≤ H := by
      rintro _ ⟨l, _hl, rfl⟩
      exact l.property
    have hLMnormal : LM.Normal := hNormal_of_Phi_le LM hPhiLM
    rcases hTopCover LM hLMnormal hLMX hPhiLM hLMH with
      hLM_Phi | hLM_H
    · left
      apply Subgroup.map_injective H.subtype_injective
      rw [hmapPhi]
      exact hLM_Phi
    · right
      apply Subgroup.map_injective H.subtype_injective
      rw [hmapTop]
      exact hLM_H
  have hMidCoverH :
      ∀ L : Subgroup H, L.Normal → IsXInvariantSubgroup X L →
        CH ≤ L → L ≤ PhiH → L = CH ∨ L = PhiH := by
    intro L _hLnormal hLX hCL hLPhi
    let LM : Subgroup P := L.map H.subtype
    let : IsInvariant X H L := ⟨hLX⟩
    have hLMX : IsXInvariantSubgroup X LM := by
      dsimp [LM]
      exact (isInvariant_map_subtype H L).invariant
    have hCLM : C ≤ LM := by
      rw [← hmapC]
      exact Subgroup.map_mono hCL
    have hLMPhi : LM ≤ Phi := by
      rw [← hmapPhi]
      exact Subgroup.map_mono hLPhi
    rcases hMidCover LM hLMX hCLM hLMPhi with hLM_C | hLM_Phi
    · left
      apply Subgroup.map_injective H.subtype_injective
      rw [hmapC]
      exact hLM_C
    · right
      apply Subgroup.map_injective H.subtype_injective
      rw [hmapPhi]
      exact hLM_Phi
  have hBotCoverH :
      ∀ L : Subgroup H, L.Normal → IsXInvariantSubgroup X L →
        ⊥ ≤ L → L ≤ CH → L = ⊥ ∨ L = CH := by
    intro L _hLnormal hLX _hbotL hLC
    let LM : Subgroup P := L.map H.subtype
    let : IsInvariant X H L := ⟨hLX⟩
    have hLMX : IsXInvariantSubgroup X LM := by
      dsimp [LM]
      exact (isInvariant_map_subtype H L).invariant
    have hLMC : LM ≤ C := by
      rw [← hmapC]
      exact Subgroup.map_mono hLC
    rcases hBotCover LM hLMX hLMC with hLM_bot | hLM_C
    · left
      apply Subgroup.map_injective H.subtype_injective
      rw [hmapBot]
      exact hLM_bot
    · right
      apply Subgroup.map_injective H.subtype_injective
      rw [hmapC]
      exact hLM_C
  exact ⟨
    ⟨hPhiH_lt_top, inferInstance, hPhiHNormal,
      by intro k x; simp, hPhiHX, hTopCoverH⟩,
    ⟨hCH_lt_PhiH, hPhiHNormal, hCHNormal,
      hPhiHX, hCHX, hMidCoverH⟩,
    ⟨hCH_pos, hCHNormal, inferInstance, hCHX,
      by
        intro k x
        constructor
        · intro hx
          subst x
          simp
        · intro hx
          have hback := congrArg (fun y : H => k⁻¹ • y) hx
          simpa [smul_smul] using hback,
      hBotCoverH⟩⟩

private theorem lemma13_omegaLength_three_of_ambient_chain
    {X P : Type u} [Group X] [Group P] [MulDistribMulAction X P]
    {H Phi C : Subgroup P}
    [IsInvariant X P H] [IsInvariant X P Phi] [IsInvariant X P C]
    (hPhi_lt_H : Phi < H) (hC_lt_Phi : C < Phi)
    (hC_pos : (⊥ : Subgroup P) < C)
    (hPhiNormal : Phi.Normal) (hCNormal : C.Normal)
    (hNormal_of_Phi_le : ∀ L : Subgroup P, Phi ≤ L → L.Normal)
    (hTopCover : ∀ L : Subgroup P, L.Normal →
      IsXInvariantSubgroup X L → Phi ≤ L → L ≤ H →
        L = Phi ∨ L = H)
    (hMidCover : ∀ L : Subgroup P, IsXInvariantSubgroup X L →
      C ≤ L → L ≤ Phi → L = C ∨ L = Phi)
    (hBotCover : ∀ L : Subgroup P, IsXInvariantSubgroup X L →
      L ≤ C → L = ⊥ ∨ L = C) :
    OmegaLength X H 3 := by
  rcases lemma13_three_chain_data_of_ambient_chain
      hPhi_lt_H hC_lt_Phi hC_pos hPhiNormal hCNormal
      hNormal_of_Phi_le hTopCover hMidCover hBotCover with
    ⟨hupper, hmiddle, hlower⟩
  exact lemma13_omegaLength_three_of_chain
    (Phi.subgroupOf H) (C.subgroupOf H)
    hupper.1 hmiddle.1 hlower.1 hupper.2.2.1 hmiddle.2.2.1
    hupper.2.2.2.2.1 hmiddle.2.2.2.2.1
    hupper.2.2.2.2.2 hmiddle.2.2.2.2.2 hlower.2.2.2.2.2

private theorem lemma13_subgroup_action_data
    {X P : Type u} [Group X] [Group P] [MulDistribMulAction X P]
    {H : Subgroup P} [IsInvariant X P H]
    (hP : IsSuzukiTwoGroup P) (hXcyclic : IsCyclic X)
    (hXregular : ActionRegularOn X P (involutions P))
    (hXprimeSupport : ∀ p : ℕ, p.Prime → p ∣ Nat.card X →
      p ∣ Nat.card {x : P // x ∈ involutions P})
    (hH_noncomm : ¬ IsMulCommutative H)
    (hAllInv : ∀ a : P, IsInvolution a → a ∈ H) :
    IsSuzukiTwoGroup H ∧ FaithfulSMul X H ∧
      ActionRegularOn X H (involutions H) ∧
      (∀ x : H, x ∈ involutions H →
        ∀ y : H, y ∈ involutions H → ∃ k : X, y = k • x) ∧
      (∀ p : ℕ, p.Prime → p ∣ Nat.card X →
        p ∣ Nat.card {x : H // x ∈ involutions H}) := by
  let : Finite P := finite_of_isSuzukiTwoGroup hP
  have hH_regular : ActionRegularOn X H (involutions H) := by
    constructor
    · intro x hx k
      have hxP : IsInvolution (x : P) :=
        ⟨fun hx1 => hx.ne_one (Subtype.ext hx1),
          congrArg Subtype.val hx.sq_eq_one⟩
      have hkP := hXregular.1 (x : P) hxP k
      exact ⟨fun hk1 => hkP.ne_one (congrArg Subtype.val hk1),
        Subtype.ext hkP.sq_eq_one⟩
    · intro x hx y hy
      have hxP : IsInvolution (x : P) :=
        ⟨fun hx1 => hx.ne_one (Subtype.ext hx1),
          congrArg Subtype.val hx.sq_eq_one⟩
      have hyP : IsInvolution (y : P) :=
        ⟨fun hy1 => hy.ne_one (Subtype.ext hy1),
          congrArg Subtype.val hy.sq_eq_one⟩
      rcases hXregular.2 (x : P) hxP (y : P) hyP with
        ⟨k, hk, hunique⟩
      refine ⟨k, Subtype.ext hk, ?_⟩
      intro l hl
      exact hunique l (congrArg Subtype.val hl)
  have hH_faithful : FaithfulSMul X H := by
    rw [faithfulSMul_iff]
    intro k hkfix
    rcases hP.2.2.1 with ⟨x, _y, hx, _hy, _hxy⟩
    let xH : H := ⟨x, hAllInv x hx⟩
    have hxH : IsInvolution xH :=
      ⟨fun hx1 => hx.ne_one (congrArg Subtype.val hx1),
        Subtype.ext hx.sq_eq_one⟩
    have hfix : k • xH = xH := hkfix xH
    rcases hH_regular.2 xH hxH xH hxH with ⟨z, _hz, hunique⟩
    exact (hunique k hfix.symm).trans (hunique 1 (by simp)).symm
  have hH_trans : ∀ x : H, x ∈ involutions H →
      ∀ y : H, y ∈ involutions H → ∃ k : X, y = k • x := by
    intro x hx y hy
    rcases hH_regular.2 x hx y hy with ⟨k, hk, _hunique⟩
    exact ⟨k, hk⟩
  have hH_primeSupport : ∀ p : ℕ, p.Prime → p ∣ Nat.card X →
      p ∣ Nat.card {x : H // x ∈ involutions H} := by
    let e : {x : P // x ∈ involutions P} ≃
        {x : H // x ∈ involutions H} :=
      { toFun := fun x =>
          ⟨⟨x.1, hAllInv x.1 x.2⟩,
            ⟨fun hx1 => x.2.ne_one (congrArg Subtype.val hx1),
              Subtype.ext x.2.sq_eq_one⟩⟩
        invFun := fun x =>
          ⟨x.1.1,
            ⟨fun hx1 => x.2.ne_one (Subtype.ext hx1),
              congrArg Subtype.val x.2.sq_eq_one⟩⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun x => Subtype.ext (Subtype.ext rfl) }
    have hcard : Nat.card {x : P // x ∈ involutions P} =
        Nat.card {x : H // x ∈ involutions H} := Nat.card_congr e
    intro p hp hpdiv
    rw [← hcard]
    exact hXprimeSupport p hp hpdiv
  have hH_suzuki : IsSuzukiTwoGroup H := by
    have hpow : ∃ r : ℕ, Nat.card (⊤ : Subgroup H) = 2 ^ r := by
      obtain ⟨r, hr⟩ :=
        (isPGroup_of_isSuzukiTwoGroup hP).to_subgroup H |>.exists_card_eq
      exact ⟨r, by simpa using hr⟩
    have htwo : ∃ x y : H,
        IsInvolution x ∧ IsInvolution y ∧ x ≠ y := by
      rcases hP.2.2.1 with ⟨x, y, hx, hy, hxy⟩
      let xH : H := ⟨x, hAllInv x hx⟩
      let yH : H := ⟨y, hAllInv y hy⟩
      have hxH : IsInvolution xH :=
        ⟨fun hx1 => hx.ne_one (congrArg Subtype.val hx1),
          Subtype.ext hx.sq_eq_one⟩
      have hyH : IsInvolution yH :=
        ⟨fun hy1 => hy.ne_one (congrArg Subtype.val hy1),
          Subtype.ext hy.sq_eq_one⟩
      exact ⟨xH, yH, hxH, hyH,
        fun hxyH => hxy (congrArg Subtype.val hxyH)⟩
    exact ⟨hpow, hH_noncomm, htwo,
      ⟨X, inferInstance, inferInstance, hXcyclic, hH_faithful, hH_regular⟩⟩
  exact ⟨hH_suzuki, hH_faithful, hH_regular, hH_trans, hH_primeSupport⟩

/-- Higman Lemma 13: no Suzuki `2`-group has Omega-length greater than three. -/
private theorem lemma13_irreducible_actor_layer_finrank_eq
    {V W : Type u}
    [AddCommGroup V] [Module (ZMod 2) V] [Nontrivial V]
    [Finite V] [Module.Finite (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] [Nontrivial W]
    [Finite W] [Module.Finite (ZMod 2) W]
    (T : V ≃ₗ[ZMod 2] V) (S : W ≃ₗ[ZMod 2] W)
    (hT_irreducible : ∀ U : Submodule (ZMod 2) V,
      (∀ v : V, v ∈ U → T v ∈ U) → U = ⊥ ∨ U = ⊤)
    (hS_transitive : ∀ x : W, x ≠ 0 → ∀ y : W, y ≠ 0 →
      ∃ k : ℕ, (S ^ k) x = y)
    (n : ℕ) (hn : 2 ≤ n) (hW_card : Nat.card W = 2 ^ n)
    (q : V → W) (hq_equivariant : ∀ v : V, q (T v) = S (q v))
    (hq_nonzero : ∃ v : V, q v ≠ 0)
    (hT_order_dvd : orderOf T ∣ 2 ^ n - 1) :
    Module.finrank (ZMod 2) V = n := by
  have hq_pow : ∀ j : ℕ, ∀ v : V, q ((T ^ j) v) = (S ^ j) (q v) := by
    intro j
    induction j with
    | zero => intro v; rfl
    | succ j ih =>
        intro v
        rw [show T ^ (j + 1) = T * T ^ j by rw [pow_succ'],
          LinearEquiv.mul_apply, hq_equivariant, ih]
        rw [show S ^ (j + 1) = S * S ^ j by rw [pow_succ'],
          LinearEquiv.mul_apply]
  obtain ⟨v0, hv0⟩ := hq_nonzero
  have hfix : (S ^ orderOf T) (q v0) = q v0 := by
    rw [← hq_pow, pow_orderOf_eq_one]
    rfl
  have hS_pow : S ^ orderOf T = 1 := by
    apply LinearEquiv.ext
    intro w
    by_cases hw : w = 0
    · subst w
      simp
    · obtain ⟨k, hk⟩ := hS_transitive (q v0) hv0 w hw
      calc
        (S ^ orderOf T) w = (S ^ orderOf T) ((S ^ k) (q v0)) := by rw [hk]
        _ = (S ^ k) ((S ^ orderOf T) (q v0)) := by
          rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply]
          congr 1
          rw [← pow_add, ← pow_add, Nat.add_comm]
        _ = w := by rw [hfix, hk]
  have hS_order : orderOf S = 2 ^ n - 1 :=
    lemma4_transitive_linearAut_order S hS_transitive n hn hW_card
  have hS_order_dvd_T : orderOf S ∣ orderOf T :=
    orderOf_dvd_of_pow_eq_one hS_pow
  have hT_order : orderOf T = 2 ^ n - 1 :=
    Nat.dvd_antisymm hT_order_dvd (by simpa [hS_order] using hS_order_dvd_T)
  obtain ⟨m, hm, lambda, coordinates, _u, _hV_card, hlambda,
      hcoordinates, _hu, _hexpansion⟩ :=
    lemma5_irreducible_conjugate_eigenbasis T hT_irreducible
  have hfinrank : Module.finrank (ZMod 2) V = m :=
    coordinates.finrank_eq.symm.trans (GaloisField.finrank 2 hm.ne')
  have hT_order_eq_lambda :
      orderOf T = orderOf (Units.mk0 lambda hlambda) :=
    lemma6_coordinate_unit_order T coordinates lambda hlambda hcoordinates
  have hfield_dvd : orderOf T ∣ 2 ^ m - 1 := by
    rw [hT_order_eq_lambda]
    have h := orderOf_dvd_natCard (Units.mk0 lambda hlambda)
    rw [Nat.card_units, GaloisField.card 2 m hm.ne'] at h
    exact h
  have hn_dvd_m : n ∣ m := by
    have hdvd : 2 ^ n - 1 ∣ 2 ^ m - 1 := by
      rw [← hT_order]
      exact hfield_dvd
    have hmod : 2 ^ (m % n) - 1 = 0 := by
      rw [← Nat.pow_sub_one_mod_pow_sub_one 2 n m]
      exact Nat.mod_eq_zero_of_dvd hdvd
    have hsmall_pow_pos : 0 < 2 ^ (m % n) := pow_pos (by omega) _
    have hpow_one : 2 ^ (m % n) = 1 := by omega
    have hm_mod : m % n = 0 :=
      (Nat.pow_eq_one.mp hpow_one).resolve_left (by omega)
    exact Nat.dvd_of_mod_eq_zero hm_mod
  have hm_dvd_n : m ∣ n := by
    rw [← hfinrank]
    exact lemma5_irreducible_finrank_dvd_of_order_dvd T hT_irreducible n
      (by rw [hT_order])
  rw [hfinrank]
  exact Nat.dvd_antisymm hm_dvd_n hn_dvd_m

private theorem lemma13_commutator_sup_right_le
    {G : Type u} [Group G] {R A B C : Subgroup G} [C.Normal]
    (hRA : ⁅R, A⁆ ≤ C) (hRB : ⁅R, B⁆ ≤ C) :
    ⁅R, A ⊔ B⁆ ≤ C := by
  let q := QuotientGroup.mk' C
  have hRA_map : ⁅R.map q, A.map q⁆ = ⊥ := by
    rw [← Subgroup.map_commutator]
    apply (Subgroup.map_eq_bot_iff (f := q) (H := ⁅R, A⁆)).2
    simpa [q] using hRA
  have hRB_map : ⁅R.map q, B.map q⁆ = ⊥ := by
    rw [← Subgroup.map_commutator]
    apply (Subgroup.map_eq_bot_iff (f := q) (H := ⁅R, B⁆)).2
    simpa [q] using hRB
  have hRA_cent : R.map q ≤ Subgroup.centralizer (A.map q : Set (G ⧸ C)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hRA_map
  have hRB_cent : R.map q ≤ Subgroup.centralizer (B.map q : Set (G ⧸ C)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hRB_map
  have hR_sup_cent :
      R.map q ≤ Subgroup.centralizer ((A.map q ⊔ B.map q : Subgroup (G ⧸ C)) : Set (G ⧸ C)) := by
    intro r hr
    rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure,
      Subgroup.mem_centralizer_iff]
    intro x hx
    rcases hx with hxA | hxB
    · exact Subgroup.mem_centralizer_iff.mp (hRA_cent hr) x hxA
    · exact Subgroup.mem_centralizer_iff.mp (hRB_cent hr) x hxB
  have hmap_bot : (⁅R, A ⊔ B⁆).map q = ⊥ := by
    rw [Subgroup.map_commutator, Subgroup.map_sup]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hR_sup_cent
  have hle_ker : ⁅R, A ⊔ B⁆ ≤ q.ker :=
    (Subgroup.map_eq_bot_iff (f := q) (H := ⁅R, A ⊔ B⁆)).mp hmap_bot
  simpa [q] using hle_ker

private theorem lemma13_frattini_le_of_sup_and_squares
    {Q : Type u} [Group Q] [Finite Q]
    [Fact (Nat.Prime 2)] [Fact (IsPGroup 2 Q)]
    (A Y C : Subgroup Q) [A.Normal] [C.Normal]
    (hsup : A ⊔ Y = ⊤)
    (hcomm_le_C : commutator Q ≤ C)
    (hA_sq : ∀ a : A, (a : Q) ^ 2 ∈ C)
    (hY_sq : ∀ y : Y, (y : Q) ^ 2 ∈ C) :
    frattini Q ≤ C := by
  have hquotient_comm : IsMulCommutative (Q ⧸ C) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le
      (N := C)).mpr hcomm_le_C
  let : IsMulCommutative (Q ⧸ C) := hquotient_comm
  have hsq : ∀ q : Q, q ^ 2 ∈ C := by
    intro q
    have hq_sup : q ∈ A ⊔ Y := by rw [hsup]; trivial
    rcases (Subgroup.mem_sup_of_normal_left (s := A) (t := Y)).mp hq_sup with
      ⟨a, haA, y, hyY, rfl⟩
    let aA : A := ⟨a, haA⟩
    let yY : Y := ⟨y, hyY⟩
    apply (QuotientGroup.eq_one_iff (N := C) ((a * y) ^ 2)).mp
    calc
      QuotientGroup.mk' C ((a * y) ^ 2) =
          (QuotientGroup.mk' C (a * y)) ^ 2 := by rw [map_pow]
      _ = (QuotientGroup.mk' C a * QuotientGroup.mk' C y) ^ 2 := by rw [map_mul]
      _ = (QuotientGroup.mk' C a) ^ 2 * (QuotientGroup.mk' C y) ^ 2 :=
        mul_pow (QuotientGroup.mk' C a) (QuotientGroup.mk' C y) 2
      _ = 1 := by
        have ha_sq : a ^ 2 ∈ C := by simpa [aA] using hA_sq aA
        have hy_sq : y ^ 2 ∈ C := by simpa [yY] using hY_sq yY
        have ha_one : QuotientGroup.mk' C (a ^ 2) = 1 :=
          (QuotientGroup.eq_one_iff (N := C) (a ^ 2)).mpr ha_sq
        have hy_one : QuotientGroup.mk' C (y ^ 2) = 1 :=
          (QuotientGroup.eq_one_iff (N := C) (y ^ 2)).mpr hy_sq
        rw [← map_pow, ← map_pow, ha_one, hy_one, one_mul]
  rw [frattini_eq_closure_commutator_union_powers (R := Q) (p := 2)]
  refine (Subgroup.closure_le (K := C)).2 ?_
  rintro z (hz | ⟨q, rfl⟩)
  · exact hcomm_le_C hz
  · exact hsq q

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem lemma13_square_mem_bottom_of_chain_actor_data
    {X P : Type u} [Group X] [Group P] [MulDistribMulAction X P]
    (g : X) (A B : Subgroup P)
    (hdata : Lemma12ChainActorData g A B) :
    ∀ p : P, p ^ 2 ∈ B := by
  classical
  unfold Lemma12ChainActorData at hdata
  rcases hdata with
    ⟨k, n, xi, q0, U, V, bracket, squareMap,
      hxi, hn, hq0_ker, hq0_surj, hq0_mk, hU,
      hUV, hL1, hkernel1, hbracket, hsquare, hform⟩
  intro p
  have hpker : p ^ 2 ∈ q0.ker := by
    rw [MonoidHom.mem_ker]
    let p0 : (⊤ : Subgroup P).lowerCentralSeries 0 := Subgroup.topEquiv.symm p
    have hp0sq : p0 ^ 2 ∈ lowerCentralFactorKernel P 0 := by
      unfold lowerCentralFactorKernel
      exact (le_sup_left :
        squaresSubgroup ((⊤ : Subgroup P).lowerCentralSeries 0) ≤
          squaresSubgroup ((⊤ : Subgroup P).lowerCentralSeries 0) ⊔
            ((⊤ : Subgroup P).lowerCentralSeries 1).subgroupOf ((⊤ : Subgroup P).lowerCentralSeries 0))
        (Subgroup.subset_closure ⟨p0, rfl⟩)
    calc
      q0 (p ^ 2) = (q0 p) ^ 2 := by rw [map_pow]
      _ = (QuotientGroup.mk' (lowerCentralFactorKernel P 0) p0) ^ 2 := by
        rw [hq0_mk]
      _ = QuotientGroup.mk' (lowerCentralFactorKernel P 0) (p0 ^ 2) := by
        rw [map_pow]
      _ = 1 := (QuotientGroup.eq_one_iff (N := lowerCentralFactorKernel P 0)
        (p0 ^ 2)).mpr hp0sq
  rw [hq0_ker] at hpker
  exact hpker


/-! ### The ambient iterated lower-central bracket for Lemma 13 -/

private theorem lemma13_commutator_one_one_le_three
    {H : Type u} [Group H] :
    ⁅(⊤ : Subgroup H).lowerCentralSeries 1, (⊤ : Subgroup H).lowerCentralSeries 1⁆ ≤
      (⊤ : Subgroup H).lowerCentralSeries 3 := by
  let q : H →* H ⧸ (⊤ : Subgroup H).lowerCentralSeries 3 :=
    QuotientGroup.mk' ((⊤ : Subgroup H).lowerCentralSeries 3)
  have hmap3 : ((⊤ : Subgroup H).lowerCentralSeries 3).map q = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    change (⊤ : Subgroup H).lowerCentralSeries 3 ≤
      (QuotientGroup.mk' ((⊤ : Subgroup H).lowerCentralSeries 3)).ker
    rw [QuotientGroup.ker_mk']
  have hrotate1 :
      ⁅⁅((⊤ : Subgroup H).lowerCentralSeries 0).map q,
          ((⊤ : Subgroup H).lowerCentralSeries 1).map q⁆,
        ((⊤ : Subgroup H).lowerCentralSeries 0).map q⁆ = ⊥ := by
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator]
    rw [Subgroup.commutator_comm ((⊤ : Subgroup H).lowerCentralSeries 0)
      ((⊤ : Subgroup H).lowerCentralSeries 1)]
    change ((⊤ : Subgroup H).lowerCentralSeries 3).map q = ⊥
    exact hmap3
  have hrotate2 :
      ⁅⁅((⊤ : Subgroup H).lowerCentralSeries 1).map q,
          ((⊤ : Subgroup H).lowerCentralSeries 0).map q⁆,
        ((⊤ : Subgroup H).lowerCentralSeries 0).map q⁆ = ⊥ := by
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator]
    change ((⊤ : Subgroup H).lowerCentralSeries 3).map q = ⊥
    exact hmap3
  have hthree := Subgroup.commutator_commutator_eq_bot_of_rotate
    (H₁ := ((⊤ : Subgroup H).lowerCentralSeries 0).map q)
    (H₂ := ((⊤ : Subgroup H).lowerCentralSeries 0).map q)
    (H₃ := ((⊤ : Subgroup H).lowerCentralSeries 1).map q)
    hrotate1 hrotate2
  rw [← Subgroup.map_commutator, ← Subgroup.map_commutator] at hthree
  change (⁅(⊤ : Subgroup H).lowerCentralSeries 1, (⊤ : Subgroup H).lowerCentralSeries 1⁆).map q = ⊥ at hthree
  have hle := (Subgroup.map_eq_bot_iff
    ⁅(⊤ : Subgroup H).lowerCentralSeries 1, (⊤ : Subgroup H).lowerCentralSeries 1⁆).mp hthree
  change ⁅(⊤ : Subgroup H).lowerCentralSeries 1, (⊤ : Subgroup H).lowerCentralSeries 1⁆ ≤ q.ker at hle
  change ⁅(⊤ : Subgroup H).lowerCentralSeries 1, (⊤ : Subgroup H).lowerCentralSeries 1⁆ ≤
    (QuotientGroup.mk' ((⊤ : Subgroup H).lowerCentralSeries 3)).ker at hle
  rw [QuotientGroup.ker_mk'] at hle
  exact hle


private def lemma13_nextBracketLift
    {H : Type u} [Group H]
    (x : (⊤ : Subgroup H).lowerCentralSeries 0) (c : (⊤ : Subgroup H).lowerCentralSeries 1) :
    (⊤ : Subgroup H).lowerCentralSeries 2 :=
  ⟨⁅(x : H), (c : H)⁆, by
    have hcx : ⁅(c : H), (x : H)⁆ ∈ (⊤ : Subgroup H).lowerCentralSeries 2 := by
      rw [show 2 = 1 + 1 by omega, Subgroup.lowerCentralSeries_succ]
      exact Subgroup.subset_closure
        ⟨(c : H), c.property, (x : H), trivial, rfl⟩
    have hinv := ((⊤ : Subgroup H).lowerCentralSeries 2).inv_mem hcx
    simpa only [commutatorElement_inv] using hinv⟩

private def lemma13_deeperBracketLift
    {H : Type u} [Group H]
    (x : (⊤ : Subgroup H).lowerCentralSeries 0) (d : (⊤ : Subgroup H).lowerCentralSeries 2) :
    (⊤ : Subgroup H).lowerCentralSeries 2 :=
  ⟨⁅(x : H), (d : H)⁆, by
    apply (⊤ : Subgroup H).lowerCentralSeries_antitone (by omega : 2 ≤ 3)
    have hdx : ⁅(d : H), (x : H)⁆ ∈ (⊤ : Subgroup H).lowerCentralSeries 3 := by
      rw [show 3 = 2 + 1 by omega, Subgroup.lowerCentralSeries_succ]
      exact Subgroup.subset_closure
        ⟨(d : H), d.property, (x : H), trivial, rfl⟩
    have hinv := ((⊤ : Subgroup H).lowerCentralSeries 3).inv_mem hdx
    simpa only [commutatorElement_inv] using hinv⟩

private theorem lemma13_deeperBracketLift_mem_kernel
    {H : Type u} [Group H]
    (x : (⊤ : Subgroup H).lowerCentralSeries 0) (d : (⊤ : Subgroup H).lowerCentralSeries 2) :
    lemma13_deeperBracketLift x d ∈ lowerCentralFactorKernel H 2 := by
  apply (show
    ((⊤ : Subgroup H).lowerCentralSeries 3).subgroupOf ((⊤ : Subgroup H).lowerCentralSeries 2) ≤
      lowerCentralFactorKernel H 2 by
    rw [lowerCentralFactorKernel]
    exact le_sup_right)
  change ⁅(x : H), (d : H)⁆ ∈ (⊤ : Subgroup H).lowerCentralSeries 3
  have hdx : ⁅(d : H), (x : H)⁆ ∈ (⊤ : Subgroup H).lowerCentralSeries 3 := by
    rw [show 3 = 2 + 1 by omega, Subgroup.lowerCentralSeries_succ]
    exact Subgroup.subset_closure
      ⟨(d : H), d.property, (x : H), trivial, rfl⟩
  have hinv := ((⊤ : Subgroup H).lowerCentralSeries 3).inv_mem hdx
  simpa only [commutatorElement_inv] using hinv

private theorem lemma13_quotient_conj_eq
    {H : Type u} [Group H]
    (x : (⊤ : Subgroup H).lowerCentralSeries 0) (d : (⊤ : Subgroup H).lowerCentralSeries 2) :
    QuotientGroup.mk' (lowerCentralFactorKernel H 2)
        (⟨(x : H) * (d : H) * (x : H)⁻¹,
          (inferInstance : ((⊤ : Subgroup H).lowerCentralSeries 2).Normal).conj_mem
            (d : H) d.property (x : H)⟩ : (⊤ : Subgroup H).lowerCentralSeries 2) =
      QuotientGroup.mk' (lowerCentralFactorKernel H 2) d := by
  let q := QuotientGroup.mk' (lowerCentralFactorKernel H 2)
  have hfactor :
      (⟨(x : H) * (d : H) * (x : H)⁻¹,
        (inferInstance : ((⊤ : Subgroup H).lowerCentralSeries 2).Normal).conj_mem
          (d : H) d.property (x : H)⟩ : (⊤ : Subgroup H).lowerCentralSeries 2) =
        lemma13_deeperBracketLift x d * d := by
    apply Subtype.ext
    change (x : H) * (d : H) * (x : H)⁻¹ =
      ((x : H) * (d : H) * (x : H)⁻¹ * (d : H)⁻¹) * (d : H)
    group
  rw [hfactor, map_mul]
  have hkernel : q (lemma13_deeperBracketLift x d) = 1 := by
    apply (QuotientGroup.eq_one_iff _).2
    exact lemma13_deeperBracketLift_mem_kernel x d
  rw [hkernel, one_mul]

private def lemma13_bracketRightHom
    {H : Type u} [Group H] (x : (⊤ : Subgroup H).lowerCentralSeries 0) :
    (⊤ : Subgroup H).lowerCentralSeries 1 →* LowerCentralFactor H 2 where
  toFun c :=
    QuotientGroup.mk' (lowerCentralFactorKernel H 2)
      (lemma13_nextBracketLift x c)
  map_one' := by
    have hone : lemma13_nextBracketLift x 1 = 1 := by
      apply Subtype.ext
      simp [lemma13_nextBracketLift]
    rw [hone, map_one]
  map_mul' c d := by
    have hfactor :
        lemma13_nextBracketLift x (c * d) =
          lemma13_nextBracketLift x c *
            (⟨(c : H) * (lemma13_nextBracketLift x d : H) * (c : H)⁻¹,
              (inferInstance : ((⊤ : Subgroup H).lowerCentralSeries 2).Normal).conj_mem
                (lemma13_nextBracketLift x d : H)
                (lemma13_nextBracketLift x d).property (c : H)⟩ :
              (⊤ : Subgroup H).lowerCentralSeries 2) := by
      apply Subtype.ext
      change ⁅(x : H), (c : H) * (d : H)⁆ =
        ⁅(x : H), (c : H)⁆ *
          ((c : H) * ⁅(x : H), (d : H)⁆ * (c : H)⁻¹)
      simp only [commutatorElement_def]
      group
    change QuotientGroup.mk' (lowerCentralFactorKernel H 2)
        (lemma13_nextBracketLift x (c * d)) =
      QuotientGroup.mk' (lowerCentralFactorKernel H 2)
          (lemma13_nextBracketLift x c) *
        QuotientGroup.mk' (lowerCentralFactorKernel H 2)
          (lemma13_nextBracketLift x d)
    rw [hfactor, map_mul]
    let c0 : (⊤ : Subgroup H).lowerCentralSeries 0 :=
      ⟨(c : H),
        (⊤ : Subgroup H).lowerCentralSeries_antitone
          (by omega : 0 ≤ 1) c.property⟩
    rw [lemma13_quotient_conj_eq c0 (lemma13_nextBracketLift x d)]

private theorem lemma13_bracketRightHom_kernel
    {H : Type u} [Group H] (x : (⊤ : Subgroup H).lowerCentralSeries 0) :
    lowerCentralFactorKernel H 1 ≤ (lemma13_bracketRightHom x).ker := by
  rw [lowerCentralFactorKernel]
  apply sup_le
  · rw [squaresSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    change lemma13_bracketRightHom x (c ^ 2) = 1
    rw [map_pow]
    exact lowerCentralFactor_sq_eq_one 2 _
  · intro d hd
    change QuotientGroup.mk' (lowerCentralFactorKernel H 2)
      (lemma13_nextBracketLift x d) = 1
    apply (QuotientGroup.eq_one_iff _).2
    let d' : (⊤ : Subgroup H).lowerCentralSeries 2 := ⟨(d : H), hd⟩
    have heq : lemma13_nextBracketLift x d = lemma13_deeperBracketLift x d' := by
      apply Subtype.ext
      rfl
    rw [heq]
    exact lemma13_deeperBracketLift_mem_kernel x d'

private def lemma13_bracketRightFactorHom
    {H : Type u} [Group H] (x : (⊤ : Subgroup H).lowerCentralSeries 0) :
    LowerCentralFactor H 1 →* LowerCentralFactor H 2 :=
  QuotientGroup.lift (lowerCentralFactorKernel H 1)
    (lemma13_bracketRightHom x) (lemma13_bracketRightHom_kernel x)


private def lemma13_bracketLeftHom
    {H : Type u} [Group H] :
    (⊤ : Subgroup H).lowerCentralSeries 0 →*
      (LowerCentralFactor H 1 →* LowerCentralFactor H 2) where
  toFun x := lemma13_bracketRightFactorHom x
  map_one' := by
    apply MonoidHom.ext
    intro cq
    refine Quotient.inductionOn' cq ?_
    intro c
    change QuotientGroup.mk' (lowerCentralFactorKernel H 2)
      (lemma13_nextBracketLift 1 c) = 1
    have hone : lemma13_nextBracketLift 1 c = 1 := by
      apply Subtype.ext
      simp [lemma13_nextBracketLift]
    rw [hone, map_one]
  map_mul' x z := by
    apply MonoidHom.ext
    intro cq
    refine Quotient.inductionOn' cq ?_
    intro c
    have hfactor :
        lemma13_nextBracketLift (x * z) c =
          (⟨(x : H) * (lemma13_nextBracketLift z c : H) * (x : H)⁻¹,
            (inferInstance : ((⊤ : Subgroup H).lowerCentralSeries 2).Normal).conj_mem
              (lemma13_nextBracketLift z c : H)
              (lemma13_nextBracketLift z c).property (x : H)⟩ :
            (⊤ : Subgroup H).lowerCentralSeries 2) *
          lemma13_nextBracketLift x c := by
      apply Subtype.ext
      change ⁅(x : H) * (z : H), (c : H)⁆ =
        ((x : H) * ⁅(z : H), (c : H)⁆ * (x : H)⁻¹) *
          ⁅(x : H), (c : H)⁆
      simp only [commutatorElement_def]
      group
    change QuotientGroup.mk' (lowerCentralFactorKernel H 2)
        (lemma13_nextBracketLift (x * z) c) =
      QuotientGroup.mk' (lowerCentralFactorKernel H 2)
          (lemma13_nextBracketLift x c) *
        QuotientGroup.mk' (lowerCentralFactorKernel H 2)
          (lemma13_nextBracketLift z c)
    rw [hfactor, map_mul, lemma13_quotient_conj_eq]
    exact mul_comm _ _

private theorem lemma13_bracketLeftHom_kernel
    {H : Type u} [Group H] :
    lowerCentralFactorKernel H 0 ≤
      (lemma13_bracketLeftHom (H := H)).ker := by
  change
    (squaresSubgroup ((⊤ : Subgroup H).lowerCentralSeries 0) ⊔
      ((⊤ : Subgroup H).lowerCentralSeries 1).subgroupOf ((⊤ : Subgroup H).lowerCentralSeries 0)) ≤ _
  apply sup_le
  · rw [squaresSubgroup, Subgroup.closure_le]
    rintro _ ⟨x, rfl⟩
    change lemma13_bracketLeftHom (H := H) (x ^ 2) = 1
    rw [map_pow]
    apply MonoidHom.ext
    intro c
    change (lemma13_bracketLeftHom (H := H) x c) ^ 2 = 1
    exact lowerCentralFactor_sq_eq_one 2 _
  · intro x hx
    change lemma13_bracketLeftHom (H := H) x = 1
    apply MonoidHom.ext
    intro cq
    refine Quotient.inductionOn' cq ?_
    intro c
    change QuotientGroup.mk' (lowerCentralFactorKernel H 2)
      (lemma13_nextBracketLift x c) = 1
    apply (QuotientGroup.eq_one_iff _).2
    apply (show
      ((⊤ : Subgroup H).lowerCentralSeries 3).subgroupOf ((⊤ : Subgroup H).lowerCentralSeries 2) ≤
        lowerCentralFactorKernel H 2 by
      rw [lowerCentralFactorKernel]
      exact le_sup_right)
    exact lemma13_commutator_one_one_le_three
      (Subgroup.commutator_mem_commutator hx c.property)

private def lemma13_bracketFactorHom
    {H : Type u} [Group H] :
    LowerCentralFactor H 0 →*
      (LowerCentralFactor H 1 →* LowerCentralFactor H 2) :=
  QuotientGroup.lift (lowerCentralFactorKernel H 0)
    (lemma13_bracketLeftHom (H := H))
    (lemma13_bracketLeftHom_kernel (H := H))


private noncomputable def lemma13_bracketFactorAddHom
    {H : Type u} [Group H] :
    Additive (LowerCentralFactor H 0) →+
      (Additive (LowerCentralFactor H 1) →ₗ[ZMod 2]
        Additive (LowerCentralFactor H 2)) where
  toFun x :=
    ((lemma13_bracketFactorHom x.toMul).toAdditive).toZModLinearMap 2
  map_zero' := by
    apply LinearMap.ext
    intro c
    apply Additive.toMul.injective
    exact MonoidHom.map_one₂ (lemma13_bracketFactorHom (H := H)) c.toMul
  map_add' x z := by
    apply LinearMap.ext
    intro c
    apply Additive.toMul.injective
    exact MonoidHom.map_mul₂ (lemma13_bracketFactorHom (H := H))
      x.toMul z.toMul c.toMul

private noncomputable def lemma13_lowerCentralIteratedBracket
    {H : Type u} [Group H] :
    Additive (LowerCentralFactor H 0) →ₗ[ZMod 2]
      Additive (LowerCentralFactor H 1) →ₗ[ZMod 2]
        Additive (LowerCentralFactor H 2) :=
  (lemma13_bracketFactorAddHom (H := H)).toZModLinearMap 2

private theorem lemma13_lowerCentralIteratedBracket_mk_mk
    {H : Type u} [Group H]
    (x : (⊤ : Subgroup H).lowerCentralSeries 0) (c : (⊤ : Subgroup H).lowerCentralSeries 1) :
    lemma13_lowerCentralIteratedBracket
        (Additive.ofMul
          (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x))
        (Additive.ofMul
          (QuotientGroup.mk' (lowerCentralFactorKernel H 1) c)) =
      Additive.ofMul
        (QuotientGroup.mk' (lowerCentralFactorKernel H 2)
          (lemma13_nextBracketLift x c)) :=
  rfl


set_option maxHeartbeats 800000 in
private theorem lemma13_lowerCentralJacobi
    {H : Type u} [Group H]
    (bracket : Additive (LowerCentralFactor H 0) →ₗ[ZMod 2]
      Additive (LowerCentralFactor H 0) →ₗ[ZMod 2]
        Additive (LowerCentralFactor H 1))
    (hbracket_mk : ∀ x y : (⊤ : Subgroup H).lowerCentralSeries 0,
      ∀ hcomm : ⁅(x : H), (y : H)⁆ ∈ (⊤ : Subgroup H).lowerCentralSeries 1,
        bracket
            (Additive.ofMul
              (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x))
            (Additive.ofMul
              (QuotientGroup.mk' (lowerCentralFactorKernel H 0) y)) =
          Additive.ofMul
            (QuotientGroup.mk' (lowerCentralFactorKernel H 1)
              ⟨⁅(x : H), (y : H)⁆, hcomm⟩))
    (x y z : Additive (LowerCentralFactor H 0)) :
    lemma13_lowerCentralIteratedBracket x (bracket y z) +
      lemma13_lowerCentralIteratedBracket y (bracket z x) +
        lemma13_lowerCentralIteratedBracket z (bracket x y) = 0 := by
  obtain ⟨x0, hx0⟩ :=
    QuotientGroup.mk'_surjective (lowerCentralFactorKernel H 0) x.toMul
  obtain ⟨y0, hy0⟩ :=
    QuotientGroup.mk'_surjective (lowerCentralFactorKernel H 0) y.toMul
  obtain ⟨z0, hz0⟩ :=
    QuotientGroup.mk'_surjective (lowerCentralFactorKernel H 0) z.toMul
  have hx : x = Additive.ofMul
      (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x0) := by
    apply Additive.toMul.injective
    exact hx0.symm
  have hy : y = Additive.ofMul
      (QuotientGroup.mk' (lowerCentralFactorKernel H 0) y0) := by
    apply Additive.toMul.injective
    exact hy0.symm
  have hz : z = Additive.ofMul
      (QuotientGroup.mk' (lowerCentralFactorKernel H 0) z0) := by
    apply Additive.toMul.injective
    exact hz0.symm
  rw [hx, hy, hz]
  let cYZ : (⊤ : Subgroup H).lowerCentralSeries 1 := ⟨⁅(y0 : H), (z0 : H)⁆, by
    rw [Subgroup.top_lowerCentralSeries_one]
    exact Subgroup.commutator_mem_commutator (by simp) (by simp)⟩
  let cZX : (⊤ : Subgroup H).lowerCentralSeries 1 := ⟨⁅(z0 : H), (x0 : H)⁆, by
    rw [Subgroup.top_lowerCentralSeries_one]
    exact Subgroup.commutator_mem_commutator (by simp) (by simp)⟩
  let cXY : (⊤ : Subgroup H).lowerCentralSeries 1 := ⟨⁅(x0 : H), (y0 : H)⁆, by
    rw [Subgroup.top_lowerCentralSeries_one]
    exact Subgroup.commutator_mem_commutator (by simp) (by simp)⟩
  rw [hbracket_mk y0 z0 cYZ.property,
    hbracket_mk z0 x0 cZX.property,
    hbracket_mk x0 y0 cXY.property,
    lemma13_lowerCentralIteratedBracket_mk_mk,
    lemma13_lowerCentralIteratedBracket_mk_mk,
    lemma13_lowerCentralIteratedBracket_mk_mk]
  apply Additive.toMul.injective
  change
    QuotientGroup.mk' (lowerCentralFactorKernel H 2)
          (lemma13_nextBracketLift x0 cYZ) *
        QuotientGroup.mk' (lowerCentralFactorKernel H 2)
          (lemma13_nextBracketLift y0 cZX) *
      QuotientGroup.mk' (lowerCentralFactorKernel H 2)
        (lemma13_nextBracketLift z0 cXY) = 1
  let q0 := QuotientGroup.mk' (lowerCentralFactorKernel H 0)
  let q1 := QuotientGroup.mk' (lowerCentralFactorKernel H 1)
  let q2 := QuotientGroup.mk' (lowerCentralFactorKernel H 2)
  let xInv : (⊤ : Subgroup H).lowerCentralSeries 0 := x0⁻¹
  let yInv : (⊤ : Subgroup H).lowerCentralSeries 0 := y0⁻¹
  let zInv : (⊤ : Subgroup H).lowerCentralSeries 0 := z0⁻¹
  let cZinvXinv : (⊤ : Subgroup H).lowerCentralSeries 1 :=
    ⟨⁅(zInv : H), (xInv : H)⁆, by
      rw [Subgroup.top_lowerCentralSeries_one]
      exact Subgroup.commutator_mem_commutator (by simp) (by simp)⟩
  let cYinvZ : (⊤ : Subgroup H).lowerCentralSeries 1 :=
    ⟨⁅(yInv : H), (z0 : H)⁆, by
      rw [Subgroup.top_lowerCentralSeries_one]
      exact Subgroup.commutator_mem_commutator (by simp) (by simp)⟩
  let tA : (⊤ : Subgroup H).lowerCentralSeries 2 :=
    lemma13_nextBracketLift y0 cZinvXinv
  let tB : (⊤ : Subgroup H).lowerCentralSeries 2 :=
    lemma13_nextBracketLift xInv cYinvZ
  have hcA : q1 cZinvXinv = q1 cZX := by
    apply Additive.ofMul.injective
    calc
      Additive.ofMul (q1 cZinvXinv) =
          bracket (Additive.ofMul (q0 zInv))
            (Additive.ofMul (q0 xInv)) :=
        (hbracket_mk zInv xInv cZinvXinv.property).symm
      _ = bracket (Additive.ofMul (q0 z0))
            (Additive.ofMul (q0 x0)) := by
        simp only [q0, zInv, xInv, map_inv, ofMul_inv,
          ZModModule.neg_eq_self]
      _ = Additive.ofMul (q1 cZX) :=
        hbracket_mk z0 x0 cZX.property
  have hcB : q1 cYinvZ = q1 cYZ := by
    apply Additive.ofMul.injective
    calc
      Additive.ofMul (q1 cYinvZ) =
          bracket (Additive.ofMul (q0 yInv))
            (Additive.ofMul (q0 z0)) :=
        (hbracket_mk yInv z0 cYinvZ.property).symm
      _ = bracket (Additive.ofMul (q0 y0))
            (Additive.ofMul (q0 z0)) := by
        simp only [q0, yInv, map_inv, ofMul_inv,
          ZModModule.neg_eq_self]
      _ = Additive.ofMul (q1 cYZ) :=
        hbracket_mk y0 z0 cYZ.property
  have htA : q2 tA = q2 (lemma13_nextBracketLift y0 cZX) := by
    apply Additive.ofMul.injective
    calc
      Additive.ofMul (q2 tA) =
          lemma13_lowerCentralIteratedBracket
            (Additive.ofMul (q0 y0)) (Additive.ofMul (q1 cZinvXinv)) :=
        (lemma13_lowerCentralIteratedBracket_mk_mk y0 cZinvXinv).symm
      _ = lemma13_lowerCentralIteratedBracket
            (Additive.ofMul (q0 y0)) (Additive.ofMul (q1 cZX)) := by
        rw [hcA]
      _ = Additive.ofMul
            (q2 (lemma13_nextBracketLift y0 cZX)) :=
        lemma13_lowerCentralIteratedBracket_mk_mk y0 cZX
  have htB : q2 tB = q2 (lemma13_nextBracketLift x0 cYZ) := by
    apply Additive.ofMul.injective
    calc
      Additive.ofMul (q2 tB) =
          lemma13_lowerCentralIteratedBracket
            (Additive.ofMul (q0 xInv)) (Additive.ofMul (q1 cYinvZ)) :=
        (lemma13_lowerCentralIteratedBracket_mk_mk xInv cYinvZ).symm
      _ = lemma13_lowerCentralIteratedBracket
            (Additive.ofMul (q0 x0)) (Additive.ofMul (q1 cYZ)) := by
        rw [hcB]
        simp only [q0, xInv, map_inv, ofMul_inv,
          ZModModule.neg_eq_self]
      _ = Additive.ofMul
            (q2 (lemma13_nextBracketLift x0 cYZ)) :=
        lemma13_lowerCentralIteratedBracket_mk_mk x0 cYZ
  let zConjTA : (⊤ : Subgroup H).lowerCentralSeries 2 :=
    ⟨(z0 : H) * (tA : H)⁻¹ * (z0 : H)⁻¹,
      (inferInstance : ((⊤ : Subgroup H).lowerCentralSeries 2).Normal).conj_mem
        ((tA : H)⁻¹) (((⊤ : Subgroup H).lowerCentralSeries 2).inv_mem tA.property) (z0 : H)⟩
  let yConjTB : (⊤ : Subgroup H).lowerCentralSeries 2 :=
    ⟨(y0 : H) * (tB : H)⁻¹ * (y0 : H)⁻¹,
      (inferInstance : ((⊤ : Subgroup H).lowerCentralSeries 2).Normal).conj_mem
        ((tB : H)⁻¹) (((⊤ : Subgroup H).lowerCentralSeries 2).inv_mem tB.property) (y0 : H)⟩
  let inner : (⊤ : Subgroup H).lowerCentralSeries 2 := zConjTA * yConjTB
  let rhs : (⊤ : Subgroup H).lowerCentralSeries 2 :=
    ⟨(x0 : H) * (inner : H) * (x0 : H)⁻¹,
      (inferInstance : ((⊤ : Subgroup H).lowerCentralSeries 2).Normal).conj_mem
        (inner : H) inner.property (x0 : H)⟩
  have hHallRaw :
      ⁅(z0 : H), ⁅(x0 : H), (y0 : H)⁆⁆ =
        (x0 : H) * (z0 : H) *
            ⁅(y0 : H), ⁅(z0 : H)⁻¹, (x0 : H)⁻¹⁆⁆⁻¹ * (z0 : H)⁻¹ *
          (y0 : H) * ⁅(x0 : H)⁻¹, ⁅(y0 : H)⁻¹, (z0 : H)⁆⁆⁻¹ *
            (y0 : H)⁻¹ * (x0 : H)⁻¹ := by
    simp only [commutatorElement_def]
    group
  have hHallSub :
      lemma13_nextBracketLift z0 cXY = rhs := by
    apply Subtype.ext
    simpa only [rhs, inner, zConjTA, yConjTB, tA, tB,
      cXY, cZinvXinv, cYinvZ, xInv, yInv, zInv,
      lemma13_nextBracketLift, Subgroup.coe_mul, Subgroup.coe_inv,
      Subtype.coe_mk, mul_assoc] using hHallRaw
  have hqRhs : q2 rhs = q2 (tA⁻¹) * q2 (tB⁻¹) := by
    calc
      q2 rhs = q2 inner := by
        simpa only [rhs] using lemma13_quotient_conj_eq x0 inner
      _ = q2 zConjTA * q2 yConjTB := by rw [map_mul]
      _ = q2 (tA⁻¹) * q2 (tB⁻¹) := by
        rw [show q2 zConjTA = q2 (tA⁻¹) by
          simpa only [q2, zConjTA, Subgroup.coe_inv] using
            lemma13_quotient_conj_eq z0 (tA⁻¹)]
        rw [show q2 yConjTB = q2 (tB⁻¹) by
          simpa only [q2, yConjTB, Subgroup.coe_inv] using
            lemma13_quotient_conj_eq y0 (tB⁻¹)]
  have hqHall :
      q2 (lemma13_nextBracketLift z0 cXY) =
        (q2 tA)⁻¹ * (q2 tB)⁻¹ := by
    calc
      q2 (lemma13_nextBracketLift z0 cXY) = q2 rhs := congrArg q2 hHallSub
      _ = q2 (tA⁻¹) * q2 (tB⁻¹) := hqRhs
      _ = (q2 tA)⁻¹ * (q2 tB)⁻¹ := by rw [map_inv, map_inv]
  have hinvSelf (w : LowerCentralFactor H 2) : w⁻¹ = w := by
    apply inv_eq_of_mul_eq_one_right
    simpa [pow_two] using lowerCentralFactor_sq_eq_one 2 w
  rw [← htB, ← htA]
  rw [← hinvSelf (q2 tA), ← hinvSelf (q2 tB)]
  rw [mul_comm (q2 tB)⁻¹ (q2 tA)⁻¹, ← hqHall]
  change q2 (lemma13_nextBracketLift z0 cXY) *
    q2 (lemma13_nextBracketLift z0 cXY) = 1
  simpa [pow_two] using
    lowerCentralFactor_sq_eq_one 2
      (q2 (lemma13_nextBracketLift z0 cXY))


set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem lemma13_exists_nontrivial_middle_outer_commutator
    {X P : Type u} [Group X] [Group P] [MulDistribMulAction X P]
    (g : X) (A B : Subgroup P)
    (hdata : Lemma12ChainActorData g A B) :
    ∃ x : P, x ∈ A ∧ ∃ y : P, ⁅x, y⁆ ≠ 1 := by
  classical
  unfold Lemma12ChainActorData at hdata
  rcases hdata with
    ⟨k, n, xi, q0, U, V, bracket, squareMap,
      hxi, hn, hq0_ker, hq0_surj, hq0_mk, hU,
      hUV, hL1, hkernel1, hbracket, hsquare, hform⟩
  have hcross :
      ∃ u : U, ∃ v : V,
        bracket (u : Additive (LowerCentralFactor P 0))
          (v : Additive (LowerCentralFactor P 0)) ≠ 0 := by
    rcases hform with hformB | hformC
    · unfold Lemma12TypeBNormalizedData at hformB
      rcases hformB with
        ⟨eta, epsilon, uNorm, vNorm, centerCoordinates,
          heta, hepsilon, horder, huAction, hvAction, hcenterAction,
          hsquareU, hsquareV, hcrossFormula⟩
      refine ⟨uNorm 1, vNorm 1, ?_⟩
      intro hzero
      have hformula := hcrossFormula 1 1
      rw [hzero] at hformula
      simp only [map_zero, mul_one] at hformula
      exact hepsilon hformula.symm
    · unfold Lemma12TypeCNormalizedData at hformC
      rcases hformC with
        ⟨theta, lambda, eta, epsilon, outerNorm, middleNorm,
          centerCoordinates, hlambda, heta, hepsilon, hthetaOrder,
          hthetaSquare, hlambdaOrder, hetaOrder, hetaRelation,
          houterAction, hmiddleAction, hcenterAction, hsquareMiddle,
          hcrossFormula⟩
      refine ⟨middleNorm 1, outerNorm 1, ?_⟩
      intro hzero
      have hformula := hcrossFormula 1 1
      rw [hzero] at hformula
      simp only [map_zero, one_pow, map_one, mul_one] at hformula
      exact hepsilon hformula.symm
  rcases hcross with ⟨u, v, huv⟩
  have huMap :
      (u : Additive (LowerCentralFactor P 0)).toMul ∈ A.map q0 :=
    (hU (u : Additive (LowerCentralFactor P 0))).mp u.property
  rcases huMap with ⟨x, hxA, hqx⟩
  obtain ⟨y, hqy⟩ := hq0_surj (v : Additive (LowerCentralFactor P 0)).toMul
  let x0 : (⊤ : Subgroup P).lowerCentralSeries 0 := Subgroup.topEquiv.symm x
  let y0 : (⊤ : Subgroup P).lowerCentralSeries 0 := Subgroup.topEquiv.symm y
  have hcomm : ⁅(x0 : P), (y0 : P)⁆ ∈ (⊤ : Subgroup P).lowerCentralSeries 1 := by
    rw [Subgroup.top_lowerCentralSeries_one]
    exact Subgroup.commutator_mem_commutator (by simp) (by simp)
  have hxmk :
      Additive.ofMul
          (QuotientGroup.mk' (lowerCentralFactorKernel P 0) x0) =
        (u : Additive (LowerCentralFactor P 0)) := by
    apply Additive.toMul.injective
    change QuotientGroup.mk' (lowerCentralFactorKernel P 0) x0 = (u : Additive (LowerCentralFactor P 0)).toMul
    calc
      QuotientGroup.mk' (lowerCentralFactorKernel P 0) x0 = q0 x := by
        simpa [x0] using (hq0_mk x).symm
      _ = (u : Additive (LowerCentralFactor P 0)).toMul := hqx
  have hymk :
      Additive.ofMul
          (QuotientGroup.mk' (lowerCentralFactorKernel P 0) y0) =
        (v : Additive (LowerCentralFactor P 0)) := by
    apply Additive.toMul.injective
    change QuotientGroup.mk' (lowerCentralFactorKernel P 0) y0 = (v : Additive (LowerCentralFactor P 0)).toMul
    calc
      QuotientGroup.mk' (lowerCentralFactorKernel P 0) y0 = q0 y := by
        simpa [y0] using (hq0_mk y).symm
      _ = (v : Additive (LowerCentralFactor P 0)).toMul := hqy
  have hbracketValue := hbracket x0 y0 hcomm
  rw [hxmk, hymk] at hbracketValue
  have hout_ne :
      Additive.ofMul
          (QuotientGroup.mk' (lowerCentralFactorKernel P 1)
            ⟨⁅(x0 : P), (y0 : P)⁆, hcomm⟩) ≠ 0 := by
    rw [← hbracketValue]
    exact huv
  have hcomm_ne : ⁅(x0 : P), (y0 : P)⁆ ≠ 1 := by
    intro hone
    apply hout_ne
    have honeSub :
        (⟨⁅(x0 : P), (y0 : P)⁆, hcomm⟩ :
          (⊤ : Subgroup P).lowerCentralSeries 1) = 1 := Subtype.ext hone
    rw [honeSub, map_one, ofMul_one]
  exact ⟨x, hxA, y, by simpa [x0, y0] using hcomm_ne⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem lemma13_lowerCentralFactorKernel_zero_eq_of_canonical_ker
    {H : Type u} [Group H]
    (B : Subgroup H) (q : H →* LowerCentralFactor H 0)
    (hq_ker : q.ker = B)
    (hq_mk : ∀ p : H, q p =
      QuotientGroup.mk' (lowerCentralFactorKernel H 0)
        (Subgroup.topEquiv.symm p)) :
    lowerCentralFactorKernel H 0 =
      B.subgroupOf ((⊤ : Subgroup H).lowerCentralSeries 0) := by
  ext x
  have hx_top : Subgroup.topEquiv.symm (x : H) = x := by
    apply Subtype.ext
    rfl
  constructor
  · intro hx
    change (x : H) ∈ B
    rw [← hq_ker, MonoidHom.mem_ker, hq_mk]
    apply (QuotientGroup.eq_one_iff _).2
    simpa only [hx_top] using hx
  · intro hx
    rw [← QuotientGroup.ker_mk' (lowerCentralFactorKernel H 0),
      MonoidHom.mem_ker]
    have hqone : q (x : H) = 1 := by
      rw [← MonoidHom.mem_ker, hq_ker]
      exact hx
    rw [hq_mk] at hqone
    simpa only [hx_top] using hqone

private def lemma13_factorZeroInclusionMonoidHom
    {Q : Type u} [Group Q] (H : Subgroup Q) :
    (⊤ : Subgroup H).lowerCentralSeries 0 →* (⊤ : Subgroup Q).lowerCentralSeries 0 where
  toFun x := ⟨((x : H) : Q), by trivial⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private def lemma13_factorZeroInclusionHom
    {Q : Type u} [Group Q]
    (H Phi C : Subgroup Q)
    (hC_le_Phi : C ≤ Phi)
    (hkernelH : lowerCentralFactorKernel H 0 =
      (C.subgroupOf H).subgroupOf ((⊤ : Subgroup H).lowerCentralSeries 0))
    (hkernelQ : lowerCentralFactorKernel Q 0 =
      Phi.subgroupOf ((⊤ : Subgroup Q).lowerCentralSeries 0)) :
    LowerCentralFactor H 0 →* LowerCentralFactor Q 0 :=
  QuotientGroup.lift (lowerCentralFactorKernel H 0)
    ((QuotientGroup.mk' (lowerCentralFactorKernel Q 0)).comp
      (lemma13_factorZeroInclusionMonoidHom H)) (by
        intro x hx
        apply (QuotientGroup.eq_one_iff _).2
        rw [hkernelH] at hx
        rw [hkernelQ]
        exact hC_le_Phi hx)


private noncomputable def lemma13_factorZeroInclusionLinearMap
    {Q : Type u} [Group Q]
    (H Phi C : Subgroup Q)
    (hC_le_Phi : C ≤ Phi)
    (hkernelH : lowerCentralFactorKernel H 0 =
      (C.subgroupOf H).subgroupOf ((⊤ : Subgroup H).lowerCentralSeries 0))
    (hkernelQ : lowerCentralFactorKernel Q 0 =
      Phi.subgroupOf ((⊤ : Subgroup Q).lowerCentralSeries 0)) :
    Additive (LowerCentralFactor H 0) →ₗ[ZMod 2]
      Additive (LowerCentralFactor Q 0) :=
  (lemma13_factorZeroInclusionHom H Phi C hC_le_Phi hkernelH hkernelQ).toAdditive.toZModLinearMap 2

private theorem lemma13_factorZeroInclusionLinearMap_mk
    {Q : Type u} [Group Q]
    (H Phi C : Subgroup Q)
    (hC_le_Phi : C ≤ Phi)
    (hkernelH : lowerCentralFactorKernel H 0 =
      (C.subgroupOf H).subgroupOf ((⊤ : Subgroup H).lowerCentralSeries 0))
    (hkernelQ : lowerCentralFactorKernel Q 0 =
      Phi.subgroupOf ((⊤ : Subgroup Q).lowerCentralSeries 0))
    (x : (⊤ : Subgroup H).lowerCentralSeries 0) :
    lemma13_factorZeroInclusionLinearMap H Phi C hC_le_Phi hkernelH hkernelQ
        (Additive.ofMul
          (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x)) =
      Additive.ofMul
        (QuotientGroup.mk' (lowerCentralFactorKernel Q 0)
          (lemma13_factorZeroInclusionMonoidHom H x)) := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem lemma13_factorZeroInclusionLinearMap_eq_zero_of_mem
    {Q : Type u} [Group Q]
    (H Phi C : Subgroup Q)
    (qH : H →* LowerCentralFactor H 0)
    (U : Submodule (ZMod 2) (Additive (LowerCentralFactor H 0)))
    (hC_le_Phi : C ≤ Phi)
    (hkernelH : lowerCentralFactorKernel H 0 =
      (C.subgroupOf H).subgroupOf ((⊤ : Subgroup H).lowerCentralSeries 0))
    (hkernelQ : lowerCentralFactorKernel Q 0 =
      Phi.subgroupOf ((⊤ : Subgroup Q).lowerCentralSeries 0))
    (hqH_mk : ∀ p : H, qH p =
      QuotientGroup.mk' (lowerCentralFactorKernel H 0)
        (Subgroup.topEquiv.symm p))
    (hU : ∀ z : Additive (LowerCentralFactor H 0),
      z ∈ U ↔ z.toMul ∈ (Phi.subgroupOf H).map qH)
    (u : Additive (LowerCentralFactor H 0)) (hu : u ∈ U) :
    lemma13_factorZeroInclusionLinearMap H Phi C hC_le_Phi
        hkernelH hkernelQ u = 0 := by
  rcases (hU u).mp hu with ⟨p, hpPhi, hp⟩
  have hu_eq : u = Additive.ofMul (qH p) := by
    apply Additive.toMul.injective
    exact hp.symm
  rw [hu_eq, hqH_mk,
    lemma13_factorZeroInclusionLinearMap_mk]
  apply Additive.ofMul.injective
  apply (QuotientGroup.eq_one_iff _).2
  rw [hkernelQ]
  exact hpPhi

private noncomputable def lemma13_factorZeroComplementLinearMap
    {Q : Type u} [Group Q]
    (H Phi C : Subgroup Q)
    (V : Submodule (ZMod 2) (Additive (LowerCentralFactor H 0)))
    (hC_le_Phi : C ≤ Phi)
    (hkernelH : lowerCentralFactorKernel H 0 =
      (C.subgroupOf H).subgroupOf ((⊤ : Subgroup H).lowerCentralSeries 0))
    (hkernelQ : lowerCentralFactorKernel Q 0 =
      Phi.subgroupOf ((⊤ : Subgroup Q).lowerCentralSeries 0)) :
    V →ₗ[ZMod 2] Additive (LowerCentralFactor Q 0) :=
  (lemma13_factorZeroInclusionLinearMap H Phi C hC_le_Phi hkernelH hkernelQ).comp
    V.subtype

private theorem lemma13_factorZeroInclusion_eq_complement
    {Q : Type u} [Group Q]
    (H Phi C : Subgroup Q)
    (qH : H →* LowerCentralFactor H 0)
    (U V : Submodule (ZMod 2) (Additive (LowerCentralFactor H 0)))
    (hC_le_Phi : C ≤ Phi)
    (hkernelH : lowerCentralFactorKernel H 0 =
      (C.subgroupOf H).subgroupOf ((⊤ : Subgroup H).lowerCentralSeries 0))
    (hkernelQ : lowerCentralFactorKernel Q 0 =
      Phi.subgroupOf ((⊤ : Subgroup Q).lowerCentralSeries 0))
    (hqH_mk : ∀ p : H, qH p =
      QuotientGroup.mk' (lowerCentralFactorKernel H 0)
        (Subgroup.topEquiv.symm p))
    (hU : ∀ z : Additive (LowerCentralFactor H 0),
      z ∈ U ↔ z.toMul ∈ (Phi.subgroupOf H).map qH)
    (hUV : IsCompl U V)
    (z : Additive (LowerCentralFactor H 0)) :
    ∃ v : V,
      lemma13_factorZeroInclusionLinearMap H Phi C hC_le_Phi
          hkernelH hkernelQ z =
        lemma13_factorZeroComplementLinearMap H Phi C V hC_le_Phi
          hkernelH hkernelQ v := by
  obtain ⟨u, v, huv, _⟩ :=
    Submodule.existsUnique_add_of_isCompl hUV z
  refine ⟨v, ?_⟩
  calc
    lemma13_factorZeroInclusionLinearMap H Phi C hC_le_Phi
          hkernelH hkernelQ z =
        lemma13_factorZeroInclusionLinearMap H Phi C hC_le_Phi
          hkernelH hkernelQ ((u : Additive (LowerCentralFactor H 0)) + v) := by
            rw [huv]
    _ = lemma13_factorZeroInclusionLinearMap H Phi C hC_le_Phi
          hkernelH hkernelQ u +
        lemma13_factorZeroInclusionLinearMap H Phi C hC_le_Phi
          hkernelH hkernelQ v := by rw [map_add]
    _ = lemma13_factorZeroInclusionLinearMap H Phi C hC_le_Phi
          hkernelH hkernelQ v := by
            rw [lemma13_factorZeroInclusionLinearMap_eq_zero_of_mem
              H Phi C qH U hC_le_Phi hkernelH hkernelQ hqH_mk hU u
                u.property, zero_add]
    _ = lemma13_factorZeroComplementLinearMap H Phi C V hC_le_Phi
          hkernelH hkernelQ v := rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem lemma13_factorZeroComplementLinearMap_injective
    {Q : Type u} [Group Q]
    (H Phi C : Subgroup Q)
    (_hPhi_le_H : Phi ≤ H)
    (U V : Submodule (ZMod 2) (Additive (LowerCentralFactor H 0)))
    (qH : H →* LowerCentralFactor H 0)
    (hC_le_Phi : C ≤ Phi)
    (hkernelH : lowerCentralFactorKernel H 0 =
      (C.subgroupOf H).subgroupOf ((⊤ : Subgroup H).lowerCentralSeries 0))
    (hkernelQ : lowerCentralFactorKernel Q 0 =
      Phi.subgroupOf ((⊤ : Subgroup Q).lowerCentralSeries 0))
    (hqH_mk : ∀ p : H, qH p =
      QuotientGroup.mk' (lowerCentralFactorKernel H 0)
        (Subgroup.topEquiv.symm p))
    (hU : ∀ z : Additive (LowerCentralFactor H 0),
      z ∈ U ↔ z.toMul ∈ (Phi.subgroupOf H).map qH)
    (hUV : IsCompl U V) :
    Function.Injective
      (lemma13_factorZeroComplementLinearMap H Phi C V hC_le_Phi hkernelH hkernelQ) := by
  intro v w hvw
  have hsub : (v : Additive (LowerCentralFactor H 0)) - w ∈ U := by
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
      (lowerCentralFactorKernel H 0) ((v : Additive (LowerCentralFactor H 0)) - w).toMul
    let p : H := (x : H)
    have hrepr : ((v : Additive (LowerCentralFactor H 0)) - w).toMul = qH p := by
      rw [hqH_mk]
      have hx_top : Subgroup.topEquiv.symm p = x := by
        apply Subtype.ext
        rfl
      rw [hx_top]
      exact hx.symm
    apply (hU _).2
    have htargetZero :
        lemma13_factorZeroInclusionLinearMap H Phi C hC_le_Phi hkernelH hkernelQ
            ((v : Additive (LowerCentralFactor H 0)) - w) = 0 := by
      rw [map_sub]
      change lemma13_factorZeroComplementLinearMap H Phi C V hC_le_Phi hkernelH hkernelQ v -
          lemma13_factorZeroComplementLinearMap H Phi C V hC_le_Phi hkernelH hkernelQ w = 0
      rw [hvw, sub_self]
    have hxAdd :
        Additive.ofMul
            (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x) =
          (v : Additive (LowerCentralFactor H 0)) - w := by
      apply Additive.toMul.injective
      exact hx
    have hmkZero :
        QuotientGroup.mk' (lowerCentralFactorKernel Q 0)
          (lemma13_factorZeroInclusionMonoidHom H x) = 1 := by
      apply Additive.ofMul.injective
      rw [← lemma13_factorZeroInclusionLinearMap_mk
        H Phi C hC_le_Phi hkernelH hkernelQ x, hxAdd]
      exact htargetZero
    have hxPhi : ((x : H) : Q) ∈ Phi := by
      have hxker := (QuotientGroup.eq_one_iff
        (N := lowerCentralFactorKernel Q 0)
        (lemma13_factorZeroInclusionMonoidHom H x)).mp hmkZero
      rw [hkernelQ] at hxker
      exact hxker
    let pPhi : Phi.subgroupOf H := ⟨p, hxPhi⟩
    exact ⟨pPhi, pPhi.property, by simp [hrepr, pPhi]⟩
  have hsubV : (v : Additive (LowerCentralFactor H 0)) - w ∈ V :=
    V.sub_mem v.property w.property
  have hbot : (v : Additive (LowerCentralFactor H 0)) - w ∈ (⊥ :
      Submodule (ZMod 2) (Additive (LowerCentralFactor H 0))) :=
    hUV.1.le_bot ⟨hsub, hsubV⟩
  have hzero : (v : Additive (LowerCentralFactor H 0)) - w = 0 := by
    simpa using hbot
  apply Subtype.ext
  exact sub_eq_zero.mp hzero

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem lemma13_factorZeroInclusionLinearMap_equivariant
    {Q : Type u} [Group Q]
    (H Phi C : Subgroup Q)
    (hC_le_Phi : C ≤ Phi)
    (hkernelH : lowerCentralFactorKernel H 0 =
      (C.subgroupOf H).subgroupOf ((⊤ : Subgroup H).lowerCentralSeries 0))
    (hkernelQ : lowerCentralFactorKernel Q 0 =
      Phi.subgroupOf ((⊤ : Subgroup Q).lowerCentralSeries 0))
    (thetaQ : MulAut Q) (thetaH : MulAut H)
    (hcompat : ∀ x : H, thetaQ (x : Q) = (thetaH x : H))
    (v : Additive (LowerCentralFactor H 0)) :
    lemma13_factorZeroInclusionLinearMap H Phi C hC_le_Phi hkernelH hkernelQ
        (lowerCentralFactorLinearAut thetaH 0 v) =
      lowerCentralFactorLinearAut thetaQ 0
        (lemma13_factorZeroInclusionLinearMap H Phi C hC_le_Phi hkernelH hkernelQ v) := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
    (lowerCentralFactorKernel H 0) v.toMul
  have hv : v = Additive.ofMul
      (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x) := by
    apply Additive.toMul.injective
    exact hx.symm
  rw [hv, lowerCentralFactorLinearAut_ofMul_mk,
    lemma13_factorZeroInclusionLinearMap_mk,
    lemma13_factorZeroInclusionLinearMap_mk,
    lowerCentralFactorLinearAut_ofMul_mk]
  apply Additive.ofMul.injective
  apply congrArg (QuotientGroup.mk' (lowerCentralFactorKernel Q 0))
  apply Subtype.ext
  change ((thetaH (x : H) : H) : Q) = thetaQ ((x : H) : Q)
  exact (hcompat (x : H)).symm

private noncomputable def lemma13_zmod2LinearEquivOfMulEquiv
    {G H : Type*} [CommGroup G] [CommGroup H]
    [Module (ZMod 2) (Additive G)] [Module (ZMod 2) (Additive H)]
    (e : G ≃* H) : Additive G ≃ₗ[ZMod 2] Additive H where
  toLinearMap := e.toAdditive.toAddMonoidHom.toZModLinearMap 2
  invFun := e.symm.toAdditive
  left_inv x := by
    apply Additive.toMul.injective
    exact e.symm_apply_apply x.toMul
  right_inv x := by
    apply Additive.toMul.injective
    exact e.apply_symm_apply x.toMul
private noncomputable def lemma13_centerFactorMulEquiv
    {Q : Type u} [Group Q]
    (A C : Subgroup Q)
    (hC_le_A : C ≤ A)
    (hL1A : (⊤ : Subgroup A).lowerCentralSeries 1 = C.subgroupOf A)
    (hkernel1A : lowerCentralFactorKernel A 1 = ⊥)
    (hL2Q : (⊤ : Subgroup Q).lowerCentralSeries 2 = C)
    (hkernel2Q : lowerCentralFactorKernel Q 2 = ⊥) :
    LowerCentralFactor A 1 ≃* LowerCentralFactor Q 2 :=
  ((QuotientGroup.quotientMulEquivOfEq hkernel1A).trans
      (QuotientGroup.quotientBot (G := (⊤ : Subgroup A).lowerCentralSeries 1))).trans
    ((MulEquiv.subgroupCongr hL1A).trans
      ((Subgroup.subgroupOfEquivOfLe hC_le_A).trans
        ((MulEquiv.subgroupCongr hL2Q).symm.trans
          ((QuotientGroup.quotientMulEquivOfEq hkernel2Q).trans
            (QuotientGroup.quotientBot
              (G := (⊤ : Subgroup Q).lowerCentralSeries 2))).symm)))

private noncomputable def lemma13_centerFactorLinearEquiv
    {Q : Type u} [Group Q]
    (A C : Subgroup Q)
    (hC_le_A : C ≤ A)
    (hL1A : (⊤ : Subgroup A).lowerCentralSeries 1 = C.subgroupOf A)
    (hkernel1A : lowerCentralFactorKernel A 1 = ⊥)
    (hL2Q : (⊤ : Subgroup Q).lowerCentralSeries 2 = C)
    (hkernel2Q : lowerCentralFactorKernel Q 2 = ⊥) :
    Additive (LowerCentralFactor A 1) ≃ₗ[ZMod 2]
      Additive (LowerCentralFactor Q 2) :=
  lemma13_zmod2LinearEquivOfMulEquiv
    (lemma13_centerFactorMulEquiv A C hC_le_A hL1A hkernel1A hL2Q hkernel2Q)

private def lemma13_centerSeriesInclusion
    {Q : Type u} [Group Q]
    (A C : Subgroup Q)
    (hL1A : (⊤ : Subgroup A).lowerCentralSeries 1 = C.subgroupOf A)
    (hL2Q : (⊤ : Subgroup Q).lowerCentralSeries 2 = C)
    (x : (⊤ : Subgroup A).lowerCentralSeries 1) : (⊤ : Subgroup Q).lowerCentralSeries 2 :=
  ⟨((x : A) : Q), by
    rw [hL2Q]
    have hxC : (x : A) ∈ C.subgroupOf A := by
      rw [← hL1A]
      exact x.property
    exact hxC⟩

private theorem lemma13_centerFactorLinearEquiv_mk
    {Q : Type u} [Group Q]
    (A C : Subgroup Q)
    (hC_le_A : C ≤ A)
    (hL1A : (⊤ : Subgroup A).lowerCentralSeries 1 = C.subgroupOf A)
    (hkernel1A : lowerCentralFactorKernel A 1 = ⊥)
    (hL2Q : (⊤ : Subgroup Q).lowerCentralSeries 2 = C)
    (hkernel2Q : lowerCentralFactorKernel Q 2 = ⊥)
    (x : (⊤ : Subgroup A).lowerCentralSeries 1) :
    lemma13_centerFactorLinearEquiv A C hC_le_A hL1A hkernel1A hL2Q hkernel2Q
        (Additive.ofMul
          (QuotientGroup.mk' (lowerCentralFactorKernel A 1) x)) =
      Additive.ofMul
        (QuotientGroup.mk' (lowerCentralFactorKernel Q 2)
          (lemma13_centerSeriesInclusion A C hL1A hL2Q x)) := by
  rfl
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private noncomputable def lemma13_middleFactorLinearEquiv
    {Q : Type u} [Group Q]
    (A C Phi : Subgroup Q)
    (hPhi_le_A : Phi ≤ A)
    (qA : A →* LowerCentralFactor A 0)
    (U : Submodule (ZMod 2) (Additive (LowerCentralFactor A 0)))
    (hqA_ker : qA.ker = C.subgroupOf A)
    (hU : ∀ u : Additive (LowerCentralFactor A 0),
      u ∈ U ↔ u.toMul ∈ (Phi.subgroupOf A).map qA)
    (hL1_eq_Phi : (⊤ : Subgroup Q).lowerCentralSeries 1 = Phi)
    (hkernel1_eq_C : lowerCentralFactorKernel Q 1 =
      C.subgroupOf ((⊤ : Subgroup Q).lowerCentralSeries 1)) :
    Additive (LowerCentralFactor Q 1) ≃ₗ[ZMod 2] U := by
  let f0 : (⊤ : Subgroup Q).lowerCentralSeries 1 →* Multiplicative U :=
    { toFun := fun x =>
        let xA : A := ⟨(x : Q), hPhi_le_A (by
          rw [← hL1_eq_Phi]
          exact x.property)⟩
        Multiplicative.ofAdd ⟨Additive.ofMul (qA xA), (hU _).2 (by
          let xPhiA : Phi.subgroupOf A := ⟨xA, by
            rw [← hL1_eq_Phi]
            exact x.property⟩
          exact ⟨xPhiA, xPhiA.property, rfl⟩)⟩
      map_one' := by
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        apply Additive.toMul.injective
        exact qA.map_one
      map_mul' := by
        intro x y
        let xA : A := ⟨(x : Q), hPhi_le_A (by
          rw [← hL1_eq_Phi]
          exact x.property)⟩
        let yA : A := ⟨(y : Q), hPhi_le_A (by
          rw [← hL1_eq_Phi]
          exact y.property)⟩
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        apply Additive.toMul.injective
        change qA (xA * yA) = qA xA * qA yA
        exact qA.map_mul xA yA
    }
  have hf0_ker : f0.ker = lowerCentralFactorKernel Q 1 := by
    ext x
    let xA : A := ⟨(x : Q), hPhi_le_A (by
      rw [← hL1_eq_Phi]
      exact x.property)⟩
    constructor
    · intro hx
      have hq : qA xA = 1 := by
        have hx' := congrArg (fun z : Multiplicative U => z.toAdd) hx
        have hx'' := congrArg Subtype.val hx'
        apply Additive.ofMul.injective
        simpa [f0, xA] using hx''
      rw [hkernel1_eq_C]
      change (x : Q) ∈ C
      have hxAker : xA ∈ qA.ker := hq
      rw [hqA_ker] at hxAker
      exact hxAker
    · intro hx
      have hxC : (x : Q) ∈ C := by
        rw [hkernel1_eq_C] at hx
        exact hx
      have hxAker : xA ∈ qA.ker := by
        rw [hqA_ker]
        exact hxC
      change f0 x = 1
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      apply Additive.toMul.injective
      simpa [f0, xA] using hxAker
  have hf0_surjective : Function.Surjective f0 := by
    intro u
    have huMap : (u.toAdd : Additive (LowerCentralFactor A 0)).toMul ∈
        (Phi.subgroupOf A).map qA :=
      (hU _).1 u.toAdd.property
    rcases huMap with ⟨xPhiA, hxPhiA, hxq⟩
    let x : (⊤ : Subgroup Q).lowerCentralSeries 1 := ⟨((xPhiA : A) : Q), by
      rw [hL1_eq_Phi]
      exact hxPhiA⟩
    refine ⟨x, ?_⟩
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    apply Additive.toMul.injective
    simpa [f0, x] using hxq
  let fLift := QuotientGroup.lift (lowerCentralFactorKernel Q 1) f0
    (by rw [← hf0_ker])
  let f : LowerCentralFactor Q 1 →* Multiplicative U :=
    { toFun := fLift
      map_one' := by
        exact fLift.map_one
      map_mul' := by
        intro x y
        exact fLift.map_mul x y }
  have hf_surjective : Function.Surjective f := by
    intro u
    obtain ⟨x, hx⟩ := hf0_surjective u
    refine ⟨QuotientGroup.mk' (lowerCentralFactorKernel Q 1) x, ?_⟩
    exact hx
  have hf_injective : Function.Injective f := by
    intro x
    refine Quotient.inductionOn' x ?_
    intro a y
    refine Quotient.inductionOn' y ?_
    intro b hab
    apply QuotientGroup.eq_iff_div_mem.mpr
    rw [← hf0_ker]
    change f0 (a / b) = 1
    rw [map_div, show f0 a = f0 b by exact hab]
    simp
  letI : Module (ZMod 2) (Additive (Multiplicative U)) :=
    inferInstanceAs (Module (ZMod 2) U)
  exact lemma13_zmod2LinearEquivOfMulEquiv
    (MulEquiv.ofBijective f ⟨hf_injective, hf_surjective⟩)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem lemma13_middleFactorLinearEquiv_mk
    {Q : Type u} [Group Q]
    (A C Phi : Subgroup Q)
    (hPhi_le_A : Phi ≤ A)
    (qA : A →* LowerCentralFactor A 0)
    (U : Submodule (ZMod 2) (Additive (LowerCentralFactor A 0)))
    (hqA_ker : qA.ker = C.subgroupOf A)
    (hU : ∀ u : Additive (LowerCentralFactor A 0),
      u ∈ U ↔ u.toMul ∈ (Phi.subgroupOf A).map qA)
    (hL1_eq_Phi : (⊤ : Subgroup Q).lowerCentralSeries 1 = Phi)
    (hkernel1_eq_C : lowerCentralFactorKernel Q 1 =
      C.subgroupOf ((⊤ : Subgroup Q).lowerCentralSeries 1))
    (x : (⊤ : Subgroup Q).lowerCentralSeries 1) :
    ((lemma13_middleFactorLinearEquiv A C Phi hPhi_le_A qA U hqA_ker hU
        hL1_eq_Phi hkernel1_eq_C
        (Additive.ofMul
          (QuotientGroup.mk' (lowerCentralFactorKernel Q 1) x)) : U) :
      Additive (LowerCentralFactor A 0)) =
      Additive.ofMul (qA
        (⟨(x : Q), hPhi_le_A (by
          rw [← hL1_eq_Phi]
          exact x.property)⟩ : A)) := by
  rfl

private theorem lemma13_alternating_isSymm
    {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] W)
    (halternating : ∀ v : V, B v v = 0) :
    ∀ x y : V, B x y = B y x := by
  intro x y
  calc
    B x y = -B x y := (ZModModule.neg_eq_self _).symm
    _ = B y x := LinearMap.IsAlt.neg halternating x y

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem lemma13_factorZeroInclusion_bracket_eq_zero
    {Q : Type u} [Group Q]
    (A Phi C : Subgroup Q)
    (hC_le_Phi : C ≤ Phi) (hcommAA_le_C : ⁅A, A⁆ ≤ C)
    (hkernel0A : lowerCentralFactorKernel A 0 =
      (C.subgroupOf A).subgroupOf ((⊤ : Subgroup A).lowerCentralSeries 0))
    (hkernel0Q : lowerCentralFactorKernel Q 0 =
      Phi.subgroupOf ((⊤ : Subgroup Q).lowerCentralSeries 0))
    (hkernel1Q : lowerCentralFactorKernel Q 1 =
      C.subgroupOf ((⊤ : Subgroup Q).lowerCentralSeries 1))
    (bracketQ : Additive (LowerCentralFactor Q 0) →ₗ[ZMod 2]
      Additive (LowerCentralFactor Q 0) →ₗ[ZMod 2]
        Additive (LowerCentralFactor Q 1))
    (hbracketQ_mk : ∀ x y : (⊤ : Subgroup Q).lowerCentralSeries 0,
      ∀ hcomm : ⁅(x : Q), (y : Q)⁆ ∈ (⊤ : Subgroup Q).lowerCentralSeries 1,
        bracketQ
            (Additive.ofMul
              (QuotientGroup.mk' (lowerCentralFactorKernel Q 0) x))
            (Additive.ofMul
              (QuotientGroup.mk' (lowerCentralFactorKernel Q 0) y)) =
          Additive.ofMul
            (QuotientGroup.mk' (lowerCentralFactorKernel Q 1)
              ⟨⁅(x : Q), (y : Q)⁆, hcomm⟩))
    (a b : Additive (LowerCentralFactor A 0)) :
    bracketQ
        (lemma13_factorZeroInclusionLinearMap A Phi C hC_le_Phi
          hkernel0A hkernel0Q a)
        (lemma13_factorZeroInclusionLinearMap A Phi C hC_le_Phi
          hkernel0A hkernel0Q b) = 0 := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
    (lowerCentralFactorKernel A 0) a.toMul
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective
    (lowerCentralFactorKernel A 0) b.toMul
  have ha : a = Additive.ofMul
      (QuotientGroup.mk' (lowerCentralFactorKernel A 0) x) := by
    apply Additive.toMul.injective
    exact hx.symm
  have hb : b = Additive.ofMul
      (QuotientGroup.mk' (lowerCentralFactorKernel A 0) y) := by
    apply Additive.toMul.injective
    exact hy.symm
  let xQ : (⊤ : Subgroup Q).lowerCentralSeries 0 := lemma13_factorZeroInclusionMonoidHom A x
  let yQ : (⊤ : Subgroup Q).lowerCentralSeries 0 := lemma13_factorZeroInclusionMonoidHom A y
  have hcommQ : ⁅(xQ : Q), (yQ : Q)⁆ ∈ (⊤ : Subgroup Q).lowerCentralSeries 1 := by
    rw [Subgroup.top_lowerCentralSeries_one]
    exact Subgroup.commutator_mem_commutator (by trivial) (by trivial)
  rw [ha, hb, lemma13_factorZeroInclusionLinearMap_mk,
    lemma13_factorZeroInclusionLinearMap_mk,
    hbracketQ_mk xQ yQ hcommQ]
  apply Additive.ofMul.injective
  apply (QuotientGroup.eq_one_iff _).2
  rw [hkernel1Q]
  change ⁅((x : A) : Q), ((y : A) : Q)⁆ ∈ C
  apply hcommAA_le_C
  exact Subgroup.commutator_mem_commutator (x : A).property (y : A).property

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem lemma13_localBracket_to_ambientIterated
    {Q : Type u} [Group Q]
    (A C Phi : Subgroup Q)
    (hC_le_A : C ≤ A) (hPhi_le_A : Phi ≤ A) (hC_le_Phi : C ≤ Phi)
    (qA : A →* LowerCentralFactor A 0)
    (U : Submodule (ZMod 2) (Additive (LowerCentralFactor A 0)))
    (hqA_ker : qA.ker = C.subgroupOf A)
    (hqA_mk : ∀ p : A, qA p =
      QuotientGroup.mk' (lowerCentralFactorKernel A 0)
        (Subgroup.topEquiv.symm p))
    (hU : ∀ u : Additive (LowerCentralFactor A 0),
      u ∈ U ↔ u.toMul ∈ (Phi.subgroupOf A).map qA)
    (hkernel0A : lowerCentralFactorKernel A 0 =
      (C.subgroupOf A).subgroupOf ((⊤ : Subgroup A).lowerCentralSeries 0))
    (hkernel0Q : lowerCentralFactorKernel Q 0 =
      Phi.subgroupOf ((⊤ : Subgroup Q).lowerCentralSeries 0))
    (hL1A : (⊤ : Subgroup A).lowerCentralSeries 1 = C.subgroupOf A)
    (hkernel1A : lowerCentralFactorKernel A 1 = ⊥)
    (hL1Q : (⊤ : Subgroup Q).lowerCentralSeries 1 = Phi)
    (hkernel1Q : lowerCentralFactorKernel Q 1 =
      C.subgroupOf ((⊤ : Subgroup Q).lowerCentralSeries 1))
    (hL2Q : (⊤ : Subgroup Q).lowerCentralSeries 2 = C)
    (hkernel2Q : lowerCentralFactorKernel Q 2 = ⊥)
    (bracketA : Additive (LowerCentralFactor A 0) →ₗ[ZMod 2]
      Additive (LowerCentralFactor A 0) →ₗ[ZMod 2]
        Additive (LowerCentralFactor A 1))
    (hbracketA : ∀ x y : (⊤ : Subgroup A).lowerCentralSeries 0,
      ∀ hcomm : ⁅(x : A), (y : A)⁆ ∈ (⊤ : Subgroup A).lowerCentralSeries 1,
        bracketA
            (Additive.ofMul
              (QuotientGroup.mk' (lowerCentralFactorKernel A 0) x))
            (Additive.ofMul
              (QuotientGroup.mk' (lowerCentralFactorKernel A 0) y)) =
          Additive.ofMul
            (QuotientGroup.mk' (lowerCentralFactorKernel A 1)
              ⟨⁅(x : A), (y : A)⁆, hcomm⟩))
    (a : Additive (LowerCentralFactor A 0))
    (w : Additive (LowerCentralFactor Q 1)) :
    lemma13_centerFactorLinearEquiv A C hC_le_A hL1A hkernel1A hL2Q hkernel2Q
        (bracketA
          ((lemma13_middleFactorLinearEquiv A C Phi hPhi_le_A qA U hqA_ker hU
              hL1Q hkernel1Q w : U) :
            Additive (LowerCentralFactor A 0)) a) =
      lemma13_lowerCentralIteratedBracket
        (lemma13_factorZeroInclusionLinearMap A Phi C hC_le_Phi
          hkernel0A hkernel0Q a) w := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
    (lowerCentralFactorKernel A 0) a.toMul
  obtain ⟨c, hc⟩ := QuotientGroup.mk'_surjective
    (lowerCentralFactorKernel Q 1) w.toMul
  have ha : a = Additive.ofMul
      (QuotientGroup.mk' (lowerCentralFactorKernel A 0) x) := by
    apply Additive.toMul.injective
    exact hx.symm
  have hw : w = Additive.ofMul
      (QuotientGroup.mk' (lowerCentralFactorKernel Q 1) c) := by
    apply Additive.toMul.injective
    exact hc.symm
  let cA : A := ⟨(c : Q), hPhi_le_A (by
    rw [← hL1Q]
    exact c.property)⟩
  let c0A : (⊤ : Subgroup A).lowerCentralSeries 0 := Subgroup.topEquiv.symm cA
  have hmiddle :
      ((lemma13_middleFactorLinearEquiv A C Phi hPhi_le_A qA U hqA_ker hU
          hL1Q hkernel1Q w : U) :
        Additive (LowerCentralFactor A 0)) =
        Additive.ofMul
          (QuotientGroup.mk' (lowerCentralFactorKernel A 0) c0A) := by
    rw [hw, lemma13_middleFactorLinearEquiv_mk, hqA_mk]
  have hcommA : ⁅(c0A : A), (x : A)⁆ ∈ (⊤ : Subgroup A).lowerCentralSeries 1 := by
    rw [Subgroup.top_lowerCentralSeries_one]
    exact Subgroup.commutator_mem_commutator (by trivial) (by trivial)
  rw [hmiddle, ha, hbracketA c0A x hcommA,
    lemma13_centerFactorLinearEquiv_mk,
    lemma13_factorZeroInclusionLinearMap_mk,
    hw, lemma13_lowerCentralIteratedBracket_mk_mk]
  apply Additive.ofMul.injective
  let q2 := QuotientGroup.mk' (lowerCentralFactorKernel Q 2)
  calc
    q2 (lemma13_centerSeriesInclusion A C hL1A hL2Q
          ⟨⁅(c0A : A), (x : A)⁆, hcommA⟩) =
        q2 ((lemma13_nextBracketLift
          (lemma13_factorZeroInclusionMonoidHom A x) c)⁻¹) := by
      apply congrArg q2
      apply Subtype.ext
      exact (commutatorElement_inv ((x : A) : Q) (c : Q)).symm
    _ = (q2 (lemma13_nextBracketLift
          (lemma13_factorZeroInclusionMonoidHom A x) c))⁻¹ := by
      rw [map_inv]
    _ = q2 (lemma13_nextBracketLift
          (lemma13_factorZeroInclusionMonoidHom A x) c) :=
      inv_eq_of_mul_eq_one_right (by
        simpa [pow_two] using lowerCentralFactor_sq_eq_one 2
          (q2 (lemma13_nextBracketLift
            (lemma13_factorZeroInclusionMonoidHom A x) c)))
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem lemma13_canonicalFactorZeroMap_equivariant
    {H : Type u} [Group H]
    (q : H →* LowerCentralFactor H 0)
    (hq_mk : ∀ p : H, q p =
      QuotientGroup.mk' (lowerCentralFactorKernel H 0)
        (Subgroup.topEquiv.symm p))
    (theta : MulAut H) (a : H) :
    Additive.ofMul (q (theta a)) =
      lowerCentralFactorLinearAut theta 0 (Additive.ofMul (q a)) := by
  rw [hq_mk, hq_mk, lowerCentralFactorLinearAut_ofMul_mk]
  apply Additive.ofMul.injective
  apply congrArg (QuotientGroup.mk' (lowerCentralFactorKernel H 0))
  apply Subtype.ext
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem lemma13_middleFactorLinearEquiv_equivariant
    {Q : Type u} [Group Q]
    (A C Phi : Subgroup Q)
    (hPhi_le_A : Phi ≤ A)
    (qA : A →* LowerCentralFactor A 0)
    (U : Submodule (ZMod 2) (Additive (LowerCentralFactor A 0)))
    (hqA_ker : qA.ker = C.subgroupOf A)
    (hU : ∀ u : Additive (LowerCentralFactor A 0),
      u ∈ U ↔ u.toMul ∈ (Phi.subgroupOf A).map qA)
    (hL1_eq_Phi : (⊤ : Subgroup Q).lowerCentralSeries 1 = Phi)
    (hkernel1_eq_C : lowerCentralFactorKernel Q 1 =
      C.subgroupOf ((⊤ : Subgroup Q).lowerCentralSeries 1))
    (thetaQ : MulAut Q) (thetaA : MulAut A)
    (hcompat : ∀ a : A, thetaQ (a : Q) = (thetaA a : A))
    (hqA_equivariant : ∀ a : A,
      Additive.ofMul (qA (thetaA a)) =
        lowerCentralFactorLinearAut thetaA 0 (Additive.ofMul (qA a)))
    (v : Additive (LowerCentralFactor Q 1)) :
    ((lemma13_middleFactorLinearEquiv A C Phi hPhi_le_A qA U hqA_ker hU
        hL1_eq_Phi hkernel1_eq_C
        (lowerCentralFactorLinearAut thetaQ 1 v) : U) :
      Additive (LowerCentralFactor A 0)) =
      lowerCentralFactorLinearAut thetaA 0
        ((lemma13_middleFactorLinearEquiv A C Phi hPhi_le_A qA U hqA_ker hU
          hL1_eq_Phi hkernel1_eq_C v : U) :
          Additive (LowerCentralFactor A 0)) := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
    (lowerCentralFactorKernel Q 1) v.toMul
  have hv : v = Additive.ofMul
      (QuotientGroup.mk' (lowerCentralFactorKernel Q 1) x) := by
    apply Additive.toMul.injective
    exact hx.symm
  rw [hv, lowerCentralFactorLinearAut_ofMul_mk,
    lemma13_middleFactorLinearEquiv_mk,
    lemma13_middleFactorLinearEquiv_mk]
  let xA : A := ⟨(x : Q), hPhi_le_A (by
    rw [← hL1_eq_Phi]
    exact x.property)⟩
  have hthetaA_mem : thetaQ (x : Q) ∈ A := by
    rw [hcompat xA]
    exact (thetaA xA).property
  let thetaXA : A := ⟨thetaQ (x : Q), hthetaA_mem⟩
  have hthetaXA : thetaXA = thetaA xA := by
    apply Subtype.ext
    exact hcompat xA
  change Additive.ofMul (qA thetaXA) =
    lowerCentralFactorLinearAut thetaA 0 (Additive.ofMul (qA xA))
  rw [hthetaXA]
  exact hqA_equivariant xA

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem lemma13_exists_frobenius_conjugate_of_equivariant_linearEquiv
    (n : ℕ) (hn : 0 < n)
    (L : BinaryGaloisField n ≃ₗ[ZMod 2] BinaryGaloisField n)
    (alpha beta : BinaryGaloisField n)
    (hL : ∀ x, L (alpha * x) = beta * L x) :
    ∃ j : Fin n, alpha ^ (2 ^ (j : ℕ)) = beta := by
  classical
  let B : BinaryGaloisField n →ₗ[ZMod 2]
      BinaryGaloisField n →ₗ[ZMod 2] BinaryGaloisField n :=
    { toFun := fun a =>
        { toFun := fun b => a * L b
          map_add' := by
            intro b c
            rw [map_add, mul_add]
          map_smul' := by
            intro c b
            fin_cases c <;> simp }
      map_add' := by
        intro a b
        apply LinearMap.ext
        intro c
        change (a + b) * L c = a * L c + b * L c
        exact add_mul a b (L c)
      map_smul' := by
        intro c a
        apply LinearMap.ext
        intro b
        fin_cases c <;> simp }
  obtain ⟨coeff, hexpansion, hsupport⟩ :=
    PFAppendixIII.frobeniusBilinear_expansion_with_support_of_equivariant
      n hn B 1 alpha beta (by
        intro a b
        change (1 * a) * L (alpha * b) = beta * (a * L b)
        rw [one_mul, hL]
        ring)
  have hcoeff : ∃ i j, coeff i j ≠ 0 := by
    by_contra hzero
    push Not at hzero
    have hbad := hexpansion 1 (L.symm 1)
    dsimp [B] at hbad
    simp only [L.apply_symm_apply, one_mul] at hbad
    simp_rw [hzero] at hbad
    simp at hbad
  rcases hcoeff with ⟨i, j, hij⟩
  refine ⟨j, ?_⟩
  simpa using hsupport i j hij


private theorem lemma13_exists_normalized_field_equiv_of_cross_functional
    (n : ℕ)
    (F : BinaryGaloisField n →ₗ[ZMod 2]
      BinaryGaloisField n →ₗ[ZMod 2] BinaryGaloisField n)
    (L : BinaryGaloisField n ≃ₗ[ZMod 2] BinaryGaloisField n)
    (sigmaA sigmaY : BinaryGaloisField n ≃+* BinaryGaloisField n)
    (hA : ∀ a y, F a y = sigmaA a * F 1 y)
    (hY : ∀ a y, L (F a y) = sigmaY y * L (F a 1))
    (hne : ∃ a y, F a y ≠ 0) :
    ∃ T : BinaryGaloisField n ≃+* BinaryGaloisField n,
      ∀ x, T x = (L (F 1 1))⁻¹ * L (F 1 1 * x) := by
  let c : BinaryGaloisField n := F 1 1
  let d : BinaryGaloisField n := L c
  have hc : c ≠ 0 := by
    intro hc0
    rcases hne with ⟨a, y, hay⟩
    have hF1y : F 1 y = 0 := by
      apply L.injective
      rw [hY]
      simp [c, hc0]
    apply hay
    rw [hA, hF1y, mul_zero]
  have hd : d ≠ 0 := by
    exact fun hd0 => hc (L.map_eq_zero_iff.mp (by simpa [d] using hd0))
  let cUnit : (BinaryGaloisField n)ˣ := Units.mk0 c hc
  let dUnit : (BinaryGaloisField n)ˣ := Units.mk0 d hd
  let Tlin : BinaryGaloisField n ≃ₗ[ZMod 2] BinaryGaloisField n :=
    ((cUnit.mulLeftLinearEquiv (ZMod 2) (BinaryGaloisField n)).trans L).trans
      ((dUnit⁻¹).mulLeftLinearEquiv (ZMod 2) (BinaryGaloisField n))
  have hTlin (x : BinaryGaloisField n) :
      Tlin x = d⁻¹ * L (c * x) := by
    rfl
  have hTmul (x z : BinaryGaloisField n) : Tlin (x * z) = Tlin x * Tlin z := by
    let a := sigmaA.symm x
    let y := sigmaY.symm (Tlin z)
    have ha : sigmaA a = x := sigmaA.apply_symm_apply x
    have hy : sigmaY y = Tlin z := sigmaY.apply_symm_apply (Tlin z)
    have hF1y : F 1 y = c * z := by
      apply L.injective
      calc
        L (F 1 y) = sigmaY y * L (F 1 1) := hY 1 y
        _ = Tlin z * d := by rw [hy]
        _ = L (c * z) := by
          rw [hTlin]
          field_simp [hd]
    have hcore : L (x * (c * z)) = Tlin z * L (x * c) := by
      calc
        L (x * (c * z)) = L (sigmaA a * F 1 y) := by rw [ha, hF1y]
        _ = L (F a y) := congrArg L (hA a y).symm
        _ = sigmaY y * L (F a 1) := hY a y
        _ = Tlin z * L (x * c) := by rw [hy, hA a 1, ha]
    have hcz : L (c * z) = d * Tlin z := by
      rw [hTlin]
      field_simp [hd]
    rw [hTlin, hTlin, hTlin]
    rw [show c * (x * z) = x * (c * z) by ring, hcore, hcz]
    rw [show L (c * x) = L (x * c) by rw [mul_comm]]
    field_simp [hd]
  let T : BinaryGaloisField n ≃+* BinaryGaloisField n :=
    { toFun := Tlin
      invFun := Tlin.symm
      left_inv := Tlin.symm_apply_apply
      right_inv := Tlin.apply_symm_apply
      map_mul' := hTmul
      map_add' := Tlin.map_add }
  refine ⟨T, ?_⟩
  intro x
  simp [T, hTlin, c, d]

private theorem lemma13_frobenius_index_modEq_of_primitive
    (n a b : ℕ) (hn : 2 ≤ n)
    (lambda : BinaryGaloisField n) (hlambda : lambda ≠ 0)
    (horder : orderOf (Units.mk0 lambda hlambda) = 2 ^ n - 1)
    (hpow : lambda ^ (2 ^ a) = lambda ^ (2 ^ b)) :
    Nat.ModEq n a b := by
  let lambdaUnit : (BinaryGaloisField n)ˣ := Units.mk0 lambda hlambda
  have hunit : lambdaUnit ^ (2 ^ a) = lambdaUnit ^ (2 ^ b) := by
    apply Units.ext
    exact hpow
  have hmod := pow_eq_pow_iff_modEq.mp hunit
  change Nat.ModEq (orderOf lambdaUnit) (2 ^ a) (2 ^ b) at hmod
  rw [show orderOf lambdaUnit = 2 ^ n - 1 by exact horder] at hmod
  have hredA := lemma6_two_pow_modEq_cyclic n a
  have hredB := lemma6_two_pow_modEq_cyclic n b
  have hres : Nat.ModEq (2 ^ n - 1) (2 ^ (a % n)) (2 ^ (b % n)) :=
    hredA.symm.trans (hmod.trans hredB)
  have hsmall (r : ℕ) (hr : r < n) : 2 ^ r < 2 ^ n - 1 := by
    have hrle : r ≤ n - 1 := by omega
    have hpowle : 2 ^ r ≤ 2 ^ (n - 1) :=
      Nat.pow_le_pow_right (by omega) hrle
    have hhalf : 2 ^ (n - 1) < 2 ^ n - 1 := by
      have htwo_le : 2 ≤ 2 ^ (n - 1) := by
        have hpow_le := Nat.pow_le_pow_right
          (by omega : 0 < 2) (by omega : 1 ≤ n - 1)
        simpa using hpow_le
      rw [show n = (n - 1) + 1 by omega, pow_succ]
      rw [show n - 1 + 1 - 1 = n - 1 by omega]
      omega
    exact lt_of_le_of_lt hpowle hhalf
  have heq : 2 ^ (a % n) = 2 ^ (b % n) :=
    hres.eq_of_lt_of_lt (hsmall _ (Nat.mod_lt _ (by omega)))
      (hsmall _ (Nat.mod_lt _ (by omega)))
  change a % n = b % n
  exact Nat.pow_right_injective (by norm_num : 1 < 2) heq

private theorem lemma13_orderOf_twoPow_of_primitive
    (n k : ℕ) (hn : 2 ≤ n)
    (lambda : BinaryGaloisField n) (hlambda : lambda ≠ 0)
    (horder : orderOf (Units.mk0 lambda hlambda) = 2 ^ n - 1) :
    orderOf (Units.mk0 (lambda ^ (2 ^ k)) (pow_ne_zero _ hlambda)) = 2 ^ n - 1 := by
  let lambdaUnit : (BinaryGaloisField n)ˣ := Units.mk0 lambda hlambda
  have hunit : Units.mk0 (lambda ^ (2 ^ k)) (pow_ne_zero _ hlambda) =
      lambdaUnit ^ (2 ^ k) := by
    apply Units.ext
    rfl
  rw [hunit]
  have hodd : Odd (2 ^ n - 1) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    refine ⟨2 ^ m - 1, ?_⟩
    rw [pow_succ]
    have hpos : 0 < 2 ^ m := by positivity
    omega
  have hcop : Nat.Coprime (2 ^ n - 1) (2 ^ k) :=
    Nat.Coprime.pow_right k hodd.coprime_two_right
  rw [orderOf_pow' lambdaUnit (by positivity : 2 ^ k ≠ 0), horder,
    hcop.gcd_eq_one, Nat.div_one]

private theorem lemma13_typeC_frobenius_index
    (n : ℕ) (hn : 2 ≤ n)
    (theta : BinaryGaloisField n ≃+* BinaryGaloisField n)
    (lambda : BinaryGaloisField n) (hlambda : lambda ≠ 0)
    (horder : orderOf (Units.mk0 lambda hlambda) = 2 ^ n - 1)
    (s : Fin n)
    (htheta_lambda : theta lambda = lambda ^ (2 ^ (s : ℕ)))
    (hthetaSquare : ∀ x : BinaryGaloisField n, theta (theta (x ^ 2)) = x) :
    Nat.ModEq n (2 * (s : ℕ) + 1) 0 := by
  have hsquare := hthetaSquare lambda
  have hpow : lambda ^ (2 ^ (2 * (s : ℕ) + 1)) = lambda ^ (2 ^ 0) := by
    rw [show 2 * (s : ℕ) + 1 = (s : ℕ) + ((s : ℕ) + 1) by omega,
      pow_add]
    calc
      lambda ^ (2 ^ (s : ℕ) * 2 ^ ((s : ℕ) + 1)) =
          (lambda ^ (2 ^ (s : ℕ))) ^ (2 ^ ((s : ℕ) + 1)) := by
        rw [pow_mul]
      _ = (theta lambda) ^ (2 ^ ((s : ℕ) + 1)) := by rw [htheta_lambda]
      _ = theta (lambda ^ (2 ^ ((s : ℕ) + 1))) := by rw [map_pow]
      _ = theta (theta (lambda ^ 2)) := by
        congr 1
        rw [map_pow, htheta_lambda, pow_succ, pow_mul]
      _ = lambda := hsquare
      _ = lambda ^ (2 ^ 0) := by simp
  exact lemma13_frobenius_index_modEq_of_primitive n _ _ hn lambda hlambda
    horder hpow

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem lemma13_typeB_jacobi_rank_one
    {P W : Type u} [Group P]
    [AddCommGroup W] [Module (ZMod 2) W]
    (n : ℕ)
    (U V : Submodule (ZMod 2) (Additive (LowerCentralFactor P 0)))
    (bracket : Additive (LowerCentralFactor P 0) →ₗ[ZMod 2]
      Additive (LowerCentralFactor P 0) →ₗ[ZMod 2]
        Additive (LowerCentralFactor P 1))
    (cross : V →ₗ[ZMod 2] W →ₗ[ZMod 2] U)
    (epsilon : BinaryGaloisField n)
    (middleNorm : BinaryGaloisField n ≃ₗ[ZMod 2] U)
    (outerNorm : BinaryGaloisField n ≃ₗ[ZMod 2] V)
    (centerCoordinates : BinaryGaloisField n ≃ₗ[ZMod 2]
      Additive (LowerCentralFactor P 1))
    (hepsilon : epsilon ≠ 0)
    (hcrossFormula : ∀ a b : BinaryGaloisField n,
      centerCoordinates.symm
          (bracket (middleNorm a : Additive (LowerCentralFactor P 0))
            (outerNorm b : Additive (LowerCentralFactor P 0))) =
        epsilon * a * b)
    (hJacobi : ∀ (a a' : V) (w : W),
      bracket ((cross a' w : U) : Additive (LowerCentralFactor P 0))
          (a : Additive (LowerCentralFactor P 0)) +
        bracket ((cross a w : U) : Additive (LowerCentralFactor P 0))
          (a' : Additive (LowerCentralFactor P 0)) = 0) :
    ∀ (a : BinaryGaloisField n) (w : W),
      middleNorm.symm (cross (outerNorm a) w) =
        a * middleNorm.symm (cross (outerNorm 1) w) := by
  intro a w
  have hj := hJacobi (outerNorm a) (outerNorm 1) w
  have hj' := congrArg centerCoordinates.symm hj
  simp only [map_add, map_zero] at hj'
  rw [← middleNorm.apply_symm_apply (cross (outerNorm 1) w),
    ← middleNorm.apply_symm_apply (cross (outerNorm a) w),
    hcrossFormula, hcrossFormula] at hj'
  have hcore :
      epsilon * middleNorm.symm (cross (outerNorm a) w) =
        epsilon * (a * middleNorm.symm (cross (outerNorm 1) w)) := by
    have h := eq_neg_of_add_eq_zero_right hj'
    calc
      epsilon * middleNorm.symm (cross (outerNorm a) w) =
          epsilon * middleNorm.symm (cross (outerNorm a) w) * 1 := by simp
      _ = -(epsilon * middleNorm.symm (cross (outerNorm 1) w) * a) := h
      _ = epsilon * (a * middleNorm.symm (cross (outerNorm 1) w)) := by
        rw [ZModModule.neg_eq_self]
        ring
  exact mul_left_cancel₀ hepsilon hcore

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem lemma13_typeC_jacobi_rank_one
    {P W : Type u} [Group P]
    [AddCommGroup W] [Module (ZMod 2) W]
    (n : ℕ) (hn : 2 ≤ n)
    (U V : Submodule (ZMod 2) (Additive (LowerCentralFactor P 0)))
    (bracket : Additive (LowerCentralFactor P 0) →ₗ[ZMod 2]
      Additive (LowerCentralFactor P 0) →ₗ[ZMod 2]
        Additive (LowerCentralFactor P 1))
    (cross : V →ₗ[ZMod 2] W →ₗ[ZMod 2] U)
    (theta : BinaryGaloisField n ≃+* BinaryGaloisField n)
    (lambda epsilon : BinaryGaloisField n)
    (middleNorm : BinaryGaloisField n ≃ₗ[ZMod 2] U)
    (outerNorm : BinaryGaloisField n ≃ₗ[ZMod 2] V)
    (centerCoordinates : BinaryGaloisField n ≃ₗ[ZMod 2]
      Additive (LowerCentralFactor P 1))
    (hepsilon : epsilon ≠ 0)
    (hthetaSquare : ∀ x : BinaryGaloisField n,
      theta (theta (x ^ 2)) = x)
    (hcrossFormula : ∀ a b : BinaryGaloisField n,
      centerCoordinates.symm
          (bracket (middleNorm b : Additive (LowerCentralFactor P 0))
            (outerNorm a : Additive (LowerCentralFactor P 0))) =
        epsilon * a ^ (2 ^ (n - 1)) * theta (b ^ 2))
    (hJacobi : ∀ (a a' : V) (w : W),
      bracket ((cross a' w : U) : Additive (LowerCentralFactor P 0))
          (a : Additive (LowerCentralFactor P 0)) +
        bracket ((cross a w : U) : Additive (LowerCentralFactor P 0))
          (a' : Additive (LowerCentralFactor P 0)) = 0) :
    ∃ sigma : BinaryGaloisField n ≃+* BinaryGaloisField n,
      (sigma lambda) ^ 2 = theta lambda ∧
      ∀ (a : BinaryGaloisField n) (w : W),
        middleNorm.symm (cross (outerNorm a) w) =
          sigma a * middleNorm.symm (cross (outerNorm 1) w) := by
  let K := BinaryGaloisField n
  let : Fintype K := Fintype.ofFinite K
  let frobAlg : K ≃ₐ[ZMod 2] K :=
    FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K
  let frob : K ≃+* K := frobAlg.toRingEquiv
  let sqrtAlg : K ≃ₐ[ZMod 2] K := frobAlg ^ (n - 1)
  let sqrt : K ≃+* K := sqrtAlg.toRingEquiv
  let psi : K ≃+* K := frob.trans theta
  let sigma : K ≃+* K := sqrt.trans psi.symm
  have hsqrt (x : K) : sqrt x = x ^ (2 ^ (n - 1)) := by
    change ((frobAlg ^ (n - 1) : K ≃ₐ[ZMod 2] K) : K → K) x = _
    rw [AlgEquiv.coe_pow,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
    simp [ZMod.card]
  have hsquareRoot (x : K) :
      (x ^ 2) ^ (2 ^ (n - 1)) = x := by
    calc
      (x ^ 2) ^ (2 ^ (n - 1)) = x ^ (2 ^ n) := by
        rw [← pow_mul]
        congr 1
        calc
          2 * 2 ^ (n - 1) = 2 ^ (n - 1) * 2 := Nat.mul_comm _ _
          _ = 2 ^ ((n - 1) + 1) := (pow_succ 2 (n - 1)).symm
          _ = 2 ^ n := by congr 1; omega
      _ = x := by
        have h := FiniteField.pow_card (K := K) x
        have hcard : Fintype.card K = 2 ^ n := by
          rw [← Nat.card_eq_fintype_card]
          exact GaloisField.card 2 n (by omega)
        simpa only [hcard] using h
  have hsqrt_sq (x : K) : (sqrt x) ^ 2 = x := by
    rw [hsqrt]
    calc
      (x ^ (2 ^ (n - 1))) ^ 2 = (x ^ 2) ^ (2 ^ (n - 1)) := by
        rw [← pow_mul, ← pow_mul]
        congr 1
        omega
      _ = x := hsquareRoot x
  have hsqrt_lambda : sqrt lambda = theta (theta lambda) := by
    apply frob.injective
    change (sqrt lambda) ^ 2 = (theta (theta lambda)) ^ 2
    rw [hsqrt_sq]
    symm
    calc
      (theta (theta lambda)) ^ 2 = theta (theta (lambda ^ 2)) := by
        rw [map_pow, map_pow]
      _ = lambda := hthetaSquare lambda
  have hsigma_sq : (sigma lambda) ^ 2 = theta lambda := by
    apply theta.injective
    change psi (sigma lambda) = theta (theta lambda)
    rw [show psi (sigma lambda) = sqrt lambda by
      exact psi.apply_symm_apply (sqrt lambda)]
    exact hsqrt_lambda
  refine ⟨sigma, hsigma_sq, ?_⟩
  intro a w
  have hj := hJacobi (outerNorm a) (outerNorm 1) w
  have hj' := congrArg centerCoordinates.symm hj
  simp only [map_add, map_zero] at hj'
  rw [← middleNorm.apply_symm_apply (cross (outerNorm 1) w),
    ← middleNorm.apply_symm_apply (cross (outerNorm a) w),
    hcrossFormula, hcrossFormula] at hj'
  have hcore :
      epsilon * theta ((middleNorm.symm (cross (outerNorm a) w)) ^ 2) =
        epsilon * (sqrt a *
          theta ((middleNorm.symm (cross (outerNorm 1) w)) ^ 2)) := by
    have h := eq_neg_of_add_eq_zero_right hj'
    calc
      epsilon * theta ((middleNorm.symm (cross (outerNorm a) w)) ^ 2) =
          epsilon * 1 ^ (2 ^ (n - 1)) *
            theta ((middleNorm.symm (cross (outerNorm a) w)) ^ 2) := by simp
      _ = -(epsilon * a ^ (2 ^ (n - 1)) *
          theta ((middleNorm.symm (cross (outerNorm 1) w)) ^ 2)) := h
      _ = epsilon * (sqrt a *
          theta ((middleNorm.symm (cross (outerNorm 1) w)) ^ 2)) := by
        rw [ZModModule.neg_eq_self, hsqrt]
        ring
  have htheta :
      theta ((middleNorm.symm (cross (outerNorm a) w)) ^ 2) =
        sqrt a * theta ((middleNorm.symm (cross (outerNorm 1) w)) ^ 2) :=
    mul_left_cancel₀ hepsilon hcore
  apply psi.injective
  change theta ((middleNorm.symm (cross (outerNorm a) w)) ^ 2) =
    psi (sigma a * middleNorm.symm (cross (outerNorm 1) w))
  rw [map_mul, show psi (sigma a) = sqrt a by
    exact psi.apply_symm_apply (sqrt a)]
  exact htheta

private def Lemma13JacobiSpectralData
    {P W : Type u} [Group P]
    [AddCommGroup W] [Module (ZMod 2) W]
    (xi : MulAut P) (n : ℕ)
    (U V : Submodule (ZMod 2) (Additive (LowerCentralFactor P 0)))
    (_bracket : Additive (LowerCentralFactor P 0) →ₗ[ZMod 2]
      Additive (LowerCentralFactor P 0) →ₗ[ZMod 2]
        Additive (LowerCentralFactor P 1))
    (cross : V →ₗ[ZMod 2] W →ₗ[ZMod 2] U) : Prop :=
  ∃ (eta rho : BinaryGaloisField n)
      (middleNorm : BinaryGaloisField n ≃ₗ[ZMod 2] U)
      (outerNorm : BinaryGaloisField n ≃ₗ[ZMod 2] V)
      (sigma : BinaryGaloisField n ≃+* BinaryGaloisField n)
      (heta : eta ≠ 0) (hrho : rho ≠ 0),
    orderOf (Units.mk0 eta heta) = 2 ^ n - 1 ∧
    orderOf (Units.mk0 rho hrho) = 2 ^ n - 1 ∧
    ((eta = rho ∧ sigma rho = rho) ∨
      ∃ s : Fin n,
        eta ^ 2 = rho * rho ^ (2 ^ (s : ℕ)) ∧
        Nat.ModEq n (2 * (s : ℕ) + 1) 0 ∧
        (sigma rho) ^ 2 = rho ^ (2 ^ (s : ℕ))) ∧
    (∀ b : BinaryGaloisField n,
      lowerCentralFactorLinearAut xi 0
          (middleNorm b : Additive (LowerCentralFactor P 0)) =
        (middleNorm (eta * b) : Additive (LowerCentralFactor P 0))) ∧
    (∀ a : BinaryGaloisField n,
      lowerCentralFactorLinearAut xi 0
          (outerNorm a : Additive (LowerCentralFactor P 0)) =
        (outerNorm (rho * a) : Additive (LowerCentralFactor P 0))) ∧
    ∀ (a : BinaryGaloisField n) (w : W),
      middleNorm.symm (cross (outerNorm a) w) =
        sigma a * middleNorm.symm (cross (outerNorm 1) w)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem lemma13_jacobiSpectralData_of_normalized
    {P W : Type u} [Group P]
    [AddCommGroup W] [Module (ZMod 2) W]
    (xi : MulAut P) (n : ℕ) (hn : 2 ≤ n)
    (U V : Submodule (ZMod 2) (Additive (LowerCentralFactor P 0)))
    (bracket : Additive (LowerCentralFactor P 0) →ₗ[ZMod 2]
      Additive (LowerCentralFactor P 0) →ₗ[ZMod 2]
        Additive (LowerCentralFactor P 1))
    (squareMap : Additive (LowerCentralFactor P 0) →
      Additive (LowerCentralFactor P 1))
    (cross : V →ₗ[ZMod 2] W →ₗ[ZMod 2] U)
    (hJacobi : ∀ (a a' : V) (w : W),
      bracket ((cross a' w : U) : Additive (LowerCentralFactor P 0))
          (a : Additive (LowerCentralFactor P 0)) +
        bracket ((cross a w : U) : Additive (LowerCentralFactor P 0))
          (a' : Additive (LowerCentralFactor P 0)) = 0)
    (hform : Lemma12TypeBNormalizedData xi n U V bracket squareMap ∨
      Lemma12TypeCNormalizedData xi n U V bracket squareMap) :
    Lemma13JacobiSpectralData xi n U V bracket cross := by
  rcases hform with hformB | hformC
  · unfold Lemma12TypeBNormalizedData at hformB
    rcases hformB with
      ⟨eta, epsilon, middleNorm, outerNorm, centerCoordinates,
        heta, hepsilon, horder, hmiddleAction, houterAction,
        _hcenterAction, _hsquareMiddle, _hsquareOuter, hcrossFormula⟩
    refine ⟨eta, eta, middleNorm, outerNorm, RingEquiv.refl _,
      heta, heta, horder, horder, Or.inl ⟨rfl, rfl⟩,
      hmiddleAction, houterAction, ?_⟩
    exact lemma13_typeB_jacobi_rank_one n U V bracket cross epsilon
      middleNorm outerNorm centerCoordinates hepsilon hcrossFormula hJacobi
  · unfold Lemma12TypeCNormalizedData at hformC
    rcases hformC with
      ⟨theta, lambda, eta, epsilon, outerNorm, middleNorm,
        centerCoordinates, hlambda, heta, hepsilon, _hthetaOrder,
        hthetaSquare, hlambdaOrder, hetaOrder, hetaRelation,
        houterAction, hmiddleAction, _hcenterAction, _hsquareMiddle,
        hcrossFormula⟩
    obtain ⟨s, hthetaLambda⟩ :=
      lemma13_exists_frobenius_conjugate_of_equivariant_linearEquiv
        n (by omega) (theta.toAddEquiv.toLinearEquiv (fun c x => by
          simpa using (ZMod.map_smul theta.toAddMonoidHom c x)))
        lambda (theta lambda) (by
          intro x
          exact theta.map_mul lambda x)
    have hthetaLambda' : theta lambda = lambda ^ (2 ^ (s : ℕ)) :=
      hthetaLambda.symm
    obtain ⟨sigma, hsigmaLambda, hfactor⟩ :=
      lemma13_typeC_jacobi_rank_one n hn U V bracket cross theta lambda
        epsilon middleNorm outerNorm centerCoordinates hepsilon
          hthetaSquare hcrossFormula hJacobi
    refine ⟨eta, lambda, middleNorm, outerNorm, sigma, heta, hlambda,
      hetaOrder, hlambdaOrder, Or.inr ⟨s, ?_, ?_, ?_⟩,
      hmiddleAction, houterAction, hfactor⟩
    · simpa only [hthetaLambda'] using hetaRelation
    · exact lemma13_typeC_frobenius_index n hn theta lambda hlambda
        hlambdaOrder s hthetaLambda' hthetaSquare
    · exact hsigmaLambda.trans hthetaLambda'

private theorem lemma13_primitive_frobenius_ne_one
    (n k : ℕ) (hn : 2 ≤ n)
    (lambda : BinaryGaloisField n) (hlambda : lambda ≠ 0)
    (horder : orderOf (Units.mk0 lambda hlambda) = 2 ^ n - 1) :
    lambda ^ (2 ^ k) ≠ 1 := by
  intro hpow
  have hdiv : 2 ^ n - 1 ∣ 2 ^ k := by
    rw [← horder]
    apply orderOf_dvd_of_pow_eq_one
    apply Units.ext
    exact hpow
  have hodd : Odd (2 ^ n - 1) := by
    obtain ⟨e, he⟩ :=
      Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    refine ⟨2 ^ e - 1, ?_⟩
    rw [he, pow_succ]
    have he_pos : 0 < 2 ^ e := by positivity
    omega
  have hcoprime : Nat.Coprime (2 ^ n - 1) (2 ^ k) :=
    Nat.Coprime.pow_right k hodd.coprime_two_right
  have hone : 2 ^ n - 1 = 1 :=
    Nat.eq_one_of_dvd_coprimes hcoprime dvd_rfl hdiv
  have hfour_le : 4 ≤ 2 ^ n := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hn
  omega

private theorem lemma13_jacobi_spectral_contradiction
    (n : ℕ) (hn : 2 ≤ n)
    (R S E U V : BinaryGaloisField n)
    (hR : R ≠ 0) (hS : S ≠ 0)
    (hRorder : orderOf (Units.mk0 R hR) = 2 ^ n - 1)
    (hSorder : orderOf (Units.mk0 S hS) = 2 ^ n - 1)
    (hcross : U * V = E)
    (hbranchA : (E = R ∧ U = R) ∨
      ∃ s : Fin n,
        E ^ 2 = R * R ^ (2 ^ (s : ℕ)) ∧
        Nat.ModEq n (2 * (s : ℕ) + 1) 0 ∧
        U ^ 2 = R ^ (2 ^ (s : ℕ)))
    (hbranchY : (E = S ∧ V = S) ∨
      ∃ t : Fin n,
        E ^ 2 = S * S ^ (2 ^ (t : ℕ)) ∧
        Nat.ModEq n (2 * (t : ℕ) + 1) 0 ∧
        V ^ 2 = S ^ (2 ^ (t : ℕ))) : False := by
  rcases hbranchA with hbranchA | ⟨s, hEA, hs, hUA⟩
  · rcases hbranchY with hbranchY | ⟨t, hEY, ht, hVY⟩
    · rcases hbranchA with ⟨hER, hUR⟩
      rcases hbranchY with ⟨hES, hVS⟩
      have hE : E ≠ 0 := hER.symm ▸ hR
      have hEE : E * E = E := by
        calc
          E * E = U * V := by rw [hUR, ← hER, hVS, ← hES]
          _ = E := hcross
      have hEone : E = 1 := by
        apply mul_left_cancel₀ hE
        simpa using hEE
      have hRone : R = 1 := hER.symm.trans hEone
      apply lemma13_primitive_frobenius_ne_one n 0 hn R hR hRorder
      simp [hRone]
    · rcases hbranchA with ⟨hER, hUR⟩
      have hE : E ≠ 0 := hER.symm ▸ hR
      have hU : U ≠ 0 := hUR.symm ▸ hR
      have hVone : V = 1 := by
        apply mul_left_cancel₀ hU
        calc
          U * V = E := hcross
          _ = R := hER
          _ = U * 1 := by rw [hUR, mul_one]
      apply lemma13_primitive_frobenius_ne_one n (t : ℕ) hn S hS hSorder
      simpa [hVone] using hVY.symm
  · rcases hbranchY with hbranchY | ⟨t, hEY, ht, hVY⟩
    · rcases hbranchY with ⟨hES, hVS⟩
      have hV : V ≠ 0 := hVS.symm ▸ hS
      have hUone : U = 1 := by
        apply mul_right_cancel₀ hV
        calc
          U * V = E := hcross
          _ = S := hES
          _ = 1 * V := by rw [hVS, one_mul]
      apply lemma13_primitive_frobenius_ne_one n (s : ℕ) hn R hR hRorder
      simpa [hUone] using hUA.symm
    · have hRpow_ne : R ^ (2 ^ (s : ℕ)) ≠ 0 := pow_ne_zero _ hR
      have hSpow_ne : S ^ (2 ^ (t : ℕ)) ≠ 0 := pow_ne_zero _ hS
      have hcross_sq : E ^ 2 =
          R ^ (2 ^ (s : ℕ)) * S ^ (2 ^ (t : ℕ)) := by
        calc
          E ^ 2 = (U * V) ^ 2 := by rw [hcross]
          _ = U ^ 2 * V ^ 2 := by ring
          _ = R ^ (2 ^ (s : ℕ)) * S ^ (2 ^ (t : ℕ)) := by
            rw [hUA, hVY]
      have hR_eq : R = S ^ (2 ^ (t : ℕ)) := by
        apply mul_left_cancel₀ hRpow_ne
        calc
          R ^ (2 ^ (s : ℕ)) * R = R * R ^ (2 ^ (s : ℕ)) :=
            mul_comm _ _
          _ = E ^ 2 := hEA.symm
          _ = R ^ (2 ^ (s : ℕ)) * S ^ (2 ^ (t : ℕ)) := hcross_sq
      have hS_eq : S = R ^ (2 ^ (s : ℕ)) := by
        apply mul_right_cancel₀ hSpow_ne
        calc
          S * S ^ (2 ^ (t : ℕ)) = E ^ 2 := hEY.symm
          _ = R ^ (2 ^ (s : ℕ)) * S ^ (2 ^ (t : ℕ)) := hcross_sq
      have hRcycle : R ^ (2 ^ ((s : ℕ) + (t : ℕ))) = R := by
        calc
          R ^ (2 ^ ((s : ℕ) + (t : ℕ))) =
              R ^ (2 ^ (s : ℕ) * 2 ^ (t : ℕ)) := by rw [pow_add]
          _ = (R ^ (2 ^ (s : ℕ))) ^ (2 ^ (t : ℕ)) :=
            pow_mul _ _ _
          _ = S ^ (2 ^ (t : ℕ)) := by rw [← hS_eq]
          _ = R := hR_eq.symm
      have hsum : Nat.ModEq n ((s : ℕ) + (t : ℕ)) 0 :=
        lemma13_frobenius_index_modEq_of_primitive
          n ((s : ℕ) + (t : ℕ)) 0 hn R hR hRorder (by
            simpa using hRcycle)
      have hsumTwo : Nat.ModEq n (2 * ((s : ℕ) + (t : ℕ))) 0 := by
        simpa using hsum.mul_left 2
      have hsumTwoPlus :
          Nat.ModEq n (2 * ((s : ℕ) + (t : ℕ)) + 2) 0 := by
        convert hs.add ht using 1
        all_goals omega
      have hsumTwoToTwo :
          Nat.ModEq n (2 * ((s : ℕ) + (t : ℕ)) + 2) 2 := by
        simpa using hsumTwo.add_right 2
      have htwoZero : Nat.ModEq n 2 0 :=
        hsumTwoToTwo.symm.trans hsumTwoPlus
      have htwoSZero : Nat.ModEq n (2 * (s : ℕ)) 0 := by
        simpa using htwoZero.mul_right (s : ℕ)
      have htwoSOne : Nat.ModEq n (2 * (s : ℕ) + 1) 1 := by
        simpa using htwoSZero.add_right 1
      have honeZero : Nat.ModEq n 1 0 := htwoSOne.symm.trans hs
      have : (1 : ℕ) = 0 :=
        honeZero.eq_of_lt_of_lt (by omega) (by omega)
      omega

private theorem lemma13_transport_spectral_branch
    (n k : ℕ)
    (T sigma : BinaryGaloisField n ≃+* BinaryGaloisField n)
    (eta rho : BinaryGaloisField n)
    (hbranch : (eta = rho ∧ sigma rho = rho) ∨
      ∃ s : Fin n,
        eta ^ 2 = rho * rho ^ (2 ^ (s : ℕ)) ∧
        Nat.ModEq n (2 * (s : ℕ) + 1) 0 ∧
        (sigma rho) ^ 2 = rho ^ (2 ^ (s : ℕ))) :
    ((T (eta ^ (2 ^ k)) = T (rho ^ (2 ^ k)) ∧
        T (sigma (rho ^ (2 ^ k))) = T (rho ^ (2 ^ k))) ∨
      ∃ s : Fin n,
        (T (eta ^ (2 ^ k))) ^ 2 =
            T (rho ^ (2 ^ k)) *
              T (rho ^ (2 ^ k)) ^ (2 ^ (s : ℕ)) ∧
        Nat.ModEq n (2 * (s : ℕ) + 1) 0 ∧
        (T (sigma (rho ^ (2 ^ k)))) ^ 2 =
          T (rho ^ (2 ^ k)) ^ (2 ^ (s : ℕ))) := by
  rcases hbranch with ⟨heta, hsigma⟩ | ⟨s, heta, hs, hsigma⟩
  · refine Or.inl ⟨?_, ?_⟩
    · rw [heta]
    · simp only [map_pow, hsigma]
  · refine Or.inr ⟨s, ?_, hs, ?_⟩
    · calc
        (T (eta ^ (2 ^ k))) ^ 2 = T ((eta ^ (2 ^ k)) ^ 2) := by
          exact (map_pow T (eta ^ (2 ^ k)) 2).symm
        _ = T ((eta ^ 2) ^ (2 ^ k)) := by rw [pow_right_comm]
        _ = T ((rho * rho ^ (2 ^ (s : ℕ))) ^ (2 ^ k)) := by rw [heta]
        _ = T (rho ^ (2 ^ k) *
            (rho ^ (2 ^ (s : ℕ))) ^ (2 ^ k)) := by rw [mul_pow]
        _ = T (rho ^ (2 ^ k) *
            (rho ^ (2 ^ k)) ^ (2 ^ (s : ℕ))) := by
              rw [pow_right_comm rho (2 ^ (s : ℕ)) (2 ^ k)]
        _ = T (rho ^ (2 ^ k)) *
            T (rho ^ (2 ^ k)) ^ (2 ^ (s : ℕ)) := by
              simp only [map_mul, map_pow]
    · calc
        (T (sigma (rho ^ (2 ^ k)))) ^ 2 =
            T ((sigma (rho ^ (2 ^ k))) ^ 2) := by
              exact (map_pow T (sigma (rho ^ (2 ^ k))) 2).symm
        _ = T (((sigma rho) ^ (2 ^ k)) ^ 2) := by
              rw [map_pow sigma rho (2 ^ k)]
        _ = T (((sigma rho) ^ 2) ^ (2 ^ k)) := by rw [pow_right_comm]
        _ = T ((rho ^ (2 ^ (s : ℕ))) ^ (2 ^ k)) := by rw [hsigma]
        _ = T ((rho ^ (2 ^ k)) ^ (2 ^ (s : ℕ))) := by
              rw [pow_right_comm rho (2 ^ (s : ℕ)) (2 ^ k)]
        _ = T (rho ^ (2 ^ k)) ^ (2 ^ (s : ℕ)) := by
              exact map_pow T (rho ^ (2 ^ k)) (2 ^ (s : ℕ))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem lemma13_coordinate_action_pow
    {H : Type u} [Group H]
    (xi : MulAut H) (n : ℕ)
    (W : Submodule (ZMod 2) (Additive (LowerCentralFactor H 0)))
    (coordinates : BinaryGaloisField n ≃ₗ[ZMod 2] W)
    (lambda : BinaryGaloisField n)
    (hAction : ∀ a : BinaryGaloisField n,
      lowerCentralFactorLinearAut xi 0
          (coordinates a : Additive (LowerCentralFactor H 0)) =
        (coordinates (lambda * a) :
          Additive (LowerCentralFactor H 0))) :
    ∀ j : ℕ, ∀ a : BinaryGaloisField n,
      (lowerCentralFactorLinearAut xi 0 ^ j)
          (coordinates a : Additive (LowerCentralFactor H 0)) =
        (coordinates (lambda ^ j * a) :
          Additive (LowerCentralFactor H 0)) := by
  intro j
  induction j with
  | zero =>
      intro a
      simp
  | succ j ih =>
      intro a
      rw [pow_succ, LinearEquiv.mul_apply, hAction, ih]
      simp [pow_succ, mul_assoc]
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
public theorem lemma13_no_length_greater_than_three
    {X P : Type u} [Group X] [Group P] [MulDistribMulAction X P]
    (_hP : IsSuzukiTwoGroup P)
    (_hXcyclic : IsCyclic X) (_hXfaithful : FaithfulSMul X P)
    (_hXregular : ActionRegularOn X P (involutions P))
    (_hXtrans : ∀ x : P, x ∈ involutions P →
      ∀ y : P, y ∈ involutions P → ∃ k : X, y = k • x)
    (_hXprimeSupport : ∀ p : ℕ, p.Prime → p ∣ Nat.card X →
      p ∣ Nat.card {x : P // x ∈ involutions P}) :
    ¬ (∃ m : ℕ, 3 < m ∧ OmegaLength X P m) := by
  have hlengthFourImpossible :
      ∀ {Q : Type u} [Group Q] [MulDistribMulAction X Q],
        IsSuzukiTwoGroup Q → IsCyclic X → FaithfulSMul X Q →
        ActionRegularOn X Q (involutions Q) →
        (∀ x : Q, x ∈ involutions Q →
          ∀ y : Q, y ∈ involutions Q → ∃ k : X, y = k • x) →
        (∀ p : ℕ, p.Prime → p ∣ Nat.card X →
          p ∣ Nat.card {x : Q // x ∈ involutions Q}) →
        OmegaLength X Q 4 → False := by
    classical
    intro Q _ _ hQ hXcyclic hXfaithful hXregular hXtrans
      hXprimeSupport hLen
    let : Finite Q := finite_of_isSuzukiTwoGroup hQ
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let : Fact (IsPGroup 2 Q) := ⟨isPGroup_of_isSuzukiTwoGroup hQ⟩
    rcases hLen with ⟨subgroups, htop, hbot, _hle, hsteps⟩
    let A : Subgroup Q := subgroups ⟨1, by decide⟩
    let B : Subgroup Q := subgroups ⟨2, by decide⟩
    let C : Subgroup Q := subgroups ⟨3, by decide⟩
    have hupper :
        A < ⊤ ∧ (⊤ : Subgroup Q).Normal ∧ A.Normal ∧
          IsXInvariantSubgroup X (⊤ : Subgroup Q) ∧
          IsXInvariantSubgroup X A ∧
          ∀ L : Subgroup Q, L.Normal → IsXInvariantSubgroup X L →
            A ≤ L → L ≤ ⊤ → L = A ∨ L = ⊤ := by
      have h := hsteps (0 : Fin 4)
      simpa [A, htop] using h
    have hmiddle :
        B < A ∧ A.Normal ∧ B.Normal ∧
          IsXInvariantSubgroup X A ∧ IsXInvariantSubgroup X B ∧
          ∀ L : Subgroup Q, L.Normal → IsXInvariantSubgroup X L →
            B ≤ L → L ≤ A → L = B ∨ L = A := by
      have h := hsteps (1 : Fin 4)
      simpa [A, B] using h
    have hlower :
        C < B ∧ B.Normal ∧ C.Normal ∧
          IsXInvariantSubgroup X B ∧ IsXInvariantSubgroup X C ∧
          ∀ L : Subgroup Q, L.Normal → IsXInvariantSubgroup X L →
            C ≤ L → L ≤ B → L = C ∨ L = B := by
      have h := hsteps (2 : Fin 4)
      simpa [B, C] using h
    have hbottom :
        (⊥ : Subgroup Q) < C ∧ C.Normal ∧ (⊥ : Subgroup Q).Normal ∧
          IsXInvariantSubgroup X C ∧
          IsXInvariantSubgroup X (⊥ : Subgroup Q) ∧
          ∀ L : Subgroup Q, L.Normal → IsXInvariantSubgroup X L →
            ⊥ ≤ L → L ≤ C → L = ⊥ ∨ L = C := by
      have hs4 : subgroups (4 : Fin 5) = (⊥ : Subgroup Q) := by
        simpa using hbot
      have h := hsteps (3 : Fin 4)
      simpa [C, hs4] using h
    let PhiTop : Subgroup Q :=
      (frattini (⊤ : Subgroup Q)).map (⊤ : Subgroup Q).subtype
    have hPhiData : IsMulCommutative PhiTop ∧
        ∀ x : PhiTop, x ^ 4 = 1 := by
      simpa [PhiTop] using lemma9_frattini_abelian_exponent_four
        hQ hXcyclic hXfaithful hXtrans
    have hPhiCommonData :
        PhiTop = frattini Q ∧ PhiTop.Normal ∧
          IsXInvariantSubgroup X PhiTop ∧ PhiTop ≠ ⊥ ∧
          ∀ a : Q, IsInvolution a → a ∈ PhiTop := by
      have hPhiTop_eq : PhiTop = frattini Q := by
        ext p
        constructor
        · rintro ⟨z, hz, rfl⟩
          exact
            (frattini_le_comap_frattini_of_surjective
              (φ := (⊤ : Subgroup Q).subtype) (by
                intro q
                exact ⟨⟨q, trivial⟩, rfl⟩)) hz
        · intro hp
          have hz :=
            (frattini_le_comap_frattini_of_surjective
              (φ := (Subgroup.topEquiv (G := Q)).symm.toMonoidHom)
              (Subgroup.topEquiv (G := Q)).symm.surjective) hp
          exact ⟨(Subgroup.topEquiv (G := Q)).symm p, hz, by simp⟩
      have hPhiNormal : PhiTop.Normal := by
        rw [hPhiTop_eq]
        infer_instance
      have hPhiX : IsXInvariantSubgroup X PhiTop := by
        change ∀ x : X, ∀ a : Q, a ∈ PhiTop ↔ x • a ∈ PhiTop
        rw [hPhiTop_eq]
        exact (isInvariant_of_characteristic (A := X) (G := Q)
          (frattini Q)).invariant
      have hPhiNe : PhiTop ≠ ⊥ := by
        intro hPhiBot
        have hcomm_le : commutator Q ≤ frattini Q :=
          commutator_le_frattini_of_isPGroup (R := Q) (p := 2)
        have hcomm_bot : commutator Q = ⊥ := by
          apply le_antisymm
          · rw [← hPhiTop_eq, hPhiBot] at hcomm_le
            exact hcomm_le
          · exact bot_le
        apply hQ.2.1
        have hcenter_top : Subgroup.center Q = ⊤ :=
          (commutator_eq_bot_iff_center_eq_top Q).mp hcomm_bot
        let : CommGroup Q := Group.commGroupOfCenterEqTop hcenter_top
        exact IsMulCommutative.mk <| Std.Commutative.mk <| fun x y => mul_comm x y
      exact ⟨hPhiTop_eq, hPhiNormal, hPhiX, hPhiNe,
        lemma1_involutions_mem_of_nontrivial_invariant
          hQ hXtrans hPhiX hPhiNe⟩
    rcases hPhiCommonData with
      ⟨hPhiTop_eq, hPhiNormal, hPhiX, hPhiNe, hAllInvPhi⟩
    have hCData : IsMulCommutative C ∧ ∀ x : C, x ^ 2 = 1 := by
      exact lemma9_minimal_invariant_abelian_exponent_two
        hQ hbottom.2.1 hbottom.2.2.2.1 (ne_of_gt hbottom.1)
        (fun D hDn hDX hDC =>
          hbottom.2.2.2.2.2 D hDn hDX bot_le hDC)
    have hC_le_Phi : C ≤ PhiTop := by
      intro c hc
      by_cases hc_one : c = 1
      · subst c
        exact PhiTop.one_mem
      · apply hAllInvPhi c
        refine ⟨hc_one, ?_⟩
        let cC : C := ⟨c, hc⟩
        simpa [cC] using congrArg Subtype.val (hCData.2 cC)
    have hPhi_le_A : PhiTop ≤ A := by
      let D : Subgroup Q := A ⊔ PhiTop
      have hD_normal : D.Normal := by
        let : A.Normal := hupper.2.2.1
        let : PhiTop.Normal := hPhiNormal
        dsimp [D]
        infer_instance
      have hD_X : IsXInvariantSubgroup X D := by
        let : IsInvariant X Q A := ⟨hupper.2.2.2.2.1⟩
        let : IsInvariant X Q PhiTop := ⟨hPhiX⟩
        exact (isInvariant_sup A PhiTop).invariant
      rcases hupper.2.2.2.2.2 D hD_normal hD_X le_sup_left le_top with
        hD_A | hD_top
      · exact le_sup_right.trans (le_of_eq hD_A)
      · have hA_top : A = ⊤ :=
          frattini_nongenerating (G := Q) (K := A) (by
            simpa [D, hPhiTop_eq] using hD_top)
        exact False.elim (hupper.1.ne hA_top)
    have hAllInvC : ∀ a : Q, IsInvolution a → a ∈ C :=
      lemma1_involutions_mem_of_nontrivial_invariant
        hQ hXtrans hbottom.2.2.2.1 (ne_of_gt hbottom.1)
    obtain ⟨nC, hnC, hC_card⟩ :
        ∃ n : ℕ, n ≠ 0 ∧ Nat.card C = 2 ^ n := by
      obtain ⟨n, hcard⟩ :=
        (isPGroup_of_isSuzukiTwoGroup hQ).to_subgroup C |>.exists_card_eq
      refine ⟨n, ?_, hcard⟩
      intro hn
      have hcard_one : Nat.card C = 1 := by simpa [hn] using hcard
      have hC_bot : C = ⊥ :=
        (Subgroup.card_eq_one (H := C)).mp hcard_one
      exact (ne_of_gt hbottom.1) hC_bot
    let involEquivC : {x : Q // x ∈ involutions Q} ≃ {c : C // c ≠ 1} :=
      { toFun := fun x =>
          ⟨⟨x, hAllInvC x x.property⟩,
            fun hx => x.property.1 (congrArg Subtype.val hx)⟩
        invFun := fun c =>
          ⟨c.1, ⟨fun hc => c.2 (Subtype.ext hc), by
            simpa using congrArg Subtype.val (hCData.2 c.1)⟩⟩
        left_inv := by
          intro x
          apply Subtype.ext
          rfl
        right_inv := by
          intro c
          apply Subtype.ext
          apply Subtype.ext
          rfl }
    have hinvolution_card :
        Nat.card {x : Q // x ∈ involutions Q} = 2 ^ nC - 1 := by
      calc
        Nat.card {x : Q // x ∈ involutions Q} =
            Nat.card {c : C // c ≠ 1} := Nat.card_congr involEquivC
        _ = Nat.card C - 1 := by
          let : Fintype C := Fintype.ofFinite C
          rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
          simp
        _ = 2 ^ nC - 1 := by rw [hC_card]
    obtain ⟨x0, _y0, hx0, _hy0, _hxy0⟩ := hQ.2.2.1
    let orbitC : X → {x : Q // x ∈ involutions Q} :=
      fun k => ⟨k • x0, hXregular.1 x0 hx0 k⟩
    have horbitC_injective : Function.Injective orbitC := by
      intro k l hkl
      have heq : k • x0 = l • x0 := congrArg Subtype.val hkl
      rcases hXregular.2 x0 hx0 (k • x0)
          (hXregular.1 x0 hx0 k) with ⟨a, _ha, huniq⟩
      exact (huniq k rfl).trans (huniq l heq).symm
    have horbitC_surjective : Function.Surjective orbitC := by
      rintro ⟨y, hy⟩
      rcases hXregular.2 x0 hx0 y hy with ⟨k, hk, _huniq⟩
      exact ⟨k, Subtype.ext hk.symm⟩
    let : Finite X := Finite.of_injective orbitC horbitC_injective
    let : Fintype X := Fintype.ofFinite X
    have hX_card : Nat.card X =
        Nat.card {x : Q // x ∈ involutions Q} :=
      Nat.card_congr (Equiv.ofBijective orbitC
        ⟨horbitC_injective, horbitC_surjective⟩)
    have hX_odd : Odd (Fintype.card X) := by
      rw [← Nat.card_eq_fintype_card, hX_card, hinvolution_card]
      obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnC
      refine ⟨2 ^ e - 1, ?_⟩
      rw [pow_succ]
      have he_pos : 0 < 2 ^ e := by positivity
      omega
    let : IsInvariant X Q (frattini Q) := ⟨by
      have hPhiX' := hPhiX
      change ∀ x : X, ∀ a : Q, a ∈ PhiTop ↔ x • a ∈ PhiTop at hPhiX'
      simpa only [hPhiTop_eq] using hPhiX'⟩
    let : MulAction.QuotientAction X (frattini Q) :=
      quotientAction_of_isInvariant (A := X) (G := Q) (frattini Q)
        inferInstance
    let : MulDistribMulAction X (Q ⧸ frattini Q) :=
      quotientMulDistribMulAction (A := X) (G := Q) (frattini Q)
        inferInstance
    let : IsElementaryAbelian 2 (Q ⧸ frattini Q) :=
      isElementaryAbelian_quotient_frattini (R := Q) (p := 2)
    let : CommGroup (Q ⧸ frattini Q) := IsMulCommutative.instCommGroup
    let AQ : Subgroup (Q ⧸ frattini Q) :=
      A.map (QuotientGroup.mk' (frattini Q))
    let : IsInvariant X Q A := ⟨hupper.2.2.2.2.1⟩
    let : IsInvariant X (Q ⧸ frattini Q) AQ := by
      dsimp [AQ]
      exact isInvariant_map_quotient A
    obtain ⟨WQ, hAQWQ, hWQ_forward⟩ :=
      exists_isCompl_invariant_subgroup_of_odd_group hX_odd AQ (by
        intro k q hq
        exact (IsInvariant.invariant (A := X) (G := Q ⧸ frattini Q)
          (H := AQ) k q).1 hq)
    let : IsInvariant X (Q ⧸ frattini Q) WQ := by
      refine ⟨?_⟩
      intro k q
      constructor
      · exact hWQ_forward k q
      · intro hq
        have hback := hWQ_forward k⁻¹ (k • q) hq
        simpa [smul_smul] using hback
    let Xlift : Subgroup Q :=
      AQ.comap (QuotientGroup.mk' (frattini Q))
    let Ylift : Subgroup Q :=
      WQ.comap (QuotientGroup.mk' (frattini Q))
    have hXlift_eq_A : Xlift = A := by
      dsimp [Xlift, AQ]
      rw [QuotientGroup.comap_map_mk']
      exact sup_eq_right.mpr (by simpa [← hPhiTop_eq] using hPhi_le_A)
    let : WQ.Normal := by infer_instance
    have hYlift_normal : Ylift.Normal := by
      dsimp [Ylift]
      infer_instance
    have hYlift_X : IsXInvariantSubgroup X Ylift := by
      dsimp [Ylift]
      exact (isInvariant_comap_quotient WQ (by
        intro k q
        simp)).invariant
    have hAQ_inf_WQ : AQ ⊓ WQ = ⊥ := disjoint_iff.mp hAQWQ.1
    have hAQ_sup_WQ : AQ ⊔ WQ = ⊤ := codisjoint_iff.mp hAQWQ.2
    have hXlift_inf_Ylift : Xlift ⊓ Ylift = PhiTop := by
      dsimp [Xlift, Ylift]
      rw [← Subgroup.comap_inf AQ WQ
        (QuotientGroup.mk' (frattini Q)), hAQ_inf_WQ]
      simp [hPhiTop_eq]
    have hXlift_sup_Ylift : Xlift ⊔ Ylift = ⊤ := by
      dsimp [Xlift, Ylift]
      rw [Subgroup.comap_sup_eq (QuotientGroup.mk' (frattini Q)) AQ WQ
        (QuotientGroup.mk'_surjective (frattini Q)), hAQ_sup_WQ]
      simp
    by_cases hPhiExpTwo : ∀ x : PhiTop, x ^ 2 = 1
    · have hPhi_eq_C : PhiTop = C := by
        apply le_antisymm
        · intro x hx
          by_cases hx_one : x = 1
          · subst x
            exact C.one_mem
          · apply hAllInvC x
            refine ⟨hx_one, ?_⟩
            let xPhi : PhiTop := ⟨x, hx⟩
            simpa [xPhi] using congrArg Subtype.val (hPhiExpTwo xPhi)
        · exact hC_le_Phi
      let QuotientIrreducible (U : Subgroup (Q ⧸ frattini Q)) : Prop :=
        ∀ L : Subgroup (Q ⧸ frattini Q),
          IsInvariant X (Q ⧸ frattini Q) L → L ≤ U → L = ⊥ ∨ L = U
      have hExponentTwoQuotientSplit :
          ∃ UQ VQ WQ'': Subgroup (Q ⧸ frattini Q),
            IsInvariant X (Q ⧸ frattini Q) UQ ∧
            IsInvariant X (Q ⧸ frattini Q) VQ ∧
            IsInvariant X (Q ⧸ frattini Q) WQ'' ∧
            UQ ⊓ VQ = ⊥ ∧ UQ ⊔ VQ = AQ ∧
            AQ ⊓ WQ'' = ⊥ ∧ AQ ⊔ WQ'' = ⊤ ∧
            QuotientIrreducible UQ ∧ QuotientIrreducible VQ ∧
              QuotientIrreducible WQ'' ∧ UQ ≠ ⊥ ∧ VQ ≠ ⊥ ∧ WQ'' ≠ ⊥ := by
        let BQ : Subgroup (Q ⧸ frattini Q) :=
          B.map (QuotientGroup.mk' (frattini Q))
        let : IsInvariant X Q B := ⟨hmiddle.2.2.2.2.1⟩
        let : IsInvariant X (Q ⧸ frattini Q) BQ := by
          dsimp [BQ]
          exact isInvariant_map_quotient B
        have hBQ_le_AQ : BQ ≤ AQ := by
          dsimp [BQ, AQ]
          exact Subgroup.map_mono hmiddle.1.le
        obtain ⟨VQ, hVQ_le_AQ, hVQ_forward,
            hBQ_inf_VQ, hBQ_sup_VQ⟩ :=
          exists_isCompl_invariant_subgroup_within hX_odd AQ BQ hBQ_le_AQ
            (by
              intro k q hq
              exact (IsInvariant.invariant (A := X) (G := Q ⧸ frattini Q)
                (H := AQ) k q).1 hq)
            (by
              intro k q hq
              exact (IsInvariant.invariant (A := X) (G := Q ⧸ frattini Q)
                (H := BQ) k q).1 hq)
        have hVQ_invariant : IsInvariant X (Q ⧸ frattini Q) VQ := ⟨by
          intro k q
          constructor
          · exact hVQ_forward k q
          · intro hq
            have hback := hVQ_forward k⁻¹ (k • q) hq
            simpa [smul_smul] using hback⟩
        have hBQ_inf_WQ : BQ ⊓ WQ = ⊥ := by
          apply le_antisymm
          · calc
              BQ ⊓ WQ ≤ AQ ⊓ WQ := inf_le_inf hBQ_le_AQ le_rfl
              _ = ⊥ := hAQ_inf_WQ
          · exact bot_le
        have hVQ_inf_WQ : VQ ⊓ WQ = ⊥ := by
          apply le_antisymm
          · calc
              VQ ⊓ WQ ≤ AQ ⊓ WQ := inf_le_inf hVQ_le_AQ le_rfl
              _ = ⊥ := hAQ_inf_WQ
          · exact bot_le
        have hfrattini_eq_C : frattini Q = C :=
          hPhiTop_eq.symm.trans hPhi_eq_C
        have hBQ_comap :
            BQ.comap (QuotientGroup.mk' (frattini Q)) = B := by
          dsimp [BQ]
          rw [QuotientGroup.comap_map_mk']
          exact sup_eq_right.mpr (by
            simpa [hfrattini_eq_C] using hlower.1.le)
        have hBQ_irreducible : QuotientIrreducible BQ := by
          intro L hLinv hLBQ
          let D : Subgroup Q :=
            L.comap (QuotientGroup.mk' (frattini Q))
          have hDnormal : D.Normal := by
            dsimp [D]
            infer_instance
          let : IsInvariant X (Q ⧸ frattini Q) L := hLinv
          have hDX : IsXInvariantSubgroup X D := by
            dsimp [D]
            exact (isInvariant_comap_quotient L (by
              intro k q
              simp)).invariant
          have hC_D : C ≤ D := by
            intro c hc
            change QuotientGroup.mk' (frattini Q) c ∈ L
            have hcfr : c ∈ frattini Q := by simpa [hfrattini_eq_C] using hc
            have hmk : QuotientGroup.mk' (frattini Q) c = 1 :=
              (QuotientGroup.eq_one_iff c).mpr hcfr
            rw [hmk]
            exact L.one_mem
          have hD_B : D ≤ B := by
            change L.comap (QuotientGroup.mk' (frattini Q)) ≤ B
            rw [← hBQ_comap]
            exact Subgroup.comap_mono hLBQ
          have hmapD : D.map (QuotientGroup.mk' (frattini Q)) = L := by
            dsimp [D]
            exact Subgroup.map_comap_eq_self_of_surjective
              (QuotientGroup.mk'_surjective (frattini Q)) L
          rcases hlower.2.2.2.2.2 D hDnormal hDX hC_D hD_B with
            hDC | hDB
          · left
            rw [← hmapD, hDC]
            apply le_antisymm
            · rintro _ ⟨c, hc, rfl⟩
              apply Subgroup.mem_bot.mpr
              exact (QuotientGroup.eq_one_iff c).mpr (by
                simpa [hfrattini_eq_C] using hc)
            · exact bot_le
          · right
            rw [← hmapD, hDB]
        have hVQ_irreducible : QuotientIrreducible VQ := by
          intro L hLinv hLVQ
          let D : Subgroup Q :=
            (BQ ⊔ L).comap (QuotientGroup.mk' (frattini Q))
          have hDnormal : D.Normal := by
            dsimp [D]
            infer_instance
          let : IsInvariant X (Q ⧸ frattini Q) L := hLinv
          let : IsInvariant X (Q ⧸ frattini Q) (BQ ⊔ L) :=
            isInvariant_sup BQ L
          have hDX : IsXInvariantSubgroup X D := by
            dsimp [D]
            exact (isInvariant_comap_quotient (BQ ⊔ L) (by
              intro k q
              simp)).invariant
          have hB_D : B ≤ D := by
            rw [← hBQ_comap]
            exact Subgroup.comap_mono le_sup_left
          have hD_A : D ≤ A := by
            change (BQ ⊔ L).comap (QuotientGroup.mk' (frattini Q)) ≤ A
            rw [← hXlift_eq_A]
            exact Subgroup.comap_mono
              (sup_le hBQ_le_AQ (hLVQ.trans hVQ_le_AQ))
          have hmapD :
              D.map (QuotientGroup.mk' (frattini Q)) = BQ ⊔ L := by
            dsimp [D]
            exact Subgroup.map_comap_eq_self_of_surjective
              (QuotientGroup.mk'_surjective (frattini Q)) (BQ ⊔ L)
          rcases hmiddle.2.2.2.2.2 D hDnormal hDX hB_D hD_A with
            hDB | hDA
          · left
            have hsup_eq_BQ : BQ ⊔ L = BQ := by
              rw [← hmapD, hDB]
            have hL_BQ : L ≤ BQ :=
              le_sup_right.trans (le_of_eq hsup_eq_BQ)
            have hL_bot : L ≤ (⊥ : Subgroup (Q ⧸ frattini Q)) := by
              calc
                L ≤ BQ ⊓ VQ := le_inf hL_BQ hLVQ
                _ = ⊥ := hBQ_inf_VQ
            exact le_antisymm hL_bot bot_le
          · right
            have hsup_eq_AQ : BQ ⊔ L = AQ := by
              rw [← hmapD, hDA]
            apply le_antisymm hLVQ
            intro v hvV
            have hvSup : v ∈ BQ ⊔ L := by
              rw [hsup_eq_AQ]
              exact hVQ_le_AQ hvV
            rcases (Subgroup.mem_sup_of_normal_left
                (s := BQ) (t := L)).mp hvSup with
              ⟨b, hbBQ, l, hlL, hbl⟩
            have hlV : l ∈ VQ := hLVQ hlL
            have hbV : b ∈ VQ := by
              have hb_eq : b = v * l⁻¹ := by
                calc
                  b = b * l * l⁻¹ := by simp
                  _ = v * l⁻¹ := by rw [hbl]
              rw [hb_eq]
              exact VQ.mul_mem hvV (VQ.inv_mem hlV)
            have hbBot : b ∈ (⊥ : Subgroup (Q ⧸ frattini Q)) := by
              rw [← hBQ_inf_VQ]
              exact ⟨hbBQ, hbV⟩
            have hbOne : b = 1 := Subgroup.mem_bot.mp hbBot
            have hv_eq_l : v = l := by
              rw [← hbl, hbOne, one_mul]
            rw [hv_eq_l]
            exact hlL
        have hWQ_irreducible : QuotientIrreducible WQ := by
          intro L hLinv hLWQ
          let D : Subgroup Q :=
            (AQ ⊔ L).comap (QuotientGroup.mk' (frattini Q))
          have hDnormal : D.Normal := by
            dsimp [D]
            infer_instance
          let : IsInvariant X (Q ⧸ frattini Q) L := hLinv
          let : IsInvariant X (Q ⧸ frattini Q) (AQ ⊔ L) :=
            isInvariant_sup AQ L
          have hDX : IsXInvariantSubgroup X D := by
            dsimp [D]
            exact (isInvariant_comap_quotient (AQ ⊔ L) (by
              intro k q
              simp)).invariant
          have hA_D : A ≤ D := by
            rw [← hXlift_eq_A]
            exact Subgroup.comap_mono le_sup_left
          have hD_top : D ≤ (⊤ : Subgroup Q) := le_top
          have hmapD :
              D.map (QuotientGroup.mk' (frattini Q)) = AQ ⊔ L := by
            dsimp [D]
            exact Subgroup.map_comap_eq_self_of_surjective
              (QuotientGroup.mk'_surjective (frattini Q)) (AQ ⊔ L)
          rcases hupper.2.2.2.2.2 D hDnormal hDX hA_D hD_top with
            hDA | hDtop
          · left
            have hsup_eq_AQ : AQ ⊔ L = AQ := by
              rw [← hmapD, hDA]
            have hL_AQ : L ≤ AQ :=
              le_sup_right.trans (le_of_eq hsup_eq_AQ)
            have hL_bot : L ≤ (⊥ : Subgroup (Q ⧸ frattini Q)) := by
              calc
                L ≤ AQ ⊓ WQ := le_inf hL_AQ hLWQ
                _ = ⊥ := hAQ_inf_WQ
            exact le_antisymm hL_bot bot_le
          · right
            have hsup_eq_top : AQ ⊔ L = ⊤ := by
              rw [← hmapD, hDtop,
                Subgroup.map_top_of_surjective
                  (QuotientGroup.mk' (frattini Q))
                  (QuotientGroup.mk'_surjective (frattini Q))]
            apply le_antisymm hLWQ
            intro w hwW
            have hwSup : w ∈ AQ ⊔ L := by rw [hsup_eq_top]; trivial
            rcases (Subgroup.mem_sup_of_normal_left
                (s := AQ) (t := L)).mp hwSup with
              ⟨a, haAQ, l, hlL, hal⟩
            have hlW : l ∈ WQ := hLWQ hlL
            have haW : a ∈ WQ := by
              have ha_eq : a = w * l⁻¹ := by
                calc
                  a = a * l * l⁻¹ := by simp
                  _ = w * l⁻¹ := by rw [hal]
              rw [ha_eq]
              exact WQ.mul_mem hwW (WQ.inv_mem hlW)
            have haBot : a ∈ (⊥ : Subgroup (Q ⧸ frattini Q)) := by
              rw [← hAQ_inf_WQ]
              exact ⟨haAQ, haW⟩
            have haOne : a = 1 := Subgroup.mem_bot.mp haBot
            have hw_eq_l : w = l := by
              rw [← hal, haOne, one_mul]
            rw [hw_eq_l]
            exact hlL
        have hBQ_ne : BQ ≠ ⊥ := by
          intro hBQ_bot
          have hBC : B = C := by
            calc
              B = BQ.comap (QuotientGroup.mk' (frattini Q)) := hBQ_comap.symm
              _ = (⊥ : Subgroup (Q ⧸ frattini Q)).comap
                    (QuotientGroup.mk' (frattini Q)) := by rw [hBQ_bot]
              _ = frattini Q := by simp
              _ = C := hfrattini_eq_C
          exact hlower.1.ne hBC.symm
        have hVQ_ne : VQ ≠ ⊥ := by
          intro hVQ_bot
          have hBQ_eq_AQ : BQ = AQ := by
            simpa [hVQ_bot] using hBQ_sup_VQ
          have hBA : B = A := by
            calc
              B = BQ.comap (QuotientGroup.mk' (frattini Q)) := hBQ_comap.symm
              _ = AQ.comap (QuotientGroup.mk' (frattini Q)) := by rw [hBQ_eq_AQ]
              _ = A := hXlift_eq_A
          exact hmiddle.1.ne hBA
        have hWQ_ne : WQ ≠ ⊥ := by
          intro hWQ_bot
          have hAQ_top : AQ = ⊤ := by
            simpa [hWQ_bot] using hAQ_sup_WQ
          have hAtop : A = ⊤ := by
            calc
              A = AQ.comap (QuotientGroup.mk' (frattini Q)) := hXlift_eq_A.symm
              _ = (⊤ : Subgroup (Q ⧸ frattini Q)).comap
                    (QuotientGroup.mk' (frattini Q)) := by rw [hAQ_top]
              _ = ⊤ := by simp
          exact hupper.1.ne hAtop
        exact ⟨BQ, VQ, WQ, inferInstance, hVQ_invariant, inferInstance,
          hBQ_inf_VQ, hBQ_sup_VQ, hAQ_inf_WQ, hAQ_sup_WQ,
          hBQ_irreducible, hVQ_irreducible, hWQ_irreducible,
          hBQ_ne, hVQ_ne, hWQ_ne⟩
      have hexponentTwoCase : False := by
        rcases hExponentTwoQuotientSplit with
          ⟨UQ, VQ, WQ'', hUQinv, hVQinv, hWQinv, hUQinfVQ,
            hUQsupVQ, hAQinfWQ, hAQsupWQ, hUQirr, hVQirr, hWQirr,
            hUQ_ne, hVQ_ne, hWQ_ne⟩
        have hfrattini_eq_C : frattini Q = C :=
          hPhiTop_eq.symm.trans hPhi_eq_C
        have hcomm_le_C : commutator Q ≤ C := by
          calc
            commutator Q ≤ frattini Q :=
              commutator_le_frattini_of_isPGroup (R := Q) (p := 2)
            _ = C := hfrattini_eq_C
        have hcomm_ne_bot : commutator Q ≠ ⊥ := by
          intro hcomm_bot
          apply hQ.2.1
          have hcenter_top : Subgroup.center Q = ⊤ :=
            (commutator_eq_bot_iff_center_eq_top Q).mp hcomm_bot
          let : CommGroup Q := Group.commGroupOfCenterEqTop hcenter_top
          exact IsMulCommutative.mk <| Std.Commutative.mk <| fun x y => mul_comm x y
        have hcomm_X : IsXInvariantSubgroup X (commutator Q) :=
          (isInvariant_of_characteristic (A := X) (G := Q)
            (commutator Q)).invariant
        have hcommutator_eq_C : commutator Q = C := by
          rcases hbottom.2.2.2.2.2 (commutator Q) inferInstance hcomm_X
              bot_le hcomm_le_C with hbot | hC
          · exact False.elim (hcomm_ne_bot hbot)
          · exact hC
        have hL1_eq_C : (⊤ : Subgroup Q).lowerCentralSeries 1 = C := by
          rw [Subgroup.top_lowerCentralSeries_one]
          exact hcommutator_eq_C
        have hclass_two : (⊤ : Subgroup Q).lowerCentralSeries 2 = ⊥ := by
          have hL2_normal : ((⊤ : Subgroup Q).lowerCentralSeries 2).Normal := by infer_instance
          have hL2_X : IsXInvariantSubgroup X ((⊤ : Subgroup Q).lowerCentralSeries 2) :=
            (isInvariant_of_characteristic (A := X) (G := Q)
              ((⊤ : Subgroup Q).lowerCentralSeries 2)).invariant
          have hL2_le_C : (⊤ : Subgroup Q).lowerCentralSeries 2 ≤ C := by
            calc
              (⊤ : Subgroup Q).lowerCentralSeries 2 ≤ (⊤ : Subgroup Q).lowerCentralSeries 1 :=
                (⊤ : Subgroup Q).lowerCentralSeries_antitone (by omega)
              _ = C := hL1_eq_C
          rcases hbottom.2.2.2.2.2 ((⊤ : Subgroup Q).lowerCentralSeries 2)
              hL2_normal hL2_X bot_le hL2_le_C with hbot | hC
          · exact hbot
          · exfalso
            have hstable : ∀ n : ℕ, 1 ≤ n → (⊤ : Subgroup Q).lowerCentralSeries n = C := by
              intro n hn
              obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
              induction k with
              | zero => simpa using hL1_eq_C
              | succ k ih =>
                  change ⁅(⊤ : Subgroup Q).lowerCentralSeries (1 + k), (⊤ : Subgroup Q)⁆ = C
                  rw [ih (by omega)]
                  calc
                    ⁅C, (⊤ : Subgroup Q)⁆ =
                        ⁅(⊤ : Subgroup Q).lowerCentralSeries 1, (⊤ : Subgroup Q)⁆ := by
                          rw [hL1_eq_C]
                    _ = (⊤ : Subgroup Q).lowerCentralSeries 2 := rfl
                    _ = C := hC
            let : Group.IsNilpotent Q :=
              IsPGroup.isNilpotent (isPGroup_of_isSuzukiTwoGroup hQ)
            let c := Group.nilpotencyClass Q
            have hc_pos : 0 < c := by
              apply Nat.pos_of_ne_zero
              intro hc
              have hsub : Subsingleton Q :=
                (Group.nilpotencyClass_zero_iff_subsingleton (G := Q)).mp hc
              rcases hQ.2.2.1 with ⟨x, y, _hx, _hy, hxy⟩
              exact hxy (hsub.elim x y)
            have hcC : (⊤ : Subgroup Q).lowerCentralSeries c = C := hstable c (by omega)
            have hcbot : (⊤ : Subgroup Q).lowerCentralSeries c = ⊥ := by
              dsimp [c]
              exact Subgroup.lowerCentralSeries_nilpotencyClass
            exact hbottom.1.ne (hcC.symm.trans hcbot).symm
        have hC_le_center : C ≤ Subgroup.center Q := by
          rw [← hcommutator_eq_C]
          have hclass := hclass_two
          rw [show 2 = 1 + 1 by omega, Subgroup.lowerCentralSeries_succ,
            Subgroup.top_lowerCentralSeries_one] at hclass
          change ⁅commutator Q, (⊤ : Subgroup Q)⁆ = ⊥ at hclass
          rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hclass
          simpa [← Subgroup.centralizer_univ, ← Subgroup.coe_top] using hclass
        have hsquares_le_C : squaresSubgroup Q ≤ C := by
          rw [squaresSubgroup, Subgroup.closure_le]
          rintro _ ⟨y, rfl⟩
          rw [← hfrattini_eq_C]
          exact pth_power_mem_frattini_of_isPGroup (R := Q) (p := 2) y
        have hkernel1_bot : lowerCentralFactorKernel Q 1 = ⊥ := by
          apply le_antisymm
          · rw [lowerCentralFactorKernel]
            apply sup_le
            · rw [squaresSubgroup, Subgroup.closure_le]
              rintro _ ⟨x, rfl⟩
              change x ^ 2 = 1
              apply Subtype.ext
              change (x : Q) ^ 2 = 1
              let c : C := ⟨x, hL1_eq_C ▸ x.property⟩
              simpa [c] using congrArg Subtype.val (hCData.2 c)
            · intro x hx
              change (x : Q) ∈ (⊤ : Subgroup Q).lowerCentralSeries 2 at hx
              rw [hclass_two] at hx
              simpa using hx
          · exact bot_le
        have hkernel0_map_C :
            (lowerCentralFactorKernel Q 0).map
                ((⊤ : Subgroup Q).lowerCentralSeries 0).subtype = C := by
          have hsquares_map :
              (squaresSubgroup ((⊤ : Subgroup Q).lowerCentralSeries 0)).map
                  ((⊤ : Subgroup Q).lowerCentralSeries 0).subtype = squaresSubgroup Q := by
            apply le_antisymm
            · rw [squaresSubgroup, MonoidHom.map_closure, Subgroup.closure_le]
              rintro _ ⟨x, ⟨y, rfl⟩, rfl⟩
              exact Subgroup.subset_closure ⟨(y : Q), rfl⟩
            · rw [squaresSubgroup, Subgroup.closure_le]
              rintro _ ⟨y, rfl⟩
              let yt : (⊤ : Subgroup Q).lowerCentralSeries 0 := ⟨y, trivial⟩
              exact ⟨yt ^ 2, Subgroup.subset_closure ⟨yt, rfl⟩, rfl⟩
          have hnext_map :
              (((⊤ : Subgroup Q).lowerCentralSeries 1).subgroupOf
                  ((⊤ : Subgroup Q).lowerCentralSeries 0)).map
                    ((⊤ : Subgroup Q).lowerCentralSeries 0).subtype = (⊤ : Subgroup Q).lowerCentralSeries 1 :=
            Subgroup.map_subgroupOf_eq_of_le
              ((⊤ : Subgroup Q).lowerCentralSeries_antitone
                (by omega : 0 ≤ 1))
          rw [lowerCentralFactorKernel, Subgroup.map_sup, hsquares_map,
            hnext_map, hL1_eq_C]
          exact sup_eq_right.mpr (by simpa [hL1_eq_C] using hsquares_le_C)
        have hnC_two : 2 ≤ nC := by
          let oneC : C := ⟨1, C.one_mem⟩
          let xC : C := ⟨x0, hAllInvC x0 hx0⟩
          let yC : C := ⟨_y0, hAllInvC _y0 _hy0⟩
          have hx_ne : oneC ≠ xC := by
            intro h
            exact hx0.ne_one (congrArg Subtype.val h).symm
          have hy_ne : oneC ≠ yC := by
            intro h
            exact _hy0.ne_one (congrArg Subtype.val h).symm
          have hxy_ne : xC ≠ yC := by
            intro h
            exact _hxy0 (congrArg Subtype.val h)
          let : Fintype C := Fintype.ofFinite C
          have hthree : ({oneC, xC, yC} : Finset C).card = 3 := by
            rw [Finset.card_insert_of_notMem (by simp [hx_ne, hy_ne])]
            rw [Finset.card_insert_of_notMem (by simp [hxy_ne])]
            simp
          have hle : 3 ≤ Nat.card C := by
            rw [Nat.card_eq_fintype_card, ← hthree]
            exact Finset.card_le_card (Finset.subset_univ _)
          rw [hC_card] at hle
          by_contra hn
          have hnle : nC ≤ 1 := by omega
          interval_cases nC <;> norm_num at hle
        let q0 : Q →* LowerCentralFactor Q 0 :=
          (QuotientGroup.mk' (lowerCentralFactorKernel Q 0)).comp
            Subgroup.topEquiv.symm.toMonoidHom
        have hq0_ker : q0.ker = frattini Q := by
          ext p
          change QuotientGroup.mk' (lowerCentralFactorKernel Q 0)
              (Subgroup.topEquiv.symm p) = 1 ↔ p ∈ frattini Q
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          constructor
          · intro hp
            rw [hfrattini_eq_C]
            rw [← hkernel0_map_C]
            exact ⟨Subgroup.topEquiv.symm p, hp, rfl⟩
          · intro hp
            have hpmap : p ∈
                (lowerCentralFactorKernel Q 0).map
                  ((⊤ : Subgroup Q).lowerCentralSeries 0).subtype := by
              rw [hkernel0_map_C]
              rwa [← hfrattini_eq_C]
            rcases hpmap with ⟨z, hz, hzp⟩
            have hz_eq : z = Subgroup.topEquiv.symm p := by
              apply Subtype.ext
              exact hzp
            exact hz_eq ▸ hz
        have hq0_surj : Function.Surjective q0 := by
          intro v
          obtain ⟨z, rfl⟩ :=
            QuotientGroup.mk'_surjective (lowerCentralFactorKernel Q 0) v
          refine ⟨Subgroup.topEquiv z, ?_⟩
          exact congrArg (QuotientGroup.mk' (lowerCentralFactorKernel Q 0))
            (Subgroup.topEquiv.symm_apply_apply z)
        let : FaithfulSMul X Q := hXfaithful
        let : IsCyclic X := hXcyclic
        obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := X)
        let tau : MulAut Q := MulDistribMulAction.toMulAut X Q g
        obtain ⟨bracket, _bracketK, squareMap, _hbracketK_tmul,
            hbracket_equivariant, hbracket_self, hbracket_mk,
            _hbracket_span, hsquare_mk, hsquare_equivariant, hsquare_add⟩ :=
          lemma5_square_map_normal_form_quadratic_core
            tau nC (by
              change squaresSubgroup Q ≤
                (⊤ : Subgroup Q).lowerCentralSeries 1
              rw [hL1_eq_C]
              exact hsquares_le_C)
        have hsquare_anisotropic :
            ∀ v : Additive (LowerCentralFactor Q 0), squareMap v = 0 → v = 0 := by
          intro v hv
          obtain ⟨x, hx⟩ :=
            QuotientGroup.mk'_surjective (lowerCentralFactorKernel Q 0) v.toMul
          have hv_repr : v = Additive.ofMul
              (QuotientGroup.mk' (lowerCentralFactorKernel Q 0) x) := by
            apply Additive.toMul.injective
            exact hx.symm
          have hxsquare_mem : (x : Q) ^ 2 ∈ (⊤ : Subgroup Q).lowerCentralSeries 1 := by
            rw [hL1_eq_C]
            exact hsquares_le_C (Subgroup.subset_closure ⟨(x : Q), rfl⟩)
          have hmk_zero :
              Additive.ofMul
                  (QuotientGroup.mk' (lowerCentralFactorKernel Q 1)
                    ⟨(x : Q) ^ 2, hxsquare_mem⟩) = 0 := by
            rw [← hsquare_mk x hxsquare_mem, ← hv_repr]
            exact hv
          have hmk_one :
              QuotientGroup.mk' (lowerCentralFactorKernel Q 1)
                  ⟨(x : Q) ^ 2, hxsquare_mem⟩ = 1 := by
            apply Additive.ofMul.injective
            simpa using hmk_zero
          have hsqker :
              (⟨(x : Q) ^ 2, hxsquare_mem⟩ : (⊤ : Subgroup Q).lowerCentralSeries 1) ∈
                lowerCentralFactorKernel Q 1 :=
            (QuotientGroup.eq_one_iff
              (N := lowerCentralFactorKernel Q 1)
              (⟨(x : Q) ^ 2, hxsquare_mem⟩ : (⊤ : Subgroup Q).lowerCentralSeries 1)).mp hmk_one
          rw [hkernel1_bot] at hsqker
          have hxsquare : (x : Q) ^ 2 = 1 := by
            have hsquare_one :
                (⟨(x : Q) ^ 2, hxsquare_mem⟩ : (⊤ : Subgroup Q).lowerCentralSeries 1) = 1 := by
              simpa using hsqker
            exact congrArg Subtype.val hsquare_one
          by_cases hxone : (x : Q) = 1
          · apply Additive.toMul.injective
            change v.toMul = 1
            rw [← hx]
            have xone : x = 1 := Subtype.ext hxone
            rw [xone]
            exact map_one _
          · have hxC : (x : Q) ∈ C := hAllInvC (x : Q) ⟨hxone, hxsquare⟩
            have hxmap : (x : Q) ∈
                (lowerCentralFactorKernel Q 0).map
                  ((⊤ : Subgroup Q).lowerCentralSeries 0).subtype := by
              rw [hkernel0_map_C]
              exact hxC
            rcases hxmap with ⟨z, hz, hzx⟩
            have hzx' : z = x := by
              apply Subtype.ext
              exact hzx
            have hxker : x ∈ lowerCentralFactorKernel Q 0 := hzx' ▸ hz
            have hxquot :
                QuotientGroup.mk' (lowerCentralFactorKernel Q 0) x = 1 :=
              (QuotientGroup.eq_one_iff
                (N := lowerCentralFactorKernel Q 0) x).mpr hxker
            apply Additive.toMul.injective
            change v.toMul = 1
            rw [← hx]
            exact hxquot
        let e0 : Q ⧸ frattini Q ≃* LowerCentralFactor Q 0 :=

          (QuotientGroup.quotientMulEquivOfEq hq0_ker.symm).trans
            (QuotientGroup.quotientKerEquivOfSurjective q0 hq0_surj)
        have he0_mk (x : Q) :
            e0 (QuotientGroup.mk' (frattini Q) x) = q0 x := by
          change QuotientGroup.kerLift q0
              (QuotientGroup.quotientMulEquivOfEq hq0_ker.symm
                (QuotientGroup.mk' (frattini Q) x)) = q0 x
          have hm :
              QuotientGroup.quotientMulEquivOfEq hq0_ker.symm
                  (QuotientGroup.mk' (frattini Q) x) =
                QuotientGroup.mk' q0.ker x :=
            QuotientGroup.quotientMulEquivOfEq_mk hq0_ker.symm x
          rw [hm]
          change QuotientGroup.kerLift q0
              (x : Q ⧸ q0.ker) = q0 x
          exact QuotientGroup.kerLift_mk q0 x
        have he0_equivariant (x : Q ⧸ frattini Q) :
            Additive.ofMul (e0 (g • x)) =
              lowerCentralFactorLinearAut tau 0 (Additive.ofMul (e0 x)) := by
          obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (frattini Q) x
          have hsmul :
              g • QuotientGroup.mk' (frattini Q) y =
                QuotientGroup.mk' (frattini Q) (g • y) :=
            MulAction.Quotient.smul_mk (H := frattini Q) g y
          rw [hsmul, he0_mk, he0_mk]
          change Additive.ofMul
              (QuotientGroup.mk' (lowerCentralFactorKernel Q 0)
                (Subgroup.topEquiv.symm (g • y))) =
            lowerCentralFactorLinearAut tau 0
              (Additive.ofMul
                (QuotientGroup.mk' (lowerCentralFactorKernel Q 0)
                  (Subgroup.topEquiv.symm y)))
          rw [lowerCentralFactorLinearAut_ofMul_mk]
          apply Additive.ofMul.injective
          apply congrArg (QuotientGroup.mk' (lowerCentralFactorKernel Q 0))
          apply Subtype.ext
          rfl
        have hfactor1_card : Nat.card (LowerCentralFactor Q 1) = 2 ^ nC := by
          calc
            Nat.card (LowerCentralFactor Q 1) =
                Nat.card ((⊤ : Subgroup Q).lowerCentralSeries 1) :=
              Nat.card_congr
                (((QuotientGroup.quotientMulEquivOfEq hkernel1_bot).trans
                  (QuotientGroup.quotientBot
                    (G := (⊤ : Subgroup Q).lowerCentralSeries 1))).toEquiv)
            _ = Nat.card C := by rw [hL1_eq_C]
            _ = 2 ^ nC := hC_card
        have hS_transitive :
            ∀ x : Additive (LowerCentralFactor Q 1), x ≠ 0 →
              ∀ y : Additive (LowerCentralFactor Q 1), y ≠ 0 →
                ∃ j : ℕ, (lowerCentralFactorLinearAut tau 1 ^ j) x = y := by
          intro x hx y hy
          obtain ⟨a, ha⟩ :=
            QuotientGroup.mk'_surjective (lowerCentralFactorKernel Q 1) x.toMul
          obtain ⟨b, hb⟩ :=
            QuotientGroup.mk'_surjective (lowerCentralFactorKernel Q 1) y.toMul
          have ha_ne : (a : Q) ≠ 1 := by
            intro ha1
            apply hx
            apply Additive.toMul.injective
            change x.toMul = 1
            rw [← ha]
            have ha_one : a = 1 := Subtype.ext ha1
            rw [ha_one]
            exact map_one _
          have hb_ne : (b : Q) ≠ 1 := by
            intro hb1
            apply hy
            apply Additive.toMul.injective
            change y.toMul = 1
            rw [← hb]
            have hb_one : b = 1 := Subtype.ext hb1
            rw [hb_one]
            exact map_one _
          let aC : C := ⟨a, hL1_eq_C ▸ a.property⟩
          let bC : C := ⟨b, hL1_eq_C ▸ b.property⟩
          have ha_sq : (a : Q) ^ 2 = 1 := by
            simpa [aC] using congrArg Subtype.val (hCData.2 aC)
          have hb_sq : (b : Q) ^ 2 = 1 := by
            simpa [bC] using congrArg Subtype.val (hCData.2 bC)
          obtain ⟨z, hz⟩ :=
            hXtrans (a : Q) ⟨ha_ne, ha_sq⟩ (b : Q) ⟨hb_ne, hb_sq⟩
          obtain ⟨j, rfl⟩ := mem_powers_iff_mem_zpowers.mpr (hg z)
          refine ⟨j, ?_⟩
          have hx_repr : x =
              Additive.ofMul
                (QuotientGroup.mk' (lowerCentralFactorKernel Q 1) a) := by
            apply Additive.toMul.injective
            exact ha.symm
          have hy_repr : y =
              Additive.ofMul
                (QuotientGroup.mk' (lowerCentralFactorKernel Q 1) b) := by
            apply Additive.toMul.injective
            exact hb.symm
          rw [← lowerCentralFactorLinearAut_pow, hx_repr, hy_repr,
            lowerCentralFactorLinearAut_ofMul_mk]
          apply Additive.toMul.injective
          apply congrArg (QuotientGroup.mk' (lowerCentralFactorKernel Q 1))
          apply Subtype.ext
          change (tau ^ j) (a : Q) = (b : Q)
          have hpow_aut :
              tau ^ j = MulDistribMulAction.toMulAut X Q (g ^ j) := by
            change (MulDistribMulAction.toMulAut X Q g) ^ j =
              MulDistribMulAction.toMulAut X Q (g ^ j)
            exact (map_pow (MulDistribMulAction.toMulAut X Q) g j).symm
          rw [hpow_aut]
          exact hz.symm
        have hfactor1_nontrivial : Nontrivial (LowerCentralFactor Q 1) :=
          Finite.one_lt_card_iff_nontrivial.mp (by
            rw [hfactor1_card]
            have : 1 < 2 ^ nC := by
              exact one_lt_pow₀ (by omega) hnC
            exact this)
        let : Nontrivial (LowerCentralFactor Q 1) := hfactor1_nontrivial
        have hLayerCard :
            ∀ (U : Subgroup (Q ⧸ frattini Q)),
              IsInvariant X (Q ⧸ frattini Q) U →
              QuotientIrreducible U → U ≠ ⊥ →
              Nat.card U = 2 ^ nC := by
          intro U hUinv hUirr hU_ne
          let : IsInvariant X (Q ⧸ frattini Q) U := hUinv
          let : Nontrivial U := (Subgroup.nontrivial_iff_ne_bot U).mpr hU_ne
          let : IsElementaryAbelian 2 U := by
            refine
              { toIsMulCommutative := inferInstance
                exponent_dvd_p :=
                  Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_ }
            intro u
            apply Subtype.ext
            exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
              (IsElementaryAbelian.exponent_dvd_p 2 (Q ⧸ frattini Q)) u
          let rhoU :=
            Theory.Representation.ofElementaryAbelianAction (A := X) (G := U) (p := 2)
          let rhoEquiv : X →* (Additive U ≃ₗ[ZMod 2] Additive U) :=
            (LinearMap.GeneralLinearGroup.generalLinearEquiv
              (ZMod 2) (Additive U)).toMonoidHom.comp rhoU.asGroupHom
          let T : Additive U ≃ₗ[ZMod 2] Additive U := rhoEquiv g
          let S := lowerCentralFactorLinearAut tau 1
          have hT_val (v : Additive U) :
              T v = Additive.ofMul (g • v.toMul) := by
            change rhoU g v = Additive.ofMul (g • v.toMul)
            exact Theory.Representation.ofElementaryAbelianAction_apply g v
          have hT_pow_val :
              ∀ j : ℕ, ∀ v : Additive U,
                (T ^ j) v = Additive.ofMul (g ^ j • v.toMul) := by
            intro j
            induction j with
            | zero => intro v; simp
            | succ j ih =>
                intro v
                rw [show T ^ (j + 1) = T * T ^ j by rw [pow_succ'],
                  LinearEquiv.mul_apply, hT_val, ih]
                simp [pow_succ', smul_smul]
          have hT_irreducible :
              ∀ W : Submodule (ZMod 2) (Additive U),
                (∀ v : Additive U, v ∈ W → T v ∈ W) →
                W = ⊥ ∨ W = ⊤ := by
            intro W hW
            let eU : Subgroup U ≃o Submodule (ZMod 2) (Additive U) :=
              Subgroup.toAddSubgroup.trans
                (AddSubgroup.toZModSubmodule (n := 2))
            let L0 : Subgroup U := eU.symm W
            let L : Subgroup (Q ⧸ frattini Q) := L0.map U.subtype
            have hW_pow :
                ∀ j : ℕ, ∀ v : Additive U, v ∈ W → (T ^ j) v ∈ W := by
              intro j
              induction j with
              | zero => intro v hv; simpa using hv
              | succ j ih =>
                  intro v hv
                  rw [show T ^ (j + 1) = T * T ^ j by rw [pow_succ'],
                    LinearEquiv.mul_apply]
                  exact hW _ (ih v hv)
            have hL_le_U : L ≤ U := by
              rintro _ ⟨u, _hu, rfl⟩
              exact u.property
            have hL_forward :
                ∀ k : X, ∀ x : Q ⧸ frattini Q, x ∈ L → k • x ∈ L := by
              intro k x hx
              rcases hx with ⟨u, hu, rfl⟩
              obtain ⟨j, rfl⟩ := mem_powers_iff_mem_zpowers.mpr (hg k)
              have huW : Additive.ofMul u ∈ W := by
                change Additive.ofMul u ∈ eU (eU.symm W) at hu
                simpa only [eU.apply_symm_apply] using hu
              have hpowW :
                  Additive.ofMul (g ^ j • u) ∈ W := by
                have hmem := hW_pow j (Additive.ofMul u) huW
                rw [hT_pow_val] at hmem
                simpa using hmem
              let gu : U := ⟨g ^ j • (u : Q ⧸ frattini Q),
                (IsInvariant.invariant (A := X) (G := Q ⧸ frattini Q)
                  (H := U) (g ^ j) u).1 u.property⟩
              have hgu : gu ∈ L0 := by
                have hgu_eq : gu = g ^ j • u := by
                  apply Subtype.ext
                  rfl
                change Additive.ofMul gu ∈ eU (eU.symm W)
                rw [hgu_eq]
                simpa only [eU.apply_symm_apply] using hpowW
              exact ⟨gu, hgu, rfl⟩
            have hLinv : IsInvariant X (Q ⧸ frattini Q) L := by
              refine ⟨?_⟩
              intro k x
              constructor
              · exact hL_forward k x
              · intro hx
                have hback := hL_forward k⁻¹ (k • x) hx
                simpa [smul_smul] using hback
            rcases hUirr L hLinv hL_le_U with hLbot | hLtop
            · left
              have hL0bot : L0 = ⊥ := by
                apply Subgroup.map_injective U.subtype_injective
                simpa [L] using hLbot
              calc
                W = eU L0 := by simp [L0]
                _ = eU ⊥ := congrArg eU hL0bot
                _ = ⊥ := eU.map_bot
            · right
              have hL0top : L0 = ⊤ := by
                have hmap_top : (⊤ : Subgroup U).map U.subtype = U := by
                  simpa [MonoidHom.range_eq_map] using
                    (Subgroup.range_subtype (H := U))
                apply Subgroup.map_injective U.subtype_injective
                calc
                  L0.map U.subtype = U := hLtop
                  _ = (⊤ : Subgroup U).map U.subtype := hmap_top.symm
              calc
                W = eU L0 := by simp [L0]
                _ = eU ⊤ := congrArg eU hL0top
                _ = ⊤ := eU.map_top
          let q : Additive U → Additive (LowerCentralFactor Q 1) :=
            fun v => squareMap
              (Additive.ofMul (e0 (v.toMul : Q ⧸ frattini Q)))
          have hq_equivariant (v : Additive U) : q (T v) = S (q v) := by
            rw [hT_val]
            change squareMap
                (Additive.ofMul (e0 (g • (v.toMul : Q ⧸ frattini Q)))) =
              lowerCentralFactorLinearAut tau 1
                (squareMap
                  (Additive.ofMul (e0 (v.toMul : Q ⧸ frattini Q))))
            rw [he0_equivariant, hsquare_equivariant]
          have hq_nonzero : ∃ v : Additive U, q v ≠ 0 := by
            obtain ⟨u, hu⟩ := exists_ne (1 : U)
            refine ⟨Additive.ofMul u, ?_⟩
            intro hzero
            apply hu
            apply Subtype.ext
            apply e0.injective
            apply Additive.ofMul.injective
            exact hsquare_anisotropic _ hzero
          have hmap : orderOf T ∣ orderOf g := by
            simpa [T] using orderOf_map_dvd rhoEquiv g
          have hgcard : orderOf g ∣ Nat.card X := orderOf_dvd_natCard g
          have hT_order_dvd : orderOf T ∣ 2 ^ nC - 1 := by
            rw [← hinvolution_card, ← hX_card]
            exact hmap.trans hgcard
          have hfinrank :
              Module.finrank (ZMod 2) (Additive U) = nC :=
            lemma13_irreducible_actor_layer_finrank_eq T S hT_irreducible
              hS_transitive nC hnC_two hfactor1_card q hq_equivariant
              hq_nonzero hT_order_dvd
          have hcard := Module.natCard_eq_pow_finrank
            (K := ZMod 2) (V := Additive U)
          exact (Nat.card_congr Additive.toMul).symm.trans
            (by simpa [hfinrank] using hcard)
        have hUQ_card : Nat.card UQ = 2 ^ nC :=
          hLayerCard UQ hUQinv hUQirr hUQ_ne
        have hVQ_card : Nat.card VQ = 2 ^ nC :=
          hLayerCard VQ hVQinv hVQirr hVQ_ne
        have hWQ_card : Nat.card WQ'' = 2 ^ nC :=
          hLayerCard WQ'' hWQinv hWQirr hWQ_ne
        have hUQ_le_AQ : UQ ≤ AQ := by
          rw [← hUQsupVQ]
          exact le_sup_left
        have hVQ_le_AQ : VQ ≤ AQ := by
          rw [← hUQsupVQ]
          exact le_sup_right
        let UQA : Subgroup AQ := UQ.subgroupOf AQ
        let VQA : Subgroup AQ := VQ.subgroupOf AQ
        have hUVA_isCompl : IsCompl UQA VQA := by
          constructor
          · rw [disjoint_iff]
            apply le_antisymm
            · intro x hx
              have hx' : (x : Q ⧸ frattini Q) ∈ UQ ⊓ VQ :=
                ⟨hx.1, hx.2⟩
              rw [hUQinfVQ] at hx'
              simpa using hx'
            · exact bot_le
          · rw [codisjoint_iff, ← Subgroup.subgroupOf_sup hUQ_le_AQ hVQ_le_AQ,
              hUQsupVQ, Subgroup.subgroupOf_self]
        have hUVA_complement : UQA.IsComplement' VQA := by
          apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
            hUVA_isCompl.disjoint
          rw [← Subgroup.coe_mul_of_left_le_normalizer_right UQA VQA
            Subgroup.le_normalizer_of_normal,
            hUVA_isCompl.codisjoint.eq_top]
          rfl
        have hAQ_card : Nat.card AQ = 2 ^ (2 * nC) := by
          have hcard := hUVA_complement.card_mul_card
          have hUQA_card : Nat.card UQA = Nat.card UQ :=
            Nat.card_congr
              (Subgroup.subgroupOfEquivOfLe (H := UQ) (K := AQ)
                hUQ_le_AQ).toEquiv
          have hVQA_card : Nat.card VQA = Nat.card VQ :=
            Nat.card_congr
              (Subgroup.subgroupOfEquivOfLe (H := VQ) (K := AQ)
                hVQ_le_AQ).toEquiv
          rw [hUQA_card, hVQA_card, hUQ_card, hVQ_card] at hcard
          calc
            Nat.card AQ = 2 ^ nC * 2 ^ nC := hcard.symm
            _ = 2 ^ (nC + nC) := by rw [pow_add]
            _ = 2 ^ (2 * nC) :=
              congrArg (fun k : ℕ => 2 ^ k) (by omega)
        have hAQW_isCompl : IsCompl AQ WQ'' := by
          constructor
          · rw [disjoint_iff, hAQinfWQ]
          · rw [codisjoint_iff, hAQsupWQ]
        have hAQW_complement : AQ.IsComplement' WQ'' := by
          apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
            hAQW_isCompl.disjoint
          rw [← Subgroup.coe_mul_of_left_le_normalizer_right AQ WQ''
            Subgroup.le_normalizer_of_normal,
            hAQW_isCompl.codisjoint.eq_top]
          rfl
        have hquotient_card :
            Nat.card (Q ⧸ frattini Q) = 2 ^ (3 * nC) := by
          have hcard := hAQW_complement.card_mul_card
          rw [hAQ_card, hWQ_card] at hcard
          calc
            Nat.card (Q ⧸ frattini Q) = 2 ^ (2 * nC) * 2 ^ nC :=
              hcard.symm
            _ = 2 ^ (2 * nC + nC) := by rw [pow_add]
            _ = 2 ^ (3 * nC) :=
              congrArg (fun k : ℕ => 2 ^ k) (by omega)
        have hfactor0_card :
            Nat.card (LowerCentralFactor Q 0) = 2 ^ (3 * nC) := by
          calc
            Nat.card (LowerCentralFactor Q 0) =
                Nat.card (Q ⧸ frattini Q) := Nat.card_congr e0.symm.toEquiv
            _ = 2 ^ (3 * nC) := hquotient_card
        have finrank_eq_of_card
            (V : Type u) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
            (d : ℕ) (hcard : Nat.card V = 2 ^ d) :
            Module.finrank (ZMod 2) V = d := by
          let : Module.Finite (ZMod 2) V := Module.Finite.of_finite
          have h := Module.natCard_eq_pow_finrank
            (K := ZMod 2) (V := V)
          have hpow : 2 ^ Module.finrank (ZMod 2) V = 2 ^ d := by
            calc
              2 ^ Module.finrank (ZMod 2) V = Nat.card V := by
                simpa using h.symm
              _ = 2 ^ d := hcard
          exact Nat.pow_right_injective (a := 2) (by omega) hpow
        have hfactor0_finrank :
            Module.finrank (ZMod 2) (Additive (LowerCentralFactor Q 0)) =
              3 * nC :=
          finrank_eq_of_card (Additive (LowerCentralFactor Q 0))
            (3 * nC) ((Nat.card_congr Additive.toMul).trans hfactor0_card)
        have hfactor1_finrank :
            Module.finrank (ZMod 2) (Additive (LowerCentralFactor Q 1)) =
              nC :=
          finrank_eq_of_card (Additive (LowerCentralFactor Q 1)) nC
            ((Nat.card_congr Additive.toMul).trans hfactor1_card)
        have hsquare_zero : squareMap 0 = 0 := by
          simpa using hsquare_add 0 0
        have hdim :
            2 * Module.finrank (ZMod 2)
                (Additive (LowerCentralFactor Q 1)) <
              Module.finrank (ZMod 2)
                (Additive (LowerCentralFactor Q 0)) := by
          rw [hfactor0_finrank, hfactor1_finrank]
          omega
        obtain ⟨v, hv, hvzero⟩ := lemma10_exists_nonzero_quadratic_zero
          (Additive (LowerCentralFactor Q 0))
          (Additive (LowerCentralFactor Q 1)) squareMap bracket
          hsquare_zero hsquare_add hbracket_self hdim
        exact hv (hsquare_anisotropic v hvzero)
      exact hexponentTwoCase
    · have hPhiOrderFour : ∃ x : PhiTop, x ^ 2 ≠ 1 ∧ x ^ 4 = 1 := by
        push Not at hPhiExpTwo
        rcases hPhiExpTwo with ⟨x, hx⟩
        exact ⟨x, hx, hPhiData.2 x⟩
      let PhiSq : Subgroup Q :=
        (squaresSubgroup PhiTop).map PhiTop.subtype
      have hPhiSq_normal : PhiSq.Normal := by
        let : PhiTop.Normal := hPhiNormal
        dsimp [PhiSq]
        infer_instance
      have hPhiSq_X : IsXInvariantSubgroup X PhiSq := by
        let : IsInvariant X Q PhiTop := ⟨hPhiX⟩
        have hforward : ∀ k : X, ∀ p : Q, p ∈ PhiSq → k • p ∈ PhiSq := by
          intro k p hp
          rcases hp with ⟨z, hz, rfl⟩
          refine ⟨k • z, ?_, rfl⟩
          exact
            (Subgroup.characteristic_iff_le_comap.mp
              (squaresSubgroupCharacteristic PhiTop)
              (MulDistribMulAction.toMulAut X PhiTop k)) hz
        intro k p
        constructor
        · exact hforward k p
        · intro hp
          have hpinv := hforward k⁻¹ (k • p) hp
          simpa [smul_smul] using hpinv
      have hPhiSq_le_C : PhiSq ≤ C := by
        have hsquares_le : squaresSubgroup PhiTop ≤ C.comap PhiTop.subtype := by
          rw [squaresSubgroup, Subgroup.closure_le]
          rintro _ ⟨x, rfl⟩
          change (x : Q) ^ 2 ∈ C
          by_cases hx_sq : (x : Q) ^ 2 = 1
          · rw [hx_sq]
            exact C.one_mem
          · apply hAllInvC ((x : Q) ^ 2)
            refine ⟨hx_sq, ?_⟩
            calc
              ((x : Q) ^ 2) ^ 2 = (x : Q) ^ (2 * 2) := by
                rw [pow_mul]
              _ = (x : Q) ^ 4 := by norm_num
              _ = 1 := by
                simpa using congrArg Subtype.val (hPhiData.2 x)
        rintro _ ⟨z, hz, rfl⟩
        exact hsquares_le hz
      have hPhiSq_ne : PhiSq ≠ ⊥ := by
        rcases hPhiOrderFour with ⟨x, hx_sq, _hx_four⟩
        intro hbot
        have hx_mem : ((x : Q) ^ 2) ∈ PhiSq := by
          refine ⟨x ^ 2, ?_, ?_⟩
          · exact Subgroup.subset_closure ⟨x, rfl⟩
          · rfl
        rw [hbot] at hx_mem
        apply hx_sq
        apply Subtype.ext
        simpa using hx_mem
      have hPhiSq_eq_C : PhiSq = C := by
        rcases hbottom.2.2.2.2.2 PhiSq hPhiSq_normal hPhiSq_X
            bot_le hPhiSq_le_C with hbot | hC
        · exact False.elim (hPhiSq_ne hbot)
        · exact hC
      have hA_ne_Phi : A ≠ PhiTop := by
        intro hA_eq
        have hBA_Phi : B < PhiTop := hA_eq ▸ hmiddle.1
        exact lemma13_no_four_step_abelian_exponent_four
          (A := PhiTop) (B := B) (C := C) hQ hXtrans
          hPhiData.1 hPhiX hPhiData.2 hBA_Phi hlower.1 hbottom.1
          hmiddle.2.2.2.2.1 hlower.2.2.2.2.1
      have hPhi_ne_C : PhiTop ≠ C := by
        intro hPhi_eq_C
        rcases hPhiOrderFour with ⟨x, hx_sq, _hx_four⟩
        have hxC : (x : Q) ∈ C := by
          rw [← hPhi_eq_C]
          exact x.property
        let xC : C := ⟨x, hxC⟩
        apply hx_sq
        apply Subtype.ext
        simpa [xC] using congrArg Subtype.val (hCData.2 xC)
      have hC_min_X :
          ∀ L : Subgroup Q, IsXInvariantSubgroup X L → L ≤ C →
            L = ⊥ ∨ L = C := by
        intro L hLX hLC
        by_cases hL_bot : L = ⊥
        · exact Or.inl hL_bot
        right
        apply le_antisymm hLC
        let : Nontrivial L :=
          (Subgroup.nontrivial_iff_ne_bot L).mpr hL_bot
        obtain ⟨lL, hlL_one⟩ := exists_ne (1 : L)
        have hl_one : (lL : Q) ≠ 1 := by
          intro hl
          exact hlL_one (Subtype.ext hl)
        have hlC : (lL : Q) ∈ C := hLC lL.property
        have hl_inv : IsInvolution (lL : Q) := by
          refine ⟨hl_one, ?_⟩
          let lC : C := ⟨lL, hlC⟩
          simpa [lC] using congrArg Subtype.val (hCData.2 lC)
        intro c hcC
        by_cases hc_one : c = 1
        · subst c
          exact L.one_mem
        have hc_inv : IsInvolution c := by
          refine ⟨hc_one, ?_⟩
          let cC : C := ⟨c, hcC⟩
          simpa [cC] using congrArg Subtype.val (hCData.2 cC)
        rcases hXtrans (lL : Q) hl_inv c hc_inv with ⟨k, hk⟩
        rw [hk]
        exact (hLX k (lL : Q)).mp lL.property
      have hC_cover_Phi :
          ∀ L : Subgroup Q, IsXInvariantSubgroup X L →
            C ≤ L → L ≤ PhiTop → L = C ∨ L = PhiTop := by
        intro L hLX hCL hLPhi
        by_cases hL_C : L = C
        · exact Or.inl hL_C
        by_cases hL_Phi : L = PhiTop
        · exact Or.inr hL_Phi
        have hC_lt_L : C < L := lt_of_le_of_ne hCL (Ne.symm hL_C)
        have hL_lt_Phi : L < PhiTop := lt_of_le_of_ne hLPhi hL_Phi
        exact False.elim (lemma13_no_four_step_abelian_exponent_four
          (A := PhiTop) (B := L) (C := C) hQ hXtrans
          hPhiData.1 hPhiX hPhiData.2 hL_lt_Phi hC_lt_L hbottom.1
          hLX hbottom.2.2.2.1)
      have hPhi_cover_A :
          ∀ L : Subgroup Q, L.Normal → IsXInvariantSubgroup X L →
            PhiTop ≤ L → L ≤ A → L = PhiTop ∨ L = A := by
        intro L hLnormal hLX hPhiL hLA
        by_cases hPhiB : PhiTop ≤ B
        · have hPhi_eq_B : PhiTop = B := by
            rcases hlower.2.2.2.2.2 PhiTop hPhiNormal hPhiX
                hC_le_Phi hPhiB with hPhi_eq_C | hPhi_eq_B
            · exact False.elim (hPhi_ne_C hPhi_eq_C)
            · exact hPhi_eq_B
          rcases hmiddle.2.2.2.2.2 L hLnormal hLX
              (hPhi_eq_B ▸ hPhiL) hLA with hL_eq_B | hL_eq_A
          · exact Or.inl (hL_eq_B.trans hPhi_eq_B.symm)
          · exact Or.inr hL_eq_A
        · have hB_sup_Phi_normal : (B ⊔ PhiTop).Normal := by
            let : B.Normal := hmiddle.2.2.1
            let : PhiTop.Normal := hPhiNormal
            infer_instance
          have hB_sup_Phi_X : IsXInvariantSubgroup X (B ⊔ PhiTop) := by
            let : IsInvariant X Q B := ⟨hmiddle.2.2.2.2.1⟩
            let : IsInvariant X Q PhiTop := ⟨hPhiX⟩
            exact (isInvariant_sup B PhiTop).invariant
          have hB_sup_Phi_eq_A : B ⊔ PhiTop = A := by
            rcases hmiddle.2.2.2.2.2 (B ⊔ PhiTop)
                hB_sup_Phi_normal hB_sup_Phi_X le_sup_left
                (sup_le hmiddle.1.le hPhi_le_A) with hsup_eq_B | hsup_eq_A
            · exact False.elim (hPhiB
                (le_sup_right.trans (le_of_eq hsup_eq_B)))
            · exact hsup_eq_A
          have hB_inf_Phi_normal : (B ⊓ PhiTop).Normal := by
            let : B.Normal := hmiddle.2.2.1
            let : PhiTop.Normal := hPhiNormal
            infer_instance
          have hB_inf_Phi_X : IsXInvariantSubgroup X (B ⊓ PhiTop) := by
            let : IsInvariant X Q B := ⟨hmiddle.2.2.2.2.1⟩
            let : IsInvariant X Q PhiTop := ⟨hPhiX⟩
            exact (isInvariant_inf B PhiTop).invariant
          have hB_inf_Phi_eq_C : B ⊓ PhiTop = C := by
            rcases hlower.2.2.2.2.2 (B ⊓ PhiTop)
                hB_inf_Phi_normal hB_inf_Phi_X
                (le_inf hlower.1.le hC_le_Phi) inf_le_left with
              hinf_eq_C | hinf_eq_B
            · exact hinf_eq_C
            · have hB_le_Phi : B ≤ PhiTop := by
                rw [← hinf_eq_B]
                exact inf_le_right
              have hPhi_eq_A : PhiTop = A := by
                apply le_antisymm hPhi_le_A
                rw [← hB_sup_Phi_eq_A]
                exact sup_le hB_le_Phi le_rfl
              exact False.elim (hA_ne_Phi hPhi_eq_A.symm)
          have hB_inf_L_normal : (B ⊓ L).Normal := by
            let : B.Normal := hmiddle.2.2.1
            let : L.Normal := hLnormal
            infer_instance
          have hB_inf_L_X : IsXInvariantSubgroup X (B ⊓ L) := by
            let : IsInvariant X Q B := ⟨hmiddle.2.2.2.2.1⟩
            let : IsInvariant X Q L := ⟨hLX⟩
            exact (isInvariant_inf B L).invariant
          rcases hlower.2.2.2.2.2 (B ⊓ L)
              hB_inf_L_normal hB_inf_L_X
              (le_inf hlower.1.le (hC_le_Phi.trans hPhiL))
              inf_le_left with hinf_eq_C | hinf_eq_B
          · left
            apply le_antisymm
            · intro x hxL
              have hxSup : x ∈ B ⊔ PhiTop := by
                rw [hB_sup_Phi_eq_A]
                exact hLA hxL
              let : B.Normal := hmiddle.2.2.1
              rcases (Subgroup.mem_sup_of_normal_left
                  (s := B) (t := PhiTop)).mp hxSup with
                ⟨b, hbB, p, hpPhi, hbp⟩
              have hpL : p ∈ L := hPhiL hpPhi
              have hbL : b ∈ L := by
                have hb_eq : b = x * p⁻¹ := by
                  calc
                    b = b * p * p⁻¹ := by simp
                    _ = x * p⁻¹ := by rw [hbp]
                rw [hb_eq]
                exact L.mul_mem hxL (L.inv_mem hpL)
              have hbC : b ∈ C := by
                rw [← hinf_eq_C]
                exact ⟨hbB, hbL⟩
              rw [← hbp]
              exact PhiTop.mul_mem (hC_le_Phi hbC) hpPhi
            · exact hPhiL
          · right
            apply le_antisymm hLA
            rw [← hB_sup_Phi_eq_A]
            exact sup_le (by
              rw [← hinf_eq_B]
              exact inf_le_right) hPhiL
      have hPhi_lt_A : PhiTop < A :=
        lt_of_le_of_ne hPhi_le_A (Ne.symm hA_ne_Phi)
      have hC_lt_Phi : C < PhiTop :=
        lt_of_le_of_ne hC_le_Phi (Ne.symm hPhi_ne_C)
      have hPhi_le_Ylift : PhiTop ≤ Ylift := by
        rw [← hXlift_inf_Ylift]
        exact inf_le_right
      have hYlift_ne_Phi : Ylift ≠ PhiTop := by
        intro hY_eq
        have hsup := hXlift_sup_Ylift
        rw [hXlift_eq_A, hY_eq, sup_eq_left.mpr hPhi_le_A] at hsup
        exact hupper.1.ne hsup
      have hPhi_lt_Ylift : PhiTop < Ylift :=
        lt_of_le_of_ne hPhi_le_Ylift (Ne.symm hYlift_ne_Phi)
      have hYlift_lt_top : Ylift < (⊤ : Subgroup Q) := by
        apply lt_top_iff_ne_top.mpr
        intro hY_top
        have hA_eq_Phi : A = PhiTop := by
          simpa [hXlift_eq_A, hY_top] using hXlift_inf_Ylift
        exact hA_ne_Phi hA_eq_Phi
      have hA_sup_Ylift : A ⊔ Ylift = (⊤ : Subgroup Q) := by
        simpa [hXlift_eq_A] using hXlift_sup_Ylift
      have hYlift_cover_top :
          ∀ L : Subgroup Q, L.Normal → IsXInvariantSubgroup X L →
            Ylift ≤ L → L ≤ ⊤ → L = Ylift ∨ L = ⊤ := by
        intro L hLnormal hLX hYL _hLtop
        have hA_inf_L_normal : (A ⊓ L).Normal := by
          let : A.Normal := hupper.2.2.1
          let : L.Normal := hLnormal
          infer_instance
        have hA_inf_L_X : IsXInvariantSubgroup X (A ⊓ L) := by
          let : IsInvariant X Q A := ⟨hupper.2.2.2.2.1⟩
          let : IsInvariant X Q L := ⟨hLX⟩
          exact (isInvariant_inf A L).invariant
        rcases hPhi_cover_A (A ⊓ L) hA_inf_L_normal hA_inf_L_X
            (le_inf hPhi_le_A (hPhi_le_Ylift.trans hYL)) inf_le_left with
          hinf_eq_Phi | hinf_eq_A
        · left
          apply le_antisymm
          · intro x hxL
            have hxSup : x ∈ A ⊔ Ylift := by
              rw [hA_sup_Ylift]
              trivial
            let : A.Normal := hupper.2.2.1
            rcases (Subgroup.mem_sup_of_normal_left
                (s := A) (t := Ylift)).mp hxSup with
              ⟨a, haA, y, hyY, hay⟩
            have hyL : y ∈ L := hYL hyY
            have haL : a ∈ L := by
              have ha_eq : a = x * y⁻¹ := by
                calc
                  a = a * y * y⁻¹ := by simp
                  _ = x * y⁻¹ := by rw [hay]
              rw [ha_eq]
              exact L.mul_mem hxL (L.inv_mem hyL)
            have haPhi : a ∈ PhiTop := by
              rw [← hinf_eq_Phi]
              exact ⟨haA, haL⟩
            rw [← hay]
            exact Ylift.mul_mem (hPhi_le_Ylift haPhi) hyY
          · exact hYL
        · right
          apply top_unique
          rw [← hA_sup_Ylift]
          exact sup_le (by
            rw [← hinf_eq_A]
            exact inf_le_right) hYL
      have hA_noncomm : ¬ IsMulCommutative A := by
        intro hAcomm
        have hAmax : ∀ M : Subgroup Q, M.Normal → IsMulCommutative M →
            IsXInvariantSubgroup X M → A < M → False := by
          intro M hMnormal hMcomm hMX hAM
          rcases hupper.2.2.2.2.2 M hMnormal hMX hAM.le le_top with
            hM_A | hM_top
          · exact (ne_of_gt hAM) hM_A
          · apply hQ.2.1
            let : IsMulCommutative M := hMcomm
            refine IsMulCommutative.mk <| Std.Commutative.mk <| fun x y => ?_
            let mx : M := ⟨x, by rw [hM_top]; trivial⟩
            let my : M := ⟨y, by rw [hM_top]; trivial⟩
            simpa [mx, my] using congrArg Subtype.val (mul_comm mx my)
        have hAexp : ∀ x : A, x ^ 4 = 1 :=
          (lemma9_maximal_abelian_contains_frattini hQ hXcyclic hXfaithful
            hXtrans hupper.2.2.1 hAcomm hupper.2.2.2.2.1 hAmax).1
        exact lemma13_no_four_step_abelian_exponent_four
          (A := A) (B := B) (C := C) hQ hXtrans hAcomm
          hupper.2.2.2.2.1 hAexp hmiddle.1 hlower.1 hbottom.1
          hmiddle.2.2.2.2.1 hlower.2.2.2.2.1
      have hYlift_noncomm : ¬ IsMulCommutative Ylift := by
        intro hYcomm
        have hYmax : ∀ M : Subgroup Q, M.Normal → IsMulCommutative M →
            IsXInvariantSubgroup X M → Ylift < M → False := by
          intro M hMnormal hMcomm hMX hYM
          rcases hYlift_cover_top M hMnormal hMX hYM.le le_top with
            hM_Y | hM_top
          · exact (ne_of_gt hYM) hM_Y
          · apply hQ.2.1
            let : IsMulCommutative M := hMcomm
            refine IsMulCommutative.mk <| Std.Commutative.mk <| fun x y => ?_
            let mx : M := ⟨x, by rw [hM_top]; trivial⟩
            let my : M := ⟨y, by rw [hM_top]; trivial⟩
            simpa [mx, my] using congrArg Subtype.val (mul_comm mx my)
        have hYexp : ∀ x : Ylift, x ^ 4 = 1 :=
          (lemma9_maximal_abelian_contains_frattini hQ hXcyclic hXfaithful
            hXtrans hYlift_normal hYcomm hYlift_X hYmax).1
        exact lemma13_no_four_step_abelian_exponent_four
          (A := Ylift) (B := PhiTop) (C := C) hQ hXtrans hYcomm
          hYlift_X hYexp hPhi_lt_Ylift hC_lt_Phi hbottom.1
          hPhiX hbottom.2.2.2.1
      have hC_le_center : C ≤ Subgroup.center Q := by
        let : C.Normal := hbottom.2.1
        let D : Subgroup Q := ⁅C, (⊤ : Subgroup Q)⁆
        have hD_le_C : D ≤ C := by
          simpa [D] using
            (Subgroup.commutator_le_left C (⊤ : Subgroup Q))
        have hD_normal : D.Normal := by
          have hnormal :
              (D.subgroupOf (C ⊔ (⊤ : Subgroup Q))).Normal := by
            simpa [D] using commutator_normal_in_sup C (⊤ : Subgroup Q)
          rw [sup_top_eq] at hnormal
          constructor
          intro d hd q
          let dTop : (⊤ : Subgroup Q) := ⟨d, trivial⟩
          let qTop : (⊤ : Subgroup Q) := ⟨q, trivial⟩
          have hconj := hnormal.conj_mem dTop hd qTop
          exact hconj
        have hD_X : IsXInvariantSubgroup X D := by
          let : IsInvariant X Q C := ⟨hbottom.2.2.2.1⟩
          let : IsInvariant X Q (⊤ : Subgroup Q) := ⟨by
            intro x q
            simp⟩
          exact (isInvariant_commutator C (⊤ : Subgroup Q)).invariant
        rcases hbottom.2.2.2.2.2 D hD_normal hD_X bot_le hD_le_C with
          hD_bot | hD_C
        · have hcentralizer :
              C ≤ Subgroup.centralizer (⊤ : Set Q) := by
            have hcomm_bot : ⁅C, (⊤ : Subgroup Q)⁆ = ⊥ := by
              simpa [D] using hD_bot
            change C ≤ Subgroup.centralizer
              (↑(⊤ : Subgroup Q) : Set Q)
            exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm_bot
          simpa [← Subgroup.centralizer_univ, ← Subgroup.coe_top] using
            hcentralizer
        · exfalso
          have hC_eq_comm : C = ⁅C, (⊤ : Subgroup Q)⁆ := by
            simpa [D] using hD_C.symm
          have hC_le_series : ∀ i : ℕ, C ≤ (⊤ : Subgroup Q).lowerCentralSeries i := by
            intro i
            induction i with
            | zero => simp
            | succ i ih =>
                rw [Subgroup.lowerCentralSeries_succ, hC_eq_comm]
                exact Subgroup.commutator_mono ih le_rfl
          let : Group.IsNilpotent Q :=
            IsPGroup.isNilpotent (isPGroup_of_isSuzukiTwoGroup hQ)
          have hnil : Group.IsNilpotent Q := inferInstance
          obtain ⟨i, hi⟩ :=
            Subgroup.nilpotent_iff_lowerCentralSeries.mp hnil
          have hC_bot : C ≤ (⊥ : Subgroup Q) := by
            rw [← hi]
            exact hC_le_series i
          exact hbottom.1.ne (bot_unique hC_bot).symm
      let : IsMulCommutative PhiTop := hPhiData.1
      let : IsInvariant X Q PhiTop := ⟨hPhiX⟩
      let : IsInvariant X Q C := ⟨hbottom.2.2.2.1⟩
      let squareToC : PhiTop →* C :=
        { toFun := fun x => ⟨(x : Q) ^ 2, by
            rw [← hPhiSq_eq_C]
            refine ⟨x ^ 2, ?_, rfl⟩
            exact Subgroup.subset_closure ⟨x, rfl⟩⟩
          map_one' := by
            apply Subtype.ext
            simp
          map_mul' := by
            intro x y
            apply Subtype.ext
            change ((x : Q) * (y : Q)) ^ 2 =
              (x : Q) ^ 2 * (y : Q) ^ 2
            exact congrArg Subtype.val (mul_pow x y 2) }
      have hsquareToC_ker : squareToC.ker = C.subgroupOf PhiTop := by
        ext x
        simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
        constructor
        · intro hx
          have hxQ : (x : Q) ^ 2 = 1 := by
            simpa [squareToC] using congrArg Subtype.val hx
          by_cases hx_one : (x : Q) = 1
          · simp [hx_one]
          · exact hAllInvC (x : Q) ⟨hx_one, hxQ⟩
        · intro hx
          let xC : C := ⟨x, hx⟩
          apply Subtype.ext
          simpa [squareToC, xC] using congrArg Subtype.val (hCData.2 xC)
      have hsquares_eq_range :
          squaresSubgroup PhiTop =
            (powMonoidHom 2 : PhiTop →* PhiTop).range := by
        apply le_antisymm
        · rw [squaresSubgroup, Subgroup.closure_le]
          rintro _ ⟨x, rfl⟩
          exact ⟨x, by simp [powMonoidHom]⟩
        · rintro _ ⟨x, rfl⟩
          exact Subgroup.subset_closure ⟨x, by simp [powMonoidHom]⟩
      have hsquareToC_surj : Function.Surjective squareToC := by
        intro c
        have hcPhiSq : (c : Q) ∈ PhiSq := by
          rw [hPhiSq_eq_C]
          exact c.property
        rcases hcPhiSq with ⟨z, hz, hzc⟩
        rw [hsquares_eq_range] at hz
        rcases hz with ⟨x, hx⟩
        refine ⟨x, ?_⟩
        apply Subtype.ext
        change (x : Q) ^ 2 = (c : Q)
        calc
          (x : Q) ^ 2 = (z : Q) := by
            simpa [powMonoidHom] using congrArg Subtype.val hx
          _ = (c : Q) := hzc
      let squareQuotientEquiv :
          PhiTop ⧸ C.subgroupOf PhiTop ≃* C :=
        (QuotientGroup.quotientMulEquivOfEq hsquareToC_ker.symm).trans
          (QuotientGroup.quotientKerEquivOfSurjective
            squareToC hsquareToC_surj)
      have hsquareQuotientEquiv_mk (p : PhiTop) :
          squareQuotientEquiv
              (QuotientGroup.mk' (C.subgroupOf PhiTop) p) =
            squareToC p := by
        change QuotientGroup.kerLift squareToC
            (QuotientGroup.quotientMulEquivOfEq hsquareToC_ker.symm
              (QuotientGroup.mk' (C.subgroupOf PhiTop) p)) =
          squareToC p
        have hm :
            QuotientGroup.quotientMulEquivOfEq hsquareToC_ker.symm
                (QuotientGroup.mk' (C.subgroupOf PhiTop) p) =
              QuotientGroup.mk' squareToC.ker p :=
          QuotientGroup.quotientMulEquivOfEq_mk hsquareToC_ker.symm p
        rw [hm]
        exact QuotientGroup.kerLift_mk squareToC p
      let : IsInvariant X PhiTop (C.subgroupOf PhiTop) :=
        isInvariant_subgroupOf C PhiTop
      let : MulAction.QuotientAction X (C.subgroupOf PhiTop) :=
        quotientAction_of_isInvariant (A := X) (G := PhiTop)
          (C.subgroupOf PhiTop) inferInstance
      have hsquareQuotientEquiv_equivariant
          (x : X) (p : PhiTop ⧸ C.subgroupOf PhiTop) :
          squareQuotientEquiv (x • p) = x • squareQuotientEquiv p := by
        obtain ⟨z, rfl⟩ :=
          QuotientGroup.mk'_surjective (C.subgroupOf PhiTop) p
        have hsmul :
            x • QuotientGroup.mk' (C.subgroupOf PhiTop) z =
              QuotientGroup.mk' (C.subgroupOf PhiTop) (x • z) :=
          MulAction.Quotient.smul_mk (H := C.subgroupOf PhiTop) x z
        rw [hsmul, hsquareQuotientEquiv_mk,
          hsquareQuotientEquiv_mk]
        apply Subtype.ext
        exact (smul_pow' x (z : Q) 2).symm
      have hNormal_of_Phi_le :
          ∀ L : Subgroup Q, PhiTop ≤ L → L.Normal := by
        intro L hPhiL
        let LQ : Subgroup (Q ⧸ frattini Q) :=
          L.map (QuotientGroup.mk' (frattini Q))
        let : LQ.Normal := by infer_instance
        have hcomap :
            LQ.comap (QuotientGroup.mk' (frattini Q)) = L := by
          dsimp [LQ]
          rw [QuotientGroup.comap_map_mk']
          exact sup_eq_right.mpr (by
            simpa [← hPhiTop_eq] using hPhiL)
        rw [← hcomap]
        infer_instance
      have hA_inf_Ylift : A ⊓ Ylift = PhiTop := by
        simpa [hXlift_eq_A] using hXlift_inf_Ylift
      have hPhi_cover_Ylift :
          ∀ L : Subgroup Q, L.Normal → IsXInvariantSubgroup X L →
            PhiTop ≤ L → L ≤ Ylift → L = PhiTop ∨ L = Ylift := by
        intro L hLnormal hLX hPhiL hLY
        have hA_sup_L_normal : (A ⊔ L).Normal := by
          let : A.Normal := hupper.2.2.1
          let : L.Normal := hLnormal
          infer_instance
        have hA_sup_L_X : IsXInvariantSubgroup X (A ⊔ L) := by
          let : IsInvariant X Q A := ⟨hupper.2.2.2.2.1⟩
          let : IsInvariant X Q L := ⟨hLX⟩
          exact (isInvariant_sup A L).invariant
        rcases hupper.2.2.2.2.2 (A ⊔ L) hA_sup_L_normal hA_sup_L_X
            le_sup_left le_top with hsup_eq_A | hsup_eq_top
        · left
          apply le_antisymm
          · rw [← hA_inf_Ylift]
            exact le_inf (le_sup_right.trans (le_of_eq hsup_eq_A)) hLY
          · exact hPhiL
        · right
          apply le_antisymm hLY
          intro y hyY
          have hySup : y ∈ A ⊔ L := by
            rw [hsup_eq_top]
            trivial
          let : A.Normal := hupper.2.2.1
          rcases (Subgroup.mem_sup_of_normal_left
              (s := A) (t := L)).mp hySup with
            ⟨a, haA, l, hlL, hal⟩
          have hlY : l ∈ Ylift := hLY hlL
          have haY : a ∈ Ylift := by
            have ha_eq : a = y * l⁻¹ := by
              calc
                a = a * l * l⁻¹ := by simp
                _ = y * l⁻¹ := by rw [hal]
            rw [ha_eq]
            exact Ylift.mul_mem hyY (Ylift.inv_mem hlY)
          have haPhi : a ∈ PhiTop := by
            rw [← hA_inf_Ylift]
            exact ⟨haA, haY⟩
          rw [← hal]
          exact L.mul_mem (hPhiL haPhi) hlL
      let : IsInvariant X Q PhiTop := ⟨hPhiX⟩
      let : IsInvariant X Q C := ⟨hbottom.2.2.2.1⟩
      let : IsInvariant X Q Ylift := ⟨hYlift_X⟩
      have hAChain : Lemma13ThreeChainData (X := X)
          (PhiTop.subgroupOf A) (C.subgroupOf A) :=
        lemma13_three_chain_data_of_ambient_chain
          (H := A) (Phi := PhiTop) (C := C)
          hPhi_lt_A hC_lt_Phi hbottom.1 hPhiNormal hbottom.2.1
          hNormal_of_Phi_le hPhi_cover_A hC_cover_Phi hC_min_X
      have hYliftChain : Lemma13ThreeChainData (X := X)
          (PhiTop.subgroupOf Ylift) (C.subgroupOf Ylift) :=
        lemma13_three_chain_data_of_ambient_chain
          (H := Ylift) (Phi := PhiTop) (C := C)
          hPhi_lt_Ylift hC_lt_Phi hbottom.1 hPhiNormal hbottom.2.1
          hNormal_of_Phi_le hPhi_cover_Ylift hC_cover_Phi hC_min_X
      have hLenA : OmegaLength X A 3 :=
        lemma13_omegaLength_three_of_ambient_chain
          (H := A) (Phi := PhiTop) (C := C)
          hPhi_lt_A hC_lt_Phi hbottom.1 hPhiNormal hbottom.2.1
          hNormal_of_Phi_le hPhi_cover_A hC_cover_Phi hC_min_X
      have hLenYlift : OmegaLength X Ylift 3 :=
        lemma13_omegaLength_three_of_ambient_chain
          (H := Ylift) (Phi := PhiTop) (C := C)
          hPhi_lt_Ylift hC_lt_Phi hbottom.1 hPhiNormal hbottom.2.1
          hNormal_of_Phi_le hPhi_cover_Ylift hC_cover_Phi hC_min_X
      have hAllInvA : ∀ a : Q, IsInvolution a → a ∈ A := by
        intro a ha
        exact hlower.1.le.trans hmiddle.1.le (hAllInvC a ha)
      have hAllInvYlift : ∀ a : Q, IsInvolution a → a ∈ Ylift := by
        intro a ha
        exact hPhi_le_Ylift (hC_le_Phi (hAllInvC a ha))
      rcases lemma13_subgroup_action_data hQ hXcyclic hXregular
          hXprimeSupport hA_noncomm hAllInvA with
        ⟨hASuzuki, hAfaithful, _hAregular, hAtrans, hAprimeSupport⟩
      rcases lemma13_subgroup_action_data hQ hXcyclic hXregular
          hXprimeSupport hYlift_noncomm hAllInvYlift with
        ⟨hYSuzuki, hYfaithful, _hYregular, hYtrans, hYprimeSupport⟩
      obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := X)
      have hPhiSubgroupOf_comm (H : Subgroup Q) :
          IsMulCommutative (PhiTop.subgroupOf H) := by
        refine IsMulCommutative.mk <| Std.Commutative.mk <| fun a b => ?_
        apply Subtype.ext
        apply Subtype.ext
        exact setLike_mul_comm
          (s := PhiTop) a.property b.property
      have hAResult :=
        lemma12_chain_typeBCD hASuzuki hXcyclic hAfaithful
          hAtrans hAprimeSupport g hg hAChain.1 hAChain.2.1 hAChain.2.2
      have hAType :
          IsSuzukiTwoTypeB (⊤ : Subgroup A) ∨
            IsSuzukiTwoTypeC (⊤ : Subgroup A) ∨
              IsSuzukiTwoTypeD (⊤ : Subgroup A) :=
        hAResult.1
      have hAActorData :
          Lemma12ChainActorData g (PhiTop.subgroupOf A)
            (C.subgroupOf A) :=
        hAResult.2.2.2 (hPhiSubgroupOf_comm A)
      have hYliftResult :=
        lemma12_chain_typeBCD hYSuzuki hXcyclic hYfaithful
          hYtrans hYprimeSupport g hg hYliftChain.1
          hYliftChain.2.1 hYliftChain.2.2
      have hYliftType :
          IsSuzukiTwoTypeB (⊤ : Subgroup Ylift) ∨
            IsSuzukiTwoTypeC (⊤ : Subgroup Ylift) ∨
              IsSuzukiTwoTypeD (⊤ : Subgroup Ylift) :=
        hYliftResult.1
      have hYliftActorData :
          Lemma12ChainActorData g (PhiTop.subgroupOf Ylift)
            (C.subgroupOf Ylift) :=
        hYliftResult.2.2.2 (hPhiSubgroupOf_comm Ylift)
      have hA_sq_bottom :=
        lemma13_square_mem_bottom_of_chain_actor_data g
          (PhiTop.subgroupOf A) (C.subgroupOf A) hAActorData
      have hYlift_sq_bottom :=
        lemma13_square_mem_bottom_of_chain_actor_data g
          (PhiTop.subgroupOf Ylift) (C.subgroupOf Ylift) hYliftActorData
      have hA_internal_comm :=
        lemma13_exists_nontrivial_middle_outer_commutator g
          (PhiTop.subgroupOf A) (C.subgroupOf A) hAActorData
      have hYlift_internal_comm :=
        lemma13_exists_nontrivial_middle_outer_commutator g
          (PhiTop.subgroupOf Ylift) (C.subgroupOf Ylift) hYliftActorData
      have hexponentFourCase : False := by
        unfold Lemma12ChainActorData at hAActorData hYliftActorData
        rcases hAActorData with
          ⟨kA, nA, xiA, qA, UA, VA, bracketA, squareA,
            hxiA, hnA, hqA_ker, hqA_surj, hqA_mk, hUA,
            hUVA, hL1A, hkernel1A, hbracketA, hsquareA, hformA⟩
        rcases hYliftActorData with
          ⟨kY, nY, xiY, qY, UY, VY, bracketY, squareY,
            hxiY, hnY, hqY_ker, hqY_surj, hqY_mk, hUY,
            hUVY, hL1Y, hkernel1Y, hbracketY, hsquareY, hformY⟩
        have hC_le_A : C ≤ A := hC_le_Phi.trans hPhi_le_A
        have hC_le_Ylift : C ≤ Ylift := hC_le_Phi.trans hPhi_le_Ylift
        have hfactor1A_card_eq_C :
            Nat.card (LowerCentralFactor A 1) = Nat.card C := by
          change Nat.card
              (((⊤ : Subgroup A).lowerCentralSeries 1) ⧸ lowerCentralFactorKernel A 1) =
            Nat.card C
          rw [hkernel1A]
          calc
            Nat.card (((⊤ : Subgroup A).lowerCentralSeries 1) ⧸
                  (⊥ : Subgroup ((⊤ : Subgroup A).lowerCentralSeries 1))) =
                Nat.card ((⊤ : Subgroup A).lowerCentralSeries 1) :=
              Nat.card_congr QuotientGroup.quotientBot.toEquiv
            _ = Nat.card (C.subgroupOf A) := by rw [hL1A]
            _ = Nat.card C :=
              Nat.card_congr
                (Subgroup.subgroupOfEquivOfLe hC_le_A).toEquiv
        have hfactor1Y_card_eq_C :
            Nat.card (LowerCentralFactor Ylift 1) = Nat.card C := by
          change Nat.card
              (((⊤ : Subgroup Ylift).lowerCentralSeries 1) ⧸
                lowerCentralFactorKernel Ylift 1) = Nat.card C
          rw [hkernel1Y]
          calc
            Nat.card (((⊤ : Subgroup Ylift).lowerCentralSeries 1) ⧸
                  (⊥ : Subgroup ((⊤ : Subgroup Ylift).lowerCentralSeries 1))) =
                Nat.card ((⊤ : Subgroup Ylift).lowerCentralSeries 1) :=
              Nat.card_congr QuotientGroup.quotientBot.toEquiv
            _ = Nat.card (C.subgroupOf Ylift) := by rw [hL1Y]
            _ = Nat.card C :=
              Nat.card_congr
                (Subgroup.subgroupOfEquivOfLe hC_le_Ylift).toEquiv
        have hfactor1A_card_pow :
            Nat.card (LowerCentralFactor A 1) = 2 ^ nA := by
          rcases hformA with hformAB | hformAC
          · rcases hformAB with
              ⟨eta, epsilon, uNorm, vNorm, centerCoordinates,
                heta, hepsilon, _⟩
            calc
              Nat.card (LowerCentralFactor A 1) =
                  Nat.card (Additive (LowerCentralFactor A 1)) := rfl
              _ = Nat.card (BinaryGaloisField nA) :=
                (Nat.card_congr centerCoordinates.toEquiv).symm
              _ = 2 ^ nA := GaloisField.card 2 nA (by omega)
          · unfold Lemma12TypeCNormalizedData at hformAC
            rcases hformAC with
              ⟨theta, lambda, eta, epsilon, outerNorm, middleNorm,
                centerCoordinates, hlambda, heta, hepsilon, _⟩
            calc
              Nat.card (LowerCentralFactor A 1) =
                  Nat.card (Additive (LowerCentralFactor A 1)) := rfl
              _ = Nat.card (BinaryGaloisField nA) :=
                (Nat.card_congr centerCoordinates.toEquiv).symm
              _ = 2 ^ nA := GaloisField.card 2 nA (by omega)
        have hfactor1Y_card_pow :
            Nat.card (LowerCentralFactor Ylift 1) = 2 ^ nY := by
          rcases hformY with hformYB | hformYC
          · rcases hformYB with
              ⟨eta, epsilon, uNorm, vNorm, centerCoordinates,
                heta, hepsilon, _⟩
            calc
              Nat.card (LowerCentralFactor Ylift 1) =
                  Nat.card (Additive (LowerCentralFactor Ylift 1)) := rfl
              _ = Nat.card (BinaryGaloisField nY) :=
                (Nat.card_congr centerCoordinates.toEquiv).symm
              _ = 2 ^ nY := GaloisField.card 2 nY (by omega)
          · unfold Lemma12TypeCNormalizedData at hformYC
            rcases hformYC with
              ⟨theta, lambda, eta, epsilon, outerNorm, middleNorm,
                centerCoordinates, hlambda, heta, hepsilon, _⟩
            calc
              Nat.card (LowerCentralFactor Ylift 1) =
                  Nat.card (Additive (LowerCentralFactor Ylift 1)) := rfl
              _ = Nat.card (BinaryGaloisField nY) :=
                (Nat.card_congr centerCoordinates.toEquiv).symm
              _ = 2 ^ nY := GaloisField.card 2 nY (by omega)
        have hnA_eq_nC : nA = nC := by
          apply Nat.pow_right_injective (by norm_num : 1 < 2)
          calc
            2 ^ nA = Nat.card (LowerCentralFactor A 1) :=
              hfactor1A_card_pow.symm
            _ = Nat.card C := hfactor1A_card_eq_C
            _ = 2 ^ nC := hC_card
        have hnY_eq_nC : nY = nC := by
          apply Nat.pow_right_injective (by norm_num : 1 < 2)
          calc
            2 ^ nY = Nat.card (LowerCentralFactor Ylift 1) :=
              hfactor1Y_card_pow.symm
            _ = Nat.card C := hfactor1Y_card_eq_C
            _ = 2 ^ nC := hC_card
        have hnA_eq_nY : nA = nY := hnA_eq_nC.trans hnY_eq_nC.symm
        subst nY
        subst nC
        have hA_sq_C (a : A) : (a : Q) ^ 2 ∈ C := by
          exact hA_sq_bottom a
        have hYlift_sq_C (y : Ylift) : (y : Q) ^ 2 ∈ C := by
          exact hYlift_sq_bottom y
        have hcommA_eq_C : ⁅A, A⁆ = C := by
          calc
            ⁅A, A⁆ = (commutator A).map A.subtype :=
              (Subgroup.map_subtype_commutator A).symm
            _ = (C.subgroupOf A).map A.subtype := by
              rw [← Subgroup.top_lowerCentralSeries_one, hL1A]
            _ = C := Subgroup.map_subgroupOf_eq_of_le hC_le_A
        have hcommYlift_eq_C : ⁅Ylift, Ylift⁆ = C := by
          calc
            ⁅Ylift, Ylift⁆ = (commutator Ylift).map Ylift.subtype :=
              (Subgroup.map_subtype_commutator Ylift).symm
            _ = (C.subgroupOf Ylift).map Ylift.subtype := by
              rw [← Subgroup.top_lowerCentralSeries_one, hL1Y]
            _ = C := Subgroup.map_subgroupOf_eq_of_le hC_le_Ylift
        have hC_le_commutator : C ≤ commutator Q := by
          calc
            C = ⁅A, A⁆ := hcommA_eq_C.symm
            _ ≤ ⁅(⊤ : Subgroup Q), ⊤⁆ :=
              Subgroup.commutator_mono le_top le_top
            _ = commutator Q := rfl
        have hcommutator_le_Phi : commutator Q ≤ PhiTop := by
          calc
            commutator Q ≤ frattini Q :=
              commutator_le_frattini_of_isPGroup (R := Q) (p := 2)
            _ = PhiTop := hPhiTop_eq.symm
        have hcommutator_X : IsXInvariantSubgroup X (commutator Q) :=
          (isInvariant_of_characteristic (A := X) (G := Q)
            (commutator Q)).invariant
        have hcommutator_eq_Phi : commutator Q = PhiTop := by
          rcases hC_cover_Phi (commutator Q) hcommutator_X
              hC_le_commutator hcommutator_le_Phi with hcomm_C | hcomm_Phi
          · let : A.Normal := hupper.2.2.1
            let : C.Normal := hbottom.2.1
            have hPhi_le_C : PhiTop ≤ C := by
              rw [hPhiTop_eq]
              exact lemma13_frattini_le_of_sup_and_squares A Ylift C
                hA_sup_Ylift (by rw [hcomm_C]) hA_sq_C hYlift_sq_C
            exact False.elim (hC_lt_Phi.2 hPhi_le_C)
          · exact hcomm_Phi
        have hL1_eq_Phi : (⊤ : Subgroup Q).lowerCentralSeries 1 = PhiTop := by
          rw [Subgroup.top_lowerCentralSeries_one]
          exact hcommutator_eq_Phi
        have hPhi_comm_A_le_C : ⁅PhiTop, A⁆ ≤ C := by
          calc
            ⁅PhiTop, A⁆ ≤ ⁅A, A⁆ :=
              Subgroup.commutator_mono hPhi_le_A le_rfl
            _ = C := hcommA_eq_C
        have hPhi_comm_Ylift_le_C : ⁅PhiTop, Ylift⁆ ≤ C := by
          calc
            ⁅PhiTop, Ylift⁆ ≤ ⁅Ylift, Ylift⁆ :=
              Subgroup.commutator_mono hPhi_le_Ylift le_rfl
            _ = C := hcommYlift_eq_C
        have hPhi_comm_top_le_C : ⁅PhiTop, (⊤ : Subgroup Q)⁆ ≤ C := by
          rw [← hA_sup_Ylift]
          let : C.Normal := hbottom.2.1
          exact lemma13_commutator_sup_right_le
            hPhi_comm_A_le_C hPhi_comm_Ylift_le_C
        have hL2_le_C : (⊤ : Subgroup Q).lowerCentralSeries 2 ≤ C := by
          change ⁅(⊤ : Subgroup Q).lowerCentralSeries 1, (⊤ : Subgroup Q)⁆ ≤ C
          rw [hL1_eq_Phi]
          exact hPhi_comm_top_le_C
        have hL2_ne_bot : (⊤ : Subgroup Q).lowerCentralSeries 2 ≠ ⊥ := by
          rcases hA_internal_comm with ⟨x, hxPhi, y, hxy_ne⟩
          have hxyQ_ne : ⁅(x : Q), (y : Q)⁆ ≠ 1 := by
            intro hxy
            apply hxy_ne
            exact Subtype.ext hxy
          have hxy_mem : ⁅(x : Q), (y : Q)⁆ ∈ (⊤ : Subgroup Q).lowerCentralSeries 2 := by
            change ⁅(x : Q), (y : Q)⁆ ∈
              ⁅(⊤ : Subgroup Q).lowerCentralSeries 1, (⊤ : Subgroup Q)⁆
            apply Subgroup.commutator_mem_commutator
            · rw [hL1_eq_Phi]
              exact hxPhi
            · trivial
          intro hbot
          apply hxyQ_ne
          have : ⁅(x : Q), (y : Q)⁆ ∈ (⊥ : Subgroup Q) := by
            rw [← hbot]
            exact hxy_mem
          simpa using this
        have hL2_X : IsXInvariantSubgroup X ((⊤ : Subgroup Q).lowerCentralSeries 2) :=
          (isInvariant_of_characteristic (A := X) (G := Q)
            ((⊤ : Subgroup Q).lowerCentralSeries 2)).invariant
        have hL2_eq_C : (⊤ : Subgroup Q).lowerCentralSeries 2 = C := by
          rcases hC_min_X ((⊤ : Subgroup Q).lowerCentralSeries 2) hL2_X hL2_le_C with
            hbot | hC
          · exact False.elim (hL2_ne_bot hbot)
          · exact hC
        have hkernel0_map_eq_Phi :
            (lowerCentralFactorKernel Q 0).map
                ((⊤ : Subgroup Q).lowerCentralSeries 0).subtype = PhiTop := by
          have hsquares_map :
              (squaresSubgroup ((⊤ : Subgroup Q).lowerCentralSeries 0)).map
                  ((⊤ : Subgroup Q).lowerCentralSeries 0).subtype = squaresSubgroup Q := by
            apply le_antisymm
            · rw [squaresSubgroup, MonoidHom.map_closure, Subgroup.closure_le]
              rintro _ ⟨x, ⟨y, rfl⟩, rfl⟩
              exact Subgroup.subset_closure ⟨(y : Q), rfl⟩
            · rw [squaresSubgroup, Subgroup.closure_le]
              rintro _ ⟨y, rfl⟩
              let yt : (⊤ : Subgroup Q).lowerCentralSeries 0 := ⟨y, trivial⟩
              exact ⟨yt ^ 2, Subgroup.subset_closure ⟨yt, rfl⟩, rfl⟩
          have hsquares_le_Phi : squaresSubgroup Q ≤ PhiTop := by
            rw [squaresSubgroup, Subgroup.closure_le]
            rintro _ ⟨y, rfl⟩
            rw [hPhiTop_eq]
            exact pth_power_mem_frattini_of_isPGroup
              (R := Q) (p := 2) y
          have hnext_map :
              (((⊤ : Subgroup Q).lowerCentralSeries 1).subgroupOf
                  ((⊤ : Subgroup Q).lowerCentralSeries 0)).map
                    ((⊤ : Subgroup Q).lowerCentralSeries 0).subtype =
                (⊤ : Subgroup Q).lowerCentralSeries 1 :=
            Subgroup.map_subgroupOf_eq_of_le
              ((⊤ : Subgroup Q).lowerCentralSeries_antitone
                (by omega : 0 ≤ 1))
          rw [lowerCentralFactorKernel, Subgroup.map_sup, hsquares_map,
            hnext_map, hL1_eq_Phi]
          exact sup_eq_right.mpr hsquares_le_Phi
        have hPhi_le_L0 : PhiTop ≤ (⊤ : Subgroup Q).lowerCentralSeries 0 := by
          intro x hx
          trivial
        have hkernel0_eq_Phi :
            lowerCentralFactorKernel Q 0 =
              PhiTop.subgroupOf ((⊤ : Subgroup Q).lowerCentralSeries 0) := by
          apply (Subgroup.map_injective
            ((⊤ : Subgroup Q).lowerCentralSeries 0).subtype_injective)
          calc
            (lowerCentralFactorKernel Q 0).map
                ((⊤ : Subgroup Q).lowerCentralSeries 0).subtype = PhiTop :=
              hkernel0_map_eq_Phi
            _ = (PhiTop.subgroupOf ((⊤ : Subgroup Q).lowerCentralSeries 0)).map
                ((⊤ : Subgroup Q).lowerCentralSeries 0).subtype :=
              (Subgroup.map_subgroupOf_eq_of_le hPhi_le_L0).symm
        have hkernel1_map_eq_C :
            (lowerCentralFactorKernel Q 1).map
                ((⊤ : Subgroup Q).lowerCentralSeries 1).subtype = C := by
          have hsquares_map :
              (squaresSubgroup ((⊤ : Subgroup Q).lowerCentralSeries 1)).map
                  ((⊤ : Subgroup Q).lowerCentralSeries 1).subtype = PhiSq := by
            rw [hL1_eq_Phi]
          have hnext_map :
              (((⊤ : Subgroup Q).lowerCentralSeries 2).subgroupOf
                  ((⊤ : Subgroup Q).lowerCentralSeries 1)).map
                    ((⊤ : Subgroup Q).lowerCentralSeries 1).subtype =
                (⊤ : Subgroup Q).lowerCentralSeries 2 :=
            Subgroup.map_subgroupOf_eq_of_le
              ((⊤ : Subgroup Q).lowerCentralSeries_antitone
                (by omega : 1 ≤ 2))
          rw [lowerCentralFactorKernel, Subgroup.map_sup, hsquares_map,
            hnext_map, hPhiSq_eq_C, hL2_eq_C, sup_idem]
        have hC_le_L1 : C ≤ (⊤ : Subgroup Q).lowerCentralSeries 1 := by
          rw [hL1_eq_Phi]
          exact hC_le_Phi
        have hkernel1_eq_C :
            lowerCentralFactorKernel Q 1 =
              C.subgroupOf ((⊤ : Subgroup Q).lowerCentralSeries 1) := by
          apply (Subgroup.map_injective
            ((⊤ : Subgroup Q).lowerCentralSeries 1).subtype_injective)
          calc
            (lowerCentralFactorKernel Q 1).map
                ((⊤ : Subgroup Q).lowerCentralSeries 1).subtype = C := hkernel1_map_eq_C
            _ = (C.subgroupOf ((⊤ : Subgroup Q).lowerCentralSeries 1)).map
                ((⊤ : Subgroup Q).lowerCentralSeries 1).subtype :=
              (Subgroup.map_subgroupOf_eq_of_le hC_le_L1).symm
        have hL3_eq_bot : (⊤ : Subgroup Q).lowerCentralSeries 3 = ⊥ := by
          have hL2_le_center : (⊤ : Subgroup Q).lowerCentralSeries 2 ≤ Subgroup.center Q := by
            rw [hL2_eq_C]
            exact hC_le_center
          simpa using
            (Subgroup.lowerCentralSeries_succ_eq_bot
              (⊤ : Subgroup Q) (n := 2)
              hL2_le_center)
        have hkernel2_bot : lowerCentralFactorKernel Q 2 = ⊥ := by
          apply le_antisymm
          · rw [lowerCentralFactorKernel]
            apply sup_le
            · rw [squaresSubgroup, Subgroup.closure_le]
              rintro _ ⟨x, rfl⟩
              change x ^ 2 = 1
              apply Subtype.ext
              change (x : Q) ^ 2 = 1
              let c : C := ⟨x, hL2_eq_C ▸ x.property⟩
              simpa [c] using congrArg Subtype.val (hCData.2 c)
            · intro x hx
              change (x : Q) ∈ (⊤ : Subgroup Q).lowerCentralSeries 3 at hx
              rw [hL3_eq_bot] at hx
              simpa using hx
          · exact bot_le
        have hkernel0A_eq_C : lowerCentralFactorKernel A 0 =
            (C.subgroupOf A).subgroupOf ((⊤ : Subgroup A).lowerCentralSeries 0) :=
          lemma13_lowerCentralFactorKernel_zero_eq_of_canonical_ker
            (C.subgroupOf A) qA hqA_ker hqA_mk
        have hkernel0Y_eq_C : lowerCentralFactorKernel Ylift 0 =
            (C.subgroupOf Ylift).subgroupOf
              ((⊤ : Subgroup Ylift).lowerCentralSeries 0) :=
          lemma13_lowerCentralFactorKernel_zero_eq_of_canonical_ker
            (C.subgroupOf Ylift) qY hqY_ker hqY_mk
        let outerA : VA →ₗ[ZMod 2]
            Additive (LowerCentralFactor Q 0) :=
          lemma13_factorZeroComplementLinearMap A PhiTop C VA hC_le_Phi
            hkernel0A_eq_C hkernel0_eq_Phi
        let outerY : VY →ₗ[ZMod 2]
            Additive (LowerCentralFactor Q 0) :=
          lemma13_factorZeroComplementLinearMap Ylift PhiTop C VY hC_le_Phi
            hkernel0Y_eq_C hkernel0_eq_Phi
        have houterA_injective : Function.Injective outerA :=
          lemma13_factorZeroComplementLinearMap_injective
            A PhiTop C hPhi_le_A UA VA qA hC_le_Phi
              hkernel0A_eq_C hkernel0_eq_Phi hqA_mk hUA hUVA
        have houterY_injective : Function.Injective outerY :=
          lemma13_factorZeroComplementLinearMap_injective
            Ylift PhiTop C hPhi_le_Ylift UY VY qY hC_le_Phi
              hkernel0Y_eq_C hkernel0_eq_Phi hqY_mk hUY hUVY
        let middleA : Additive (LowerCentralFactor Q 1) ≃ₗ[ZMod 2] UA :=
          lemma13_middleFactorLinearEquiv A C PhiTop hPhi_le_A qA UA
            hqA_ker hUA hL1_eq_Phi hkernel1_eq_C
        let middleY : Additive (LowerCentralFactor Q 1) ≃ₗ[ZMod 2] UY :=
          lemma13_middleFactorLinearEquiv Ylift C PhiTop hPhi_le_Ylift qY UY
            hqY_ker hUY hL1_eq_Phi hkernel1_eq_C
        obtain ⟨bracketQ, hbracketQ_mk, hbracketQ_equivariant,
            hbracketQ_self, hbracketQ_span⟩ :=
          lemma4_exists_lowerCentralBracket (H := Q)
        have hJacobiQ := lemma13_lowerCentralJacobi bracketQ hbracketQ_mk
        let centerA : Additive (LowerCentralFactor A 1) ≃ₗ[ZMod 2]
            Additive (LowerCentralFactor Q 2) :=
          lemma13_centerFactorLinearEquiv A C hC_le_A hL1A hkernel1A
            hL2_eq_C hkernel2_bot
        let centerY : Additive (LowerCentralFactor Ylift 1) ≃ₗ[ZMod 2]
            Additive (LowerCentralFactor Q 2) :=
          lemma13_centerFactorLinearEquiv Ylift C hC_le_Ylift hL1Y hkernel1Y
            hL2_eq_C hkernel2_bot
        have hbracketQ_symm : ∀ x y, bracketQ x y = bracketQ y x :=
          lemma13_alternating_isSymm bracketQ hbracketQ_self
        have houterAA_zero (a b : VA) :
            bracketQ (outerA a) (outerA b) = 0 := by
          change bracketQ
              (lemma13_factorZeroInclusionLinearMap A PhiTop C hC_le_Phi
                hkernel0A_eq_C hkernel0_eq_Phi
                  (a : Additive (LowerCentralFactor A 0)))
              (lemma13_factorZeroInclusionLinearMap A PhiTop C hC_le_Phi
                hkernel0A_eq_C hkernel0_eq_Phi
                  (b : Additive (LowerCentralFactor A 0))) = 0
          exact lemma13_factorZeroInclusion_bracket_eq_zero
            A PhiTop C hC_le_Phi (by rw [hcommA_eq_C])
              hkernel0A_eq_C hkernel0_eq_Phi hkernel1_eq_C
                bracketQ hbracketQ_mk _ _
        have houterYY_zero (y z : VY) :
            bracketQ (outerY y) (outerY z) = 0 := by
          change bracketQ
              (lemma13_factorZeroInclusionLinearMap Ylift PhiTop C hC_le_Phi
                hkernel0Y_eq_C hkernel0_eq_Phi
                  (y : Additive (LowerCentralFactor Ylift 0)))
              (lemma13_factorZeroInclusionLinearMap Ylift PhiTop C hC_le_Phi
                hkernel0Y_eq_C hkernel0_eq_Phi
                  (z : Additive (LowerCentralFactor Ylift 0))) = 0
          exact lemma13_factorZeroInclusion_bracket_eq_zero
            Ylift PhiTop C hC_le_Phi (by rw [hcommYlift_eq_C])
              hkernel0Y_eq_C hkernel0_eq_Phi hkernel1_eq_C
                bracketQ hbracketQ_mk _ _
        let crossA : VA →ₗ[ZMod 2] VY →ₗ[ZMod 2] UA :=
          { toFun := fun a =>
              { toFun := fun y => middleA (bracketQ (outerA a) (outerY y))
                map_add' := by
                  intro y z
                  change middleA (bracketQ (outerA a) (outerY (y + z))) =
                    middleA (bracketQ (outerA a) (outerY y)) +
                      middleA (bracketQ (outerA a) (outerY z))
                  simp only [map_add]
                map_smul' := by
                  intro c y
                  change middleA (bracketQ (outerA a) (outerY (c • y))) =
                    c • middleA (bracketQ (outerA a) (outerY y))
                  simp only [map_smul] }
            map_add' := by
              intro a b
              apply LinearMap.ext
              intro y
              change middleA (bracketQ (outerA (a + b)) (outerY y)) =
                middleA (bracketQ (outerA a) (outerY y)) +
                  middleA (bracketQ (outerA b) (outerY y))
              simp only [map_add, LinearMap.add_apply]
            map_smul' := by
              intro c a
              apply LinearMap.ext
              intro y
              change middleA (bracketQ (outerA (c • a)) (outerY y)) =
                c • middleA (bracketQ (outerA a) (outerY y))
              simp only [map_smul, LinearMap.smul_apply] }
        let crossY : VA →ₗ[ZMod 2] VY →ₗ[ZMod 2] UY :=
          { toFun := fun a =>
              { toFun := fun y => middleY (bracketQ (outerA a) (outerY y))
                map_add' := by
                  intro y z
                  change middleY (bracketQ (outerA a) (outerY (y + z))) =
                    middleY (bracketQ (outerA a) (outerY y)) +
                      middleY (bracketQ (outerA a) (outerY z))
                  simp only [map_add]
                map_smul' := by
                  intro c y
                  change middleY (bracketQ (outerA a) (outerY (c • y))) =
                    c • middleY (bracketQ (outerA a) (outerY y))
                  simp only [map_smul] }
            map_add' := by
              intro a b
              apply LinearMap.ext
              intro y
              change middleY (bracketQ (outerA (a + b)) (outerY y)) =
                middleY (bracketQ (outerA a) (outerY y)) +
                  middleY (bracketQ (outerA b) (outerY y))
              simp only [map_add, LinearMap.add_apply]
            map_smul' := by
              intro c a
              apply LinearMap.ext
              intro y
              change middleY (bracketQ (outerA (c • a)) (outerY y)) =
                c • middleY (bracketQ (outerA a) (outerY y))
              simp only [map_smul, LinearMap.smul_apply] }
        have hJacobiA_local (a a' : VA) (y : VY) :
            bracketA
                ((crossA a' y : UA) : Additive (LowerCentralFactor A 0))
                (a : Additive (LowerCentralFactor A 0)) +
              bracketA
                ((crossA a y : UA) : Additive (LowerCentralFactor A 0))
                (a' : Additive (LowerCentralFactor A 0)) = 0 := by
          apply centerA.injective
          rw [map_zero, map_add]
          change centerA
              (bracketA
                ↑(middleA (bracketQ (outerA a') (outerY y)))
                ↑a) +
            centerA
              (bracketA
                ↑(middleA (bracketQ (outerA a) (outerY y)))
                ↑a') = 0
          rw [lemma13_localBracket_to_ambientIterated
              A C PhiTop hC_le_A hPhi_le_A hC_le_Phi qA UA hqA_ker hqA_mk hUA
                hkernel0A_eq_C hkernel0_eq_Phi hL1A hkernel1A
                  hL1_eq_Phi hkernel1_eq_C hL2_eq_C hkernel2_bot
                    bracketA hbracketA
                    (a : Additive (LowerCentralFactor A 0))
                    (bracketQ (outerA a') (outerY y)),
            lemma13_localBracket_to_ambientIterated
              A C PhiTop hC_le_A hPhi_le_A hC_le_Phi qA UA hqA_ker hqA_mk hUA
                hkernel0A_eq_C hkernel0_eq_Phi hL1A hkernel1A
                  hL1_eq_Phi hkernel1_eq_C hL2_eq_C hkernel2_bot
                    bracketA hbracketA
                    (a' : Additive (LowerCentralFactor A 0))
                    (bracketQ (outerA a) (outerY y))]
          have hj := hJacobiQ (outerA a) (outerA a') (outerY y)
          rw [hbracketQ_symm (outerY y) (outerA a), houterAA_zero,
            map_zero, add_zero] at hj
          exact hj
        have hJacobiY_local (a : VA) (y y' : VY) :
            bracketY
                ((crossY a y' : UY) : Additive (LowerCentralFactor Ylift 0))
                (y : Additive (LowerCentralFactor Ylift 0)) +
              bracketY
                ((crossY a y : UY) : Additive (LowerCentralFactor Ylift 0))
                (y' : Additive (LowerCentralFactor Ylift 0)) = 0 := by
          apply centerY.injective
          rw [map_zero, map_add]
          change centerY
              (bracketY
                ↑(middleY (bracketQ (outerA a) (outerY y')))
                ↑y) +
            centerY
              (bracketY
                ↑(middleY (bracketQ (outerA a) (outerY y)))
                ↑y') = 0
          rw [lemma13_localBracket_to_ambientIterated
              Ylift C PhiTop hC_le_Ylift hPhi_le_Ylift hC_le_Phi qY UY
                hqY_ker hqY_mk hUY hkernel0Y_eq_C hkernel0_eq_Phi
                  hL1Y hkernel1Y hL1_eq_Phi hkernel1_eq_C
                    hL2_eq_C hkernel2_bot bracketY hbracketY
                    (y : Additive (LowerCentralFactor Ylift 0))
                    (bracketQ (outerA a) (outerY y')),
            lemma13_localBracket_to_ambientIterated
              Ylift C PhiTop hC_le_Ylift hPhi_le_Ylift hC_le_Phi qY UY
                hqY_ker hqY_mk hUY hkernel0Y_eq_C hkernel0_eq_Phi
                  hL1Y hkernel1Y hL1_eq_Phi hkernel1_eq_C
                    hL2_eq_C hkernel2_bot bracketY hbracketY
                    (y' : Additive (LowerCentralFactor Ylift 0))
                    (bracketQ (outerA a) (outerY y))]
          have hj := hJacobiQ (outerY y) (outerY y') (outerA a)
          rw [hbracketQ_symm (outerY y') (outerA a), houterYY_zero,
            map_zero, add_zero] at hj
          exact hj
        let commonActor : X := g ^ (2 ^ (kA + kY))
        let commonQ : MulAut Q :=
          MulDistribMulAction.toMulAut X Q commonActor
        let commonA : MulAut A := xiA ^ (2 ^ kY)
        let commonY : MulAut Ylift := xiY ^ (2 ^ kA)
        have hcommonA_actor : commonA =
            MulDistribMulAction.toMulAut X A commonActor := by
          change xiA ^ (2 ^ kY) =
            MulDistribMulAction.toMulAut X A commonActor
          rw [hxiA]
          calc
            (MulDistribMulAction.toMulAut X A (g ^ (2 ^ kA))) ^
                  (2 ^ kY) =
                MulDistribMulAction.toMulAut X A
                  ((g ^ (2 ^ kA)) ^ (2 ^ kY)) :=
              (map_pow (MulDistribMulAction.toMulAut X A)
                (g ^ (2 ^ kA)) (2 ^ kY)).symm
            _ = MulDistribMulAction.toMulAut X A commonActor := by
              congr 1
              change (g ^ (2 ^ kA)) ^ (2 ^ kY) =
                g ^ (2 ^ (kA + kY))
              rw [← pow_mul, pow_add]
        have hcommonY_actor : commonY =
            MulDistribMulAction.toMulAut X Ylift commonActor := by
          change xiY ^ (2 ^ kA) =
            MulDistribMulAction.toMulAut X Ylift commonActor
          rw [hxiY]
          calc
            (MulDistribMulAction.toMulAut X Ylift (g ^ (2 ^ kY))) ^
                  (2 ^ kA) =
                MulDistribMulAction.toMulAut X Ylift
                  ((g ^ (2 ^ kY)) ^ (2 ^ kA)) :=
              (map_pow (MulDistribMulAction.toMulAut X Ylift)
                (g ^ (2 ^ kY)) (2 ^ kA)).symm
            _ = MulDistribMulAction.toMulAut X Ylift commonActor := by
              congr 1
              change (g ^ (2 ^ kY)) ^ (2 ^ kA) =
                g ^ (2 ^ (kA + kY))
              rw [← pow_mul, pow_add, Nat.mul_comm]
        have hcommonA_compat (a : A) :
            commonQ (a : Q) = (commonA a : A) := by
          rw [hcommonA_actor]
          rfl
        have hcommonY_compat (y : Ylift) :
            commonQ (y : Q) = (commonY y : Ylift) := by
          rw [hcommonY_actor]
          rfl
        have houterA_common (a a' : VA)
            (ha : lowerCentralFactorLinearAut commonA 0
              (a : Additive (LowerCentralFactor A 0)) =
                (a' : Additive (LowerCentralFactor A 0))) :
            outerA a' = lowerCentralFactorLinearAut commonQ 0 (outerA a) := by
          change lemma13_factorZeroInclusionLinearMap A PhiTop C hC_le_Phi
              hkernel0A_eq_C hkernel0_eq_Phi
                (a' : Additive (LowerCentralFactor A 0)) = _
          rw [← ha]
          exact lemma13_factorZeroInclusionLinearMap_equivariant
            A PhiTop C hC_le_Phi hkernel0A_eq_C hkernel0_eq_Phi
              commonQ commonA hcommonA_compat
                (a : Additive (LowerCentralFactor A 0))
        have houterY_common (y y' : VY)
            (hy : lowerCentralFactorLinearAut commonY 0
              (y : Additive (LowerCentralFactor Ylift 0)) =
                (y' : Additive (LowerCentralFactor Ylift 0))) :
            outerY y' = lowerCentralFactorLinearAut commonQ 0 (outerY y) := by
          change lemma13_factorZeroInclusionLinearMap Ylift PhiTop C hC_le_Phi
              hkernel0Y_eq_C hkernel0_eq_Phi
                (y' : Additive (LowerCentralFactor Ylift 0)) = _
          rw [← hy]
          exact lemma13_factorZeroInclusionLinearMap_equivariant
            Ylift PhiTop C hC_le_Phi hkernel0Y_eq_C hkernel0_eq_Phi
              commonQ commonY hcommonY_compat
                (y : Additive (LowerCentralFactor Ylift 0))
        have hcrossA_common (a a' : VA) (y y' : VY)
            (ha : lowerCentralFactorLinearAut commonA 0
              (a : Additive (LowerCentralFactor A 0)) =
                (a' : Additive (LowerCentralFactor A 0)))
            (hy : lowerCentralFactorLinearAut commonY 0
              (y : Additive (LowerCentralFactor Ylift 0)) =
                (y' : Additive (LowerCentralFactor Ylift 0))) :
            ((crossA a' y' : UA) : Additive (LowerCentralFactor A 0)) =
              lowerCentralFactorLinearAut commonA 0
                ((crossA a y : UA) : Additive (LowerCentralFactor A 0)) := by
          change ((middleA (bracketQ (outerA a') (outerY y')) : UA) :
              Additive (LowerCentralFactor A 0)) = _
          rw [houterA_common a a' ha, houterY_common y y' hy,
            hbracketQ_equivariant]
          exact lemma13_middleFactorLinearEquiv_equivariant
            A C PhiTop hPhi_le_A qA UA hqA_ker hUA
              hL1_eq_Phi hkernel1_eq_C commonQ commonA hcommonA_compat
                (lemma13_canonicalFactorZeroMap_equivariant qA hqA_mk commonA)
                  (bracketQ (outerA a) (outerY y))
        let crossYRev : VY →ₗ[ZMod 2] VA →ₗ[ZMod 2] UY :=
          { toFun := fun y =>
              { toFun := fun a => crossY a y
                map_add' := by
                  intro a b
                  change crossY (a + b) y = crossY a y + crossY b y
                  rw [map_add, LinearMap.add_apply]
                map_smul' := by
                  intro c a
                  change crossY (c • a) y = c • crossY a y
                  rw [map_smul, LinearMap.smul_apply] }
            map_add' := by
              intro y z
              apply LinearMap.ext
              intro a
              exact (crossY a).map_add y z
            map_smul' := by
              intro c y
              apply LinearMap.ext
              intro a
              exact (crossY a).map_smul c y }
        have hspecA := lemma13_jacobiSpectralData_of_normalized
          xiA nA hnA UA VA bracketA squareA crossA hJacobiA_local hformA
        have hspecY := lemma13_jacobiSpectralData_of_normalized
          xiY nA hnA UY VY bracketY squareY crossYRev
            (fun y y' a => hJacobiY_local a y y') hformY
        unfold Lemma13JacobiSpectralData at hspecA hspecY
        rcases hspecA with
          ⟨etaA, rhoA, middleNormA, outerNormA, sigmaA, hetaA, hrhoA,
            hetaA_order, hrhoA_order, hbranchA,
            hmiddleA_action, houterA_action, hfactorA⟩
        rcases hspecY with
          ⟨etaY, rhoY, middleNormY, outerNormY, sigmaY, hetaY, hrhoY,
            hetaY_order, hrhoY_order, hbranchY,
            hmiddleY_action, houterY_action, hfactorY⟩
        have hmiddleA_common_action (b : BinaryGaloisField nA) :
            lowerCentralFactorLinearAut commonA 0
                (middleNormA b : Additive (LowerCentralFactor A 0)) =
              (middleNormA (etaA ^ (2 ^ kY) * b) :
                Additive (LowerCentralFactor A 0)) := by
          change lowerCentralFactorLinearAut (xiA ^ (2 ^ kY)) 0
              (middleNormA b : Additive (LowerCentralFactor A 0)) = _
          rw [lowerCentralFactorLinearAut_pow]
          exact lemma13_coordinate_action_pow xiA nA UA middleNormA etaA
            hmiddleA_action (2 ^ kY) b
        have houterA_common_action (a : BinaryGaloisField nA) :
            lowerCentralFactorLinearAut commonA 0
                (outerNormA a : Additive (LowerCentralFactor A 0)) =
              (outerNormA (rhoA ^ (2 ^ kY) * a) :
                Additive (LowerCentralFactor A 0)) := by
          change lowerCentralFactorLinearAut (xiA ^ (2 ^ kY)) 0
              (outerNormA a : Additive (LowerCentralFactor A 0)) = _
          rw [lowerCentralFactorLinearAut_pow]
          exact lemma13_coordinate_action_pow xiA nA VA outerNormA rhoA
            houterA_action (2 ^ kY) a
        have hmiddleY_common_action (b : BinaryGaloisField nA) :
            lowerCentralFactorLinearAut commonY 0
                (middleNormY b : Additive (LowerCentralFactor Ylift 0)) =
              (middleNormY (etaY ^ (2 ^ kA) * b) :
                Additive (LowerCentralFactor Ylift 0)) := by
          change lowerCentralFactorLinearAut (xiY ^ (2 ^ kA)) 0
              (middleNormY b : Additive (LowerCentralFactor Ylift 0)) = _
          rw [lowerCentralFactorLinearAut_pow]
          exact lemma13_coordinate_action_pow xiY nA UY middleNormY etaY
            hmiddleY_action (2 ^ kA) b
        have houterY_common_action (a : BinaryGaloisField nA) :
            lowerCentralFactorLinearAut commonY 0
                (outerNormY a : Additive (LowerCentralFactor Ylift 0)) =
              (outerNormY (rhoY ^ (2 ^ kA) * a) :
                Additive (LowerCentralFactor Ylift 0)) := by
          change lowerCentralFactorLinearAut (xiY ^ (2 ^ kA)) 0
              (outerNormY a : Additive (LowerCentralFactor Ylift 0)) = _
          rw [lowerCentralFactorLinearAut_pow]
          exact lemma13_coordinate_action_pow xiY nA VY outerNormY rhoY
            houterY_action (2 ^ kA) a
        let F : BinaryGaloisField nA →ₗ[ZMod 2]
            BinaryGaloisField nA →ₗ[ZMod 2] BinaryGaloisField nA :=
          { toFun := fun a =>
              { toFun := fun y => middleNormA.symm
                    (crossA (outerNormA a) (outerNormY y))
                map_add' := by
                  intro y z
                  change middleNormA.symm
                      (crossA (outerNormA a) (outerNormY (y + z))) =
                    middleNormA.symm
                        (crossA (outerNormA a) (outerNormY y)) +
                      middleNormA.symm
                        (crossA (outerNormA a) (outerNormY z))
                  simp only [map_add]
                map_smul' := by
                  intro c y
                  change middleNormA.symm
                      (crossA (outerNormA a) (outerNormY (c • y))) =
                    c • middleNormA.symm
                      (crossA (outerNormA a) (outerNormY y))
                  simp only [map_smul] }
            map_add' := by
              intro a b
              apply LinearMap.ext
              intro y
              change middleNormA.symm
                  (crossA (outerNormA (a + b)) (outerNormY y)) =
                middleNormA.symm
                    (crossA (outerNormA a) (outerNormY y)) +
                  middleNormA.symm
                    (crossA (outerNormA b) (outerNormY y))
              simp only [map_add, LinearMap.add_apply]
            map_smul' := by
              intro c a
              apply LinearMap.ext
              intro y
              change middleNormA.symm
                  (crossA (outerNormA (c • a)) (outerNormY y)) =
                c • middleNormA.symm
                  (crossA (outerNormA a) (outerNormY y))
              simp only [map_smul, LinearMap.smul_apply] }
        let L : BinaryGaloisField nA ≃ₗ[ZMod 2] BinaryGaloisField nA :=
          (((middleNormA.trans middleA.symm).trans middleY).trans
            middleNormY.symm)
        have hFA (a y : BinaryGaloisField nA) :
            F a y = sigmaA a * F 1 y := by
          change middleNormA.symm
              (crossA (outerNormA a) (outerNormY y)) =
            sigmaA a * middleNormA.symm
              (crossA (outerNormA 1) (outerNormY y))
          exact hfactorA a (outerNormY y)
        have hFY (a y : BinaryGaloisField nA) :
            L (F a y) = sigmaY y * L (F a 1) := by
          rw [show F a y = middleNormA.symm
                (crossA (outerNormA a) (outerNormY y)) by rfl,
            show F a 1 = middleNormA.symm
                (crossA (outerNormA a) (outerNormY 1)) by rfl]
          dsimp only [L, LinearEquiv.trans_apply]
          simp only [middleNormA.apply_symm_apply]
          rw [show crossA (outerNormA a) (outerNormY y) =
                middleA (bracketQ (outerA (outerNormA a))
                  (outerY (outerNormY y))) by rfl,
            show crossA (outerNormA a) (outerNormY 1) =
                middleA (bracketQ (outerA (outerNormA a))
                  (outerY (outerNormY 1))) by rfl]
          simp only [middleA.symm_apply_apply]
          have h := hfactorY y (outerNormA a)
          rw [show crossYRev (outerNormY y) (outerNormA a) =
                middleY (bracketQ (outerA (outerNormA a))
                  (outerY (outerNormY y))) by rfl,
            show crossYRev (outerNormY 1) (outerNormA a) =
                middleY (bracketQ (outerA (outerNormA a))
                  (outerY (outerNormY 1))) by rfl] at h
          exact h
        have hF_ne : ∃ a y : BinaryGaloisField nA, F a y ≠ 0 := by
          by_contra hF_zero
          push Not at hF_zero
          have hcross_zero (v : VA) (w : VY) :
              bracketQ (outerA v) (outerY w) = 0 := by
            apply middleA.injective
            rw [map_zero]
            change crossA v w = 0
            apply middleNormA.symm.injective
            rw [map_zero]
            have h := hF_zero (outerNormA.symm v) (outerNormY.symm w)
            change middleNormA.symm
                (crossA (outerNormA (outerNormA.symm v))
                  (outerNormY (outerNormY.symm w))) = 0 at h
            simpa only [outerNormA.apply_symm_apply,
              outerNormY.apply_symm_apply] using h
          have hcommAY_le_C : ⁅A, Ylift⁆ ≤ C := by
            apply Subgroup.commutator_le.mpr
            intro a ha y hy
            let aA : A := ⟨a, ha⟩
            let yY : Ylift := ⟨y, hy⟩
            obtain ⟨v, hv⟩ := lemma13_factorZeroInclusion_eq_complement
              A PhiTop C qA UA VA hC_le_Phi hkernel0A_eq_C
                hkernel0_eq_Phi hqA_mk hUA hUVA
                  (Additive.ofMul (qA aA))
            obtain ⟨w, hw⟩ := lemma13_factorZeroInclusion_eq_complement
              Ylift PhiTop C qY UY VY hC_le_Phi hkernel0Y_eq_C
                hkernel0_eq_Phi hqY_mk hUY hUVY
                  (Additive.ofMul (qY yY))
            let a0 : (⊤ : Subgroup Q).lowerCentralSeries 0 := ⟨a, by trivial⟩
            let y0 : (⊤ : Subgroup Q).lowerCentralSeries 0 := ⟨y, by trivial⟩
            have hclassA : Additive.ofMul
                  (QuotientGroup.mk' (lowerCentralFactorKernel Q 0) a0) =
                outerA v := by
              calc
                Additive.ofMul
                    (QuotientGroup.mk' (lowerCentralFactorKernel Q 0) a0) =
                    lemma13_factorZeroInclusionLinearMap A PhiTop C
                      hC_le_Phi hkernel0A_eq_C hkernel0_eq_Phi
                        (Additive.ofMul (qA aA)) := by
                          rw [hqA_mk,
                            lemma13_factorZeroInclusionLinearMap_mk]
                          rfl
                _ = outerA v := hv
            have hclassY : Additive.ofMul
                  (QuotientGroup.mk' (lowerCentralFactorKernel Q 0) y0) =
                outerY w := by
              calc
                Additive.ofMul
                    (QuotientGroup.mk' (lowerCentralFactorKernel Q 0) y0) =
                    lemma13_factorZeroInclusionLinearMap Ylift PhiTop C
                      hC_le_Phi hkernel0Y_eq_C hkernel0_eq_Phi
                        (Additive.ofMul (qY yY)) := by
                          rw [hqY_mk,
                            lemma13_factorZeroInclusionLinearMap_mk]
                          rfl
                _ = outerY w := hw
            have hcomm : ⁅(a0 : Q), (y0 : Q)⁆ ∈ (⊤ : Subgroup Q).lowerCentralSeries 1 := by
              rw [Subgroup.top_lowerCentralSeries_one]
              exact Subgroup.commutator_mem_commutator (by trivial) (by trivial)
            have hbr := hbracketQ_mk a0 y0 hcomm
            rw [hclassA, hclassY, hcross_zero] at hbr
            have hmk_one :
                QuotientGroup.mk' (lowerCentralFactorKernel Q 1)
                    ⟨⁅(a0 : Q), (y0 : Q)⁆, hcomm⟩ = 1 := by
              apply Additive.ofMul.injective
              simpa using hbr.symm
            have hker := (QuotientGroup.eq_one_iff _).mp hmk_one
            rw [hkernel1_eq_C] at hker
            exact hker
          let : C.Normal := hbottom.2.1
          have hA_sup_comm_le_C : ⁅A, A ⊔ Ylift⁆ ≤ C :=
            lemma13_commutator_sup_right_le
              (by rw [hcommA_eq_C]) hcommAY_le_C
          have hYA_le_C : ⁅Ylift, A⁆ ≤ C := by
            simpa only [Subgroup.commutator_comm] using hcommAY_le_C
          have hY_sup_comm_le_C : ⁅Ylift, A ⊔ Ylift⁆ ≤ C :=
            lemma13_commutator_sup_right_le hYA_le_C
              (by rw [hcommYlift_eq_C])
          have hsup_A_le_C : ⁅A ⊔ Ylift, A⁆ ≤ C := by
            simpa only [Subgroup.commutator_comm] using hA_sup_comm_le_C
          have hsup_Y_le_C : ⁅A ⊔ Ylift, Ylift⁆ ≤ C := by
            simpa only [Subgroup.commutator_comm] using hY_sup_comm_le_C
          have hsup_comm_le_C : ⁅A ⊔ Ylift, A ⊔ Ylift⁆ ≤ C :=
            lemma13_commutator_sup_right_le hsup_A_le_C hsup_Y_le_C
          have hcomm_le_C : commutator Q ≤ C := by
            change ⁅(⊤ : Subgroup Q), ⊤⁆ ≤ C
            rw [← hA_sup_Ylift]
            exact hsup_comm_le_C
          apply hC_lt_Phi.2
          rw [← hcommutator_eq_Phi]
          exact hcomm_le_C
        obtain ⟨T, hT⟩ :=
          lemma13_exists_normalized_field_equiv_of_cross_functional
            nA F L sigmaA sigmaY hFA hFY hF_ne
        let c : BinaryGaloisField nA := F 1 1
        let d : BinaryGaloisField nA := L c
        have hc : c ≠ 0 := by
          intro hc0
          rcases hF_ne with ⟨a, y, hay⟩
          have hF1y : F 1 y = 0 := by
            apply L.injective
            rw [hFY]
            simp [c, hc0]
          apply hay
          rw [hFA, hF1y, mul_zero]
        have hd : d ≠ 0 := by
          exact fun hd0 => hc (L.map_eq_zero_iff.mp (by simpa [d] using hd0))
        have hL_apply (b : BinaryGaloisField nA) :
            L b = middleNormY.symm
              (middleY (middleA.symm (middleNormA b))) := rfl
        have hmiddleA_transport (b : BinaryGaloisField nA) :
            middleA.symm (middleNormA (etaA ^ (2 ^ kY) * b)) =
              lowerCentralFactorLinearAut commonQ 1
                (middleA.symm (middleNormA b)) := by
          apply middleA.injective
          rw [middleA.apply_symm_apply]
          apply Subtype.ext
          calc
            ((middleNormA (etaA ^ (2 ^ kY) * b) : UA) :
                Additive (LowerCentralFactor A 0)) =
                lowerCentralFactorLinearAut commonA 0
                  ((middleNormA b : UA) :
                    Additive (LowerCentralFactor A 0)) :=
              (hmiddleA_common_action b).symm
            _ = ((middleA
                  (lowerCentralFactorLinearAut commonQ 1
                    (middleA.symm (middleNormA b))) : UA) :
                Additive (LowerCentralFactor A 0)) := by
              symm
              have heq := lemma13_middleFactorLinearEquiv_equivariant
                  A C PhiTop hPhi_le_A qA UA hqA_ker hUA
                    hL1_eq_Phi hkernel1_eq_C commonQ commonA
                      hcommonA_compat
                        (lemma13_canonicalFactorZeroMap_equivariant
                          qA hqA_mk commonA)
                            (middleA.symm (middleNormA b))
              change ((middleA
                    (lowerCentralFactorLinearAut commonQ 1
                      (middleA.symm (middleNormA b))) : UA) :
                  Additive (LowerCentralFactor A 0)) =
                lowerCentralFactorLinearAut commonA 0
                  (((middleA (middleA.symm (middleNormA b))) : UA) :
                    Additive (LowerCentralFactor A 0)) at heq
              simpa only [middleA.apply_symm_apply] using heq
        have hL_common (b : BinaryGaloisField nA) :
            L (etaA ^ (2 ^ kY) * b) =
              etaY ^ (2 ^ kA) * L b := by
          rw [hL_apply (etaA ^ (2 ^ kY) * b), hmiddleA_transport b]
          apply middleNormY.injective
          rw [middleNormY.apply_symm_apply]
          let z : Additive (LowerCentralFactor Q 1) :=
            middleA.symm (middleNormA b)
          have hcoord : middleY z = middleNormY (L b) := by
            rw [hL_apply, middleNormY.apply_symm_apply]
          apply Subtype.ext
          calc
            ((middleY (lowerCentralFactorLinearAut commonQ 1 z) : UY) :
                Additive (LowerCentralFactor Ylift 0)) =
                lowerCentralFactorLinearAut commonY 0
                  ((middleY z : UY) :
                    Additive (LowerCentralFactor Ylift 0)) :=
              lemma13_middleFactorLinearEquiv_equivariant
                Ylift C PhiTop hPhi_le_Ylift qY UY hqY_ker hUY
                  hL1_eq_Phi hkernel1_eq_C commonQ commonY
                    hcommonY_compat
                      (lemma13_canonicalFactorZeroMap_equivariant
                        qY hqY_mk commonY) z
            _ = lowerCentralFactorLinearAut commonY 0
                  ((middleNormY (L b) : UY) :
                    Additive (LowerCentralFactor Ylift 0)) := by rw [hcoord]
            _ = ((middleNormY (etaY ^ (2 ^ kA) * L b) : UY) :
                Additive (LowerCentralFactor Ylift 0)) :=
              hmiddleY_common_action (L b)
        have hT_eta : T (etaA ^ (2 ^ kY)) = etaY ^ (2 ^ kA) := by
          calc
            T (etaA ^ (2 ^ kY)) =
                d⁻¹ * L (c * etaA ^ (2 ^ kY)) := hT _
            _ = d⁻¹ * L (etaA ^ (2 ^ kY) * c) := by
              congr 2
              rw [mul_comm]
            _ = d⁻¹ * (etaY ^ (2 ^ kA) * L c) := by rw [hL_common]
            _ = etaY ^ (2 ^ kA) := by
              change d⁻¹ * (etaY ^ (2 ^ kA) * d) = _
              field_simp [hd]
        have houterA_one_common :
            lowerCentralFactorLinearAut commonA 0
                (outerNormA 1 : Additive (LowerCentralFactor A 0)) =
              (outerNormA (rhoA ^ (2 ^ kY)) :
                Additive (LowerCentralFactor A 0)) := by
          simpa using houterA_common_action 1
        have houterY_one_common :
            lowerCentralFactorLinearAut commonY 0
                (outerNormY 1 : Additive (LowerCentralFactor Ylift 0)) =
              (outerNormY (rhoY ^ (2 ^ kA)) :
                Additive (LowerCentralFactor Ylift 0)) := by
          simpa using houterY_common_action 1
        have hcross_common := hcrossA_common
          (outerNormA 1) (outerNormA (rhoA ^ (2 ^ kY)))
          (outerNormY 1) (outerNormY (rhoY ^ (2 ^ kA)))
          houterA_one_common houterY_one_common
        have hc_cross :
            crossA (outerNormA 1) (outerNormY 1) = middleNormA c := by
          apply middleNormA.symm.injective
          rw [middleNormA.symm_apply_apply]
          change F 1 1 = c
          rfl
        have hF_common :
            F (rhoA ^ (2 ^ kY)) (rhoY ^ (2 ^ kA)) =
              etaA ^ (2 ^ kY) * c := by
          apply middleNormA.injective
          rw [show F (rhoA ^ (2 ^ kY)) (rhoY ^ (2 ^ kA)) =
                middleNormA.symm
                  (crossA (outerNormA (rhoA ^ (2 ^ kY)))
                    (outerNormY (rhoY ^ (2 ^ kA)))) by rfl,
            middleNormA.apply_symm_apply]
          apply Subtype.ext
          calc
            ((crossA (outerNormA (rhoA ^ (2 ^ kY)))
                (outerNormY (rhoY ^ (2 ^ kA))) : UA) :
              Additive (LowerCentralFactor A 0)) =
                lowerCentralFactorLinearAut commonA 0
                  ((crossA (outerNormA 1) (outerNormY 1) : UA) :
                    Additive (LowerCentralFactor A 0)) := hcross_common
            _ = lowerCentralFactorLinearAut commonA 0
                  ((middleNormA c : UA) :
                    Additive (LowerCentralFactor A 0)) := by rw [hc_cross]
            _ = ((middleNormA (etaA ^ (2 ^ kY) * c) : UA) :
                Additive (LowerCentralFactor A 0)) :=
              hmiddleA_common_action c
        have hFY_common :
            L (F (rhoA ^ (2 ^ kY)) (rhoY ^ (2 ^ kA))) =
              sigmaY (rhoY ^ (2 ^ kA)) *
                L (sigmaA (rhoA ^ (2 ^ kY)) * c) := by
          calc
            L (F (rhoA ^ (2 ^ kY)) (rhoY ^ (2 ^ kA))) =
                sigmaY (rhoY ^ (2 ^ kA)) *
                  L (F (rhoA ^ (2 ^ kY)) 1) := hFY _ _
            _ = sigmaY (rhoY ^ (2 ^ kA)) *
                L (sigmaA (rhoA ^ (2 ^ kY)) * c) := by
              rw [hFA]
        have hscalarL :
            L (c * sigmaA (rhoA ^ (2 ^ kY))) *
                sigmaY (rhoY ^ (2 ^ kA)) =
              L (c * etaA ^ (2 ^ kY)) := by
          calc
            L (c * sigmaA (rhoA ^ (2 ^ kY))) *
                sigmaY (rhoY ^ (2 ^ kA)) =
                sigmaY (rhoY ^ (2 ^ kA)) *
                  L (sigmaA (rhoA ^ (2 ^ kY)) * c) := by
                    rw [mul_comm c, mul_comm
                      (L (sigmaA (rhoA ^ (2 ^ kY)) * c))]
            _ = L (F (rhoA ^ (2 ^ kY)) (rhoY ^ (2 ^ kA))) :=
              hFY_common.symm
            _ = L (etaA ^ (2 ^ kY) * c) := by rw [hF_common]
            _ = L (c * etaA ^ (2 ^ kY)) := by
              congr 1
              rw [mul_comm]
        have hscalar :
            T (sigmaA (rhoA ^ (2 ^ kY))) *
                sigmaY (rhoY ^ (2 ^ kA)) =
              T (etaA ^ (2 ^ kY)) := by
          calc
            T (sigmaA (rhoA ^ (2 ^ kY))) *
                sigmaY (rhoY ^ (2 ^ kA)) =
                (d⁻¹ * L (c * sigmaA (rhoA ^ (2 ^ kY)))) *
                  sigmaY (rhoY ^ (2 ^ kA)) := by rw [hT]
            _ = d⁻¹ *
                (L (c * sigmaA (rhoA ^ (2 ^ kY))) *
                  sigmaY (rhoY ^ (2 ^ kA))) := by ring
            _ = d⁻¹ * L (c * etaA ^ (2 ^ kY)) := by rw [hscalarL]
            _ = T (etaA ^ (2 ^ kY)) := (hT _).symm
        have hrhoA_pow : rhoA ^ (2 ^ kY) ≠ 0 := pow_ne_zero _ hrhoA
        have hrhoY_pow : rhoY ^ (2 ^ kA) ≠ 0 := pow_ne_zero _ hrhoY
        have hR : T (rhoA ^ (2 ^ kY)) ≠ 0 := by
          intro hzero
          apply hrhoA_pow
          apply T.injective
          simpa using hzero
        have hRorder :
            orderOf (Units.mk0 (T (rhoA ^ (2 ^ kY))) hR) =
              2 ^ nA - 1 := by
          let eUnits : (BinaryGaloisField nA)ˣ ≃*
              (BinaryGaloisField nA)ˣ := Units.mapEquiv T.toMulEquiv
          have hunit :
              Units.mk0 (T (rhoA ^ (2 ^ kY))) hR =
                eUnits (Units.mk0 (rhoA ^ (2 ^ kY)) hrhoA_pow) := by
            apply Units.ext
            rfl
          calc
            orderOf (Units.mk0 (T (rhoA ^ (2 ^ kY))) hR) =
                orderOf (eUnits
                  (Units.mk0 (rhoA ^ (2 ^ kY)) hrhoA_pow)) := by rw [hunit]
            _ = orderOf (Units.mk0 (rhoA ^ (2 ^ kY)) hrhoA_pow) :=
              eUnits.orderOf_eq _
            _ = 2 ^ nA - 1 :=
              lemma13_orderOf_twoPow_of_primitive
                nA kY hnA rhoA hrhoA hrhoA_order
        have hSorder :
            orderOf (Units.mk0 (rhoY ^ (2 ^ kA)) hrhoY_pow) =
              2 ^ nA - 1 :=
          lemma13_orderOf_twoPow_of_primitive
            nA kA hnA rhoY hrhoY hrhoY_order
        refine lemma13_jacobi_spectral_contradiction nA hnA
          (T (rhoA ^ (2 ^ kY))) (rhoY ^ (2 ^ kA))
          (etaY ^ (2 ^ kA)) (T (sigmaA (rhoA ^ (2 ^ kY))))
          (sigmaY (rhoY ^ (2 ^ kA))) hR hrhoY_pow hRorder hSorder
            ?_ ?_ ?_
        · simpa only [hT_eta] using hscalar
        · simpa only [hT_eta] using
            (lemma13_transport_spectral_branch
              nA kY T sigmaA etaA rhoA hbranchA)
        · simpa only [RingEquiv.refl_apply] using
            (lemma13_transport_spectral_branch
              nA kA (RingEquiv.refl _) sigmaY etaY rhoY hbranchY)
      exact hexponentFourCase
  have hlongInduction :
      ∀ n : ℕ, ∀ {Q : Type u} [Group Q] [MulDistribMulAction X Q],
        IsSuzukiTwoGroup Q → IsCyclic X → FaithfulSMul X Q →
        ActionRegularOn X Q (involutions Q) →
        (∀ x : Q, x ∈ involutions Q →
          ∀ y : Q, y ∈ involutions Q → ∃ k : X, y = k • x) →
        (∀ p : ℕ, p.Prime → p ∣ Nat.card X →
          p ∣ Nat.card {x : Q // x ∈ involutions Q}) →
        Nat.card Q = n →
        (∃ m : ℕ, 3 < m ∧ OmegaLength X Q m) → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro Q _ _ hQ hXcyclic hXfaithful hXregular hXtrans
          hXprimeSupport hQcard hlong
        rcases hlong with ⟨m, hm, hLen⟩
        by_cases hm4 : m = 4
        · subst m
          exact hlengthFourImpossible hQ hXcyclic hXfaithful hXregular
            hXtrans hXprimeSupport hLen
        have hm5 : 5 ≤ m := by omega
        rcases hLen with ⟨subgroups, htop, hbot, hle, hsteps⟩
        let H : Subgroup Q := subgroups ⟨1, by omega⟩
        have hfirst := hsteps ⟨0, by omega⟩
        change
          subgroups ⟨1, by omega⟩ < subgroups ⟨0, by omega⟩ ∧
            (subgroups ⟨0, by omega⟩).Normal ∧
            (subgroups ⟨1, by omega⟩).Normal ∧
            IsXInvariantSubgroup X (subgroups ⟨0, by omega⟩) ∧
            IsXInvariantSubgroup X (subgroups ⟨1, by omega⟩) ∧ _ at hfirst
        have hH_normal : H.Normal := hfirst.2.2.1
        have hH_X : IsXInvariantSubgroup X H := hfirst.2.2.2.2.1
        have hH_lt_top : H < (⊤ : Subgroup Q) := by
          simpa [H, htop] using hfirst.1
        have hH_ne_bot : H ≠ ⊥ := by
          have hsecond := (hsteps ⟨1, by omega⟩).1
          change subgroups ⟨2, by omega⟩ < subgroups ⟨1, by omega⟩ at hsecond
          exact ne_of_gt (lt_of_le_of_lt bot_le (by simpa [H] using hsecond))
        have hH_noncomm : ¬ IsMulCommutative H := by
          intro hHcomm
          have hHmax : ∀ B : Subgroup Q, B.Normal → IsMulCommutative B →
              IsXInvariantSubgroup X B → H < B → False := by
            intro B hBnormal hBcomm hB_X hHB
            rcases hfirst.2.2.2.2.2 B hBnormal hB_X
                (by simpa [H] using hHB.le)
                (by change B ≤ subgroups 0; rw [htop]; exact le_top) with hBH | hBtop
            · have hBH' : B = H := by simpa [H] using hBH
              exact (ne_of_gt hHB) hBH'
            · have hBtop' : B = (⊤ : Subgroup Q) := by
                simpa [htop] using hBtop
              apply hQ.2.1
              let : IsMulCommutative B := hBcomm
              refine IsMulCommutative.mk <| Std.Commutative.mk <| fun x y => ?_
              let bx : B := ⟨x, by rw [hBtop']; trivial⟩
              let by' : B := ⟨y, by rw [hBtop']; trivial⟩
              simpa [bx, by'] using congrArg Subtype.val (mul_comm bx by')
          have hExp : ∀ x : H, x ^ 4 = 1 :=
            (lemma9_maximal_abelian_contains_frattini
              hQ hXcyclic hXfaithful hXtrans hH_normal hHcomm hH_X hHmax).1
          rcases lemma1_abelian_invariant_homocyclic
              hQ hXtrans hHcomm hH_X with ⟨e, r, ⟨phi⟩, hpower⟩
          let : Nontrivial H :=
            (Subgroup.nontrivial_iff_ne_bot H).mpr hH_ne_bot
          have hr : 0 < r := by
            apply Nat.pos_of_ne_zero
            intro hr0
            subst r
            have htarget :
                Nontrivial (Multiplicative (Fin 0 → ZMod (2 ^ e))) :=
              (Equiv.nontrivial_congr phi.toEquiv).mp inferInstance
            exact (not_nontrivial_iff_subsingleton.mpr inferInstance) htarget
          have he : e ≤ 2 := by
            let i0 : Fin r := ⟨0, hr⟩
            let basis : Fin r → ZMod (2 ^ e) := Pi.single i0 1
            let x : H := phi.symm (Multiplicative.ofAdd basis)
            have hx4 : x ^ 4 = 1 := hExp x
            have htarget : (Multiplicative.ofAdd basis) ^ 4 = 1 := by
              simpa [x] using congrArg phi hx4
            have hi := congrArg
              (fun z : Multiplicative (Fin r → ZMod (2 ^ e)) => z.toAdd i0)
              htarget
            have hcast : ((4 : ℕ) : ZMod (2 ^ e)) = 0 := by
              simpa [basis, Pi.single_eq_same, nsmul_eq_mul] using hi
            have hdvd : 2 ^ e ∣ 4 :=
              (ZMod.natCast_eq_zero_iff 4 (2 ^ e)).mp hcast
            have hdvd' : 2 ^ e ∣ 2 ^ 2 := by simpa using hdvd
            exact (Nat.pow_dvd_pow_iff_le_right' (b := 0)).mp hdvd'
          let B2 : Subgroup Q := subgroups ⟨2, by omega⟩
          let B3 : Subgroup Q := subgroups ⟨3, by omega⟩
          let B4 : Subgroup Q := subgroups ⟨4, by omega⟩
          have hB2_lt : B2 < H := by
            have hstep := (hsteps ⟨1, by omega⟩).1
            change subgroups ⟨2, by omega⟩ <
              subgroups ⟨1, by omega⟩ at hstep
            simpa only [B2, H] using hstep
          have hB3_lt : B3 < B2 := by
            have hstep := (hsteps ⟨2, by omega⟩).1
            change subgroups ⟨3, by omega⟩ <
              subgroups ⟨2, by omega⟩ at hstep
            simpa only [B3, B2] using hstep
          have hB4_lt : B4 < B3 := by
            have hstep := (hsteps ⟨3, by omega⟩).1
            change subgroups ⟨4, by omega⟩ <
              subgroups ⟨3, by omega⟩ at hstep
            simpa only [B4, B3] using hstep
          have hB2_X : IsXInvariantSubgroup X B2 := by
            have hstep := (hsteps ⟨1, by omega⟩).2.2.2.2.1
            change IsXInvariantSubgroup X
              (subgroups ⟨2, by omega⟩) at hstep
            simpa only [B2] using hstep
          have hB3_X : IsXInvariantSubgroup X B3 := by
            have hstep := (hsteps ⟨2, by omega⟩).2.2.2.2.1
            change IsXInvariantSubgroup X
              (subgroups ⟨3, by omega⟩) at hstep
            simpa only [B3] using hstep
          have hB4_X : IsXInvariantSubgroup X B4 := by
            have hstep := (hsteps ⟨3, by omega⟩).2.2.2.2.1
            change IsXInvariantSubgroup X
              (subgroups ⟨4, by omega⟩) at hstep
            simpa only [B4] using hstep
          let Pow (s : ℕ) : Subgroup Q := Subgroup.closure
            {x : Q | ∃ a : H, (a : Q) ^ (2 ^ s) = x}
          obtain ⟨sH, hsH_le, hsH⟩ := hpower H le_rfl hH_X
          obtain ⟨s2, hs2_le, hs2⟩ := hpower B2 hB2_lt.le hB2_X
          obtain ⟨s3, hs3_le, hs3⟩ :=
            hpower B3 (hB3_lt.le.trans hB2_lt.le) hB3_X
          obtain ⟨s4, hs4_le, hs4⟩ :=
            hpower B4 (hB4_lt.le.trans (hB3_lt.le.trans hB2_lt.le)) hB4_X
          have hsH' : H = Pow sH := by simpa [Pow] using hsH
          have hs2' : B2 = Pow s2 := by simpa [Pow] using hs2
          have hs3' : B3 = Pow s3 := by simpa [Pow] using hs3
          have hs4' : B4 = Pow s4 := by simpa [Pow] using hs4
          have hsH2 : sH ≠ s2 := by
            intro hs
            apply (ne_of_gt hB2_lt)
            rw [hsH', hs2', hs]
          have hsH3 : sH ≠ s3 := by
            intro hs
            apply (ne_of_gt (hB3_lt.trans hB2_lt))
            rw [hsH', hs3', hs]
          have hsH4 : sH ≠ s4 := by
            intro hs
            apply (ne_of_gt (hB4_lt.trans (hB3_lt.trans hB2_lt)))
            rw [hsH', hs4', hs]
          have hs23 : s2 ≠ s3 := by
            intro hs
            apply (ne_of_gt hB3_lt)
            rw [hs2', hs3', hs]
          have hs24 : s2 ≠ s4 := by
            intro hs
            apply (ne_of_gt (hB4_lt.trans hB3_lt))
            rw [hs2', hs4', hs]
          have hs34 : s3 ≠ s4 := by
            intro hs
            apply (ne_of_gt hB4_lt)
            rw [hs3', hs4', hs]
          omega
        let : Finite Q := finite_of_isSuzukiTwoGroup hQ
        let : MulDistribMulAction X H :=
          { smul := fun x a => ⟨x • (a : Q), (hH_X x (a : Q)).mp a.property⟩
            one_smul := fun a => Subtype.ext (one_smul X (a : Q))
            mul_smul := fun x y a => Subtype.ext (mul_smul x y (a : Q))
            smul_mul := fun x a b => Subtype.ext (smul_mul' x (a : Q) (b : Q))
            smul_one := fun x => Subtype.ext (smul_one x) }
        have hAllInv : ∀ a : Q, IsInvolution a → a ∈ H :=
          lemma1_involutions_mem_of_nontrivial_invariant
            hQ hXtrans hH_X hH_ne_bot
        have hH_regular : ActionRegularOn X H (involutions H) := by
          constructor
          · intro x hx k
            have hxQ : IsInvolution (x : Q) :=
              ⟨fun hx1 => hx.ne_one (Subtype.ext hx1),
                congrArg Subtype.val hx.sq_eq_one⟩
            have hkQ := hXregular.1 (x : Q) hxQ k
            exact ⟨fun hk1 => hkQ.ne_one (congrArg Subtype.val hk1),
              Subtype.ext hkQ.sq_eq_one⟩
          · intro x hx y hy
            have hxQ : IsInvolution (x : Q) :=
              ⟨fun hx1 => hx.ne_one (Subtype.ext hx1),
                congrArg Subtype.val hx.sq_eq_one⟩
            have hyQ : IsInvolution (y : Q) :=
              ⟨fun hy1 => hy.ne_one (Subtype.ext hy1),
                congrArg Subtype.val hy.sq_eq_one⟩
            rcases hXregular.2 (x : Q) hxQ (y : Q) hyQ with
              ⟨k, hk, hunique⟩
            refine ⟨k, Subtype.ext hk, ?_⟩
            intro l hl
            exact hunique l (congrArg Subtype.val hl)
        have hH_faithful : FaithfulSMul X H := by
          rw [faithfulSMul_iff]
          intro k hkfix
          rcases hQ.2.2.1 with ⟨x, _y, hx, _hy, _hxy⟩
          let xH : H := ⟨x, hAllInv x hx⟩
          have hxH : IsInvolution xH :=
            ⟨fun hx1 => hx.ne_one (congrArg Subtype.val hx1),
              Subtype.ext hx.sq_eq_one⟩
          have hfix : k • xH = xH := hkfix xH
          rcases hH_regular.2 xH hxH xH hxH with ⟨z, _hz, hunique⟩
          exact (hunique k hfix.symm).trans (hunique 1 (by simp)).symm
        have hH_trans : ∀ x : H, x ∈ involutions H →
            ∀ y : H, y ∈ involutions H → ∃ k : X, y = k • x := by
          intro x hx y hy
          rcases hH_regular.2 x hx y hy with ⟨k, hk, _hunique⟩
          exact ⟨k, hk⟩
        have hH_primeSupport : ∀ p : ℕ, p.Prime → p ∣ Nat.card X →
            p ∣ Nat.card {x : H // x ∈ involutions H} := by
          let e : {x : Q // x ∈ involutions Q} ≃
              {x : H // x ∈ involutions H} :=
            { toFun := fun x =>
                ⟨⟨x.1, hAllInv x.1 x.2⟩,
                  ⟨fun hx1 => x.2.ne_one (congrArg Subtype.val hx1),
                    Subtype.ext x.2.sq_eq_one⟩⟩
              invFun := fun x =>
                ⟨x.1.1,
                  ⟨fun hx1 => x.2.ne_one (Subtype.ext hx1),
                    congrArg Subtype.val x.2.sq_eq_one⟩⟩
              left_inv := fun x => Subtype.ext rfl
              right_inv := fun x => Subtype.ext (Subtype.ext rfl) }
          have hcard : Nat.card {x : Q // x ∈ involutions Q} =
              Nat.card {x : H // x ∈ involutions H} := Nat.card_congr e
          intro p hp hpdiv
          rw [← hcard]
          exact hXprimeSupport p hp hpdiv
        have hH_suzuki : IsSuzukiTwoGroup H := by
          have hpow : ∃ r : ℕ, Nat.card (⊤ : Subgroup H) = 2 ^ r := by
            obtain ⟨r, hr⟩ :=
              (isPGroup_of_isSuzukiTwoGroup hQ).to_subgroup H |>.exists_card_eq
            exact ⟨r, by simpa using hr⟩
          have htwo : ∃ x y : H,
              IsInvolution x ∧ IsInvolution y ∧ x ≠ y := by
            rcases hQ.2.2.1 with ⟨x, y, hx, hy, hxy⟩
            let xH : H := ⟨x, hAllInv x hx⟩
            let yH : H := ⟨y, hAllInv y hy⟩
            have hxH : IsInvolution xH :=
              ⟨fun hx1 => hx.ne_one (congrArg Subtype.val hx1),
                Subtype.ext hx.sq_eq_one⟩
            have hyH : IsInvolution yH :=
              ⟨fun hy1 => hy.ne_one (congrArg Subtype.val hy1),
                Subtype.ext hy.sq_eq_one⟩
            exact ⟨xH, yH, hxH, hyH,
              fun hxyH => hxy (congrArg Subtype.val hxyH)⟩
          exact ⟨hpow, hH_noncomm, htwo,
            ⟨X, inferInstance, inferInstance, hXcyclic, hH_faithful, hH_regular⟩⟩
        have hH_long : ∃ ell : ℕ, 3 < ell ∧ OmegaLength X H ell := by
          let B2Q : Subgroup Q := subgroups ⟨2, by omega⟩
          let B3Q : Subgroup Q := subgroups ⟨3, by omega⟩
          let B4Q : Subgroup Q := subgroups ⟨4, by omega⟩
          let B5Q : Subgroup Q := subgroups ⟨5, by omega⟩
          have hB2Q_lt : B2Q < H := by
            have hstep := (hsteps ⟨1, by omega⟩).1
            change subgroups ⟨2, by omega⟩ <
              subgroups ⟨1, by omega⟩ at hstep
            simpa only [B2Q, H] using hstep
          have hB3Q_lt : B3Q < B2Q := by
            have hstep := (hsteps ⟨2, by omega⟩).1
            change subgroups ⟨3, by omega⟩ <
              subgroups ⟨2, by omega⟩ at hstep
            simpa only [B3Q, B2Q] using hstep
          have hB4Q_lt : B4Q < B3Q := by
            have hstep := (hsteps ⟨3, by omega⟩).1
            change subgroups ⟨4, by omega⟩ <
              subgroups ⟨3, by omega⟩ at hstep
            simpa only [B4Q, B3Q] using hstep
          have hB5Q_lt : B5Q < B4Q := by
            have hstep := (hsteps ⟨4, by omega⟩).1
            change subgroups ⟨5, by omega⟩ <
              subgroups ⟨4, by omega⟩ at hstep
            simpa only [B5Q, B4Q] using hstep
          have hB3Q_le_H : B3Q ≤ H := hB3Q_lt.le.trans hB2Q_lt.le
          have hB4Q_le_H : B4Q ≤ H := hB4Q_lt.le.trans hB3Q_le_H
          let B2 : Subgroup H := B2Q.subgroupOf H
          let B3 : Subgroup H := B3Q.subgroupOf H
          let B4 : Subgroup H := B4Q.subgroupOf H
          have subgroupOf_lt_subgroupOf
              {C D : Subgroup Q} (hC : C ≤ H) (hD : D ≤ H)
              (hCD : C < D) : C.subgroupOf H < D.subgroupOf H := by
            refine lt_of_le_of_ne ?_ ?_
            · intro x hx
              exact hCD.le hx
            · intro heq
              rcases SetLike.exists_of_lt hCD with ⟨x, hxD, hxC⟩
              let xH : H := ⟨x, hD hxD⟩
              have hxD' : xH ∈ D.subgroupOf H := hxD
              have hxC' : xH ∈ C.subgroupOf H := by rw [heq]; exact hxD'
              exact hxC hxC'
          have hB2_lt_top : B2 < (⊤ : Subgroup H) := by
            have h := subgroupOf_lt_subgroupOf hB2Q_lt.le le_rfl hB2Q_lt
            simpa [B2] using h
          have hB3_lt_B2 : B3 < B2 :=
            subgroupOf_lt_subgroupOf hB3Q_le_H hB2Q_lt.le hB3Q_lt
          have hB4_lt_B3 : B4 < B3 :=
            subgroupOf_lt_subgroupOf hB4Q_le_H hB3Q_le_H hB4Q_lt
          have hB4_ne_bot : B4 ≠ ⊥ := by
            rcases SetLike.exists_of_lt hB5Q_lt with ⟨x, hxB4, hxB5⟩
            have hx_ne_one : x ≠ 1 := by
              intro hx
              subst x
              exact hxB5 B5Q.one_mem
            let xH : H := ⟨x, hB4Q_le_H hxB4⟩
            intro hB4bot
            have hxBot : xH ∈ (⊥ : Subgroup H) := by
              rw [← hB4bot]
              exact (show (xH : Q) ∈ B4Q from hxB4)
            have hxH_one := Subgroup.mem_bot.mp hxBot
            exact hx_ne_one (by
              simpa [xH] using congrArg Subtype.val hxH_one)
          have hbot_lt_B4 : (⊥ : Subgroup H) < B4 :=
            bot_lt_iff_ne_bot.mpr hB4_ne_bot
          have hB2Q_normal : B2Q.Normal := by
            have hstep := (hsteps ⟨1, by omega⟩).2.2.1
            change (subgroups ⟨2, by omega⟩).Normal at hstep
            simpa only [B2Q] using hstep
          have hB3Q_normal : B3Q.Normal := by
            have hstep := (hsteps ⟨2, by omega⟩).2.2.1
            change (subgroups ⟨3, by omega⟩).Normal at hstep
            simpa only [B3Q] using hstep
          have hB4Q_normal : B4Q.Normal := by
            have hstep := (hsteps ⟨3, by omega⟩).2.2.1
            change (subgroups ⟨4, by omega⟩).Normal at hstep
            simpa only [B4Q] using hstep
          have hB2_normal : B2.Normal := by
            rw [Subgroup.normal_subgroupOf_iff hB2Q_lt.le]
            intro b k hb _hk
            exact hB2Q_normal.conj_mem b hb k
          have hB3_normal : B3.Normal := by
            rw [Subgroup.normal_subgroupOf_iff hB3Q_le_H]
            intro b k hb _hk
            exact hB3Q_normal.conj_mem b hb k
          have hB4_normal : B4.Normal := by
            rw [Subgroup.normal_subgroupOf_iff hB4Q_le_H]
            intro b k hb _hk
            exact hB4Q_normal.conj_mem b hb k
          have hB2Q_X : IsXInvariantSubgroup X B2Q := by
            have hstep := (hsteps ⟨1, by omega⟩).2.2.2.2.1
            change IsXInvariantSubgroup X
              (subgroups ⟨2, by omega⟩) at hstep
            simpa only [B2Q] using hstep
          have hB3Q_X : IsXInvariantSubgroup X B3Q := by
            have hstep := (hsteps ⟨2, by omega⟩).2.2.2.2.1
            change IsXInvariantSubgroup X
              (subgroups ⟨3, by omega⟩) at hstep
            simpa only [B3Q] using hstep
          have hB4Q_X : IsXInvariantSubgroup X B4Q := by
            have hstep := (hsteps ⟨3, by omega⟩).2.2.2.2.1
            change IsXInvariantSubgroup X
              (subgroups ⟨4, by omega⟩) at hstep
            simpa only [B4Q] using hstep
          have hB2_X : IsXInvariantSubgroup X B2 := by
            intro x b
            exact hB2Q_X x (b : Q)
          have hB3_X : IsXInvariantSubgroup X B3 := by
            intro x b
            exact hB3Q_X x (b : Q)
          have hB4_X : IsXInvariantSubgroup X B4 := by
            intro x b
            exact hB4Q_X x (b : Q)
          have htop_X : IsXInvariantSubgroup X (⊤ : Subgroup H) := by
            intro x a
            simp
          have hbot_X : IsXInvariantSubgroup X (⊥ : Subgroup H) := by
            intro x a
            constructor
            · intro ha
              rw [Subgroup.mem_bot.mp ha]
              simp
            · intro ha
              have h := congrArg (fun t : H => x⁻¹ • t)
                (Subgroup.mem_bot.mp ha)
              apply Subgroup.mem_bot.mpr
              simpa [smul_smul] using h
          let α := {C : Subgroup H // C.Normal ∧ IsXInvariantSubgroup X C}
          let : BoundedOrder α := {
            top := ⟨⊤, inferInstance, htop_X⟩
            le_top := fun C => show C.1 ≤ (⊤ : Subgroup H) from le_top
            bot := ⟨⊥, inferInstance, hbot_X⟩
            bot_le := fun C => show (⊥ : Subgroup H) ≤ C.1 from bot_le }
          let : Finite α := by
            let f : α → Set H := fun C => (C.1 : Set H)
            have hf : Function.Injective f := by
              intro C D hCD
              apply Subtype.ext
              ext x
              exact iff_of_eq (congr_fun hCD x)
            exact Finite.of_injective f hf
          let a4 : α := ⟨B4, hB4_normal, hB4_X⟩
          let a3 : α := ⟨B3, hB3_normal, hB3_X⟩
          let a2 : α := ⟨B2, hB2_normal, hB2_X⟩
          have ha4 : (⊥ : α) < a4 := hbot_lt_B4
          have ha3 : a4 < a3 := hB4_lt_B3
          have ha2 : a3 < a2 := hB3_lt_B2
          have hatop : a2 < (⊤ : α) := hB2_lt_top
          let s0 : LTSeries α := RelSeries.singleton _ (⊥ : α)
          let s1 : LTSeries α := s0.snoc a4 (by simpa [s0] using ha4)
          let s2 : LTSeries α := s1.snoc a3 (by simpa [s1] using ha3)
          let s3 : LTSeries α := s2.snoc a2 (by simpa [s2] using ha2)
          let s4 : LTSeries α := s3.snoc (⊤ : α) (by simpa [s3] using hatop)
          obtain ⟨t, i, _hit, hhead, hlast⟩ :=
            LTSeries.exists_relSeries_covBy_and_head_eq_bot_and_last_eq_bot s4
          have hs4_length : s4.length = 4 := by simp [s4, s3, s2, s1, s0]
          have ht_length : 4 ≤ t.length := by
            have hi := Fintype.card_le_of_injective i i.injective
            simp only [Fintype.card_fin] at hi
            rw [hs4_length] at hi
            omega
          refine ⟨t.length, by omega, fun j => ((t.reverse j).1 : Subgroup H),
            ?_, ?_, ?_, ?_⟩
          · have hTop : t.reverse.head = (⊤ : α) := by
              simpa using hlast
            change (t.reverse.head.1 : Subgroup H) = ⊤
            exact congrArg Subtype.val hTop
          · have hBot : t.reverse.last = (⊥ : α) := by
              simpa using hhead
            change (t.reverse.last.1 : Subgroup H) = ⊥
            exact congrArg Subtype.val hBot
          · intro j
            have hcov : t.reverse j.succ ⋖ t.reverse j.castSucc := by
              simpa using (t.reverse.step j)
            exact hcov.le
          · intro j
            have hcov : t.reverse j.succ ⋖ t.reverse j.castSucc := by
              simpa using (t.reverse.step j)
            refine ⟨hcov.lt, (t.reverse j.castSucc).2.1,
              (t.reverse j.succ).2.1, (t.reverse j.castSucc).2.2,
              (t.reverse j.succ).2.2, ?_⟩
            intro L hLnormal hLX hML hLN
            let Lx : α := ⟨L, hLnormal, hLX⟩
            have hMLx : t.reverse j.succ ≤ Lx := hML
            have hLNx : Lx ≤ t.reverse j.castSucc := hLN
            rcases hcov.wcovBy.eq_or_eq hMLx hLNx with hcase | hcase
            · left
              exact congrArg Subtype.val hcase
            · right
              exact congrArg Subtype.val hcase
        have hH_card_lt : Nat.card H < Nat.card Q := by
          have hnot : ¬ (⊤ : Subgroup Q) ≤ H := not_le_of_gt hH_lt_top
          rw [SetLike.not_le_iff_exists] at hnot
          rcases hnot with ⟨q, _hqtop, hqH⟩
          simpa using (Finite.card_subtype_lt hqH)
        have hH_card_lt_n : Nat.card H < n := by
          simpa [← hQcard] using hH_card_lt
        exact ih (Nat.card H) hH_card_lt_n hH_suzuki hXcyclic hH_faithful
          hH_regular hH_trans hH_primeSupport rfl hH_long
  have hreduceLongToFour :
      (∃ m : ℕ, 3 < m ∧ OmegaLength X P m) → False :=
    hlongInduction (Nat.card P) _hP _hXcyclic _hXfaithful _hXregular
      _hXtrans _hXprimeSupport rfl
  exact hreduceLongToFour
end Higman
end External
end CFSG.BenderSuzuki
