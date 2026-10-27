module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Lemma3_4
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.MinimalNormalPSubgroupIsElementaryAbelian
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.QuotientGroup.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Faithful irreducible conjugation on a minimal normal p-subgroup
-/

namespace CFSG.Glauberman

open scoped IsMulCommutative

universe u

private theorem conjNormal_ker_eq_centralizer
    {Q : Type u} [Group Q] (H : Subgroup Q) [H.Normal] :
    (MulAut.conjNormal (H := H)).ker = Subgroup.centralizer (H : Set Q) := by
  ext q
  constructor
  · intro hq
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hact : MulAut.conjNormal (H := H) q = 1 := hq
    have heval := congrArg (fun a : MulAut H => a ⟨h, hh⟩) hact
    have hconj : q * h * q⁻¹ = h := congrArg Subtype.val heval
    calc
      h * q = (q * h * q⁻¹) * q := by rw [hconj]
      _ = q * h := by group
  · intro hq
    rw [MonoidHom.mem_ker]
    ext h
    have hcomm : (h : Q) * q = q * (h : Q) :=
      Subgroup.mem_centralizer_iff.mp hq (h : Q) h.2
    simp only [MulAut.conjNormal_apply, MulAut.one_apply]
    rw [← hcomm]
    group

private def quotientCentralizerConj
    {Q : Type u} [Group Q] (H : Subgroup Q) [H.Normal] :
    Q ⧸ Subgroup.centralizer (H : Set Q) →* MulAut H :=
  QuotientGroup.lift (Subgroup.centralizer (H : Set Q))
    (MulAut.conjNormal (H := H)) (by
      rw [← conjNormal_ker_eq_centralizer H])

private theorem quotientCentralizerConj_injective
    {Q : Type u} [Group Q] (H : Subgroup Q) [H.Normal] :
    Function.Injective (quotientCentralizerConj H) := by
  refine (MonoidHom.ker_eq_bot_iff (quotientCentralizerConj H)).mp ?_
  apply le_antisymm
  · intro z hz
    refine Quotient.inductionOn' z ?_ hz
    intro q hq
    have hqker : q ∈ (MulAut.conjNormal (H := H)).ker := by
      rw [MonoidHom.mem_ker]
      change quotientCentralizerConj H
        (QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) q) = 1
      exact hq
    have hqC : q ∈ Subgroup.centralizer (H : Set Q) := by
      rw [← conjNormal_ker_eq_centralizer H]
      exact hqker
    have hqone : QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) q = 1 :=
      (QuotientGroup.eq_one_iff q).2 hqC
    simpa [hqone]
  · exact bot_le

private def quotientCentralizerConjTagged
    {Q : Type u} [Group Q] (H : Subgroup Q) [H.Normal] :
    Q ⧸ Subgroup.centralizer (H : Set Q) →*
      MulAut (Multiplicative (Additive H)) :=
  (MulAut.congr (MulEquiv.multiplicativeAdditive H)).symm.toMonoidHom.comp
    (quotientCentralizerConj H)

private theorem quotientCentralizerConjTagged_mk'_apply
    {Q : Type u} [Group Q] (H : Subgroup Q) [H.Normal]
    (q : Q) (h : Multiplicative (Additive H)) :
    MulEquiv.multiplicativeAdditive H
        (quotientCentralizerConjTagged H
          (QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) q) h) =
      MulAut.conjNormal (H := H) q (MulEquiv.multiplicativeAdditive H h) := by
  rfl

private theorem quotientCentralizerConjTagged_injective
    {Q : Type u} [Group Q] (H : Subgroup Q) [H.Normal] :
    Function.Injective (quotientCentralizerConjTagged H) := by
  exact (MulAut.congr (MulEquiv.multiplicativeAdditive H)).symm.injective.comp
    (quotientCentralizerConj_injective H)

private theorem minimalNormal_quotientCentralizerConjTagged_irreducible
    {Q : Type u} [Group Q] [Finite Q]
    (H : Subgroup Q) [H.Normal] [IsMinimalNormal H]
    [IsMulCommutative H] :
    IrreducibleAction (V := Additive H)
      (G := Q ⧸ Subgroup.centralizer (H : Set Q))
      (quotientCentralizerConjTagged H) := by
  rw [irreducibleAction_iff]
  intro W hWinv
  let eH : Multiplicative (Additive H) ≃* H :=
    MulEquiv.multiplicativeAdditive H
  let f : Multiplicative (Additive H) →* Q := H.subtype.comp eH.toMonoidHom
  let WQ : Subgroup Q := W.map f
  have hf_inj : Function.Injective f := H.subtype_injective.comp eH.injective
  have hWQnormal : WQ.Normal := by
    refine ⟨?_⟩
    intro n hn q
    rcases Subgroup.mem_map.mp hn with ⟨w, hw, rfl⟩
    let qbar : Q ⧸ Subgroup.centralizer (H : Set Q) :=
      QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) q
    have hactmem : quotientCentralizerConjTagged H qbar w ∈ W :=
      hWinv qbar w hw
    refine Subgroup.mem_map.mpr
      ⟨quotientCentralizerConjTagged H qbar w, hactmem, ?_⟩
    have hval := congrArg Subtype.val
      (quotientCentralizerConjTagged_mk'_apply H q w)
    simpa [f, eH, qbar, MulAut.conjNormal_apply] using hval
  let : WQ.Normal := hWQnormal
  have hWQle : WQ ≤ H := by
    intro q hq
    rcases Subgroup.mem_map.mp hq with ⟨w, _hw, rfl⟩
    exact (eH w).2
  rcases IsMinimalNormal.minimal WQ hWQle with hbot | htop
  · left
    exact (Subgroup.map_eq_bot_iff_of_injective W hf_inj).mp (by
      simpa [WQ] using hbot)
  · right
    apply Subgroup.map_injective hf_inj
    have hmapTop : (⊤ : Subgroup (Multiplicative (Additive H))).map f = H := by
      ext q
      constructor
      · rintro ⟨w, _hw, rfl⟩
        exact (eH w).2
      · intro hq
        let h : H := ⟨q, hq⟩
        let w : Multiplicative (Additive H) := eH.symm h
        refine ⟨w, by trivial, ?_⟩
        simp [f, eH, w, h]
    calc
      W.map f = WQ := rfl
      _ = H := htop
      _ = (⊤ : Subgroup (Multiplicative (Additive H))).map f := hmapTop.symm

public theorem exists_minimalNormal_pSubgroup_faithful_irreducible_action
    {p : ℕ} [Fact p.Prime] {Q : Type u} [Group Q] [Finite Q]
    (H : Subgroup Q) [H.Normal] [IsMinimalNormal H]
    (hHne : H ≠ ⊥) (hHp : IsPGroup p H) :
    letI : IsElementaryAbelian p H :=
      minimalNormal_pSubgroup_isElementaryAbelian H hHne hHp
    ∃ ρ : Q ⧸ Subgroup.centralizer (H : Set Q) →*
        MulAut (Multiplicative (Additive H)),
      Function.Injective ρ ∧
        IrreducibleAction (V := Additive H)
          (G := Q ⧸ Subgroup.centralizer (H : Set Q)) ρ ∧
        ∀ (q : Q) (h : Multiplicative (Additive H)),
          MulEquiv.multiplicativeAdditive H
              (ρ (QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) q) h) =
            MulAut.conjNormal (H := H) q
              (MulEquiv.multiplicativeAdditive H h) := by
  let : IsElementaryAbelian p H :=
    minimalNormal_pSubgroup_isElementaryAbelian H hHne hHp
  let : IsMulCommutative H :=
    (inferInstance : IsElementaryAbelian p H).toIsMulCommutative
  refine ⟨quotientCentralizerConjTagged H,
    quotientCentralizerConjTagged_injective H,
    minimalNormal_quotientCentralizerConjTagged_irreducible H, ?_⟩
  exact quotientCentralizerConjTagged_mk'_apply H

end CFSG.Glauberman
