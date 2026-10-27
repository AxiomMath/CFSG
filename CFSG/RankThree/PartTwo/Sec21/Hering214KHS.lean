module

public import CFSG.RankThree.PartTwo.Sec21.Hering214KEmb
public import CFSG.RankThree.PartTwo.Sec21.Hering214KGen
public import CFSG.Sporadic.Recognition.HSPinnedIdent
public import CFSG.Sporadic.SmallOddCore.HSWordBound

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open CFSG.Blueprint CFSG.Sporadic.Recognition.HSGraph CFSG.ComponentClassification.WittDesign
open CFSG.Sporadic.Recognition.HSPinned (nonempty_mulEquiv_hs)

theorem nonempty_mulEquiv_evenSubgroup_hs :
    Nonempty (↥(evenSubgroup hexads) ≃* NativeSporadic.HS) := by
  obtain ⟨s, hs, -, hsign⟩ := hsFacts_hexads.odd
  exact nonempty_mulEquiv_hs (evenSubgroup hexads) (index_evenSubgroup ⟨s, hs, hsign⟩)

theorem exists_injective_m22_hom_evenSubgroup :
    ∃ j : ↥NativeSporadic.M22 →* ↥(evenSubgroup hexads), Function.Injective j := by
  let D : MData hexads := mdataHexads
  let j : D.carrier →* evenSubgroup hexads :=
    ((MulAction.stabilizer (autGroup hexads) (vInf : Vert hexads)).subtype.comp
      D.toStab).codRestrict (evenSubgroup hexads)
      (fun τ => MonoidHom.mem_ker.mpr (D.signHom_toStab τ))
  have hj : Function.Injective j := by
    intro τ τ' h
    have h1 : D.toStab τ = D.toStab τ' :=
      Subtype.ext (Subtype.ext
        (congrArg (fun x : evenSubgroup hexads => (x : autGroup hexads).1) h))
    apply Subtype.ext
    rw [← D.restrictΩ_toStab τ, ← D.restrictΩ_toStab τ', h1]
  exact ⟨j, hj⟩

theorem exists_injective_m22_hom_hs :
    ∃ ι : ↥NativeSporadic.M22 →* NativeSporadic.HS, Function.Injective ι := by
  obtain ⟨e⟩ := nonempty_mulEquiv_evenSubgroup_hs
  obtain ⟨j, hj⟩ := exists_injective_m22_hom_evenSubgroup
  exact ⟨(e : ↥(evenSubgroup hexads) →* NativeSporadic.HS).comp j, e.injective.comp hj⟩

theorem hs_center_eq_bot :
    Subgroup.center NativeSporadic.HS = ⊥ := by
  haveI : Finite NativeSporadic.HS := CFSG.Sporadic.HS.fam_hs_simplicity.1
  refine center_eq_bot_of_simple_of_not_prime CFSG.Sporadic.HS.isSimpleGroup_HS ?_
  rw [CFSG.Sporadic.HS.card_HS]
  norm_num

theorem nonempty_mulAut_equiv_hs :
    Nonempty (MulAut NativeSporadic.HS ≃* MulAut CFSG.Sporadic.Schreier.hsP) :=
  ⟨@MulAut.congr NativeSporadic.HS Units.instGroup _ _ CFSG.Sporadic.Schreier.hsPermEquiv⟩

theorem hs_mulAut_card :
    Nat.card (MulAut NativeSporadic.HS) ≤ 2 * Nat.card NativeSporadic.HS := by
  obtain ⟨e⟩ := nonempty_mulAut_equiv_hs
  have h1 := CFSG.Sporadic.SmallOddCore.hs_card_mulAut_le
  rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.HS.card_HS]
  omega

theorem eInvNine_hs :
    EInvNine NativeSporadic.HS := by
  haveI : Finite NativeSporadic.HS := CFSG.Sporadic.HS.fam_hs_simplicity.1
  obtain ⟨ι, hι⟩ := exists_injective_m22_hom_hs
  have hZ := hs_center_eq_bot
  have hY : Nat.card NativeSporadic.HS = 44352000 := CFSG.Sporadic.HS.card_HS
  exact eInvNine_of_m22_embedding hZ
    (fun α hα => exists_conj_of_pow_three_of_card_le hZ hs_mulAut_card hα)
    (card_sylow_three_of_padicValNat hY (by decide +kernel)) ι hι

theorem eInvNine_of_mulEquiv_hs
    {X : Type} [Group X] (e : X ≃* NativeSporadic.HS) : EInvNine X :=
  @EInvNine.of_mulEquiv X NativeSporadic.HS _ Units.instGroup e eInvNine_hs

end CFSG.RankThree.PartTwo.Sec21.Hering214
