module

public import CFSG.Quasithin.MS93.S38ETypes
public import CFSG.Quasithin.MS93.S38EBNat
public import CFSG.Quasithin.MS93.S38OffHatMod
public import CFSG.Quasithin.MS93.S38EIdent

public section

namespace CFSG.Quasithin.MS93.S38E

open CFSG.Quasithin CFSG.Quasithin.Fan86.Univ CFSG.Quasithin.MS93 CFSG.QuasithinUnique
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

namespace EndSetup

variable (h : PUHyp M T L) {α' : Vtx (puAmalgam h.le)} {e : ℕ}
  (hS : EndSetup (Vv (puAmalgam h.le) (baseA _)) (stab _ (baseA _)) (puTrans h.le L (baseA _))
    (Qv _ (baseB _)) (Qv _ (baseA _)) (XM _ α') e)
  (lam : ↥⁅Vv (puAmalgam h.le) (baseA _), Vv (puAmalgam h.le) (baseA _)⁆ →* ℂˣ)
  (hlam1 : ∀ c : ↥⁅Vv (puAmalgam h.le) (baseA _), Vv (puAmalgam h.le) (baseA _)⁆,
    (c : (puAmalgam h.le).Universal) ∈
      ⁅⁅Vv (puAmalgam h.le) (baseA _), Vv (puAmalgam h.le) (baseA _)⁆, Qv _ (baseB _)⁆ →
      lam c = 1)
  (hirr : IrrSec (hS.rho lam hlam1).range (commV (hS.kY lam hlam1))
    (commV (hS.kY lam hlam1) ⊓ fixV (hS.kY lam hlam1)))
include hirr

omit hirr in
theorem kS_le_range : hS.kS lam hlam1 ≤ (hS.secRho lam hlam1).range := Subgroup.map_le_range _ _

omit hirr in
theorem false_of_ffCaseSL3 (hK : FFCaseSL3 (IsIrrRep.imL L (hS.rhoM h lam hlam1))) : False := by
  rw [imL_rhoM] at hK
  obtain ⟨n, F, _, _, -, -, -, -, hcase⟩ := hK
  obtain ⟨E, hEK, hne⟩ := S38EB.card_commV_mul_card_fixV_ne hcase
  exact hne (hS.card_commV_mul_card_fixV_SM lam hlam1 (hEK.trans (hS.kS_le_range h lam hlam1)))

theorem false_of_ffCaseHatA6 (he2 : 2 ≤ e)
    (hK : FFCaseHatA6 (IsIrrRep.imL L (hS.rhoM h lam hlam1))) :
    False := by
  rw [imL_rhoM] at hK
  obtain ⟨h6, -, hcard, -⟩ := hK
  have hH := S38H.HatMod.of_tripleA6Six (hS.sq_SM lam hlam1) h6
  have hN : hS.eS lam hlam1 ≤ Subgroup.normalizer (hS.kS lam hlam1 : Set (MulAut _)) := by
    have := IsIrrRep.range_le_normalizer (ρ := hS.rhoM h lam hlam1) h
    rw [range_rhoM, imL_rhoM] at this
    exact (Subgroup.map_le_range _ _).trans this
  obtain ⟨-, -, hf, hle⟩ := hH.offender hN (hS.isElemAbelian2_eS lam hlam1)
    (hS.eS_ne_bot lam hlam1 hirr he2) (hS.card_le_card_eS_mul lam hlam1 hirr)
  have hdual := hS.card_commV_mul_card_fixV_SM lam hlam1 (P := hS.eS lam hlam1)
    (Subgroup.map_le_range _ _)
  have h16 : 16 ≤ Nat.card (commV (hS.eS lam hlam1)) := by
    rw [← hf]
    exact Subgroup.card_le_of_le hle
  rw [hf, hcard] at hdual
  nlinarith

theorem false_of_ffConclusion (he2 : 2 ≤ e) (hT : S32.TypeFacts)
    (hconc : FFConclusion (hS.rhoM h lam hlam1).range (IsIrrRep.imL L (hS.rhoM h lam hlam1)))
    (htype : Nat.card (S32.Lstar L) = 360 ∨
      ∃ m, 1 ≤ m ∧ Nat.card (S32.Lstar L) = CFSG.Open.ordA 2 (2 ^ m))
    (hD6 : Nat.card (S32.Lstar L) = 360 → AlternatingNatural (hS.kS lam hlam1) ⊤ ⊥ 6 → False) :
    False := by
  have hρ := hS.isIrrRep_rhoM h lam hlam1 hirr
  obtain ⟨-, -, hcase, -⟩ := hconc
  rcases hcase with hsl3 | hhat | hsp4 | hg2
  · exact hS.false_of_ffCaseSL3 h lam hlam1 hsl3
  · exact hS.false_of_ffCaseHatA6 h lam hlam1 hirr he2 hhat
  · rcases hsp4 with ⟨n, hn, hbin⟩ | halt
    · have h1 := card_lstar_of_sp4Nat hρ h hn hbin
      rcases htype with h360 | ⟨m, hm, hA⟩
      · exact (S32.ordBC_two_ne (by omega)).2.1 (h1.symm.trans h360)
      · exact ordBC_two_ne_ordA_two (by omega) hm (h1.symm.trans hA)
    · have h1 := card_lstar_of_altNat hρ h halt
      rw [imL_rhoM] at halt
      exact hD6 h1 halt
  · rcases card_lstar_of_ffCaseG2 hρ h hT hg2 with ⟨n, hn, h1⟩ | h1
    · rcases htype with h360 | ⟨m, hm, hA⟩
      · exact (S32.ordG2_ne (by omega)).2.1 (h1.symm.trans h360)
      · exact ordG2_ne_ordA_two (by omega) hm (h1.symm.trans hA)
    · rcases htype with h360 | ⟨m, hm, hA⟩
      · rw [h1] at h360
        norm_num at h360
      · exact S32.ordA_two_ne_6048 hm (hA.symm.trans h1)

end EndSetup

end CFSG.Quasithin.MS93.S38E
