module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4AutSetting
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4AutLn
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4AutCard
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4HexD

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.D4Hex

section Act


noncomputable instance instMulActionAutPt : MulAction (MulAut D) (Fin 819) :=
  MulAction.compHom _ autPt

noncomputable instance instMulActionAutLn : MulAction (MulAut D) (Fin 2457) :=
  MulAction.compHom _ autLn

theorem autPt_smul_def (α : MulAut D) (p : Fin 819) : α • p = autPt α p := rfl

theorem autLn_smul_def (α : MulAut D) (l : Fin 2457) : α • l = autLn α l := rfl

theorem conj_smul_pt (g : D) (p : Fin 819) : (MulAut.conj g : MulAut D) • p = g • p := by
  rw [autPt_smul_def, autPt_conj, smul_pt_def]

theorem conj_smul_ln (g : D) (l : Fin 2457) : (MulAut.conj g : MulAut D) • l = g • l := by
  rw [autLn_smul_def, autLn_conj]
  rfl

instance instGraphActionAut : GraphAction (MulAut D) hexGraph := hexGraphAction_of (fun α p v => by
  rw [mem_hexLine_iff_lineSet, mem_hexLine_iff_lineSet]
  exact mem_lineSet_autPt_iff α p v)

instance instGraphActionK3 : GraphAction ↥(autStab d4H ⊔ autStab d4N) hexGraph :=
  ⟨fun g a b => GraphAction.adj_smul (g : MulAut D) a b⟩

instance instGraphActionInn : GraphAction ↥(MulAut.conj : D →* MulAut D).range hexGraph :=
  ⟨fun g a b => GraphAction.adj_smul (g : MulAut D) a b⟩

end Act

section Card

variable
  {D' : Type} [Group D'] (hD' : IsLieOverTwo .trialityD4 0 1 D')

include hD' in
theorem card_d3Setting_Yb_dvd : Nat.card d3Setting.Yb ∣ 3 * Nat.card D :=
  (Subgroup.card_subgroup_dvd_card (autStab d4H ⊔ autStab d4N)).trans (d4_card_aut_dvd hD')

end Card

end CFSG.Quasithin.D4Hex
