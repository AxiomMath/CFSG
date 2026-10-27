module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieCtr
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieFus
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieVD
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieFP
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieRel

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL5

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.Quasithin.H13.Sec53F.Unit CFSG.LocalAnalysis.EvenBN.U5
  CFSG.Quasithin.H13.F431.Un CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

include h in
theorem exists_unOutRel5 (hf : f = 2) {K₀ : Subgroup (MulAut (hypPSU h 2 1))}
    (F₂ : Subgroup (K ≃+* K)) (hinn : Pi h ≤ K₀)
    (hev : ¬ Odd (Nat.card K₀ / Nat.card (hypPSU h 2 1)))
    (hT : IsSylowTwoOf (Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F₂) K₀) :
    ∃ (g z t : MulAut (hypPSU h 2 1)) (V : Subgroup (MulAut (hypPSU h 2 1))),
      UnOutRel K₀ (Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) F₂)
        (Ssd5 h (hypProjUnitriangular h 2 1) (fStab5_U h) ⊥) g
        (K₀ ⊓ autStab (u5PtP h)) (K₀ ⊓ autStab (u5LnP h)) z t V := by
  have hf2 : 2 ≤ f := by omega
  have hbar : bar5 h ∈ F₂ := bar5_mem_of_sylow h hinn hev hT
  obtain ⟨hUT, hTstd⟩ := Ssd5_std h F₂
  have hSU := Ssd5_bot_eq_Uh h
  refine ⟨fa5 h (bar5 h), cj5 h (z5Y h), cj5 h (t5Y h), Vh h, ?_⟩
  exact
  { sylow := hT
    N_le := inf_le_left
    N'_le := inf_le_left
    T_le := le_inf hT.1 (Ssd5_le_autStab_Pt h F₂)
    T_le' := le_inf hT.1 (Ssd5_le_autStab_Ln h F₂)
    S_le := Ssd5_mono h le_rfl bot_le
    S_norm := Ssd5_le_normalizer_bot h F₂
    cyc := Ssd5_cyc h F₂
    z_mem := cj5_z5Y_mem_S h
    z_two := orderOf_cj5_z5Y h
    t_mem := cj5_t5Y_mem_S h
    t_two := orderOf_cj5_t5Y h
    zt_not_conj := fun k _ => zt_not_conj5 h k
    z_ZN := z_ZN5 h hf2 hinn
    Z_sq := fun x hx => Z_sq5 h hf2 hinn hx
    ZN_trans := fun x hx hx1 => ZN_trans5 h hf2 hinn hx hx1
    center_T := fun w hw hc hw1 => center_T5 h hf2 hinn hT.2.1 hw hc hw1
    fusion := fusion5 h hf2 hinn F₂
    V_le := hSU ▸ un5_V_le h
    V_ab := fun a ha b hb => un5_V_ab h ha hb
    V_sq := fun a ha => un5_V_sq h ha
    V_zt := un5_V_zt h
    V_eq := un5_V_eq h hf2 hinn
    V_unique := fun E hE hab hsq hcard => un5_V_unique h hf2 hUT hTstd E hE hab hsq hcard
    f_mem := fa5_mem_Ssd5 h hbar
    f_not := fun hmem => fld5_bar_ne_one h
      (fa5_mem_Dlin h (Pi_le_Dlin (Uh_le_Pi (hSU ▸ hmem))))
    f_sq := by rw [sq, fa5_mul, fld5_bar_mul_self, fa5_one]
    Tf_lt_z := fp5_Tf_lt_z h hf2 F₂ hbar
    Tf_lt_t := fp5_Tf_lt_t h hf2 F₂ hbar
    Sylow_Tf := fp5_Sylow_Tf h hf2 hinn F₂ hbar hT
    W_le := hSU ▸ un5_W_le h hUT hTstd
    W_ne := fp5_W_ne h hf2 hinn F₂ hbar
    W_cls := fun y hy hk => by
      obtain ⟨k, -, hk⟩ := hk
      exact fp5_W_cls h hf2 hinn F₂ hbar hy ⟨k, hk⟩ }

end CFSG.Quasithin.H13.F431.Un.OL5
