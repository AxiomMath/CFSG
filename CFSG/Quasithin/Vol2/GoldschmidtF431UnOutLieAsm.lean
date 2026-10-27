module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieSyl
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieNstD
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieFusC
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieVC
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieTD
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieWC
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieNst
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieNstC
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieRel
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieTB
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsYam

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.EvenBN.U4 CFSG.QuasithinUnique CFSG.Open
  CFSG.Quasithin CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.Un.OL

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

theorem exists_unOutRel (hf : 2 ≤ f) [IsSimpleGroup (Xg h)]
    (hY : CFSG.Quasithin.H13.Sec53F.Yam.YamStd (Xg h) (Psy h) (Pt h) (Ln h))
    (K₀ : Subgroup (MulAut (Xg h)))
    (hinn : (MulAut.conj : Xg h →* MulAut (Xg h)).range ≤ K₀)
    (hev : ¬ Odd (Nat.card K₀ / Nat.card (Xg h))) :
    ∃ (T S : Subgroup (MulAut (Xg h))) (g z t : MulAut (Xg h)) (V : Subgroup (MulAut (Xg h))),
      UnOutRel K₀ T S g (K₀ ⊓ autStab (Pt h)) (K₀ ⊓ autStab (Ln h)) z t V := by
  have hFk : ¬ Odd (Nat.card (FK h K₀)) := by
    have hpos : 0 < Nat.card (Xg h) := Nat.card_pos
    rwa [card_eq_mul_FK h hinn, Nat.mul_div_cancel_left _ hpos] at hev
  obtain ⟨F₂, hF₂, hbar, φ₀, hφ₀, hgen⟩ := exists_F2 h (FK h K₀) hFk
  rw [inf_autStab_Pt h hY.coatom₀ hinn, inf_autStab_Ln h hY.coatom₁ hinn]
  have hTK : Ssd h (Psy h) (fStab_Psy h) F₂ ≤ K₀ := Ssd_le h hinn hF₂.1
  have hz : cj h (z1X h) ∈ Ssd h (Psy h) (fStab_Psy h) ⊥ := cj_mem_Ssd h (z1X_mem_Psy h)
  have ht : cj h (z2X h) ∈ Ssd h (Psy h) (fStab_Psy h) ⊥ := cj_mem_Ssd h (z2X_mem_Psy h)
  have hZN := centerOf_perfectCore_Ssd_Pt h hf (FK h K₀)
  refine ⟨Ssd h (Psy h) (fStab_Psy h) F₂, Ssd h (Psy h) (fStab_Psy h) ⊥, fbar h,
    cj h (z1X h), cj h (z2X h), Ssd h (A1X h) (fStab_A1X h) ⊥, ?_⟩
  exact
  { sylow := isSylowTwoOf_Ssd_Psy h hinn hF₂
    N_le := Ssd_le h hinn le_rfl
    N'_le := Ssd_le h hinn le_rfl
    T_le := Ssd_mono h (Psy_le_Pt h) hF₂.1
    T_le' := Ssd_mono h (Psy_le_Ln h) hF₂.1
    S_le := Ssd_mono h le_rfl bot_le
    S_norm := Ssd_le_normalizer_bot h _ _ F₂
    cyc := ⟨fa h φ₀, fa_mem_Ssd h hφ₀, Ssd_eq_sup_zpowers h _ _ hgen⟩
    z_mem := hz
    z_two := orderOf_cj_z1X h
    t_mem := ht
    t_two := orderOf_cj_z2X h
    zt_not_conj := fun k _ => not_conj_z1X_z2X h k
    z_ZN := by
      rw [hZN]
      exact cj_z1X_mem_Ssd_ZX h ⊥
    Z_sq := fun x hx => by
      rw [hZN] at hx
      exact Ssd_ZX_sq h x hx
    ZN_trans := fun x hx hx1 => by
      rw [hZN] at hx
      exact Ssd_ZX_trans h hf _ x hx hx1
    center_T := fun w hw hc hw1 =>
      Ssd_ZX_trans h hf _ w (center_Ssd_le h hf F₂ w hw hc) hw1
    fusion := fun x hx hx2 => fusion_Ssd h F₂ (FK h K₀) x hx hx2
    V_le := Ssd_mono h (fun x hx => miyamotoA1_le_P h hx) le_rfl
    V_ab := (Ssd_A1X_elemAb h).1
    V_sq := (Ssd_A1X_elemAb h).2
    V_zt := ⟨cj_mem_Ssd h (z1X_mem_A1X h), cj_mem_Ssd h (z2X_mem_A1X h)⟩
    V_eq := by
      rw [pCoreOf_Ssd_Ln h hf]
      ext x
      constructor
      · intro hx
        exact ⟨hx, Subgroup.mem_centralizer_iff.2 fun y hy => (Ssd_A1X_elemAb h).1 y hy x hx⟩
      · exact fun hx => hx.1
    V_unique := fun E hE hab hsq hcard => V_unique h hf F₂ E hE hab hsq hcard
    f_mem := fbar_mem_Ssd h hbar
    f_not := fbar_not_mem_Ssd_bot h
    f_sq := fbar_sq h
    Tf_lt_z := Tf_lt_z h hf F₂
    Tf_lt_t := Tf_lt_t h hf F₂
    Sylow_Tf := Sylow_Tf h hf F₂ (FK h K₀) hF₂
    W_le := W_le h F₂
    W_ne := ⟨cj h (z1X h), W_ne h hf F₂, by rw [hZN]; exact cj_z1X_mem_Ssd_ZX h ⊥,
      fun e => by
        have := orderOf_cj_z1X h
        rw [e, orderOf_one] at this
        exact absurd this (by norm_num)⟩
    W_cls := fun y hy hk => by
      rw [hZN]
      obtain ⟨k, -, hk⟩ := hk
      exact W_cls h hf F₂ y hy ⟨k, hk⟩ }

end CFSG.Quasithin.H13.F431.Un
