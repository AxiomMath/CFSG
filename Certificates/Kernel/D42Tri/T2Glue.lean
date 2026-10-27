module

public import Certificates.Kernel.D42Tri.T2Rec
public import Certificates.Kernel.D42Tri.RhoGlue
public import CFSG.Certificates.Kernel.D42T2Sound
public import CFSG.ClassicalInvolution.Q3.Q3TLTO8
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.Spor.CommBaseSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD42Tri

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.CommBase
  CFSG.KC.D42T2 CertificateChecks.KernelO8 CFSG.EvenSmallLie.OmegaEight
  CFSG.HardMathSupport.Dickson.Bal207.D42Tri CFSG.Sporadic.SmallOddCore Equiv MulAction

abbrev t2p : Fin 360 := ⟨1, by norm_num⟩

abbrev t2x : Fin 360 := ⟨178, by norm_num⟩

abbrev t2y : Fin 360 := ⟨242, by norm_num⟩

theorem prep_gen {z : ℕ} (hz : z < 8) :
    CFSG.KS.Raw.Orb.PRep 360 9 (AP.S z) (gen z) := by
  have h := rep_gen (i := z) (by omega)
  rw [gen_get (by omega)] at h
  exact CFSG.KS.Raw.Orb.prep_of_rep h

theorem word_apply {W : List ℕ} (hW : lettersOK 8 W = true)
    (q : Fin 360) : wapp 9 (mask 9) AP.S W q = word gen W q :=
  wapp_eq (fun _ hz => prep_gen hz) (lettersOK_iff.1 hW) q

theorem word_mem {W : List ℕ} (hW : lettersOK 8 W = true) : word gen W ∈ omegaT := by
  unfold word
  refine omegaT.list_prod_mem fun g hg => ?_
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hg
  exact gen_mem_omegaT (lettersOK_iff.1 hW z hz)

theorem word_fix {W : List ℕ} (hW : lettersOK 8 W = true)
    {a : Fin 360} (h : Nat.beq (wapp 9 (mask 9) AP.S W a) a = true) :
    word gen W ∈ stabilizer (Perm (Fin 360)) a :=
  mem_stabilizer_iff.2 (by
    rw [Perm.smul_def]
    exact Fin.ext (by rw [← word_apply hW]; exact Nat.eq_of_beq_eq_true h))

theorem t2Words_parts : (∀ W ∈ [TD.w1, TD.w2, TD.w3, TD.w4, TD.w5, TD.w6], lettersOK 8 W = true) ∧
    (∀ W ∈ [TD.w1, TD.w2, TD.w3, TD.w4, TD.w5, TD.w6],
      Nat.beq (wapp 9 (mask 9) AP.S W 1) 1 = true) ∧
    (∀ W ∈ [TD.w3, TD.w4, TD.w5, TD.w6], Nat.beq (wapp 9 (mask 9) AP.S W 178) 178 = true) ∧
    ∀ W ∈ [TD.w5, TD.w6], Nat.beq (wapp 9 (mask 9) AP.S W 242) 242 = true := by
  have h := t2Words
  simp only [bAnd_iff, allL_iff] at h
  exact h

noncomputable abbrev om1 : Subgroup (Perm (Fin 360)) := omegaT ⊓ stabilizer (Perm (Fin 360)) t2p

noncomputable abbrev om2 : Subgroup (Perm (Fin 360)) := om1 ⊓ stabilizer (Perm (Fin 360)) t2x

noncomputable abbrev om3 : Subgroup (Perm (Fin 360)) := om2 ⊓ stabilizer (Perm (Fin 360)) t2y

theorem mem_om1 {W : List ℕ}
    (hW : W ∈ [TD.w1, TD.w2, TD.w3, TD.w4, TD.w5, TD.w6]) : word gen W ∈ om1 :=
  Subgroup.mem_inf.2 ⟨word_mem (t2Words_parts.1 W hW), word_fix (t2Words_parts.1 W hW)
    (t2Words_parts.2.1 W hW)⟩

theorem mem_om2 {W : List ℕ}
    (hW : W ∈ [TD.w3, TD.w4, TD.w5, TD.w6]) : word gen W ∈ om2 := by
  have h1 : W ∈ [TD.w1, TD.w2, TD.w3, TD.w4, TD.w5, TD.w6] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hW ⊢
    tauto
  exact Subgroup.mem_inf.2 ⟨mem_om1 h1, word_fix (t2Words_parts.1 W h1)
    (t2Words_parts.2.2.1 W hW)⟩

theorem mem_om3 {W : List ℕ} (hW : W ∈ [TD.w5, TD.w6]) :
    word gen W ∈ om3 := by
  have h1 : W ∈ [TD.w1, TD.w2, TD.w3, TD.w4, TD.w5, TD.w6] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hW ⊢
    tauto
  have h2 : W ∈ [TD.w3, TD.w4, TD.w5, TD.w6] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hW ⊢
    tauto
  exact Subgroup.mem_inf.2 ⟨mem_om2 h2, word_fix (t2Words_parts.1 W h1)
    (t2Words_parts.2.2.2 W hW)⟩

theorem t2_natArr : CFSG.Sporadic.SmallOddCore.Native.natArr (t2Tbl ()) =
    unpack 360 9 (T2H.F 0) := by
  have h := CFSG.KC.Misc.HexFlat.hexT_sound T2H.all (by norm_num) 0 (by norm_num)
  rw [← T2H.eq] at h
  exact h

theorem t2Pt_parts : pm (T2H.F 0) = true ∧ Nat.beq (pg 9 (mask 9) (T2H.F 0) 1) 178 = true ∧
    Nat.beq (pg 9 (mask 9) (T2H.F 0) 178) 242 = true := by
  have h := t2Pt
  simp only [bAnd_iff] at h
  exact h

theorem permOK_t2 : CFSG.Sporadic.SmallOddCore.permOK 360 (t2Tbl ()) = true := by
  unfold CFSG.Sporadic.SmallOddCore.permOK
  rw [t2_natArr]
  exact isInvA_of t2Pt_parts.1

theorem prep_t2 : CFSG.KS.Raw.Orb.PRep 360 9 (T2H.F 0) (tp 360 (t2Tbl ())) := by
  have h := co2Rep_natArr_iff.2 (rep_tp permOK_t2)
  rw [t2_natArr] at h
  exact CFSG.KS.Raw.Orb.prep_of_rep h

theorem t2_p : tp 360 (t2Tbl ()) t2p = t2x :=
  Fin.ext (by rw [← prep_t2 t2p]; exact Nat.eq_of_beq_eq_true t2Pt_parts.2.1)

theorem t2_x : tp 360 (t2Tbl ()) t2x = t2y :=
  Fin.ext (by rw [← prep_t2 t2x]; exact Nat.eq_of_beq_eq_true t2Pt_parts.2.2)

theorem orb0 : 120 ≤ (orbit omegaT t2p).ncard := by
  have h := t2Orb0
  simp only [bAnd_iff] at h
  have hl := Nat.eq_of_beq_eq_true h.2
  have := orbOK_sound h.1 omegaT gen (fun l hl => gen_mem_omegaT hl)
    (fun l hl q => prep_gen hl q) (by norm_num)
  rw [hl] at this
  exact this

theorem orb1 : 120 ≤ (orbit om1 t2x).ncard := by
  have h := t2Orb1
  simp only [bAnd_iff] at h
  have hl := Nat.eq_of_beq_eq_true h.2
  have := orbOK_sound h.1 om1 (fun l => word gen ([TD.w1, TD.w2].getD l []))
    (fun l hl => by
      interval_cases l
      · exact mem_om1 (by simp)
      · exact mem_om1 (by simp))
    (fun l hl q => by
      interval_cases l
      · exact word_apply (t2Words_parts.1 _ (by simp)) q
      · exact word_apply (t2Words_parts.1 _ (by simp)) q) (by norm_num)
  rw [hl] at this
  exact this

theorem orb2 : 56 ≤ (orbit om2 t2y).ncard := by
  have h := t2Orb2
  simp only [bAnd_iff] at h
  have hl := Nat.eq_of_beq_eq_true h.2
  have := orbOK_sound h.1 om2 (fun l => word gen ([TD.w3, TD.w4].getD l []))
    (fun l hl => by
      interval_cases l
      · exact mem_om2 (by simp)
      · exact mem_om2 (by simp))
    (fun l hl q => by
      interval_cases l
      · exact word_apply (t2Words_parts.1 _ (by simp)) q
      · exact word_apply (t2Words_parts.1 _ (by simp)) q) (by norm_num)
  rw [hl] at this
  exact this

theorem orbC :
    (orbit ↥(CFSG.Sporadic.Schreier.centralizerIn omegaT (tp 360 (t2Tbl ()))) t2p).ncard ≤
      120 := by
  have hsub : orbit ↥(CFSG.Sporadic.Schreier.centralizerIn omegaT (tp 360 (t2Tbl ()))) t2p ⊆
      Set.range (Fin.castLE (by norm_num : 120 ≤ 360)) := by
    rintro _ ⟨⟨c, hc⟩, rfl⟩
    have hc0 : c ∈ stab0 :=
      omegaT_le_stab0 (CFSG.Sporadic.Schreier.mem_centralizerIn.1 hc).1
    have hlt : ((c t2p : Fin 360) : ℕ) < 120 := (hc0 t2p).1 (by decide)
    exact ⟨⟨_, hlt⟩, Fin.ext rfl⟩
  calc _ ≤ (Set.range (Fin.castLE (by norm_num : 120 ≤ 360))).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = 120 := by
        rw [Set.ncard_range_of_injective (Fin.castLE_injective _)]
        simp

@[expose] noncomputable def tcGT : Array CFSG.Sporadic.Th.Native.Table :=
  #[tabT (unpack 360 9 (TC.G 0)), tabT (unpack 360 9 (TC.G 1))]

@[expose] noncomputable def tcGI : Array CFSG.Sporadic.Th.Native.Table :=
  #[tabT (unpack 360 9 (TC.GI 0)), tabT (unpack 360 9 (TC.GI 1))]

theorem rep_tabT_unpack {P : ℕ} {g : Perm (Fin 360)} (h : CFSG.KS.Raw.Orb.PRep 360 9 P g) :
    CFSG.Sporadic.Th.Rep 360 (tabT (unpack 360 9 P)) g := by
  rw [← arrTable_unpack]
  exact CFSG.ComponentClassification.J2Cover.rep_arrTable (by norm_num)
    (CFSG.KS.Raw.Orb.rep_unpack h)

theorem tcCanon_parts : (∀ j < 2, canonK 360 9 (mask 9) (360 * 9) (TC.G j) = true ∧
      canonK 360 9 (mask 9) (360 * 9) (TC.GI j) = true) ∧
    canonK 360 9 (mask 9) (360 * 9) TC.R = true ∧ szOK 360 9 = true := by
  have h := tcCanon
  simp only [bAnd_iff] at h
  exact ⟨fun j hj => by simpa only [bAnd_iff] using allN_spec h.1 j hj, h.2⟩

theorem tcBind_parts : (∀ j < 2, (∀ q < 360, Nat.beq (pg 9 (mask 9) (TC.G j) q)
      (wapp 9 (mask 9) AP.S ([TD.w5, TD.w6].getD j []) q) = true) ∧
      permOK 360 9 (mask 9) (360 * 9) (TC.G j) (TC.GI j) = true) ∧ TC.R = T2H.F 0 := by
  have h := tcBind
  simp only [bAnd_iff] at h
  refine ⟨fun j hj => ?_, Nat.eq_of_beq_eq_true h.2⟩
  have h' := allN_spec h.1 j hj
  simp only [bAnd_iff] at h'
  exact ⟨allN_spec h'.1, h'.2⟩

theorem tc_cnt : TC.cnt = 72 := Nat.eq_of_beq_eq_true tcCnt

theorem prep_tcG {j : ℕ} (hj : j < 2) :
    CFSG.KS.Raw.Orb.PRep 360 9 (TC.G j) (word gen ([TD.w5, TD.w6].getD j [])) := by
  intro q
  have hW : lettersOK 8 ([TD.w5, TD.w6].getD j []) = true := by
    interval_cases j
    · exact t2Words_parts.1 _ (by simp)
    · exact t2Words_parts.1 _ (by simp)
  rw [Nat.eq_of_beq_eq_true ((tcBind_parts.1 j hj).1 q q.2), word_apply hW]

theorem class72 :
    72 ≤ (CFSG.Sporadic.Schreier.conjClass om3 (tp 360 (t2Tbl ()))).ncard := by
  have hG : TabsOK 360 9 2 TC.G tcGT := by
    refine ⟨rfl, fun j hj => ⟨?_, (tcCanon_parts.1 j hj).1⟩⟩
    interval_cases j <;> rfl
  have hGI : TabsOK 360 9 2 TC.GI tcGI := by
    refine ⟨rfl, fun j hj => ⟨?_, (tcCanon_parts.1 j hj).2⟩⟩
    interval_cases j <;> rfl
  have hp : ∀ i < TC.cnt, penumPtK 360 9 (mask 9) (360 * 9) true TC.G TC.GI 2 TC.cnt TC.T TC.PL
      TC.POS TC.SRT TC.SRI i = true := by
    intro i hi
    have hi' := hi
    rw [tc_cnt] at hi'
    exact CFSG.KS.BaseMask.penumSl_spec tcPen (by omega) (by omega) hi
  have hs : ∀ i < TC.cnt, hsortPtK 360 9 (mask 9) TC.cnt TC.T TC.HS TC.HSI i = true := by
    intro i hi
    have hi' := hi
    rw [tc_cnt] at hi'
    exact slK_spec tcHs i (by omega) (by omega) hi
  obtain ⟨-, ht, hd⟩ := conjH_sound (X := TC.R) (x := tabT (unpack 360 9 TC.R)) (cap := 72)
    tcCanon_parts.2.2 hG hGI rfl tcHd hp hs
  have hroot : CFSG.Sporadic.Th.Rep 360 (tabT (unpack 360 9 TC.R)) (tp 360 (t2Tbl ())) := by
    rw [tcBind_parts.2]
    exact rep_tabT_unpack prep_t2
  have hg : ∀ l < tcGT.size, CFSG.Sporadic.Th.Rep 360 tcGT[l]! (word gen ([TD.w5, TD.w6].getD l []))
      ∧ CFSG.Sporadic.Th.Rep 360 tcGI[l]! (word gen ([TD.w5, TD.w6].getD l []))⁻¹ ∧
      word gen ([TD.w5, TD.w6].getD l []) ∈ om3 := by
    intro l hl
    have hl2 : l < 2 := hl
    have e1 : tcGT[l]! = tabT (unpack 360 9 (TC.G l)) := (hG.2 l hl2).1
    have e2 : tcGI[l]! = tabT (unpack 360 9 (TC.GI l)) := (hGI.2 l hl2).1
    refine ⟨?_, ?_, ?_⟩
    · rw [e1]
      exact rep_tabT_unpack (prep_tcG hl2)
    · rw [e2]
      exact rep_tabT_unpack (prep_inv_of_permOK (prep_tcG hl2) (tcBind_parts.1 l hl2).2)
    · interval_cases l
      · exact mem_om3 (by simp)
      · exact mem_om3 (by simp)
  exact CFSG.ClassicalInvolution.Q3.O8.le_ncard_conjClass_of_closureOK (H := om3) hg hroot
    (m := 72) (c := hRec 360 9 TC.cnt TC.T TC.PL) (by rw [ht, hd, hRec_size', tc_cnt]; decide)

theorem card_centralizer_t2_le' :
    Nat.card (CFSG.Sporadic.Schreier.centralizerIn omegaT (tp 360 (t2Tbl ()))) ≤ 431 := by
  have key := mul_card_centralizerIn_le omegaT (tp 360 (t2Tbl ())) t2p t2x t2y t2_p t2_x
    orb0 orb1 orb2 class72 orbC
  rw [card_omegaT] at key
  omega

end CertificateChecks.KernelD42Tri

end
