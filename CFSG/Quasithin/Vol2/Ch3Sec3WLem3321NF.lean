module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321NF
public import CFSG.Quasithin.Vol2.Ch3Sec3WCase4CountRPf
public import CFSG.Quasithin.Vol2.Ch3Sec3WLem3321
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321GPNF
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321GT

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open CFSG.Quasithin.H13.L3316 (liftPre liftCore liftCore_le liftCore_eq)
open scoped commutatorElement IsMulCommutative

theorem L3321.step3_3_21gSum_of_onW (h5 : Stmt3_3_5) (h7 : Stmt3_3_7)
    (h13 : Stmt3_3_13LTOn Site3321a1)
    (h14 : Stmt3_3_14) (hGA : GriessAllModelsStatement) (he : Step3_3_21e)
    (hC34 : CFSG.Quasithin.C134L32CorrM) :
    Step3_3_21gSum := by
  intro G _ _ T M L D h ⟨e⟩ hc hmod
  by_contra hout
  obtain ⟨hML, hMN⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hMN
  obtain ⟨α, ρ, U₁, U₂, hαs, hαk, hαkV, hαU, hαv, hdirect, ⟨D₁⟩, ⟨D₂⟩⟩ :=
    L3321.exists_coords_sum h14 hGA h e hmod
  have hmod' : Mod3321 T L := ⟨hc, Or.inr hmod⟩
  have hcomm := L3321.commV_eq_top h7 h14 he h ⟨e⟩ hmod'
  have hdirect' := hdirect
  rw [hcomm] at hdirect
  have he' := he G T M L D h ⟨e⟩ hmod'
  obtain ⟨S, hST, hTS, hTLS, hQS, hconj, ⟨t₀, ht₀, ht₀S, u₀, hu₀, hact, hdich⟩, hDS⟩ :=
    L3321.exists_inner_of_DH h hTL hαs hαk hαU hout (by
      have hPL := L3316.liftPre_le α L3321.P2
      exact h13 G T M L D _ h ⟨hTL, ⟨e⟩, hc, hmod, hout, α, ρ, U₁, U₂, hαs, hαk, hαU,
          fun l hl => hαv l, hdirect', ⟨D₁⟩, ⟨D₂⟩, rfl⟩
        (inH_sup_of_le h hPL) (sup_le_sup_right hPL T)
        (L3321.nonempty_wreath hαs hαk hTL h.sylow.1 hαU hout))
  have hR : L3321.RData G T M L D S α := ⟨h, hTL, hαs, hαk, hαkV, hαU, hST, hTLS, hQS, hconj⟩
  have h13' := fun y (hy : y ∈ liftCore α (FLc.QI 4 {1})) =>
    L3321.conj_Y_one (hTL ht₀) hu₀ hact hy
  have h31' := fun y (hy : y ∈ liftCore α (FLc.QI 4 {3})) =>
    L3321.conj_Y_three (hTL ht₀) hu₀ hact hy
  have hkT : α.ker.map L.subtype ≤ T := by
    rw [hαk]
    rintro _ ⟨l, hl, rfl⟩
    exact hR.RT (hR.pCoreOf_L_le_R ((Lem3328.mem_pCore_iff l).mp hl))
  have hL : L ≤ liftCore α (FLc.QI 4 {1}) ⊔ liftCore α (FLc.QI 4 {3}) ⊔ T :=
    le_sup_left.trans (Ln2.sup_liftCore_eq (Nat.card_zmod 2) le_rfl (by norm_num) hαs hkT hαU).le
  rcases hR.isMSPair_or_one with hMS | ⟨C, hCS, hC1, hchar, hCN⟩
  · obtain ⟨ψ, hψs, hψk, -⟩ := hR.exists_levi_one
    have hα₂ := L3321.isModO2Surj_comp hψs hψk
    obtain ⟨j, hj⟩ := Ln2.exists_isC134CaseW hC34 hMS hR.isLocal_one.2.1
      (hR.le_normalizer_Y {1}) hα₂.1 hα₂.2
    have hV16 := L3321.card_comm_ge_one h hαs hαv D₁
    rcases j with _ | _ | _ | _ | _ | _ | j
    · exact hj.elim
    · exact hR.not_case12_one hV16 (Or.inl rfl) hj
    · exact hR.not_case12_one hV16 (Or.inr rfl) hj
    · exact hR.not_case3_one hj (L3321.exists_fixed_comm_one h hαs hαv D₁)
    · exact Case4Count.case4CorrA1Twist_holdsW G T M L D S α t₀ hR ⟨hc, hmod⟩ ht₀ ht₀S hdich
        h13' h31' hj
    · exact hR.not_case5_one hj
    · exact hj.elim
  · exact L3321.false_of_char h5 h14 h hST hTS hDS hL ht₀ h31' hCS hC1 hchar hCN

theorem stmt3_3_21_of_onW
    (h5 : Stmt3_3_5) (h7 : Stmt3_3_7) (h9 : Stmt3_3_9) (h13a : Stmt3_3_13LTOn Site3321a1)
    (h13b : Stmt3_3_13LTOn Site3321a2) (h14 : Stmt3_3_14)
    (h18 : Stmt3_3_18) (h20 : Stmt3_3_20) (h51 : AsB51) (hI16 : AsI16Cover)
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (hGA : GriessAllModelsStatement)
    (h15 : Step3_3_15R) (hC34 : CFSG.Quasithin.C134L32CorrM)
    (h12 : Step3_3_12R) (hfQ : Step3_3_21fQ) :
    Stmt3_3_21 := by
  intro G _ _ T M L D h
  refine ⟨fun e => ?_⟩
  obtain ⟨-, hMN⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hMN
  obtain ⟨hab, -, hmod⟩ := Ln2.module_cases h18 h51 hI16 h h38 h39 hTL (Or.inl rfl) e
  have hd := L3321.step3_3_21d_of h5 h7 h9 h14
  have he := L3321.step3_3_21e_of h5 h14 hGA hd
  have hf := L3321.step3_3_21f_ofW h7 h9 h14 hGA he h15 hC34 h12 h20 hd hfQ
  have hgExt := L3321.step3_3_21gExt_of_on h9 h13b h14 hGA hd
  rcases hmod with ⟨Z, hZ, hZ2, -, hext⟩ | hsum
  · have hext' : Mod3321Ext T L := ⟨Z, hZ, hZ2, hext⟩
    exact hf G T M L D h ⟨e⟩ ⟨hab, Or.inl hext'⟩ (hgExt G T M L D h ⟨e⟩ hab hext')
  · exact hf G T M L D h ⟨e⟩ ⟨hab, Or.inr hsum⟩
      (L3321.step3_3_21gSum_of_onW h5 h7 h13a h14 hGA he hC34 G T M L D h ⟨e⟩ hab hsum)

end CFSG.Quasithin.H13
