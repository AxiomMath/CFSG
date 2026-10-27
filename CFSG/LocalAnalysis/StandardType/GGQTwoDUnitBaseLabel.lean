module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBase
public import CFSG.LocalAnalysis.StandardType.GGMemberRowsDefs
public import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseLabel
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseOrthFrame
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaE6Pat
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaE6PatCox
import CFSG.LocalAnalysis.StandardType.GGStdUnitaryFourExcl
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSQ2U62Setup
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpCount
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQFourTBSmall
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaE6PatRows
import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrameOfMarking
import CFSG.LocalAnalysis.StandardType.GGOrthFramePairs
import CFSG.LocalAnalysis.StandardType.GGOrthRk1Centralizer
import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrameCenter
import CFSG.LocalAnalysis.StandardType.GGQTwoPThree

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo

variable {G : Type} [Group G] [Finite G]

variable {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
  {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {m : ℕ}

private theorem qtwoDB29_orthM_absurd {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hRig : GGLabelRigidInput)
    (hroute : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer L Bs)
    (hrefl : GGIsReflection p r) (hr6 : Nat.card ↥(ggRankOneIn L Bs r) = 6)
    (h : GGInnerDiagOnLabel (fun p lab => ggRowP_EOmM p lab ∧ 2 ≤ lab.n) p Bs L) : False := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hroute
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : Group.IsPerfect ↥L := Group.IsPerfect.mk h.1
  have hconf : GGConfig p B Bs x L D J := hroute.1.1
  obtain ⟨-, hBs, -, -, -⟩ := hconf.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hconf.2.1.2.2.2
  have hZK : ∀ lab, ggRowP_EOmM p lab ∧ 2 ≤ lab.n →
      GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) → Subgroup.center ↥L = ⊥ := by
    intro lab hl hhas
    have h5 : 5 ≤ lab.rank := hl.1.2.1
    exact OrthTorus.center_eq_bot_of_hasLabel_orth (Or.inr hl.1.1) (by omega) hl.2 hhas
  obtain ⟨lab, hPlab, -, Φ, -, hΦF, hQ, hdim, -⟩ :=
    OrthTorus.exists_orthFrameCore_of_marking hRig hp2 hBs hSC
      (fun lab hl => Or.inr hl.1) h hZK (ggGamma_L_exists_ne_one hconf)
  obtain ⟨g, hgL, -, hgconj⟩ := mem_ggAutomizer_iff.mp hrA
  have hg : g ∈ Φ.ψ.range := by rw [Φ.hrange]; exact hgL
  obtain ⟨w, hw⟩ := hg
  have hwr : ∀ b : ↥Bs, ((r b : ↥Bs) : G) = Φ.ψ w * b * (Φ.ψ w)⁻¹ := by
    intro b
    rw [hw]
    exact hgconj b
  have hthree := CFSG.RankThree.PartOne.exists_threeSingular_of_dim Φ.Q hQ Φ.hr hdim
  haveI : Nontrivial Φ.V := CFSG.RankThree.PartOne.nontrivial_of_threeSingular hthree
  have hZ := CFSG.RankThree.PartOne.center_orthDerived_eq_bot hQ hthree
  obtain ⟨xs, hxs⟩ := Φ.exists_signed_action_of_inner hp2 hQ hZ w r hwr hrefl
  have hrank := Φ.rankOne_eq_map_of_signed_action w r xs hwr hxs
  set a : Fin Φ.r := xs.1.1.1 with ha
  set b : Fin Φ.r := xs.1.1.2 with hb
  have hab : a ≠ b := ne_of_lt xs.1.2
  have hq4 : 4 ≤ Nat.card Φ.F := by
    rw [hΦF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) hPlab.2
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) Φ.F) =
      Nat.card Φ.F * (Nat.card Φ.F ^ 2 - 1) := by
    rw [CFSG.OrderReductions.LinearOrders.card_specialLinear Φ.F 2 (by norm_num)]
    norm_num [Finset.Icc_self]
  have hcardRankOne : Nat.card ↥(Φ.Δ.rankOne a b) =
      Nat.card Φ.F * (Nat.card Φ.F ^ 2 - 1) := by
    obtain ⟨θ, hθinj, hθrange, -⟩ :=
      OrthTorus.tbjOm_rankOne_model hp2 Φ.hA Φ.Δ (le_trans (by norm_num) Φ.hr) hq4 Φ.hfix a b hab
    rw [← hθrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv).symm.trans hSL
  have hcardRankOnePos : Nat.card ↥(Φ.Δ.rankOnePos a b) =
      Nat.card Φ.F * (Nat.card Φ.F ^ 2 - 1) := by
    have h1 : ({a, b} : Finset (Fin Φ.r)).card ≤ 2 := by
      calc ({a, b} : Finset (Fin Φ.r)).card =
          (insert a ({b} : Finset (Fin Φ.r))).card := rfl
        _ ≤ ({b} : Finset (Fin Φ.r)).card + 1 := Finset.card_insert_le a _
        _ = 2 := by simp
    have h2 : 2 < Φ.r := by have := Φ.hr; omega
    have hcard : ({a, b} : Finset (Fin Φ.r)).card <
        (Finset.univ : Finset (Fin Φ.r)).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      exact lt_of_le_of_lt h1 h2
    obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    rw [Finset.mem_insert, Finset.mem_singleton] at hk
    obtain ⟨w', -, -, -, hwconj⟩ :=
      Φ.Δ.exists_dinv_conj Φ.hfix hab (fun h => hk (Or.inr h.symm)) (fun h => hk (Or.inl h.symm))
    rw [hwconj, Subgroup.card_map_of_injective (MulAut.conj w').injective]
    exact hcardRankOne
  have hle : (if xs.2 = true then Φ.Δ.rankOnePos a b else Φ.Δ.rankOne a b) ≤
      CFSG.RankThree.Classical2.orthDerived Φ.Q := by
    by_cases hx : xs.2 = true
    · rw [if_pos hx]; exact Φ.Δ.rankOnePos_le a b
    · rw [if_neg hx]; exact Φ.Δ.rankOne_le a b
  have hcardSigned : Nat.card ↥(if xs.2 = true then Φ.Δ.rankOnePos a b
      else Φ.Δ.rankOne a b) = Nat.card Φ.F * (Nat.card Φ.F ^ 2 - 1) := by
    by_cases hx : xs.2 = true
    · rw [if_pos hx]; exact hcardRankOnePos
    · rw [if_neg hx]; exact hcardRankOne
  have hfin : Nat.card ↥(ggRankOneIn L Bs r) = Nat.card Φ.F * (Nat.card Φ.F ^ 2 - 1) := by
    rw [hrank, Subgroup.card_map_of_injective Φ.hinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact hcardSigned
  have h60 : 60 ≤ Nat.card Φ.F * (Nat.card Φ.F ^ 2 - 1) := by
    have h16 : 16 ≤ Nat.card Φ.F ^ 2 := by nlinarith [hq4]
    have h15 : 15 ≤ Nat.card Φ.F ^ 2 - 1 := by omega
    calc 60 = 4 * 15 := by norm_num
      _ ≤ Nat.card Φ.F * (Nat.card Φ.F ^ 2 - 1) := Nat.mul_le_mul hq4 h15
  omega

theorem ggQTwoDUnit_memberUnitary_L_or_u62 (hRig : GGLabelRigidInput) (hTBF : GGTBFixInput)
    (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e) (e' : Fin m ≃ ι) (hm : 4 ≤ m) (hM : M = (ggCoxeterMatrixD m).reindex e') (hL : qtwoOrthL.compl G L 𝒦) :
    GGMemberUnitary p Bs L ∨ (m = 6 ∧ GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) p Bs L) := by
  obtain ⟨r, hrA, hrc, hr6⟩ := hcfg.2.2.2.2
  have hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e := hcfg.2.2.2.1
  have hns : ¬ GGSplitLie p L := hcfg.2.2.1
  have hp3 : p = 3 := ggQTwo_p_eq_three hcfg.1 M e hpres hrA hrc hr6
  subst hp3
  have hroute : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦 := hcfg.1
  have hD : GGIsWeylMatrixD M := ⟨m, e', by omega, hM⟩
  have hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := GGIsWeylMatrixAD.le_three (Or.inr hD)
  have hconf : GGConfig 3 B Bs x L D J := hroute.1.1
  have hrefl : GGIsReflection 3 r := ggCoxRefl_isReflection hpres.2 hrc
  have hNP : GGNoReflE6Pat 3 Bs L :=
    ggX_noReflE6Pat_typeD hroute hpres hD (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl))
  have hlab := ggL_baseLabel_of_nonSplit hroute hpres hle3 hns
  have hmain : GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧
      ¬ (lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5))) 3 Bs L ∨ (m = 6 ∧ GGInnerDiagOnLabel
        (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) 3 Bs L) := by
    rcases GGInnerDiagOnLabel.elim_or hlab with hESU | hrest1
    ·
      have hsplit : GGInnerDiagOnLabel (fun p lab =>
          (ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 3) ∨
          (ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) ∨
          (ggRowP_ESU p lab ∧ ¬ (lab.n = 1 ∧
            (lab.rank = 3 ∨ lab.rank = 5)))) 3 Bs L :=
        hESU.mono' fun lab hl => by
          by_cases h3 : lab.n = 1 ∧ lab.rank = 3
          · exact Or.inl ⟨hl, h3.1, h3.2⟩
          by_cases h5 : lab.n = 1 ∧ lab.rank = 5
          · exact Or.inr (Or.inl ⟨hl, h5.1, h5.2⟩)
          · exact Or.inr (Or.inr ⟨hl, fun hc => by
              rcases hc.2 with h | h
              · exact h3 ⟨hc.1, h⟩
              · exact h5 ⟨hc.1, h⟩⟩)
      rcases GGInnerDiagOnLabel.elim_or hsplit with h3 | hrest
      · exact (not_ggInnerDiagOnLabel_unitary_four hconf
          (h3.mono' fun lab hl => ⟨hl.1.1.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1),
            hl.2.2, hl.1.2⟩)).elim
      rcases GGInnerDiagOnLabel.elim_or hrest with h5 | hgoal
      ·
        have hFix : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer L Bs, φ b = b) →
            (b : G) ∈ Subgroup.zpowers x := by
          obtain ⟨y, K', hN⟩ := exists_ggNbr hconf.1.2.2.2.2.2.2.2 hconf.2.2
          intro b hb
          exact hTBF G 3 B Bs x L D J hconf hroute.1.2.1 hroute.1.2.2.1 hroute.1.2.2.2.1
            y K' hN (hroute.2.1 y K' hN) (Or.inr hroute.2.1) b hb
        obtain ⟨-, σ, -⟩ := nsQ2U62_card_D hroute hFix h5 hpres hD
        refine Or.inr ⟨?_, h5⟩
        simpa using Fintype.card_congr (e'.trans σ.symm)
      · exact Or.inl hgoal
    · rcases GGInnerDiagOnLabel.elim_or hrest1 with hEOmM | hrest2
      ·
        have hsplit : GGInnerDiagOnLabel (fun p lab =>
            (ggRowP_EOmM p lab ∧ lab.n = 1) ∨
            (ggRowP_EOmM p lab ∧ 2 ≤ lab.n)) 3 Bs L :=
          GGInnerDiagOnLabel.mono_label_of_hasLabel (fun lab hΛ _ hl => by
            by_cases hn : lab.n = 1
            · exact Or.inl ⟨hl, hn⟩
            · exact Or.inr ⟨hl, by have h1 := hΛ.1; omega⟩) hEOmM
        rcases GGInnerDiagOnLabel.elim_or hsplit with h1 | h2
        · obtain ⟨lab, hΛ, hhas, R, _, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel h1
          obtain ⟨hEM, hn1⟩ := hP.1
          exact (hL ⟨lab, hΛ, hhas, hn1, Or.inr hEM.1⟩).elim
        · exact (qtwoDB29_orthM_absurd hRig hroute hrA hrefl hr6 h2).elim
      · rcases GGInnerDiagOnLabel.elim_or hrest2 with hTw | hF4
        ·
          exact (NSJoin.false_of_twE6_L_typeD hroute hpres hD hTw).elim
        ·
          have hF4' : GGInnerDiagOnLabel (fun _ lab => lab.n = 1 ∧
              (ggRowP_EOmP 3 lab ∨ ggRowP_EE7 3 lab ∨ ggRowP_EE8 3 lab ∨
                ggRowP_NF4 3 lab)) 3 Bs L :=
            hF4.mono' fun lab hl => ⟨hl.1, hl.2.2⟩
          have hF4'' : GGInnerDiagOnLabel (fun _ lab =>
              (lab.n = 1 ∧ ggRowP_EOmP 3 lab) ∨
              (lab.n = 1 ∧ (ggRowP_EE7 3 lab ∨ ggRowP_EE8 3 lab ∨
                ggRowP_NF4 3 lab))) 3 Bs L :=
            hF4'.mono' fun lab hl => hl.2.imp (fun h => ⟨hl.1, h⟩) (fun h => ⟨hl.1, h⟩)
          rcases GGInnerDiagOnLabel.elim_or hF4'' with hP | hRest
          ·
            obtain ⟨lab, hΛ, hhas, R, _, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hP
            obtain ⟨hn1, hEP⟩ := hP.1
            exact (hL ⟨lab, hΛ, hhas, hn1, Or.inl hEP.1⟩).elim
          · have hRest' : GGInnerDiagOnLabel (fun _ lab =>
                (lab.n = 1 ∧ ggRowP_EE7 3 lab) ∨
                (lab.n = 1 ∧ (ggRowP_EE8 3 lab ∨ ggRowP_NF4 3 lab))) 3 Bs L :=
              hRest.mono' fun lab hl => hl.2.imp (fun h => ⟨hl.1, h⟩) (fun h => ⟨hl.1, h⟩)
            rcases GGInnerDiagOnLabel.elim_or hRest' with h7 | hRest2
            · exact (ggX_row_absurd_of_noReflE6Pat hRig ggRowE6Pat_EE7 hroute (Or.inl rfl) hNP
                (h7.mono' fun lab hl => hl.2)).elim
            · have hRest2' : GGInnerDiagOnLabel (fun _ lab =>
                  (lab.n = 1 ∧ ggRowP_EE8 3 lab) ∨ (lab.n = 1 ∧ ggRowP_NF4 3 lab)) 3 Bs L :=
                hRest2.mono' fun lab hl => hl.2.imp (fun h => ⟨hl.1, h⟩) (fun h => ⟨hl.1, h⟩)
              rcases GGInnerDiagOnLabel.elim_or hRest2' with h8 | hNF4
              · exact (ggX_row_absurd_of_noReflE6Pat hRig ggRowE6Pat_EE8 hroute (Or.inl rfl) hNP
                  (h8.mono' fun lab hl => hl.2)).elim
              · exact (NSJoin.not_f4Three_of_cfg hroute hpres hle3
                  (hNF4.mono' fun lab hl => ⟨hl.2.1, rfl, by rw [hl.1]; norm_num⟩)).elim
  exact hmain

theorem ggQTwoDUnit_memberUnitary_L_of_ne_six (hRig : GGLabelRigidInput) (hTBF : GGTBFixInput)
    (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e) (e' : Fin m ≃ ι) (hm : 4 ≤ m) (hm6 : m ≠ 6)
    (hM : M = (ggCoxeterMatrixD m).reindex e') (hL : qtwoOrthL.compl G L 𝒦) :
    GGMemberUnitary p Bs L :=
  (ggQTwoDUnit_memberUnitary_L_or_u62 hRig hTBF hcfg e' hm hM hL).resolve_right fun h => hm6 h.1

end CFSG.StandardType.QTwo

end
