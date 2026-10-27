module

public import CFSG.LocalAnalysis.StandardType.GGFrameRouteJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGFrameFSxOrth
import CFSG.LocalAnalysis.StandardType.GGFrameFSxEndsCardJoinAux
public import CFSG.LocalAnalysis.StandardType.GGFrameFSxE7
import CFSG.LocalAnalysis.StandardType.GGFrameRouteFSCenter
import CFSG.LocalAnalysis.StandardType.GGFrameRouteFSEnds
import CFSG.LocalAnalysis.StandardType.GGFrameRouteLower
import CFSG.LocalAnalysis.StandardType.GGFrameRouteE7Models
import CFSG.LocalAnalysis.StandardType.GGTableBBstar

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open CFSG.Assembly CFSG.LieType.ChevTwo
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (AutThreePowInner)

variable {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

theorem card_bstar_eq_of_ne (hR : GGSecFiveRestHyp 3 B Bs x L D J) (hne : B ≠ Bs) :
    Nat.card Bs = 3 * Nat.card B := by
  obtain ⟨hle, hab, hcard, -⟩ := hR.1.2.1
  exact card_eq_three_mul_of_le_of_ne hle hab hcard hne

theorem bstar_eq_sup_of_restHyp (hR : GGSecFiveRestHyp 3 B Bs x L D J)
    (hN : (L.subgroupOf (Subgroup.centralizer ({x} : Set G))).Normal)
    (hZ : Subgroup.center ↥L = ⊥) (hAut : AutThreePowInner ↥L) :
    x ∉ L ∧ Bs = Subgroup.zpowers x ⊔ (Bs ⊓ L) := by
  obtain ⟨-, hBs, hxB, hLx, -⟩ := hR.1.tableB_facts
  have hS : LargeEvenSStar 3 B x L := hR.1.1.2.2.2.2.2.2.1
  exact bstar_eq_sup_of_elemAbelian hBs hxB hS.2.2.1 hLx hN hZ hAut
    hR.1.2.1.2.2.2 (fun S hSL hSp => hS.2.2.2.2 S hSL hSp)

theorem card_bstar_le_three_mul_inf (hR : GGSecFiveRestHyp 3 B Bs x L D J)
    (h : Bs = Subgroup.zpowers x ⊔ (Bs ⊓ L)) : Nat.card Bs ≤ 3 * Nat.card ↥(Bs ⊓ L) := by
  obtain ⟨-, hBs, hxB, hLx, -⟩ := hR.1.tableB_facts
  have hx1 : x ≠ 1 := hR.1.1.2.2.2.2.2.2.1.2.2.1
  exact card_sup_zpowers_le_three_mul_card_inf hBs hxB hx1 h

theorem ne_bstar_of_le_centralizer (hR : GGSecFiveRestHyp 3 B Bs x L D J)
    (hN : (L.subgroupOf (Subgroup.centralizer ({x} : Set G))).Normal)
    (hsup : Bs = Subgroup.zpowers x ⊔ (Bs ⊓ L))
    (hK : ∀ T : Subgroup G, IsPGroup 2 T → T ≤ Subgroup.normalizer (L : Set G) →
      Bs ⊓ L ≤ Subgroup.normalizer (T : Set G) → T ≤ Subgroup.centralizer (L : Set G)) :
    B ≠ Bs := by
  obtain ⟨-, -, -, hLx, -⟩ := hR.1.tableB_facts
  obtain ⟨-, -, -, -, -, -, -, hST⟩ := hR.1.1
  obtain ⟨-, hT, -, -⟩ := hST
  exact ne_bstar_of_stdType_twoGroup hT hLx hN hsup fun T hT2 hTN hET =>
    (hK T hT2 hTN hET).trans (Subgroup.centralizer_le (inf_le_right : Bs ⊓ L ≤ L))

theorem ne_bstar_of_D6
    (hR : GGSecFiveRestHyp 3 B Bs x L D J)
    (hAt : GGSecFiveWeylAtJoin 3 B Bs x L D J CoxeterMatrix.E₇)
    (hm : LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1)) :
    B ≠ Bs := by
  have hZ : Subgroup.center ↥L = ⊥ :=
    center_eq_bot_of_fsEndMarking (fun _ hl => ⟨Or.inl ⟨hl.1, hl.2.1⟩, hl.2.2⟩) hm
  have hFSLab : LargeEvenMarking L (fun lab _ _ _ _ _ => FSLab lab) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨h.2.2, Or.inl ⟨h.1, h.2.1⟩⟩) hm
  have hN : (L.subgroupOf (Subgroup.centralizer ({x} : Set G))).Normal :=
    fsEnds_normal B Bs x L D J hR hFSLab
  obtain ⟨e⟩ := nonempty_mulEquiv_omegaPlusSix_of_marking hm hZ
  have hQ : GoodQ (StatedQuadPlus 6 (ZMod 2)) := goodQ_plus (n := 5) (by norm_num)
  have hind : OmegaTwoAutInduced (StatedQuadPlus 6 (ZMod 2)) :=
    omegaTwoAutInduced_plus_of_four_le (n := 5) (by norm_num)
  have hsup := bstar_eq_sup_of_restHyp hR hN hZ (autThreePowInner_of_goodQ hQ hind e)
  obtain ⟨𝒦, -, -, hM⟩ := hAt
  have hBscard : 3 ^ 7 ≤ Nat.card Bs :=
    pow_le_card_of_weylOfType_of_two Nat.prime_three (by norm_num) hR.1.2.1.2.1 hM
      exists_elemAbelian_two_coxeterE7
  have hle := card_bstar_le_three_mul_inf hR hsup.2
  have h6 : 3 ^ 6 ≤ Nat.card ↥(Bs ⊓ L) := by
    have hmul : 3 * 3 ^ 6 ≤ 3 * Nat.card ↥(Bs ⊓ L) := by
      calc 3 * 3 ^ 6 = 3 ^ 7 := by norm_num
        _ ≤ Nat.card Bs := hBscard
        _ ≤ 3 * Nat.card ↥(Bs ⊓ L) := hle
    exact Nat.le_of_mul_le_mul_left hmul (by norm_num)
  refine ne_bstar_of_le_centralizer hR hN hsup.2 (fun T hT2 hTN hET => ?_)
  exact le_centralizer_of_goodQ hQ hind (by decide) e hZ inf_le_right
    (IsElemAbelian.mono hR.1.2.1.2.1 inf_le_left) (by simpa [Fintype.card_sum] using h6)
    hT2 hTN hET

theorem ne_bstar_of_twD7
    (hR : GGSecFiveRestHyp 3 B Bs x L D J)
    (hAt : GGSecFiveWeylAtJoin 3 B Bs x L D J CoxeterMatrix.E₈)
    (hm : LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 7 ∧ lab.n = 1)) :
    B ≠ Bs := by
  have hZ : Subgroup.center ↥L = ⊥ :=
    center_eq_bot_of_fsEndMarking (fun _ hl => ⟨Or.inr (Or.inl ⟨hl.1, hl.2.1⟩), hl.2.2⟩) hm
  have hFSLab : LargeEvenMarking L (fun lab _ _ _ _ _ => FSLab lab) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨h.2.2, Or.inr (Or.inl ⟨h.1, h.2.1⟩)⟩) hm
  have hN : (L.subgroupOf (Subgroup.centralizer ({x} : Set G))).Normal :=
    fsEnds_normal B Bs x L D J hR hFSLab
  obtain ⟨e⟩ := nonempty_mulEquiv_omegaMinusSeven_of_marking hm hZ
  have hQ : GoodQ (StatedQuadMinus 7 (ZMod 2) 1 1) := goodQ_minus (n := 6) (by omega)
  have hind : OmegaTwoAutInduced (StatedQuadMinus 7 (ZMod 2) 1 1) :=
    omegaTwoAutInduced_minus_of_three_le (n := 6) (by omega)
  have hsup := bstar_eq_sup_of_restHyp hR hN hZ (autThreePowInner_of_goodQ hQ hind e)
  obtain ⟨𝒦, -, -, hM⟩ := hAt
  have hBscard : 3 ^ 8 ≤ Nat.card Bs :=
    pow_le_card_of_weylOfType_of_two Nat.prime_three (by norm_num) hR.1.2.1.2.1 hM
      exists_elemAbelian_two_coxeterE8
  have hle := card_bstar_le_three_mul_inf hR hsup.2
  have h7 : 3 ^ 7 ≤ Nat.card ↥(Bs ⊓ L) := by
    have hmul : 3 * 3 ^ 7 ≤ 3 * Nat.card ↥(Bs ⊓ L) := by
      calc 3 * 3 ^ 7 = 3 ^ 8 := by norm_num
        _ ≤ Nat.card Bs := hBscard
        _ ≤ 3 * Nat.card ↥(Bs ⊓ L) := hle
    exact Nat.le_of_mul_le_mul_left hmul (by norm_num)
  refine ne_bstar_of_le_centralizer hR hN hsup.2 (fun T hT2 hTN hET => ?_)
  exact le_centralizer_of_goodQ hQ hind (by decide) e hZ inf_le_right
    (IsElemAbelian.mono hR.1.2.1.2.1 inf_le_left) (by simpa [Fintype.card_sum] using h7)
    hT2 hTN hET

theorem ne_bstar_of_E7
    (hR : GGSecFiveRestHyp 3 B Bs x L D J)
    (hAt : GGSecFiveWeylAtJoin 3 B Bs x L D J CoxeterMatrix.E₈)
    (hm : LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .E7 ∧ lab.rank = 0 ∧ lab.n = 1)) :
    B ≠ Bs := by
  have hZ : Subgroup.center ↥L = ⊥ :=
    center_eq_bot_of_fsEndMarking (fun _ hl => ⟨Or.inr (Or.inr ⟨hl.1, hl.2.1⟩), hl.2.2⟩) hm
  have hFSLab : LargeEvenMarking L (fun lab _ _ _ _ _ => FSLab lab) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨h.2.2, Or.inr (Or.inr ⟨h.1, h.2.1⟩)⟩) hm
  have hN : (L.subgroupOf (Subgroup.centralizer ({x} : Set G))).Normal :=
    fsEnds_normal B Bs x L D J hR hFSLab
  obtain ⟨⟨t, r, n⟩, ⟨hmt, -, hn⟩, hlab⟩ := exists_glaLabel hm
  dsimp only at hmt hn
  subst hn
  have ht : t = .E7 := hmt
  obtain ⟨φ⟩ := exists_mulEquiv_adjointGroup_of_isLabel_E7' (lab := ⟨t, r, 1⟩) hlab ht hZ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKcard : Nat.card (GaloisField 2 1) = 2 := by
    simpa using GaloisField.card 2 1 (by omega)
  have hsup := bstar_eq_sup_of_restHyp hR hN hZ (autThreePowInner_of_E7Two hKcard φ)
  obtain ⟨𝒦, -, -, hM⟩ := hAt
  have hBscard : 3 ^ 8 ≤ Nat.card Bs :=
    pow_le_card_of_weylOfType_of_two Nat.prime_three (by norm_num) hR.1.2.1.2.1 hM
      exists_elemAbelian_two_coxeterE8
  have hle := card_bstar_le_three_mul_inf hR hsup.2
  have h7 : 3 ^ 7 ≤ Nat.card ↥(Bs ⊓ L) := by
    have hmul : 3 * 3 ^ 7 ≤ 3 * Nat.card ↥(Bs ⊓ L) := by
      calc 3 * 3 ^ 7 = 3 ^ 8 := by norm_num
        _ ≤ Nat.card Bs := hBscard
        _ ≤ 3 * Nat.card ↥(Bs ⊓ L) := hle
    exact Nat.le_of_mul_le_mul_left hmul (by norm_num)
  refine ne_bstar_of_le_centralizer hR hN hsup.2 (fun T hT2 hTN hET => ?_)
  exact le_centralizer_of_E7Two hKcard φ hZ inf_le_right
    (IsElemAbelian.mono hR.1.2.1.2.1 inf_le_left) h7 hT2 hTN hET

private theorem marking_or_of_label {X : Type} [Group X] {P Q : LargeEvenLabel → Prop}
    (h : LargeEvenMarking X (fun lab _ _ _ _ _ => P lab ∨ Q lab)) :
    LargeEvenMarking X (fun lab _ _ _ _ _ => P lab) ∨
      LargeEvenMarking X (fun lab _ _ _ _ _ => Q lab) := by
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  obtain ⟨R, _, I, F, -, -, θ, hPQ⟩ := largeEvenRawDatum_exists hraw
  rcases hPQ with hP | hQ
  · exact Or.inl ⟨hX, lab, hlab,
      largeEvenRawDatum_mono (fun R _ I F hc => ⟨hc.1, hc.2.1, hc.2.2.choose, hP⟩) hraw⟩
  · exact Or.inr ⟨hX, lab, hlab,
      largeEvenRawDatum_mono (fun R _ I F hc => ⟨hc.1, hc.2.1, hc.2.2.choose, hQ⟩) hraw⟩

theorem ggFSxEndsCardJoinInput_holds :
    GGFSxEndsCardJoinInput := by
  intro G _ _ B Bs x L D J hR hW hq
  refine ⟨?_, ?_⟩
  · intro hAt hm
    exact card_bstar_eq_of_ne hR (ne_bstar_of_D6 hR hAt hm)
  · intro hAt hm
    have hsplit : LargeEvenMarking L (fun lab _ _ _ _ _ =>
        lab.tag = .twD ∧ lab.rank = 7 ∧ lab.n = 1) ∨
        LargeEvenMarking L (fun lab _ _ _ _ _ =>
          lab.tag = .E7 ∧ lab.rank = 0 ∧ lab.n = 1) := by
      have hm' : LargeEvenMarking L (fun lab _ _ _ _ _ =>
          (lab.tag = .twD ∧ lab.rank = 7 ∧ lab.n = 1) ∨
            (lab.tag = .E7 ∧ lab.rank = 0 ∧ lab.n = 1)) :=
        largeEvenMarking_mono (fun _ _ _ _ _ _ h => by
          rcases h with ⟨h | h, hn⟩
          · exact Or.inl ⟨h.1, h.2, hn⟩
          · exact Or.inr ⟨h.1, h.2, hn⟩) hm
      exact marking_or_of_label hm'
    rcases hsplit with hmD | hmE7
    · exact card_bstar_eq_of_ne hR (ne_bstar_of_twD7 hR hAt hmD)
    · exact card_bstar_eq_of_ne hR (ne_bstar_of_E7 hR hAt hmE7)

end CFSG.StandardType.FrameRoute

end
