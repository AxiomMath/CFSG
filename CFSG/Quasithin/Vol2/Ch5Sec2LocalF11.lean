module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem524
public import CFSG.Quasithin.Vol2.Ch5Sec1Facts
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.CharTwo
public import CFSG.LieType.CurtisTits.Conclusion

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace Hyp5_1_8

variable {G : Type} [Group G] [Finite G] {T M L H : Subgroup G} {n : ℕ}

theorem pCoreOf_oTwoUpper_ne_bot (hyp : Hyp5_1_8 G T M L H n) :
    pCoreOf 2 (oTwoUpper H) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have hH := hyp.hStar
  intro h0
  set K := oTwoUpper H with hKdef
  set Q := pCoreOf 2 H with hQ
  have hKH : K ≤ H := oTwoUpper_le H
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := le_normalizer_oTwoUpper H
  have hHQ : H ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf 2 H
  have hKQ : K ⊓ Q ≤ pCoreOf 2 K := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ ((pCoreOf_isPGroup 2 H).to_le inf_le_right)
    exact (le_inf Subgroup.le_normalizer (hKH.trans hHQ)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  rw [h0] at hKQ
  have hcomm : ⁅K, Q⁆ = ⊥ := by
    rw [eq_bot_iff, ← le_bot_iff.mp hKQ]
    refine le_inf ?_ ?_
    · exact Subgroup.le_normalizer_iff_commutator_le_left.mp ((pCoreOf_le 2 H).trans hHK)
    · exact Subgroup.le_normalizer_iff_commutator_le_right.mp (hKH.trans hHQ)
  have hKC : K ≤ Subgroup.centralizer (Q : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hchar : CharTwo H := charTwo_of_inH' h.qtke h.sylow hH.1
  have hKle : K ≤ Q := fun x hx => hchar ⟨hKH hx, hKC hx⟩
  have hK1 : K = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact hKQ ⟨hx, hKle hx⟩
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hH.1.1
  apply hH.2.1
  rw [eq_oTwoUpper_sup_of_isSylowTwoOf' hTH, ← hKdef, hK1, bot_sup_eq]
  exact h.T_le

end Hyp5_1_8

theorem isRankOneListed_oTwoQuot {G : Type} [Group G] {L : Subgroup G} {n : ℕ} (hn : 1 ≤ n)
    (h : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 n) : IsRankOneListed (oTwoQuot ↥L) := by
  have e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* oTwoQuot ↥L :=
    QuotientGroup.quotientMulEquivOfEq (CFSG.Quasithin.BlueprintB2.pCore_eq_open_pCore 2 ↥L)
  exact isRankOneListed_of_lieModel hn (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e h)

theorem stmtF11_5_2_of (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact) (h432 : Stmt4_3_2)
    (h510 : Stmt5_1_10) (h521 : Stmt5_2_1) (hL2 : Stmt5_2_L2) (hLie : Stmt5_2_L2Lie) :
    StmtF11_5_2 := by
  intro G _ _ T M L V H B D L₂ n hyp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have hN := hyp.notation59
  have hH := hyp.hStar
  obtain ⟨k, -, hBorel, -, -⟩ := h510 G T M L H B D n hyp.toHyp5_1_8 hN
  obtain ⟨hlist, hbor, -⟩ := hLie G T M L H B D L₂ n hyp.toHyp5_1_8 hN hyp.choice
  obtain ⟨hTL₂, hKL₂⟩ := hL2 G T M L H B D L₂ n hyp.toHyp5_1_8 hN hyp.choice
  have h524 := stmt5_2_4_of h331 hR h510 h521 hLie G T M L V H B D L₂ n hyp
  have hS2 : sec52S M H ≤ Subgroup.normalizer (L₂ : Set G) :=
    h521 G T M L H B D L₂ n hyp.toHyp5_1_8 hN hyp.choice hyp.notL34
  have hDL₂ : D ≤ Subgroup.normalizer (L₂ : Set G) :=
    le_sup_left.trans (le_sup_left.trans h524.2.2.2)
  set S := sec52S M H with hSdef
  have hSK : S ⊓ oTwoUpper H = T ⊓ oTwoUpper H := hyp.toHyp5_1_8.inf_oTwoUpper_eq hBorel
  have hL₂K := hyp.choice.le_oTwoUpper
  have hSL₂ : S ⊓ L₂ = T ⊓ L₂ := by
    rw [← inf_eq_right.mpr hL₂K, ← inf_assoc, hSK, inf_assoc]
  have hSL : S ⊓ L = T ⊓ L := h.inf_L_eq h331 hR hH
  have hborL₂ : borelOf L₂ S = borelOf L₂ T := by
    unfold borelOf
    rw [hSL₂]
  have hborL : borelOf L S = borelL T L := by
    unfold borelOf
    rw [hSL]
  have hSM : S ≤ M := (pCoreOf_le 2 _).trans inf_le_left
  have hSH : S ≤ H := (pCoreOf_le 2 _).trans inf_le_right
  have hS2grp : IsPGroup 2 ↥S := pCoreOf_isPGroup 2 _
  have hTLS : T ⊓ L ≤ S := hSL ▸ inf_le_left
  have hDTL : D ⊔ (T ⊓ L) = borelL T L := h.borelL_eq_sup hN.2.1
  have hTMH : T ≤ M ⊓ H := le_inf h.T_le hH.1.1
  have hO2le : ∀ X : Subgroup G, T ≤ X → M ⊓ H ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) →
      pCoreOf 2 X ≤ S := by
    intro X hTX hMHX
    have hXT : pCoreOf 2 X ≤ T := F7.isSylowTwoOf_pCoreOf_le (h.isSylowTwoOf hTX)
    exact le_pCoreOf_of_le_normalizer 2 (hXT.trans hTMH) hMHX (pCoreOf_isPGroup 2 X)
  have hOM : pCoreOf 2 M ≤ S :=
    hO2le M h.T_le (inf_le_left.trans (le_normalizer_pCoreOf 2 M))
  set Mp := Subgroup.normalizer (oTwoUpper H : Set G) with hMp
  have hHMp : H ≤ Mp := le_normalizer_oTwoUpper H
  have hTMp : T ≤ Mp := hH.1.1.trans hHMp
  have hOMp : pCoreOf 2 Mp ≤ S :=
    hO2le Mp hTMp ((inf_le_right.trans hHMp).trans (le_normalizer_pCoreOf 2 Mp))
  have hMchar : CharTwo M := charTwo_of_inH' h.qtke h.sylow (inH_of_inM ⟨h.maxTwoLocal, h.T_le⟩)
  have hMpO : pCoreOf 2 Mp ≠ ⊥ := by
    intro h0
    apply hyp.toHyp5_1_8.pCoreOf_oTwoUpper_ne_bot
    have hle : pCoreOf 2 (oTwoUpper H) ≤ pCoreOf 2 Mp :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans Subgroup.le_normalizer)
        (normalizer_le_normalizer_pCoreOf 2 (oTwoUpper H)) (pCoreOf_isPGroup 2 _)
    rw [h0] at hle
    exact le_bot_iff.mp hle
  have hMpchar : CharTwo Mp := charTwo_of_inH' h.qtke h.sylow ⟨hTMp, hMpO⟩
  have ho2 : pCoreOf 2 (L ⊔ L₂ ⊔ S) = ⊥ := by
    obtain ⟨huniq, -⟩ := h432 G T M L h.simple h.nonabelian h.qtke h.sylow h.maxTwoLocal h.T_le
      h.maximal h.faithful h.L_le h.normal ⟨n, h.two_le, h.lie⟩
    by_contra hne
    have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 (L ⊔ L₂ ⊔ S) : Set G)) :=
      ⟨_, hne, pCoreOf_isPGroup 2 _, rfl⟩
    obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
    have hG0 : L ⊔ L₂ ⊔ S ≤ M' := (le_normalizer_pCoreOf 2 _).trans hle
    have hM'eq : M' = M := huniq M' hM' (le_sup_left.trans (le_sup_left.trans hG0))
    have hL2M : L₂ ≤ M := hM'eq ▸ (le_sup_right.trans le_sup_left).trans hG0
    have hKM : oTwoUpper H ≤ M := by
      rw [hKL₂]
      exact conjClosure_le fun t ht z hz =>
        M.mul_mem (M.mul_mem (h.T_le ht) (hL2M hz)) (M.inv_mem (h.T_le ht))
    have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hH.1.1
    exact hH.2.1 ((eq_oTwoUpper_sup_of_isSylowTwoOf' hTH).le.trans (sup_le hKM h.T_le))
  refine ⟨⟨inferInstance, hS2grp, hSM.trans h.normal, ?_, ?_, ?_, ?_⟩,
    ⟨inferInstance, hS2grp, hS2, ?_, hlist, ?_, ?_⟩, ho2⟩
  ·
    rw [hSL]
    exact A4.isSylowTwoOf_inf_normal (h.isSylowTwoOf le_sup_right) le_sup_left
      h.sup_le_normalizer
  ·
    exact isRankOneListed_oTwoQuot (by have := h.two_le; omega) h.lie
  ·
    rw [hborL₂]
    exact hbor.trans h.normal
  ·
    have hY : L ⊔ S ⊔ borelOf L₂ S ≤ M := by
      rw [hborL₂]
      exact sup_le (sup_le h.L_le hSM) hbor
    exact charTwo_of_pCore_centralizer_le hMchar hY
      (inf_le_left.trans (hOM.trans (le_sup_right.trans le_sup_left)))
  ·
    rw [hSL₂]
    exact hTL₂
  ·
    rw [hborL, ← hDTL]
    exact sup_le hDL₂ (hTLS.trans hS2)
  ·
    have hY : L₂ ⊔ S ⊔ borelOf L S ≤ Mp := by
      rw [hborL, ← hDTL]
      refine sup_le (sup_le (hL₂K.trans Subgroup.le_normalizer) (hSH.trans hHMp)) ?_
      exact sup_le hyp.D_le ((inf_le_left.trans hH.1.1).trans hHMp)
    exact charTwo_of_pCore_centralizer_le hMpchar hY
      (inf_le_left.trans (hOMp.trans (le_sup_right.trans le_sup_left)))

end CFSG.Quasithin.H13
