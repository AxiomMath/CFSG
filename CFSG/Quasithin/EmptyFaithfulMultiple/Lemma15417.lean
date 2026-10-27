module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Statements
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma116
public import CFSG.Quasithin.Background.A1a
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremE

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type*} [Group G]

private theorem evenCharacteristic_assembly_of_open (hev : quasithinEvenCharacteristic G) :
    CFSG.Assembly.Quasithin.quasithinEvenCharacteristic G :=
  hev

private theorem isSylowTwoOf_top_of_quasithinIsSylowTwo {T : Subgroup G}
    (hT : quasithinIsSylowTwo T) : IsSylowTwoOf T ⊤ := by
  refine ⟨le_top, hT.1, ?_⟩
  change ¬ 2 ∣ T.relIndex ⊤
  rw [Subgroup.relIndex_top_right]
  exact hT.2

variable [Finite G]

theorem lemma115Hyp_of_le {H I S M : Subgroup G} {z : G} (h : Lemma115Hyp H S M z)
    (hSI : S ≤ I) (hIH : I ≤ H) : Lemma115Hyp I S M z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSH : IsSylowTwoOf S H := h.sylow
  have hHI : pCoreOf 2 H ≤ pCoreOf 2 I :=
    CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer
      ((EscapingLocal.pCoreOf_le_of_isSylowTwoOf hSH).trans hSI)
      (hIH.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H))
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H)
  have hSHM : IsSylowTwoOf S (H ⊓ M) := B6.isSylowTwoOf_mono hSH h.S_le_inf inf_le_left
  have hQS : pCoreOf 2 (H ⊓ M) ≤ S := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hSHM
  have hQ : pCoreOf 2 (H ⊓ M) ≤ pCoreOf 2 (I ⊓ M) :=
    pCoreOf_le_pCoreOf_of_sylow (inf_le_inf_right M hIH) hSH.2.1 (le_inf hSI h.le) hSHM.2.2
  have hPH : pCoreOf 2 M ⊓ H ≤ pCoreOf 2 (H ⊓ M) := by
    refine CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer
      (le_inf inf_le_right (inf_le_left.trans
        (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 M))) ?_
      ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M).to_le inf_le_left)
    exact CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf _ _ _
      (inf_le_right.trans
        (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M))
      (inf_le_left.trans Subgroup.le_normalizer)
  refine
    { pCore_ne_bot := fun hI => h.pCore_ne_bot (le_bot_iff.mp (hI ▸ hHI))
      sylow := B6.isSylowTwoOf_mono hSH hSI hIH
      charTwo := h.charTwo
      pCore_M_ne_bot := h.pCore_M_ne_bot
      le := h.le
      centralizer_le := fun x hx => ?_
      centralizer_z_le := h.centralizer_z_le
      z_ne_one := h.z_ne_one
      z_mem := h.z_mem
      z_central := h.z_central
      z_sq := h.z_sq }
  have hxH : x ∈ H :=
    h.centralizer_le ⟨hx.1, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hQ) hx.2⟩
  exact hSI (hQS (hPH ⟨hx.1, hxH⟩))

theorem charTwo_of_omegaOneCenter_inf_pCoreOf_ne_bot
    (hev : CFSG.Assembly.Quasithin.quasithinEvenCharacteristic G) {T B H I : Subgroup G}
    (hT : IsSylowTwoOf T ⊤) (hBT : B ≤ T) (hBH : B ⊔ Subgroup.centralizer (B : Set G) ≤ H)
    (hHB : H ≤ Subgroup.normalizer (B : Set G)) (hS : IsSylowTwoOf (T ⊓ H) H)
    (hSI : T ⊓ H ≤ I) (hIH : I ≤ H) (hZ : quasithinOmegaOneCenter T ⊓ pCoreOf 2 I ≠ ⊥) :
    CharTwo I := by
  set D := pCoreOf 2 I
  set N := Subgroup.normalizer (D : Set G)
  have hB : IsPGroup 2 B := hT.2.1.to_le hBT
  have hBH' : B ≤ H := le_sup_left.trans hBH
  have hCH : Subgroup.centralizer (B : Set G) ≤ H := le_sup_right.trans hBH
  have hBD : B ≤ D :=
    CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer ((le_inf hBT hBH').trans hSI)
      (hIH.trans hHB) hB
  have hBN : B ≤ N := hBD.trans Subgroup.le_normalizer
  have hIN : I ≤ N := CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 I
  have hZT : quasithinOmegaOneCenter T ≤ T ⊓ Subgroup.centralizer (T : Set G) :=
    (Subgroup.closure_le _).mpr fun w hw => hw.1
  have hDZ : D ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) ≠ ⊥ := by
    intro hbot
    refine hZ (eq_bot_iff.mpr fun x hx => ?_)
    rw [← hbot]
    exact ⟨hx.2, hZT hx.1⟩
  have hNc : CharTwo N := charTwo_normalizer_of_inf_center hev hT
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 I) hDZ
  have hHN : CharTwo (H ⊓ N) :=
    charTwo_of_centralizer_sup_le_of_le_normalizer hNc hBN hB
      (sup_le (le_inf hBH' hBN) (le_inf (inf_le_right.trans hCH) inf_le_left))
      (le_inf inf_le_right (inf_le_left.trans hHB))
  have hIHN : I ≤ H ⊓ N := le_inf hIH hIN
  have hSHN : IsSylowTwoOf (T ⊓ H) (H ⊓ N) := B6.isSylowTwoOf_mono hS (hSI.trans hIHN) inf_le_left
  exact charTwo_of_pCore_centralizer_le hHN hIHN
    (inf_le_left.trans ((EscapingLocal.pCoreOf_le_of_isSylowTwoOf hSHN).trans hSI))

theorem stmt15417_of_evenCharacteristic (hev : quasithinEvenCharacteristic G) {T : Subgroup G}
    (hT : quasithinIsSylowTwo T) : Stmt15417 G T := by
  have hev' := evenCharacteristic_assembly_of_open hev
  have hT' := isSylowTwoOf_top_of_quasithinIsSylowTwo hT
  intro B H I hB1 hBT hBH hHB hS hSI hIH
  refine ⟨fun z hz hz1 Mz hMz => ?_,
    charTwo_of_omegaOneCenter_inf_pCoreOf_ne_bot hev' hT' hBT hBH hHB hS hSI hIH⟩
  obtain ⟨hzT, hzc, hz2⟩ := mem_quasithinOmegaOneCenter_iff.mp hz
  exact lemma115Hyp_of_le (lemma116 hev' (hT.1.to_le hBT) hB1 hBH hHB hS hT' inf_le_left hzT hzc
    hz1 hz2 hMz.1 hMz.2) hSI hIH

theorem stmt15417_of {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hyp : MultipleCentralizerHypothesis G T) : Stmt15417 G T :=
  stmt15417_of_evenCharacteristic hyp.qtke.2.1 hyp.sylow

end CFSG.Quasithin.EmptyFaithfulMultiple
