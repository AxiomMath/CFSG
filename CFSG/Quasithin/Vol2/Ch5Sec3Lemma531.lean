module

public import CFSG.Quasithin.Vol2.Ch5Sec3L3
import CFSG.Quasithin.Vol2.Ch1Unique
import CFSG.Quasithin.Vol2.Ch1A3Cat
import CFSG.Quasithin.Vol2.Ch5Sec1Basic
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native36
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native38
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134Final
import CFSG.Quasithin.Background.KnownMultTypes
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem conjClosure_eq_self_of_le_normalizer {Z H : Subgroup G}
    (h : H ≤ Subgroup.normalizer (Z : Set G)) : conjClosure Z H = Z := by
  refine le_antisymm ((Subgroup.closure_le _).mpr ?_) (le_conjClosure Z H)
  rintro _ ⟨g, hg, z, hz, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (h hg) z).mp hz

theorem isSylowTwoOf_of_le_of_le {S X L : Subgroup G} (hS : IsSylowTwoOf S L) (hSX : S ≤ X)
    (hXL : X ≤ L) : IsSylowTwoOf S X := by
  refine ⟨hSX, hS.2.1, fun h2 => hS.2.2 ?_⟩
  have e := Subgroup.relIndex_mul_relIndex S X L hSX hXL
  change 2 ∣ S.relIndex L
  rw [← e]
  exact dvd_mul_of_dvd_left h2 _

theorem pCoreOf_eq_of_isSylowTwoOf_of_normal [Finite G] {S X : Subgroup G}
    (hS : IsSylowTwoOf S X) (hn : X ≤ Subgroup.normalizer (S : Set G)) : pCoreOf 2 X = S :=
  le_antisymm (hS.le_of_normalizes (CFSG.LieType.BorelTits.pCoreOf_le 2 X)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X))
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hS.1 hn hS.2.1)

theorem stmt5_3_1_of
    (h39 : Vol2Native.A39ForSQTKCat) (hC58 : TheoremC58) (h511 : Stmt5_1_1)
    (h527 : Stmt5_2_7) : Stmt5_3_1 := by
  intro G _ _ T M L V H B D L₂ n t m f hyp hty hpar
  have : IsSimpleGroup G := hyp.simple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h37 : A37ForSQTK := a37ForSQTK_of_cat Vol2Native.a37ForSQTKCat_proved
  have h38 : A38ForSQTK := a38ForSQTK_of_cat (Vol2Native.a38ForSQTKCat_of_facts mult2Fact
    Vol2Native.a134SQTKFactCat Vol2Native.a36CoreForSQTKCat_proved
    Vol2Native.a37ForSQTKCat_proved)
  have h39' : A39ForSQTK := a39ForSQTK_of_cat h39
  have hLmax : quasithinIsMaximalLocal T L := hyp.maximal
  have hKmax : quasithinIsMaximalLocal T (oTwoUpper H) := hty.2
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hyp.T_le.trans hyp.normal
  have hTH : T ≤ H := hyp.hStar.1.1
  have hTK : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    hTH.trans (le_normalizer_oTwoUpper H)
  have hU1 : IsUniqueM (L ⊔ T) (sec53M1 L) := by
    have := lemma_1_2_7_three hyp.qtke hyp.simple hyp.nonabelian h37 h38 h39' hyp.sylow hLmax
    rwa [conjClosure_eq_self_of_le_normalizer hTL] at this
  have hU2 : IsUniqueM (oTwoUpper H ⊔ T) (sec53M2 H) := by
    have := lemma_1_2_7_three hyp.qtke hyp.simple hyp.nonabelian h37 h38 h39' hyp.sylow hKmax
    rwa [conjClosure_eq_self_of_le_normalizer hTK] at this
  have hMM1 : M = sec53M1 L := hU1.2 M ⟨hyp.maxTwoLocal, sup_le hyp.L_le hyp.T_le⟩
  have hHKT : H = oTwoUpper H ⊔ T :=
    eq_oTwoUpper_sup_of_isSylowTwoOf' (isSylowTwoOf_of_isSylowTwo hyp.sylow hTH)
  have hne : sec53M1 L ≠ sec53M2 H := by
    intro heq
    apply hyp.hStar.2.1
    rw [hHKT, hMM1, heq]
    exact sup_le Subgroup.le_normalizer hTK
  have hT1 : T ≤ sec53M1 L := hTL
  have hT2 : T ≤ sec53M2 H := hTK
  obtain ⟨-, ⟨-, -, -, hSL, hSK, hSO⟩, hOL, hOK⟩ := h527 G T M L V H B D L₂ n hyp
  have hB1 : B ≤ sec53M1 L := hyp.notation59.1.1.trans (inf_le_left.trans hyp.normal)
  have hB2 : B ≤ sec53M2 H :=
    hyp.notation59.1.1.trans (inf_le_right.trans (le_normalizer_oTwoUpper H))
  have hD1 : D ≤ sec53M1 L :=
    hyp.notation59.2.1.1.trans (inf_le_left.trans Subgroup.le_normalizer)
  have hO1 : pCoreOf 2 (sec53M1 L) = pCoreOf 2 L := by
    refine le_antisymm ?_ (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans Subgroup.le_normalizer)
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L))
    rw [hOL]
    exact pCoreOf_le_pCoreOf_of_sylow (isSylowTwoOf_of_isSylowTwo hyp.sylow hT1) le_sup_right
      (sup_le (sup_le (sup_le Subgroup.le_normalizer hB1) hD1) hT1)
  have hO2 : pCoreOf 2 (sec53M2 H) = pCoreOf 2 (oTwoUpper H) := by
    refine le_antisymm ?_ (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans Subgroup.le_normalizer)
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _))
    rw [hOK]
    exact pCoreOf_le_pCoreOf_of_sylow (isSylowTwoOf_of_isSylowTwo hyp.sylow hT2) le_sup_right
      (sup_le (sup_le (sup_le Subgroup.le_normalizer hB2) hyp.D_le) hT2)
  have hCT1 : CharTwo (sec53M1 L) :=
    charTwo_of_inH' hyp.qtke hyp.sylow ⟨hT1, pCoreOf_ne_bot_of_isTwoLocal hU1.1.1.1⟩
  have hCT2 : CharTwo (sec53M2 H) :=
    charTwo_of_inH' hyp.qtke hyp.sylow ⟨hT2, pCoreOf_ne_bot_of_isTwoLocal hU2.1.1.1⟩
  have hSK' : T ⊓ L = T ⊓ oTwoUpper H := hSL.symm.trans hSK
  have hSLs : IsSylowTwoOf (T ⊓ L) L := A4.isSylowTwoOf_inf_normal
    (isSylowTwoOf_of_isSylowTwo hyp.sylow (le_sup_right : T ≤ L ⊔ T)) le_sup_left
    (sup_le Subgroup.le_normalizer hTL)
  have hSKs : IsSylowTwoOf (T ⊓ L) (oTwoUpper H) := by
    rw [hSK']
    exact A4.isSylowTwoOf_inf_normal
      (isSylowTwoOf_of_isSylowTwo hyp.sylow (le_sup_right : T ≤ oTwoUpper H ⊔ T)) le_sup_left
      (sup_le Subgroup.le_normalizer hTK)
  obtain ⟨z, hz, hz2⟩ := exists_involution_sec53ZS hyp.toHyp5_0_1
  have hSne : sec53S T L ≠ ⊥ := fun h0 => by
    have hzS : z ∈ sec53S T L := (Subgroup.mem_inf.mp hz).1
    rw [h0, Subgroup.mem_bot] at hzS
    rw [hzS, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hTS : T ≤ Subgroup.normalizer (sec53S T L : Set G) :=
    le_normalizer_inf_of_normalizes Subgroup.le_normalizer hTL
  have hS2 : IsPGroup 2 (sec53S T L) := hyp.sylow.1.to_le inf_le_left
  have hSN : sec53S T L ≤ pCoreOf 2 (Subgroup.normalizer (sec53S T L : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hS2
  have hInHN : InH T (Subgroup.normalizer (sec53S T L : Set G)) :=
    ⟨hTS, fun h0 => hSne (le_bot_iff.mp (h0 ▸ hSN))⟩
  have h311 := theorem311Stmt_of_C58 hC58 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow
  have hN1 : Subgroup.normalizer (sec53S T L : Set G) ≤ sec53M1 L := by
    obtain ⟨N, hN⟩ := (h511 G T M L V n hyp.toHyp5_0_1 hyp.ch5Module).2.2.2
    have hsyl : IsSylowTwoOf (sec53S T L) (oTwoUpper (L ⊔ T) ⊔ sec53S T L) := by
      rw [hyp.oTwoUpper_sup_eq, sup_eq_left.mpr inf_le_right]
      exact hSLs
    obtain ⟨R₀, hR₀, hR₀S, hR₀N⟩ := h311 _ (L ⊔ T) (sec53S T L) hInHN ⟨le_sup_right,
      hLmax.1.2.2.2⟩ ⟨N, hN.uniqueMax⟩ hSne inf_le_left hsyl le_rfl
    refine le_sup_left.trans (hR₀N.trans (le_of_isUniqueM_of_isTwoLocal hU1
      ⟨R₀, hR₀, hS2.to_le hR₀S, rfl⟩ (le_sup_right.trans hR₀N)))
  have hN2 : Subgroup.normalizer (sec53S T L : Set G) ≤ sec53M2 H := by
    have hmin := ((h511 G T M L V n hyp.toHyp5_0_1 hyp.ch5Module).2.1 H hyp.hStar).1
    have hsyl : IsSylowTwoOf (sec53S T L) (oTwoUpper H ⊔ sec53S T L) := by
      rw [sup_eq_left.mpr (show sec53S T L ≤ oTwoUpper H from hSK'.le.trans inf_le_right)]
      exact hSKs
    obtain ⟨R₀, hR₀, hR₀S, hR₀N⟩ := h311 _ H (sec53S T L) hInHN hyp.hStar.1
      ⟨H ⊓ M, hmin.uniqueMax⟩ hSne inf_le_left hsyl le_rfl
    have hKT : oTwoUpper H ⊔ T ≤ Subgroup.normalizer (R₀ : Set G) :=
      hHKT ▸ (le_sup_right.trans hR₀N)
    exact le_sup_left.trans (hR₀N.trans (le_of_isUniqueM_of_isTwoLocal hU2
      ⟨R₀, hR₀, hS2.to_le hR₀S, rfl⟩ hKT))
  have hSLK : sec53S T L ≤ L ⊓ oTwoUpper H :=
    le_inf inf_le_right (hSK'.le.trans inf_le_right)
  have hLKG : L ⊓ oTwoUpper H ≤ (L ⊔ B ⊔ D) ⊓ (oTwoUpper H ⊔ B ⊔ D) :=
    inf_le_inf (le_sup_left.trans le_sup_left) (le_sup_left.trans le_sup_left)
  have hGS : (L ⊔ B ⊔ D) ⊓ (oTwoUpper H ⊔ B ⊔ D) ≤ Subgroup.normalizer (sec53S T L : Set G) := by
    rw [show sec53S T L = T ⊓ L from rfl, ← hSL, hSO]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hOLK : pCoreOf 2 (L ⊓ oTwoUpper H) = sec53S T L :=
    pCoreOf_eq_of_isSylowTwoOf_of_normal (isSylowTwoOf_of_le_of_le hSLs hSLK inf_le_left)
      (hLKG.trans hGS)
  have hM12S : sec53M12 L H ≤ Subgroup.normalizer (sec53S T L : Set G) := by
    rw [← hOLK]
    exact (le_normalizer_inf_of_normalizes inf_le_left inf_le_right).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  have hNS : Subgroup.normalizer (sec53S T L : Set G) = sec53M12 L H :=
    le_antisymm (le_inf hN1 hN2) hM12S
  refine ⟨⟨hLmax.1, hKmax.1, hU1, hU2, hne⟩, ⟨hCT1, hO1, hCT2, hO2⟩, ⟨hNS, ?_, ?_⟩, ?_, ?_⟩
  · exact le_antisymm (inf_le_right.trans hNS.le) (le_inf inf_le_left hM12S)
  · exact le_antisymm (inf_le_right.trans hNS.le) (le_inf inf_le_right hM12S)
  ·
    refine le_antisymm (sup_le Subgroup.le_normalizer inf_le_left) ?_
    have := B6.frattini_two (H := sec53M1 L) (N := L) Subgroup.le_normalizer le_rfl hSLs
    rw [show sec53M1 L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) = sec53M12 L H from
      le_antisymm (inf_le_right.trans hNS.le) (le_inf inf_le_left hM12S)] at this
    exact this
  · refine le_antisymm (sup_le Subgroup.le_normalizer inf_le_right) ?_
    have := B6.frattini_two (H := sec53M2 H) (N := oTwoUpper H) Subgroup.le_normalizer le_rfl hSKs
    rw [show sec53M2 H ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) = sec53M12 L H from
      le_antisymm (inf_le_right.trans hNS.le) (le_inf inf_le_right hM12S)] at this
    exact this

end CFSG.Quasithin.H13
