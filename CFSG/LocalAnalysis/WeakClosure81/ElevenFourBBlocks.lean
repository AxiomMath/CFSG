module

public import CFSG.LocalAnalysis.WeakClosure81.ElevenFourBFam
public import CFSG.LocalAnalysis.WeakClosure81.Eleven
public import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.RankThree.PartOne CFSG.CGT.PushingUp
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6 Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Setting11

variable {M V Q : Subgroup G}

theorem V_le_Q (hset : Setting11 M V Q) : V ≤ Q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVpg : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hset.isElemAbelian
  have hVcV : V ≤ Subgroup.centralizer (V : Set G) := fun v hv => by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (B2F.isElemAbelian_comm hset.isElemAbelian hv hw).symm
  let K₀ : Subgroup G := M ⊓ Subgroup.centralizer (V : Set G)
  have hVK : V ≤ K₀ := le_inf hset.V_le_M hVcV
  have hVnorm : (V.subgroupOf K₀).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hVK]
    exact inf_le_right.trans (Subgroup.centralizer_le_normalizer (V : Set G))
  have hVpg' : IsPGroup 2 (V.subgroupOf K₀) :=
    hVpg.of_equiv (Subgroup.subgroupOfEquivOfLe hVK).symm
  have hle : (V.subgroupOf K₀ : Subgroup ↥K₀) ≤ CFSG.pCore 2 ↥K₀ :=
    le_sSup ⟨hVnorm, hVpg'⟩
  obtain ⟨T, hT⟩ := sylow_of_isSylowOf (S := Q) (H := K₀) hset.sylowQ
  have hTs : CFSG.pCore 2 ↥K₀ ≤ (T : Subgroup ↥K₀) := CFSG.fitting_pCore_le_sylow T
  intro v hv
  have hv' : (⟨v, hVK hv⟩ : ↥K₀) ∈ (V.subgroupOf K₀ : Subgroup ↥K₀) := hv
  have hmem : (⟨v, hVK hv⟩ : ↥K₀) ∈ (T : Subgroup ↥K₀) := hTs (hle hv')
  rw [hT] at hmem
  exact (Subgroup.mem_subgroupOf (H := Q) (K := K₀)).1 hmem

theorem V_le_baum (hset : Setting11 M V Q) : V ≤ baum Q := by
  have hQCV : Q ≤ Subgroup.centralizer (V : Set G) := hset.sylowQ.1.trans inf_le_right
  have hVCQ : V ≤ Subgroup.centralizer (Q : Set G) := eleven_a hQCV
  have hZQ : omegaOneCenterOf (thompsonJ Q) ≤ Q :=
    (C1GN.omegaOneCenterOf_le_self (thompsonJ Q)).trans (C1GN.thompsonJ_le Q)
  refine le_inf (V_le_Q hset) ?_
  exact hVCQ.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hZQ))

theorem le_normalizer_of_isBTBlock (hset : Setting11 M V Q) {K E U : Subgroup G} (hUV : U ≤ V)
    (hE : IsBTBlock K Q E) : U ≤ Subgroup.normalizer (E : Set G) :=
  hUV.trans ((V_le_baum hset).trans (BHS6.baum_le_normalizer_of_isBTBlock hE))

theorem cStarIn_le (hset : Setting11 M V Q) (K : Subgroup G) : cStarIn K Q ≤ M := by
  have hQ2 : IsPGroup 2 Q := hset.sylowQ.2.1
  have hQne : Q ≠ ⊥ := fun h =>
    hset.V_ne_bot (le_bot_iff.1 ((V_le_Q hset).trans (le_of_eq h)))
  have hZQ : omegaOneCenterOf Q ≤ Q := CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le Q
  have hZne : omegaOneCenterOf Q ≠ ⊥ :=
    CFSG.QuasithinUnique.Setup.omegaOneCenterOf_ne_bot hQ2 hQne
  have hZchar : ((omegaOneCenterOf Q).subgroupOf Q).Characteristic :=
    CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf Q
  have hZ2 : IsPGroup 2 (omegaOneCenterOf Q) := hQ2.to_le hZQ
  have hnormZ : Subgroup.normalizer (omegaOneCenterOf Q : Set G) ≤ M :=
    eleven_b_char hset.uniqueMax hZQ hZchar hZne hZ2
  have hpart1 : K ⊓ Subgroup.centralizer (omegaOneCenterOf Q : Set G) ≤ M :=
    (inf_le_right.trans
      (Subgroup.centralizer_le_normalizer (omegaOneCenterOf Q : Set G))).trans hnormZ
  have hpart2 : cgsIn K (baum Q) ≤ M := by
    refine iSup_le fun C => iSup_le fun hCB => iSup_le fun hCne => iSup_le fun hCchar => ?_
    have hCQ : C ≤ Q := hCB.trans (C1GN.baum_le Q)
    have hCcharQ : (C.subgroupOf Q).Characteristic :=
      C1GN.characteristic_subgroupOf_trans (C1GN.baum_le Q) hCB (C1GN.characteristic_baum Q)
        hCchar
    have hC2 : IsPGroup 2 C := hQ2.to_le hCQ
    exact inf_le_right.trans (eleven_b_char hset.uniqueMax hCQ hCcharQ hCne hC2)
  exact sup_le hpart1 hpart2

theorem cStarIn_centralizer_ne (hset : Setting11 M V Q) {U : Subgroup G}
    (hU : U ∈ gammaEleven M V) :
    cStarIn (Subgroup.centralizer (U : Set G)) Q ≠ Subgroup.centralizer (U : Set G) := by
  intro h
  exact hU.2.2.1 (h ▸ cStarIn_le hset (Subgroup.centralizer (U : Set G)))

theorem charTwo_centralizer (hset : Setting11 M V Q) {U : Subgroup G} (hUV : U ≤ V)
    (hU0 : U ≠ ⊥) : CFSG.QuasithinUnique.CharTwo (Subgroup.centralizer (U : Set G)) := by
  have hVpg : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hset.isElemAbelian
  exact CFSG.QuasithinUnique.charTwo_iff_isCharacteristicP.2
    (eleven_e hset.charTwo hU0 (hVpg.to_le hUV))

end Setting11

@[expose] def elevenBlocksB (M Q U : Subgroup G) : Set (Subgroup G) :=
  {E | E ∈ bhsBlocks (Subgroup.centralizer (U : Set G)) Q ∧ ¬ E ≤ M}

theorem mem_elevenBlocksB_iff {M Q U E : Subgroup G} :
    E ∈ elevenBlocksB M Q U ↔ E ∈ bhsBlocks (Subgroup.centralizer (U : Set G)) Q ∧ ¬ E ≤ M :=
  Iff.rfl

theorem exists_isBHSFamily_centralizer {M V Q U : Subgroup G}
    (hset : Setting11 M V Q) (hU : U ∈ gammaEleven M V) :
    ∃ 𝒢 : Set (Subgroup G), IsBHSFamily (Subgroup.centralizer (U : Set G)) Q 𝒢 :=
  exists_isBHSFamily
    (hK := Setting11.charTwo_centralizer hset hU.1 hU.2.1)
    (hQ := eleven_two_sylow hset.isElemAbelian hset.V_le_M hset.uniqueMax hset.sylowQ hU)
    (hne := Setting11.cStarIn_centralizer_ne hset hU)

theorem eleven_three_B {M V Q U : Subgroup G}
    (hset : Setting11 M V Q) (hU : U ∈ gammaEleven M V) :
    Subgroup.centralizer (U : Set G) =
      Subgroup.centralizer (U : Set G) ⊓ M ⊔ (⨆ E ∈ elevenBlocksB M Q U, E) := by
  obtain ⟨𝒢, h𝒢⟩ := exists_isBHSFamily_centralizer hset hU
  have hK : CFSG.QuasithinUnique.CharTwo (Subgroup.centralizer (U : Set G)) :=
    Setting11.charTwo_centralizer hset hU.1 hU.2.1
  have hQsyl : CFSG.RankThree.PartOne.IsSylowOf 2 Q (Subgroup.centralizer (U : Set G)) :=
    eleven_two_sylow hset.isElemAbelian hset.V_le_M hset.uniqueMax hset.sylowQ hU
  refine le_antisymm ?_ ?_
  · calc Subgroup.centralizer (U : Set G)
        = cStarIn (Subgroup.centralizer (U : Set G)) Q ⊔ (⨆ E ∈ 𝒢, E) := h𝒢.sup_eq.symm
      _ ≤ Subgroup.centralizer (U : Set G) ⊓ M ⊔ (⨆ E ∈ elevenBlocksB M Q U, E) := by
          refine sup_le ?_ ?_
          · exact (le_inf (CFSG.CGT.PushingUpLit.BHS.cStarIn_le
                (Subgroup.centralizer (U : Set G)) Q)
                (Setting11.cStarIn_le hset
                  (Subgroup.centralizer (U : Set G)))).trans le_sup_left
          · refine iSup₂_le fun E hE => ?_
            by_cases hEM : E ≤ M
            · exact (le_inf (h𝒢.le hE) hEM).trans le_sup_left
            · refine (le_iSup₂ (f := fun E (_ : E ∈ elevenBlocksB M Q U) => E) E ?_).trans
                le_sup_right
              exact mem_elevenBlocksB_iff.2
                ⟨(IsBHSFamily.mem_iff h𝒢 hK hQsyl).1 hE, hEM⟩
  · refine sup_le inf_le_left ?_
    refine iSup₂_le fun E hE => ?_
    have hE𝒢 : E ∈ 𝒢 :=
      (IsBHSFamily.mem_iff h𝒢 hK hQsyl).2 (mem_elevenBlocksB_iff.1 hE).1
    exact (h𝒢.isBlock E hE𝒢).le

theorem exists_mem_elevenBlocksB {M V Q U : Subgroup G}
    (hset : Setting11 M V Q) (hU : U ∈ gammaEleven M V) : ∃ Y, Y ∈ elevenBlocksB M Q U := by
  by_contra hempty
  simp only [not_exists] at hempty
  have hbot : (⨆ E ∈ elevenBlocksB M Q U, E) = ⊥ := by
    rw [iSup_eq_bot]
    intro E
    rw [iSup_eq_bot]
    intro hE
    exact absurd hE (hempty E)
  have hthree := eleven_three_B hset hU
  rw [hbot, sup_bot_eq] at hthree
  exact hU.2.2.1 ((le_of_eq hthree).trans inf_le_right)

theorem isBlockOfInX_of_mem_elevenBlocksB {M V Q U Y : Subgroup G}
    (hset : Setting11 M V Q) (hU : U ∈ gammaEleven M V) (hY : Y ∈ elevenBlocksB M Q U) :
    IsBlockOfInX (Subgroup.centralizer (U : Set G)) Y := by
  obtain ⟨𝒢, h𝒢⟩ := exists_isBHSFamily_centralizer hset hU
  have hK : CFSG.QuasithinUnique.CharTwo (Subgroup.centralizer (U : Set G)) :=
    Setting11.charTwo_centralizer hset hU.1 hU.2.1
  have hQsyl : CFSG.RankThree.PartOne.IsSylowOf 2 Q (Subgroup.centralizer (U : Set G)) :=
    eleven_two_sylow hset.isElemAbelian hset.V_le_M hset.uniqueMax hset.sylowQ hU
  have hY𝒢 : Y ∈ 𝒢 :=
    (IsBHSFamily.mem_iff h𝒢 hK hQsyl).2 (mem_elevenBlocksB_iff.1 hY).1
  exact h𝒢.isBlockOfInX hK hQsyl hY𝒢

theorem pCoreOf_ne_bot_of_mem_elevenBlocksB {M V Q U Y : Subgroup G}
    (hset : Setting11 M V Q) (hU : U ∈ gammaEleven M V) (hY : Y ∈ elevenBlocksB M Q U) :
    pCoreOf 2 Y ≠ ⊥ := by
  obtain ⟨𝒢, h𝒢⟩ := exists_isBHSFamily_centralizer hset hU
  have hK : CFSG.QuasithinUnique.CharTwo (Subgroup.centralizer (U : Set G)) :=
    Setting11.charTwo_centralizer hset hU.1 hU.2.1
  have hQsyl : CFSG.RankThree.PartOne.IsSylowOf 2 Q (Subgroup.centralizer (U : Set G)) :=
    eleven_two_sylow hset.isElemAbelian hset.V_le_M hset.uniqueMax hset.sylowQ hU
  have hY𝒢 : Y ∈ 𝒢 :=
    (IsBHSFamily.mem_iff h𝒢 hK hQsyl).2 (mem_elevenBlocksB_iff.1 hY).1
  exact BHS6.pCoreOf_ne_bot (h𝒢.isBlock Y hY𝒢) (h𝒢.charTwo hK hQsyl hY𝒢)

theorem isBlockOfInX_conjSubgroup {K L : Subgroup G} (g : G) (h : IsBlockOfInX K L) :
    IsBlockOfInX (conjSubgroup K g) (conjSubgroup L g) := by
  obtain ⟨hLK, hsub, hX⟩ := h
  exact ⟨conjSubgroup_mono_left g hLK,
    CFSG.GroupTheory.isSubnormal_subgroupOf_conjugate g hsub, inClassX_conjugate hX g⟩

end CFSG.LocalAnalysis.WeakClosure81
