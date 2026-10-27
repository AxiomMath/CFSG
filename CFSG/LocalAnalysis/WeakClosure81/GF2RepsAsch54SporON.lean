module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Inputs
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporGen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ONanLatticePar

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ONanLatticeModel
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CalL0
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporOrder
import CFSG.LocalAnalysis.WeakClosure81.W18ASNineCF
import CFSG.Sporadic.Schreier.SteinbergBIONOuterTwo

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)
open CFSG.ONSchreier CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.ComponentClassification.CatLeaf (lieOrderDivisor lieOrderNumerator)

theorem isSylowIn_onT_subgroupOf :
    IsSylowIn 2 (onT.subgroupOf Pv) ⊤ :=
  ⟨le_top, onT_isPGroup, by rw [Subgroup.relIndex_top_right]; exact onT_not_dvd_index⟩

section


theorem not_hasCompFactor_isCalL0_onM :
    ¬ HasCompFactor (onM.subgroupOf Pv) IsCalL0 := by
  rintro ⟨K, _, hK, hcal⟩
  have hO := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  have : Finite K := isCompositionFactor_finite hK
  have hL3 := onl_secL3_C K (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20b_simpSec_of_cf hK)
    (isCalL0_nonabelian_not_sectionalTwoRankLE K hcal).1
  obtain ⟨-, hord, -⟩ := hO K .PSL 3 2 2 (Blueprint.LieModel.admissible hL3) hL3
  have hD : lieOrderDivisor .PSL 3 (2 ^ 2) = 3 := by decide +kernel
  have hN : lieOrderNumerator .PSL 3 (2 ^ 2) = 60480 := by decide +kernel
  rw [hD, hN] at hord
  exact not_isCalL0_of_card hO (k := 6) (N := 20160) (by decide +kernel) (by omega) hcal

theorem not_hasCompFactor_isCalL0_parP :
    ¬ HasCompFactor ONPar.parP IsCalL0 :=
  not_hasCompFactor_isCalL0_of_dvd CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
    (k := 9) (N := 1536) (by decide +kernel) (dvd_of_eq ONPar.card_parP)

theorem isLPair_onM_parP :
    IsLPair IsCalL0 (onT.subgroupOf Pv) (onM.subgroupOf Pv) ONPar.parP where
  le_left := fun _ hx => Subgroup.mem_subgroupOf.2 (ONPar.onT_le_M (Subgroup.mem_subgroupOf.1 hx))
  le_right := ONPar.Tp_le_parP
  ne_top_left h := by
    have h1 := congrArg (fun H : Subgroup Pv => Nat.card H) h
    simp only [Subgroup.card_top, card_Pv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe onM_le).toEquiv, card_onM] at h1
    omega
  ne_top_right h := by
    have h1 := congrArg (fun H : Subgroup Pv => Nat.card H) h
    simp only [Subgroup.card_top, card_Pv, ONPar.card_parP] at h1
    omega
  not_left := not_hasCompFactor_isCalL0_onM
  not_right := not_hasCompFactor_isCalL0_parP
  sup_eq_top := by rw [sup_comm]; exact ONPar.parP_sup_M


theorem asch54ONGen_holds : Asch54ONGen := by
  intro Q _ _ L T hLn hφ hC hT
  obtain ⟨φ⟩ := hφ
  have := hLn
  exact lGen_eq_top_of_isLPair_of_aut
    (fun X _ _ hX => (isCalL0_nonabelian_not_sectionalTwoRankLE X hX).1)
    (Nat.le_of_dvd two_pos Sporadic.SteinbergBI.card_outer_Pv_dvd_two) isSylowIn_onT_subgroupOf
    isLPair_onM_parP (fun ψ hψ => ⟨onl_C_inv ψ hψ, ONPar.parP_map hψ⟩) L (φ.trans onEquivPv) hC
    hT

theorem asch54SporGenAt_onan :
    Asch54SporGenAt .ONan := by
  intro Q _ _ L T hLn hs hC hT
  obtain ⟨e⟩ := hs
  obtain ⟨f⟩ := Sporadic.Bridge.ON.nonempty_mulEquiv
  exact asch54ONGen_holds Q L T hLn ⟨e.trans f.symm⟩ hC hT

end

end CFSG.LocalAnalysis.WeakClosure81

end
