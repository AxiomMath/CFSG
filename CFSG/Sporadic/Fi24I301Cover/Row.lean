module

public import CFSG.Sporadic.Fi24I301.Row
public import CFSG.Sporadic.Fi24I301Cover.Forms
public import CFSG.Sporadic.Fi24I301Cover.Layer
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301CoverQuot
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301CoverSplit

public section

namespace CFSG.Sporadic.Fi24I301Cover

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8 CFSG.LocalAnalysis.GLTheoremA.H301
open CFSG.Sporadic.FischerOddCore CFSG.Sporadic.Fi24I301
  CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime
  CFSG.EvenSporadicStandard.TwoFi22.DS81
open CFSG.Sporadic.Fi24 (J)


theorem isSolvable_centralizer_dJ_inf_normalizer :
    Group.IsSolvable ↥(Subgroup.centralizer ({dJ} : Set J) ⊓ Subgroup.normalizer (RJ : Set J)) := by
  haveI := isSolvable_centralizer_dJ_inf card_fi24P_inf_centralizer_psi
  exact Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective (inf_le_inf le_rfl normalizer_RJ_le))

theorem isSolvable_centralizer_dJ_inf_centralizer :
    Group.IsSolvable ↥(Subgroup.centralizer ({dJ} : Set J) ⊓
      Subgroup.centralizer (centerOf (rowR0Of dJ RJ) : Set J)) := by
  haveI := isSolvable_centralizer_dJ_inf card_fi24P_inf_centralizer_psi
  have hle : Subgroup.centralizer (centerOf (rowR0Of dJ RJ) : Set J) ≤ fi24C := by
    refine Subgroup.centralizer_le ?_
    rw [Set.singleton_subset_iff]
    refine ⟨⟨fi24R2, fi24R2_mem_rowR0⟩, Subgroup.mem_center_iff.2 fun r => Subtype.ext ?_, rfl⟩
    exact comm_fi24R2_of_mem_C (RJ_le_C (Subgroup.mem_inf.1 r.2).1)
  exact Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective (inf_le_inf le_rfl hle))

theorem fi24h_split (E : Type) [Group E] [Finite E]
    (π : E →* J) (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center E)
    (hk3 : Nat.card π.ker = 3) :
    ∃ Bh : Subgroup E, IsElemAbelian 3 Bh ∧ Bh ⊓ Subgroup.center E = ⊥ ∧ Bh.map π = B1J ∧
      ∃ dh ∈ Bh, π dh = dJ := by
  obtain ⟨Bh, hBh, hBhk, hBhmap, hlift⟩ := exists_elemAbelian_complement_of_noForms π hπ hker.le
    hk3 (fun i : Fin 5 => xJ i) (fun i j => xJ_comm i.isLt j.isLt) (fun i => xJ_pow_three i.isLt)
    (fun k : Fin 2 => nJ k) nMat (fun k i => nJ_conj_ofFn k i) nMat_noAlt noLinForm xJ_indep_ofFn
  obtain ⟨dh, hdh, hdhπ⟩ := hlift 0
  exact ⟨Bh, hBh, by rw [← hker]; exact hBhk, by rw [hBhmap, range_xJ], dh, hdh, hdhπ⟩

theorem fi24h_hI
    (E : Type) [Group E] [Finite E] (π : E →* J) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.center E) (hk3 : Nat.card π.ker = 3)
    (_ : ⁅(⊤ : Subgroup E), (⊤ : Subgroup E)⁆ = ⊤) (dh : E) (hdh : π dh = dJ) :
    RowI .fi24h 3 (rowIOf 3 dh) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 isConj_dJ
  obtain ⟨ĉ, rfl⟩ := hπ c
  have hs : π (ĉ * dh * ĉ⁻¹) =
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three.fi24Rep3 0 := by
    rw [map_mul, map_mul, map_inv, hdh, hc]
  have hconj : IsConj (ĉ * dh * ĉ⁻¹) dh := isConj_iff.2 ⟨ĉ⁻¹, by group⟩
  exact isTypeWithCenter_glaPLayer_centralizer_of_isConj hconj
    (isTypeWithCenter_layer_cover_rep0 π hπ hker.le (by rw [hk3]; decide) hs)

theorem i301ARowCover_fi24h :
    I301ARowCover .fi24h :=
  @i301ARowCover_of_model .fi24 .fi24h rfl rfl rfl rfl rfl (fun _ _ _ => rfl) J inferInstance
    inferInstance nonempty_jEquiv _ _ _ i301ARowCfg_fi24 rowKOf_fi24
    isSolvable_centralizer_dJ_inf_normalizer isSolvable_centralizer_dJ_inf_centralizer
    fi24h_split fi24h_hI

end CFSG.Sporadic.Fi24I301Cover
