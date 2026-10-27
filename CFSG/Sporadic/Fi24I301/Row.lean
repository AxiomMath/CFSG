module

public import CFSG.Sporadic.Fi24I301.Basic
public import CFSG.Sporadic.Fi24I301.ClassP
public import CFSG.Sporadic.Fi24I301.Local
public import CFSG.Sporadic.Fi24I301.Layer
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Fi24Max
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Solv
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Transport

public section

namespace CFSG.Sporadic.Fi24I301

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8 CFSG.LocalAnalysis.GLTheoremA.H301
open CFSG.Sporadic.FischerOddCore CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime
  CFSG.EvenSporadicStandard.TwoFi22.DS81
open CFSG.Sporadic.Fi24 (J)


theorem glaPLayer_eq_bot_of_le {X : Subgroup J}
    (hX : X ≤ Subgroup.centralizer ({dJ} : Set J) ⊓ fi24C) : GLAPLayer 3 X = ⊥ := by
  haveI := isSolvable_centralizer_dJ_inf card_fi24P_inf_centralizer_psi
  haveI : Group.IsSolvable ↥X :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hX)
  exact glaPLayer_eq_bot_of_isSolvable Nat.prime_three

theorem rowKOf_fi24 : rowKOf 3 dJ RJ = ⊥ :=
  glaPLayer_eq_bot_of_le (inf_le_inf
    (by unfold rowIOf GLAPLayer; exact sSup_le fun _ hQ => hQ.1) normalizer_RJ_le)

theorem fi24R2_mem_rowR0 : fi24R2 ∈ rowR0Of dJ RJ :=
  Subgroup.mem_inf.2 ⟨fi24R2_mem_RJ, (Subgroup.mem_centralizer_singleton_iff (G := J)).2
    (comm_fi24R2_of_mem_C (xJ_mem 0)).symm⟩

theorem fi24_hK6 : rowKOf 3 dJ RJ = GLAPLayer 3 (Subgroup.centralizer ({dJ} : Set J) ⊓
    Subgroup.centralizer (centerOf (rowR0Of dJ RJ) : Set J)) := by
  rw [rowKOf_fi24, glaPLayer_eq_bot_of_le (inf_le_inf le_rfl ?_)]
  refine Subgroup.centralizer_le ?_
  rw [Set.singleton_subset_iff]
  refine ⟨⟨fi24R2, fi24R2_mem_rowR0⟩, Subgroup.mem_center_iff.2 fun r => Subtype.ext ?_, rfl⟩
  exact comm_fi24R2_of_mem_C (RJ_le_C (Subgroup.mem_inf.1 r.2).1)

theorem i301ARowCfg_fi24 :
    I301ARowCfg .fi24 RJ B1J dJ := by
  have hBC := B1J_le_C
  exact
  { hR := fi24_hR
    hB := fi24_hB
    hBN := hBC.trans fi24C_le_normalizer_RJ
    hd := fi24_hd
    hI := isTypeWithCenter_glaPLayer_centralizer_of_isConj isConj_dJ.symm
      isTypeWithCenter_layer_rep0
    hK := rowKOf_fi24
    hR0 := card_rowR0_fi24
    hR0t := Or.inl rowR0_fi24_extraspecial
    hK6 := Or.inr fi24_hK6
    hNL := fun h => absurd h (by decide)
    hMax := by
      show ∀ (A : Type) [Group A] [Finite A] (ι : J →* A), Function.Injective ι →
        ι.range.Normal → Subgroup.centralizer (ι.range : Set A) = ⊥ →
        ∀ R' : Subgroup A, IsPGroup 2 R' →
          (rowKOf 3 dJ RJ ⊔ B1J).map ι ≤ Subgroup.normalizer (R' : Set A) →
          RJ.map ι ≤ R' → R' = RJ.map ι
      rw [rowKOf_fi24, bot_sup_eq]
      exact fi24_hMax catalogIs_J fi24_hR.1 fi24_hR.2 fi24R2_mem_RJ
        (fun q hq => comm_fi24R2_of_mem_C (RJ_le_C hq)) fi24R2_ne_one fi24_hB.1 fi24_hB.2
        (fun b hb => comm_fi24R2_of_mem_C (hBC hb)) (hBC.trans fi24C_le_normalizer_RJ) }

theorem i301ARow_fi24 :
    I301ARow .fi24 :=
  @i301ARow_of_model .fi24 J inferInstance inferInstance nonempty_jEquiv _ _ _ i301ARowCfg_fi24

end CFSG.Sporadic.Fi24I301
