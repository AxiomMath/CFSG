module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporGen
public import CFSG.Sporadic.Fi23.StarKernel
public import CFSG.Sporadic.FischerOddCore.Fi23Aut
public import Certificates.Certificate75340

import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporOrder
import CFSG.LocalAnalysis.WeakClosure81.W18ASNineCF
import CFSG.Quasithin.Vol2.Ch8Sec2L829LN1

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)
open CFSG.Sporadic.Fi23 CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Perm CFSG.Perm.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Asch54Fi23

theorem b0_exists :
    ∃ B : Subgroup CFSG.Sporadic.Fi23.J, slvl 0 ≤ B ∧ slvl 0 ≤ Subgroup.centralizer ({conjPt 2776} : Set CFSG.Sporadic.Fi23.J) ∧
      Nat.card B = 318504960 ∧ ¬ B ≤ Subgroup.centralizer ({conjPt 2776} : Set CFSG.Sporadic.Fi23.J) :=
  Certificates.certificate75340

noncomputable def B0 :
    Subgroup CFSG.Sporadic.Fi23.J :=
  Classical.choose b0_exists

theorem b0_spec :
    slvl 0 ≤ B0 ∧ slvl 0 ≤ Subgroup.centralizer ({conjPt 2776} : Set CFSG.Sporadic.Fi23.J) ∧
      Nat.card B0 = 318504960 ∧ ¬ B0 ≤ Subgroup.centralizer ({conjPt 2776} : Set CFSG.Sporadic.Fi23.J) :=
  Classical.choose_spec b0_exists

theorem card_B0 :
    Nat.card B0 = 318504960 :=
  b0_spec.2.2.1

theorem slvl_zero_le_B0 :
    slvl 0 ≤ B0 :=
  b0_spec.1

@[expose] noncomputable def dP : CFSG.Sporadic.Fi23.J := conjPt 2776

theorem dP_mem : dP ∈ D23 :=
  (isConj_d_iff _).2 ⟨⟨2776, by decide⟩, rfl⟩

noncomputable abbrev A0 : Subgroup CFSG.Sporadic.Fi23.J :=
  Subgroup.centralizer ({dP} : Set CFSG.Sporadic.Fi23.J)

theorem slvl_zero_le_A0 :
    slvl 0 ≤ A0 :=
  b0_spec.2.1

theorem not_B0_le_A0 :
    ¬ B0 ≤ A0 :=
  b0_spec.2.2.2

theorem not_hasCompFactor_isCalL0_centralizer_d :
    ¬ HasCompFactor (Subgroup.centralizer ({d} : Set CFSG.Sporadic.Fi23.J)) IsCalL0 := by
  rintro ⟨L, _, hL, hcal⟩
  have hO := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  rcases isCompositionFactor_of_normal rho.ker hL with h1 | h2
  · exact not_isCalL0_of_isCompositionFactor_of_dvd hO (k := 1) (N := 2) (by decide +kernel)
      (dvd_of_eq card_ker_rho) h1 hcal
  · have h3 := (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr
      (QuotientGroup.quotientKerEquivRange rho)).1 h2
    have h4 := (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr
      (MulEquiv.subgroupCongr range_rho)).1 h3
    have : IsSimpleGroup pi22.range := by
      have := CFSG.Sporadic.Fi22.isSimpleGroup_J
      exact (MonoidHom.ofInjective pi22_injective).symm.isSimpleGroup
    exact not_isCalL0_of_isCompositionFactor_of_isSimpleGroup hO (k := 17)
      (by rw [card_range_pi22]; decide +kernel) h4 hcal

private theorem hasCompFactor_centralizer_conj {G : Type} [Group G]
    (P : ∀ (X : Type) [Group X], Prop) (c x : G) :
    HasCompFactor (Subgroup.centralizer ({c * x * c⁻¹} : Set G)) P ↔
      HasCompFactor (Subgroup.centralizer ({x} : Set G)) P := by
  have e := CFSG.Fischer.centralizer_singleton_eq_map (MulAut.conj c) x
  rw [MulAut.conj_apply] at e
  rw [e]
  exact hasCompFactor_map_of_injective _ (MulAut.conj c).injective _

theorem not_hasCompFactor_isCalL0_A0 :
    ¬ HasCompFactor A0 IsCalL0 := by
  obtain ⟨c, hc⟩ := isConj_iff.1 dP_mem
  rw [A0, ← hc, hasCompFactor_centralizer_conj]
  exact not_hasCompFactor_isCalL0_centralizer_d

theorem not_hasCompFactor_isCalL0_B0 :
    ¬ HasCompFactor B0 IsCalL0 :=
  not_hasCompFactor_isCalL0_of_dvd CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
    (k := 18) (N := 318504960) (by decide +kernel) (dvd_of_eq card_B0)

theorem isSylowIn_slvl_zero :
    IsSylowIn 2 (slvl 0) ⊤ :=
  ⟨le_top, IsPGroup.of_card (n := 18) (by rw [card_slvl_zero]; norm_num),
    by rw [Subgroup.relIndex_top_right, slvl_index]; decide⟩

theorem isLPair_A0_B0 :
    IsLPair IsCalL0 (slvl 0) A0 B0 where
  le_left := slvl_zero_le_A0
  le_right := slvl_zero_le_B0
  ne_top_left := (isCoatom_centralizer_of_mem dP_mem).1
  ne_top_right h := by
    have h1 := congrArg (fun H : Subgroup CFSG.Sporadic.Fi23.J => Nat.card H) h
    simp only [Subgroup.card_top, card_B0, CFSG.Sporadic.Fi23.card_J] at h1
    omega
  not_left := not_hasCompFactor_isCalL0_A0
  not_right := not_hasCompFactor_isCalL0_B0
  sup_eq_top := (isCoatom_centralizer_of_mem dP_mem).2 _
    (lt_of_le_of_ne le_sup_left fun h => not_B0_le_A0 (le_sup_right.trans h.ge))

end Asch54Fi23

open Asch54Fi23 in
theorem asch54SporGenAt_fi23 :
    Asch54SporGenAt .Fi23 := by
  have hfin : Finite CFSG.Blueprint.NativeSporadic.Fi23 := Finite.of_equiv CFSG.Sporadic.Fi23.J fi23EquivJ.symm.toEquiv
  have hs : Nonempty (TauCeti.SporadicName.Fi23.Group ≃* CFSG.Blueprint.NativeSporadic.Fi23) :=
    CFSG.Sporadic.Bridge.Fi23.nonempty_mulEquiv.map MulEquiv.symm
  have hT := @isSylowIn_top_map_mulEquiv (↥CFSG.Sporadic.Fi23.J) inferInstance CFSG.Blueprint.NativeSporadic.Fi23
    inferInstance 2 (slvl 0) isSylowIn_slvl_zero fi23EquivJ.symm
  have hP := @IsLPair.map (↥CFSG.Sporadic.Fi23.J) inferInstance IsCalL0 (slvl 0) A0 B0
    CFSG.Blueprint.NativeSporadic.Fi23 inferInstance isLPair_A0_B0 fi23EquivJ.symm
  exact @asch54SporGenAt_of_isLPair_of_card_outer_eq_one .Fi23
    CFSG.Blueprint.NativeSporadic.Fi23 inferInstance hfin hs
    CFSG.Sporadic.FischerOddCore.card_outer_fi23 _ _ _ hT hP

end CFSG.LocalAnalysis.WeakClosure81
