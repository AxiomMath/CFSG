module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
public import CFSG.Open.StatedDefs

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Levi
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympData
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympHas
import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherParabolicData
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.PCoreSp
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympLevi
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
import CFSG.ClassicalInvolution.Models.SymplecticPairs.Pairs
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
import CFSG.LocalAnalysis.AGLEmbedding.IIIaResidualDefs
import CFSG.LocalAnalysis.AGLEmbedding.J3MSideDefs
import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD

open CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.AGLEmbedding.LeviBlock
open Matrix

private lemma flag_succ_one_eq_span_singleton_D22 (m : ℕ) {K : Type} [Field K] :
    SymplecticFlag.flag (m + 1) K 1
      = Submodule.span K {Pi.single (Sum.inl (0 : Fin (m + 1))) (1 : K)} := by
  have hset : (fun j : Fin (m + 1) =>
        (Pi.single (Sum.inl j) (1 : K) : Fin (m + 1) ⊕ Fin (m + 1) → K)) ''
        {j | (j : ℕ) < 1}
      = {Pi.single (Sum.inl (0 : Fin (m + 1))) (1 : K)} := by
    ext v
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, hj, rfl⟩
      have hjval : (j : ℕ) = 0 := Nat.lt_one_iff.mp hj
      have hj0 : j = 0 := Fin.ext (by simpa using hjval)
      subst hj0
      rfl
    · intro hv
      exact ⟨0, by simp, hv.symm⟩
  rw [SymplecticFlag.flag, ite_eq_left (show 1 ≤ m + 1 by omega), SymplecticFlag.isoFlag,
    hset]

private lemma gl_mulVec_injective_D22 {n : Type} [Fintype n] [DecidableEq n] {K : Type} [Field K]
    (u : GL n K) : Function.Injective (((u : GL n K) : Matrix n n K).mulVec) :=
  Matrix.mulVec_injective_iff_isUnit.mpr ⟨u, rfl⟩

private lemma mem_stabilizer_span_singleton_iff_D22 {r : ℕ} {K : Type} [Field K]
    {A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} (hA : Function.Injective A.mulVec)
    {v : Fin r ⊕ Fin r → K} (hv : v ≠ 0) :
    (Submodule.span K {v}).map (Matrix.mulVecLin A) = Submodule.span K {v} ↔
      ∃ c : K, A *ᵥ v = c • v := by
  rw [Submodule.map_span, Set.image_singleton, Matrix.mulVecLin_apply]
  have hAv : A *ᵥ v ≠ 0 := fun h => hv (hA (by rw [h, Matrix.mulVec_zero]))
  constructor
  · intro h
    have hmem : A *ᵥ v ∈ Submodule.span K {v} := by
      rw [← h]
      exact Submodule.mem_span_singleton_self (A *ᵥ v)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := fun hcz => hAv (by rw [hc, hcz, zero_smul])
    rw [hc]
    exact Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc0) v

private lemma lineStab_statedSp_succ_eq_flagStabilizer_D22 (m : ℕ) {K : Type} [Field K] :
    lineStab (StatedSp (m + 1) K) (Pi.single (Sum.inl (0 : Fin (m + 1))) (1 : K))
      = SymplecticHigher.flagStabilizer (m + 1) K ({1} : Set ℕ) := by
  have hflag : SymplecticFlag.flag (m + 1) K 1
      = Submodule.span K {Pi.single (Sum.inl (0 : Fin (m + 1))) (1 : K)} :=
    flag_succ_one_eq_span_singleton_D22 (K := K) m
  have hv : (Pi.single (Sum.inl (0 : Fin (m + 1))) (1 : K) :
      Fin (m + 1) ⊕ Fin (m + 1) → K) ≠ 0 := by
    intro h
    have h1 : (1 : K) = 0 := by
      simpa using congrFun h (Sum.inl (0 : Fin (m + 1)))
    exact one_ne_zero h1
  have hsingle : SymplecticHigher.flagStabilizer (m + 1) K ({1} : Set ℕ)
      = SymplecticFlag.stabilizer (m + 1) K (SymplecticFlag.flag (m + 1) K 1) := by
    apply le_antisymm
    · intro g hg
      rw [SymplecticHigher.mem_flagStabilizer] at hg
      exact hg 1 (by simp)
    · intro g hg
      rw [SymplecticHigher.mem_flagStabilizer]
      intro i hi
      rw [Set.mem_singleton_iff] at hi
      subst hi
      exact hg
  rw [hsingle, hflag]
  apply le_antisymm
  · intro γ hγ
    rw [mem_lineStab] at hγ
    rw [SymplecticFlag.mem_stabilizer]
    rw [mem_stabilizer_span_singleton_iff_D22 (K := K) (A :=
      ((γ : GL (Fin (m + 1) ⊕ Fin (m + 1)) K) :
        Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) K))
      (gl_mulVec_injective_D22 (K := K) (γ : GL (Fin (m + 1) ⊕ Fin (m + 1)) K))
      (v := Pi.single (Sum.inl (0 : Fin (m + 1))) (1 : K)) hv]
    exact hγ
  · intro γ hγ
    rw [SymplecticFlag.mem_stabilizer] at hγ
    rw [mem_lineStab]
    rw [mem_stabilizer_span_singleton_iff_D22 (K := K) (A :=
      ((γ : GL (Fin (m + 1) ⊕ Fin (m + 1)) K) :
        Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) K))
      (gl_mulVec_injective_D22 (K := K) (γ : GL (Fin (m + 1) ⊕ Fin (m + 1)) K))
      (v := Pi.single (Sum.inl (0 : Fin (m + 1))) (1 : K)) hv] at hγ
    exact hγ

private lemma spFlagLeviBlock_one_D22 (m : ℕ) {K : Type} [Field K]
    (hI : ∀ i ∈ ({1} : Set ℕ), i ≤ m + 1) :
    spFlagLeviBlock (K := K) hI 1 (1 : Fin (m + 1 + 1)) = ⊥ := by
  let j1 : Fin (m + 1 + 1) := ⟨1, by omega⟩
  have hj1 : (1 : Fin (m + 1 + 1)) = j1 := Fin.ext (by simp [j1])
  rw [hj1]
  have hj0 : (j1 : ℕ) ≠ 0 := by simp [j1]
  have hj : (j1 : ℕ) ∈ ({1} : Set ℕ) := by simp [j1]
  rw [spFlagLeviBlock_of_mem (K := K) hI hj0 hj]
  have hp : spFlagPrev ({1} : Set ℕ) (j1 : ℕ) = 0 := by
    rw [show (j1 : ℕ) = 1 from rfl]
    exact Nat.eq_zero_of_le_zero (spFlagPrev_le ({1} : Set ℕ) 1)
  rw [hp]
  refine le_antisymm ?_ bot_le
  rintro x ⟨A, rfl⟩
  haveI : Subsingleton (Matrix.SpecialLinearGroup (Fin 1) K) := inferInstance
  rw [Subsingleton.elim A 1]
  simp

private lemma spFlagLeviBlock_eq_bot_of_ne_zero_D22 (m : ℕ) {K : Type} [Field K]
    (hI : ∀ i ∈ ({1} : Set ℕ), i ≤ m + 1) {j : Fin (m + 1 + 1)} (hj : j ≠ 0) :
    spFlagLeviBlock (K := K) hI 1 j = ⊥ := by
  by_cases h1 : (j : ℕ) = 1
  · have hj_eq : j = 1 := Fin.ext h1
    rw [hj_eq]
    exact spFlagLeviBlock_one_D22 m hI
  · rw [spFlagLeviBlock_of_not_mem (K := K) hI (fun h0 => hj (Fin.ext h0))
      (fun hmem => h1 (Set.mem_singleton_iff.mp hmem))]

private lemma pi_spFlagLeviBlock_eq_map_mulSingle_D22 (m : ℕ) {K : Type} [Field K]
    (hI : ∀ i ∈ ({1} : Set ℕ), i ≤ m + 1) :
    Subgroup.pi Set.univ (spFlagLeviBlock (K := K) hI 1)
      = (spFlagLeviBlock (K := K) hI 1 0).map
        (MonoidHom.mulSingle (fun _ : Fin (m + 1 + 1) => StatedSp (m + 1) K) 0) := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.pi_le_iff]
    intro i
    by_cases hi : i = 0
    · subst hi
      exact le_rfl
    · rw [spFlagLeviBlock_eq_bot_of_ne_zero_D22 (K := K) m hI hi, Subgroup.map_bot]
      exact bot_le
  · rintro x ⟨y, hy, rfl⟩
    change Pi.mulSingle (0 : Fin (m + 1 + 1)) y ∈
      Subgroup.pi Set.univ (spFlagLeviBlock (K := K) hI 1)
    rw [Subgroup.mulSingle_mem_pi]
    intro _
    exact hy

private lemma monoidHom_mulSingle_injective_D22 {ι : Type} [DecidableEq ι] (G : Type)
    [MulOneClass G] (i : ι) :
    Function.Injective (MonoidHom.mulSingle (fun _ : ι => G) i) := by
  intro x y h
  have := congrFun h i
  simpa [MonoidHom.mulSingle_apply] using this

private noncomputable def pi_spFlagLeviBlock_equiv_D22 (m : ℕ) {K : Type} [Field K] [Finite K]
    [CharP K 2] (hK : 4 ≤ Nat.card K) (hm : 1 ≤ m) (hI : ∀ i ∈ ({1} : Set ℕ), i ≤ m + 1) :
    ↥(Subgroup.pi Set.univ (spFlagLeviBlock (K := K) hI 1)) ≃* StatedSp m K := by
  have hS_eq : Subgroup.pi Set.univ (spFlagLeviBlock (K := K) hI 1)
      = (spFlagLeviBlock (K := K) hI 1 0).map
        (MonoidHom.mulSingle (fun _ : Fin (m + 1 + 1) => StatedSp (m + 1) K) 0) :=
    pi_spFlagLeviBlock_eq_map_mulSingle_D22 (K := K) m hI
  have eS_sf : ↥(Subgroup.pi Set.univ (spFlagLeviBlock (K := K) hI 1))
      ≃* ↥(spFlagLeviBlock (K := K) hI 1 0) :=
    (MulEquiv.subgroupCongr hS_eq).trans
      ((spFlagLeviBlock (K := K) hI 1 0).equivMapOfInjective
        (MonoidHom.mulSingle (fun _ : Fin (m + 1 + 1) => StatedSp (m + 1) K) 0)
        (monoidHom_mulSingle_injective_D22 (G := StatedSp (m + 1) K)
          (i := (0 : Fin (m + 1 + 1))))).symm
  have e3 : ↥(spFlagLeviBlock (K := K) hI 1 0) ≃* commutator (StatedSp (m + 1 - 1) K) :=
    spFlagLeviBlockZeroEquiv (K := K) hI 1 (j := 0) rfl
  have hcomm_top : commutator (StatedSp (m + 1 - 1) K) = ⊤ :=
    (spFlag_isQuasisimple_Sp (K := K) (m := m + 1 - 1) (by omega) (Or.inl hK)).1
  have e4 : ↥(commutator (StatedSp (m + 1 - 1) K)) ≃* StatedSp (m + 1 - 1) K :=
    (MulEquiv.subgroupCongr hcomm_top).trans Subgroup.topEquiv
  have eE : StatedSp (m + 1 - 1) K ≃* StatedSp m K :=
    MulEquiv.cast (M := fun n : ℕ => ↥(StatedSp n K)) (Nat.add_sub_cancel m 1)
  exact (eS_sf.trans e3).trans (e4.trans eE)

theorem nonempty_bar2_hinf_lineStab_statedSp (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) (m : ℕ) (hm : 1 ≤ m) :
    Nonempty (Bar2 (Hinf (lineStab (StatedSp (m + 1) K) (Pi.single (Sum.inl 0) 1))) ≃*
      ↥(StatedSp m K)) := by
  rw [lineStab_statedSp_succ_eq_flagStabilizer_D22 (K := K) m]
  have hI : ∀ i ∈ ({1} : Set ℕ), i ≤ m + 1 := by
    intro i hi
    rw [Set.mem_singleton_iff] at hi
    subst hi
    omega
  have hI1 : ∀ i ∈ ({1} : Set ℕ), 1 ≤ i := by
    intro i hi
    rw [Set.mem_singleton_iff] at hi
    subst hi
    omega
  have htI : (1 : ℕ) ∈ ({1} : Set ℕ) := by simp
  have hmax : ∀ c ∈ ({1} : Set ℕ), c ≤ 1 := by
    intro c hc
    rw [Set.mem_singleton_iff] at hc
    subst hc
    omega
  let S : Subgroup (Fin (m + 1 + 1) → StatedSp (m + 1) K) :=
    Subgroup.pi Set.univ (spFlagLeviBlock (K := K) hI 1)
  have hSR : S ≤ (spFlagLeviHom (K := K) hI htI).range :=
    pi_le_range_spFlagLeviHom (K := K) hI htI hmax
  have hcomm : ⁅(spFlagLeviHom (K := K) hI htI).range,
      (spFlagLeviHom (K := K) hI htI).range⁆ ≤ S :=
    commutator_range_spFlagLeviHom_le (K := K) hI htI
  have eS : ↥S ≃* StatedSp m K := pi_spFlagLeviBlock_equiv_D22 (K := K) m hK hm hI
  haveI : Group.IsPerfect (StatedSp m K) :=
    Group.isPerfect_def.mpr (spFlag_isQuasisimple_Sp (K := K) (m := m) hm (Or.inl hK)).1
  haveI : Group.IsPerfect ↥S :=
    Group.IsPerfect.ofSurjective (f := eS.symm.toMonoidHom) eS.symm.surjective
  have hSperf : ⁅S, S⁆ = S := Subgroup.commutator_eq_self (H := S)
  have hSO2 : CFSG.pCore 2 ↥S = ⊥ := by
    have hmap : (CFSG.pCore 2 ↥S).map eS.toMonoidHom = ⊥ := by
      rw [CFSG.pCore_map_iso 2 eS]
      exact CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat.pCore_statedSp_eq_bot 2 m
    exact (Subgroup.map_eq_bot_iff_of_injective (H := CFSG.pCore 2 ↥S)
      (f := eS.toMonoidHom) eS.injective).mp hmap
  obtain ⟨e⟩ := nonempty_bar2_hinf_equiv_of_leviHom
    (P := SymplecticHigher.flagStabilizer (m + 1) K ({1} : Set ℕ))
    (β := spFlagLeviHom (K := K) hI htI)
    (hker := isPGroup_ker_spFlagLeviHom (K := K) hI htI hI1)
    (S := S) (hSR := hSR) (hcomm := hcomm) (hperf := hSperf) (hO2 := hSO2)
  exact ⟨e.trans eS⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD
