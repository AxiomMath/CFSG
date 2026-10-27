module

import CFSG.LocalAnalysis.UniquenessCase.UC22P22wg
import CFSG.LocalAnalysis.UniquenessCase.UC22P22d
import CFSG.LocalAnalysis.UniquenessCase.UC22P22yg
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rk
import CFSG.LocalAnalysis.ComponentInitial.SteinbergBISp6EvenSymplecticCore
public import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge4
public import CFSG.LocalAnalysis.UniquenessCase.UC22S22c
import CFSG.CGT.PushingUpLit.Transport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

variable {G : Type} [Group G] [Finite G]

theorem uc22p22we_isL3_of_statedSL {X : Type} [Group X] (φ : X ≃* ↥(CFSG.Open.StatedSL 3 (ZMod 2))) : IsL3 X 1 :=
  CFSG.LocalAnalysis.ComponentInitial.SteinbergBI.lieModel_PSL_three_two_of_mulEquiv
    (φ.trans ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 (ZMod 2)).symm.trans
      (MulEquiv.ofBijective _ CFSG.LocalAnalysis.ComponentInitial.bijective_toGL_three_zmod_two)))

theorem uc22p22we_factorShape_of_shape148 {X : Type} [Group X] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) X V} {H : Subgroup X} {U C : Submodule (ZMod 2) V} (h : Shape148 ρ H U C) :
    FactorShape22 ↥H := by
  rcases h with ⟨n, -, F, _, _, hF, -, -, -, φ, -⟩ | ⟨-, -, -, φ, -⟩ | ⟨Ai, hAi, -⟩ | ⟨-, -, -, φ, -⟩
  · exact Or.inl ⟨n, F, inferInstance, inferInstance, hF, ⟨φ⟩⟩
  · exact Or.inr (Or.inl (uc22p22we_isL3_of_statedSL φ))
  · obtain ⟨-, -, -, φ, -⟩ := (hAi 0).2.2
    exact Or.inr (Or.inl (uc22p22we_isL3_of_statedSL φ))
  · exact Or.inr (Or.inr ⟨φ⟩)

namespace P22w

theorem exists_le_factor {X : Type} [Group X] [Finite X] {H : Subgroup X} {m : ℕ} {Hs : Fin m → Subgroup X}
    (hd : IsInternalDirect H Hs) {L : Subgroup X} (hq : CFSG.Open.IsQuasisimple ↥L)
    (hsub : CFSG.Open.IsSubnormal L H) : ∃ i, L ≤ Hs i := by
  have hLH : L ≤ H := hsub.le
  set L' : Subgroup ↥H := L.subgroupOf H with hL'
  have hL'c : CFSG.Open.IsComponentOf L' ⊤ :=
    ⟨le_top, CFSG.Open.IsSubnormal.of_mathlib ((CFSG.Open.IsSubnormal.iff_subgroupOf hLH).1 hsub),
      CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLH) hq⟩
  by_contra hall
  push Not at hall
  have hcomm : ∀ i, (Hs i).subgroupOf H ≤ centralizer (L' : Set ↥H) := by
    intro i
    haveI : ((Hs i).subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (le_of_isInternalDirect hd i)).2
        (le_normalizer_of_isInternalDirect hd i)
    rcases CFSG.ComponentClassification.LocalComponents.normal_contains_or_commutes L' ((Hs i).subgroupOf H)
        hL'c with hle | hc
    · exfalso
      refine hall i fun x hx => ?_
      have : (⟨x, hLH hx⟩ : ↥H) ∈ (Hs i).subgroupOf H := hle hx
      exact this
    · rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact hc
  have htop : (⊤ : Subgroup ↥H) ≤ centralizer (L' : Set ↥H) := by
    have h1 : (⨆ i, (Hs i).subgroupOf H) = ⊤ := by
      rw [← uc22br4_subgroupOf_iSup H Hs (le_of_isInternalDirect hd), hd.1, Subgroup.subgroupOf_self]
    rw [← h1]
    exact iSup_le hcomm
  have hcen : L' ≤ Subgroup.center ↥H := by
    intro k hk
    rw [Subgroup.mem_center_iff]
    intro g
    exact ((Subgroup.mem_centralizer_iff.1 (htop (Subgroup.mem_top g))) k hk).symm
  haveI : Group.IsPerfect ↥L' := ⟨hL'c.2.2.1⟩
  haveI : Nontrivial ↥L' := CFSG.ComponentClassification.Quasisimple.nontrivial hL'c.2.2
  exact (Subgroup.nontrivial_iff_ne_bot L').1 inferInstance
    (CFSG.ComponentClassification.Quasisimple.perfect_le_center_eq_bot L' hcen)

theorem eq_alternating_of_isComponentOf {L : Subgroup (Equiv.Perm (Fin 5))} (hL : CFSG.Open.IsComponentOf L ⊤) :
    L = alternatingGroup (Fin 5) := by
  have hLA : L ≤ alternatingGroup (Fin 5) := by
    have hperf : ⁅L, L⁆ = L := by
      have h1 : (_root_.commutator ↥L).map L.subtype = (⊤ : Subgroup ↥L).map L.subtype := by
        rw [hL.2.2.1]
      rwa [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype] at h1
    rw [← hperf]
    refine le_trans (Subgroup.commutator_mono le_top le_top) ?_
    rw [← _root_.commutator_def]
    exact Abelianization.commutator_subset_ker Equiv.Perm.sign
  have hsub : CFSG.Open.IsSubnormal L (alternatingGroup (Fin 5)) := by
    have h1 := CFSG.Open.IsSubnormal.inf_of_le hL.2.1 (le_top : alternatingGroup (Fin 5) ≤ ⊤)
    rwa [inf_eq_left.2 hLA] at h1
  rcases CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hsub alternatingGroup.isSimpleGroup_five with h0 | h0
  · exfalso
    haveI : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial hL.2.2
    exact (Subgroup.nontrivial_iff_ne_bot L).1 inferInstance h0
  · exact h0

end P22w

theorem uc22p22we_compShape_of_factor {X : Type} [Group X] [Finite X]
    (hX : FactorShape22 X) {L : Subgroup X} (hL : CFSG.Open.IsComponentOf L ⊤) :
    (∃ n : ℕ, IsL2 ↥L n) ∨ IsL2Odd ↥L 7 := by
  have hq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hne : L ≠ ⊥ := by
    intro h0
    haveI : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial hq
    exact (Subgroup.nontrivial_iff_ne_bot L).1 inferInstance h0
  have htopEq : IsSimpleGroup X → L = ⊤ := fun hs => by
    haveI := hs
    exact (CFSG.Open.IsSubnormal.eq_bot_or_top hL.2.1).resolve_left hne
  rcases hX with ⟨n, hn⟩ | hn | hS5
  · obtain ⟨F, _, _, hF, ⟨φ⟩⟩ := hn
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · exfalso
      have hn1 : n = 1 := by
        have := P22y.one_le_of_card hF
        omega
      subst hn1
      haveI : Group.IsSolvable X := by
        refine CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
        rw [P22y.card_of_isL2Ev_one ⟨F, inferInstance, inferInstance, hF, ⟨φ⟩⟩,
          show (6 : ℕ) = 2 * 3 from rfl, Nat.primeFactors_mul (by norm_num) (by norm_num),
          Nat.Prime.primeFactors Nat.prime_two, Nat.Prime.primeFactors Nat.prime_three]
        decide
      haveI : Group.IsSolvable ↥L := Group.isSolvable_of_isSolvable_injective (Subgroup.subtype_injective L)
      haveI : Group.IsPerfect ↥L := ⟨hq.1⟩
      haveI : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial hq
      exact Group.IsPerfect.not_isSolvable (↥L) inferInstance
    · have htop := htopEq (P22y.isSimpleGroup_of_isL2Ev ⟨F, inferInstance, inferInstance, hF, ⟨φ⟩⟩ hn2)
      exact Or.inl ⟨n, uc22p22d_isL2_of_statedSL hn2 hF
        (((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).trans φ)⟩
  · have htop := htopEq (uc22p22r_lieModel_isSimple_classical (Or.inl rfl) hn)
    exact Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).symm
      (CFSG.LocalAnalysis.ComponentInitial.PSL3_two_PSL2_seven_paired_isomorphism X hn))
  ·
    obtain ⟨φ⟩ := hS5
    set L₂ : Subgroup (Equiv.Perm (Fin 5)) := L.map φ.toMonoidHom with hL₂
    have hL₂c : CFSG.Open.IsComponentOf L₂ ⊤ := by
      refine ⟨le_top, ?_, CFSG.Open.IsQuasisimple.of_mulEquiv
        (L.equivMapOfInjective φ.toMonoidHom φ.injective).symm hq⟩
      have h1 := CFSG.Open.IsSubnormal.map φ.toMonoidHom hL.2.1
      rwa [Subgroup.map_top_of_surjective _ φ.surjective] at h1
    have hA := P22w.eq_alternating_of_isComponentOf hL₂c
    set K := GaloisField 2 2
    have hK : Nat.card K = 2 ^ 2 := GaloisField.card 2 2 (by norm_num)
    obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five K
      (Or.inl (by rw [hK]; norm_num))
    have hZ := CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSL_two_eq_bot (K := K)
    let g : CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 K) ≃* ↥(CFSG.Open.StatedSL 2 K) :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    refine Or.inl ⟨2, uc22p22d_isL2_of_statedSL le_rfl hK ?_⟩
    exact (((L.equivMapOfInjective φ.toMonoidHom φ.injective).trans (MulEquiv.subgroupCongr hA)).trans
      e5.symm).trans g

end CFSG.LocalAnalysis.UniquenessCase.UC22
