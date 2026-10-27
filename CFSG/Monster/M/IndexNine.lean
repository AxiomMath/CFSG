module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicPermutesPackage
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoSetupSylow
public import CFSG.Monster.VisQuot.SylowT
public import CFSG.RankThree.PartOne.SPOR.OuterM
public import CFSG.YGroups.Y443.Tri.Finiteness

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.M

open CFSG.Monster.Generated (Gmat)
open CFSG.Monster.Existence (xGmat cent centGmatEquiv)
open CFSG.Monster.Griess (SpaceB)
open CFSG.Monster.Visible (Gvis)
open CFSG.Monster.VisQuot (Tmat Tvis mem_toMat toMat_le_centralizer rhoQvis_le_Tvis xGmat_mem_Tmat
  isSylowTwoOf_Tmat)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

theorem xGmat_ne_one : xGmat ≠ 1 := by
  intro h
  have h1 : CFSG.Monster.Generated.xmat = (1 : SpaceB ≃ₗ[ℚ] SpaceB) := congrArg Subtype.val h
  rw [CFSG.Monster.Generated.xmat_eq_xB] at h1
  exact CFSG.Monster.Griess.one_ne_xB h1.symm

theorem mem_Tmat_and_commute_iff (t : Gmat) :
    (t ∈ Tmat ∧ ∀ y ∈ Tmat, t * y = y * t) ↔ t = 1 ∨ t = xGmat := by
  constructor
  · rintro ⟨-, hcomm⟩
    have hmem : (t : SpaceB ≃ₗ[ℚ] SpaceB) ∈
        Gmat ⊓ Subgroup.centralizer (CFSG.Monster.Generated.Qmat :
          Set (SpaceB ≃ₗ[ℚ] SpaceB)) := by
      refine ⟨t.2, Subgroup.mem_centralizer_iff.2 ?_⟩
      intro q hq
      have hqG : q ∈ Gvis := CFSG.Monster.Generated.Qmat_le_Hmat hq
      have hqTvis : (⟨q, hqG⟩ : Gvis) ∈ Tvis :=
        rhoQvis_le_Tvis (Subgroup.mem_subgroupOf.2 hq)
      have hqT : (⟨q, CFSG.Monster.Generated.Hmat_le_Gmat hqG⟩ : Gmat) ∈ Tmat :=
        mem_toMat.2 ⟨⟨q, hqG⟩, hqTvis, rfl⟩
      exact (congrArg Subtype.val (hcomm _ hqT)).symm
    rw [CFSG.Monster.Existence.Gmat_inf_centralizer_Qmat] at hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hmod : CFSG.Monster.Generated.xmat ^ (k % 2) = CFSG.Monster.Generated.xmat ^ k := by
      have h := zpow_mod_orderOf CFSG.Monster.Generated.xmat k
      rwa [CFSG.Monster.Generated.orderOf_xmat] at h
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left
      have h1' : (t : SpaceB ≃ₗ[ℚ] SpaceB) = 1 := by
        rw [← hk, ← hmod, h0, zpow_zero]
      exact Subtype.ext h1'
    · right
      have h1' : (t : SpaceB ≃ₗ[ℚ] SpaceB) = CFSG.Monster.Generated.xmat := by
        rw [← hk, ← hmod, h1, zpow_one]
      exact Subtype.ext h1'
  · rintro (rfl | rfl)
    · exact ⟨Tmat.one_mem, fun y _ => by simp⟩
    · refine ⟨xGmat_mem_Tmat, fun y hy => ?_⟩
      exact (Subgroup.mem_centralizer_singleton_iff.1 (toMat_le_centralizer Tvis hy)).symm

theorem normalizer_Tmat_le_cent : Subgroup.normalizer (Tmat : Set Gmat) ≤ cent xGmat := by
  refine CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.normalizer_le_centralizer_of_center
    (R := Tmat) (z := xGmat) xGmat_mem_Tmat xGmat_ne_one ?_ ?_
  · intro y hy
    exact (Subgroup.mem_centralizer_singleton_iff.1 (toMat_le_centralizer Tvis hy)).symm
  · intro y hy hyc
    exact (mem_Tmat_and_commute_iff y).1 ⟨hy, hyc⟩

@[expose] noncomputable def centPhiH :
    ↥(cent xGmat) →* CFSG.Monster.VisCert.Hvis :=
  CFSG.Monster.Schur.PhiH.comp centGmatEquiv.toMonoidHom

theorem centPhiH_surjective :
    Function.Surjective centPhiH :=
  CFSG.Monster.Schur.PhiH_surjective.comp centGmatEquiv.surjective

theorem isPGroup_ker_centPhiH :
    IsPGroup 2 centPhiH.ker := by
  have hPhiH : CFSG.Monster.Schur.PhiH.ker = CFSG.Monster.Visible.rhoQvis := by
    simp only [CFSG.Monster.Schur.PhiH, MonoidHom.ker_codRestrict,
      CFSG.Monster.Schur.ker_PhiV]
  have hker : centPhiH.ker =
      CFSG.Monster.Visible.rhoQvis.comap centGmatEquiv.toMonoidHom := by
    rw [centPhiH, ← MonoidHom.comap_ker, hPhiH]
  rw [hker]
  exact (IsPGroup.of_card CFSG.Monster.Existence.natCard_rhoQvis).comap_of_injective
    centGmatEquiv.toMonoidHom centGmatEquiv.injective

theorem gmat_indexNinePackage_of_co1
    {Δ : Type*} [Group Δ] (eΔ : Δ ≃* CFSG.Blueprint.NativeSporadic.Co1)
    (hΔ : IndexNinePackage Δ) : IndexNinePackage Gmat := by
  classical
  let e' : Δ ≃* CFSG.Monster.VisCert.Hvis :=
    eΔ.trans CFSG.Monster.Existence.Co1Bridge.co1EquivHvis
  have : Finite Δ := Finite.of_equiv CFSG.Monster.VisCert.Hvis e'.symm.toEquiv
  let π : ↥(cent xGmat) →* Δ := e'.symm.toMonoidHom.comp centPhiH
  have hπ : Function.Surjective π := e'.symm.surjective.comp centPhiH_surjective
  have hker : IsPGroup 2 π.ker := by
    rw [show π.ker = centPhiH.ker from
      MonoidHom.ker_comp_of_injective centPhiH e'.symm.toMonoidHom e'.symm.injective]
    exact isPGroup_ker_centPhiH
  have hAut : ∀ α : MulAut Gmat, ∃ g : Gmat, ∀ x : Gmat, α x = g * x * g⁻¹ := by
    intro α
    obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.SPOR.allInner_Gmat α
    exact ⟨g, fun x => by rw [hg, MulAut.conj_apply]⟩
  have hU : CFSG.QuasithinUnique.IsSylowTwoOf Tmat ⊤ :=
    isSylowTwoOf_Tmat CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder
  exact indexNinePackage_of_quotient hAut hU normalizer_Tmat_le_cent π hπ hker hΔ.inner

end CFSG.Monster.M
