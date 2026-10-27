module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512Gen
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch513
public import CFSG.RankThree.PartTwo.KFacts.KS14Sz
public import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)

theorem isCalL1_of_suzukiModel {X : Type} [Group X] {f : ℕ}
    (h : CFSG.Blueprint.SuzukiModel X 2 f) : IsCalL1 X := by
  have hf : ∃ a : ℕ, 1 ≤ a ∧ f = 2 * a + 1 := by
    obtain ⟨-, a, ha, -, -, -, hf, -⟩ := h
    exact ⟨a, ha, hf⟩
  obtain ⟨a, ha, hfa⟩ := hf
  refine ⟨f, ⟨a, by omega⟩, by omega, Or.inr (Or.inl ?_)⟩
  exact CFSG.Blueprint.LieModel.twistedB2_iff.2 ⟨rfl, h⟩

variable {G : Type} [Group G] [Finite G]

section Solvable


theorem isSolvable_relPPrimeCore_three {H : Subgroup G} (hK : CFSG.Open.IsKGroup ↥H)
    (hno : ¬ HasCompFactor H IsCalL1) : Group.IsSolvable ↥(relPPrimeCore 3 H) := by
  set R := relPPrimeCore 3 H with hRdef
  have hRH : R ≤ H := relPPrimeCore_le_ambient 3 H
  haveI hRn : (R.subgroupOf H).Normal := normal_subgroupOf_relPPrimeCore 3 H
  have hcop : Nat.Coprime 3 (Nat.card R) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.coprime_card_relPPrimeCore
      Nat.prime_three H
  refine isSolvable_of_forall_isCompositionFactor_comm _ le_rfl ?_
  intro L _ hL a b
  by_contra hab
  haveI : Finite L := isCompositionFactor_finite hL
  have e : ↥(R.subgroupOf H) ≃* ↥R := Subgroup.subgroupOfEquivOfLe hRH
  have hL' : E1.IsCompositionFactor ↥(R.subgroupOf H) L :=
    (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr e).2 hL
  have hLH : E1.IsCompositionFactor ↥H L :=
    kbr_isCompositionFactor_of_normal_subgroup (R.subgroupOf H) hL'
  have hnab : ∃ x y : L, x * y ≠ y * x := ⟨a, b, hab⟩
  obtain ⟨N, M, hNM, hle, hNs, hMs, hs, ⟨eL⟩⟩ := hLH
  haveI := hs
  haveI : IsSimpleGroup L := eL.symm.isSimpleGroup
  have hnabM : ∃ x y : ↥M ⧸ N.subgroupOf M, x * y ≠ y * x :=
    CFSG.KCore.nonabelian_of_mulEquiv eL hnab
  obtain ⟨i, ⟨ei⟩⟩ := hK M N hle hs hnabM
  have hcat : CFSG.Assembly.InCatalog L := ⟨i, ⟨eL.symm.trans ei⟩⟩
  have h3 : ¬ 3 ∣ Nat.card L := fun h3 =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop (h3.trans (isCompositionFactor_natCard_dvd hL))
  obtain ⟨f, hf⟩ :=
    CFSG.RankThree.PartTwo.KFacts.KS14.suzukiModel_of_inCatalog_of_not_three_dvd L hnab hcat h3
  exact hno ⟨L, inferInstance, ⟨N, M, hNM, hle, hNs, hMs, hs, ⟨eL⟩⟩,
    isCalL1_of_suzukiModel hf⟩

end Solvable

end CFSG.LocalAnalysis.WeakClosure81

end
