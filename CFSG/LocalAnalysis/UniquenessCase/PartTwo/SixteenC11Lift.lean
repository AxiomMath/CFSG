module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven11Red
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Fb43ThreeA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81 CFSG.LocalAnalysis.RankThreeUC.SourceSetting
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c11_normalizer_le_of_bar_noncyclic (D : Data G) (h61 : UC6.R6_1 D)
    {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) (h : Hyp125 D V₀ V) {p : ℕ} (hp : p ∈ D.sig)
    {P : Subgroup (MulAut (Vtil V₀ V hV))} (hPM : P ≤ Mbar D.M V₀ V hV) (hPp : IsPGroup p ↥P)
    (hPc : ¬ IsCyclic ↥P)
    (hPW : P ≤ normalizer ((barSub V₀ V hV (E3.wClos V 0 D.T) : Subgroup _) : Set _)) :
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hprime : p.Prime := (D.sig_prime p hp).1
  haveI : Fact p.Prime := ⟨hprime⟩
  have hP : PairFacts D.M V₀ V := h.pairFacts
  have hM : D.M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  have hT : IsSylowIn 2 D.T D.M :=
    (CFSG.ABGLocalTools.isSylowOf_iff (p := 2)).1 D.sylowM
  let W₀ : Subgroup G := E3.wClos V 0 D.T
  let Wbar : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV W₀
  let R : Subgroup G := D.T ⊓ preBarSub D.M V₀ V hV Wbar
  let N₁ : Subgroup G := D.M ⊓ normalizer (R : Set G)
  have hW0T : W₀ ≤ D.T := wClos_zero_le V D.T
  have hW0M : W₀ ≤ D.M := hW0T.trans D.sylowM.le
  have hW0S : W₀ ≤ stabTil V₀ V := hW0T.trans (D.sylowM.le.trans hM)
  have hW0R : W₀ ≤ R := le_inf hW0T (le_preBarSub_barSub hV hW0M hW0S)
  have hWbar_le : Wbar ≤ barSub V₀ V hV D.T := barSub_mono V₀ V hV hW0T
  have hN₁s : N₁ ≤ stabTil V₀ V := inf_le_left.trans hM
  let f : ↥N₁ →* MulAut (Vtil V₀ V hV) := (actTil V₀ V hV).comp (Subgroup.inclusion hN₁s)
  have hPle : P ≤ f.range := by
    intro φ hφ
    obtain ⟨m, hm, hmM, hmN, hmφ⟩ :=
      s16c1_normalizer_lift hM hT hWbar_le (hPM hφ) (hPW hφ)
    refine ⟨⟨m, hmM, hmN⟩, ?_⟩
    show actTil V₀ V hV ⟨m, hN₁s ⟨hmM, hmN⟩⟩ = φ
    rw [show (⟨m, hN₁s ⟨hmM, hmN⟩⟩ : ↥(stabTil V₀ V)) = ⟨m, hm⟩ from Subtype.ext rfl,
      hmφ]
  obtain ⟨P', hP'p, hP'map⟩ := exists_pGroup_map_eq f P hPp hPle
  have hXM : P'.map N₁.subtype ≤ D.M := (Subgroup.map_subtype_le P').trans inf_le_left
  have hXp : IsPGroup p (P'.map N₁.subtype) := hP'p.map N₁.subtype
  have hXc : ¬ IsCyclic ↥(P'.map N₁.subtype) := by
    intro hcyc
    haveI : IsCyclic ↥(P'.map N₁.subtype) := hcyc
    haveI : IsCyclic ↥P' :=
      isCyclic_of_surjective
        (Subgroup.equivMapOfInjective P' N₁.subtype N₁.subtype_injective).symm
        (Subgroup.equivMapOfInjective P' N₁.subtype N₁.subtype_injective).symm.surjective
    haveI : IsCyclic ↥(P'.map f) :=
      isCyclic_of_surjective (f.subgroupMap P') (f.subgroupMap_surjective P')
    rw [hP'map] at this
    exact hPc this
  have hXW : P'.map N₁.subtype ≤ normalizer (E3.wClos V 0 D.T : Set G) := by
    have hWR : E3.wClos V 0 D.T = E3.wClos V 0 R :=
      E3.e3_15 hT (inf_le_left.trans D.sylowM.le)
        (IsPGroup.to_le D.sylowM.isPGroup inf_le_left) hW0R
    calc P'.map N₁.subtype ≤ normalizer (R : Set G) :=
          (Subgroup.map_subtype_le P').trans inf_le_right
      _ ≤ normalizer (E3.wClos V 0 R : Set G) := E3.normalizer_le_normalizer_wClos R
      _ = normalizer (E3.wClos V 0 D.T : Set G) := by rw [hWR]
  exact s16c1611_normalizer_le_of_noncyclic D h61 hV h hp hXM hXp hXc hXW

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
