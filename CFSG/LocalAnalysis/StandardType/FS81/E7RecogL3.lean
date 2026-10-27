module

public import CFSG.LocalAnalysis.StandardType.FS81.E7RecogPieces
public import CFSG.HardMathSupport.C14IdxA2Hom
public import CFSG.ClassicalInvolution.ModelFacts.E7ModelWeyl
public import CFSG.CGT.T75N.L29KL
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf12L3E8

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.C14Idx CFSG.LieType.Chevalley
  CFSG.SeitzReduction
open scoped MatrixGroups

local instance e7RecogL3NeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

private abbrev l3Alpha : Fin (Tag.rank .E7) → ℤ := ![1, 2, 3, 4, 3, 2, 1]

private abbrev l3Beta : Fin (Tag.rank .E7) → ℤ := Pi.single 0 1

private abbrev d6Alpha : Fin (Tag.rank .E7) → ℤ := ![0, 1, 1, 2, 2, 1, 1]

private abbrev d6Beta : Fin (Tag.rank .E7) → ℤ := Pi.single 5 1

private lemma oddDerivPairB_l3 : oddDerivPairB .E7 l3Alpha l3Beta = true := by decide +kernel

private lemma oddDerivPair_l3 :
    OddDerivPair .E7 l3Alpha l3Beta :=
  (oddDerivPairB_iff (τ := .E7) (a := l3Alpha) (b := l3Beta)).1 oddDerivPairB_l3

private lemma oddDerivPairB_d6 : oddDerivPairB .E7 d6Alpha d6Beta = true := by decide +kernel

private lemma oddDerivPair_d6 :
    OddDerivPair .E7 d6Alpha d6Beta :=
  (oddDerivPairB_iff (τ := .E7) (a := d6Alpha) (b := d6Beta)).1 oddDerivPairB_d6

private lemma l3Alpha_add_l3Beta : l3Alpha + l3Beta = highRoot .E7 := by decide +kernel

private lemma d6Alpha_add_d6Beta : d6Alpha + d6Beta = E7Pilot.d6HighRoot := by decide +kernel

private lemma thetaE7_eq_highRoot :
    (CFSG.ClassicalInvolution.ModelFacts.Levi.thetaE7 : Fin (Tag.rank .E7) → ℤ) =
      highRoot .E7 := by
  rw [CFSG.ClassicalInvolution.ModelFacts.E7Model.thetaE7_eq]
  rfl

private lemma a2PairRoot_zero_two (α β : Fin (Tag.rank .E7) → ℤ) :
    a2PairRoot α β 0 2 = α + β := by
  simp [a2PairRoot]

private lemma a2PairRoot_two_zero (α β : Fin (Tag.rank .E7) → ℤ) :
    a2PairRoot α β 2 0 = -(α + β) := by
  simp [a2PairRoot]

private lemma isRootB_a2PairRoot_l3 :
    ∀ (i j : Fin 3), i ≠ j → RootOps.isRootB .E7 (a2PairRoot l3Alpha l3Beta i j) = true := by
  decide +kernel

private lemma isRoot_a2PairRoot_l3
    {i j : Fin 3} (hij : i ≠ j) :
    IsRoot .E7 (a2PairRoot l3Alpha l3Beta i j) :=
  RootOps.isRootB_iff.1 (isRootB_a2PairRoot_l3 i j hij)

private lemma isRootB_a2PairRoot_d6 :
    ∀ (i j : Fin 3), i ≠ j → RootOps.isRootB .E7 (a2PairRoot d6Alpha d6Beta i j) = true := by
  decide +kernel

private lemma isRoot_a2PairRoot_d6
    {i j : Fin 3} (hij : i ≠ j) :
    IsRoot .E7 (a2PairRoot d6Alpha d6Beta i j) :=
  RootOps.isRootB_iff.1 (isRootB_a2PairRoot_d6 i j hij)

private lemma a2PairRoot_d6_coeff :
    ∀ i j : Fin 3, a2PairRoot d6Alpha d6Beta i j (highNode .E7) = 0 := by
  decide +kernel

private lemma mem_perpRoots_a2PairRoot_d6
    {i j : Fin 3} (hij : i ≠ j) :
    a2PairRoot d6Alpha d6Beta i j ∈ EPilot.perpRoots .E7 :=
  EPilot.mem_perpRoots_iff.2 ⟨isRoot_a2PairRoot_d6 hij, a2PairRoot_d6_coeff i j⟩

private lemma injective_of_transvection_eq_pinnedX
    {ρ : SL(3, ZMod 2) →* ModGL .E7 (ZMod 2)}
    {i j : Fin 3} (hij : i ≠ j) {γ : Fin (Tag.rank .E7) → ℤ} {c : ZMod 2} (hc : c ≠ 0)
    (hγ : ρ (Matrix.SpecialLinearGroup.transvection hij c) = pinnedX .E7 (ZMod 2) γ c) :
    Function.Injective ρ := by
  haveI : IsSimpleGroup (SL(3, ZMod 2)) :=
    CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.isSimpleGroup_l3Two
  refine ρ.ker_eq_bot_iff.1 ?_
  rcases Subgroup.Normal.eq_bot_or_eq_top ρ.ker with hbot | htop
  · exact hbot
  · exfalso
    have h1 : Matrix.SpecialLinearGroup.transvection hij c ∈ ρ.ker := by
      rw [htop]
      exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker, hγ] at h1
    have h0 : pinnedX .E7 (ZMod 2) γ c = pinnedX .E7 (ZMod 2) γ 0 := by rw [h1, pinnedX_zero]
    exact hc (pinnedX_injective .E7 (ZMod 2) γ h0)

theorem exists_sl3_of_oddDerivPair
    {α β : Fin (Tag.rank .E7) → ℤ} (h : OddDerivPair .E7 α β)
    (S : Set (Fin (Tag.rank .E7) → ℤ))
    (hS : ∀ (i j : Fin 3), i ≠ j → a2PairRoot α β i j ∈ S) :
    ∃ P : Subgroup (ModGL .E7 (ZMod 2)),
      P ≤ rootSpan .E7 (ZMod 2) S ∧
        rootSubgroup .E7 (ZMod 2) (α + β) ⊔ rootSubgroup .E7 (ZMod 2) (-(α + β)) ≤ P ∧
        Nonempty (↥P ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  obtain ⟨ρ, hρ⟩ := exists_a2Hom_of_oddDerivPair (τ := .E7) (L := ZMod 2) (K := ZMod 2)
    (RingHom.id (ZMod 2)) h
  have hcomap : (rootSpan .E7 (ZMod 2) S).comap ρ = ⊤ := by
    refine CFSG.CGT.T75N.eq_top_of_transvections_gen _ ?_
    intro i j hij c
    rw [Subgroup.mem_comap, hρ i j hij c]
    exact pinnedX_mem_rootSpan (hS i j hij) c
  have hle : ρ.range ≤ rootSpan .E7 (ZMod 2) S := by
    rw [MonoidHom.range_eq_map]
    exact Subgroup.map_le_iff_le_comap.2 (le_of_eq hcomap.symm)
  have htwo : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide +kernel
  have hroot : ∀ γ : Fin (Tag.rank .E7) → ℤ, pinnedX .E7 (ZMod 2) γ 1 ∈ ρ.range →
      rootSubgroup .E7 (ZMod 2) γ ≤ ρ.range := by
    intro γ hγ
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    rcases htwo c with rfl | rfl
    · rw [pinnedX_zero]
      exact Subgroup.one_mem _
    · exact hγ
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have hX : pinnedX .E7 (ZMod 2) (α + β) 1 ∈ ρ.range :=
    ⟨Matrix.SpecialLinearGroup.transvection h02 1, by
      rw [hρ 0 2 h02 1, a2PairRoot_zero_two]
      simp⟩
  have hXn : pinnedX .E7 (ZMod 2) (-(α + β)) 1 ∈ ρ.range :=
    ⟨Matrix.SpecialLinearGroup.transvection h20 1, by
      rw [hρ 2 0 h20 1, a2PairRoot_two_zero]
      simp⟩
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have hX0 : ρ (Matrix.SpecialLinearGroup.transvection h01 (1 : ZMod 2)) =
      pinnedX .E7 (ZMod 2) (a2PairRoot α β 0 1) 1 := by
    rw [hρ 0 1 h01 1]
    simp
  exact ⟨ρ.range, hle, sup_le (hroot _ hX) (hroot _ hXn),
    ⟨(MonoidHom.ofInjective (injective_of_transvection_eq_pinnedX h01 one_ne_zero hX0)).symm⟩⟩

theorem e7ModelL3_holds :
    E7ModelL3 := by
  obtain ⟨P₁, hP₁le, hP₁J, hP₁iso⟩ := exists_sl3_of_oddDerivPair (S := {γ | IsRoot .E7 γ})
    oddDerivPair_l3 (fun i j hij => isRoot_a2PairRoot_l3 hij)
  obtain ⟨P₂, hP₂le, hP₂J, hP₂iso⟩ := exists_sl3_of_oddDerivPair (S := EPilot.perpRoots .E7)
    oddDerivPair_d6 (fun i j hij => mem_perpRoots_a2PairRoot_d6 hij)
  have hP₁AG : P₁ ≤ adjointGroup .E7 (ZMod 2) :=
    hP₁le.trans (iSup₂_le fun γ _ => rootSubgroup_le_adjointGroup γ)
  have hP₂AG : P₂ ≤ adjointGroup .E7 (ZMod 2) :=
    hP₂le.trans (iSup₂_le fun γ _ => rootSubgroup_le_adjointGroup γ)
  refine ⟨⟨P₁.subgroupOf (adjointGroup .E7 (ZMod 2)), ?_, ?_⟩,
    ⟨P₂.subgroupOf (adjointGroup .E7 (ZMod 2)), ?_, ?_, ?_⟩⟩
  · refine Subgroup.subgroupOf_mono _ ?_
    change rootSubgroup .E7 (ZMod 2) (highRoot .E7) ⊔
      rootSubgroup .E7 (ZMod 2) (-highRoot .E7) ≤ P₁
    rw [← l3Alpha_add_l3Beta]
    exact hP₁J
  · exact ⟨(Subgroup.subgroupOfEquivOfLe hP₁AG).trans hP₁iso.some⟩
  · refine Subgroup.subgroupOf_mono _ ?_
    rw [← d6Alpha_add_d6Beta]
    exact hP₂J
  · exact Subgroup.subgroupOf_mono _ hP₂le
  · exact ⟨(Subgroup.subgroupOfEquivOfLe hP₂AG).trans hP₂iso.some⟩

private lemma exists_conj_d6HighRoot :
    ∃ n ∈ adjointGroup .E7 (ZMod 2),
      (rootSubgroup .E7 (ZMod 2) E7Pilot.d6HighRoot ⊔
          rootSubgroup .E7 (ZMod 2) (-E7Pilot.d6HighRoot)).map
          (MulAut.conj n).toMonoidHom =
        rootSubgroup .E7 (ZMod 2) (highRoot .E7) ⊔
          rootSubgroup .E7 (ZMod 2) (-highRoot .E7) := by
  obtain ⟨n, hn, hmap⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.E7Model.exists_conj_rankOne_to_theta (F := ZMod 2)
      (β := E7Pilot.d6HighRoot) E7Pilot.isRoot_d6HighRoot
  have hA : rootRankOneGroup .E7 (ZMod 2) E7Pilot.d6HighRoot =
      rootSubgroup .E7 (ZMod 2) E7Pilot.d6HighRoot ⊔
        rootSubgroup .E7 (ZMod 2) (-E7Pilot.d6HighRoot) :=
    CFSG.ClassicalInvolution.ModelFacts.rootRankOneGroup_eq_sup E7Pilot.isRoot_d6HighRoot
  have hB : rootRankOneGroup .E7 (ZMod 2)
        (CFSG.ClassicalInvolution.ModelFacts.Levi.thetaE7) =
      rootSubgroup .E7 (ZMod 2) (highRoot .E7) ⊔
        rootSubgroup .E7 (ZMod 2) (-highRoot .E7) := by
    rw [CFSG.ClassicalInvolution.ModelFacts.rootRankOneGroup_eq_sup
      CFSG.ClassicalInvolution.ModelFacts.Levi.isRoot_thetaE7, thetaE7_eq_highRoot]
  exact ⟨n, hn, by rw [← hA, ← hB]; exact hmap⟩

private lemma map_conj_inv_eq_of_map_conj_eq
    {A B : Subgroup (ModGL .E7 (ZMod 2))} {n : ModGL .E7 (ZMod 2)}
    (h : A.map (MulAut.conj n).toMonoidHom = B) :
    B.map (MulAut.conj n⁻¹).toMonoidHom = A := by
  have hinv : (MulAut.conj n⁻¹ : MulAut (ModGL .E7 (ZMod 2))) = (MulAut.conj n).symm := by
    rw [map_inv (MulAut.conj (G := ModGL .E7 (ZMod 2))) n, MulAut.inv_def]
  rw [hinv]
  exact (Subgroup.map_symm_eq_iff_map_eq (K := A) (H := B) (e := MulAut.conj n)).2 h

private lemma exists_conj_highRootSL2 :
    ∃ g : ↥(adjointGroup .E7 (ZMod 2)),
      ((rootSubgroup .E7 (ZMod 2) (highRoot .E7) ⊔
          rootSubgroup .E7 (ZMod 2) (-highRoot .E7)).subgroupOf
            (adjointGroup .E7 (ZMod 2))).map (MulAut.conj g).toMonoidHom =
        (rootSubgroup .E7 (ZMod 2) E7Pilot.d6HighRoot ⊔
          rootSubgroup .E7 (ZMod 2) (-E7Pilot.d6HighRoot)).subgroupOf
            (adjointGroup .E7 (ZMod 2)) := by
  obtain ⟨n, hn, hmap⟩ := exists_conj_d6HighRoot
  have hBA := map_conj_inv_eq_of_map_conj_eq hmap
  refine ⟨⟨n⁻¹, inv_mem hn⟩, ?_⟩
  have hstep := CFSG.SeitzReduction.UnitaryPilot.map_conj_subgroupOf
    (H := rootSubgroup .E7 (ZMod 2) (highRoot .E7) ⊔
      rootSubgroup .E7 (ZMod 2) (-highRoot .E7))
    (S := adjointGroup .E7 (ZMod 2)) ⟨n⁻¹, inv_mem hn⟩
  rw [hstep]
  have hcoe : ((⟨n⁻¹, inv_mem hn⟩ : ↥(adjointGroup .E7 (ZMod 2))) : ModGL .E7 (ZMod 2)) = n⁻¹ :=
    rfl
  rw [hcoe, hBA]

theorem e7ModelConj_holds :
    E7ModelConj :=
  exists_conj_highRootSL2

end CFSG.StandardType.FrameRoute.FS81
