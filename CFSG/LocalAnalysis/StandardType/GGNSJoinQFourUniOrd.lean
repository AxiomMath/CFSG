module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinQFourRows
public import CFSG.LocalAnalysis.StandardType.GGNSJoinByType
public import CFSG.LocalAnalysis.StandardType.GGMemberRowsDefs
public import CFSG.LocalAnalysis.StandardType.GGMemberUnitaryPos
import CFSG.LocalAnalysis.StandardType.GGMemberUnitaryRk1Aux
import CFSG.LocalAnalysis.StandardType.GGNSJoinRankOneOfRk1

public section

namespace CFSG.StandardType

namespace NSJoin

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open CFSG.LieType.Steinberg

open scoped MatrixGroups

theorem nsQFourRow_uniOrd {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hT : ∀ {ι : Type} {M : CoxeterMatrix ι}, T M → ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hRig : GGLabelRigidInput) :
    NSQFourRowOf T NSRowUniOrd := by
  intro G _ _ p B Bs x L D J 𝒦 hreg hrow
  obtain ⟨hcfg, hns, ι, M, e, hpres, hTM, hbig⟩ := hreg
  have h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := hT hTM
  have hU : GGMemberUnitary p Bs L := hrow
  obtain ⟨K, hKfield, hKfin, hKchar, f, n, ψ, hKcard, hn4, hker, hrange, hpf, hpos, hlab⟩ :=
    ggMemberUnitary_position hcfg (Or.inl rfl) hU
  letI : Field K := hKfield
  letI : Finite K := hKfin
  letI : CharP K 2 := hKchar
  obtain ⟨ε, hεrefl, hεlevi⟩ := hpos
  obtain ⟨bb, hnb, hlabL⟩ := hlab
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · exfalso
      have h1 : 1 < Nat.card K := Finite.one_lt_card
      rw [hKcard, h0] at h1
      norm_num at h1
    · exact h0
  let a0 : Fin n := ⟨0, by omega⟩
  let b0 : Fin n := ⟨1, by omega⟩
  have hab : a0 ≠ b0 := by
    intro h
    have := congrArg Fin.val h
    simp [a0, b0] at this
  have hA : ((ε (Equiv.swap a0 b0) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) ∈ ggAutomizer L Bs :=
    (ε (Equiv.swap a0 b0)).2
  have hC := ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres h3
    (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) hA) (hεrefl a0 b0 hab)
  have hguard := hbig _ hA hC
  have hrS : ggRankOneIn L Bs ((ε (Equiv.swap a0 b0) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) =
      (ggSuPairBlock K 2 f n a0 b0).map ψ := hεlevi a0 b0 hab
  let blockMap : Su K 2 f 2 →* Su K 2 f n := blockEmb K 2 f n 2 0 (by omega)
  have hblockrange : blockMap.range = ggSuPairBlock K 2 f n a0 b0 := by
    change (blockEmb K 2 f n 2 0 (by omega)).range = ggSuPairBlock K 2 f n a0 b0
    simpa [a0, b0] using
      ggPhanNSAPairAux_range_blockEmb2 (K := K) (p := 2) (f := f) (n := n) (i := 0) (by omega)
  obtain ⟨eSL⟩ :=
    CFSG.LieType.Steinberg.CentralExt.SUThreeThree.nonempty_sl2_mulEquiv_SUid_two
      (p := 2) (f := f) hKcard
  have hblockMap_inj : Function.Injective blockMap := blockEmb_injective (by omega)
  have hφinj : Function.Injective (blockMap.comp eSL.toMonoidHom) :=
    hblockMap_inj.comp eSL.injective
  haveI : CharP (fixedSubfield K 2 f) 2 := inferInstance
  let θ : Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield K 2 f) →* G :=
    ψ.comp (blockMap.comp eSL.toMonoidHom)
  have hθinj : Function.Injective θ :=
    PsiDiag.injective_comp_of_ker_le_center (blockMap.comp eSL.toMonoidHom) hφinj ψ hker
  have hrangeθ : θ.range =
      ggRankOneIn L Bs ((ε (Equiv.swap a0 b0) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) := by
    change (ψ.comp (blockMap.comp eSL.toMonoidHom)).range = _
    rw [MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eSL.surjective,
      Subgroup.map_top, hblockrange, hrS]
  have hcard : Nat.card ↥(ggRankOneIn L Bs
      ((ε (Equiv.swap a0 b0) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)) =
      Nat.card (fixedSubfield K 2 f) * (Nat.card (fixedSubfield K 2 f) ^ 2 - 1) := by
    rw [← hrangeθ, ← ggSL2_card (fixedSubfield K 2 f)]
    exact Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv.symm
  rw [hcard, CFSG.LieType.Steinberg.card_fixedSubfield hKcard] at hguard
  have hf2 : 2 ≤ f := by
    by_contra hlt
    have : f = 1 := by omega
    subst this
    exact hguard (by norm_num)
  have hΛ : LargeEvenInLambda2 ⟨.twA, bb, f⟩ := by
    refine ⟨hf1, ?_⟩
    show 2 ≤ bb ∧ (bb = 2 → 2 ≤ f)
    omega
  exact largeEvenMarking_mono (fun lab' _ _ _ _ _ ⟨he, hP⟩ => ⟨by
      unfold GGLabQFour; rw [he]; exact hf2, hP⟩)
    (ggInnerDiagOn_relabel hRig hcfg.1.2.2.1.1 hΛ hlabL)

end NSJoin

end CFSG.StandardType

end
