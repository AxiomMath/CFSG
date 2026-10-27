module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private abbrev s16c6ConjAction (C : Subgroup G) : MulAction ↥C G where
  smul := fun c g => (c : G) * g * (c : G)⁻¹
  one_smul := fun g => by
    show ((1 : ↥C) : G) * g * ((1 : ↥C) : G)⁻¹ = g
    simp
  mul_smul := fun a b g => by
    show ((a * b : ↥C) : G) * g * ((a * b : ↥C) : G)⁻¹ =
      (a : G) * ((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹
    simp [mul_assoc]

private theorem s16c6_nine_le_card_inf_centralizer {E V₀ : Subgroup G}
    (hEN : E ≤ normalizer (V₀ : Set G)) (hV₀card : Nat.card V₀ ≤ 4)
    (hEcard : Nat.card E = 27) {w : G} (hw0 : w ∈ V₀) (hw1 : w ≠ 1) :
    9 ≤ Nat.card (E ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) := by
  classical
  let C : Subgroup G := E ⊓ Subgroup.centralizer ({w} : Set G)
  letI : MulAction ↥E G := s16c6ConjAction E
  have hstab : MulAction.stabilizer ↥E w = C.subgroupOf E := by
    ext c
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hc
      exact ⟨c.2, mul_inv_eq_iff_eq_mul.1 hc⟩
    · rintro ⟨-, hc⟩
      show (c : G) * w * (c : G)⁻¹ = w
      rw [mul_inv_eq_iff_eq_mul]
      exact hc
  have hidx : C.relIndex E = (MulAction.orbit ↥E w).ncard := by
    rw [Subgroup.relIndex, ← hstab]
    exact MulAction.index_stabilizer ↥E w
  have horb_sub : MulAction.orbit ↥E w ⊆ (V₀ : Set G) \ {1} := by
    rintro z ⟨e, rfl⟩
    refine ⟨?_, ?_⟩
    · show (e : G) * w * (e : G)⁻¹ ∈ V₀
      exact ((Subgroup.mem_normalizer_iff.1 (hEN e.2)) w).1 hw0
    · intro hz
      rw [Set.mem_singleton_iff] at hz
      refine hw1 ?_
      have h3 : (e : G)⁻¹ * ((e : G) * w * (e : G)⁻¹) * (e : G) = 1 := by
        have hz' : (e : G) * w * (e : G)⁻¹ = 1 := hz
        rw [hz']; group
      have h4 : (e : G)⁻¹ * ((e : G) * w * (e : G)⁻¹) * (e : G) = w := by group
      rw [h4] at h3
      exact h3
  have horbit_le : (MulAction.orbit ↥E w).ncard ≤ 3 := by
    have h1 : (MulAction.orbit ↥E w).ncard ≤ ((V₀ : Set G) \ {1}).ncard :=
      Set.ncard_le_ncard horb_sub
    have h2 : ((V₀ : Set G) \ {1}).ncard = Nat.card V₀ - 1 := by
      rw [Set.ncard_sdiff_singleton_of_mem (Subgroup.one_mem V₀)]
      congr 1
    rw [h2] at h1
    omega
  have hrel : C.relIndex E ≤ 3 := by rw [hidx]; exact horbit_le
  have hprod : C.relIndex E * Nat.card C = 27 := by
    have h := Subgroup.relIndex_mul_card C E
    rw [inf_eq_left.2 inf_le_left, hEcard] at h
    exact h
  by_contra hcon
  have hcon' : ¬ (9 ≤ Nat.card C) := hcon
  have h8 : Nat.card C ≤ 8 := by omega
  have hb := Nat.mul_le_mul hrel h8
  omega

theorem s16c6_v0_rank (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hc : Case163_6 D V₀ V hV L) {w : G} (hwV : w ∈ V) (hw1 : w ≠ 1)
    (hw0 : w ∈ V₀) : 2 ≤ CFSG.Open.pRank 3 (D.M ⊓ centralizer ({w} : Set G)) := by
  classical
  have hP : PairFacts D.M V₀ V := hS.setting.hyp16.hyp125.pairFacts
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp1 : 1 < 3 := by norm_num
  obtain ⟨E, hEM, hEel, hEcard⟩ := CFSG.SectionRank.exists_pRank hp1 D.M
  have hEcard27 : Nat.card E = 27 := by
    rw [hEcard, hc.2.2.2.2]
    norm_num
  have hV₀card : Nat.card V₀ ≤ 4 := by
    have h1 : Nat.card V₀ = 2 ^ mSub V₀ := card_eq_two_pow_mSub hP.elemAbelian₀.isPGroup
    have h2 : 2 ^ mSub V₀ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hS.setting.hyp16.small
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num] at h2
    exact h1.trans_le h2
  have hEN : E ≤ normalizer (V₀ : Set G) := hEM.trans hP.le_normalizer₀
  have h9 : 9 ≤ Nat.card (E ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) :=
    s16c6_nine_le_card_inf_centralizer hEN hV₀card hEcard27 hw0 hw1
  have hCel : IsElemAbelian 3 (E ⊓ Subgroup.centralizer ({w} : Set G)) :=
    hEel.mono inf_le_left
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hCel.isPGroup
  have hk2 : 2 ≤ k := by
    have h33 : 3 ^ 2 ≤ 3 ^ k := by
      calc 3 ^ 2 = 9 := by norm_num
        _ ≤ Nat.card (E ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) := h9
        _ = 3 ^ k := hk
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h33
  have hsub : (E ⊓ Subgroup.centralizer ({w} : Set G)) ≤
      D.M ⊓ Subgroup.centralizer ({w} : Set G) :=
    le_inf (inf_le_left.trans hEM) inf_le_right
  exact le_trans hk2 (CFSG.SectionRank.le_pRank hp1 hsub hCel hk)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
