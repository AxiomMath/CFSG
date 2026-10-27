module

public import CFSG.Quasithin.H13.A5S1521r
public import CFSG.Quasithin.Background.G64Case1Pre
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.RankThree.CentralLiftU.UnitaryThreeEven
public import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank

@[expose] def FactLieSL2Row1321 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ w : V, w ^ 2 = 1) →
    ∀ (G L : Subgroup (MulAut V)) (v : MulAut V), B4Hyp G L → Cond1321 G L v →
      ∀ n, 3 ≤ n → ¬ BinaryNaturalSL L ⊤ ⊥ 2 n

@[expose] def FactLieSL3Row1321 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ w : V, w ^ 2 = 1) →
    ∀ (G L : Subgroup (MulAut V)) (v : MulAut V), B4Hyp G L → Cond1321 G L v →
      ∀ n, 3 ≤ n → ¬ BinaryNaturalSL L ⊤ ⊥ 3 n

@[expose] def FactLieSL3FourRow1321 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ w : V, w ^ 2 = 1) →
    ∀ (G L : Subgroup (MulAut V)) (v : MulAut V), B4Hyp G L → Cond1321 G L v →
      ¬ BinaryNaturalSL L ⊤ ⊥ 3 2

@[expose] def FactLieSp4Row1321 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ w : V, w ^ 2 = 1) →
    ∀ (G L : Subgroup (MulAut V)) (v : MulAut V), B4Hyp G L → Cond1321 G L v →
      ∀ n, 3 ≤ n → ¬ BinaryNaturalSp4 L ⊤ ⊥ n

@[expose] def FactLieSp4FourRow1321 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ w : V, w ^ 2 = 1) →
    ∀ (G L : Subgroup (MulAut V)) (v : MulAut V), B4Hyp G L → Cond1321 G L v →
      ¬ BinaryNaturalSp4 L ⊤ ⊥ 2

@[expose] def FactLieG2Row1321 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ w : V, w ^ 2 = 1) →
    ∀ (G L : Subgroup (MulAut V)) (v : MulAut V), B4Hyp G L → Cond1321 G L v →
      ∀ n, 3 ≤ n → ¬ G2Natural L ⊤ ⊥ n

@[expose] def FactLieG2FourRow1321 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ w : V, w ^ 2 = 1) →
    ∀ (G L : Subgroup (MulAut V)) (v : MulAut V), B4Hyp G L → Cond1321 G L v →
      ¬ G2Natural L ⊤ ⊥ 2

@[expose] def FactLieOrthRow1321 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ w : V, w ^ 2 = 1) →
    ∀ (G L : Subgroup (MulAut V)) (v : MulAut V), B4Hyp G L → Cond1321 G L v →
      ∀ m, 3 ≤ m → ¬ BinaryOrthogonalFour L ⊤ ⊥ m

@[expose] def FactLieOrthFourRow1321 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ w : V, w ^ 2 = 1) →
    ∀ (G L : Subgroup (MulAut V)) (v : MulAut V), B4Hyp G L → Cond1321 G L v →
      ¬ BinaryOrthogonalFour L ⊤ ⊥ 2

@[expose] def FactLieSU3Row1321 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ w : V, w ^ 2 = 1) →
    ∀ (G L : Subgroup (MulAut V)) (v : MulAut V), B4Hyp G L → Cond1321 G L v →
      ∀ m, 2 ≤ m → ¬ BinaryNaturalSU3 L ⊤ ⊥ m

@[expose] def FactLieSzRow1321 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ w : V, w ^ 2 = 1) →
    ∀ (G L : Subgroup (MulAut V)) (v : MulAut V), B4Hyp G L → Cond1321 G L v →
      ∀ f, ¬ BinaryNaturalSz L ⊤ ⊥ f

@[expose] def FactLieNineRow1321 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ w : V, w ^ 2 = 1) →
    ∀ (G L : Subgroup (MulAut V)) (v : MulAut V), B4Hyp G L → Cond1321 G L v →
      ∀ m, 3 ≤ m → ¬ BinaryNineTensor L ⊤ ⊥ m

@[expose] def FactLieNineTwoRow1321 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ w : V, w ^ 2 = 1) →
    ∀ (G L : Subgroup (MulAut V)) (v : MulAut V), B4Hyp G L → Cond1321 G L v →
      ¬ BinaryNineTensor L ⊤ ⊥ 1

@[expose] def FactLieNineFourRow1321 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ w : V, w ^ 2 = 1) →
    ∀ (G L : Subgroup (MulAut V)) (v : MulAut V), B4Hyp G L → Cond1321 G L v →
      ¬ BinaryNineTensor L ⊤ ⊥ 2

@[expose] def FactLieTwistRow1321 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ w : V, w ^ 2 = 1) →
    ∀ (G L : Subgroup (MulAut V)) (v : MulAut V), B4Hyp G L → Cond1321 G L v →
      ∀ a, 3 ≤ a → ¬ TwistedTensorSp4 L ⊤ ⊥ a

@[expose] def FactLieTwistTwoRow1321 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ w : V, w ^ 2 = 1) →
    ∀ (G L : Subgroup (MulAut V)) (v : MulAut V), B4Hyp G L → Cond1321 G L v →
      ¬ TwistedTensorSp4 L ⊤ ⊥ 1

@[expose] def FactLieTwistFourRow1321 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ w : V, w ^ 2 = 1) →
    ∀ (G L : Subgroup (MulAut V)) (v : MulAut V), B4Hyp G L → Cond1321 G L v →
      ¬ TwistedTensorSp4 L ⊤ ⊥ 2

section Vacuous

variable {V : Type} [CommGroup V]

theorem not_binaryNaturalSL_zero (H : Subgroup (MulAut V)) (d : ℕ) :
    ¬ BinaryNaturalSL H ⊤ ⊥ d 0 := by
  rintro ⟨K, _, _, hK, -⟩
  exact card_field_ne_one K (by simpa using hK)

theorem not_binaryNaturalSU3_zero (H : Subgroup (MulAut V)) : ¬ BinaryNaturalSU3 H ⊤ ⊥ 0 := by
  rintro ⟨K, _, _, hK, -⟩
  exact card_field_ne_one K (by simpa using hK)

theorem false_of_isQuasisimple_isSolvable {X : Type*} [Group X] (hq : CFSG.IsQuasisimple X)
    (hs : Group.IsSolvable X) : False := by
  have : Nontrivial X := CFSG.LocalCores.isQuasisimple_nontrivial hq
  have : Group.IsPerfect X := hq.1
  exact Group.IsPerfect.not_isSolvable X hs

variable [Finite V]

theorem not_binaryNaturalSL_two_one {L : Subgroup (MulAut V)} (hq : CFSG.IsQuasisimple ↥L) :
    ¬ BinaryNaturalSL L ⊤ ⊥ 2 1 := by
  rintro ⟨K, _, _, hK, π, hπ⟩
  have hinj : Function.Injective π :=
    G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ
  let e : ↥(StatedSL 2 K) ≃* ↥L := MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
  have h6 : Nat.card ↥L = 6 := by
    rw [← Nat.card_congr e.toEquiv,
      ← Nat.card_congr (specialLinearGroupEquivStatedSL 2 K).toEquiv,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK]
    norm_num
  exact G64.not_isQuasisimple_of_card_six h6 hq

omit [Finite V] in
theorem not_binaryNaturalSU3_one {L : Subgroup (MulAut V)} (hq : CFSG.IsQuasisimple ↥L) :
    ¬ BinaryNaturalSU3 L ⊤ ⊥ 1 := by
  rintro ⟨K, _, _, hK, π, hπ⟩
  have hinj : Function.Injective π :=
    G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ
  let e : ↥(StatedSU 3 (2 ^ 1) K) ≃* ↥L := MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K :=
    ⟨Nat.prime_two, le_rfl, hK.trans (by norm_num)⟩
  have hcard := CFSG.RankThree.CentralLiftU.card_statedSU_three_two hU rfl
  have := Fintype.ofFinite ↥(StatedSU 3 (2 ^ 1) K)
  have hsolv : Group.IsSolvable ↥(StatedSU 3 (2 ^ 1) K) :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 3)
      (b := 3) Nat.prime_two Nat.prime_three (by norm_num)
      (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)
  exact false_of_isQuasisimple_isSolvable hq
    (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)

end Vacuous

theorem factLieRows1321_of (hSL2 : FactLieSL2Row1321) (hSL3 : FactLieSL3Row1321)
    (hSL3f : FactLieSL3FourRow1321) (hSp4 : FactLieSp4Row1321) (hSp4f : FactLieSp4FourRow1321)
    (hG2 : FactLieG2Row1321) (hG2f : FactLieG2FourRow1321) (hO : FactLieOrthRow1321)
    (hOf : FactLieOrthFourRow1321) (hSU3 : FactLieSU3Row1321) (hSz : FactLieSzRow1321)
    (hN : FactLieNineRow1321) (hN2 : FactLieNineTwoRow1321) (hN4 : FactLieNineFourRow1321)
    (hT : FactLieTwistRow1321) (hT2 : FactLieTwistTwoRow1321)
    (hT4 : FactLieTwistFourRow1321) : FactLieRows1321 := by
  intro V _ _ hV G L v hB4 hc hrow
  have hq : CFSG.IsQuasisimple ↥L := hB4.2.2.1
  rcases hrow with ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | ⟨m, hm, h⟩ | ⟨m, h⟩ |
      ⟨f, h⟩ | ⟨m, hm, h⟩ | ⟨a, ha, h⟩
  ·
    rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · interval_cases n
      · exact not_binaryNaturalSL_zero L 2 h
      · exact not_binaryNaturalSL_two_one hq h
      · exact hn rfl
    · exact hSL2 V hV G L v hB4 hc n hn3 h
  ·
    rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · interval_cases n
      · exact not_binaryNaturalSL_zero L 3 h
      · exact hn rfl
      · exact hSL3f V hV G L v hB4 hc h
    · exact hSL3 V hV G L v hB4 hc n hn3 h
  ·
    rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · obtain rfl : n = 2 := by omega
      exact hSp4f V hV G L v hB4 hc h
    · exact hSp4 V hV G L v hB4 hc n hn3 h
  ·
    rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · obtain rfl : n = 2 := by omega
      exact hG2f V hV G L v hB4 hc h
    · exact hG2 V hV G L v hB4 hc n hn3 h
  ·
    rcases Nat.lt_or_ge m 3 with hm3 | hm3
    · obtain rfl : m = 2 := by omega
      exact hOf V hV G L v hB4 hc h
    · exact hO V hV G L v hB4 hc m hm3 h
  ·
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · interval_cases m
      · exact not_binaryNaturalSU3_zero L h
      · exact not_binaryNaturalSU3_one hq h
    · exact hSU3 V hV G L v hB4 hc m hm2 h
  ·
    exact hSz V hV G L v hB4 hc f h
  ·
    rcases Nat.lt_or_ge m 3 with hm3 | hm3
    · interval_cases m
      · exact hN2 V hV G L v hB4 hc h
      · exact hN4 V hV G L v hB4 hc h
    · exact hN V hV G L v hB4 hc m hm3 h
  ·
    rcases Nat.lt_or_ge a 3 with ha3 | ha3
    · interval_cases a
      · exact hT2 V hV G L v hB4 hc h
      · exact hT4 V hV G L v hB4 hc h
    · exact hT V hV G L v hB4 hc a ha3 h

end CFSG.Quasithin.H13.A5
