module

public import CFSG.RankThree.PartTwo.Sec19.Item19ResProofSeitzInner
import CFSG.Adapters.ClassicalCatalogLinearUnitary
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3CoverGenCoverUni
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

@[expose] def Seitz199Outer : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (D : Subgroup (MulAut X)),
    (∀ φ ∈ D, φ ^ 3 = 1) → Nat.card D = 9 → CFSG.IsQuasisimple X → Sec4.IsSLThreePi X →
    ¬ D ≤ (MulAut.conj : X →* MulAut X).range →
    (∃ e ∈ D, ∃ s : X, s ^ 3 = 1 ∧ MulAut.conj s ∈ D ∧ e s ≠ s) →
    Subgroup.closure {x : X | ∃ φ ∈ D, φ ≠ 1 ∧ φ x = x} = ⊤

namespace Item19ResProof

open TauCeti CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

theorem isElemAbelian_of_pow_three {Y : Type*} [Group Y] {D : Subgroup Y}
    (hD3 : ∀ φ ∈ D, φ ^ 3 = 1) (hD9 : Nat.card D = 9) : CFSG.Open.IsElemAbelian 3 D := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hD9]; norm_num), hD3⟩

theorem closure_fixSet_sl_of_fixCube {X : Type} [Group X] {q : ℕ} {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = q) (hq : q % 3 = 1) (ι : X ≃* StatedSL 3 K)
    (D : Subgroup (MulAut X)) (hD : CFSG.Open.IsElemAbelian 3 D) (hD9 : Nat.card D = 9)
    (hfix : FixCube D) : Subgroup.closure (fixSet D) = ⊤ := by
  set ψ : X ≃* Matrix.SpecialLinearGroup (Fin 3) K :=
    ι.trans (specialLinearGroupEquivStatedSL 3 K).symm with hψ
  have h3 : 3 ∣ Nat.card K - 1 := by rw [hK]; omega
  have h := closure_fixSet_eq_top_linear h3 (mapAut ψ D) (isElemAbelian_mapAut hD ψ)
    (by rw [card_mapAut, hD9]) (hfix.mapAut ψ)
  exact (closure_fixSet_mapAut_eq_top_iff ψ D).mp h

theorem exists_unitaryFieldData {K : Type} [Field K] [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq1 : q ≠ 1) : ∃ p f : ℕ, q = p ^ f ∧ UnitaryFieldData p f K := by
  have := Fintype.ofFinite K
  obtain ⟨p, -, n, hp, hcard⟩ := FiniteField.card' K
  rw [← Nat.card_eq_fintype_card, hK] at hcard
  have hdvd : q ∣ p ^ (n : ℕ) := ⟨q, by rw [← hcard]; ring⟩
  obtain ⟨k, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  refine ⟨p, k, rfl, hp, ?_, by rw [hK, ← pow_mul, mul_comm]⟩
  by_contra h
  have hk : k = 0 := by omega
  rw [hk, pow_zero] at hq1
  exact hq1 rfl

theorem exists_unitary_model {X : Type} [Group X] (hX : CFSG.IsQuasisimple X) {q : ℕ} {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = q ^ 2) (hq : q % 3 = 2) (ι : X ≃* StatedSU 3 q K) :
    ∃ p f : ℕ, ∃ _ : UnitaryFieldData p f K, p ^ f % 3 = 2 ∧ 2 < p ^ f ∧
      Nonempty (X ≃* CFSG.ClassicalGroups.UnitaryFlag.unitarySU p f K 3) := by
  obtain ⟨p, f, rfl, hU⟩ := exists_unitaryFieldData hK (by omega)
  refine ⟨p, f, hU, hq, ?_, ⟨ι⟩⟩
  have hp2 : 2 ≤ p ^ f := hU.prime.two_le.trans (Nat.le_self_pow (by have := hU.one_le; omega) p)
  by_contra h
  have hpf : p ^ f = 2 := by omega
  obtain ⟨rfl, rfl⟩ := CFSG.ClassicalModels.eq_two_one_of_pow_eq_two hU.prime hU.one_le hpf
  have hcard := CFSG.RankThree.CentralLiftU.card_statedSU_three_two hU rfl
  have := Fintype.ofFinite (StatedSU 3 (2 ^ 1) K)
  have hsolv : Group.IsSolvable (StatedSU 3 (2 ^ 1) K) :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 3) (b := 3)
      Nat.prime_two Nat.prime_three (by norm_num)
      (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)
  have hsolvX : Group.IsSolvable X :=
    Group.isSolvable_of_surjective (f := ι.symm.toMonoidHom) (MulEquiv.surjective _)
  have : Group.IsPerfect X := hX.1
  have := CFSG.LocalCores.isQuasisimple_nontrivial hX
  exact Group.IsPerfect.not_isSolvable X hsolvX

theorem closure_fixSet_su_of_fixCube
    {X : Type} [Group X] {p f : ℕ} {K : Type} [Field K] (hU : UnitaryFieldData p f K)
    (hq : p ^ f % 3 = 2) (hq2 : 2 < p ^ f)
    (ι : X ≃* CFSG.ClassicalGroups.UnitaryFlag.unitarySU p f K 3)
    (D : Subgroup (MulAut X)) (hD : CFSG.Open.IsElemAbelian 3 D) (hD9 : Nat.card D = 9)
    (hfix : FixCube D) : Subgroup.closure (fixSet D) = ⊤ := by
  have h3 : 3 ∣ p ^ f + 1 := by omega
  have h := closure_fixSet_eq_top_unitary hU h3 hq2
    (CFSG.AGLEmbedding.KFactProofs.CoverThree.subfieldDiagGenAll_of_certificates hU h3)
    (mapAut ι D) (isElemAbelian_mapAut hD ι) (by rw [card_mapAut, hD9]) (hfix.mapAut ι)
  exact (closure_fixSet_mapAut_eq_top_iff ι D).mp h

theorem nonempty_mulEquiv_sl34 {X : Type} [Group X] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) (ι : X ≃* StatedSL 3 K) :
    Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) := by
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have hcard : Fintype.card K = Fintype.card (GaloisField 2 2) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card 2 2 (by norm_num)]
    norm_num
  exact ⟨(ι.trans (specialLinearGroupEquivStatedSL 3 K).symm).trans
    (slCongr (FiniteField.ringEquivOfCardEq hcard))⟩

end Item19ResProof

end CFSG.RankThree.PartTwo.Sec19
