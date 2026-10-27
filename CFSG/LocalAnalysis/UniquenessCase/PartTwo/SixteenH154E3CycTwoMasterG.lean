module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoCoreBG
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoSelfG
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoIdx
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.Background.A1bPGroups

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin Subgroup

variable {X : Type} [CommGroup X] {Mb : Subgroup (MulAut X)} {ψ z : MulAut X} {U : Subgroup X}
  {q m : ℕ}

private theorem s16h_e3_CycTwoMasterG_rank_comm_pow {p n : ℕ} {P : Type*} [Group P]
    (h : IsElemAbelianOfRank p n P) :
    (∀ a b : P, a * b = b * a) ∧ ∀ a : P, a ^ p = 1 := by
  obtain ⟨e⟩ := h
  refine ⟨fun a b => e.injective ?_, fun a => e.injective ?_⟩
  · rw [map_mul, map_mul, mul_comm]
  · rw [map_pow, map_one]
    ext i
    simp

private theorem s16h_e3_CycTwoMasterG_rank_card {p n : ℕ} {P : Type*} [Group P]
    (h : IsElemAbelianOfRank p n P) : Nat.card P = p ^ n := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd]
  rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod]

private theorem s16h_e3_CycTwoMasterG_isElemAbelian_of_rank {p n : ℕ} {G : Type*} [Group G]
    {E : Subgroup G} (h : IsElemAbelianOfRank p n ↥E) : IsElemAbelian p E := by
  obtain ⟨hcomm, hpow⟩ := s16h_e3_CycTwoMasterG_rank_comm_pow h
  refine ⟨IsMulCommutative.of_comm hcomm, fun x hx => ?_⟩
  have := congrArg Subtype.val (hpow ⟨x, hx⟩)
  simpa using this

theorem s16h_e3_CycTwoMasterG [Finite X] [Finite (MulAut X)] (hq : q.Prime) (hq2 : q ≠ 2)
    (F : s16h_CycFrameG q m Mb ψ z U) {D : Subgroup (MulAut ↥U)}
    (hDA : D ≤ autSub (s16h_CycN Mb z) U) (hDab : IsElemAbelianOfRank q 2 ↥D)
    (hzD : F.rho ⟨z, F.z_mem_N⟩ ∈ D)
    (hSyl : ∀ a ∈ autSub (s16h_CycN Mb z) U, (∃ k : ℕ, orderOf a = q ^ k) → a ∈ D)
    (hcent : ∀ c ∈ autSub (s16h_CycN Mb z) U,
      c ∈ Subgroup.centralizer (D : Set (MulAut ↥U)) → c ∈ D)
    (hker : Nat.card ↥(F.core D ⊓ centSub U) ≤ q) :
    ∃ P : Subgroup (MulAut X), P ≤ Mb ∧ Mb ≤ Subgroup.normalizer (P : Set (MulAut X)) ∧
      ¬ q ∣ P.relIndex Mb ∧ IsPGroup q ↥P ∧ IsElemAbelianOfRank q 3 ↥P ∧
      Subgroup.centralizer (P : Set (MulAut X)) ⊓ Mb ≤ P := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hDe : IsElemAbelian q D := s16h_e3_CycTwoMasterG_isElemAbelian_of_rank hDab
  have hDcard : Nat.card ↥D = q ^ 2 := s16h_e3_CycTwoMasterG_rank_card hDab
  have hPel : IsElemAbelian q (F.core D) := s16h_e3_CycTwoCoreAG_isElemAbelian F hDe
  have hPgrp : IsPGroup q ↥(F.core D) := CFSG.Open.IsElemAbelian.isPGroup hPel
  obtain ⟨hcard, hk⟩ := s16h_e3_CycTwoCoreBG_card hq F hDA hDe hDcard hzD hSyl
  have hker_eq : Nat.card ↥(F.core D ⊓ centSub U) = q := le_antisymm hker hk
  have hcardP : Nat.card ↥(F.core D) = q ^ 3 := by
    rw [hcard, hker_eq]
    ring
  have hrank : IsElemAbelianOfRank q 3 ↥(F.core D) :=
    CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := q) (n := 3)
      (fun a b => hPel.1.is_comm.comm a b) (fun x => Subtype.ext (hPel.2 x x.2)) hcardP
  refine ⟨F.core D, F.core_le D, F.core_normalizes D, ?_, hPgrp, hrank, ?_⟩
  · exact s16h_e3_CycTwoIdx_not_dvd hq hq2 (F.core_le_N D) F.N_le F.idx
      (fun n hn hqn => s16h_e3_CycTwoCoreAG_mem_of_prime hq F hSyl hn hqn)
  · exact s16h_e3_CycTwoSelfG_centralizer_le hq F hDA hDe hzD hSyl hcent

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
