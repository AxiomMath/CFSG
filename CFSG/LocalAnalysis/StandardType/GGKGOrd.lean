module

public import CFSG.LocalAnalysis.StandardType.GGKGTag
public import CFSG.Adapters.LieModelOrders
public import CFSG.LocalAnalysis.StandardType.GGKnownInputsNoU6Classical

public section

namespace CFSG.StandardType.KG

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.Y10GField CFSG.LocalAnalysis.GLTheoremA.Y10F

theorem kg_card_BC
    {X : Type} [Group X] {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab)
    (ht : lab.tag = .B ∨ lab.tag = .C) (hX : GGHasLabel lab X) :
    Nat.card X = 2 ^ (lab.n * lab.rank ^ 2) *
      ∏ i ∈ Finset.Icc 1 lab.rank, (2 ^ (2 * lab.n * i) - 1) := by
  have htag : lab.tag = .A ∨ lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D := by
    rcases ht with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  have hmarked := SCFourCover.largeEvenLabelAll_markedModel_classical hl htag
  have hraw : LargeEvenRawDatum lab
      (fun R _ I F => Nonempty (X ≃* R) ∧ MarkedModel lab R) :=
    hmarked (fun R _ _ _ => Nonempty (X ≃* R)) hX
  obtain ⟨R, hRgrp, I, F, hIso, hM⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨e⟩ := hIso
  have hcard : Nat.card X = Nat.card R := Nat.card_congr e.toEquiv
  have hrank2 : 2 ≤ lab.rank := by
    rcases ht with h | h
    · have hh := hl.2
      rw [h] at hh
      exact hh.1
    · have hh := hl.2
      rw [h] at hh
      exact hh.1
  have hM' : CFSG.Blueprint.LieModel R .PSp lab.rank 2 lab.n := by
    rcases ht with h | h <;>
      simpa only [MarkedModel, markTag, markRank, markChar, markDeg, h] using hM
  have hlie : Nat.card R =
      CFSG.EvenSmallLie.CatalogOrders.lieOrd .PSp lab.rank (2 ^ lab.n) :=
    CFSG.Blueprint.LieModel.card_eq_lieOrd (by omega) hM'
  rw [hcard, hlie]
  simp only [CFSG.EvenSmallLie.CatalogOrders.lieOrd, CFSG.Open.ordBC]
  have hn1 : 1 ≤ lab.n := hl.1
  have hn0 : lab.n ≠ 0 := by omega
  have hodd : Odd (2 ^ lab.n - 1) :=
    Nat.Even.sub_odd (Nat.one_le_two_pow) (Nat.even_pow.mpr ⟨even_two, hn0⟩) odd_one
  have hgcd : Nat.gcd 2 (2 ^ lab.n - 1) = 1 :=
    (Nat.coprime_two_left.mpr hodd).gcd_eq_one
  rw [hgcd, Nat.div_one]
  congr 1
  · rw [← pow_mul]
    congr 1
    ring
  · apply Finset.prod_congr rfl
    intro i hi
    rw [← pow_mul]
    congr 1
    ring

theorem kg_seven_dvd_card_C
    {X : Type} [Group X] {k f : ℕ} (hk : 3 ≤ k) (hC : GGHasLabel ⟨.C, k, f⟩ X) :
    7 ∣ Nat.card X := by
  have hl : LargeEvenInLambda2 ⟨.C, k, f⟩ := kg_inLambda2_C hk hC
  rw [kg_card_BC (lab := ⟨.C, k, f⟩) hl (Or.inr rfl) hC]
  apply Dvd.dvd.mul_left
  have hmem : 3 ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have h7 : 7 ∣ 2 ^ (2 * f * 3) - 1 := by
    have hbase : 7 ∣ 2 ^ 6 - 1 := by norm_num
    have hstep : 2 ^ 6 - 1 ∣ (2 ^ 6) ^ f - 1 ^ f :=
      Nat.sub_dvd_pow_sub_pow (2 ^ 6) 1 f
    have hone : (2 ^ 6) ^ f - 1 ^ f = 2 ^ (2 * f * 3) - 1 := by
      rw [one_pow, ← pow_mul]
      congr 1
      ring
    simpa only [hone] using hbase.trans hstep
  exact h7.trans (Finset.dvd_prod_of_mem (s := Finset.Icc 1 k)
    (f := fun i => 2 ^ (2 * f * i) - 1) hmem)

theorem kg_five_dvd_card_C
    {X : Type} [Group X] {k f : ℕ} (hk : 3 ≤ k) (hC : GGHasLabel ⟨.C, k, f⟩ X) :
    5 ∣ Nat.card X := by
  have hl : LargeEvenInLambda2 ⟨.C, k, f⟩ := kg_inLambda2_C hk hC
  rw [kg_card_BC (lab := ⟨.C, k, f⟩) hl (Or.inr rfl) hC]
  apply Dvd.dvd.mul_left
  have hmem : 2 ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have h5 : 5 ∣ 2 ^ (2 * f * 2) - 1 := by
    have hbase : 5 ∣ 2 ^ 4 - 1 := by norm_num
    have hstep : 2 ^ 4 - 1 ∣ (2 ^ 4) ^ f - 1 ^ f :=
      Nat.sub_dvd_pow_sub_pow (2 ^ 4) 1 f
    have hone : (2 ^ 4) ^ f - 1 ^ f = 2 ^ (2 * f * 2) - 1 := by
      rw [one_pow, ← pow_mul]
      congr 1
      ring
    simpa only [hone] using hbase.trans hstep
  exact h5.trans (Finset.dvd_prod_of_mem (s := Finset.Icc 1 k)
    (f := fun i => 2 ^ (2 * f * i) - 1) hmem)

end CFSG.StandardType.KG
