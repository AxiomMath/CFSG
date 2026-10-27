module

public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoTorus
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoRank
import CFSG.LieType.SeitzGeneration.ExcTorusF4One
import CFSG.LieType.SeitzGeneration.ExcTorusF4Two
import CFSG.LieType.SeitzGeneration.Lift
import CFSG.LieType.SeitzGeneration.RegimesExcFamilies
import CFSG.RankThree.PartOne.KE.EDualStabilizer

public section

namespace CFSG.StandardType.ExcFieldAutCentRankF4

open CFSG.Blueprint.Chevalley
open CFSG.Open (IsElemAbelian)

section Rank


private theorem exists_ringHom_of_dvd_card {F D : Type} [Field F] [Field D] [Finite F] [Finite D]
    [CharP F 2] [CharP D 2] {f d : ℕ} (hF : Nat.card F = 2 ^ f) (hD : Nat.card D = 2 ^ d)
    (hfd : f ∣ d) : Nonempty (F →+* D) := by
  let _ : Algebra (ZMod 2) F := ZMod.algebra F 2
  let _ : Algebra (ZMod 2) D := ZMod.algebra D 2
  have : Fintype F := Fintype.ofFinite F
  have : Fintype D := Fintype.ofFinite D
  have hfF : Module.finrank (ZMod 2) F = f := by
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := F)
    rw [ZMod.card, Fintype.card_eq_nat_card, hF] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  have hfD : Module.finrank (ZMod 2) D = d := by
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := D)
    rw [ZMod.card, Fintype.card_eq_nat_card, hD] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  obtain ⟨ι⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod 2) (K := F) (L := D)
    (by rw [hfF, hfD]; exact hfd)
  exact ⟨ι.toRingHom⟩

private theorem zmod3_smul_eq_zero (v : Fin 3 → ZMod 3) : (3 : ℕ) • v = 0 := by
  have h3 : ((3 : ℕ) : ZMod 3) = 0 := CharP.cast_eq_zero (ZMod 3) 3
  calc (3 : ℕ) • v = ((3 : ℕ) : ZMod 3) • v := (Nat.cast_smul_eq_nsmul (ZMod 3) 3 v).symm
    _ = 0 := by rw [h3, zero_smul]

private theorem ofAdd_pow_three (x : Multiplicative (Fin 3 → ZMod 3)) : x ^ 3 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  exact zmod3_smul_eq_zero (Multiplicative.toAdd x)

private theorem isElemAbelian_range_torusE (K : Type) [Field K] [CharP K 2] :
    IsElemAbelian 3 (CFSG.StandardType.TableBF4Two.torusE K).range := by
  have htop : IsElemAbelian 3 (⊤ : Subgroup (Multiplicative (Fin 3 → ZMod 3))) := by
    rw [← Subgroup.closure_univ]
    refine CFSG.Open.IsElemAbelian.closure_of_commute ?_ ?_
    · intro a _ b _
      exact mul_comm a b
    · intro a _
      exact ofAdd_pow_three a
  have hmap := CFSG.Open.IsElemAbelian.map htop (CFSG.StandardType.TableBF4Two.torusE K)
  rwa [Subgroup.map_top] at hmap

private theorem card_range_torusE (K : Type) [Field K] [CharP K 2] :
    Nat.card (CFSG.StandardType.TableBF4Two.torusE K).range = 3 ^ 3 := by
  let e := MonoidHom.ofInjective (CFSG.StandardType.TableBF4Two.torusE_injective (K := K))
  rw [← Nat.card_congr e.toEquiv]
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative]
  simp [Fintype.card_fun, ZMod.card]

private theorem orderOf_cardK_dvd_two {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hd : p ∣ Nat.card K ^ 2 - 1) :
    orderOf ((Nat.card K : ℕ) : ZMod p) ∣ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Nonempty K := ⟨0⟩
  have hqpos : 0 < Nat.card K := Nat.card_pos
  have h1le : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow 2 (Nat.card K) hqpos
  have h0 : ((Nat.card K ^ 2 - 1 : ℕ) : ZMod p) = 0 := by
    rw [CharP.cast_eq_zero_iff (ZMod p) p]
    exact hd
  have hsq : ((Nat.card K : ZMod p)) ^ 2 = 1 := by
    have hsub : ((Nat.card K ^ 2 - 1 : ℕ) : ZMod p) =
        ((Nat.card K : ZMod p)) ^ 2 - 1 := by
      rw [Nat.cast_sub h1le, Nat.cast_pow, Nat.cast_one]
    rw [hsub, sub_eq_zero] at h0
    exact h0
  exact orderOf_dvd_of_pow_eq_one hsq

theorem card_le_pow_four {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hd : p ∣ Nat.card K ^ 2 - 1) {E : Subgroup (adjointGroup .F4 K)}
    (hE : IsElemAbelian p E) : Nat.card E ≤ p ^ 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hfcard⟩ := FiniteField.card (K := K) 2
  let K' := GaloisField 2 (2 * (f : ℕ))
  have hK'ne : 2 * (f : ℕ) ≠ 0 := by
    have hf0 : (f : ℕ) ≠ 0 := PNat.ne_zero f
    omega
  have hK'card : Nat.card K' = 2 ^ (2 * (f : ℕ)) :=
    GaloisField.card 2 (2 * (f : ℕ)) hK'ne
  have hKcard : Nat.card K = 2 ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card, hfcard]
  have hq2 : Nat.card K ^ 2 = 2 ^ (2 * (f : ℕ)) := by
    rw [hKcard, ← pow_mul, Nat.mul_comm (f : ℕ) 2]
  have hpq' : p ∣ Nat.card K' - 1 := by
    rw [hK'card, ← hq2]
    exact hd
  have hdvd : (f : ℕ) ∣ 2 * (f : ℕ) := ⟨2, by ring⟩
  obtain ⟨ι⟩ := exists_ringHom_of_dvd_card hKcard hK'card hdvd
  have hT : CFSG.StandardType.GGF4ToralRankInput K' p := by
    rcases eq_or_ne p 3 with hp3 | hp3
    · subst hp3
      exact CFSG.StandardType.TableBF4.ggF4ToralRankInput_three hpq'
    · have hp5 : 5 ≤ p := by
        have hodd : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left hp2
        have h2 : 2 ≤ p := hp.two_le
        by_contra h
        have hlt : p < 5 := Nat.lt_of_not_le h
        have hp3' : p = 3 := by omega
        exact hp3 hp3'
      exact CFSG.StandardType.TableBF4.ggF4ToralRankInput_of_five_le hp hp5 hpq'
  have hmapE : IsElemAbelian p (E.map (CFSG.StandardType.TableBF4Two.adjointMap ι)) :=
    CFSG.StandardType.TableB.isElemAbelian_map hE _
  have h1 := CFSG.StandardType.GGF4ToralRankInput.card_le (K := K') hp hpq' hT hmapE
  rwa [Subgroup.card_map_of_injective
    (CFSG.StandardType.TableBF4Two.adjointMap_injective ι)] at h1

theorem exists_elemAbelian_pow_three_le {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ∣ Nat.card K ^ 2 - 1) :
    ∃ E : Subgroup (adjointGroup .F4 K), IsElemAbelian p E ∧ p ^ 3 ≤ Nat.card E := by
  rcases eq_or_ne p 3 with hp3 | hp3
  · subst hp3
    exact ⟨(CFSG.StandardType.TableBF4Two.torusE K).range,
      isElemAbelian_range_torusE K, (card_range_torusE K).ge⟩
  · have hp5 : 5 ≤ p := by
      have hodd : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left hp2
      have h2 : 2 ≤ p := hp.two_le
      by_contra h
      have hlt : p < 5 := Nat.lt_of_not_le h
      have hp3' : p = 3 := by omega
      exact hp3 hp3'
    have hdvd := orderOf_cardK_dvd_two (K := K) hp hd
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
    · obtain ⟨E, hE, hcard⟩ :=
        CFSG.LieType.SeitzGeneration.exists_elemAbelian_F4_one K hp (by omega) h1
      exact ⟨E, hE, by rw [hcard]; exact Nat.pow_le_pow_right hp.pos (by norm_num : 3 ≤ 4)⟩
    · obtain ⟨E, hE, hcard⟩ :=
        CFSG.LieType.SeitzGeneration.exists_elemAbelian_F4_two K hp (by omega) h2
      exact ⟨E, hE, by rw [hcard]; exact Nat.pow_le_pow_right hp.pos (by norm_num : 3 ≤ 4)⟩

end Rank

end CFSG.StandardType.ExcFieldAutCentRankF4
