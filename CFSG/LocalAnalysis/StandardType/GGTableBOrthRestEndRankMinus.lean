module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestEndRank
public import CFSG.Timmesfeld.Orders.ClassicalOrthogonal

public section

namespace CFSG.StandardType

open CFSG.Assembly
open scoped Matrix

namespace OrthRestEnd

section Count

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem card_nonzero_singular_qMinus (m : ℕ) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (Nat.card {v : LargeEvenMinusIdx m → K // v ≠ 0 ∧ TableBOrth.qMinusForm K m b c v = 0} : ℤ) =
      ((Nat.card K : ℤ) ^ (m + 1) + 1) * ((Nat.card K : ℤ) ^ m - 1) := by
  have h1 := card_singular_eq_succ (TableBOrth.qMinusForm K m b c)
  have h2 := CFSG.Timmesfeld.ClassicalOrders.card_singular_congr
    (TableBOrth.qMinusIsometry (K := K) m b c)
  have h3 := (CFSG.Timmesfeld.ClassicalOrders.card_quadMinus (K := K) m hirr).1
  rw [← h2, h1] at h3
  push_cast at h3
  linarith

theorem not_dvd_card_nonzero_singular_qMinus {m p : ℕ} {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hmo : Odd m) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) :
    ¬ p ∣ Nat.card
      {v : LargeEvenMinusIdx m → K // v ≠ 0 ∧ TableBOrth.qMinusForm K m b c v = 0} := by
  intro hdvd
  have h := card_nonzero_singular_qMinus m hirr
  have hq : (Nat.card K : ZMod p) = -1 := by
    have h1 : ((Nat.card K + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpq
    push_cast at h1
    exact eq_neg_of_add_eq_zero_left h1
  have h0 : ((Nat.card {v : LargeEvenMinusIdx m → K // v ≠ 0 ∧
      TableBOrth.qMinusForm K m b c v = 0} : ℤ) : ZMod p) = 0 := by
    rw [Int.cast_natCast]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
  rw [h] at h0
  push_cast at h0
  rw [hq, hmo.add_one.neg_one_pow, hmo.neg_one_pow] at h0
  have h4 : ((4 : ℕ) : ZMod p) = 0 := by
    have e : ((4 : ℕ) : ZMod p) = -((1 + 1) * (-1 - 1)) := by push_cast; ring
    rw [e, h0, neg_zero]
  have h4' : p ∣ 2 ^ 2 := (ZMod.natCast_eq_zero_iff _ _).mp h4
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h4'))

end Count

end OrthRestEnd

theorem ggOrthRestMinusRankInput_holds : GGOrthRestMinusRankInput := by
  intro K _ _ n m p b c hK _ hmo hp hpn hbc E hE
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · have h1 : 1 < Nat.card K := Finite.one_lt_card
      rw [hK, h0, pow_zero] at h1
      omega
    · exact h0
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hn hK
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h1 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    omega
  have : Fact p.Prime := ⟨hp⟩
  have hsc := TableBOrth.scalars_subgroupOf_omegaMinus_eq_bot (K := K) (m := m) b c
  set f : OrthRest.RMinus K m b c →* GL (LargeEvenMinusIdx m) K :=
    (LargeEvenOmega (LargeEvenQMinus m b c)).subtype.comp
      (TableBOrth.projMkEquiv hsc).symm.toMonoidHom with hf
  have hfi : Function.Injective f :=
    (LargeEvenOmega _).subtype_injective.comp (TableBOrth.projMkEquiv hsc).symm.injective
  have hiso : ∀ g ∈ E.map f, ∀ v, TableBOrth.qMinusForm K m b c ((g : Matrix _ _ K) *ᵥ v) =
      TableBOrth.qMinusForm K m b c v := by
    rintro _ ⟨r, -, rfl⟩ v
    rw [TableBOrth.coe_qMinusForm]
    exact TableBOrth.isometry_of_mem_orthGroup
      (TableBOrth.omega_le_orth _ ((TableBOrth.projMkEquiv hsc).symm r).2) v
  have hcomm : ∀ g ∈ E.map f, ∀ h ∈ E.map f, g * h = h * g := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩
    rw [← map_mul, ← map_mul, TableB.IsElemAbelian.comm hE ha ha']
  have hexp : ∀ g ∈ E.map f, g ^ p = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hE.2 a ha, map_one]
  have hpg : IsPGroup p (E.map f) := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hexp g g.2)⟩
  have hpq : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
  obtain ⟨v, hv0, -, hvfix⟩ := OrthRestEnd.exists_fixed_singular (TableBOrth.qMinusForm K m b c)
    (E.map f) hpg hiso (OrthRestEnd.not_dvd_card_nonzero_singular_qMinus hbc hmo hp hp2 hpq)
  have h := OrthRestEnd.card_le_of_isometry_fixed (TableBOrth.qMinusForm K m b c)
    (TableBOrth.nondegenerate_qMinusForm m hbc) hp hp2 (E.map f) hiso hcomm hexp hv0 hvfix
  have hc : Fintype.card (LargeEvenMinusIdx m) / 2 - 1 = m := by
    simp only [LargeEvenMinusIdx, Fintype.card_sum, Fintype.card_fin]
    omega
  rwa [hc, Subgroup.card_map_of_injective hfi] at h

end CFSG.StandardType
