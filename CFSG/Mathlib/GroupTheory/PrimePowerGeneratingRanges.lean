module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Nat.PadicValNat
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.GroupTheory

theorem mem_subgroup_of_primePower_generating_ranges
    {S R : Type*} [CommGroup S] [Group R] {ι : Sort*}
    (d : ι → S →* R) (T H : Subgroup R) (hT : T = ⨆ i, (d i).range)
    (hcomm : ∀ x ∈ T, ∀ y ∈ T, Commute x y)
    {p N : ℕ} (hp : p.Prime) (hN : N ≠ 0) (hexp : ∀ s : S, s ^ N = 1)
    (hgen : ∀ i s, (∃ k : ℕ, s ^ p ^ k = 1) → d i s ∈ H)
    {x : R} (hxT : x ∈ T) (hxp : ∃ k : ℕ, x ^ p ^ k = 1) : x ∈ H := by
  let a := padicValNat p N
  let m := Nat.divMaxPow N p
  have hmN : m * p ^ a = N := Nat.divMaxPow_mul_pow_padicValNat p N
  have hpm : p.Coprime m := hp.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_divMaxPow hp.one_lt hN)
  have hxpow : x ^ m ∈ H := by
    have hx : x ∈ ⨆ i, (d i).range := hT ▸ hxT
    refine (Subgroup.iSup_induction (S := fun i => (d i).range)
      (C := fun y => y ∈ T ∧ y ^ m ∈ H) hx ?_ ?_ ?_).2
    · rintro i y ⟨s, rfl⟩
      have hyT : d i s ∈ T := by
        rw [hT]
        exact Subgroup.mem_iSup_of_mem i ⟨s, rfl⟩
      have hs : (s ^ m) ^ p ^ a = 1 := by
        rw [← pow_mul, hmN]
        exact hexp s
      exact ⟨hyT, by simpa only [map_pow] using hgen i (s ^ m) ⟨a, hs⟩⟩
    · exact ⟨T.one_mem, by simp⟩
    · rintro y z ⟨hyT, hyH⟩ ⟨hzT, hzH⟩
      refine ⟨T.mul_mem hyT hzT, ?_⟩
      rw [(hcomm y hyT z hzT).mul_pow]
      exact H.mul_mem hyH hzH
  obtain ⟨k, hk⟩ := hxp
  have hmorder : m.Coprime (orderOf x) :=
    (hpm.symm.pow_right k).of_dvd_right (orderOf_dvd_of_pow_eq_one hk)
  obtain ⟨r, hr⟩ := exists_pow_eq_self_of_coprime hmorder
  rw [← hr]
  exact H.pow_mem hxpow r

end CFSG.GroupTheory
