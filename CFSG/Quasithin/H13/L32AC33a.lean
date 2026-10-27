module

public import CFSG.Quasithin.H13.A5S136sz0
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem sz_aut_eq_one_of_inv {X : Type} [Group X] [Finite X]
    {e : ℕ} (hX : IsSz e X) {α β γ : MulAut X} (hα3 : α ^ 3 = 1) {k : ℕ}
    (hγ : γ ^ 2 ^ k = 1) (hrel : β * α * β⁻¹ * α = γ) : α = 1 := by
  have hcyc := (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0}
    X 2 e hX).1.1
  have hcomm : ∀ a b : Outer X, a * b = b * a := fun a b => (IsCyclic.commGroup).mul_comm a b
  obtain ⟨g, hg⟩ := H13.A5.ConfSz.exists_conj_of_two_pow hX γ hγ
  have hγ1 : (QuotientGroup.mk γ : Outer X) = 1 := by
    rw [hg]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩
  set a : Outer X := QuotientGroup.mk α with ha
  set b : Outer X := QuotientGroup.mk β with hb
  have h1 : b * a * b⁻¹ * a = 1 := by
    rw [ha, hb, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, hrel, hγ1]
  have h2 : a * a = 1 := by
    calc a * a = b * a * b⁻¹ * a := by
          rw [hcomm b a, mul_assoc a b, mul_inv_cancel, mul_one]
      _ = 1 := h1
  have h3 : a ^ 3 = 1 := by rw [ha, ← QuotientGroup.mk_pow, hα3, QuotientGroup.mk_one]
  have ha1 : a = 1 := by
    calc a = a ^ 3 * (a * a)⁻¹ := by group
      _ = 1 := by rw [h3, h2, inv_one, mul_one]
  obtain ⟨g₀, hg₀⟩ := (QuotientGroup.eq_one_iff α).mp ha1
  have hc3 : g₀ ^ 3 ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro z
    have h4 : MulAut.conj (g₀ ^ 3) z = z := by
      rw [map_pow, hg₀, hα3]
      rfl
    rw [MulAut.conj_apply] at h4
    calc z * g₀ ^ 3 = g₀ ^ 3 * z * (g₀ ^ 3)⁻¹ * g₀ ^ 3 := by rw [h4]
      _ = g₀ ^ 3 * z := by group
  have hcop : Nat.Coprime 3 (orderOf g₀) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h =>
      H13.A5.ConfSz.three_not_dvd_card hX (h.trans (orderOf_dvd_natCard g₀))
  have hg₀c : g₀ ∈ Subgroup.center X :=
    (Subgroup.zpowers_le.mpr hc3) (A4.mem_zpowers_pow_of_coprime hcop)
  rw [← hg₀]
  ext z
  rw [MulAut.conj_apply, MulAut.one_apply, ← Subgroup.mem_center_iff.mp hg₀c z,
    mul_inv_cancel_right]

theorem centralizes_sz_of_inv {Y : Type} [Group Y]
    {N : Subgroup Y} [N.Normal] [Finite N] {e : ℕ} (hN : IsSz e ↥N) {y t : Y} (hy3 : y ^ 3 = 1)
    {k : ℕ} (hk : (t * y * t⁻¹ * y) ^ 2 ^ k = 1) {n : Y} (hn : n ∈ N) : y * n * y⁻¹ = n := by
  have h := sz_aut_eq_one_of_inv hN (α := MulAut.conjNormal y) (β := MulAut.conjNormal t)
    (γ := MulAut.conjNormal (t * y * t⁻¹ * y)) (by rw [← map_pow, hy3, map_one])
    (k := k) (by rw [← map_pow, hk, map_one]) (by simp only [map_mul, map_inv])
  have h1 := congrArg (fun f : MulAut ↥N => ((f ⟨n, hn⟩ : ↥N) : Y)) h
  simpa using h1

end CFSG.Quasithin.H13.L32A.C
