module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.EmptyFaithful.T1515C7Grp

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

namespace V2InQ

section Conj

variable {V : Type} [CommGroup V] [Finite V] {A Tb : Subgroup (MulAut V)} {t τ x y z : MulAut V}

theorem exists_conj_mul_of_not_mem_Z (h : SevenCtx A Tb t) (g : SevenGen A Tb τ x y z)
    {u : MulAut V} (hu : u ∈ oTwoUpper A) (huZ : u ∉ frattiniIn (oTwoUpper A)) :
    ∃ q ∈ oTwoUpper A, q * u * q⁻¹ = z * u := by
  have hz3 : z ^ 3 = 1 := SevenGen.z3 h g
  have hz1 : z ≠ 1 := g.z1
  obtain ⟨p, hp, hpu⟩ : ∃ p ∈ oTwoUpper A, p * u ≠ u * p := by
    by_contra hall
    push Not at hall
    exact huZ ((h.mem_Z_iff).2 ⟨hu, hall⟩)
  set c := p * u * p⁻¹ * u⁻¹ with hc
  have hcZ : c ∈ frattiniIn (oTwoUpper A) := h.comm_mem_Z hp hu
  obtain ⟨j, hj⟩ := SevenGen.Z_pow h g hcZ
  have hcne : c ≠ 1 := by
    intro h1
    apply hpu
    have : p * u * p⁻¹ = u := by
      calc p * u * p⁻¹ = (p * u * p⁻¹ * u⁻¹) * u := by group
        _ = u := by rw [← hc, h1, one_mul]
    calc p * u = (p * u * p⁻¹) * p := by group
      _ = u * p := by rw [this]
  have hpu' : p * u * p⁻¹ = c * u := by rw [hc]; group
  have hcp : p * c = c * p := h.Z_central hcZ hp
  have hj3 : j % 3 = 1 ∨ j % 3 = 2 := by
    by_contra hcon
    have h0 : j % 3 = 0 := by omega
    apply hcne
    rw [hj, ← Nat.div_add_mod j 3, h0, add_zero, pow_mul, hz3, one_pow]
  have hzj : z ^ j = z ^ (j % 3) := by
    conv_lhs => rw [← Nat.div_add_mod j 3, pow_add, pow_mul, hz3, one_pow, one_mul]
  rcases hj3 with h1 | h2
  · refine ⟨p, hp, ?_⟩
    rw [hpu', hj, hzj, h1, pow_one]
  · refine ⟨p ^ 2, (oTwoUpper A).pow_mem hp 2, ?_⟩
    have hc2 : c = z ^ 2 := by rw [hj, hzj, h2]
    have hcc : c * c = z := by
      rw [hc2, ← pow_add]
      have : z ^ (2 + 2) = z ^ 3 * z := by rw [← pow_succ]
      rw [this, hz3, one_mul]
    calc p ^ 2 * u * (p ^ 2)⁻¹ = p * (p * u * p⁻¹) * p⁻¹ := by rw [pow_two]; group
      _ = p * (c * u) * p⁻¹ := by rw [hpu']
      _ = (p * c * p⁻¹) * (p * u * p⁻¹) := by group
      _ = c * (c * u) := by rw [hcp, mul_inv_cancel_right, hpu']
      _ = (c * c) * u := by group
      _ = z * u := by rw [hcc]

end Conj

section Ebar

variable {V : Type*} [Group V]

@[expose] def Ebar (z y : MulAut V) (hz3 : z ^ 3 = 1) (hy3 : y ^ 3 = 1) (hzy : z * y = y * z) :
    Subgroup (MulAut V) where
  carrier := {g | ∃ i j : ℕ, g = z ^ i * y ^ j}
  one_mem' := ⟨0, 0, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨i, j, rfl⟩ ⟨i', j', rfl⟩
    refine ⟨i + i', j + j', ?_⟩
    have hc : Commute (y ^ j) (z ^ i') :=
      Commute.pow_pow (show Commute y z from hzy.symm) j i'
    rw [pow_add, pow_add]
    calc z ^ i * y ^ j * (z ^ i' * y ^ j') = z ^ i * (y ^ j * z ^ i') * y ^ j' := by group
      _ = z ^ i * (z ^ i' * y ^ j) * y ^ j' := by rw [hc.eq]
      _ = z ^ i * z ^ i' * (y ^ j * y ^ j') := by group
  inv_mem' := by
    rintro _ ⟨i, j, rfl⟩
    refine ⟨2 * i, 2 * j, ?_⟩
    have hzi : (z ^ i)⁻¹ = z ^ (2 * i) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_add]
      have : i + 2 * i = 3 * i := by ring
      rw [this, pow_mul, hz3, one_pow]
    have hyj : (y ^ j)⁻¹ = y ^ (2 * j) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_add]
      have : j + 2 * j = 3 * j := by ring
      rw [this, pow_mul, hy3, one_pow]
    rw [mul_inv_rev, hyj, hzi]
    exact (Commute.pow_pow (show Commute y z from hzy.symm) (2 * j) (2 * i)).eq

variable {z y : MulAut V} {hz3 : z ^ 3 = 1} {hy3 : y ^ 3 = 1} {hzy : z * y = y * z}

theorem y_mem_Ebar : y ∈ Ebar z y hz3 hy3 hzy := ⟨0, 1, by simp⟩

theorem Ebar_cube {g : MulAut V} (hg : g ∈ Ebar z y hz3 hy3 hzy) : g ^ 3 = 1 := by
  obtain ⟨i, j, rfl⟩ := hg
  have hc : Commute (z ^ i) (y ^ j) := Commute.pow_pow (show Commute z y from hzy) i j
  rw [hc.mul_pow, ← pow_mul, ← pow_mul, mul_comm i 3, mul_comm j 3, pow_mul, pow_mul, hz3, hy3]
  simp

theorem Ebar_comm_y {g : MulAut V} (hg : g ∈ Ebar z y hz3 hy3 hzy) : g * y = y * g := by
  obtain ⟨i, j, rfl⟩ := hg
  have h1 : Commute (z ^ i) y := Commute.pow_left (show Commute z y from hzy) i
  have h2 : Commute (y ^ j) y := Commute.pow_left (Commute.refl y) j
  exact (h1.mul_left h2).eq

theorem Ebar_le {P : Subgroup (MulAut V)} (hz : z ∈ P) (hy : y ∈ P) :
    Ebar z y hz3 hy3 hzy ≤ P := by
  rintro _ ⟨i, j, rfl⟩
  exact P.mul_mem (P.pow_mem hz i) (P.pow_mem hy j)

theorem exists_not_dvd_of_ne_one {g : MulAut V} (hg : g ∈ Ebar z y hz3 hy3 hzy) (h1 : g ≠ 1) :
    ∃ a b : ℕ, g = z ^ a * y ^ b ∧ ¬ (3 ∣ a ∧ 3 ∣ b) := by
  obtain ⟨i, j, rfl⟩ := hg
  refine ⟨i, j, rfl, fun ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ => h1 ?_⟩
  rw [ha, hb, pow_mul, pow_mul, hz3, hy3]
  simp

end Ebar

end V2InQ

end CFSG.Quasithin
