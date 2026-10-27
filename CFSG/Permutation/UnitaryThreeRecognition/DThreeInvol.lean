module

public import CFSG.Permutation.UnitaryThreeRecognition.StdHyp
public import CFSG.Permutation.UnitaryThreeRecognition.SMapMoufang

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω]

namespace IsRootSubgroup

variable {Q : Subgroup G} {a : Ω} (hQ : IsRootSubgroup Q a)
variable {b : Ω} (hb : b ≠ a) {s : G} (hsa : s • a = b) (hs2 : s * s = 1)
include hQ hb hsa hs2

theorem sTor_sRight_of_sLeft_eq {j : G} (hj : j ∈ pairStab G a b) (hj2 : j * j = 1)
    (hj1 : j ≠ 1) (hsq : ∀ t ∈ pairStab G a b, t * t = 1 → t = 1 ∨ t = j)
    (hQ2 : ∀ y ∈ Q, y * y = 1 → y = 1) {u : G} (hu : u ∈ Q) (hu1 : u ≠ 1)
    (hfix : sLeft Q a b s u = u) :
    sTor Q a b s u = j ∧ j * sRight Q a b s u * j = (sRight Q a b s u)⁻¹ := by
  have hsb := swap_smul_b hsa hs2
  have hs : s⁻¹ = s := by rw [inv_eq_iff_mul_eq_one, hs2]
  have hji : j⁻¹ = j := by rw [inv_eq_iff_mul_eq_one, hj2]
  have hsj : s * j = j * s := swap_commute_involution hsa hs2 hj hj2 hj1 hsq
  have e := hQ.conj_eq_bruhat hb hsa hs2 hu hu1
  rw [hfix] at e
  have hTm : sTor Q a b s u ∈ pairStab G a b := hQ.sTor_mem hb hsa hs2 hu hu1
  have hR : sRight Q a b s u ∈ Q := hQ.sRight_mem hb hsa hs2 hu hu1
  have hR1 : sRight Q a b s u ≠ 1 := hQ.sRight_ne_one hb hsa hs2 hu hu1
  generalize sTor Q a b s u = T at *
  generalize sRight Q a b s u = R at *
  have hτ : s * T⁻¹ * s ∈ pairStab G a b := by
    have := conj_mem_pairStab hsa hsb ((pairStab G a b).inv_mem hTm)
    rwa [hs] at this
  have hX : s * u⁻¹ * s * u * s = R⁻¹ * (s * T⁻¹ * s) := by
    have e' : s * u⁻¹ * s = R⁻¹ * s * T⁻¹ * u⁻¹ := by
      calc s * u⁻¹ * s = (s * u * s)⁻¹ := by rw [mul_inv_rev, mul_inv_rev, hs]; group
        _ = (u * T * s * R)⁻¹ := by rw [e]
        _ = R⁻¹ * s * T⁻¹ * u⁻¹ := by rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, hs]; group
    rw [e']; group
  have hw : (u⁻¹ * s * u) * (u⁻¹ * s * u) = 1 := by
    calc (u⁻¹ * s * u) * (u⁻¹ * s * u) = u⁻¹ * (s * s) * u := by group
      _ = 1 := by rw [hs2]; group
  have hX2 : (s * u⁻¹ * s * u * s) * (s * u⁻¹ * s * u * s) = 1 := by
    calc (s * u⁻¹ * s * u * s) * (s * u⁻¹ * s * u * s)
        = s * (u⁻¹ * s * u) * (s * s) * (u⁻¹ * s * u) * s := by group
      _ = s * ((u⁻¹ * s * u) * (u⁻¹ * s * u)) * s := by rw [hs2]; group
      _ = s * s := by rw [hw]; group
      _ = 1 := hs2
  rw [hX] at hX2
  have hx : R⁻¹ * ((s * T⁻¹ * s) * R⁻¹ * (s * T⁻¹ * s)⁻¹) ∈ Q :=
    Q.mul_mem (Q.inv_mem hR) (hQ.normal _ hτ.1 R⁻¹ (Q.inv_mem hR))
  have heq : R⁻¹ * ((s * T⁻¹ * s) * R⁻¹ * (s * T⁻¹ * s)⁻¹) * ((s * T⁻¹ * s) * (s * T⁻¹ * s)) =
      1 * 1 := by
    rw [one_mul, ← hX2]; group
  obtain ⟨hx1, hτ2⟩ := hQ.mul_pairStab_unique hb hx Q.one_mem
    ((pairStab G a b).mul_mem hτ hτ) (pairStab G a b).one_mem heq
  rcases hsq _ hτ hτ2 with hτ1 | hτj
  · exfalso
    apply hR1
    rw [hτ1] at hx1
    have h2 : R⁻¹ * R⁻¹ = 1 := by rw [← hx1]; group
    exact inv_eq_one.mp (hQ2 _ (Q.inv_mem hR) h2)
  · have hT : T⁻¹ = j := by
      calc T⁻¹ = (s * s) * T⁻¹ * (s * s) := by rw [hs2]; group
        _ = s * (s * T⁻¹ * s) * s := by group
        _ = j := by rw [hτj, hsj, mul_assoc, hs2, mul_one]
    refine ⟨by rw [← inv_inv T, hT, hji], ?_⟩
    rw [hτj] at hx1
    have h2 : j * R⁻¹ * j⁻¹ = R := by
      calc j * R⁻¹ * j⁻¹ = R * (R⁻¹ * (j * R⁻¹ * j⁻¹)) := by group
        _ = R := by rw [hx1, mul_one]
    calc j * R * j = j * R * j⁻¹ := by rw [hji]
      _ = (j * R⁻¹ * j⁻¹)⁻¹ := by group
      _ = R⁻¹ := by rw [h2]

theorem exists_sLeft_eq_self {j : G} (hj : j ∈ pairStab G a b) {k : G}
    (hk : s = k⁻¹ * j * k) : ∃ u ∈ Q, u ≠ 1 ∧ sLeft Q a b s u = u := by
  have hsb := swap_smul_b hsa hs2
  have hsw : s • (k⁻¹ • a) = k⁻¹ • a := by
    rw [hk, mul_smul, mul_smul, smul_inv_smul, hj.1]
  have hwa : k⁻¹ • a ≠ a := by
    intro e
    rw [e, hsa] at hsw
    exact hb hsw
  have hwb : k⁻¹ • a ≠ b := by
    intro e
    rw [e, hsb] at hsw
    exact hb hsw.symm
  obtain ⟨u, hu, hub⟩ := hQ.exists_smul_eq hb hwa
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [one_smul] at hub
    exact hwb hub.symm
  refine ⟨u, hu, hu1, ?_⟩
  rw [hQ.sLeft_eq_iff hb hsa hs2 hu hu1 hu, hub]
  exact hsw

end IsRootSubgroup

namespace StdHyp

variable {Q : Subgroup G} {a b : Ω} {j s : G} {p f d : ℕ} (S : StdHyp G Q a b j s p f d)
include S

theorem eq_one_of_mem_of_mul_self {y : G} (hy : y ∈ Q) (hy2 : y * y = 1) : y = 1 := by
  by_contra hne
  have h := Subgroup.orderOf_dvd_natCard Q hy
  rw [orderOf_eq_prime (by rw [sq]; exact hy2) hne, S.hQcard] at h
  exact (Nat.not_even_iff_odd.mpr S.hpodd.pow) (even_iff_two_dvd.mpr h)

theorem sTor_sRight_of_sLeft_eq {u : G} (hu : u ∈ Q) (hu1 : u ≠ 1)
    (hfix : sLeft Q a b s u = u) :
    sTor Q a b s u = j ∧ j * sRight Q a b s u * j = (sRight Q a b s u)⁻¹ :=
  S.root.sTor_sRight_of_sLeft_eq S.hb S.hsa S.hs2 S.hj S.hj2 S.hj1 S.hsq
    (fun _ hy hy2 => S.eq_one_of_mem_of_mul_self hy hy2) hu hu1 hfix

theorem exists_sLeft_eq_self {k : G} (hk : s = k⁻¹ * j * k) :
    ∃ u ∈ Q, u ≠ 1 ∧ sLeft Q a b s u = u :=
  S.root.exists_sLeft_eq_self S.hb S.hsa S.hs2 S.hj hk

end StdHyp

end CFSG.UnitaryThreeRecognition
