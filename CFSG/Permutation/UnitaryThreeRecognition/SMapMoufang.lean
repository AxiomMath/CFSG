module

public import CFSG.Permutation.UnitaryThreeRecognition.SMap

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω]

namespace IsRootSubgroup

variable {Q : Subgroup G} {a : Ω} (hQ : IsRootSubgroup Q a)
variable {b : Ω} (hb : b ≠ a) {s : G} (hsa : s • a = b) (hs2 : s * s = 1)
include hQ hb hsa hs2

theorem sFactors_conj {u : G} (hu : u ∈ Q) (hu1 : u ≠ 1) {t : G} (ht : t ∈ pairStab G a b) :
    sLeft Q a b s (t * u * t⁻¹) = (s * t * s) * sLeft Q a b s u * (s * t * s)⁻¹ ∧
      sTor Q a b s (t * u * t⁻¹) = (s * t * s) * sTor Q a b s u * t⁻¹ ∧
      sRight Q a b s (t * u * t⁻¹) = (s * t * s) * sRight Q a b s u * (s * t * s)⁻¹ := by
  have hsb := swap_smul_b hsa hs2
  have hs : s⁻¹ = s := by rw [inv_eq_iff_mul_eq_one, hs2]
  have hσ : s * t * s ∈ pairStab G a b := by
    have := conj_mem_pairStab hsa hsb ht
    rwa [hs] at this
  have e := hQ.conj_eq_bruhat hb hsa hs2 hu hu1
  set σt := s * t * s with hσdef
  set x := sLeft Q a b s u
  set h := sTor Q a b s u
  set y := sRight Q a b s u
  have hx : x ∈ Q := hQ.sLeft_mem hb hsa hs2 hu hu1
  have hh : h ∈ pairStab G a b := hQ.sTor_mem hb hsa hs2 hu hu1
  have hy : y ∈ Q := hQ.sRight_mem hb hsa hs2 hu hu1
  have hσinv : σt⁻¹ = s * t⁻¹ * s := by rw [hσdef, mul_inv_rev, mul_inv_rev, hs, mul_assoc]
  have hst : s * σt⁻¹ = t⁻¹ * s := by
    rw [hσinv, ← mul_assoc, ← mul_assoc, hs2, one_mul]
  apply hQ.sFactors_eq hb hsa hs2 (hQ.normal σt hσ.1 x hx)
    ((pairStab G a b).mul_mem ((pairStab G a b).mul_mem hσ hh) ((pairStab G a b).inv_mem ht))
    (hQ.normal σt hσ.1 y hy)
  calc s * (t * u * t⁻¹) * s = σt * (s * u * s) * σt⁻¹ := by
        rw [hσinv, hσdef]
        calc s * (t * u * t⁻¹) * s = s * t * (s * s) * u * (s * s) * t⁻¹ * s := by
              rw [hs2]; group
          _ = s * t * s * (s * u * s) * (s * t⁻¹ * s) := by group
    _ = σt * x * h * (s * σt⁻¹) * (σt * y * σt⁻¹) := by rw [e]; group
    _ = σt * x * σt⁻¹ * (σt * h * t⁻¹) * s * (σt * y * σt⁻¹) := by rw [hst]; group

theorem sRight_ne_one {u : G} (hu : u ∈ Q) (hu1 : u ≠ 1) : sRight Q a b s u ≠ 1 := by
  have hsb := swap_smul_b hsa hs2
  intro hy1
  have e := hQ.conj_eq_bruhat hb hsa hs2 hu hu1
  have h1 : (s * u * s) • b = b := by rw [mul_smul, mul_smul, hsb, hQ.smul_self hu, hsa]
  rw [e, hy1, mul_one, mul_smul, hsb, mul_smul, (hQ.sTor_mem hb hsa hs2 hu hu1).1,
    hQ.smul_self (hQ.sLeft_mem hb hsa hs2 hu hu1)] at h1
  exact hb h1.symm

theorem bruhat_smul {x h y v : G} (hh : h ∈ pairStab G a b) (hyv : y * v ∈ Q)
    (hyv1 : y * v ≠ 1) :
    (x * h * s * y) • (v • b) =
      (x * (h * sLeft Q a b s (y * v) * h⁻¹)) • b := by
  have hhb : h⁻¹ • b = b := by rw [inv_smul_eq_iff, hh.2]
  calc (x * h * s * y) • (v • b) = x • (h • (s • ((y * v) • b))) := by simp only [mul_smul]
    _ = x • (h • (sLeft Q a b s (y * v) • b)) := by
        rw [hQ.smul_sLeft hb hsa hs2 hyv hyv1]
    _ = (x * (h * sLeft Q a b s (y * v) * h⁻¹)) • b := by simp only [mul_smul, hhb]

theorem sTor_conj_sLeft_sRight {u : G} (hu : u ∈ Q) (hu1 : u ≠ 1) :
    sTor Q a b s u * sLeft Q a b s (sRight Q a b s u) * (sTor Q a b s u)⁻¹ =
      (sLeft Q a b s u)⁻¹ := by
  have hsb := swap_smul_b hsa hs2
  have e := hQ.conj_eq_bruhat hb hsa hs2 hu hu1
  set x := sLeft Q a b s u
  set h := sTor Q a b s u
  set y := sRight Q a b s u
  have hx : x ∈ Q := hQ.sLeft_mem hb hsa hs2 hu hu1
  have hh : h ∈ pairStab G a b := hQ.sTor_mem hb hsa hs2 hu hu1
  have hy : y ∈ Q := hQ.sRight_mem hb hsa hs2 hu hu1
  have hy1 : y ≠ 1 := hQ.sRight_ne_one hb hsa hs2 hu hu1
  have hmem : h * sLeft Q a b s y * h⁻¹ ∈ Q :=
    hQ.normal h hh.1 _ (hQ.sLeft_mem hb hsa hs2 hy hy1)
  have h1 : (s * u * s) • ((1 : G) • b) = b := by
    rw [one_smul, mul_smul, mul_smul, hsb, hQ.smul_self hu, hsa]
  rw [e, hQ.bruhat_smul hb hsa hs2 hh (by rw [mul_one]; exact hy) (by rw [mul_one]; exact hy1),
    mul_one] at h1
  have h2 := hQ.eq_one_of_smul_eq (Q.mul_mem hx hmem) hb h1
  exact eq_inv_of_mul_eq_one_right h2

theorem sLeft_mul_sLeft {u v : G} (hu : u ∈ Q) (hu1 : u ≠ 1) (hv : v ∈ Q) (hv1 : v ≠ 1)
    (huv : u * sLeft Q a b s v ≠ 1) (hyv : sRight Q a b s u * v ≠ 1) :
    sLeft Q a b s (u * sLeft Q a b s v) =
      sLeft Q a b s u * (sTor Q a b s u * sLeft Q a b s (sRight Q a b s u * v) *
        (sTor Q a b s u)⁻¹) := by
  have e := hQ.conj_eq_bruhat hb hsa hs2 hu hu1
  set x := sLeft Q a b s u
  set h := sTor Q a b s u
  set y := sRight Q a b s u
  have hx : x ∈ Q := hQ.sLeft_mem hb hsa hs2 hu hu1
  have hh : h ∈ pairStab G a b := hQ.sTor_mem hb hsa hs2 hu hu1
  have hy : y ∈ Q := hQ.sRight_mem hb hsa hs2 hu hu1
  have hyvQ : y * v ∈ Q := Q.mul_mem hy hv
  have hmem : h * sLeft Q a b s (y * v) * h⁻¹ ∈ Q :=
    hQ.normal h hh.1 _ (hQ.sLeft_mem hb hsa hs2 hyvQ hyv)
  have hw : u * sLeft Q a b s v ∈ Q := Q.mul_mem hu (hQ.sLeft_mem hb hsa hs2 hv hv1)
  rw [hQ.sLeft_eq_iff hb hsa hs2 hw huv (Q.mul_mem hx hmem)]
  calc s • ((u * sLeft Q a b s v) • b) = s • (u • (sLeft Q a b s v • b)) := by rw [mul_smul]
    _ = (s * u * s) • (v • b) := by
        rw [← hQ.smul_sLeft hb hsa hs2 hv hv1, mul_smul, mul_smul]
    _ = (x * (h * sLeft Q a b s (y * v) * h⁻¹)) • b := by
        rw [e, hQ.bruhat_smul hb hsa hs2 hh hyvQ hyv]

end IsRootSubgroup

end CFSG.UnitaryThreeRecognition
