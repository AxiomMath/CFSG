module

public import CFSG.Permutation.UnitaryThreeRecognition.Fixed
public import CFSG.Permutation.UnitaryThreeRecognition.SMap

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω]

namespace IsRootSubgroup

variable {Q : Subgroup G} {a : Ω} (hQ : IsRootSubgroup Q a)
variable {b : Ω} (hb : b ≠ a) {s : G} (hsa : s • a = b) (hs2 : s * s = 1)
include hQ hb hsa hs2

omit hQ hb in
theorem swap_commute_involution {j : G} (hj : j ∈ pairStab G a b) (hj2 : j * j = 1)
    (hj1 : j ≠ 1) (hsq : ∀ t ∈ pairStab G a b, t * t = 1 → t = 1 ∨ t = j) :
    s * j = j * s := by
  have hsb := swap_smul_b hsa hs2
  have hmem : s * j * s⁻¹ ∈ pairStab G a b := conj_mem_pairStab hsa hsb hj
  have hsq' : s * j * s⁻¹ * (s * j * s⁻¹) = 1 := by
    calc s * j * s⁻¹ * (s * j * s⁻¹) = s * (j * j) * s⁻¹ := by group
      _ = 1 := by rw [hj2]; group
  rcases hsq _ hmem hsq' with h | h
  · exfalso; apply hj1
    have := congrArg (fun z => s⁻¹ * z * s) h
    simpa [mul_assoc] using this
  · calc s * j = s * j * s⁻¹ * s := by group
      _ = j * s := by rw [h]

theorem sLeft_mem_centQ {j : G} (hj : j ∈ pairStab G a b) (hsj : s * j = j * s) {z : G}
    (hz : z ∈ centQ Q j) (hz1 : z ≠ 1) : sLeft Q a b s z ∈ centQ Q j := by
  obtain ⟨hzQ, hzj⟩ := mem_centQ.mp hz
  have hx := hQ.sLeft_mem hb hsa hs2 hzQ hz1
  refine mem_centQ.mpr ⟨hx, (hQ.fixes_iff hb hj hx).mp ?_⟩
  rw [← hQ.smul_sLeft hb hsa hs2 hzQ hz1, smul_smul, ← hsj, mul_smul,
    (hQ.fixes_iff hb hj hzQ).mpr hzj]

theorem sRight_mem_centQ {j : G} (hj : j ∈ pairStab G a b) (hsj : s * j = j * s) {z : G}
    (hz : z ∈ centQ Q j) (hz1 : z ≠ 1) : sRight Q a b s z ∈ centQ Q j := by
  have hzQ := (mem_centQ.mp hz).1
  have hzi : z⁻¹ ∈ centQ Q j := (centQ Q j).inv_mem hz
  have hzi1 : z⁻¹ ≠ 1 := inv_ne_one.mpr hz1
  have h1 := (hQ.sFactors_inv hb hsa hs2 (Q.inv_mem hzQ) hzi1).2.2
  rw [inv_inv] at h1
  rw [h1]
  exact (centQ Q j).inv_mem (hQ.sLeft_mem_centQ hb hsa hs2 hj hsj hzi hzi1)

end IsRootSubgroup

end CFSG.UnitaryThreeRecognition
