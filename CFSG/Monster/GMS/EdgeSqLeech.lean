module

public import CFSG.Monster.GMS.Leech.Data
public import CFSG.Monster.GMS.EdgeSqFact

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Co1.Module (bil₀)
open scoped commutatorElement

namespace LeechSystem

variable {G : Type*} [Group G] {z : G} (L : LeechSystem z)

include L

theorem bil₀_sq_eq_zero_of_fixed
    {g : G} (hg : g ∈ Subgroup.centralizer ({z} : Set G))
    (hcQ : g * g ∈ leechQ z) {x : Fin 24 → ZMod 2}
    (hx : CFSG.Monster.GMS.co1Act (L.φ ⟨g, hg⟩) x = x) : bil₀ (L.vec (g * g)) x = 0 := by
  obtain ⟨p, hpQ, rfl⟩ := L.vec_surj x
  have hgz : g * z = z * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  have hv : L.vec (g * p * g⁻¹) = L.vec p := by
    rw [L.vec_conj ⟨g, hg⟩ p hpQ]
    exact hx
  have hgpQ : g * p * g⁻¹ ∈ leechQ z := L.conj_mem' hg hpQ
  have hgzg : g * z * g⁻¹ = z := by
    rw [hgz]
    group
  have hcp : (g * g) * p * (g * g)⁻¹ = p := by
    rcases L.eq_or_eq_mul_z hgpQ hpQ hv with h | h
    · calc (g * g) * p * (g * g)⁻¹ = g * (g * p * g⁻¹) * g⁻¹ := by group
        _ = p := by rw [h, h]
    · have hzz : z * z = 1 := L.z_mul_self
      calc (g * g) * p * (g * g)⁻¹ = g * (g * p * g⁻¹) * g⁻¹ := by group
        _ = g * (p * z) * g⁻¹ := by rw [h]
        _ = (g * p * g⁻¹) * (g * z * g⁻¹) := by group
        _ = p * z * z := by rw [h, hgzg]
        _ = p := by rw [mul_assoc, hzz, mul_one]
  have hcomm : ⁅g * g, p⁆ = 1 := by
    rw [commutatorElement_def, hcp]
    group
  exact (L.comm_eq_one_iff hcQ hpQ).1 hcomm

theorem false_of_edge_square
    (hfact : Co1EdgeFact) {g w : G}
    (hg : g ∈ Subgroup.centralizer ({z} : Set G)) (hc : g * g ∈ L.typeSet 0)
    (hw : w ∈ L.typeSet 0) (hcw : g * g * w ∈ L.typeSet 0) (hgw : g * w = w * g) : False := by
  have hcQ : g * g ∈ leechQ z := hc.1
  have hwQ : w ∈ leechQ z := hw.1
  have hgz : g * z = z * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  have hgzg : g * z * g⁻¹ = z := by
    rw [hgz]
    group
  have hzz : z * z = 1 := L.z_mul_self
  set s : Co1 := L.φ ⟨g, hg⟩ with hs
  have hss : s * s = 1 := by
    have h1 : L.φ (⟨g, hg⟩ * ⟨g, hg⟩) = 1 := (L.φ_ker _).2 hcQ
    rwa [map_mul] at h1
  have hs1 : s ≠ 1 := by
    intro h1
    have hgQ : g ∈ leechQ z := (L.φ_ker ⟨g, hg⟩).1 h1
    rcases L.extraspecial.sq g hgQ with h | h
    · exact L.ne_one_of_mem_typeSet hc h
    · exact L.ne_z_of_mem_typeSet hc h
  have hs2 : orderOf s = 2 := orderOf_eq_prime (by rw [pow_two]; exact hss) hs1
  have hfixc : co1Act s (L.vec (g * g)) = L.vec (g * g) := by
    have h := L.vec_conj ⟨g, hg⟩ (g * g) hcQ
    have e : g * (g * g) * g⁻¹ = g * g := by group
    simp only [e] at h
    exact h.symm
  have hfixw : co1Act s (L.vec w) = L.vec w := by
    have h := L.vec_conj ⟨g, hg⟩ w hwQ
    have e : g * w * g⁻¹ = w := by rw [hgw]; group
    simp only [e] at h
    exact h.symm
  have hsum : L.vec (g * g) + L.vec w ∈ co1Orbit 0 := by
    rw [← L.vec_mul _ hcQ w hwQ]
    exact hcw.2
  obtain ⟨y, hy1, hy2⟩ := hfact s hs2 (L.vec (g * g)) (L.vec w) hc.2 hw.2 hsum hfixc hfixw
    (fun x hx => L.bil₀_sq_eq_zero_of_fixed hg hcQ hx)
  obtain ⟨p, hpQ, rfl⟩ := L.vec_surj y
  set q : G := p * (g * p⁻¹ * g⁻¹) with hq
  have hqQ : q ∈ leechQ z := mul_mem hpQ (L.conj_mem' hg (inv_mem hpQ))
  have hvq : L.vec q = L.vec w := by
    rw [hq, L.vec_mul p hpQ _ (L.conj_mem' hg (inv_mem hpQ)), L.vec_conj' hg (inv_mem hpQ),
      L.vec_inv hpQ, ← hy1]
  have hgq : g * q * g⁻¹ = q := by
    rcases L.eq_or_eq_mul_z hqQ hwQ hvq with h | h
    · rw [h, hgw]
      group
    · rw [h]
      calc g * (w * z) * g⁻¹ = (g * w * g⁻¹) * (g * z * g⁻¹) := by group
        _ = w * z := by rw [hgzg, show g * w * g⁻¹ = w by rw [hgw]; group]
  have hqq : q * q = 1 := by
    have hww : w * w = 1 := L.mul_self_of_mem_typeSet_zero hw
    have hwz : w * z = z * w := L.extraspecial.central w hwQ
    rcases L.eq_or_eq_mul_z hqQ hwQ hvq with h | h
    · rw [h]
      exact hww
    · rw [h]
      calc w * z * (w * z) = w * (z * w) * z := by group
        _ = w * (w * z) * z := by rw [← hwz]
        _ = (w * w) * (z * z) := by group
        _ = 1 := by rw [hww, hzz, mul_one]
  have hid : q * (g * q * g⁻¹) = ⁅p, g * g⁆ := by
    rw [hq, commutatorElement_def]
    group
  rw [hgq, hqq] at hid
  have hpc : bil₀ (L.vec p) (L.vec (g * g)) = 0 := (L.comm_eq_one_iff hpQ hcQ).1 hid.symm
  rw [CFSG.Sporadic.Co1.Module.bil₀_comm] at hpc
  rw [hpc] at hy2
  exact absurd hy2 (by decide)

end LeechSystem

end CFSG.Monster.GMS
