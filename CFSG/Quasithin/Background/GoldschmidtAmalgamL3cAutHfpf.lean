module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cAutComm
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cHfpf

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL3
  CFSG.Quasithin.F6.GoldAmL2T

namespace F6

namespace GoldAmL3c

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

section NB

variable [Finite D] {x a a₁ a₂ : D} {N : Subgroup D} (g : Gen3 A B z V x a a₁ a₂)
  (d : NData B V x N)

include g d

theorem NData.hfpf (hU : Nat.card (conjClosure V B) = 8) {q₀ : ↥(pCoreOf 2 B)}
    (hq₀N : (q₀ : D) ∈ N) (h₀ : psi g q₀ = (zel z, zel z)) {B' T' : Subgroup D}
    (hv : Vertex B' T') (hN : pCoreOf 2 B' = N) (hxB' : x ∈ B') (hxT : x ∉ T') :
    ∀ y ∈ B', y ≠ 1 → y ^ 3 = 1 → ∀ q ∈ N, y * q * y⁻¹ = q →
      ∀ v ∈ N, q * v = v * q := by
  intro y hyB hy1 hy3 q hq hyq v hv'
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hy3' : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hyT : y ∉ T' := hv.not_mem_of_orderOf hy3'
  have hyQ : y ∉ N := fun h => hyT (hv.pCoreOf_le (hN ▸ h))
  have hxQ : x ∉ N := fun h => hxT (hv.pCoreOf_le (hN ▸ h))
  obtain ⟨π, -, hπk⟩ := hv.exists_hom
  have hπk' : ∀ w : ↥B', π w = 1 ↔ (w : D) ∈ N := fun w => by rw [hπk w, hN]
  have hpy3 : (π ⟨y, hyB⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨y, hyB⟩ : ↥B') ^ 3 = 1 := Subtype.ext (by simpa using hy3)
    rw [this, map_one]
  have hpx3 : (π ⟨x, hxB'⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨x, hxB'⟩ : ↥B') ^ 3 = 1 := Subtype.ext (by simpa [pow_three'] using g.x_cube)
    rw [this, map_one]
  have hpy1 : π ⟨y, hyB⟩ ≠ 1 := fun h => hyQ ((hπk' _).mp h)
  have hpx1 : π ⟨x, hxB'⟩ ≠ 1 := fun h => hxQ ((hπk' _).mp h)
  have hvB : v ∈ B := pCoreOf_le 2 B (d.le_QB hv')
  have hxinvB' : x⁻¹ ∈ B' := B'.inv_mem hxB'
  have hq' : ∀ {c : D} (hcB : c ∈ B'), π ⟨c, hcB⟩ = 1 → c ∈ N := fun {c} hcB h =>
    (hπk' ⟨c, hcB⟩).mp h
  suffices hqz : q ∈ Subgroup.zpowers z from (zpowers_comm_B g.hyp hvB hqz).symm
  rcases perm_three_order_three_cases _ _ hpy1 hpy3 hpx1 hpx3 with e | e
  ·
    have hq'Q : y * x⁻¹ ∈ N := by
      refine hq' (B'.mul_mem hyB hxinvB') ?_
      have : (⟨y * x⁻¹, B'.mul_mem hyB hxinvB'⟩ : ↥B') = ⟨y, hyB⟩ * ⟨x, hxB'⟩⁻¹ := rfl
      rw [this, map_mul, map_inv, e]; simp
    have hcomm := d.comm_mem g hU hq₀N h₀ (N.inv_mem hq'Q) hq
    have hxq : x * q * x⁻¹ * q⁻¹ ∈ Subgroup.zpowers z := by
      have e1 : (y * x⁻¹) * (x * q * x⁻¹) * (y * x⁻¹)⁻¹ = q := by
        calc (y * x⁻¹) * (x * q * x⁻¹) * (y * x⁻¹)⁻¹ = y * q * y⁻¹ := by group
          _ = q := hyq
      have e2 : x * q * x⁻¹ = (y * x⁻¹)⁻¹ * q * (y * x⁻¹) := by
        calc x * q * x⁻¹ = (y * x⁻¹)⁻¹ * ((y * x⁻¹) * (x * q * x⁻¹) * (y * x⁻¹)⁻¹) *
            (y * x⁻¹) := by group
          _ = (y * x⁻¹)⁻¹ * q * (y * x⁻¹) := by rw [e1]
      rw [e2]
      have e3 : (y * x⁻¹)⁻¹ * q * (y * x⁻¹) * q⁻¹ = (y * x⁻¹)⁻¹ * q * ((y * x⁻¹)⁻¹)⁻¹ * q⁻¹ := by
        rw [inv_inv]
      rw [e3]; exact hcomm
    have hfix := conj_eq_of_cube g.hyp g.x_mem g.x_cube hxq
    exact d.fixed_mem_zpowers g hU hq hfix
  ·
    have hq'Q : y * x ∈ N := by
      refine hq' (B'.mul_mem hyB hxB') ?_
      have : (⟨y * x, B'.mul_mem hyB hxB'⟩ : ↥B') = ⟨y, hyB⟩ * ⟨x, hxB'⟩ := rfl
      rw [this, map_mul, e]
      have : (π ⟨x, hxB'⟩)⁻¹ * π ⟨x, hxB'⟩ = 1 := inv_mul_cancel _
      exact this
    have hcomm := d.comm_mem g hU hq₀N h₀ (N.inv_mem hq'Q) hq
    have hxq : x⁻¹ * q * x⁻¹⁻¹ * q⁻¹ ∈ Subgroup.zpowers z := by
      have e1 : (y * x) * (x⁻¹ * q * x⁻¹⁻¹) * (y * x)⁻¹ = q := by
        calc (y * x) * (x⁻¹ * q * x⁻¹⁻¹) * (y * x)⁻¹ = y * q * y⁻¹ := by group
          _ = q := hyq
      have e2 : x⁻¹ * q * x⁻¹⁻¹ = (y * x)⁻¹ * q * (y * x) := by
        calc x⁻¹ * q * x⁻¹⁻¹ = (y * x)⁻¹ * ((y * x) * (x⁻¹ * q * x⁻¹⁻¹) * (y * x)⁻¹) *
            (y * x) := by group
          _ = (y * x)⁻¹ * q * (y * x) := by rw [e1]
      rw [e2]
      have e3 : (y * x)⁻¹ * q * (y * x) * q⁻¹ = (y * x)⁻¹ * q * ((y * x)⁻¹)⁻¹ * q⁻¹ := by
        rw [inv_inv]
      rw [e3]; exact hcomm
    have hx3' : x⁻¹ * x⁻¹ * x⁻¹ = 1 := by
      calc x⁻¹ * x⁻¹ * x⁻¹ = (x * x * x)⁻¹ := by group
        _ = 1 := by rw [g.x_cube]; simp
    have hfix' := conj_eq_of_cube g.hyp (B.inv_mem g.x_mem) hx3' hxq
    have hfix : x * q * x⁻¹ = q := by
      have : x * (x⁻¹ * q * x⁻¹⁻¹) * x⁻¹ = x * q * x⁻¹ := by
        rw [hfix']
      calc x * q * x⁻¹ = x * (x⁻¹ * q * x⁻¹⁻¹) * x⁻¹ := this.symm
        _ = q := by group
    exact d.fixed_mem_zpowers g hU hq hfix

end NB

end GoldAmL3c

end F6

end CFSG.Quasithin
