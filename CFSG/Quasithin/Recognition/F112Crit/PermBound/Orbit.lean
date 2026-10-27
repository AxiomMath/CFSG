module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Quasithin.F112Crit.PermBound

variable {H : Type*} [Group H] {Ω : Type*} [MulAction H Ω]

@[expose] def centralizingPart (D : Subgroup H) (z : H) : Subgroup H where
  carrier := {d | d ∈ D ∧ ∀ ω : Ω, (z * d * z⁻¹) • ω = d • ω}
  mul_mem' := by
    rintro a b ⟨haD, ha⟩ ⟨hbD, hb⟩
    refine ⟨D.mul_mem haD hbD, fun ω => ?_⟩
    have e : z * (a * b) * z⁻¹ = (z * a * z⁻¹) * (z * b * z⁻¹) := by group
    rw [e, mul_smul, hb, ha, mul_smul]
  one_mem' := ⟨D.one_mem, fun ω => by simp⟩
  inv_mem' := by
    rintro a ⟨haD, ha⟩
    refine ⟨D.inv_mem haD, fun ω => ?_⟩
    have e : z * a⁻¹ * z⁻¹ = (z * a * z⁻¹)⁻¹ := by group
    rw [e, inv_smul_eq_iff, ha, smul_inv_smul]

theorem centralizingPart_le (D : Subgroup H) (z : H) :
    centralizingPart (Ω := Ω) D z ≤ D := fun _ hd => hd.1

variable {D : Subgroup H} {ν₀ : Ω} {z : H}

theorem fixedBy_inter_orbit_eq (hreg : ∀ d ∈ D, d • ν₀ = ν₀ → ∀ ω : Ω, d • ω = ω)
    (hz : z • ν₀ = ν₀) (hzD : ∀ d ∈ D, ∃ d' ∈ D, ∀ ω : Ω, (z * d * z⁻¹) • ω = d' • ω) :
    MulAction.fixedBy Ω z ∩ MulAction.orbit D ν₀ =
      MulAction.orbit (centralizingPart (Ω := Ω) D z) ν₀ := by
  have hzinv : z⁻¹ • ν₀ = ν₀ := inv_smul_eq_iff.mpr hz.symm
  ext ω
  constructor
  · rintro ⟨hωz, ⟨d, rfl⟩⟩
    obtain ⟨d', hd'D, hd'⟩ := hzD d d.2
    have hfix : (z * d * z⁻¹) • ν₀ = (d : H) • ν₀ := by
      rw [mul_smul, mul_smul, hzinv]
      exact hωz
    have hw : ((d : H)⁻¹ * d') • ν₀ = ν₀ := by
      rw [mul_smul, ← hd' ν₀, hfix, inv_smul_smul]
    have htriv := hreg _ (D.mul_mem (D.inv_mem d.2) hd'D) hw
    refine ⟨⟨(d : H), d.2, fun μ => ?_⟩, rfl⟩
    have h1 := htriv μ
    rw [mul_smul, inv_smul_eq_iff] at h1
    rw [hd' μ]
    exact h1
  · rintro ⟨c, rfl⟩
    refine ⟨?_, ⟨⟨(c : H), centralizingPart_le D z c.2⟩, rfl⟩⟩
    rw [MulAction.mem_fixedBy]
    show z • ((c : H) • ν₀) = (c : H) • ν₀
    have h := c.2.2 ν₀
    rw [mul_smul, mul_smul, hzinv] at h
    exact h

theorem card_fixedBy_inter_orbit_dvd [Finite H]
    (hreg : ∀ d ∈ D, d • ν₀ = ν₀ → ∀ ω : Ω, d • ω = ω)
    (hz : z • ν₀ = ν₀) (hzD : ∀ d ∈ D, ∃ d' ∈ D, ∀ ω : Ω, (z * d * z⁻¹) • ω = d' • ω) :
    Nat.card ↥(MulAction.fixedBy Ω z ∩ MulAction.orbit D ν₀) ∣
      Nat.card ↥(MulAction.orbit D ν₀) := by
  set C := centralizingPart (Ω := Ω) D z with hC
  rw [fixedBy_inter_orbit_eq hreg hz hzD]
  have hCD : C ≤ D := centralizingPart_le D z
  have hstab : Nat.card (MulAction.stabilizer C ν₀) = Nat.card (MulAction.stabilizer D ν₀) := by
    refine Nat.card_congr
      { toFun := fun c => ⟨⟨(c : C), hCD (c : C).2⟩, c.2⟩
        invFun := fun d => ⟨⟨((d : D) : H), (d : D).2, fun ω => ?_⟩, d.2⟩
        left_inv := fun c => rfl
        right_inv := fun d => rfl }
    have hd : ((d : D) : H) • ν₀ = ν₀ := d.2
    have htriv := hreg _ (d : D).2 hd
    rw [htriv, mul_smul, mul_smul, htriv, smul_inv_smul]
  have hC' : Nat.card (MulAction.stabilizer C ν₀) * Nat.card ↥(MulAction.orbit C ν₀) =
      Nat.card C := by
    rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer]
    exact Subgroup.card_mul_index _
  have hD' : Nat.card (MulAction.stabilizer D ν₀) * Nat.card ↥(MulAction.orbit D ν₀) =
      Nat.card D := by
    rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer]
    exact Subgroup.card_mul_index _
  have hdvd : Nat.card C ∣ Nat.card D := Subgroup.card_dvd_of_le hCD
  rw [← hC', ← hD', hstab] at hdvd
  exact Nat.dvd_of_mul_dvd_mul_left Nat.card_pos hdvd

end CFSG.Quasithin.F112Crit.PermBound

end
