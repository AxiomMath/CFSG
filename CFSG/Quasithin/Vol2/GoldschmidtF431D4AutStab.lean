module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4AutLn
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4HexD
public import CFSG.Quasithin.EmptyFaithful.S1421Inputs

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin

theorem conj_aut_apply {G : Type*} [Group G] (y : MulAut G) (x : G) :
    (MulAut.conj (y x) : MulAut G) = y * MulAut.conj x * y⁻¹ := by
  ext w
  show y x * w * (y x)⁻¹ = y (x * y⁻¹ w * x⁻¹)
  simp [map_mul, map_inv]

section H


theorem mem_d4H_iff_mul_z (x : D) : x ∈ d4H ↔ x * d4z = d4z * x :=
  Subgroup.mem_centralizer_singleton_iff

theorem mem_autStab_H_iff
    (hZH : ∀ x ∈ d4H, (∀ h ∈ d4H, h * x = x * h) → x = 1 ∨ x = d4z) (y : MulAut D) :
    y ∈ autStab d4H ↔ autPt y pt0 = pt0 := by
  have hfix : autPt y pt0 = pt0 ↔ y d4z = d4z := by
    rw [← zElt_injective.eq_iff, autPt_apply, zElt_zero]
  rw [hfix]
  constructor
  · intro hy
    have hzH : d4z ∈ d4H := (mem_d4H_iff_mul_z d4z).2 rfl
    have hwH : y d4z ∈ d4H := (hy d4z).1 hzH
    have hcen : ∀ h ∈ d4H, h * y d4z = y d4z * h := by
      intro h hh
      have hx : y⁻¹ h ∈ d4H := by
        have := (hy (y⁻¹ h)).2
        rw [MulAut.apply_inv_self] at this
        exact this hh
      have hc := (mem_d4H_iff_mul_z _).1 hx
      have := congrArg y hc
      rw [map_mul, map_mul, MulAut.apply_inv_self] at this
      exact this
    rcases hZH _ hwH hcen with h | h
    · exact absurd (y.injective (h.trans (map_one y).symm)) d4z_sq.2
    · exact h
  · intro hz x
    rw [mem_d4H_iff_mul_z, mem_d4H_iff_mul_z]
    constructor
    · intro h
      have := congrArg y h
      rwa [map_mul, map_mul, hz] at this
    · intro h
      apply y.injective
      rw [map_mul, map_mul, hz]
      exact h

end H

section N


theorem mem_d4N_iff_smul_zero (g : D) : g ∈ d4N ↔ g • (0 : Fin 2457) = 0 := by
  rw [mem_d4N_iff_image, ← lineSet_injective.eq_iff, lineSet_smul, lineSet_zero]

theorem d4_exists_smul_ln (l : Fin 2457) :
    ∃ g : D, g • (0 : Fin 2457) = l := by
  obtain ⟨y, -, hy⟩ := hexGeometryD.lines l
  exact ⟨y, Sum.inr.inj hy⟩


theorem smul_aut_ln (y : MulAut D) (x : D) (l : Fin 2457) :
    (y x) • l = autLn y (x • (autLn y⁻¹ l)) := by
  have h1 : (y x) • l = autLn (MulAut.conj (y x)) l := by
    rw [autLn_conj]
    rfl
  have h2 : x • autLn y⁻¹ l = autLn (MulAut.conj x) (autLn y⁻¹ l) := by
    rw [autLn_conj]
    rfl
  rw [h1, h2, conj_aut_apply, map_mul, map_mul]
  rfl

theorem mem_autStab_N_iff
    (hNN : ∀ g : D, (∀ x, x ∈ d4N ↔ g * x * g⁻¹ ∈ d4N) → g ∈ d4N) (y : MulAut D) :
    y ∈ autStab d4N ↔ autLn y 0 = 0 := by
  have hinvl : ∀ (α : MulAut D) (l : Fin 2457), autLn α⁻¹ (autLn α l) = l := fun α l => by
    rw [← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  constructor
  · intro hy
    set l := autLn y 0 with hl
    have hy' : y⁻¹ ∈ autStab d4N := (autStab d4N).inv_mem hy
    have h2 : autLn y⁻¹ l = 0 := hinvl y 0
    have hstabl : ∀ x : D, x • l = l ↔ x ∈ d4N := by
      intro x
      have h1 := smul_aut_ln y⁻¹ x 0
      rw [inv_inv, ← hl] at h1
      have h3 : x • l = l ↔ autLn y⁻¹ (x • l) = 0 := by
        rw [← h2]
        exact (autLn y⁻¹).injective.eq_iff.symm
      rw [h3, ← h1, ← mem_d4N_iff_smul_zero]
      exact (hy' x).symm
    obtain ⟨g, hg⟩ := d4_exists_smul_ln l
    have hconjN : ∀ x : D, x ∈ d4N ↔ g⁻¹ * x * g⁻¹⁻¹ ∈ d4N := by
      intro x
      rw [← hstabl, inv_inv, mem_d4N_iff_smul_zero, mul_smul, mul_smul, inv_smul_eq_iff, hg]
    have hgi : g⁻¹ ∈ d4N := hNN g⁻¹ hconjN
    have hgN : g ∈ d4N := by
      have := d4N.inv_mem hgi
      rwa [inv_inv] at this
    rw [← hg]
    exact (mem_d4N_iff_smul_zero g).1 hgN
  · intro hy0 x
    have hy0' : autLn y⁻¹ 0 = 0 := by
      have := hinvl y 0
      rwa [hy0] at this
    rw [mem_d4N_iff_smul_zero, mem_d4N_iff_smul_zero, smul_aut_ln, hy0']
    constructor
    · intro h
      rw [h]
      exact hy0
    · intro h
      apply (autLn y).injective
      rw [h, hy0]

end N

end CFSG.Quasithin.D4Hex
