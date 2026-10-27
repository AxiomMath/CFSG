module

public import CFSG.Sporadic.Co1.Module.Pairs
public import CFSG.Monster.GMS.Facts.Co1Local
public import CFSG.Monster.GMS.S365NativeInputs
public import Certificates.Certificate10043
public meta import CFSG.Sporadic.Co1.Module.PairsCheck
public import CFSG.Sporadic.Co1.Module.OddFacts
public import Certificates.Certificate10073Base

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.Module CFSG.Sporadic.Co1.Module.Pairs

namespace S365

@[expose] def lbl (w : ℕ) : ℕ :=
  tyLab (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 w

theorem eightCheck_ok : eightCheck = true :=
  Certificates.certificate10043

theorem mem_co1Orbit_zero_of_lbl
    {w : ℕ} (hw : w < 2 ^ 24) (h : lbl w = 3) :
    toVecD 24 w ∈ co1Orbit 0 := by
  have := (tyLab_spec w hw 3 (by norm_num)).1 h
  rw [co1Orbit_zero, orbit_Co1_eq]
  exact this

theorem mem_co1Orbit_two_of_lbl
    {w : ℕ} (hw : w < 2 ^ 24) (h : lbl w = 1) :
    toVecD 24 w ∈ co1Orbit 2 := by
  have := (tyLab_spec w hw 1 (by norm_num)).1 h
  rw [co1Orbit_two, orbit_Co1_eq]
  exact this

@[expose] def Co1EightFacts : Prop :=
  ∃ x y : Fin 24 → ZMod 2, x ∈ co1Orbit 0 ∧ y ∈ co1Orbit 0 ∧ x + y ∈ co1Orbit 0 ∧
    (∃ v, v ∈ co1Orbit 2 ∧ v + x ∈ co1Orbit 0 ∧ v + y ∈ co1Orbit 0 ∧ v + x + y ∈ co1Orbit 0) ∧
    (∃ v, v ∈ co1Orbit 0 ∧ v + x ∈ co1Orbit 2 ∧ v + y ∈ co1Orbit 2 ∧ v + x + y ∈ co1Orbit 2) ∧
    (∃ v, v ∈ co1Orbit 2 ∧ v + x ∈ co1Orbit 2 ∧ v + y ∈ co1Orbit 2 ∧ v + x + y ∈ co1Orbit 2)

theorem co1EightFacts :
    Co1EightFacts := by
  have h := eightCheck_ok
  simp only [eightCheck, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨h2, h4, h6, h1, h3, h5, h7, h28, h30, h32, h34, h40, h42, h44, h46⟩ := h
  have hx := mem_co1Orbit_zero_of_lbl (w := 2) (by norm_num) h2
  have hy := mem_co1Orbit_zero_of_lbl (w := 4) (by norm_num) h4
  have hxy : toVecD 24 2 + toVecD 24 4 ∈ co1Orbit 0 := by
    have := mem_co1Orbit_zero_of_lbl (w := 6) (by norm_num) h6
    rw [show (6 : ℕ) = 2 ^^^ 4 by decide, toVecD_xor] at this
    exact this
  refine ⟨toVecD 24 2, toVecD 24 4, hx, hy, hxy, ⟨toVecD 24 1, ?_, ?_, ?_, ?_⟩,
    ⟨toVecD 24 28, ?_, ?_, ?_, ?_⟩, ⟨toVecD 24 40, ?_, ?_, ?_, ?_⟩⟩
  · exact mem_co1Orbit_two_of_lbl (by norm_num) h1
  · have := mem_co1Orbit_zero_of_lbl (w := 1 ^^^ 2) (by decide) h3
    rwa [toVecD_xor] at this
  · have := mem_co1Orbit_zero_of_lbl (w := 1 ^^^ 4) (by decide) h5
    rwa [toVecD_xor] at this
  · have := mem_co1Orbit_zero_of_lbl (w := 1 ^^^ 2 ^^^ 4) (by decide) h7
    rwa [toVecD_xor, toVecD_xor] at this
  · exact mem_co1Orbit_zero_of_lbl (by norm_num) h28
  · have := mem_co1Orbit_two_of_lbl (w := 28 ^^^ 2) (by decide) h30
    rwa [toVecD_xor] at this
  · have := mem_co1Orbit_two_of_lbl (w := 28 ^^^ 4) (by decide) h32
    rwa [toVecD_xor] at this
  · have := mem_co1Orbit_two_of_lbl (w := 28 ^^^ 2 ^^^ 4) (by decide) h34
    rwa [toVecD_xor, toVecD_xor] at this
  · exact mem_co1Orbit_two_of_lbl (by norm_num) h40
  · have := mem_co1Orbit_two_of_lbl (w := 40 ^^^ 2) (by decide) h42
    rwa [toVecD_xor] at this
  · have := mem_co1Orbit_two_of_lbl (w := 40 ^^^ 4) (by decide) h44
    rwa [toVecD_xor] at this
  · have := mem_co1Orbit_two_of_lbl (w := 40 ^^^ 2 ^^^ 4) (by decide) h46
    rwa [toVecD_xor, toVecD_xor] at this

theorem exists_co1Act_pair
    {x y x' y' : Fin 24 → ZMod 2} (hx : x ∈ co1Orbit 0)
    (hy : y ∈ co1Orbit 0) (hxy : x + y ∈ co1Orbit 0) (hx' : x' ∈ co1Orbit 0)
    (hy' : y' ∈ co1Orbit 0) (hxy' : x' + y' ∈ co1Orbit 0) :
    ∃ g : NativeSporadic.Co1, co1Act g x = x' ∧ co1Act g y = y' := by
  rw [co1Orbit_zero] at hx hy hxy hx' hy' hxy'
  have key : ∀ {a b : Vec24}, a ∈ MulAction.orbit NativeSporadic.Co1 v₂ →
      b ∈ MulAction.orbit NativeSporadic.Co1 v₂ → a + b ∈ MulAction.orbit NativeSporadic.Co1 v₂ →
      ∃ g : NativeSporadic.Co1, g • a = v₂ ∧ g • b ∈ cls 3 := by
    intro a b ha hb hab
    obtain ⟨h, rfl⟩ := ha
    refine ⟨h⁻¹, inv_smul_smul h v₂, orbit_smul_mem _ hb, ?_⟩
    have : v₂ + h⁻¹ • b = h⁻¹ • (h • v₂ + b) := by rw [smul_add, inv_smul_smul]
    rw [this]
    exact orbit_smul_mem _ hab
  obtain ⟨a, ha1, ha2⟩ := key hx hy hxy
  obtain ⟨b, hb1, hb2⟩ := key hx' hy' hxy'
  obtain ⟨k, hk1, hk2⟩ := cls_trans (j := 3) (by norm_num) ha2 hb2
  refine ⟨b⁻¹ * k * a, ?_, ?_⟩
  · show (b⁻¹ * k * a) • x = x'
    rw [mul_smul, mul_smul, ha1, hk1, ← hb1, inv_smul_smul]
  · show (b⁻¹ * k * a) • y = y'
    rw [mul_smul, mul_smul, hk2, inv_smul_smul]

end S365

end CFSG.Monster.GMS
