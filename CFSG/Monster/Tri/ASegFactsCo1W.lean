module

public import CFSG.Monster.GMS.S365Facts
public import CFSG.Monster.GMS.Leech.Linear
public import CFSG.Sporadic.Co1.Module.Pairs
public import CFSG.Monster.Tri.ASegFactsCo1WInputs
public import Certificates.Certificate10046
public meta import CFSG.Sporadic.Co1.Module.PairsCheck
public meta import CFSG.Sporadic.Co1.Module.Orbits
public import CFSG.Sporadic.Co1.Module.OddFacts
public import Certificates.Certificate10073Base

public section

namespace CFSG.Monster.Tri

open CFSG.Monster.GMS CFSG.Monster.GMS.S365 CFSG.Sporadic.Co1.Module.Pairs
  CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Co1.Module (orbitOf)

@[expose] def Co1FourW : Prop :=
  ∀ a b ω : Fin 24 → ZMod 2, FourPattern a b ω →
    ∃ p ∈ co1Orbit 0, p + a ∈ co1Orbit 0 ∧ p + b ∈ co1Orbit 0 ∧ p + ω ∈ co1Orbit 0

theorem wCheck_ok : wCheck = true :=
  Certificates.certificate10046.1

theorem baseCheck_ok : baseCheck = true :=
  Certificates.certificate10046.2

theorem mem_co1Orbit_zero_of_tyLab
    {w : ℕ} (hw : w < 2 ^ 24)
    (h : tyLab (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 w = 3) :
    toVecD 24 w ∈ co1Orbit 0 := by
  have h1 := (tyLab_spec w hw 3 (by norm_num)).1 h
  rw [co1Orbit_zero, orbit_Co1_eq]
  exact h1

theorem mem_co1Orbit_two_of_tyLab
    {w : ℕ} (hw : w < 2 ^ 24)
    (h : tyLab (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 w = 1) :
    toVecD 24 w ∈ co1Orbit 2 := by
  have h1 := (tyLab_spec w hw 1 (by norm_num)).1 h
  rw [co1Orbit_two, orbit_Co1_eq]
  exact h1

theorem wData_spec :
    ∀ pω ∈ wData, toVecD 24 pω.1 ∈ co1Orbit 0 ∧
    toVecD 24 pω.1 + toVecD 24 2 ∈ co1Orbit 0 ∧ toVecD 24 pω.1 + toVecD 24 4 ∈ co1Orbit 0 ∧
      toVecD 24 pω.1 + toVecD 24 pω.2 ∈ co1Orbit 0 := by
  have h := wCheck_ok
  have hb : ∀ pω ∈ wData, pω.1 < 2 ^ 24 ∧ pω.2 < 2 ^ 24 := by
    intro pω hpω
    simp only [wData, List.mem_cons, List.not_mem_nil, or_false] at hpω
    rcases hpω with rfl | rfl | rfl | rfl <;> norm_num
  unfold wCheck at h
  simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  intro pω hpω
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h pω hpω
  obtain ⟨hp, hω⟩ := hb pω hpω
  refine ⟨mem_co1Orbit_zero_of_tyLab hp h1, ?_, ?_, ?_⟩
  · rw [← toVecD_xor]
    exact mem_co1Orbit_zero_of_tyLab (Nat.xor_lt_two_pow hp (by norm_num)) h2
  · rw [← toVecD_xor]
    exact mem_co1Orbit_zero_of_tyLab (Nat.xor_lt_two_pow hp (by norm_num)) h3
  · rw [← toVecD_xor]
    exact mem_co1Orbit_zero_of_tyLab (Nat.xor_lt_two_pow hp hω) h4

theorem fourPattern_base :
    FourPattern (toVecD 24 2) (toVecD 24 4) (toVecD 24 40) := by
  have h := baseCheck_ok
  unfold baseCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨mem_co1Orbit_zero_of_tyLab (by norm_num) h1, mem_co1Orbit_zero_of_tyLab (by norm_num) h2,
    ?_, mem_co1Orbit_two_of_tyLab (by norm_num) h4, ?_, ?_, ?_⟩
  · rw [← toVecD_xor]
    exact mem_co1Orbit_zero_of_tyLab (by norm_num) h3
  · rw [← toVecD_xor]
    exact mem_co1Orbit_two_of_tyLab (by norm_num) h5
  · rw [← toVecD_xor]
    exact mem_co1Orbit_two_of_tyLab (by norm_num) h6
  · rw [← toVecD_xor, ← toVecD_xor]
    exact mem_co1Orbit_two_of_tyLab (by norm_num) h7

theorem co1Act_inv_co1Act (g : Co1) (v : Fin 24 → ZMod 2) : co1Act g⁻¹ (co1Act g v) = v := by
  calc co1Act g⁻¹ (co1Act g v) = (co1Act g⁻¹ * co1Act g) v := (Module.End.mul_apply _ _ _).symm
    _ = co1Act (g⁻¹ * g) v := by rw [map_mul]
    _ = v := by rw [inv_mul_cancel, map_one, Module.End.one_apply]

theorem exists_fourW_of_smul {g : Co1} {a b ω a₀ b₀ ω' p₀ : Fin 24 → ZMod 2}
    (hga : co1Act g a = a₀) (hgb : co1Act g b = b₀) (hgω : co1Act g ω = ω')
    (hp : p₀ ∈ co1Orbit 0) (h1 : p₀ + a₀ ∈ co1Orbit 0) (h2 : p₀ + b₀ ∈ co1Orbit 0)
    (h3 : p₀ + ω' ∈ co1Orbit 0) :
    ∃ p ∈ co1Orbit 0, p + a ∈ co1Orbit 0 ∧ p + b ∈ co1Orbit 0 ∧ p + ω ∈ co1Orbit 0 := by
  have key : ∀ (x x₀ : Fin 24 → ZMod 2), co1Act g x = x₀ →
      co1Act g⁻¹ p₀ + x = co1Act g⁻¹ (p₀ + x₀) := by
    intro x x₀ hx
    rw [map_add, ← hx, co1Act_inv_co1Act]
  refine ⟨co1Act g⁻¹ p₀, Leech.co1Act_mem_co1Orbit hp g⁻¹, ?_, ?_, ?_⟩
  · rw [key a a₀ hga]
    exact Leech.co1Act_mem_co1Orbit h1 g⁻¹
  · rw [key b b₀ hgb]
    exact Leech.co1Act_mem_co1Orbit h2 g⁻¹
  · rw [key ω ω' hgω]
    exact Leech.co1Act_mem_co1Orbit h3 g⁻¹

theorem co1FourW
    (hT : Co1FourT) : Co1FourW := by
  intro a b ω hP
  obtain ⟨g, hga, hgb, hgω⟩ := hT a b ω _ _ _ hP fourPattern_base
  have e42 : toVecD 24 42 = toVecD 24 40 + toVecD 24 2 := by
    rw [← toVecD_xor]
    rfl
  have e44 : toVecD 24 44 = toVecD 24 40 + toVecD 24 4 := by
    rw [← toVecD_xor]
    rfl
  have e46 : toVecD 24 46 = toVecD 24 40 + toVecD 24 2 + toVecD 24 4 := by
    rw [← toVecD_xor, ← toVecD_xor]
    rfl
  rcases hgω with h | h | h | h
  · obtain ⟨s1, s2, s3, s4⟩ := wData_spec (154, 40) (by simp [wData])
    exact exists_fourW_of_smul hga hgb h s1 s2 s3 s4
  · obtain ⟨s1, s2, s3, s4⟩ := wData_spec (290, 42) (by simp [wData])
    refine exists_fourW_of_smul hga hgb (ω' := toVecD 24 40 + toVecD 24 2) h s1 s2 s3 ?_
    rw [← e42]
    exact s4
  · obtain ⟨s1, s2, s3, s4⟩ := wData_spec (894, 44) (by simp [wData])
    refine exists_fourW_of_smul hga hgb (ω' := toVecD 24 40 + toVecD 24 4) h s1 s2 s3 ?_
    rw [← e44]
    exact s4
  · obtain ⟨s1, s2, s3, s4⟩ := wData_spec (10, 46) (by simp [wData])
    refine exists_fourW_of_smul hga hgb (ω' := toVecD 24 40 + toVecD 24 2 + toVecD 24 4) h s1 s2 s3
      ?_
    rw [← e46]
    exact s4

end CFSG.Monster.Tri
