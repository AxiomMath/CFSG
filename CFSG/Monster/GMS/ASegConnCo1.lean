module

public import CFSG.Monster.GMS.Leech.Linear
public import CFSG.Sporadic.Co1.Module.Pairs
public import CFSG.Monster.GMS.ASegConnCo1Inputs
public import Certificates.Certificate10028
public meta import CFSG.Sporadic.Co1.Module.PairsCheck
public import CFSG.Sporadic.Co1.Module.OddNative
public import CFSG.Sporadic.Co1.Module.OddFacts
public import Certificates.Certificate10073Base

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Co1.Module CFSG.Sporadic.Co1.Module.Pairs
  CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native

namespace ASegConn

theorem diamCheck_ok : diamCheck = true :=
  Certificates.certificate10028

theorem diamCheck_spec {p : ℕ} (hp : p < 98280) :
    inPts (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280
        ((orbitOf 2 98280).pts[0]! ^^^ (orbitOf 2 98280).pts[p]!) = true ∨
      ∃ q < 98280, inPts (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280
          ((orbitOf 2 98280).pts[0]! ^^^ (orbitOf 2 98280).pts[q]!) = true ∧
        inPts (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280
          ((orbitOf 2 98280).pts[p]! ^^^ (orbitOf 2 98280).pts[q]!) = true := by
  have h := diamCheck_ok
  unfold diamCheck diamCheckT at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, List.any_eq_true, List.mem_map,
    List.mem_filter] at h
  rcases h p hp with h1 | ⟨w, ⟨q, ⟨hq, hq2⟩, rfl⟩, hw⟩
  · exact Or.inl h1
  · exact Or.inr ⟨q, hq, hq2, hw⟩

theorem pt_lt
    {p : ℕ} (hp : p < 98280) : (orbitOf 2 98280).pts[p]! < 2 ^ 24 :=
  ((vOrbitOK_facts orbitOK_v₂).2 p hp).1

theorem inPts_iff_mem
    {w : ℕ} (hw : w < 2 ^ 24) :
    inPts (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 w = true ↔
      toVecD 24 w ∈ co1Orbit 0 := by
  rw [inPts_iff w hw, co1Orbit_zero, orbit_Co1_eq]

theorem exists_pt_of_mem
    {u : Vec24} (hu : u ∈ co1Orbit 0) :
    ∃ p < 98280, u = toVecD 24 (orbitOf 2 98280).pts[p]! := by
  rw [co1Orbit_zero, orbit_Co1_eq, orbit_v₂_eq] at hu
  obtain ⟨p, hp, rfl⟩ := hu
  exact ⟨p, hp, rfl⟩

theorem toVecD_pt_mem
    {q : ℕ} (hq : q < 98280) :
    toVecD 24 (orbitOf 2 98280).pts[q]! ∈ co1Orbit 0 := by
  rw [co1Orbit_zero, orbit_Co1_eq, orbit_v₂_eq]
  exact ⟨q, hq, rfl⟩

theorem co1_diam_base
    {y : Vec24} (hy : y ∈ co1Orbit 0) :
    v₂ + y ∈ co1Orbit 0 ∨ ∃ w ∈ co1Orbit 0, v₂ + w ∈ co1Orbit 0 ∧ y + w ∈ co1Orbit 0 := by
  obtain ⟨p, hp, rfl⟩ := exists_pt_of_mem hy
  have h0 : (orbitOf 2 98280).pts[0]! = 2 := pts_zero
  rcases diamCheck_spec hp with h | ⟨q, hq, h1, h2⟩
  · left
    have := (inPts_iff_mem (Nat.xor_lt_two_pow (pt_lt (by norm_num)) (pt_lt hp))).1 h
    rw [toVecD_xor, h0, toVecD_v₂] at this
    exact this
  · right
    refine ⟨toVecD 24 (orbitOf 2 98280).pts[q]!, toVecD_pt_mem hq, ?_, ?_⟩
    · have := (inPts_iff_mem (Nat.xor_lt_two_pow (pt_lt (by norm_num)) (pt_lt hq))).1 h1
      rw [toVecD_xor, h0, toVecD_v₂] at this
      exact this
    · have := (inPts_iff_mem (Nat.xor_lt_two_pow (pt_lt hp) (pt_lt hq))).1 h2
      rw [toVecD_xor] at this
      exact this

theorem co1_diam
    {u v : Vec24} (hu : u ∈ co1Orbit 0) (hv : v ∈ co1Orbit 0) :
    u + v ∈ co1Orbit 0 ∨ ∃ w ∈ co1Orbit 0, u + w ∈ co1Orbit 0 ∧ v + w ∈ co1Orbit 0 := by
  obtain ⟨c, rfl⟩ := hu
  have hv' : co1Act c⁻¹ v ∈ co1Orbit 0 := Leech.co1Act_mem_co1Orbit hv c⁻¹
  have e : co1Act c (co1Act c⁻¹ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  change co1Act c v₂ + v ∈ co1Orbit 0 ∨ ∃ w ∈ co1Orbit 0, co1Act c v₂ + w ∈ co1Orbit 0 ∧
    v + w ∈ co1Orbit 0
  rcases co1_diam_base hv' with h | ⟨w, hw, h1, h2⟩
  · left
    have := Leech.co1Act_mem_co1Orbit h c
    rwa [map_add, e] at this
  · right
    refine ⟨co1Act c w, Leech.co1Act_mem_co1Orbit hw c, ?_, ?_⟩
    · have := Leech.co1Act_mem_co1Orbit h1 c
      rwa [map_add] at this
    · have := Leech.co1Act_mem_co1Orbit h2 c
      rwa [map_add, e] at this

end ASegConn

end CFSG.Monster.GMS
