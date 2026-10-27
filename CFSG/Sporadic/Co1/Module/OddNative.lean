
module

public import CFSG.Sporadic.Co1.Module.OddNativeBase1

public import CFSG.Sporadic.Co1.Module.Forms
public import Certificates.Data.CFSGNative.Co1.Odd
public import Certificates.Certificate10074
public meta import CFSG.Sporadic.Co1.Module.Orbits
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Co1.Odd

public section

namespace CFSG.Sporadic.Co1.Module.Odd

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.OddNative Matrix

attribute [local instance] vecAct vecSMul

section SLP

variable {M : Type*} [Monoid M]

end SLP

theorem inPts_iff
    (w : ℕ) (hw : w < 2 ^ 24) :
    inPts (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 w = true ↔
      toVecD 24 w ∈ MulAction.orbit Jmat v₂ := by
  rw [orbit_v₂_eq]
  obtain ⟨-, hfacts⟩ := vOrbitOK_facts orbitOK_v₂
  constructor
  · intro h
    simp only [inPts, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact ⟨_, h.1, by rw [orbitVec, h.2]⟩
  · rintro ⟨i, hi, e⟩
    have hi' : i < 98280 := hi
    have := toVecD_injective (hfacts i hi').1 hw e
    simp only [inPts, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    rw [← this, (hfacts i hi').2.1]
    exact ⟨hi', rfl⟩

theorem type4N_iff
    (x : ℕ) (hx : x < 2 ^ 24) :
    type4N (transposeRows 24 qRows) (orbitOf 2 98280).pts
        (posTable 24 (orbitOf 2 98280).pts) 98280 x = true ↔
      toVecD 24 x ∈ MulAction.orbit Jmat v₄ := by
  have hq := q₀_toVecD x
  have hin := inPts_iff x hx
  have hz : x = 0 ↔ toVecD 24 x = 0 := by
    constructor
    · rintro rfl; exact toVecD_zero 24
    · intro h; exact toVecD_injective hx (by norm_num) (h.trans (toVecD_zero 24).symm)
  have hsing := singular_eq_union
  have hdisj := Set.disjoint_left.1 disjoint_orbit_v₂_v₄
  unfold type4N
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true']
  constructor
  · rintro ⟨⟨h0, hq0⟩, hn⟩
    have hv : toVecD 24 x ∈ {v : Vec24 | q₀ v = 0 ∧ v ≠ 0} := by
      refine ⟨?_, fun h => h0 (hz.2 h)⟩
      rw [hq]; simp [hq0]
    rw [hsing] at hv
    rcases hv with h | h
    · exact absurd (hin.2 h) (by simp [hn])
    · exact h
  · intro h4
    have hv : toVecD 24 x ∈ {v : Vec24 | q₀ v = 0 ∧ v ≠ 0} := by
      rw [hsing]; exact Or.inr h4
    obtain ⟨hq0, hne⟩ := hv
    refine ⟨⟨fun h => hne (hz.1 h), ?_⟩, ?_⟩
    · by_contra hc
      have : q0N (transposeRows 24 qRows) x = true := by simpa using hc
      have h1 : q₀ (toVecD 24 x) = 1 := by rw [hq]; simp [this]
      rw [h1] at hq0
      exact absurd hq0 (by decide)
    · by_contra hc
      have : inPts (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 x = true := by
        simpa using hc
      exact hdisj (hin.1 this) h4

theorem ncard_fixedSet4
    (Ms : List (Array ℕ)) :
    {v : Vec24 | v ∈ MulAction.orbit Jmat v₄ ∧ ∀ M ∈ Ms, rowsMatrix 24 M *ᵥ v = v}.ncard =
      fixCount4 (Ms.map (transposeRows 24)) (transposeRows 24 qRows) (orbitOf 2 98280).pts
        (posTable 24 (orbitOf 2 98280).pts) 98280 := by
  unfold fixCount4
  refine ncard_eq_countBelow fun x hx => ?_
  rw [Bool.and_eq_true, type4N_iff x hx, List.all_eq_true]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h2, fun M hM => (isFixedN_iff M hx).1 (h1 _ (List.mem_map_of_mem hM))⟩
  · rintro ⟨h2, h1⟩
    refine ⟨fun Mt hMt => ?_, h2⟩
    obtain ⟨M, hM, rfl⟩ := List.mem_map.1 hMt
    exact (isFixedN_iff M hx).2 (h1 M hM)

end CFSG.Sporadic.Co1.Module.Odd
