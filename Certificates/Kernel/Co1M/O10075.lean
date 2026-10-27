
module

public import Certificates.Kernel.Co1M.Orb98280
public import CFSG.Certificates.Kernel.Co1M.OrbitSizesBase
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Co1M.OrbitCheckOf
public import CFSG.Sporadic.Suz.Setup
public import CFSG.Sporadic.Suz.W64Spec

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KC.Co1M CFSG.KC.VecK CFSG.KC.VOrbFull CFSG.KC.Co1Orb CFSG.KC.PairCount CFSG.KLie.CT
  CFSG.Sporadic.Co1.Module CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Th.Native CertificateChecks.KernelVec.Co1 CFSG.Blueprint

theorem orb2_eq : orbitOf 2 98280 = (CFSG.Sporadic.Co1.Native.co1Data ()).orbit () := rfl

theorem orb2_tables : orbitOf 2 98280 =
    ⟨((List.range 98280).map fun h => lk Pt 32 h).toArray,
      ((List.range 98280).map fun h => UInt32.ofNat (lk AT 32 h)).toArray,
      ((List.range 98280).map fun h => UInt32.ofNat (lk BT 32 h)).toArray⟩ := by
  rw [orb2_eq]
  exact orbit_eq (CFSG.Sporadic.Co1.Native.co1Data ()) hA hB cm_seed (by quickRfl) (by quickRfl)
    cmHorb cmHbfs cmHsort

theorem orb2_ok : vOrbitOK 24 98280 dat.colsA dat.colsB (orbitOf 2 98280) = true := by
  rw [orb2_eq]
  exact orbit_ok (CFSG.Sporadic.Co1.Native.co1Data ()) hA hB cm_seed (by quickRfl) (by quickRfl)
    cmHorb cmHbfs cmHsort

theorem ap_tab {f : Nat → Nat} (hf : ∀ i < 98280, f i < 98280) {i : Nat} (hi : i < 98280) :
    ap ((List.range 98280).map fun h => UInt32.ofNat (f h)).toArray i = f i := by
  unfold ap
  rw [getElem!_pos _ i (by simpa using hi)]
  simp only [List.getElem_toArray, List.getElem_map, List.getElem_range, UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by have := hf i hi; omega)

theorem parents2 : ∀ y, 0 < y → y < 98280 → ∃ p < y, ap (orbitOf 2 98280).alpha p = y ∨
    ap (orbitOf 2 98280).beta p = y := by
  intro y hy0 hy
  have hAT : ∀ i < 98280, lk AT 32 i < 98280 := fun i hi => (orbAt_iff.1 (cmHorb i hi)).2.1
  have hBT : ∀ i < 98280, lk BT 32 i < 98280 := fun i hi => (orbAt_iff.1 (cmHorb i hi)).2.2.1
  rcases (bfsAt_iff.1 (cmHbfs y hy)).1 with h0 | ⟨hf, hs, -⟩
  · omega
  rw [orb2_tables]
  dsimp only
  obtain ⟨p, hp | hp⟩ := Nat.even_or_odd' (lk FO 32 y)
  · rw [hp, seqAt_even] at hs
    refine ⟨p, by omega, Or.inl ?_⟩
    rw [ap_tab hAT (by omega), hs]
  · rw [hp, seqAt_odd] at hs
    refine ⟨p, by omega, Or.inr ?_⟩
    rw [ap_tab hBT (by omega), hs]

theorem inPts2_iff (x : Nat) :
    CFSG.Sporadic.Co1.OddNative.inPts (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts)
      98280 x = true ↔ ∃ i < 98280, (orbitOf 2 98280).pts[i]! = x := by
  obtain ⟨hsz, hO⟩ := vOrbitOK_facts orb2_ok
  unfold CFSG.Sporadic.Co1.OddNative.inPts
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨_, h1, h2⟩
  · rintro ⟨i, hi, rfl⟩
    rw [(hO i hi).2.1]
    exact ⟨hi, rfl⟩

theorem not_found {w : Nat} (hw : notB (orbMemK 98280 (lk S 32) 17 w) = true) :
    ∀ i < 98280, (orbitOf 2 98280).pts[i]! ≠ w := by
  intro i hi e
  have h := (inPts2_iff w).2 ⟨i, hi, e⟩
  rw [orb2_eq, cm_orb_inPts] at h
  rw [h] at hw
  exact absurd hw (by decide)

theorem not_v3 : notB (orbMemK 98280 (lk S 32) 17 4096) = true := by quickRfl

theorem not_v4 : notB (orbMemK 98280 (lk S 32) 17 1) = true := by quickRfl

theorem root2 : Nat.beq (lk Pt 32 0) 2 = true := by quickRfl

theorem orbitCheck_v₂_k : orbitCheck 2 98280 [4096, 1] = true := by
  obtain ⟨hsz, hO⟩ := vOrbitOK_facts orb2_ok
  have h0 : (orbitOf 2 98280).pts[0]! = 2 := by
    rw [orb2_eq, cm_orb_twin.2.1 0 (by norm_num)]
    exact Nat.eq_of_beq_eq_true root2
  have hT := tree_of (n := 98280) (O := orbitOf 2 98280) (by norm_num) (by norm_num)
    (fun i hi => (hO i hi).2.2.1) (fun i hi => (hO i hi).2.2.2.2.1) (reach_of_parents parents2)
  unfold orbitCheck
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨orb2_ok, h0⟩, hT.1⟩, hT.2⟩, ?_⟩
  rw [List.all_eq_true]
  intro w hw
  rw [Bool.not_eq_true']
  by_contra hc
  rw [Bool.not_eq_false, Array.contains_iff_mem] at hc
  obtain ⟨i, hi, e⟩ := Array.mem_iff_getElem.1 hc
  rw [hsz] at hi
  have e' : (orbitOf 2 98280).pts[i]! = w := by rw [getElem!_pos _ i (by omega), e]
  have : w = 4096 ∨ w = 1 := by simpa using hw
  rcases this with rfl | rfl
  · exact not_found not_v3 i hi e'
  · exact not_found not_v4 i hi e'

noncomputable abbrev P2 (i : Nat) : Vec24 := toVecD 24 (lk Pt 32 i)

theorem pts2 {i : Nat} (hi : i < 98280) : (orbitOf 2 98280).pts[i]! = lk Pt 32 i := by
  rw [orb2_eq]
  exact cm_orb_twin.2.1 i hi

theorem P2_inj : Set.InjOn P2 ↑(Finset.range 98280) := by
  intro i hi j hj e
  have hi' : i < 98280 := by simpa using hi
  have hj' : j < 98280 := by simpa using hj
  have h := (orbit_spec orbitCheck_v₂_k).2.1 i hi' j hj'
  unfold orbitVec at h
  rw [pts2 hi', pts2 hj'] at h
  exact h e

theorem O2_eq :
    orb co1Act v₂ = (Finset.range 98280).image P2 := by
  apply Finset.coe_injective
  have e : (↑(orb co1Act v₂) : Set Vec24) = MulAction.orbit Jmat v₂ := by
    rw [← range_co1Act]
    ext x
    rw [Finset.mem_coe, mem_orb, Set.mem_range]
  rw [e, Finset.coe_image, ← toVecD_v₂, (orbit_spec orbitCheck_v₂_k).1]
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i, by simpa using hi, ?_⟩
    unfold orbitVec
    rw [pts2 hi]
  · rintro ⟨i, hi, rfl⟩
    have hi' : i < 98280 := by simpa using hi
    refine ⟨i, hi', ?_⟩
    unfold orbitVec
    rw [pts2 hi']

theorem Pt_lt {i : Nat} (hi : i < 98280) : lk Pt 32 i < 2 ^ 24 := by
  have := ((vOrbitOK_facts orb2_ok).2 i hi).1
  rwa [pts2 hi] at this

theorem mem_O2 {x : Nat} (hx : x < 2 ^ 24) :
    toVecD 24 x ∈ orb co1Act v₂ ↔ orbMemK 98280 (lk S 32) 17 x = true := by
  have e1 : orbMemK 98280 (lk S 32) 17 x = CFSG.Sporadic.Co1.OddNative.inPts
      (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 x := (cm_orb_inPts x).symm
  rw [e1, inPts2_iff, O2_eq, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, e⟩
    have hi' : i < 98280 := Finset.mem_range.1 hi
    refine ⟨i, hi', ?_⟩
    rw [pts2 hi']
    exact toVecD_injective (Pt_lt hi') hx e
  · rintro ⟨i, hi, e⟩
    refine ⟨i, Finset.mem_range.2 hi, ?_⟩
    rw [← e, pts2 hi]

theorem count_O2 {w : Nat} (hw : w < 2 ^ 24) :
    ((orb co1Act v₂).filter fun a => toVecD 24 w + a ∈ orb co1Act v₂).card =
      ((Finset.range 98280).filter fun i =>
        orbMemK 98280 (lk S 32) 17 (Nat.xor (lk Pt 32 i) w) = true).card := by
  have hP : ∀ i < 98280, (toVecD 24 w + P2 i ∈ orb co1Act v₂ ↔
      orbMemK 98280 (lk S 32) 17 (Nat.xor (lk Pt 32 i) w) = true) := by
    intro i hi
    have e : toVecD 24 w + P2 i = toVecD 24 (Nat.xor (lk Pt 32 i) w) := by
      change toVecD 24 w + P2 i = toVecD 24 (lk Pt 32 i ^^^ w)
      rw [toVecD_xor, add_comm]
    rw [e]
    exact mem_O2 (Nat.xor_lt_two_pow (Pt_lt hi) hw)
  have hO : ∀ i < 98280, P2 i ∈ orb co1Act v₂ := fun i hi => by
    rw [O2_eq]
    exact Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩
  refine (Finset.card_bij (fun i _ => P2 i) (fun i hi => ?_) (fun i hi j hj e => ?_)
    (fun b hb => ?_)).symm
  · rw [Finset.mem_filter, Finset.mem_range] at hi
    rw [Finset.mem_filter]
    exact ⟨hO i hi.1, (hP i hi.1).2 hi.2⟩
  · rw [Finset.mem_filter] at hi hj
    exact P2_inj (Finset.mem_coe.2 hi.1) (Finset.mem_coe.2 hj.1) e
  · rw [Finset.mem_filter] at hb
    have hb1 := hb.1
    rw [O2_eq, Finset.mem_image] at hb1
    obtain ⟨i, hi, rfl⟩ := hb1
    have hi' : i < 98280 := Finset.mem_range.1 hi
    refine ⟨i, ?_, rfl⟩
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨hi', (hP i hi').1 hb.2⟩

end CertificateChecks.KernelCo1M

end
