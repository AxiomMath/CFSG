module

public import Certificates.Kernel.AS81.Data
public import Certificates.Kernel.OmegaEight.NatData
public import CFSG.Certificates.Kernel.AS81LineSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Co2Schreier.ThirdCheck
public import CFSG.Sporadic.Schreier.Co1ThreeLocal
public import CFSG.Sporadic.Schreier.TitsChain

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelAS81

open CFSG.KC.Enum CFSG.KS CFSG.KC.AS81 CFSG.EvenSmallLie.OmegaEight CertificateChecks.KernelO8
open CFSG.ComponentClassification.AS81.MinusLines

theorem ns_bind : ∀ p < 120, nsArr[p]! = pg 8 255 NSP p := by decide +kernel

theorem ni_bind : ∀ v < 256, nsIdx[v]! = pg 8 255 NIP v := by decide +kernel

theorem rp_bind : ∀ i < 8, (rootPairs.getD i []).getD 0 (0, 0) =
    (pg 8 255 CFSG.KC.O8.RP (6 * i), pg 8 255 CFSG.KC.O8.RP (6 * i + 1)) := by decide +kernel

theorem kPts : ptsK NSP NIP O = true := by quickRfl

theorem kLines : linesK NSP NIP LT = true := by quickRfl

theorem kLine : lineK LT PR = true := by quickRfl

theorem pg_lt (w m p i : Nat) : pg w m p i ≤ m := Nat.and_le_right

theorem xor_lt8 {a b : Nat} (ha : a < 256) (hb : b < 256) : a ^^^ b < 256 :=
  Nat.xor_lt_two_pow (n := 8) ha hb

theorem toNat_mul_lt {c : Bool} {w : Nat} (hw : w < 256) : c.toNat * w < 256 := by
  cases c <;> simp <;> omega

theorem eichK_lt {u w x : Nat} (hu : u < 256) (hw : w < 256) (hx : x < 256) :
    CFSG.KC.O8.eichK false u w x < 256 := by
  unfold CFSG.KC.O8.eichK
  rw [b8K_eq, b8K_eq, q8K_eq]
  have e : ∀ a b : Bool, Nat.land a.toNat b.toNat = (a && b).toNat := fun a b => by
    cases a <;> cases b <;> rfl
  rw [e]
  exact xor_lt8 (xor_lt8 hx (toNat_mul_lt hw)) (xor_lt8 (toNat_mul_lt hu) (toNat_mul_lt hu))

theorem ns_lt (p : Nat) : pg 8 255 NSP p < 256 := Nat.lt_succ_of_le (pg_lt _ _ _ _)

theorem genArrs_get {i : Nat} (hi : i < 8) : genArrs[i]! = rootArr (rootPairs.getD i []) := by
  have hs : (rootPairs.map rootArr).toArray.size = 8 := by simp [rootPairs]
  unfold genArrs
  rw [getElem!_pos _ i (by rw [Array.size_append, hs]; simp; omega),
    Array.getElem_append_left (by rw [hs]; exact hi)]
  simp only [List.getElem_toArray, List.getElem_map]
  rw [List.getD_eq_getElem]

theorem o_size : omega1Gens.size = 8 := by
  unfold omega1Gens
  exact Array.size_ofFn

theorem o_bind : ∀ i < 8, ∀ j < 120, (omega1Gens[i]!)[j]! = pg 7 127 (O i) j := by
  intro i hi j hj
  unfold omega1Gens copy0Arr
  rw [getElem!_pos _ i (by simp; omega), Array.getElem_ofFn]
  dsimp only
  rw [getElem!_pos _ j (by simp; omega), Array.getElem_ofFn]
  dsimp only
  rw [genArrs_get hi]
  unfold rootArr
  rw [getElem!_pos _ j (by simp; omega), Array.getElem_ofFn]
  dsimp only
  rw [Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj, rp_bind i hi, ns_bind j hj, eichNat_eq,
    ni_bind _ (eichK_lt (Nat.lt_succ_of_le (pg_lt _ _ _ _)) (Nat.lt_succ_of_le (pg_lt _ _ _ _))
      (ns_lt j))]
  have h := allN_spec (allN_spec kPts i hi) j hj
  rw [CFSG.KC.Pack.strictB_eq] at h
  obtain ⟨-, h2⟩ := CFSG.KC.Pack.band_iff.1 h
  rw [Nat.eq_of_beq_eq_true h2, Nat.mul_zero, Nat.zero_add]
  rfl

theorem lineHead_eq {a b : Nat} (ha : a < 120) (hb : b < 120) :
    lineHead a b = headK NSP NIP a b := by
  unfold lineHead thirdPt headK thirdK nsK
  have hx : nsIdx[pg 8 255 NSP a ^^^ pg 8 255 NSP b]! =
      pg 8 255 NIP (Nat.xor (pg 8 255 NSP a) (pg 8 255 NSP b)) :=
    ni_bind _ (xor_lt8 (ns_lt a) (ns_lt b))
  rw [ns_bind a ha, ns_bind b hb, bNat_eq, hx, CFSG.KC.MergeR.band_eq, CFSG.KC.MergeR.band_eq,
    Bool.and_assoc]
  congr 1

theorem thirdPt_eq {a b : Nat} (ha : a < 120) (hb : b < 120) :
    thirdPt a b = thirdK NSP NIP a b := by
  unfold thirdPt thirdK nsK
  rw [ns_bind a ha, ns_bind b hb]
  exact ni_bind _ (xor_lt8 (ns_lt a) (ns_lt b))

theorem line_facts {t : Nat} (ht : t < 1120) :
    ltK LT 0 t < ltK LT 1 t ∧ ltK LT 1 t < ltK LT 2 t ∧ ltK LT 2 t < 120 ∧
      plK PR (ltK LT 0 t) (ltK LT 1 t) = t ∧ plK PR (ltK LT 1 t) (ltK LT 0 t) = t ∧
      plK PR (ltK LT 0 t) (ltK LT 2 t) = t ∧ plK PR (ltK LT 2 t) (ltK LT 0 t) = t ∧
      plK PR (ltK LT 1 t) (ltK LT 2 t) = t ∧ plK PR (ltK LT 2 t) (ltK LT 1 t) = t := by
  have hl := allN_spec kLine t ht
  simp only [CFSG.KC.Pack.strictB_eq, CFSG.KC.Pack.band_iff, Nat.blt_eq] at hl
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hl
  exact ⟨h1, h2, h3, Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5, Nat.eq_of_beq_eq_true h6,
    Nat.eq_of_beq_eq_true h7, Nat.eq_of_beq_eq_true h8, Nat.eq_of_beq_eq_true h9⟩

theorem lineList_eq : lineList = (List.range 1120).map fun t => (ltK LT 0 t, ltK LT 1 t, ltK LT 2 t) := by
  have e := flatMap_filter_range 120 120 lineHead (fun a b => (a, b, thirdPt a b))
  unfold lineList
  rw [e]
  have kL := kLines
  simp only [linesK, CFSG.KC.Pack.band_iff] at kL
  obtain ⟨hf, hc⟩ := kL
  have hk : (List.range (120 * 120)).filter (fun i => lineHead (i / 120) (i % 120)) =
      (List.range 14400).filter (keyHeadK NSP NIP) := by
    refine List.filter_congr fun i hi => ?_
    have hi' := List.mem_range.1 hi
    exact lineHead_eq (by omega) (Nat.mod_lt _ (by norm_num))
  rw [hk, filtK_sound hf, List.map_map]
  refine List.map_congr_left fun t ht => ?_
  have ht' := List.mem_range.1 ht
  obtain ⟨ha, hb, hc', -⟩ := line_facts ht'
  have h2 := Nat.eq_of_beq_eq_true (allN_spec hc t ht')
  change ((120 * ltK LT 0 t + ltK LT 1 t) / 120, (120 * ltK LT 0 t + ltK LT 1 t) % 120,
    thirdPt ((120 * ltK LT 0 t + ltK LT 1 t) / 120) ((120 * ltK LT 0 t + ltK LT 1 t) % 120)) = _
  have hb' : ltK LT 1 t < 120 := by omega
  rw [Nat.mul_add_div (by norm_num), Nat.div_eq_of_lt hb', Nat.add_zero, Nat.mul_add_mod,
    Nat.mod_eq_of_lt hb', h2, thirdPt_eq (by omega) hb']

theorem lt_size : lineArr.size = 1120 := by
  unfold lineArr
  rw [List.size_toArray, lineList_eq, List.length_map, List.length_range]

theorem lt_bind {t : Nat} (ht : t < 1120) :
    lineArr[t]! = (ltK LT 0 t, ltK LT 1 t, ltK LT 2 t) := by
  rw [getElem!_pos _ t (by rw [lt_size]; exact ht)]
  unfold lineArr
  simp only [List.getElem_toArray]
  simp only [lineList_eq, List.getElem_map, List.getElem_range]

end CertificateChecks.KernelAS81

end
