module

public import Certificates.Kernel.AS81.Bind
public import Certificates.Kernel.AS81.Checks
public import CFSG.Certificates.Kernel.SporSch.TitsPrimSound
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAS81

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.AS81 CFSG.KC.MergeG
open CFSG.KC.MergeR CertificateChecks.KernelO8 CFSG.ComponentClassification.AS81.MinusLines
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.Tits
open CFSG.EvenSmallLie.OmegaEight CFSG.Certificates

theorem key_div {x y : Nat} (hy : y < 120) : (120 * x + y) / 120 = x ∧ (120 * x + y) % 120 = y := by
  constructor <;> omega

theorem bIf_or (c d : Bool) : Bool.rec (motive := fun _ => Bool) d true c = (c || d) := by
  cases c <;> rfl

theorem onLine_eq {t v : Nat} (ht : t < 1120) : onLine lineArr[t]! v = onK LT t v := by
  rw [lt_bind ht]
  unfold onLine onK
  rw [bIf_or, bIf_or]
  apply Bool.eq_iff_iff.2
  simp only [Bool.or_eq_true, beq_iff_eq, Nat.beq_eq, or_assoc]

theorem pairIn_key {a b c x y : Nat} (hy : y < 120) (ha : a < 120) (hb : b < 120) (hc : c < 120)
    (h : pairIn a b c x y = true) : 120 * x + y ∈ keys (a, b, c) := by
  unfold pairIn at h
  unfold keys
  simp only [CFSG.KC.MergeG.bIfT_iff, CFSG.KC.Pack.band_iff, Nat.beq_eq] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp

theorem pl_get {k : Nat} (hk : k < 14400) : pairLine[k]! = plK PR (k / 120) (k % 120) := by
  refine pairLine_get (P := fun k => plK PR (k / 120) (k % 120)) ?_ ?_ k hk
  · intro t ht k hk'
    rw [lt_size] at ht
    rw [lt_bind ht] at hk'
    obtain ⟨h1, h2, h3, e1, e2, e3, e4, e5, e6⟩ := line_facts ht
    unfold keys at hk'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk'
    rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [(key_div (by omega)).1, (key_div (by omega)).2]; exact ⟨by omega, e1⟩
    · rw [(key_div (by omega)).1, (key_div (by omega)).2]; exact ⟨by omega, e2⟩
    · rw [(key_div (by omega)).1, (key_div (by omega)).2]; exact ⟨by omega, e3⟩
    · rw [(key_div (by omega)).1, (key_div (by omega)).2]; exact ⟨by omega, e4⟩
    · rw [(key_div (by omega)).1, (key_div (by omega)).2]; exact ⟨by omega, e5⟩
    · rw [(key_div (by omega)).1, (key_div (by omega)).2]; exact ⟨by omega, e6⟩
  · intro k hk'
    have hx : k / 120 < 120 := by omega
    have hy : k % 120 < 120 := Nat.mod_lt _ (by norm_num)
    have h := allN_spec (allN_spec kTab _ hx) _ hy
    rw [CFSG.KC.Pack.strictB_eq] at h
    rcases (CFSG.KC.MergeG.bIfT_iff _ _).1 h with h0 | h0
    · exact Or.inl (Nat.eq_of_beq_eq_true h0)
    · obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h0
      have ht := Nat.blt_eq.mp h1
      refine Or.inr ⟨by rw [lt_size]; exact ht, ?_⟩
      obtain ⟨f1, f2, f3, -⟩ := line_facts ht
      rw [lt_bind ht]
      have := pairIn_key hy (by omega) (by omega) f3 h2
      rwa [Nat.div_add_mod] at this

theorem pl_at {x y : Nat} (hx : x < 120) (hy : y < 120) : pairLine[120 * x + y]! = plK PR x y := by
  rw [pl_get (by omega), (key_div hy).1, (key_div hy).2]

theorem o_lt {i j : Nat} (hi : i < 8) (hj : j < 120) : pg 7 127 (O i) j < 120 := by
  have h := allN_spec (allN_spec kPts i hi) j hj
  rw [CFSG.KC.Pack.strictB_eq] at h
  exact Nat.blt_eq.mp ((bAnd_iff _ _).1 h).1

theorem lg_size : lineGens.size = 8 := by
  unfold lineGens
  rw [Array.size_map, o_size]

theorem lg_bind {i : Nat} (hi : i < 8) : lineGens[i]! = unpack 1120 11 (G i) := by
  unfold lineGens
  rw [getElem!_map_of_lt (by rw [o_size]; exact hi)]
  unfold lineImage unpack
  apply Array.ext
  · rw [Array.size_ofFn, Array.size_ofFn]
  · intro t h1 h2
    have ht : t < 1120 := by rwa [Array.size_ofFn] at h1
    rw [Array.getElem_ofFn, Array.getElem_ofFn, ← pgW_eq]
    dsimp only
    obtain ⟨f1, f2, f3, -⟩ := line_facts ht
    rw [lt_bind ht]
    dsimp only
    rw [o_bind i hi _ (by omega), o_bind i hi _ (by omega), pl_at (o_lt hi (by omega))
      (o_lt hi (by omega))]
    exact (Nat.eq_of_beq_eq_true (allN_spec (allN_spec kGens i hi) t ht)).symm

theorem hgG : lineGens.size = 8 ∧ ∀ i < 8, lineGens[i]! = unpack 1120 11 (G i) :=
  ⟨lg_size, fun _ hi => lg_bind hi⟩

theorem lg_get {i y : Nat} (hi : i < 8) (hy : y < 1120) : (lineGens[i]!)[y]! = pgW 11 (G i) y := by
  rw [lg_bind hi, unpackW_get hy, pgW_eq]

theorem line_check : lineCheck = true := by
  unfold lineCheck
  rw [Bool.and_eq_true]
  refine ⟨allLt_of fun t ht => ?_, allLt_of fun a ha => allLt_of fun b hb => ?_⟩
  · obtain ⟨f1, f2, f3, e1, -⟩ := line_facts ht
    rw [lt_bind ht]
    dsimp only
    rw [pl_at (by omega) (by omega), e1]
    simp [f1, f2, f3]
  · by_cases hab : a = b
    · subst hab
      simp
    · rw [ns_bind a ha, ns_bind b hb, bNat_eq]
      have h := allN_spec (allN_spec kPair a ha) b hb
      have hab' : Nat.beq a b = false := by
        cases e : Nat.beq a b
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true e) hab
      unfold pairK at h
      rw [hab'] at h
      dsimp only at h
      cases hB : Nat.beq (CFSG.KC.O8.b8K false (nsK NSP a) (nsK NSP b)) 1
      · have : Nat.beq (CFSG.KC.O8.b8K false (pg 8 255 NSP a) (pg 8 255 NSP b)) 1 = false := hB
        simp [this]
      · rw [hB] at h
        dsimp only at h
        rw [CFSG.KC.Pack.strictB_eq] at h
        obtain ⟨g1, g2⟩ := (bAnd_iff _ _).1 h
        obtain ⟨g2, g3⟩ := (bAnd_iff _ _).1 g2
        obtain ⟨g3, g4⟩ := (bAnd_iff _ _).1 g3
        have hp := Nat.blt_eq.mp g1
        rw [pl_at ha hb, onLine_eq hp, onLine_eq hp, onLine_eq hp, thirdPt_eq ha hb, g2, g3, g4]
        simp [hp]

theorem lineGens_check : lineGensCheck = true := by
  unfold lineGensCheck
  rw [Bool.and_eq_true]
  refine ⟨allLt_of fun j hj => ?_, allLt_of fun i hi => allLt_of fun t ht => ?_⟩
  · rw [lg_size] at hj
    have hp := allN_spec kPermG j hj
    rw [lg_bind hj, CFSG.KC.BfsPin.invCand_unpack hp]
    exact CFSG.KS.Raw.Orb.isInvA_unpack hp
  · have h := allN_spec (allN_spec kOnG i hi) t ht
    rw [CFSG.KC.Pack.strictB_eq] at h
    obtain ⟨h0, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h
    obtain ⟨f1, f2, f3, -⟩ := line_facts ht
    have hu := Nat.blt_eq.mp h0
    rw [lg_get hi ht, lt_bind ht]
    dsimp only
    rw [o_bind i hi _ (by omega), o_bind i hi _ (by omega), o_bind i hi _ f3, onLine_eq hu,
      onLine_eq hu, onLine_eq hu, h1, h2, h3]
    rfl

theorem hw : 1120 + 1 < 2 ^ 11 := by norm_num

theorem lineTrans_check : lineTransCheck = true := by
  unfold lineTransCheck forestOK
  have hr : (#[0] : Array Nat).size = 1 ∧ ∀ c < 1, (#[0] : Array Nat)[c]! = pg 11 (mask 11) (FT 0) c :=
    ⟨rfl, by decide +kernel⟩
  rw [bfsTK_sound hw hgG kCanG hr kFT]
  exact labOKK_sound hw hgG kCanG hr kLT

theorem h0_size : lineH0Arrs.size = 4 := by
  unfold lineH0Arrs
  simp [lineH0Words]

theorem h0_bind : ∀ {j : Nat}, j < 4 → lineH0Arrs[j]! = unpack 1120 11 (H j) := by
  have key : ∀ {j : Nat}, j < 4 →
      wordEqK 1120 11 (mask 11) (pidn 1120 11) G GI 8 lineH0Words[j]! (H j) = true →
      lineH0Arrs[j]! = unpack 1120 11 (H j) := by
    intro j hj hk
    unfold lineH0Arrs
    rw [getElem!_pos _ j (by simp [lineH0Words]; omega)]
    simp only [List.getElem_toArray, List.getElem_map]
    rw [← getElem!_pos lineH0Words j (by simp [lineH0Words]; omega)]
    exact (wordEqK_sound hgG kPermG hk).1
  intro j hj
  match j, hj with
  | 0, _ => exact key (by norm_num) kW0
  | 1, _ => exact key (by norm_num) kW1
  | 2, _ => exact key (by norm_num) kW2
  | 3, _ => exact key (by norm_num) kW3

theorem hgH : lineH0Arrs.size = 4 ∧ ∀ j < 4, lineH0Arrs[j]! = unpack 1120 11 (H j) :=
  ⟨h0_size, fun _ hj => h0_bind hj⟩

theorem lineH0_check : lineH0Check = true := by
  unfold lineH0Check
  simp only [Bool.and_eq_true]
  have hr : lineH0Reps.size = 5 ∧ ∀ c < 5, lineH0Reps[c]! = pg 11 (mask 11) (FH 0) c :=
    ⟨rfl, by decide +kernel⟩
  refine ⟨⟨by decide +kernel, allLt_of fun j hj => ?_⟩, ?_⟩
  · rw [h0_bind hj, unpackW_get (by norm_num)]
    exact beq_iff_eq.2 (Nat.eq_of_beq_eq_true (allN_spec kFix j hj))
  · unfold lineH0Forest
    rw [bfsTK_sound hw hgH kCanH hr kFH]
    exact labOKK_sound hw hgH kCanH hr kLH

theorem mc_eq {l : Nat} (hl : l < 4) : MC l = 1118 := Nat.eq_of_beq_eq_true (allN_spec kC l hl)

theorem mergeCKG_of {l x : Nat} (hl : l < 4) (hx : x < 1120) (hp : mergeParts l x = true)
    (hs : ∀ s < 35, segCG 1120 11 8 G (MC l) 32 (MT l) (MP l) (mA l) (rI l) (rU l) (rV l) s =
      true) :
    mergeCKG 1120 11 8 G 0 x (MC l) 32 35 (rI l) (rU l) (rV l) (MT l) (MP l) (mA l) = true := by
  simp only [mergeParts, CFSG.KC.Pack.band_iff] at hp
  obtain ⟨p1, p2, p3, p4⟩ := hp
  unfold mergeCKG
  rw [p1, CFSG.KS.PackFld.allN_of_forall hs, p2, p3, p4, Nat.blt_eq.mpr hx, mc_eq hl]
  rfl

theorem merge_of {l x : Nat} (hl : l < 4) (hx : x < 1120) (hx0 : 0 ≠ x)
    (hS : searchK 1120 11 2047 12320 8 G 0 x (MC l) (ML l) = true)
    (hM : mergeCKG 1120 11 8 G 0 x (MC l) 32 35 (rI l) (rU l) (rV l) (MT l) (MP l) (mA l) = true)
    (hrep : lineH0Reps[l + 1]! = x) :
    mergeOK 1120 lineGens 0 lineH0Reps[l + 1]! (mergeVals (lineMerge l)) = true := by
  have hc : MC l ≤ 1120 := by
    rw [mc_eq hl]
    norm_num
  have hGp : ∀ i < 8, ∀ y < 1120, (lineGens[i]!)[y]! = pg 11 2047 (G i) y := fun i hi y hy => by
    rw [lg_bind hi, unpackW_get hy]
    rfl
  have hL : mergeVals (lineMerge l) = (List.range (MC l)).map fun k => (rI l k, rU l k, rV l k) := by
    unfold mergeVals lineMerge
    rw [hrep, lineMergeSearch_eq (by norm_num) hx hx0,
      mergeSearchSteps_eq_of_searchK lg_size hGp hS (by norm_num) hc, List.map_map, List.map_map]
    rfl
  rw [hrep]
  exact mergeCKG_sound hw hgG kCanG hL hM

theorem lineMerge_check : lineMergeCheck = true := by
  unfold lineMergeCheck
  refine allLt_of fun l hl => ?_
  match l, hl with
  | 0, _ => refine merge_of ?_ ?_ ?_ kS0 (mergeCKG_of ?_ ?_ kP0 M0.all) rfl <;> norm_num
  | 1, _ => refine merge_of ?_ ?_ ?_ kS1 (mergeCKG_of ?_ ?_ kP1 M1.all) rfl <;> norm_num
  | 2, _ => refine merge_of ?_ ?_ ?_ kS2 (mergeCKG_of ?_ ?_ kP2 M2.all) rfl <;> norm_num
  | 3, _ => refine merge_of ?_ ?_ ?_ kS3 (mergeCKG_of ?_ ?_ kP3 M3.all) rfl <;> norm_num
  | n + 4, h => exact absurd h (by omega)

end CertificateChecks.KernelAS81

end
