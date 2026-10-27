module
public import CFSG.Sporadic.HNSchreier.PackedWindowChecks
public import CFSG.Sporadic.HNSchreier.PackedOrbitAccess

public section
namespace CFSG.Sporadic.HNSchreier.Native.Kernel

@[expose] def orbitPairCheck (xa xb a b : Nat) : Bool :=
  xa == a && xb == b && decide (a < 1140000) && decide (b < 1140000)

theorem orbitPairCheck_sound {xa xb a b : Nat} (h : orbitPairCheck xa xb a b = true) :
    (decide (xa < 1140000) && decide (xb < 1140000)) = true ∧
      (xa == a && xb == b) = true := by
  simp only [orbitPairCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h ⊢
  rcases h with ⟨⟨⟨ha, hb⟩, hla⟩, hlb⟩
  exact ⟨⟨by omega, by omega⟩, ha, hb⟩

@[expose] def orbitLeafCheck (n start count a b : Nat) : Bool :=
  let piece := packedWindow n (96+64*start) (64*count)
  allInKernel 0 count fun i =>
    orbitPairCheck (bits32 piece (64*i)) (bits32 piece (64*i+32))
      ((a >>> (32*i)) % 2^32) ((b >>> (32*i)) % 2^32)

@[expose] def orbitTreeCheck (n start : Nat) : OrbitNats → OrbitNats → Bool
  | .leaf wa ca a, .leaf wb cb b =>
      wa == 32 && wb == 32 && ca == cb && orbitLeafCheck n start ca a b
  | .branch ka al ar, .branch kb bl br =>
      ka == kb && orbitTreeCheck n start al bl && orbitTreeCheck n (start+ka) ar br
  | _, _ => false

theorem orbitLeafCheck_sound {n start count a b i : Nat}
    (h : orbitLeafCheck n start count a b = true) (hi : i < count) :
    orbitPairCheck (bits32 n (96+64*(start+i))) (bits32 n (96+64*(start+i)+32))
      ((a >>> (32*i)) % 2^32) ((b >>> (32*i)) % 2^32) = true := by
  unfold orbitLeafCheck at h
  have h := allInKernel_eq_true.mp h i (by omega) hi
  rw [bits32_window _ _ _ _ (by omega), bits32_window _ _ _ _ (by omega)] at h
  have ha : 96+64*start+64*i = 96+64*(start+i) := by omega
  have hb : 96+64*start+(64*i+32) = 96+64*(start+i)+32 := by omega
  simpa only [ha, hb] using h

theorem orbitTreeCheck_sound (A B : OrbitNats) (ha : A.valid = true)
    (hb : B.valid = true) (n start : Nat) (h : orbitTreeCheck n start A B = true)
    (i : Nat) (hi : i < A.size) :
    orbitPairCheck (bits32 n (96+64*(start+i))) (bits32 n (96+64*(start+i)+32))
      (UInt32.ofNat (A.get i)).toNat (UInt32.ofNat (B.get i)).toNat = true := by
  induction A generalizing B start i with
  | leaf wa ca a =>
    cases B with
    | branch => simp [orbitTreeCheck] at h
    | leaf wb cb b =>
      simp only [orbitTreeCheck, Bool.and_eq_true, beq_iff_eq] at h
      rcases h with ⟨⟨⟨rfl, rfl⟩, rfl⟩, h⟩
      change i < ca at hi
      have h := orbitLeafCheck_sound h hi
      simpa only [OrbitNats.get, OrbitNats.size, hi, ite_true,
        UInt32.toNat_ofNat', Nat.mod_mod] using h
  | branch k al ar ihl ihr =>
    cases B with
    | leaf => simp [orbitTreeCheck] at h
    | branch l bl br =>
      simp only [orbitTreeCheck, Bool.and_eq_true, beq_iff_eq] at h
      rcases h with ⟨⟨rfl, hl⟩, hr⟩
      simp only [OrbitNats.valid, Bool.and_eq_true, beq_iff_eq] at ha hb
      by_cases hik : i < k
      · simpa only [OrbitNats.get, hik, ite_true] using
          ihl bl ha.1.1 hb.1.1 start hl i (by omega)
      · have h := ihr br ha.1.2 hb.1.2 (start+k) hr (i-k) (by
          simp only [OrbitNats.size] at hi
          omega)
        have he : start+k+(i-k) = start+i := by omega
        simpa only [OrbitNats.get, hik, ite_false, he] using h

theorem orbitTreeCheck_branch (n start ka kb : Nat) (al ar bl br : OrbitNats) :
    orbitTreeCheck n start (.branch ka al ar) (.branch kb bl br) = true ↔
      ka = kb ∧ orbitTreeCheck n start al bl = true ∧
        orbitTreeCheck n (start+ka) ar br = true := by
  simp only [orbitTreeCheck, Bool.and_eq_true, beq_iff_eq, and_assoc]

theorem orbitTreeCheck_masked_sound (A B : OrbitNats) (ha : A.valid = true)
    (hb : B.valid = true) (width n : Nat) (hw : width = 9120012)
    (hs : A.size = 1140000) (h : orbitTreeCheck n 0 A B = true) :
    allInKernel 0 1140000 (fun i =>
      maskedWordRead width n (12+8*i) == (UInt32.ofNat (A.get i)).toNat &&
      maskedWordRead width n (12+8*i+4) == (UInt32.ofNat (B.get i)).toNat) = true := by
  apply allInKernel_eq_true.mpr
  intro i _ hi
  have ht := orbitTreeCheck_sound A B ha hb n 0 h i (by omega)
  have h1 : 12+8*i+3 < width := by omega
  have h2 : 12+8*i+4+3 < width := by omega
  have e1 : 8*(12+8*i) = 96+64*i := by omega
  have e2 : 8*(12+8*i+4) = 96+64*i+32 := by omega
  simpa only [maskedWordRead, h1, h2, ite_true, bits32, e1, e2, Nat.zero_add]
    using (orbitPairCheck_sound ht).2

theorem orbitTreeCheck_bounds_sound (A B : OrbitNats) (ha : A.valid = true)
    (hb : B.valid = true) (width n : Nat) (hw : width = 9120012)
    (hs : A.size = 1140000) (h : orbitTreeCheck n 0 A B = true) :
    allInKernel 0 1140000 (fun i =>
      decide (maskedWordRead width n (12+8*i) < 1140000) &&
      decide (maskedWordRead width n (12+8*i+4) < 1140000)) = true := by
  apply allInKernel_eq_true.mpr
  intro i _ hi
  have ht := orbitTreeCheck_sound A B ha hb n 0 h i (by omega)
  have h1 : 12+8*i+3 < width := by omega
  have h2 : 12+8*i+4+3 < width := by omega
  have e1 : 8*(12+8*i) = 96+64*i := by omega
  have e2 : 8*(12+8*i+4) = 96+64*i+32 := by omega
  simpa only [maskedWordRead, h1, h2, ite_true, bits32, e1, e2, Nat.zero_add]
    using (orbitPairCheck_sound ht).1

@[expose] def orbitArchiveHeader (width n : Nat) : Bool :=
  width == 12+8*1140000 &&
    ((List.range 8).map fun k => ((KernelBytes.packedFast width n).get k).toNat) ==
      "HNPAIR01".toList.map Char.toNat &&
    maskedWordRead width n 8 == 1140000

theorem orbitTreeCheck_certificate (A B : OrbitNats) (ha : A.valid = true)
    (hb : B.valid = true) (width n : Nat) (hw : width = 9120012)
    (hs : A.size = 1140000) (hh : orbitArchiveHeader width n = true)
    (h : orbitTreeCheck n 0 A B = true) :
    archDataChecksMasked width n = true ∧
      allInKernel 0 1140000 (fun i =>
        maskedWordRead width n (12+8*i) == (UInt32.ofNat (A.get i)).toNat &&
        maskedWordRead width n (12+8*i+4) == (UInt32.ofNat (B.get i)).toNat) = true := by
  constructor
  · change orbitArchiveHeader width n && _ = true
    rw [Bool.and_eq_true]
    exact ⟨hh, orbitTreeCheck_bounds_sound A B ha hb width n hw hs h⟩
  · exact orbitTreeCheck_masked_sound A B ha hb width n hw hs h

end CFSG.Sporadic.HNSchreier.Native.Kernel
