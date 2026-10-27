module
public import CFSG.Sporadic.HNSchreier.ArchMaskedChecks
public import CFSG.Sporadic.HNSchreier.ArchKernelChunks
public section
namespace CFSG.Sporadic.HNSchreier.Native.Kernel
open CFSG.Sporadic.Th.Native CFSG.Sporadic.F5.Native

@[expose] def bits32 (n offset : Nat) : Nat := (2^32-1) &&& (n >>> offset)
@[expose] def packedWindow (n start width : Nat) : Nat := (2^width-1) &&& (n >>> start)

theorem bits32_window (n start width offset : Nat) (h : offset+32 ≤ width) :
    bits32 (packedWindow n start width) offset = bits32 n (start+offset) := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [bits32, packedWindow, Nat.testBit_and, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one]
  by_cases hj : j < 32
  · have hw : offset+j < width := by omega
    simp only [hj, hw, decide_true, Bool.true_and, Nat.add_assoc]
  · simp only [hj, decide_false, Bool.false_and]

theorem window_read (width n lo hi i delta : Nat) (hw : width = 9120012)
    (hhi : hi ≤ 1140000) (hlo : lo ≤ i) (hi' : i < hi) (hd : delta ≤ 4) :
    bits32 (packedWindow n (8*(12+8*lo)) (64*(hi-lo))) (64*(i-lo)+8*delta) =
      maskedWordRead width n (12+8*i+delta) := by
  rw [bits32_window _ _ _ _ (by omega)]
  have hk : 12+8*i+delta+3 < width := by omega
  simp only [maskedWordRead, hk, ite_true, bits32]
  congr 2
  omega

@[expose] def dataWindow (_width n lo hi : Nat) : Bool :=
  let piece := packedWindow n (8*(12+8*lo)) (64*(hi-lo))
  allInKernel lo hi fun i => decide (bits32 piece (64*(i-lo)) < 1140000) &&
    decide (bits32 piece (64*(i-lo)+32) < 1140000)

@[expose] def eqWindow (_width n lo hi : Nat) (O : VOrbit) : Bool :=
  let piece := packedWindow n (8*(12+8*lo)) (64*(hi-lo))
  allInKernel lo hi fun i => bits32 piece (64*(i-lo)) == ap O.alpha i &&
    bits32 piece (64*(i-lo)+32) == ap O.beta i

theorem data_window (width n lo hi : Nat) (hw : width = 9120012) (hh : hi ≤ 1140000) :
    (allInKernel lo hi (fun i => decide (maskedWordRead width n (12+8*i) < 1140000) &&
      decide (maskedWordRead width n (12+8*i+4) < 1140000)) = true) ↔
    dataWindow width n lo hi = true := by
  simp only [dataWindow, allInKernel_eq_true]
  have ha (i : Nat) (hl : lo ≤ i) (hh' : i < hi) := window_read width n lo hi i 0 hw hh hl hh' (by omega)
  have hb (i : Nat) (hl : lo ≤ i) (hh' : i < hi) := window_read width n lo hi i 4 hw hh hl hh' (by omega)
  simp only [Nat.add_zero, Nat.mul_zero] at ha
  constructor <;> intro h i hl hh' <;> simpa only [ha i hl hh', hb i hl hh'] using h i hl hh'

theorem eq_window (width n lo hi : Nat) (O : VOrbit) (hw : width = 9120012) (hh : hi ≤ 1140000) :
    (allInKernel lo hi (fun i => maskedWordRead width n (12+8*i) == ap O.alpha i &&
      maskedWordRead width n (12+8*i+4) == ap O.beta i) = true) ↔
    eqWindow width n lo hi O = true := by
  simp only [eqWindow, allInKernel_eq_true]
  have ha (i : Nat) (hl : lo ≤ i) (hh' : i < hi) := window_read width n lo hi i 0 hw hh hl hh' (by omega)
  have hb (i : Nat) (hl : lo ≤ i) (hh' : i < hi) := window_read width n lo hi i 4 hw hh hl hh' (by omega)
  simp only [Nat.add_zero, Nat.mul_zero] at ha
  constructor <;> intro h i hl hh' <;> simpa only [ha i hl hh', hb i hl hh'] using h i hl hh'
end CFSG.Sporadic.HNSchreier.Native.Kernel
