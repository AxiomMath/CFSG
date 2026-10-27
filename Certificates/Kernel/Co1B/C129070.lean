module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co1F0Check
public meta import CFSG.Sporadic.Co1Block.TwoAData
public meta import CFSG.Sporadic.Co1Block.IotaData
public meta import CFSG.Sporadic.Co1Block.Iota
public meta import CFSG.Sporadic.Co1Block.CentCheck
public meta import CFSG.Sporadic.Schreier.Co1ChainCheck
public meta import CFSG.Sporadic.Schreier.Co1StabCheck
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import CFSG.Sporadic.Schreier.Co1StabData
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Co1.Involutions
public meta import Certificates.Data.CFSGNative.Co1.TwoB
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public import Certificates.Kernel.Co1B.Chk129070
public import Certificates.Kernel.Co1B.Iota
public import Certificates.Kernel.SporSch.Co1.Packed
public import CFSG.Certificates.Kernel.SporSch.Co1CentSound
public import CFSG.Certificates.Kernel.SporSch.Co1HeisSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.C129070

open CFSG.KS.SporSch.M24 CFSG.KS.Raw CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block
  CFSG.Sporadic.Co1Block.Native CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
  CertificateChecks.KernelSporSch.Co1Packed

theorem iotaA_u : iotaARows = unpack 24 24 IA :=
  CertificateChecks.KernelCo1B.iotaA_eq.trans (unpackR_eq_unpack _)

theorem aR_u' : aR = unpack 24 24 CFSG.KD.Co1B.SA := aR_u

theorem bR_u' : bR = unpack 24 24 CFSG.KD.Co1B.SB := bR_u

theorem base3 {M : Nat → Nat} {tR : Rows} {P : Nat} (ht : tR = unpack 24 24 P)
    (h : (Nat.beq (M 0) CFSG.KD.Co1B.SA && Nat.beq (M 1) CFSG.KD.Co1B.SB && Nat.beq (M 2) P) = true) :
    [aR, bR, tR] = (List.range 3).map fun i => unpack 24 24 (M i) := by
  simp only [Bool.and_eq_true] at h
  have hr : List.range 3 = [0, 1, 2] := rfl
  rw [hr, List.map_cons, List.map_cons, List.map_cons, List.map_nil, aR_u', bR_u', ht,
    Nat.eq_of_beq_eq_true h.1.1, Nat.eq_of_beq_eq_true h.1.2, Nat.eq_of_beq_eq_true h.2]

@[expose] noncomputable def L1 : List Rows := (List.range F1.N).map fun i => unpack 24 24 (F1.M i)

@[expose] noncomputable def L1I : List Rows := (List.range F1.N).map fun i => unpack 24 24 (F1.MI i)

@[expose] noncomputable def L2 : List Rows := (List.range F2.N).map fun i => unpack 24 24 (F2.M i)

@[expose] noncomputable def L2I : List Rows := (List.range F2.N).map fun i => unpack 24 24 (F2.MI i)

theorem hN : F1.N = 96 ∧ F2.N = 29 := by
  have h := kN
  simp only [Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem base_eq : [aR, bR, iotaARows] = (List.range 3).map fun i => unpack 24 24 (F1.M i) :=
  base3 iotaA_u kb

theorem hI : f0Bidx.all (fun j => decide (3 < j) && decide (j ≤ F1.N)) = true ∧ f0IB ≤ F1.N ∧
    f0S1 ≤ F1.N ∧ f0S2 ≤ F1.N := by
  have h := kI
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem hD1 : brayRows iotaARows f0D1 = (L1, L1I, true) := by
  have h := dagWK_sound base_eq kD1
  rwa [decWords_encWordK] at h

theorem hB : brayElts (L1, L1I, true) f0Bidx =
    (List.range f0Bidx.length).map fun i => unpack 24 24 (F2.M i) := by
  apply List.ext_getElem (by simp [brayElts])
  intro i h₁ h₂
  have h₁' : i < f0Bidx.length := by simpa [brayElts] using h₁
  simp only [brayElts, List.getElem_map, List.getElem_range]
  have hj := List.all_eq_true.1 hI.1 _ (List.getElem_mem h₁')
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
  have hb : F2.M i = F1.M (f0Bidx[i] - 1) := by
    simpa using bindFromK_sound (k := 0) kBind i h₁'
  have e : L1.getD (f0Bidx[i] - 1) (one ()) = unpack 24 24 (F1.M (f0Bidx[i] - 1)) :=
    getD_range_unpack (by omega)
  rw [e, hb]

theorem hD2 : dag (brayElts (L1, L1I, true) f0Bidx) f0D2 = (L2, L2I, true) := by
  have h := dagWK_sound hB kD2
  rwa [decWords_encWordK] at h

theorem L1_len : L1.length = F1.N := by simp [L1]

theorem L2_len : L2.length = 29 := by simp [L2, hN.2]

theorem bray_comm {l : List Nat} (hl : ∀ j ∈ l, j ∈ f0Bidx) {P : Nat} (h : commK F1.M P l = true) :
    (brayElts (L1, L1I, true) l).all (fun g => mul g (unpack 24 24 P) == mul (unpack 24 24 P) g) =
      true := by
  rw [List.all_eq_true]
  intro g hg
  simp only [brayElts, List.mem_map] at hg
  obtain ⟨j, hj, rfl⟩ := hg
  have hr := List.all_eq_true.1 hI.1 j (hl j hj)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
  have e : L1.getD (j - 1) (one ()) = unpack 24 24 (F1.M (j - 1)) := getD_range_unpack (by omega)
  rw [e, ← MatL.unpack_mulK, ← MatL.unpack_mulK, commK_sound h j hj]
  exact beq_self_eq_true _

open Certificates in
open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic in
theorem c129070 : f0Check () = true := by
  have hC := kC
  have hM := kM
  simp only [Bool.and_eq_true] at hC hM
  obtain ⟨hCa, hCb⟩ := hC
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hab, hbb⟩, hb1⟩, hba⟩, hs1a⟩, hs1b⟩, hs2b⟩, hs2ab⟩, h27⟩, h28⟩ := hM
  have i1 := hI.2.1
  have i2 := hI.2.2.1
  have i3 := hI.2.2.2
  simp only [f0IB, f0S1, f0S2] at i1 i2 i3
  have gB : L1.getD (f0IB - 1) (one ()) = unpack 24 24 PBf := getD_range_unpack (by
    unfold f0IB
    omega)
  have gS1 : L1.getD (f0S1 - 1) (one ()) = unpack 24 24 PS1 := getD_range_unpack (by
    unfold f0S1
    omega)
  have gS2 : L1.getD (f0S2 - 1) (one ()) = unpack 24 24 PS2 := getD_range_unpack (by
    unfold f0S2
    omega)
  have g27 : L2.getD (L2.length - 2) (one ()) = unpack 24 24 (F2.M 27) := by
    rw [L2_len]
    exact getD_range_unpack (by rw [hN.2]; decide)
  have g28 : L2.getD (L2.length - 1) (one ()) = unpack 24 24 (F2.M 28) := by
    rw [L2_len]
    exact getD_range_unpack (by rw [hN.2]; decide)
  have fa := bray_comm (fun j hj => List.mem_of_mem_take hj) hCa
  have fb := bray_comm (fun j hj => List.mem_of_mem_drop hj) hCb
  rw [← iotaA_u] at fa
  rw [← gB] at fb
  have fI := hI.1
  rw [← L1_len] at fI
  have fIB : decide (f0IB ≤ L1.length) = true := by
    rw [L1_len]
    exact decide_eq_true hI.2.1
  have fS1 : decide (f0S1 ≤ L1.length) = true := by
    rw [L1_len]
    exact decide_eq_true hI.2.2.1
  have fS2 : decide (f0S2 ≤ L1.length) = true := by
    rw [L1_len]
    exact decide_eq_true hI.2.2.2
  unfold f0Check
  simp only [hD1, hD2, fI, fIB, fS1, fS2, fa, fb, Bool.true_and, Bool.and_true]
  rw [gB, gS1, gS2, g27, g28, iotaA_u, aR_u', bR_u']
  simp only [← MatL.unpack_mulK, ← MatL.unpack_idM, validRows_unpack', beq_of_K hab, beq_of_K hbb,
    hb1, hba, beq_of_K hs1a, beq_of_K hs1b, beq_of_K hs2b, beq_of_K hs2ab, beq_of_K h27,
    beq_of_K h28, Bool.and_self]

end CertificateChecks.KernelCo1B.C129070

end
