module

public import Certificates.Data.CFSGNative.MonsterB.PacketData
public import CFSG.Certificates.Kernel.BabyMonster.PktSound
public import CFSG.Certificates.Kernel.BabyMonster.PktShapeSound
public import CFSG.Certificates.Kernel.BabyMonster.PktBind.Check0
public import CFSG.Certificates.Kernel.BabyMonster.PktBind.Shape0
public import CFSG.Certificates.Kernel.BabyMonster.PktBind.Shape1
public import Certificates.Kernel.BabyMonster.ForallLt
import CFSG.Certificates.Kernel.Common.Harness
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

public section

namespace CertificateChecks.KernelBM.PktShape

open CFSG.KC.YModel CFSG.KC.BM CFSG.KC.BM.Pkt

theorem lines_ok : ∀ i < 48, lineOK (lineOf CFSG.KD.PktBind.CH CFSG.KD.PktBind.S i) = true := by
  forall_lt_consts CFSG.KD.PktBind.ln 48

theorem pieces_ok : piecesOK CFSG.KD.PktBind.CH = true := by quickRfl

theorem shapes_ok : ∀ i < 48, shapeOK (lineOf CFSG.KD.PktBind.CH CFSG.KD.PktBind.S i) = true := by
  forall_lt_consts CFSG.KD.PktBind.shape 48

theorem packetRows_eq : CFSG.Monster.B.Native.packetRows () =
    ((List.range 48).map fun i => lineRows (lineOf CFSG.KD.PktBind.CH CFSG.KD.PktBind.S i)).toArray := by
  rw [CFSG.Monster.B.Native.packetRows, CFSG.KD.PktBind.eq]
  exact decodeRows_text pieces_ok CFSG.KD.PktBind.lines CFSG.KD.PktBind.nlines lines_ok

theorem packetShapeOK_true : CFSG.Monster.B.Native.packetShapeOK () = true := by
  unfold CFSG.Monster.B.Native.packetShapeOK
  rw [packetRows_eq, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true_iff_forall_mem,
    List.size_toArray, List.length_map, List.length_range]
  refine ⟨rfl, fun g hg => ?_⟩
  rw [List.mem_toArray, List.mem_map] at hg
  obtain ⟨i, hi, rfl⟩ := hg
  obtain ⟨h1, h2⟩ := shape_rows (shapes_ok i (List.mem_range.1 hi))
  rw [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true_iff_forall_mem]
  exact ⟨h1, fun r hr => h2 r (Array.mem_toList_iff.2 hr)⟩

theorem foldl_eq_of_mem {α β : Type} {f g : β → α → β} : ∀ (l : List α) (b : β),
    (∀ a ∈ l, ∀ b, f b a = g b a) → l.foldl f b = l.foldl g b
  | [], _, _ => rfl
  | a :: l, b, h => by
    rw [List.foldl_cons, List.foldl_cons, h a List.mem_cons_self b]
    exact foldl_eq_of_mem l _ (fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem packetEntryCount_eq' : CFSG.Monster.B.Native.packetEntryCount () = 259183 := by
  unfold CFSG.Monster.B.Native.packetEntryCount
  rw [packetRows_eq, List.foldl_toArray' _ _ _ rfl, List.foldl_map]
  rw [← countOK_sound CFSG.KD.PktBind.count]
  refine foldl_eq_of_mem _ _ (fun i hi n => ?_)
  rw [← Array.foldl_toList, foldl_size_add, rowsCount_lineRows (lines_ok i (List.mem_range.1 hi))]

end CertificateChecks.KernelBM.PktShape

end
