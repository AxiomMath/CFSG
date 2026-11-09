module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.U43ExtCheck
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U43Pair
public import Certificates.Kernel.U43C.Glue
import CFSG.Certificates.Kernel.Common.Harness

public section

open CFSG.AGLEmbeddingD2.Wilson.Coordinator.U43

namespace Certificates

open CFSG.KC.Loop CFSG.KD.U43 CFSG.KD.U43C CFSG.KC.U43 CFSG.KC.U43C CFSG.KC.G2Three
  CFSG.RankThree.PartTwo.Sec4.Item434RemU43

@[expose] def c12640Cands : List ℕ := [1, 3, 5, 7, 17, 19, 23, 27, 47, 64]

@[expose] noncomputable def c12640O3 (A : ℕ) : Bool :=
  !(Nat.beq A ONEF) && Nat.beq (MF A (MF A A)) ONEF

@[expose] noncomputable def c12640Z (A Z : ℕ) : Bool :=
  Nat.beq A ONEF || (Nat.beq A Z || Nat.beq A (MF Z Z))

@[expose] noncomputable def c12640E9 (Z B C : ℕ) : Bool :=
  [ONEF, Z, MF Z Z].any fun X => [ONEF, B, MF B B].any fun Y => Nat.beq C (MF X Y)

@[expose] noncomputable def c12640Ext (A Z S s : ℕ) : Bool :=
  !(c12640O3 A) || c12640Z A Z ||
    (Nat.blt s 729 && c12640O3 S && Nat.beq (MF S A) (MF A S) && !(c12640E9 Z A S))

theorem c12640_ok : allBelow 729 12 (fun t =>
    c12640Cands.any fun s => c12640Ext (UXF t) (UXF uZ) (UXF s) s) = true := by
  quickRfl

theorem c12640_o3 {p : ℕ} (hp : DatF (uAt p) (UXF p)) : isOrd3 p = c12640O3 (UXF p) := by
  unfold isOrd3 cube4 sq4 c12640O3
  rw [beqDF hp oneDF, beqDF (mulDF hp (mulDF hp hp)) oneDF]

theorem c12640_extOK {t s : ℕ} (ht : t < 729) (hs : s < 729)
    (h : c12640Ext (UXF t) (UXF uZ) (UXF s) s = true) : extOK t = true := by
  have ha := c9575_dat ht
  have hb := c9575_dat hs
  have hz : DatF zc (UXF uZ) := c9575_dat (t := uZ) (by decide)
  have e2 : [one4, zc, zc2].contains (uAt t) = c12640Z (UXF t) (UXF uZ) := by
    simp only [List.contains_cons, List.contains_nil, Bool.or_false, zc2, sq4]
    rw [beqDF ha oneDF, beqDF ha hz, beqDF ha (mulDF hz hz), c12640Z]
  have e3 : commutes4 (uAt s) (uAt t) = Nat.beq (MF (UXF s) (UXF t)) (MF (UXF t) (UXF s)) := by
    unfold commutes4
    rw [beqDF (mulDF hb ha) (mulDF ha hb)]
  have e4 : (e9Elems zc (uAt t)).contains (uAt s) = c12640E9 (UXF uZ) (UXF t) (UXF s) := by
    simp only [e9Elems, List.contains_toArray, sq4, c12640E9, List.flatMap_cons,
      List.flatMap_nil, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.append_nil, List.contains_cons, List.contains_nil, List.any_cons, List.any_nil,
      Bool.or_false]
    rw [beqDF hb (mulDF oneDF oneDF), beqDF hb (mulDF oneDF ha),
      beqDF hb (mulDF oneDF (mulDF ha ha)), beqDF hb (mulDF hz oneDF), beqDF hb (mulDF hz ha),
      beqDF hb (mulDF hz (mulDF ha ha)), beqDF hb (mulDF (mulDF hz hz) oneDF),
      beqDF hb (mulDF (mulDF hz hz) ha), beqDF hb (mulDF (mulDF hz hz) (mulDF ha ha))]
    simp only [Bool.or_assoc]
  unfold c12640Ext at h
  unfold extOK
  rw [c12640_o3 ha, e2]
  cases ho : c12640O3 (UXF t) <;> cases hzz : c12640Z (UXF t) (UXF uZ) <;>
    simp only [ho, hzz, Bool.not_true, Bool.not_false, Bool.true_or, Bool.false_or,
      Bool.or_true] at h ⊢
  simp only [Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨-, hs3⟩, hsc⟩, hse⟩ := h
  refine List.any_eq_true.2 ⟨s, List.mem_range.2 hs, ?_⟩
  rw [isOrd3Arr_getD hs, c12640_o3 hb, e3, e4, hs3, hsc, hse]
  rfl

theorem certificate12640 : CFSG.AGLEmbeddingD2.Wilson.Coordinator.U43.uExtCheck = true := by
  unfold uExtCheck
  refine List.all_eq_true.2 fun t ht => ?_
  have ht' := List.mem_range.1 ht
  obtain ⟨s, hsC, hs⟩ := List.any_eq_true.1 (allBelow_g2 c12640_ok (by decide) t ht')
  have hs7 : s < 729 := by
    simp only [c12640Cands, List.mem_cons, List.not_mem_nil, or_false] at hsC
    omega
  exact c12640_extOK ht' hs7 hs

end Certificates
