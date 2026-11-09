module

public import Certificates.Data.Kernel.Census.CatFacts.PkDefs
public import Certificates.Data.Kernel.PermCent.CV

public section

namespace CFSG.Certificates.Kernel.PkEnum.Seal

open CFSG.KS.PK

@[expose] def pkOKB (n : Nat) (p : Nat × Nat) : Bool :=
  (List.range n).all fun i => decide (fd (wd n) p.1 i < n) && decide (fd (wd n) p.2 i < n) &&
    decide (fd (wd n) p.2 (fd (wd n) p.1 i) = i) && decide (fd (wd n) p.1 (fd (wd n) p.2 i) = i)

theorem pkOKB_iff (n : Nat) (p : Nat × Nat) : pkOKB n p = true ↔ PkOK n p := by
  simp only [pkOKB, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, PkOK,
    and_assoc]

@[expose] def mkVP (n : Nat) (p : Nat × Nat) : VP n :=
  if h : pkOKB n p = true then ⟨p, (pkOKB_iff n p).1 h⟩ else oneV n

theorem mkVP_val {n : Nat} (s : VP n) : mkVP n s.1 = s := by
  unfold mkVP
  rw [dif_pos ((pkOKB_iff n s.1).2 s.2)]

theorem map_mkVP_val {n : Nat} (l : List (VP n)) : (l.map Subtype.val).map (mkVP n) = l := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id l]
  exact List.map_congr_left fun s _ => mkVP_val s

theorem eq_map_mkVP {n : Nat} {l : List (VP n)} {L : List (Nat × Nat)}
    (h : l.map Subtype.val = L) : l = L.map (mkVP n) := by
  rw [← h, map_mkVP_val]

@[expose] def codeAt {n : Nat} (l : List (VP n)) (L : List (Nat × Nat)) (k : Nat) : Bool :=
  (l.map Subtype.val).getD k (0, 0) == L.getD k (0, 0)

theorem eq_map_mkVP_of_getD {n : Nat} {l : List (VP n)} {L : List (Nat × Nat)}
    (hlen : l.length = L.length) (h : ∀ k < L.length, codeAt l L k = true) :
    l = L.map (mkVP n) := by
  refine eq_map_mkVP (List.ext_getElem (by rw [List.length_map, hlen]) fun k h1 h2 => ?_)
  have := h k h2
  rw [codeAt, beq_iff_eq, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2, Option.getD_some, Option.getD_some] at this
  exact this

@[expose] def schHead {n k : Nat} (Sc : List (VP n)) (base : Vector (Fin n) k) : Bool :=
  (Sc.filter fun s => base.toList.all fun b => decide (pkp s b = b)).all fun s =>
    CFSG.Certificates.schreierPermEq (pkp s) 1

@[expose] def schStep {n k : Nat} (Sc : List (VP n)) (base : Vector (Fin n) k) (i : Fin k)
    (e : Fin n × VP n) : Bool :=
  (stepsV Sc base i.val).all fun s =>
    match (levelV Sc base i).entries.lookup (pkp s e.1) with
    | none => false
    | some ty => siftV (levelsV Sc base (i.val + 1)) (mulV (mulV (invV ty) s) e.2)

@[expose] def schLev {n k : Nat} (Sc : List (VP n)) (base : Vector (Fin n) k) (i : Fin k) :
    Bool :=
  (levelV Sc base i).entries.all (schStep Sc base i)

theorem schV_eq {n k : Nat} (Sc : List (VP n)) (base : Vector (Fin n) k) :
    schV Sc base = (schHead Sc base && (List.finRange k).all (schLev Sc base)) := rfl

theorem schV_of {n k : Nat} {Sc : List (VP n)} {base : Vector (Fin n) k}
    (h0 : schHead Sc base = true) (h : ∀ i : Fin k, schLev Sc base i = true) :
    schV Sc base = true := by
  rw [schV_eq, h0, Bool.true_and, List.all_eq_true]
  exact fun i _ => h i

open CFSG.Certificates.Kernel.PkCV in
@[expose] noncomputable def elemsCL {n : Nat} [Small n] (Q : CFSG.Certificates.RawSchreierDatum n)
    (L : List (Nat × Nat)) : List (CV n) :=
  productsC ((List.finRange Q.baseCount).map fun i =>
    (transV (levelV (L.map (mkVP n)) Q.base i)).map toCV)

open CFSG.Certificates.Kernel.PkCV in
theorem elemsC_eq_elemsCL {n : Nat} [Small n] {Q : CFSG.Certificates.RawSchreierDatum n}
    {L : List (Nat × Nat)} (h : strongV Q = L.map (mkVP n)) : elemsC Q = elemsCL Q L := by
  unfold elemsC elemsCL
  rw [h]

end CFSG.Certificates.Kernel.PkEnum.Seal

end
