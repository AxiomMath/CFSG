module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeCharData
public import Std.Data.HashSet

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.E6DiagRegular

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.CrossChar

@[expose] def stepCode (row : Array ℕ) (c : ℕ) : ℕ :=
  (List.range 6).foldl (fun acc j => acc + row.getD (c / 256 ^ j % 256) 0 * 256 ^ j) 0

@[expose] def bfsLevel (rows : Array (Array ℕ)) (seen : Std.HashSet ℕ) (front : Array ℕ) :
    Std.HashSet ℕ × Array ℕ :=
  rows.foldl (fun (st : Std.HashSet ℕ × Array ℕ) row =>
    front.foldl (fun (st : Std.HashSet ℕ × Array ℕ) c =>
      let d := stepCode row c
      if st.1.contains d then st else (st.1.insert d, st.2.push d)) st) (seen, #[])

@[expose] def bfs (rows : Array (Array ℕ)) : ℕ → Std.HashSet ℕ → Array ℕ → Std.HashSet ℕ
  | 0, seen, _ => seen
  | n + 1, seen, front =>
    if front.isEmpty then seen else
      let r := bfsLevel rows seen front
      bfs rows n r.1 r.2

@[expose] def e6WKeys (_ : Unit := ()) : List ℕ :=
  let T := RootTables.ofCert e6Certificate
  let rows : Array (Array ℕ) := T.imgs.toArray.map List.toArray
  let id0 := encodeT (List.range Tag.E6.rank)
  let seen := bfs rows 60 (({} : Std.HashSet ℕ).insert id0) #[id0]
  (seen.toArray.qsort (· < ·)).toList

@[expose] def castL (vec : List ℕ) : List ℤ := vec.map fun x : ℕ => (x : ℤ)

@[expose] def pairZ (T : RootTables) (k : ℕ) (v : List ℤ) : ℤ := dotL (T.vecs.getD k []) v

@[expose] def regularL (T : RootTables) (nr : ℕ) (v₁ v₂ : List ℤ) : Bool :=
  (List.range nr).all fun k => !(decide (pairZ T k v₁ % 3 = 0) && decide (pairZ T k v₂ % 3 = 0))

@[expose] def fixesRootL (C : RootCertificate .E6) (T : RootTables) (t : List ℕ) : Bool :=
  (List.range C.roots.length).any fun k =>
    decide (dotL (T.vecs.getD k []) (hsL T t) = T.hts.getD k 0) &&
      (List.ofFn (C.tupleVec t (C.root k)) == List.ofFn (C.root k))

@[expose] def e6RegFixMain (C : RootCertificate .E6) (T : RootTables)
    (elems : List (List ℕ)) : Bool :=
  (List.range 729).all fun n₁ =>
    let vec₁ := digits3 .E6 n₁
    let partners := (List.range 729).filter fun n₂ =>
      regularL T C.roots.length (castL vec₁) (castL (digits3 .E6 n₂))
    partners.isEmpty ||
      (let W₁ := elems.filter (chiTestL .E6 T vec₁)
       partners.all fun n₂ =>
        let vec₂ := digits3 .E6 n₂
        W₁.all fun t => !(chiTestL .E6 T vec₂ t) || !(e6ScTest C vec₁ t) || fixesRootL C T t)

@[expose] def e6RegFixCheck (_ : Unit := ()) : Bool :=
  let S : StabCert3 := ⟨[], [], e6WKeys ()⟩
  S.check e6Certificate && e6RegFixMain e6Certificate (RootTables.ofCert e6Certificate)
    (S.elems .E6)

end CFSG.LieType.SeitzGeneration.ExcWideThree.E6DiagRegular
