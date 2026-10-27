module

public import CFSG.Monster.B.TwoA.Census.NatCert
public import Std.Data.HashMap

public section

namespace CFSG.KC.Bfs

open CFSG.Monster.B.TwoA.Census

@[expose] def natBfsFL (act : ℕ → ℕ → ℕ) (i : ℕ)
    (acc : Array ℕ × Array ℕ × Array ℕ × List (ℕ × ℕ) × Array ℕ) (k : ℕ) :
    Array ℕ × Array ℕ × Array ℕ × List (ℕ × ℕ) × Array ℕ :=
  let (pts, par, lab, idx, row) := acc
  let y := act k pts[i]!
  match idx.lookup y with
  | some j => (pts, par, lab, idx, row.push j)
  | none => (pts.push y, par.push i, lab.push k, (y, pts.size) :: idx, row.push pts.size)

@[expose] def natBfsStepL (act : ℕ → ℕ → ℕ) (ngen : ℕ) (i : ℕ)
    (st : Array ℕ × Array ℕ × Array ℕ × List (ℕ × ℕ)) :
    Array ℕ × Array ℕ × Array ℕ × List (ℕ × ℕ) × Array ℕ :=
  (List.range ngen).foldl (natBfsFL act i) (st.1, st.2.1, st.2.2.1, st.2.2.2, #[])

@[expose] def natBfsLoopL (act : ℕ → ℕ → ℕ) (ngen : ℕ) :
    ℕ → ℕ → Array ℕ → Array (Array ℕ) → Array ℕ → Array ℕ → List (ℕ × ℕ) → NatCert
  | 0, _, pts, edges, par, lab, _ => ⟨pts, edges, par, lab⟩
  | fuel + 1, i, pts, edges, par, lab, idx =>
    if i < pts.size then
      let (pts', par', lab', idx', row) := natBfsStepL act ngen i (pts, par, lab, idx)
      natBfsLoopL act ngen fuel (i + 1) pts' (edges.push row) par' lab' idx'
    else ⟨pts, edges, par, lab⟩

@[expose] def natBfsL (act : ℕ → ℕ → ℕ) (ngen : ℕ) (root : ℕ) (fuel : ℕ) : NatCert :=
  natBfsLoopL act ngen fuel 0 #[root] #[] #[0] #[0] [(root, 0)]

@[expose] def orbitSearchL (act : ℕ → ℕ → ℕ) (nh N : ℕ) : List (ℕ × NatCert) :=
  ((List.range N).foldl (fun (st : Array Bool × List (ℕ × NatCert)) i =>
      if st.1[i]! then st else
        let c := natBfsL act nh i N
        (c.pts.foldl (fun cov p => cov.set! p true) st.1, (i, c) :: st.2))
    (Array.replicate N false, [])).2.reverse

end CFSG.KC.Bfs
