module

public import CFSG.Quasithin.H13.L32NMatNInputs
public import Certificates.Data.Kernel.Mat8P

public section

namespace CFSG.KC.MatNK

open CFSG.Quasithin.H13.MatNCert CFSG.KC.Mat8P

@[expose] def bfsWNT (n : ℕ) (gens : List (List ℕ)) (cap : ℕ) :
    ℕ → NT (List ℕ) → List (List ℕ) → List (List ℕ × List ℕ) → List (List ℕ)
  | 0, _, acc, _ => acc
  | fuel + 1, seen, acc, fr =>
    match fr with
    | [] => acc
    | _ =>
      if cap ≤ acc.length then acc else
      let st := fr.foldl
        (fun (st : NT (List ℕ) × List (List ℕ) × List (List ℕ × List ℕ)) wx =>
          (List.range gens.length).foldl
            (fun (st : NT (List ℕ) × List (List ℕ) × List (List ℕ × List ℕ)) i =>
              let y := mulN (gens.getD i (oneN n)) wx.2
              if memLR st.1 y then st
              else (insLR st.1 y, (i :: wx.1) :: st.2.1, (i :: wx.1, y) :: st.2.2)) st)
        (seen, acc, [])
      bfsWNT n gens cap fuel st.1 st.2.1 st.2.2

@[expose] def elemsOfNT (n : ℕ) (gens : List (List ℕ)) (cap : ℕ := 100000) : List (List ℕ) :=
  (bfsWNT n gens cap 400 (insLR (.tip []) (oneN n)) [[]] [([], oneN n)]).map (evalW n gens)

end CFSG.KC.MatNK

end
