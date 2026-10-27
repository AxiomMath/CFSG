module

public import CFSG.Quasithin.H13.L32NM22Inputs
public import Certificates.Data.Kernel.Mat12P

public section

namespace CFSG.KC.M22K

open CFSG.KC.Mat8P CFSG.KC.Mat12P

@[expose] def orbBfsT (gs : List (List ℕ)) :
    ℕ → NT ℕ → List (ℕ × List ℕ) → List (ℕ × List ℕ) → List (ℕ × List ℕ)
  | 0, _, acc, _ => acc
  | fuel + 1, seen, acc, fr =>
    match fr with
    | [] => acc
    | _ =>
      let st := fr.foldl
        (fun (st : NT ℕ × List (ℕ × List ℕ) × List (ℕ × List ℕ)) uw =>
          (List.range gs.length).foldl
            (fun (st : NT ℕ × List (ℕ × List ℕ) × List (ℕ × List ℕ)) i =>
              let y := mvNR (gs.getD i []) uw.1
              if memP st.1 y then st
              else (insP st.1 y, (y, i :: uw.2) :: st.2.1, (y, i :: uw.2) :: st.2.2)) st)
        (seen, acc, [])
      orbBfsT gs fuel st.1 st.2.1 st.2.2

end CFSG.KC.M22K

end
