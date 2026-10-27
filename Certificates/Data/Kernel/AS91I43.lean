module

public import Certificates.Data.Kernel.AS91S42
public import Certificates.Data.Kernel.HJ12KT
public import CFSG.Quasithin.H13.AS91Sec4ThreeInputs

public section

noncomputable section

namespace Certificates.Kernel.AS91I43

open CFSG.KC.Mat12P CFSG.KC.Mat8P Certificates.Kernel.HJ12K Certificates.Kernel.AS91S42
open CFSG.Quasithin.H13.AS91.Two

@[expose] def redB (B : List ℕ) (x : ℕ) : ℕ :=
  B.foldl (fun acc b => bif Nat.blt (Nat.xor acc b) acc then Nat.xor acc b else acc) x

@[expose] def insD (r : ℕ) : List ℕ → List ℕ
  | [] => [r]
  | b :: B => bif Nat.blt b r then r :: b :: B else b :: insD r B

@[expose] def selStep (st : List ℕ × List ℕ) (x : ℕ) : List ℕ × List ℕ :=
  bif Nat.ble 7 st.2.length then st else
    bif Nat.beq (redB st.1 x) 0 then st else (insD (redB st.1 x) st.1, st.2 ++ [x])

@[expose] def selT (T : List ℕ) : List ℕ := (T.foldl selStep ([], [])).2

@[expose] def rk7 (T : List ℕ) : Bool := Nat.beq (selT T).length 7

@[expose] def imgsY (fs3 : List (ℕ → ℕ)) (w : ℕ) (ys : List ℕ) : List ℕ :=
  w :: ys ++ fs3.flatMap fun f => ys.map f

@[expose] def imgs (fs fs3 : List (ℕ → ℕ)) (w : ℕ) : List ℕ := imgsY fs3 w (fs.map fun f => f w)

@[expose] def fsQ : List (ℕ → ℕ) := (g1Q.map Prod.fst).map fun X => mvNR (unpackQ X)

@[expose] def fs3Q : List (ℕ → ℕ) := fsQ.take 3

@[expose] def cntQ (iM : ℕ) : Bool := Nat.beq (CFSG.KC.pc4096 iM) 64

@[expose] def interQ (iM zM : ℕ) (tc : List ℕ) : Bool :=
  (List.range 4096).all fun y => (bitQ iM y && bitQ iM (mvNR tc y)) == bitQ zM y

@[expose] def witC (fs fs3 : List (ℕ → ℕ)) (iM a : ℕ) : Bool :=
  (List.range 512).all fun i => bitQ iM (Nat.add a i) || rk7 (imgs fs fs3 (Nat.add a i))

@[expose] def cnt43 : Bool := cntQ (maskOf 0 iList)

@[expose] def wit43 (a : ℕ) : Bool := witC fsQ fs3Q (maskOf 0 iList) a

@[expose] def inter43 : Bool := interQ (maskOf 0 iList) (maskOf 0 zList) (unpackQ (wordP nQ tInvWord))

end Certificates.Kernel.AS91I43

end

end
