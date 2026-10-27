module

public import CFSG.Quasithin.Background.SmithB45J2SylData

public section

namespace CFSG.Quasithin.J2Row

open CFSG.Quasithin.J2Bits

@[expose] def disp (m : BM) (x : BV) : BV := (m.mv x).add x

@[expose] def moves (m : BM) (beta : List BV) : Bool := beta.any fun x => !(m.mv x).eqv x

@[expose] def chainOK (m : BM) : List (Fin 6 × BV) → List (Fin 6) → Bool
  | [], _ => true
  | (q, x) :: c, prev =>
    (disp m x).nz q && prev.all (fun q' => !(disp m x).nz q') && chainOK m c (q :: prev)

@[expose] def invOK (n : ℕ) (d : InvD) : Bool :=
  d.beta.length == n && d.beta.all (fun x => ((sEl d.idx).mv x).eqv x) &&
    d.chain.length == 6 - n && chainOK (sEl d.idx) d.chain []

@[expose] def fixOK (d : InvD) : Bool :=
  match d.fix with
  | [f₁, f₂] => ((sEl d.idx).mul (sEl f₁)).eqv (sEl f₂) &&
      (inv2A ++ inv2B).all fun e => e.idx == d.idx || e.idx == f₁ || e.idx == f₂ ||
        moves (sEl e.idx) d.beta
  | _ => false

theorem gen_check : (a6.mul a6i).eqv BM.one = true ∧ (a6i.mul a6).eqv BM.one = true ∧
    (b6.mul b6i).eqv BM.one = true ∧ (b6i.mul b6).eqv BM.one = true := by
  decide +kernel

theorem sGen_sq_check :
    (List.finRange 4).all (fun k => ((sGen k).mul (sGen k)).eqv BM.one) = true := by
  decide +kernel

theorem sGen_check : (List.finRange 4).all (fun k => (evalW (sWord k)).eqv (sGen k)) = true := by
  decide +kernel

theorem sEl_zero : (sEl 0).eqv BM.one = true := by decide +kernel

theorem sMul_check : (List.finRange 128).all (fun i => (List.finRange 4).all fun g =>
    ((sGen g).mul (sEl i)).eqv (sEl sMulV[i][g])) = true := by
  decide +kernel

theorem sPar_check : (List.finRange 128).all (fun i => i == 0 ||
    (decide (sParV[i].1 < i) && sMulV[sParV[i].1][sParV[i].2] == i)) = true := by
  decide +kernel

theorem sKey_check : (List.finRange 128).all (fun i => (List.finRange 128).all fun j =>
    i == j || (sEl i).key != (sEl j).key) = true := by
  decide +kernel

theorem sInv_check : (List.finRange 128).all (fun i =>
    !((sEl i).mul (sEl i)).eqv BM.one || i == 0 || inv2A.any (fun d => d.idx == i) ||
      inv2B.any (fun d => d.idx == i)) = true := by
  decide +kernel

theorem inv2A_check : inv2A.all (invOK 4) = true := by decide +kernel

theorem inv2B_check : inv2B.all (fun d => invOK 3 d && fixOK d) = true := by decide +kernel

theorem pair2A_check : inv2A.all (fun d => inv2A.all fun e =>
    e.idx == d.idx || moves (sEl e.idx) d.beta) = true := by
  decide +kernel

theorem comm2A_check : inv2A.all (fun d => inv2A.all fun e => e.idx == d.idx ||
    comm2A.contains (d.idx, e.idx) ||
      !((sEl d.idx).mul (sEl e.idx)).eqv ((sEl e.idx).mul (sEl d.idx))) = true := by
  decide +kernel

theorem d5_check : comm2A.all (fun p => comm2A.all fun q => p.1 != q.1 || p.2 == q.2 ||
    !comm2A.contains (p.2, q.2) || (sEl q.2).eqv ((sEl p.1).mul (sEl p.2))) = true := by
  decide +kernel

end CFSG.Quasithin.J2Row
