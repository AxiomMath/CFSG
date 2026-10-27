module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKRank

public section

namespace CFSG.Quasithin.H13.KGRank

open CFSG.QuasithinUnique.Lin2.RankCert

@[expose] def spanIdx (mul : ℕ → ℕ → ℕ) : List ℕ → List ℕ
  | [] => [0]
  | f :: F => let S := spanIdx mul F; S ++ S.map (mul f)

@[expose] def pairsOf : List ℕ → List (ℕ × ℕ)
  | a :: b :: l => (a, b) :: pairsOf l
  | _ => []

@[expose] def triplesOf : List ℕ → List (ℕ × ℕ × ℕ)
  | a :: b :: c :: l => (a, b, c) :: triplesOf l
  | _ => []

@[expose] def nodeCheck (N : ℕ) (mul : ℕ → ℕ → ℕ) (nodes : Array (List ℕ × List ℕ)) :
    ℕ → ℕ → List ℕ → List ℕ → Bool
  | 0, _, _, _ => false
  | fuel + 1, j, F, D =>
    let invs := D.filter fun x => mul x x == 0
    decide (invs.length < 2 ^ 8) ||
      (let sp := spanIdx mul F
       let cands := invs.filter fun x => !sp.contains x
       let nd := nodes.getD j ([], [])
       let reps := pairsOf nd.1
       let wit := triplesOf nd.2
       decide (sp.length < 2 ^ 8) && cands == wit.map Prod.fst &&
       wit.all (fun w => decide (w.2.1 < N) && decide (w.2.2 < reps.length) &&
          F.all (fun f => mul w.2.1 f == mul f w.2.1) &&
          mul w.2.1 w.1 == mul (reps.getD w.2.2 (0, 0)).1 w.2.1) &&
       reps.all fun rc => decide (rc.1 < N) &&
          nodeCheck N mul nodes fuel rc.2 (rc.1 :: F) (D.filter fun y => mul y rc.1 == mul rc.1 y))

@[expose] def treeCheck (N g gi : ℕ) (par cl : Array ℕ) (zi : ℕ)
    (nodes : Array (List ℕ × List ℕ)) : Bool :=
  let mul := mulIdx g gi par cl N
  decide (zi < N) && mul zi zi == 0 && (List.range N).all (fun i => mul zi i == mul i zi) &&
    nodeCheck N mul nodes (nodes.size + 1) 0 [zi] (List.range N)

end CFSG.Quasithin.H13.KGRank
