module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44DataOuter

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Sp44

@[expose] def phiE : El := (idM, 2)

@[expose] def SClist : List El :=
  (List.range 2).flatMap fun a => (List.range 2).flatMap fun b => (List.range 2).flatMap fun c =>
    (List.range 2).flatMap fun d => (List.range 4).map fun j => (uMat a b c d, j)

@[expose] def I2 : List El :=
  SClist.filter fun x => x.2 == 0 && x != oneE && gmulE x x == oneE

@[expose] def phiConj : List El := [
  (1074791425, 0), (1078998133, 0), (1074795713, 0), (1079010549, 0),
  (1079018725, 0), (1074832481, 0), (1074828449, 0), (1079026757, 0),
  (1083216969, 0), (1083233369, 0), (1087423613, 0), (1087378685, 0),
  (1083221081, 0), (1087386861, 0), (1087382557, 0), (1087435933, 0)
]

@[expose] def phiRows : List (List El × Nat × El) := [
  ([(1074807825, 0), (1074795521, 0)], 1, (1141134597, 2)),
  ([(1074807825, 0), (1074811985, 0)], 1, (285295620, 2)),
  ([(1074795521, 0), (1074811985, 0)], 2, (285295620, 2)),
  ([(1074811921, 0), (1074811985, 0)], 2, (1426395393, 2)),
  ([(1074791489, 0), (1074795521, 0)], 2, (1141134597, 2)),
  ([(1074811921, 0), (1074795585, 0)], 0, (1141117185, 0)),
  ([(1074807825, 0), (1074807889, 0)], 1, (1426395393, 2)),
  ([(1074791489, 0), (1079002197, 0)], 1, (1359287553, 2)),
  ([(1074791489, 0), (1078985797, 0)], 1, (1427178753, 2)),
  ([(1074807825, 0), (1079002197, 0)], 2, (341071109, 3)),
  ([(1074807825, 0), (1078985797, 0)], 2, (1410601217, 3)),
  ([(1074807889, 0), (1079002197, 0)], 0, (1410601217, 3)),
  ([(1074807889, 0), (1078985733, 0)], 2, (1363231748, 3)),
  ([(1074807825, 0), (1074807889, 0), (1079002197, 0)], 3, (285295620, 3)),
  ([(1074807825, 0), (1074795521, 0), (1074811985, 0)], 3, (1426395393, 2))
]

theorem sc_of_commute : ∀ x ∈ Pel, gmulE x phiE = gmulE phiE x → x ∈ SClist := by
  decide +kernel

theorem phi_mul_involutive : ∀ x ∈ SClist, gmulE phiE (gmulE phiE x) = x ∧
    gmulE phiE x ∈ SClist ∧ (gmulE phiE x).2 = (x.2 + 2) % 4 ∧ gmulE x phiE = gmulE phiE x := by
  decide +kernel

theorem phiConj_mem : ∀ p ∈ phiConj, p ∈ Pel := by
  decide +kernel

theorem outer_to_phi : ∀ x ∈ invs, x.2 = 2 → ∃ p ∈ phiConj, conjE p x = phiE := by
  decide +kernel

theorem E4_complete_aux : ∀ u ∈ I2, ∀ v ∈ I2, u = v ∨ gmulE u v ≠ gmulE v u ∨
    ∃ r ∈ phiRows, r.1.length = 2 ∧ (∀ x ∈ klein u v, x ∈ span2 r.1) ∧
      ∀ x ∈ span2 r.1, x ∈ klein u v := by
  decide +kernel

theorem E4_complete : ∀ u ∈ I2, ∀ v ∈ I2, u ≠ v → gmulE u v = gmulE v u →
    ∃ r ∈ phiRows, r.1.length = 2 ∧ (∀ x ∈ klein u v, x ∈ span2 r.1) ∧
      ∀ x ∈ span2 r.1, x ∈ klein u v := by
  intro u hu v hv huv hc
  rcases E4_complete_aux u hu v hv with h | h | h
  · exact absurd h huv
  · exact absurd hc h
  · exact h

theorem E8_complete : ∀ r ∈ phiRows, r.1.length = 2 → ∀ w ∈ I2, w ∉ span2 r.1 →
    (∀ g ∈ r.1, gmulE g w = gmulE w g) →
    ∃ r' ∈ phiRows, r'.1.length = 3 ∧ (∀ x ∈ span2 (r.1 ++ [w]), x ∈ span2 r'.1) ∧
      ∀ x ∈ span2 r'.1, x ∈ span2 (r.1 ++ [w]) := by
  decide +kernel

theorem noE16 : ∀ r ∈ phiRows, r.1.length = 3 → ∀ w ∈ I2, w ∉ span2 r.1 →
    ∃ g ∈ r.1, gmulE g w ≠ gmulE w g := by
  decide +kernel

theorem rows_ok : ∀ r ∈ phiRows, (r.1.length = 2 ∨ r.1.length = 3) ∧ (∀ g ∈ r.1, g ∈ I2) ∧
    commInv r.1 = true ∧ nodupE (span2 r.1) = true ∧ (span2 r.1).length = 2 ^ r.1.length ∧
    (∀ x ∈ span2 r.1, x ∈ span2 (phiE :: r.1) ∧ gmulE phiE x ∈ span2 (phiE :: r.1)) ∧
    ∀ x ∈ span2 (phiE :: r.1), x ∈ span2 r.1 ∨ ∃ e ∈ span2 r.1, x = gmulE phiE e := by
  decide +kernel

theorem rows_conj : ∀ r ∈ phiRows, r.2.1 < 4 ∧ validB r.2.2 = true ∧
    (∀ x ∈ span2 (phiE :: r.1), conjE r.2.2 x ∈ span2 (outerRepGens.getD r.2.1 [])) ∧
    ∀ y ∈ span2 (outerRepGens.getD r.2.1 []), ∃ x ∈ span2 (phiE :: r.1), conjE r.2.2 x = y := by
  decide +kernel

theorem reps_commInv : ∀ c < 4, commInv (outerRepGens.getD c []) = true ∧
    ∀ x ∈ outerRepGens.getD c [], validB x = true := by
  decide +kernel

end CFSG.LocalAnalysis.WeakClosure81.Sp44

end
