module

public import CFSG.RankThree.Chevalley.SteinbergBIE6D4CertDefs

public noncomputable section

namespace CFSG.RankThree.PartOne.KD4L

open CFSG.Blueprint.Chevalley CFSG.Monster.B.Classical.E6Adjoint CFSG.Monster.B.E6.StdF4
open CFSG.RankThree.Chevalley

@[expose] def pairList : List (Fin 3 × Fin 3) :=
  (List.finRange 3).flatMap fun a => (List.finRange 3).map fun b => (a, b)

theorem mem_pairList (t : Fin 3 × Fin 3) : t ∈ pairList := by
  revert t
  decide

theorem nodup_pairList : pairList.Nodup := by
  decide

@[expose] def pairClass (r : ℕ) : List (Fin 3 × Fin 3) :=
  pairList.filter fun t => ((t.1 : ℕ) + 2 * (t.2 : ℕ)) % 3 == r

@[expose] def pairWord (A₁ A₂ : ℕ) (t : Fin 3 × Fin 3) : ℕ :=
  packMul (packMul idPack (coeffSparse A₁ t.1)) (coeffSparse A₂ t.2)

@[expose] def tauLetter (Ps Qs : List (List (List ℕ))) (a : ℕ) : List (List ℕ) :=
  if a < 3 then Ps.getD a [] else if a < 6 then Qs.getD (a - 3) []
  else if a = 6 then opSubSparse 7 else if a = 7 then opSubSparse 14
  else if a = 8 then opSubSparse 9 else opSubSparse 18

@[expose] def tauLettersOK (Ps Qs : List (List (List ℕ))) : Bool :=
  ((List.finRange 3).all fun k =>
    (sparseOK (coeffSparse 8 k) && sparseOK (coeffSparse 10 k)) &&
      (sparseOK (coeffSparse 16 k) && sparseOK (coeffSparse 20 k))) &&
  (List.range 3).all fun r =>
    (sparseOK (Ps.getD r []) && sparseOK (Qs.getD r [])) &&
    ((packMul idPack (Ps.getD r []) == xorSum ((pairClass r).map (pairWord 10 8))) &&
      (packMul idPack (Qs.getD r []) == xorSum ((pairClass r).map (pairWord 20 16))))

@[expose] def tauTargetsOK (Ps Qs Ws : List (List (List ℕ))) : Bool :=
  ((sparseOK (opSubSparse 7) && sparseOK (opSubSparse 14)) &&
    (sparseOK (opSubSparse 9) && sparseOK (opSubSparse 18))) &&
  (List.range 16).all fun k => sparseOK (d4Targets.getD k []) &&
    (certPack (tauLetter Ps Qs) (Ws.getD k []) == packMul idPack (d4Targets.getD k []))

section Semantics

variable {R : Type*} [Field R] [CharP R 2]

@[expose] def pairClassEnd (A₁ A₂ : Fin 78) (r : ℕ) : Module.End R (RootModule Tag.E6 R) :=
  ((pairClass r).map fun t => coeffEnd (R := R) A₁ t.1 * coeffEnd A₂ t.2).sum

theorem packEnd_pairWord {A₁ A₂ : Fin 78} (h₁ : ∀ k, sparseOK (coeffSparse A₁ k) = true)
    (h₂ : ∀ k, sparseOK (coeffSparse A₂ k) = true) (t : Fin 3 × Fin 3) :
    packEnd R (pairWord A₁ A₂ t) = coeffEnd A₁ t.1 * coeffEnd A₂ t.2 := by
  rw [pairWord, packEnd_packMul _ (h₂ _), packEnd_packMul _ (h₁ _), packEnd_idPack, one_mul,
    sparseEnd_coeffSparse, sparseEnd_coeffSparse]

theorem sparseEnd_eq_pairClassEnd {A₁ A₂ : Fin 78} (h₁ : ∀ k, sparseOK (coeffSparse A₁ k) = true)
    (h₂ : ∀ k, sparseOK (coeffSparse A₂ k) = true) {r : ℕ} {L : List (List ℕ)}
    (hL : sparseOK L = true)
    (h : (packMul idPack L == xorSum ((pairClass r).map (pairWord A₁ A₂))) = true) :
    sparseEnd R L = pairClassEnd A₁ A₂ r := by
  rw [← packEnd_packMul_idPack hL, beq_iff_eq.1 h, packEnd_xorSum, List.map_map, pairClassEnd]
  exact congrArg List.sum (List.map_congr_left fun t _ => packEnd_pairWord h₁ h₂ t)

theorem tauLetter_P {Ps Qs : List (List (List ℕ))} {r : ℕ} (hr : r < 3) :
    tauLetter Ps Qs r = Ps.getD r [] := by
  rw [tauLetter, ite_eq_left hr]

theorem tauLetter_Q {Ps Qs : List (List (List ℕ))} {r : ℕ} (hr : r < 3) :
    tauLetter Ps Qs (3 + r) = Qs.getD r [] := by
  rw [tauLetter, ite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel_left]

theorem commute_tauTargets {Ps Qs Ws : List (List (List ℕ))}
    (hL : tauLettersOK Ps Qs = true) (hT : tauTargetsOK Ps Qs Ws = true)
    {X : Module.End R (RootModule Tag.E6 R)}
    (hP : ∀ r < 3, Commute X (pairClassEnd (R := R) 10 8 r))
    (hQ : ∀ r < 3, Commute X (pairClassEnd (R := R) 20 16 r))
    (hM₁ : Commute X (ad R (Finsupp.single (lab 7) 1) + formTensor R (Finsupp.single (lab 7) 1)))
    (hN₁ : Commute X (ad R (Finsupp.single (lab 14) 1) + formTensor R (Finsupp.single (lab 14) 1)))
    (hM₃ : Commute X (ad R (Finsupp.single (lab 9) 1) + formTensor R (Finsupp.single (lab 9) 1)))
    (hN₃ : Commute X (ad R (Finsupp.single (lab 18) 1) + formTensor R (Finsupp.single (lab 18) 1)))
    {k : ℕ} (hk : k < 16) : Commute X (sparseEnd R (d4Targets.getD k [])) := by
  simp only [tauLettersOK, tauTargetsOK, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    List.mem_range, true_implies] at hL hT
  obtain ⟨hC, hL⟩ := hL
  obtain ⟨⟨⟨hm₁, hn₁⟩, hm₃, hn₃⟩, hT⟩ := hT
  have hc : ∀ (A : Fin 78), (A = 8 ∨ A = 10 ∨ A = 16 ∨ A = 20) →
      ∀ k, sparseOK (coeffSparse A k) = true := by
    rintro A (rfl | rfl | rfl | rfl) k
    · exact (hC k).1.1
    · exact (hC k).1.2
    · exact (hC k).2.1
    · exact (hC k).2.2
  have hletter : ∀ a, sparseOK (tauLetter Ps Qs a) = true ∧
      Commute X (sparseEnd R (tauLetter Ps Qs a)) := by
    intro a
    by_cases ha : a < 3
    · obtain ⟨⟨hPs, -⟩, hPe, -⟩ := hL a ha
      rw [tauLetter_P ha]
      refine ⟨hPs, ?_⟩
      rw [sparseEnd_eq_pairClassEnd (hc 10 (by decide)) (hc 8 (by decide)) hPs hPe]
      exact hP a ha
    by_cases ha' : a < 6
    · obtain ⟨⟨-, hQs⟩, -, hQe⟩ := hL (a - 3) (by omega)
      have e3 : a = 3 + (a - 3) := by omega
      rw [e3, tauLetter_Q (by omega)]
      refine ⟨hQs, ?_⟩
      rw [sparseEnd_eq_pairClassEnd (hc 20 (by decide)) (hc 16 (by decide)) hQs hQe]
      exact hQ _ (by omega)
    by_cases h6 : a = 6
    · rw [tauLetter, ite_eq_right ha, ite_eq_right ha', ite_eq_left h6]
      refine ⟨hm₁, ?_⟩
      rw [show opSubSparse 7 = opSubSparse ((7 : Fin 78) : ℕ) from rfl, sparseEnd_opSubSparse]
      exact hM₁
    by_cases h7 : a = 7
    · rw [tauLetter, ite_eq_right ha, ite_eq_right ha', ite_eq_right h6, ite_eq_left h7]
      refine ⟨hn₁, ?_⟩
      rw [show opSubSparse 14 = opSubSparse ((14 : Fin 78) : ℕ) from rfl, sparseEnd_opSubSparse]
      exact hN₁
    by_cases h8 : a = 8
    · rw [tauLetter, ite_eq_right ha, ite_eq_right ha', ite_eq_right h6, ite_eq_right h7,
        ite_eq_left h8]
      refine ⟨hm₃, ?_⟩
      rw [show opSubSparse 9 = opSubSparse ((9 : Fin 78) : ℕ) from rfl, sparseEnd_opSubSparse]
      exact hM₃
    · rw [tauLetter, ite_eq_right ha, ite_eq_right ha', ite_eq_right h6, ite_eq_right h7,
        ite_eq_right h8]
      refine ⟨hn₃, ?_⟩
      rw [show opSubSparse 18 = opSubSparse ((18 : Fin 78) : ℕ) from rfl, sparseEnd_opSubSparse]
      exact hN₃
  obtain ⟨hTk, hcert⟩ := hT k hk
  exact commute_sparseEnd_of_cert _ _ hcert hTk fun _ _ a _ => hletter a

theorem commute_of_tauCert {Ps Qs Ws : List (List (List ℕ))}
    (hL : tauLettersOK Ps Qs = true) (hT : tauTargetsOK Ps Qs Ws = true)
    {X : Module.End R (RootModule Tag.E6 R)}
    (hP : ∀ r < 3, Commute X (pairClassEnd (R := R) 10 8 r))
    (hQ : ∀ r < 3, Commute X (pairClassEnd (R := R) 20 16 r))
    (hM₁ : Commute X (ad R (Finsupp.single (lab 7) 1) + formTensor R (Finsupp.single (lab 7) 1)))
    (hN₁ : Commute X (ad R (Finsupp.single (lab 14) 1) + formTensor R (Finsupp.single (lab 14) 1)))
    (hM₃ : Commute X (ad R (Finsupp.single (lab 9) 1) + formTensor R (Finsupp.single (lab 9) 1)))
    (hN₃ : Commute X (ad R (Finsupp.single (lab 18) 1) + formTensor R (Finsupp.single (lab 18) 1)))
    (m : ℕ) (hm : m < 4) (c : R) :
    Commute X (xOp Tag.E6 R ⟨m + 1, show m + 1 < 6 by omega⟩ c) ∧
      Commute X (yOp Tag.E6 R ⟨m + 1, show m + 1 < 6 by omega⟩ c) :=
  commute_of_d4Targets (fun _ hk => commute_tauTargets hL hT hP hQ hM₁ hN₁ hM₃ hN₃ hk) m hm c

end Semantics

@[expose] def tauPLetters : List (List (List ℕ)) := [
    [[0], [1], [2], [3], [4], [5], [6], [7], [8], [9, 29], [10], [11], [12], [13], [14],
     [15, 38], [16], [17], [18], [19], [20], [21], [22], [23], [24], [25], [26], [27], [28],
     [29], [30], [31], [32], [33], [34], [35], [36], [37], [38], [39], [18, 40], [41], [42],
     [43], [44], [45], [46], [25, 47], [48], [49], [50], [51], [52], [53], [54], [55], [56],
     [57], [58], [59], [60], [61], [62, 72], [63], [64], [65], [66], [67], [68], [69], [70],
     [71], [72], [66, 73], [74], [75], [76], [77]],
    [[], [], [], [10], [], [10], [], [], [], [19], [], [21], [], [], [], [27], [8], [29], [],
     [], [4], [], [], [], [35], [], [38], [], [], [], [18], [], [22], [], [45], [], [], [25],
     [], [], [28], [], [], [], [33], [], [], [36], [], [], [], [], [43], [], [], [], [], [],
     [64], [], [], [], [68], [], [], [], [], [72], [], [63], [], [66], [], [70], [], [], [], []],
    [[8], [], [], [8], [], [], [13], [], [], [17], [], [], [], [], [], [26], [2], [], [], [29],
     [10], [], [], [12], [], [], [], [38], [18], [], [], [41], [], [], [], [], [25], [], [],
     [50], [30], [], [], [], [], [], [], [37], [], [], [], [42], [], [], [61], [], [], [48],
     [], [], [], [], [67], [], [], [59], [], [], [72], [], [66], [], [], [71], [], [], [], []]
  ]

@[expose] def tauQLetters : List (List (List ℕ)) := [
    [[0], [1], [2], [3], [4], [5], [6], [7], [8], [9], [10], [11], [12], [13], [14], [15],
     [16], [17], [18, 40], [19], [20], [21], [22], [23], [24], [25, 47], [26], [27], [28],
     [9, 29], [30], [31], [32], [33], [34], [35], [36], [37], [15, 38], [39], [40], [41], [42],
     [43], [44], [45], [46], [47], [48], [49], [50], [51], [52], [53], [54], [55], [56], [57],
     [58], [59], [60], [61], [62], [63], [64], [65], [66, 73], [67], [68], [69], [70], [71],
     [62, 72], [73], [74], [75], [76], [77]],
    [[], [], [], [20], [], [20], [], [], [16], [], [4], [], [], [], [], [], [], [], [30], [9],
     [], [11], [32], [], [], [37], [], [15], [40], [17], [], [], [], [44], [], [24], [47], [],
     [26], [], [], [], [], [52], [], [34], [], [], [], [], [], [], [], [], [], [], [], [], [],
     [], [], [], [], [69], [58], [], [71], [], [62], [], [73], [], [67], [], [], [], [], []],
    [[16], [], [], [16], [], [], [], [], [2], [], [20], [], [23], [6], [], [], [], [9], [28],
     [], [], [], [], [], [], [36], [15], [], [], [19], [40], [], [], [], [], [], [], [47],
     [27], [], [], [31], [51], [], [], [], [], [], [57], [], [39], [], [], [], [], [], [], [],
     [], [65], [], [54], [], [], [], [], [70], [62], [], [], [], [73], [68], [], [], [], [], []]
  ]

@[expose] def tauWords : List (List (List ℕ)) := [
    [[8], [0, 3], [0, 8], [1, 4], [3, 0], [4, 1], [6, 7], [8, 9], [0, 6, 7], [0, 7, 6],
     [0, 7, 8], [0, 8, 9], [1, 4, 8], [1, 9, 4], [2, 5, 8], [3, 6, 7], [3, 6, 9], [3, 7, 6],
     [3, 9, 8], [4, 1, 9], [5, 2, 8], [5, 8, 2], [5, 9, 4], [6, 8, 6], [6, 8, 9], [7, 6, 8],
     [7, 6, 9], [7, 8, 6], [7, 8, 9], [8, 2, 5], [8, 6, 7], [8, 6, 8], [8, 6, 9], [9, 8, 6],
     [0, 3, 6, 9], [0, 3, 7, 6], [0, 3, 9, 8], [0, 5, 9, 4], [1, 3, 2, 8], [1, 4, 9, 8],
     [1, 8, 9, 4], [1, 9, 4, 8], [2, 9, 5, 8], [3, 0, 6, 7], [3, 0, 7, 8], [3, 0, 8, 9],
     [4, 1, 8, 9], [4, 8, 1, 9], [4, 9, 8, 1], [5, 8, 2, 9], [6, 7, 8, 6], [6, 7, 8, 9],
     [7, 6, 9, 8], [7, 9, 8, 6], [8, 6, 7, 9], [8, 6, 9, 8]],
    [[6], [8], [0, 3], [0, 8], [1, 4], [3, 0], [4, 1], [6, 7], [8, 9], [0, 6, 7], [0, 7, 6],
     [0, 7, 8], [0, 8, 9], [1, 4, 8], [1, 9, 4], [2, 5, 8], [3, 6, 7], [3, 6, 9], [3, 7, 6],
     [3, 9, 8], [4, 1, 9], [5, 2, 8], [5, 8, 2], [5, 9, 4], [6, 8, 6], [6, 8, 9], [7, 6, 8],
     [7, 6, 9], [7, 8, 6], [7, 8, 9], [8, 2, 5], [8, 6, 7], [8, 6, 8], [8, 6, 9], [9, 8, 6],
     [0, 3, 6, 9], [0, 3, 7, 6], [0, 3, 9, 8], [0, 5, 9, 4], [1, 3, 2, 8], [1, 4, 9, 8],
     [1, 8, 9, 4], [1, 9, 4, 8], [2, 9, 5, 8], [3, 0, 6, 7], [3, 0, 7, 8], [3, 0, 8, 9],
     [4, 1, 8, 9], [4, 8, 1, 9], [4, 9, 8, 1], [5, 8, 2, 9], [6, 7, 8, 6], [6, 7, 8, 9],
     [7, 6, 9, 8], [7, 9, 8, 6], [8, 6, 7, 9], [8, 6, 9, 8]],
    [[8], [0, 3], [1, 4], [3, 0], [3, 9], [4, 1], [6, 7], [6, 9], [7, 6], [7, 8], [8, 0],
     [9, 3], [0, 3, 9], [0, 6, 7], [0, 7, 6], [0, 7, 8], [0, 8, 9], [1, 9, 4], [3, 0, 8],
     [3, 6, 7], [3, 6, 9], [3, 7, 6], [3, 9, 8], [4, 1, 8], [4, 1, 9], [4, 9, 5], [5, 8, 2],
     [6, 7, 9], [7, 9, 7], [7, 9, 8], [8, 0, 3], [8, 2, 5], [8, 9, 7], [9, 3, 0], [9, 4, 1],
     [9, 5, 2], [9, 7, 6], [9, 7, 9], [0, 3, 6, 9], [0, 3, 7, 6], [0, 3, 9, 8], [0, 4, 9, 5],
     [1, 4, 9, 8], [1, 8, 9, 4], [1, 9, 4, 8], [2, 3, 1, 8], [2, 9, 5, 8], [3, 0, 6, 7],
     [3, 0, 7, 8], [3, 0, 8, 9], [4, 1, 8, 9], [4, 8, 1, 9], [4, 9, 8, 1], [5, 8, 2, 9],
     [6, 7, 6, 8], [6, 7, 8, 9], [6, 8, 9, 8], [6, 9, 7, 6], [7, 6, 9, 7], [7, 6, 9, 8],
     [8, 9, 7, 8], [9, 7, 8, 9]],
    [[7], [8], [0, 3], [1, 4], [3, 0], [3, 9], [4, 1], [6, 7], [6, 9], [7, 6], [7, 8], [8, 0],
     [9, 3], [0, 3, 9], [0, 6, 7], [0, 7, 6], [0, 7, 8], [0, 8, 9], [1, 9, 4], [3, 0, 8],
     [3, 6, 7], [3, 6, 9], [3, 7, 6], [3, 9, 8], [4, 1, 8], [4, 1, 9], [4, 9, 5], [5, 8, 2],
     [6, 7, 9], [7, 9, 7], [7, 9, 8], [8, 0, 3], [8, 2, 5], [8, 9, 7], [9, 3, 0], [9, 4, 1],
     [9, 5, 2], [9, 7, 6], [9, 7, 9], [0, 3, 6, 9], [0, 3, 7, 6], [0, 3, 9, 8], [0, 4, 9, 5],
     [1, 4, 9, 8], [1, 8, 9, 4], [1, 9, 4, 8], [2, 3, 1, 8], [2, 9, 5, 8], [3, 0, 6, 7],
     [3, 0, 7, 8], [3, 0, 8, 9], [4, 1, 8, 9], [4, 8, 1, 9], [4, 9, 8, 1], [5, 8, 2, 9],
     [6, 7, 6, 8], [6, 7, 8, 9], [6, 8, 9, 8], [6, 9, 7, 6], [7, 6, 9, 7], [7, 6, 9, 8],
     [8, 9, 7, 8], [9, 7, 8, 9]],
    [[2], [1, 8, 1], [5, 8, 1], [0, 5, 8, 1], [1, 5, 8, 0], [1, 8, 0, 5], [1, 8, 1, 9]],
    [[1, 9, 8], [2, 4, 8], [2, 8, 2], [4, 8, 2], [0, 4, 8, 2], [1, 9, 8, 0], [2, 8, 0, 4],
     [2, 8, 2, 9]],
    [[5], [1, 9], [5, 9], [1, 3, 9], [1, 9, 3], [4, 9, 4], [5, 9, 3], [1, 3, 9, 3],
     [2, 3, 9, 4], [3, 2, 9, 4], [4, 8, 9, 4]],
    [[2, 9], [4, 9], [2, 3, 9], [2, 9, 3], [4, 9, 3], [5, 9, 5], [1, 3, 9, 5], [2, 3, 9, 3],
     [3, 1, 9, 5], [5, 8, 9, 5]],
    [[0, 8], [8, 0], [1, 4, 8], [2, 5, 8], [3, 0, 8], [4, 1, 8], [5, 2, 8], [8, 0, 3],
     [1, 3, 2, 8], [2, 3, 1, 8]],
    [[8], [0, 8], [8, 0], [1, 4, 8], [2, 5, 8], [3, 0, 8], [4, 1, 8], [5, 2, 8], [8, 0, 3],
     [1, 3, 2, 8], [2, 3, 1, 8]],
    [[3, 9], [9, 3], [0, 3, 9], [4, 9, 5], [5, 9, 4], [9, 3, 0], [9, 4, 1], [9, 5, 2],
     [0, 4, 9, 5], [0, 5, 9, 4]],
    [[9], [3, 9], [9, 3], [0, 3, 9], [4, 9, 5], [5, 9, 4], [9, 3, 0], [9, 4, 1], [9, 5, 2],
     [0, 4, 9, 5], [0, 5, 9, 4]],
    [[1], [1, 9, 8], [2, 4, 8], [2, 8, 2], [4, 8, 2], [0, 4, 8, 2], [1, 9, 8, 0], [2, 8, 0, 4],
     [2, 8, 2, 9]],
    [[1, 8, 1], [5, 8, 1], [0, 5, 8, 1], [1, 5, 8, 0], [1, 8, 0, 5], [1, 8, 1, 9]],
    [[4], [2, 9], [4, 9], [2, 3, 9], [2, 9, 3], [4, 9, 3], [5, 9, 5], [1, 3, 9, 5],
     [2, 3, 9, 3], [3, 1, 9, 5], [5, 8, 9, 5]],
    [[1, 9], [5, 9], [1, 3, 9], [1, 9, 3], [4, 9, 4], [5, 9, 3], [1, 3, 9, 3], [2, 3, 9, 4],
     [3, 2, 9, 4], [4, 8, 9, 4]]
  ]

theorem tauLettersOK_two : tauLettersOK tauPLetters tauQLetters = true := by
  decide +kernel

theorem tauTargetsOK_two : tauTargetsOK tauPLetters tauQLetters tauWords = true := by
  decide +kernel

end CFSG.RankThree.PartOne.KD4L
