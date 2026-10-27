module

public import CFSG.RankThree.Chevalley.SteinbergBIE6Commutant
public import CFSG.RankThree.Chevalley.SteinbergBIE6BitPack

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.Monster.B.Classical.E6Adjoint CFSG.Monster.B.E6.StdF4

@[expose] def tripleList : List (Fin 3 × Fin 3 × Fin 3) :=
  (List.finRange 3).flatMap fun a => (List.finRange 3).flatMap fun b =>
    (List.finRange 3).map fun c => (a, b, c)

theorem mem_tripleList (t : Fin 3 × Fin 3 × Fin 3) : t ∈ tripleList := by
  revert t
  decide

theorem nodup_tripleList : tripleList.Nodup := by
  decide

@[expose] def tripleExp (e : ℕ) (t : Fin 3 × Fin 3 × Fin 3) : ℕ :=
  (t.1 : ℕ) + (t.2.1 : ℕ) * 2 ^ e + (t.2.2 : ℕ) * 2 ^ (2 * e)

@[expose] def classList (e r : ℕ) : List (Fin 3 × Fin 3 × Fin 3) :=
  tripleList.filter fun t => tripleExp e t % 7 == r

@[expose] def coeffSparse (A : ℕ) (k : Fin 3) : List (List ℕ) :=
  if (k : ℕ) = 0 then idSparse else if (k : ℕ) = 1 then adSparse A else tensorSparse A

@[expose] def tripleWord (A₁ A₂ A₃ : ℕ) (t : Fin 3 × Fin 3 × Fin 3) : ℕ :=
  packMul (packMul (packMul idPack (coeffSparse A₁ t.1)) (coeffSparse A₂ t.2.1))
    (coeffSparse A₃ t.2.2)

@[expose] def d4Letter (Ps Qs : List (List (List ℕ))) (a : ℕ) : List (List ℕ) :=
  if a < 7 then Ps.getD a [] else if a < 14 then Qs.getD (a - 7) []
  else if a = 14 then opSubSparse 9 else opSubSparse 18

@[expose] def d4Targets : List (List (List ℕ)) :=
  [1, 2, 3, 4].flatMap fun j =>
    [adSparse (6 + j), tensorSparse (6 + j), adSparse (12 + 2 * j), tensorSparse (12 + 2 * j)]

@[expose] def d4LettersOK (e : ℕ) (Ps Qs : List (List (List ℕ))) : Bool :=
  ((List.finRange 3).all fun k =>
    (sparseOK (coeffSparse 7 k) && sparseOK (coeffSparse 8 k) && sparseOK (coeffSparse 10 k)) &&
      (sparseOK (coeffSparse 14 k) && sparseOK (coeffSparse 16 k) &&
        sparseOK (coeffSparse 20 k))) &&
  (List.range 7).all fun r =>
    (sparseOK (Ps.getD r []) && sparseOK (Qs.getD r [])) &&
    ((packMul idPack (Ps.getD r []) == xorSum ((classList e r).map (tripleWord 7 8 10))) &&
      (packMul idPack (Qs.getD r []) == xorSum ((classList e r).map (tripleWord 14 16 20))))

@[expose] def d4TargetsOK (Ps Qs Ws : List (List (List ℕ))) : Bool :=
  (sparseOK (opSubSparse 9) && sparseOK (opSubSparse 18)) &&
  (List.range 16).all fun k => sparseOK (d4Targets.getD k []) &&
    (certPack (d4Letter Ps Qs) (Ws.getD k []) == packMul idPack (d4Targets.getD k []))

section Semantics

variable {R : Type*} [Field R] [CharP R 2]

@[expose] def coeffEnd (A : Fin 78) : Fin 3 → Module.End R (RootModule Tag.E6 R) :=
  quadCoeff (ad R (Finsupp.single (lab A) 1)) (formTensor R (Finsupp.single (lab A) 1))

theorem sparseEnd_coeffSparse (A : Fin 78) (k : Fin 3) :
    sparseEnd R (coeffSparse A k) = coeffEnd A k := by
  fin_cases k
  · exact sparseEnd_idSparse
  · exact sparseEnd_adSparse A
  · exact sparseEnd_tensorSparse A

@[expose] def classEnd (A₁ A₂ A₃ : Fin 78) (e r : ℕ) : Module.End R (RootModule Tag.E6 R) :=
  ((classList e r).map fun t =>
    coeffEnd (R := R) A₁ t.1 * coeffEnd A₂ t.2.1 * coeffEnd A₃ t.2.2).sum

theorem packEnd_tripleWord {A₁ A₂ A₃ : Fin 78} (h₁ : ∀ k, sparseOK (coeffSparse A₁ k) = true)
    (h₂ : ∀ k, sparseOK (coeffSparse A₂ k) = true) (h₃ : ∀ k, sparseOK (coeffSparse A₃ k) = true)
    (t : Fin 3 × Fin 3 × Fin 3) :
    packEnd R (tripleWord A₁ A₂ A₃ t) =
      coeffEnd A₁ t.1 * coeffEnd A₂ t.2.1 * coeffEnd A₃ t.2.2 := by
  rw [tripleWord, packEnd_packMul _ (h₃ _), packEnd_packMul _ (h₂ _), packEnd_packMul _ (h₁ _),
    packEnd_idPack, one_mul, sparseEnd_coeffSparse, sparseEnd_coeffSparse, sparseEnd_coeffSparse]

theorem sparseEnd_eq_classEnd {A₁ A₂ A₃ : Fin 78} (h₁ : ∀ k, sparseOK (coeffSparse A₁ k) = true)
    (h₂ : ∀ k, sparseOK (coeffSparse A₂ k) = true) (h₃ : ∀ k, sparseOK (coeffSparse A₃ k) = true)
    {e r : ℕ} {L : List (List ℕ)} (hL : sparseOK L = true)
    (h : (packMul idPack L == xorSum ((classList e r).map (tripleWord A₁ A₂ A₃))) = true) :
    sparseEnd R L = classEnd A₁ A₂ A₃ e r := by
  rw [← packEnd_packMul_idPack hL, beq_iff_eq.1 h, packEnd_xorSum, List.map_map, classEnd]
  exact congrArg List.sum (List.map_congr_left fun t _ => packEnd_tripleWord h₁ h₂ h₃ t)

theorem sparseEnd_d4Letter_P {Ps Qs : List (List (List ℕ))} {r : ℕ} (hr : r < 7) :
    d4Letter Ps Qs r = Ps.getD r [] := by
  rw [d4Letter, ite_eq_left hr]

theorem sparseEnd_d4Letter_Q {Ps Qs : List (List (List ℕ))} {r : ℕ} (hr : r < 7) :
    d4Letter Ps Qs (7 + r) = Qs.getD r [] := by
  rw [d4Letter, ite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel_left]

theorem commute_d4Targets {e : ℕ} {Ps Qs Ws : List (List (List ℕ))}
    (hL : d4LettersOK e Ps Qs = true) (hT : d4TargetsOK Ps Qs Ws = true)
    {X : Module.End R (RootModule Tag.E6 R)}
    (hP : ∀ r < 7, Commute X (classEnd (R := R) 7 8 10 e r))
    (hQ : ∀ r < 7, Commute X (classEnd (R := R) 14 16 20 e r))
    (hM₁ : Commute X (ad R (Finsupp.single (lab 9) 1) + formTensor R (Finsupp.single (lab 9) 1)))
    (hM₂ : Commute X
      (ad R (Finsupp.single (lab 18) 1) + formTensor R (Finsupp.single (lab 18) 1)))
    {k : ℕ} (hk : k < 16) : Commute X (sparseEnd R (d4Targets.getD k [])) := by
  simp only [d4LettersOK, d4TargetsOK, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    List.mem_range, true_implies] at hL hT
  obtain ⟨hC, hL⟩ := hL
  obtain ⟨⟨hm₁, hm₂⟩, hT⟩ := hT
  have hc : ∀ (A : Fin 78), (A = 7 ∨ A = 8 ∨ A = 10 ∨ A = 14 ∨ A = 16 ∨ A = 20) →
      ∀ k, sparseOK (coeffSparse A k) = true := by
    rintro A (rfl | rfl | rfl | rfl | rfl | rfl) k
    · exact (hC k).1.1.1
    · exact (hC k).1.1.2
    · exact (hC k).1.2
    · exact (hC k).2.1.1
    · exact (hC k).2.1.2
    · exact (hC k).2.2
  have hletter : ∀ a, sparseOK (d4Letter Ps Qs a) = true ∧
      Commute X (sparseEnd R (d4Letter Ps Qs a)) := by
    intro a
    by_cases ha : a < 7
    · obtain ⟨⟨hPs, -⟩, hPe, -⟩ := hL a ha
      rw [sparseEnd_d4Letter_P ha]
      refine ⟨hPs, ?_⟩
      rw [sparseEnd_eq_classEnd (hc 7 (by decide)) (hc 8 (by decide)) (hc 10 (by decide)) hPs hPe]
      exact hP a ha
    by_cases ha' : a < 14
    · obtain ⟨⟨-, hQs⟩, -, hQe⟩ := hL (a - 7) (by omega)
      have e7 : a = 7 + (a - 7) := by omega
      rw [e7, sparseEnd_d4Letter_Q (by omega)]
      refine ⟨hQs, ?_⟩
      rw [sparseEnd_eq_classEnd (hc 14 (by decide)) (hc 16 (by decide)) (hc 20 (by decide)) hQs
        hQe]
      exact hQ _ (by omega)
    by_cases h14 : a = 14
    · rw [d4Letter, ite_eq_right ha, ite_eq_right ha', ite_eq_left h14]
      refine ⟨hm₁, ?_⟩
      rw [show opSubSparse 9 = opSubSparse ((9 : Fin 78) : ℕ) from rfl, sparseEnd_opSubSparse]
      exact hM₁
    · rw [d4Letter, ite_eq_right ha, ite_eq_right ha', ite_eq_right h14]
      refine ⟨hm₂, ?_⟩
      rw [show opSubSparse 18 = opSubSparse ((18 : Fin 78) : ℕ) from rfl, sparseEnd_opSubSparse]
      exact hM₂
  obtain ⟨hTk, hcert⟩ := hT k hk
  exact commute_sparseEnd_of_cert _ _ hcert hTk fun _ _ a _ => hletter a

theorem d4Targets_values :
    d4Targets.getD 0 [] = adSparse 7 ∧ d4Targets.getD 1 [] = tensorSparse 7 ∧
    d4Targets.getD 2 [] = adSparse 14 ∧ d4Targets.getD 3 [] = tensorSparse 14 ∧
    d4Targets.getD 4 [] = adSparse 8 ∧ d4Targets.getD 5 [] = tensorSparse 8 ∧
    d4Targets.getD 6 [] = adSparse 16 ∧ d4Targets.getD 7 [] = tensorSparse 16 ∧
    d4Targets.getD 8 [] = adSparse 9 ∧ d4Targets.getD 9 [] = tensorSparse 9 ∧
    d4Targets.getD 10 [] = adSparse 18 ∧ d4Targets.getD 11 [] = tensorSparse 18 ∧
    d4Targets.getD 12 [] = adSparse 10 ∧ d4Targets.getD 13 [] = tensorSparse 10 ∧
    d4Targets.getD 14 [] = adSparse 20 ∧ d4Targets.getD 15 [] = tensorSparse 20 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem commute_xOp_yOp_of_coeffs (i : Fin Tag.E6.rank) {X : Module.End R (RootModule Tag.E6 R)}
    (h₁ : Commute X (ad R (Finsupp.single (lab ⟨6 + i, six_add_lt i⟩) 1)))
    (h₂ : Commute X (formTensor R (Finsupp.single (lab ⟨6 + i, six_add_lt i⟩) 1)))
    (h₃ : Commute X (ad R (Finsupp.single (lab ⟨12 + 2 * i, twelve_add_lt i⟩) 1)))
    (h₄ : Commute X (formTensor R (Finsupp.single (lab ⟨12 + 2 * i, twelve_add_lt i⟩) 1)))
    (c : R) : Commute X (xOp Tag.E6 R i c) ∧ Commute X (yOp Tag.E6 R i c) := by
  rw [xOp_eq_lab, yOp_eq_lab]
  exact ⟨((Commute.one_right X).add_right (h₁.smul_right c)).add_right (h₂.smul_right _),
    ((Commute.one_right X).add_right (h₃.smul_right c)).add_right (h₄.smul_right _)⟩

theorem commute_of_d4Targets {X : Module.End R (RootModule Tag.E6 R)}
    (h : ∀ k < 16, Commute X (sparseEnd R (d4Targets.getD k []))) (m : ℕ) (hm : m < 4) (c : R) :
    Commute X (xOp Tag.E6 R ⟨m + 1, show m + 1 < 6 by omega⟩ c) ∧
      Commute X (yOp Tag.E6 R ⟨m + 1, show m + 1 < 6 by omega⟩ c) := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15⟩ :=
    d4Targets_values
  have hA : ∀ (A : ℕ) (hA : A < 78) (k : ℕ), k < 16 → d4Targets.getD k [] = adSparse A →
      Commute X (ad R (Finsupp.single (lab ⟨A, hA⟩) 1)) := fun A hA k hk hv => by
    have := h k hk
    rw [hv, show adSparse A = adSparse ((⟨A, hA⟩ : Fin 78) : ℕ) from rfl,
      sparseEnd_adSparse] at this
    exact this
  have hB : ∀ (A : ℕ) (hA : A < 78) (k : ℕ), k < 16 → d4Targets.getD k [] = tensorSparse A →
      Commute X (formTensor R (Finsupp.single (lab ⟨A, hA⟩) 1)) := fun A hA k hk hv => by
    have := h k hk
    rw [hv, show tensorSparse A = tensorSparse ((⟨A, hA⟩ : Fin 78) : ℕ) from rfl,
      sparseEnd_tensorSparse] at this
    exact this
  interval_cases m
  · refine commute_xOp_yOp_of_coeffs _ ?_ ?_ ?_ ?_ c
    exacts [hA 7 (by decide) 0 (by decide) v0, hB 7 (by decide) 1 (by decide) v1,
      hA 14 (by decide) 2 (by decide) v2, hB 14 (by decide) 3 (by decide) v3]
  · refine commute_xOp_yOp_of_coeffs _ ?_ ?_ ?_ ?_ c
    exacts [hA 8 (by decide) 4 (by decide) v4, hB 8 (by decide) 5 (by decide) v5,
      hA 16 (by decide) 6 (by decide) v6, hB 16 (by decide) 7 (by decide) v7]
  · refine commute_xOp_yOp_of_coeffs _ ?_ ?_ ?_ ?_ c
    exacts [hA 9 (by decide) 8 (by decide) v8, hB 9 (by decide) 9 (by decide) v9,
      hA 18 (by decide) 10 (by decide) v10, hB 18 (by decide) 11 (by decide) v11]
  · refine commute_xOp_yOp_of_coeffs _ ?_ ?_ ?_ ?_ c
    exacts [hA 10 (by decide) 12 (by decide) v12, hB 10 (by decide) 13 (by decide) v13,
      hA 20 (by decide) 14 (by decide) v14, hB 20 (by decide) 15 (by decide) v15]

theorem commute_of_d4Cert {e : ℕ} {Ps Qs Ws : List (List (List ℕ))}
    (hL : d4LettersOK e Ps Qs = true) (hT : d4TargetsOK Ps Qs Ws = true)
    {X : Module.End R (RootModule Tag.E6 R)}
    (hP : ∀ r < 7, Commute X (classEnd (R := R) 7 8 10 e r))
    (hQ : ∀ r < 7, Commute X (classEnd (R := R) 14 16 20 e r))
    (hM₁ : Commute X (ad R (Finsupp.single (lab 9) 1) + formTensor R (Finsupp.single (lab 9) 1)))
    (hM₂ : Commute X
      (ad R (Finsupp.single (lab 18) 1) + formTensor R (Finsupp.single (lab 18) 1)))
    (m : ℕ) (hm : m < 4) (c : R) :
    Commute X (xOp Tag.E6 R ⟨m + 1, show m + 1 < 6 by omega⟩ c) ∧
      Commute X (yOp Tag.E6 R ⟨m + 1, show m + 1 < 6 by omega⟩ c) :=
  commute_of_d4Targets (fun _ hk => commute_d4Targets hL hT hP hQ hM₁ hM₂ hk) m hm c

end Semantics

end CFSG.RankThree.Chevalley
