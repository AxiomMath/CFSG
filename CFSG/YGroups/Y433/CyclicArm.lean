module

public import CFSG.YGroups.Y433.Q343
public import CFSG.YGroups.Y433.Y322Embed

public section

namespace CFSG.YGroups

open CFSG.Certificates.CosetEnumeration (evalWord)

@[expose] def cyc343Letter (c : ℕ) : ℕ := [0, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7].getD c 0

@[expose] def cyc433Letter (c : ℕ) : ℕ := [0, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3].getD c 0

@[expose] def armPerm : ℕ → ℕ
  | 1 => 3
  | 2 => 1
  | 3 => 2
  | _ => 0

theorem pairsPreserved_cyc343 : Relabel.PairsPreserved 3 4 3 4 3 3 cyc343Letter := by decide

theorem pairsPreserved_cyc433 : Relabel.PairsPreserved 4 3 3 3 4 3 cyc433Letter := by decide

theorem spider_cyc343 :
    evalWord (fun c => yGen 4 3 3 (cyc343Letter c)) (spiderWord 3 4) ^ 10 = 1 := by
  have e : evalWord (fun c => yGen 4 3 3 (cyc343Letter c)) (spiderWord 3 4) =
      U433.T 3 * U433.T 1 * U433.T 2 := by
    rw [Relabel.evalWord_spiderWord]
    rfl
  rw [e]
  exact Relabel.pow_eq_one_rotate (Relabel.pow_eq_one_rotate U433.spider)

theorem spider_cyc433 :
    evalWord (fun c => yGen 3 4 3 (cyc433Letter c)) (spiderWord 4 3) ^ 10 = 1 := by
  have e : evalWord (fun c => yGen 3 4 3 (cyc433Letter c)) (spiderWord 4 3) =
      Y343.T 2 * Y343.T 3 * Y343.T 1 := by
    rw [Relabel.evalWord_spiderWord]
    rfl
  rw [e]
  exact Relabel.pow_eq_one_rotate Y343.spider

noncomputable def cyc343Hom : Y343 →* U433 :=
  Relabel.hom cyc343Letter pairsPreserved_cyc343 (fun _ _ _ => spider_cyc343)

noncomputable def cyc433Hom : U433 →* Y343 :=
  Relabel.hom cyc433Letter pairsPreserved_cyc433 (fun _ _ _ => spider_cyc433)

theorem cyc343Hom_yGen {c : ℕ} (hc : c < 11) :
    cyc343Hom (yGen 3 4 3 c) = yGen 4 3 3 (cyc343Letter c) := Relabel.hom_yGen hc

theorem cyc433Hom_yGen {c : ℕ} (hc : c < 11) :
    cyc433Hom (yGen 4 3 3 c) = yGen 3 4 3 (cyc433Letter c) := Relabel.hom_yGen hc

theorem cyc433Letter_cyc343Letter : ∀ c < 11, cyc433Letter (cyc343Letter c) = c := by decide

theorem cyc343Letter_cyc433Letter : ∀ c < 11, cyc343Letter (cyc433Letter c) = c := by decide

theorem cyc343Letter_lt : ∀ c < 11, cyc343Letter c < 11 := by decide

theorem cyc433Letter_lt : ∀ c < 11, cyc433Letter c < 11 := by decide

noncomputable def cyc343Equiv : Y343 ≃* U433 :=
  MonoidHom.toMulEquiv cyc343Hom cyc433Hom
    (by
      refine PresentedGroup.ext fun c => ?_
      have hc : (c : ℕ) < 11 := c.2
      rw [MonoidHom.comp_apply, MonoidHom.id_apply, ← yGen_of_lt c.2, cyc343Hom_yGen hc,
        cyc433Hom_yGen (cyc343Letter_lt c hc), cyc433Letter_cyc343Letter c hc])
    (by
      refine PresentedGroup.ext fun c => ?_
      have hc : (c : ℕ) < 11 := c.2
      rw [MonoidHom.comp_apply, MonoidHom.id_apply, ← yGen_of_lt c.2, cyc433Hom_yGen hc,
        cyc343Hom_yGen (cyc433Letter_lt c hc), cyc343Letter_cyc433Letter c hc])

theorem cyc343Equiv_yGen {c : ℕ} (hc : c < 11) :
    cyc343Equiv (yGen 3 4 3 c) = yGen 4 3 3 (cyc343Letter c) := cyc343Hom_yGen hc

theorem cyc343Equiv_A : cyc343Equiv Y343.A = U433.A := cyc343Equiv_yGen (by decide)

theorem cyc343Equiv_B {i : ℕ} (hi : i = 1 ∨ i = 2 ∨ i = 3) :
    cyc343Equiv (Y343.B i) = U433.B (armPerm i) := by
  rcases hi with rfl | rfl | rfl <;> exact (cyc343Equiv_yGen (by decide)).trans rfl

theorem cyc343Equiv_C {i : ℕ} (hi : i = 1 ∨ i = 2 ∨ i = 3) :
    cyc343Equiv (Y343.C i) = U433.C (armPerm i) := by
  rcases hi with rfl | rfl | rfl <;> exact (cyc343Equiv_yGen (by decide)).trans rfl

theorem cyc343Equiv_D {i : ℕ} (hi : i = 1 ∨ i = 2 ∨ i = 3) :
    cyc343Equiv (Y343.D i) = U433.D (armPerm i) := by
  rcases hi with rfl | rfl | rfl <;> exact (cyc343Equiv_yGen (by decide)).trans rfl

theorem cyc343Equiv_E₂ : cyc343Equiv Y343.E₂ = U433.E₁ := cyc343Equiv_yGen (by decide)

theorem cyc343Equiv_F {i j k : ℕ} (hi : i = 1 ∨ i = 2 ∨ i = 3) (hj : j = 1 ∨ j = 2 ∨ j = 3)
    (hk : k = 1 ∨ k = 2 ∨ k = 3) :
    cyc343Equiv (Y343.F i j k) = F433 (armPerm i) (armPerm j) (armPerm k) := by
  simp only [Y343.F, F433, map_pow, map_mul, cyc343Equiv_A, cyc343Equiv_B hi, cyc343Equiv_C hi,
    cyc343Equiv_D hi, cyc343Equiv_B hj, cyc343Equiv_C hj, cyc343Equiv_B hk]

theorem cyc343Equiv_Q343Extra : cyc343Equiv Q343Extra = F433 2 3 1 :=
  cyc343Equiv_F (Or.inr (Or.inr rfl)) (Or.inl rfl) (Or.inr (Or.inl rfl))

theorem Q343ExtraWord_map_cyc343Letter : Q343ExtraWord.map cyc343Letter =
    (List.replicate 9 [0, U433.armStart 2, U433.armStart 2 + 1, U433.armStart 2 + 2,
      U433.armStart 3, U433.armStart 3 + 1, U433.armStart 1]).flatten := by
  decide

theorem cyc343Equiv_F123 : cyc343Equiv (Y343.F 1 2 3) = F433 3 1 2 :=
  cyc343Equiv_F (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))

noncomputable def Q343EquivR433 :
    Q343 ≃* R433 :=
  QuotientGroup.congr (Subgroup.normalClosure {Q343Extra})
    (Subgroup.normalClosure {F433 2 1 3}) cyc343Equiv (by
      have h : (cyc343Equiv : Y343 →* U433) Q343Extra = F433 2 1 3 :=
        cyc343Equiv_Q343Extra.trans F433_231_eq_213
      rw [Subgroup.map_normalClosure {Q343Extra} (cyc343Equiv : Y343 →* U433)
        cyc343Equiv.surjective, Set.image_singleton, h])

theorem Q343EquivR433_π
    (x : Y343) : Q343EquivR433 (Q343.π x) = R433.π (cyc343Equiv x) :=
  QuotientGroup.congr_mk _ _ _ _ x

theorem Q343_exists_mulEquiv_R433 :
    ∃ e : Q343 ≃* R433,
      e Q343.vA = R433.A ∧
      (e (Q343.vB 2) = R433.B 1 ∧ e (Q343.vC 2) = R433.C 1 ∧ e (Q343.vD 2) = R433.D 1 ∧
        e Q343.vE₂ = R433.E₁) ∧
      (e (Q343.vB 3) = R433.B 2 ∧ e (Q343.vC 3) = R433.C 2 ∧ e (Q343.vD 3) = R433.D 2) ∧
      (e (Q343.vB 1) = R433.B 3 ∧ e (Q343.vC 1) = R433.C 3 ∧ e (Q343.vD 1) = R433.D 3) :=
  ⟨Q343EquivR433, by
    refine ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
    · exact (Q343EquivR433_π _).trans (congrArg R433.π cyc343Equiv_A)
    · exact (Q343EquivR433_π _).trans (congrArg R433.π (cyc343Equiv_B (Or.inr (Or.inl rfl))))
    · exact (Q343EquivR433_π _).trans (congrArg R433.π (cyc343Equiv_C (Or.inr (Or.inl rfl))))
    · exact (Q343EquivR433_π _).trans (congrArg R433.π (cyc343Equiv_D (Or.inr (Or.inl rfl))))
    · exact (Q343EquivR433_π _).trans (congrArg R433.π cyc343Equiv_E₂)
    · exact (Q343EquivR433_π _).trans (congrArg R433.π (cyc343Equiv_B (Or.inr (Or.inr rfl))))
    · exact (Q343EquivR433_π _).trans (congrArg R433.π (cyc343Equiv_C (Or.inr (Or.inr rfl))))
    · exact (Q343EquivR433_π _).trans (congrArg R433.π (cyc343Equiv_D (Or.inr (Or.inr rfl))))
    · exact (Q343EquivR433_π _).trans (congrArg R433.π (cyc343Equiv_B (Or.inl rfl)))
    · exact (Q343EquivR433_π _).trans (congrArg R433.π (cyc343Equiv_C (Or.inl rfl)))
    · exact (Q343EquivR433_π _).trans (congrArg R433.π (cyc343Equiv_D (Or.inl rfl)))⟩

theorem Q343_cyclic_arm_identification :
    (∃ e : Q343 ≃* R433,
      e Q343.vA = R433.A ∧
      (e (Q343.vB 2) = R433.B 1 ∧ e (Q343.vC 2) = R433.C 1 ∧ e (Q343.vD 2) = R433.D 1 ∧
        e Q343.vE₂ = R433.E₁) ∧
      (e (Q343.vB 3) = R433.B 2 ∧ e (Q343.vC 3) = R433.C 2 ∧ e (Q343.vD 3) = R433.D 2) ∧
      (e (Q343.vB 1) = R433.B 3 ∧ e (Q343.vC 1) = R433.C 3 ∧ e (Q343.vD 1) = R433.D 3)) ∧
    Q343ExtraWord.map cyc343Letter =
      (List.replicate 9 [0, U433.armStart 2, U433.armStart 2 + 1, U433.armStart 2 + 2,
        U433.armStart 3, U433.armStart 3 + 1, U433.armStart 1]).flatten ∧
    F433 2 3 1 = F433 2 1 3 :=
  ⟨Q343_exists_mulEquiv_R433, Q343ExtraWord_map_cyc343Letter, F433_231_eq_213⟩

end CFSG.YGroups
