module

public import CFSG.RankThree.PartOne.CTP.SeitzLedger

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.RankThree.PartOne.Census3 (IsoLie)

@[expose] def ExtSeitzAtInnerFor (d : TauCeti.LieTypeIndex) (P : ℕ → Prop) : Prop :=
  ∀ (K : Type) [Group K] [Finite K] [IsSimpleGroup K], (∃ a b : K, a * b ≠ b * a) →
    IsoLie K d → ∀ p : ℕ, p.Prime → 5 ≤ p → p ≠ d.characteristic → P p →
      ∀ E : Subgroup (MulAut K), CFSG.IsElementaryAbelian p E → Nat.card E = p ^ 2 →
        (∀ φ ∈ E, ∃ g : K, φ = MulAut.conj g) →
        Subgroup.closure {k : K | ∃ F : Subgroup (MulAut K), F ≤ E ∧ F ≠ ⊥ ∧
          ∀ φ ∈ F, φ k = k} = ⊤ ∨ (p = 5 ∧ (d = .tits ∨ d = .suzuki 2))

@[expose] def ExtSeitzAtOuterFor (d : TauCeti.LieTypeIndex) (P : ℕ → Prop) : Prop :=
  ∀ (K : Type) [Group K] [Finite K] [IsSimpleGroup K], (∃ a b : K, a * b ≠ b * a) →
    IsoLie K d → ∀ p : ℕ, p.Prime → 5 ≤ p → p ≠ d.characteristic → P p →
      ∀ E : Subgroup (MulAut K), CFSG.IsElementaryAbelian p E → Nat.card E = p ^ 2 →
        ¬ (∀ φ ∈ E, ∃ g : K, φ = MulAut.conj g) →
        Subgroup.closure {k : K | ∃ F : Subgroup (MulAut K), F ≤ E ∧ F ≠ ⊥ ∧
          ∀ φ ∈ F, φ k = k} = ⊤ ∨ (p = 5 ∧ (d = .tits ∨ d = .suzuki 2))

theorem ExtSeitzAtInnerFor.of_inner {d : TauCeti.LieTypeIndex} {P : ℕ → Prop}
    (h : ExtSeitzAtInner d) : ExtSeitzAtInnerFor d P :=
  fun K _ _ _ hnab hiso p hp hp5 hpd _ E hE hcard hinner =>
    h K hnab hiso p hp hp5 hpd E hE hcard hinner

theorem ExtSeitzAtOuterFor.of_outer {d : TauCeti.LieTypeIndex} {P : ℕ → Prop}
    (h : ExtSeitzAtOuter d) : ExtSeitzAtOuterFor d P :=
  fun K _ _ _ hnab hiso p hp hp5 hpd _ E hE hcard hout => h K hnab hiso p hp hp5 hpd E hE hcard hout

theorem ExtSeitzAtInnerFor.mono {d : TauCeti.LieTypeIndex} {P Q : ℕ → Prop}
    (hQP : ∀ p, Q p → P p) (h : ExtSeitzAtInnerFor d P) : ExtSeitzAtInnerFor d Q :=
  fun K _ _ _ hnab hiso p hp hp5 hpd hQ E hE hcard hinner =>
    h K hnab hiso p hp hp5 hpd (hQP p hQ) E hE hcard hinner

theorem ExtSeitzAtOuterFor.mono {d : TauCeti.LieTypeIndex} {P Q : ℕ → Prop}
    (hQP : ∀ p, Q p → P p) (h : ExtSeitzAtOuterFor d P) : ExtSeitzAtOuterFor d Q :=
  fun K _ _ _ hnab hiso p hp hp5 hpd hQ E hE hcard hout =>
    h K hnab hiso p hp hp5 hpd (hQP p hQ) E hE hcard hout

theorem extSeitzAtInner_of_split {d : TauCeti.LieTypeIndex} (P : ℕ → Prop)
    (h1 : ExtSeitzAtInnerFor d P) (h2 : ExtSeitzAtInnerFor d fun p => ¬ P p) :
    ExtSeitzAtInner d := by
  intro K _ _ _ hnab hiso p hp hp5 hpd E hE hcard hinner
  by_cases hP : P p
  · exact h1 K hnab hiso p hp hp5 hpd hP E hE hcard hinner
  · exact h2 K hnab hiso p hp hp5 hpd hP E hE hcard hinner

theorem extSeitzAtOuter_of_split {d : TauCeti.LieTypeIndex} (P : ℕ → Prop)
    (h1 : ExtSeitzAtOuterFor d P) (h2 : ExtSeitzAtOuterFor d fun p => ¬ P p) :
    ExtSeitzAtOuter d := by
  intro K _ _ _ hnab hiso p hp hp5 hpd E hE hcard hout
  by_cases hP : P p
  · exact h1 K hnab hiso p hp hp5 hpd hP E hE hcard hout
  · exact h2 K hnab hiso p hp hp5 hpd hP E hE hcard hout

theorem seitzOuterProved_A1 (q : TauCeti.PrimePower) : SeitzOuterProved (.A 1 q) :=
  Or.inl ⟨q, rfl⟩

theorem seitzOuterProved_A {m : ℕ} {q : TauCeti.PrimePower} (h2 : 2 ≤ m)
    (hmq : m ≤ 3 ∨ q.card = 2) (he : q.exponent < 5) : SeitzOuterProved (.A m q) :=
  Or.inr (Or.inl ⟨m, q, rfl, h2, hmq, he⟩)

theorem seitzOuterProved_B2 {q : TauCeti.PrimePower} (he : q.exponent < 5) :
    SeitzOuterProved (.B 2 q) :=
  Or.inr (Or.inr (Or.inl ⟨q, rfl, he⟩))

theorem seitzOuterProved_B {r : ℕ} {q : TauCeti.PrimePower} (hr : 3 ≤ r) (hq : q.p = 2)
    (he : q.exponent < 5) : SeitzOuterProved (.B r q) :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨r, q, rfl, hr, hq, he⟩)))

theorem seitzOuterProved_twistedD4 {q : TauCeti.PrimePower} (hq : q.p = 2) (he : q.exponent < 5) :
    SeitzOuterProved (.twistedD 4 q) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl, hq, he⟩))))

theorem seitzOuterProved_D4 {q : TauCeti.PrimePower} (hq : q.p = 2) (he : q.exponent < 5) :
    SeitzOuterProved (.D 4 q) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl, hq, he⟩)))))

theorem seitzOuterProved_twistedA2 {q : TauCeti.PrimePower} (he : q.exponent < 5) :
    SeitzOuterProved (.twistedA 2 q) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl, he⟩))))))

theorem seitzOuterProved_twistedA3 {q : TauCeti.PrimePower} (he : q.exponent < 5) :
    SeitzOuterProved (.twistedA 3 q) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl, he⟩)))))))

theorem seitzOuterProved_twistedA4 {q : TauCeti.PrimePower} (h5 : ¬ 5 ∣ q.p ^ q.exponent + 1)
    (he : q.exponent < 5) : SeitzOuterProved (.twistedA 4 q) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨q, rfl, h5, he⟩))))))))

theorem seitzOuterProved_twistedA5 {q : TauCeti.PrimePower} (hq : q.p = 2) (he : q.exponent = 1) :
    SeitzOuterProved (.twistedA 5 q) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨q, rfl, hq, he⟩)))))))))

theorem seitzOuterProved_tits : SeitzOuterProved .tits :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl rfl))))))))))

theorem seitzOuterProved_reeG2_one : SeitzOuterProved (.reeG2 1) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl rfl)))))))))))

theorem seitzOuterProved_suzuki {m : ℕ} (hm : 2 * m + 1 < 5) : SeitzOuterProved (.suzuki m) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr ⟨m, rfl, hm⟩)))))))))))

theorem seitzSmallExponent_G2 {q : TauCeti.PrimePower} (he : q.exponent < 5) :
    SeitzSmallExponent (.G2 q) :=
  Or.inl ⟨q, Or.inl rfl, he⟩

theorem seitzSmallExponent_trialityD4 {q : TauCeti.PrimePower} (he : q.exponent < 5) :
    SeitzSmallExponent (.trialityD4 q) :=
  Or.inl ⟨q, Or.inr (Or.inl rfl), he⟩

theorem seitzSmallExponent_F4 {q : TauCeti.PrimePower} (he : q.exponent < 5) :
    SeitzSmallExponent (.F4 q) :=
  Or.inl ⟨q, Or.inr (Or.inr rfl), he⟩

theorem seitzSmallExponent_reeF4 {m : ℕ} (hm : 2 * m + 1 < 5) : SeitzSmallExponent (.reeF4 m) :=
  Or.inr ⟨m, rfl, hm⟩

theorem thm3_outer_cases {d : TauCeti.LieTypeIndex} (hd : Thm3LieIndex d) :
    SeitzOuterProved d ∨ SeitzUnitaryFive d ∨ SeitzSmallExponent d ∨
    (∃ q : TauCeti.PrimePower, q.p = 2 ∧ 5 ≤ q.exponent ∧ d = .A 2 q) ∨
    (∃ q : TauCeti.PrimePower, q.p = 2 ∧ 5 ≤ q.exponent ∧ d = .A 3 q) ∨
    (∃ q : TauCeti.PrimePower, q.p = 2 ∧ 5 ≤ q.exponent ∧ d = .twistedA 2 q) ∨
    (∃ q : TauCeti.PrimePower, q.p = 2 ∧ 5 ≤ q.exponent ∧ d = .twistedA 3 q) ∨
    (∃ q : TauCeti.PrimePower, q.p = 2 ∧ 5 ≤ q.exponent ∧ ¬ 5 ∣ q.p ^ q.exponent + 1 ∧
      d = .twistedA 4 q) ∨
    (∃ q : TauCeti.PrimePower, q.p = 2 ∧ 5 ≤ q.exponent ∧ d = .B 2 q) ∨
    (∃ q : TauCeti.PrimePower, q.p = 2 ∧ 5 ≤ q.exponent ∧ d = .B 3 q) ∨
    (∃ q : TauCeti.PrimePower, q.p = 2 ∧ 5 ≤ q.exponent ∧ d = .twistedD 4 q) ∨
    (∃ q : TauCeti.PrimePower, q.p = 2 ∧ 5 ≤ q.exponent ∧ d = .G2 q) ∨
    (∃ q : TauCeti.PrimePower, q.p = 2 ∧ 5 ≤ q.exponent ∧ d = .trialityD4 q) ∨
    (∃ m : ℕ, 2 ≤ m ∧ d = .suzuki m) ∨ (∃ m : ℕ, 2 ≤ m ∧ d = .reeF4 m) := by
  rcases hd with ⟨q, -, -, rfl⟩ | ⟨q, -, hqe, rfl | rfl⟩ | rfl |
    ⟨q, -, hqe, rfl | rfl | rfl | rfl⟩ | ⟨q, -, rfl⟩ | ⟨m, rfl⟩ |
    ⟨q, hq2, rfl | rfl | rfl | rfl | rfl | rfl | rfl⟩ | ⟨m, rfl⟩ | rfl |
    ⟨q, hq2, rfl | rfl | rfl⟩ | ⟨q, hq2, he, rfl | rfl | rfl | rfl | rfl | rfl | rfl⟩
  · exact Or.inl (seitzOuterProved_A1 q)
  · exact Or.inl (seitzOuterProved_A (by norm_num) (Or.inl (by norm_num)) (by omega))
  · exact Or.inl (seitzOuterProved_twistedA2 (by omega))
  · exact Or.inl seitzOuterProved_reeG2_one
  · right; right; left; exact seitzSmallExponent_G2 (by omega)
  · exact Or.inl (seitzOuterProved_B2 (by omega))
  · exact Or.inl (seitzOuterProved_twistedA3 (by omega))
  · exact Or.inl (seitzOuterProved_A (by norm_num) (Or.inl (by norm_num)) (by omega))
  · exact Or.inl (seitzOuterProved_A1 q)
  · by_cases hm : 2 * m + 1 < 5
    · exact Or.inl (seitzOuterProved_suzuki hm)
    · iterate 13 right
      left
      exact ⟨m, by omega, rfl⟩
  · by_cases he : q.exponent < 5
    · exact Or.inl (seitzOuterProved_twistedA2 he)
    · iterate 5 right
      left
      exact ⟨q, hq2, by omega, rfl⟩
  · by_cases he : q.exponent < 5
    · exact Or.inl (seitzOuterProved_A (by norm_num) (Or.inl (by norm_num)) he)
    · iterate 3 right
      left
      exact ⟨q, hq2, by omega, rfl⟩
  · by_cases he : q.exponent < 5
    · exact Or.inl (seitzOuterProved_B2 he)
    · iterate 8 right
      left
      exact ⟨q, hq2, by omega, rfl⟩
  · by_cases he : q.exponent < 5
    · right; right; left; exact seitzSmallExponent_G2 he
    · iterate 11 right
      left
      exact ⟨q, hq2, by omega, rfl⟩
  · by_cases he : q.exponent < 5
    · exact Or.inl (seitzOuterProved_twistedA3 he)
    · iterate 6 right
      left
      exact ⟨q, hq2, by omega, rfl⟩
  · by_cases h5 : 5 ∣ q.p ^ q.exponent + 1
    · right; left; exact ⟨q, rfl, h5⟩
    · by_cases he : q.exponent < 5
      · exact Or.inl (seitzOuterProved_twistedA4 h5 he)
      · iterate 7 right
        left
        exact ⟨q, hq2, by omega, h5, rfl⟩
  · by_cases he : q.exponent < 5
    · right; right; left; exact seitzSmallExponent_trialityD4 he
    · iterate 12 right
      left
      exact ⟨q, hq2, by omega, rfl⟩
  · by_cases hm : 2 * m + 1 < 5
    · right; right; left; exact seitzSmallExponent_reeF4 hm
    · iterate 14 right
      exact ⟨m, by omega, rfl⟩
  · exact Or.inl seitzOuterProved_tits
  · by_cases he : q.exponent < 5
    · exact Or.inl (seitzOuterProved_A (by norm_num) (Or.inl (by norm_num)) he)
    · iterate 4 right
      left
      exact ⟨q, hq2, by omega, rfl⟩
  · by_cases he : q.exponent < 5
    · exact Or.inl (seitzOuterProved_B (by norm_num) hq2 he)
    · iterate 9 right
      left
      exact ⟨q, hq2, by omega, rfl⟩
  · by_cases he : q.exponent < 5
    · exact Or.inl (seitzOuterProved_twistedD4 hq2 he)
    · iterate 10 right
      left
      exact ⟨q, hq2, by omega, rfl⟩
  · have hcard : q.card = 2 := by simp [TauCeti.PrimePower.card_def, hq2, he]
    exact Or.inl (seitzOuterProved_A (by norm_num) (Or.inr hcard) (by omega))
  · have hcard : q.card = 2 := by simp [TauCeti.PrimePower.card_def, hq2, he]
    exact Or.inl (seitzOuterProved_A (by norm_num) (Or.inr hcard) (by omega))
  · have hcard : q.card = 2 := by simp [TauCeti.PrimePower.card_def, hq2, he]
    exact Or.inl (seitzOuterProved_A (by norm_num) (Or.inr hcard) (by omega))
  · exact Or.inl (seitzOuterProved_twistedA5 hq2 he)
  · exact Or.inl (seitzOuterProved_B (by norm_num) hq2 (by omega))
  · exact Or.inl (seitzOuterProved_D4 hq2 (by omega))
  · right; right; left; exact seitzSmallExponent_F4 (by omega)

end CFSG.RankThree.PartOne.CTP
