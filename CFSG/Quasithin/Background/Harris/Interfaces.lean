module

public import CFSG.Quasithin.Background.G9Stmts

public section

namespace CFSG.Quasithin.G11.Harris

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

structure OneCompSetting (Γ A L : Subgroup (GLV V)) (m : ℕ) : Prop where
  quotient : IsQuotientOfSQTKTauCeti ↥Γ
  A_le : A ≤ Γ
  A_elem : IsElemAbelian 2 A
  A_card : Nat.card ↥A = 2 ^ m
  bound : Module.finrank (ZMod 2) V ≤ 2 * (m + 1)
  L_comp : IsComponentOf L Γ
  L_comm : ∃ a ∈ A, ∃ l ∈ L, a * l ≠ l * a
  L_normal : ∀ γ ∈ Γ, ∀ l ∈ L, γ * l * γ⁻¹ ∈ L
  L_irr : IsIrr L ⊤

theorem OneCompSetting.of_g93Hyp {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m) :
    OneCompSetting Γ A L m :=
  ⟨h.quotient, h.A_le, h.A_elem, h.A_card, h.bound, h.L_comp, h.L_comm, h.H_normal, h.H_irr⟩

@[expose] def CompType (X : Type) [Group X] : Prop :=
  (IsSimpleGroup X ∧ A23List X) ∨ (Nat.card (Subgroup.center X) = 3 ∧ A36Case2List X)

@[expose] def OneCompFor (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (Γ A L : Subgroup (GLV V)) (m : ℕ),
    OneCompSetting Γ A L m → P ↥L → G93Concl Γ L m

@[expose] def DescentOne : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (Γ A L : Subgroup (GLV V)) (m : ℕ),
    G93Hyp Γ A L L m → CompType ↥L

@[expose] def TwoComp : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (Γ A L H : Subgroup (GLV V)) (m : ℕ), G93Hyp Γ A L H m →
    (∃ L₂ : Subgroup (GLV V), IsComponentOf L₂ Γ ∧ L₂ ≠ L ∧ H = L ⊔ L₂ ∧ QuasiEquivalent L L₂) →
    G93Case14 H m ∨ G93Case15 H m

theorem g93Stmt_of_interfaces (hD : DescentOne) (hT : TwoComp) (hO : OneCompFor CompType) :
    G93Stmt := by
  intro V _ _ _ Γ A L H m h
  rcases h.H_eq with rfl | hL₂
  · exact hO V Γ A H m (OneCompSetting.of_g93Hyp h) (hD V Γ A H m h)
  · rcases hT V Γ A L H m h hL₂ with h14 | h15
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h14))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h15)))))))))))))))

theorem OneCompFor.mono {P Q : ∀ (X : Type) [Group X], Prop}
    (hPQ : ∀ (X : Type) [Group X], Q X → P X) (h : OneCompFor P) : OneCompFor Q :=
  fun V _ _ _ Γ A L m hs hQ => h V Γ A L m hs (hPQ ↥L hQ)

theorem OneCompFor.or {P Q : ∀ (X : Type) [Group X], Prop} (hP : OneCompFor P)
    (hQ : OneCompFor Q) : OneCompFor fun X _ => P X ∨ Q X :=
  fun V _ _ _ Γ A L m hs hPQ => hPQ.elim (hP V Γ A L m hs) (hQ V Γ A L m hs)

@[expose] def FamAlt (n : ℕ) (X : Type) [Group X] : Prop :=
  IsSimpleGroup X ∧ Nonempty (X ≃* alternatingGroup (Fin n))

@[expose] def FamOddL2 (X : Type) [Group X] : Prop :=
  IsSimpleGroup X ∧ ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
    ∃ f : ℕ, (f = 1 ∨ f = 2) ∧ StatedClassicalModel X .PSL 2 p f

@[expose] def FamOddL3 (X : Type) [Group X] : Prop :=
  IsSimpleGroup X ∧ ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ StatedClassicalModel X .PSL 3 p 1

@[expose] def FamOddU3 (X : Type) [Group X] : Prop :=
  IsSimpleGroup X ∧ ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ StatedClassicalModel X .PSU 3 p 1

@[expose] def FamL2 (X : Type) [Group X] : Prop :=
  IsSimpleGroup X ∧ ∃ f : ℕ, 2 ≤ f ∧ StatedClassicalModel X .PSL 2 2 f

@[expose] def FamL3 (X : Type) [Group X] : Prop :=
  IsSimpleGroup X ∧ ∃ f : ℕ, 1 ≤ f ∧ StatedClassicalModel X .PSL 3 2 f

@[expose] def FamU3 (X : Type) [Group X] : Prop :=
  IsSimpleGroup X ∧ ∃ f : ℕ, 2 ≤ f ∧ StatedClassicalModel X .PSU 3 2 f

@[expose] def FamSp4 (X : Type) [Group X] : Prop :=
  IsSimpleGroup X ∧ ∃ f : ℕ, 2 ≤ f ∧ StatedClassicalModel X .PSp 2 2 f

@[expose] def FamG2 (X : Type) [Group X] : Prop :=
  IsSimpleGroup X ∧ ∃ f : ℕ, 2 ≤ f ∧ ChevalleyExceptionalModel X .G2 2 f

@[expose] def Fam3D4 (X : Type) [Group X] : Prop :=
  IsSimpleGroup X ∧ ∃ f : ℕ, 1 ≤ f ∧ ChevalleyExceptionalModel X .trialityD4 2 f

@[expose] def Fam2F4 (X : Type) [Group X] : Prop :=
  IsSimpleGroup X ∧ ∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ ReeTitsModel X .twistedF4 2 f

@[expose] def FamSz (X : Type) [Group X] : Prop :=
  IsSimpleGroup X ∧ ∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ SuzukiModel X 2 f

@[expose] def FamTits (X : Type) [Group X] : Prop :=
  IsSimpleGroup X ∧ ReeTitsModel X .Tits 2 1

@[expose] def FamLn2 (n : ℕ) (X : Type) [Group X] : Prop :=
  IsSimpleGroup X ∧ StatedClassicalModel X .PSL n 2 1

@[expose] def FamSpor (s : TauCeti.SporadicName) (X : Type) [Group X] : Prop :=
  IsSimpleGroup X ∧ Nonempty (X ≃* NativeSporadic.Carrier s)

@[expose] def FamCoverSL3 (X : Type) [Group X] : Prop :=
  Nat.card (Subgroup.center X) = 3 ∧ ∃ (s : Bool) (p e : ℕ), p.Prime ∧ 1 ≤ e ∧
    ((p = 2 ∧ Int.ModEq 3 ((p ^ e : ℕ) : ℤ) (if s then 1 else -1)) ∨ (p ≠ 2 ∧ e = 1)) ∧
    IsSLEps3 s (p ^ e) X

@[expose] def FamHat (S : Type) [Group S] (X : Type) [Group X] : Prop :=
  Nat.card (Subgroup.center X) = 3 ∧ IsHat X S

@[expose] def FamOddL2Small (X : Type) [Group X] : Prop :=
  IsSimpleGroup X ∧ ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
    ∃ f : ℕ, (f = 1 ∨ f = 2) ∧ (p ^ f = 5 ∨ p ^ f = 7 ∨ p ^ f = 9) ∧
      StatedClassicalModel X .PSL 2 p f

@[expose] def FamOddL2Big (X : Type) [Group X] : Prop :=
  IsSimpleGroup X ∧ ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
    ∃ f : ℕ, (f = 1 ∨ f = 2) ∧ p ^ f ≠ 5 ∧ p ^ f ≠ 7 ∧ p ^ f ≠ 9 ∧
      StatedClassicalModel X .PSL 2 p f

@[expose] def FamU33 (X : Type) [Group X] : Prop :=
  IsSimpleGroup X ∧ StatedClassicalModel X .PSU 3 3 1

@[expose] def FamOddU3Big (X : Type) [Group X] : Prop :=
  IsSimpleGroup X ∧ ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ StatedClassicalModel X .PSU 3 p 1

@[expose] def FamCoverSL3Two (X : Type) [Group X] : Prop :=
  Nat.card (Subgroup.center X) = 3 ∧ ∃ e : ℕ, 1 ≤ e ∧ Int.ModEq 3 ((2 ^ e : ℕ) : ℤ) 1 ∧
    IsSL3 (2 ^ e) X

@[expose] def FamCoverSU3Two (X : Type) [Group X] : Prop :=
  Nat.card (Subgroup.center X) = 3 ∧ ∃ e : ℕ, 1 ≤ e ∧ Int.ModEq 3 ((2 ^ e : ℕ) : ℤ) (-1) ∧
    IsSU3 (2 ^ e) X

@[expose] def FamCoverOdd (X : Type) [Group X] : Prop :=
  Nat.card (Subgroup.center X) = 3 ∧ ∃ (s : Bool) (p : ℕ), p.Prime ∧ p ≠ 2 ∧ IsSLEps3 s p X

theorem oneCompFor_famOddL2 (hS : OneCompFor FamOddL2Small) (hB : OneCompFor FamOddL2Big) :
    OneCompFor FamOddL2 := by
  intro V _ _ _ Γ A L m hs ⟨hsimp, p, hp, hp2, f, hf, hm⟩
  by_cases h : p ^ f = 5 ∨ p ^ f = 7 ∨ p ^ f = 9
  · exact hS V Γ A L m hs ⟨hsimp, p, hp, hp2, f, hf, h, hm⟩
  · push Not at h
    exact hB V Γ A L m hs ⟨hsimp, p, hp, hp2, f, hf, h.1, h.2.1, h.2.2, hm⟩

theorem oneCompFor_famOddU3 (h3 : OneCompFor FamU33) (hB : OneCompFor FamOddU3Big) :
    OneCompFor FamOddU3 := by
  intro V _ _ _ Γ A L m hs ⟨hsimp, p, hp, hp2, hm⟩
  by_cases h : p = 3
  · subst h
    exact h3 V Γ A L m hs ⟨hsimp, hm⟩
  · have h5 : 5 ≤ p := by
      have := hp.two_le
      rcases Nat.lt_or_ge p 5 with hlt | hge
      · interval_cases p <;> simp_all (config := { decide := true })
      · exact hge
    exact hB V Γ A L m hs ⟨hsimp, p, hp, h5, hm⟩

theorem oneCompFor_famCoverSL3 (h1 : OneCompFor FamCoverSL3Two) (h2 : OneCompFor FamCoverSU3Two)
    (h3 : OneCompFor FamCoverOdd) : OneCompFor FamCoverSL3 := by
  intro V _ _ _ Γ A L m hs ⟨hz, s, p, e, hp, he, hpe, hm⟩
  rcases hpe with ⟨rfl, hmod⟩ | ⟨hp2, rfl⟩
  · cases s
    · exact h2 V Γ A L m hs ⟨hz, e, he, by simpa using hmod, hm⟩
    · exact h1 V Γ A L m hs ⟨hz, e, he, by simpa using hmod, hm⟩
  · exact h3 V Γ A L m hs ⟨hz, s, p, hp, hp2, by simpa using hm⟩

theorem oneCompFor_compType
    (h5 : OneCompFor (FamAlt 5)) (h6 : OneCompFor (FamAlt 6)) (h7 : OneCompFor (FamAlt 7))
    (h8 : OneCompFor (FamAlt 8)) (hOL2 : OneCompFor FamOddL2) (hOL3 : OneCompFor FamOddL3)
    (hOU3 : OneCompFor FamOddU3) (hL2 : OneCompFor FamL2) (hL3 : OneCompFor FamL3)
    (hU3 : OneCompFor FamU3) (hSp4 : OneCompFor FamSp4) (hG2 : OneCompFor FamG2)
    (h3D4 : OneCompFor Fam3D4) (h2F4 : OneCompFor Fam2F4) (hSz : OneCompFor FamSz)
    (hTits : OneCompFor FamTits) (hL4 : OneCompFor (FamLn2 4)) (hL5 : OneCompFor (FamLn2 5))
    (hSpor : ∀ s : TauCeti.SporadicName, (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨
      s = .J1 ∨ s = .J2 ∨ s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru) → OneCompFor (FamSpor s))
    (hCSL3 : OneCompFor FamCoverSL3) (hA6 : OneCompFor (FamHat (alternatingGroup (Fin 6))))
    (hA7 : OneCompFor (FamHat (alternatingGroup (Fin 7))))
    (hM22 : OneCompFor (FamHat (NativeSporadic.Carrier .M22))) :
    OneCompFor CompType := by
  intro V _ _ _ Γ A L m hs hL
  rcases hL with ⟨hsimp, hlist⟩ | ⟨hz, hlist⟩
  · rcases hlist with ⟨n, hn5, hn8, he⟩ | ⟨p, hp, hp2, (⟨f, hf, hm⟩ | hm | hm)⟩ |
      (⟨f, (⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hfo, hf, hm⟩ |
        ⟨hfo, hf, hm⟩)⟩ | hm) | ⟨n, hn, hm⟩ | ⟨s, hs', he⟩
    · interval_cases n
      · exact h5 V Γ A L m hs ⟨hsimp, he⟩
      · exact h6 V Γ A L m hs ⟨hsimp, he⟩
      · exact h7 V Γ A L m hs ⟨hsimp, he⟩
      · exact h8 V Γ A L m hs ⟨hsimp, he⟩
    · exact hOL2 V Γ A L m hs ⟨hsimp, p, hp, hp2, f, hf, hm⟩
    · exact hOL3 V Γ A L m hs ⟨hsimp, p, hp, hp2, hm⟩
    · exact hOU3 V Γ A L m hs ⟨hsimp, p, hp, hp2, hm⟩
    · exact hL2 V Γ A L m hs ⟨hsimp, f, hf, hm⟩
    · exact hL3 V Γ A L m hs ⟨hsimp, f, hf, hm⟩
    · exact hU3 V Γ A L m hs ⟨hsimp, f, hf, hm⟩
    · exact hSp4 V Γ A L m hs ⟨hsimp, f, hf, hm⟩
    · exact hG2 V Γ A L m hs ⟨hsimp, f, hf, hm⟩
    · exact h3D4 V Γ A L m hs ⟨hsimp, f, hf, hm⟩
    · exact h2F4 V Γ A L m hs ⟨hsimp, f, hfo, hf, hm⟩
    · exact hSz V Γ A L m hs ⟨hsimp, f, hfo, hf, hm⟩
    · exact hTits V Γ A L m hs ⟨hsimp, hm⟩
    · rcases hn with rfl | rfl
      · exact hL4 V Γ A L m hs ⟨hsimp, hm⟩
      · exact hL5 V Γ A L m hs ⟨hsimp, hm⟩
    · exact hSpor s hs' V Γ A L m hs ⟨hsimp, he⟩
  · rcases hlist with ⟨s, p, e, hp, he, hpe, hm⟩ | hm | hm | hm
    · exact hCSL3 V Γ A L m hs ⟨hz, s, p, e, hp, he, hpe, hm⟩
    · exact hA6 V Γ A L m hs ⟨hz, hm⟩
    · exact hA7 V Γ A L m hs ⟨hz, hm⟩
    · exact hM22 V Γ A L m hs ⟨hz, hm⟩

end CFSG.Quasithin.G11.Harris
