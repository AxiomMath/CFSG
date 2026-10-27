module

public import CFSG.Quasithin.Background.G9GolayModels
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.Background.G9StmtsModels

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

structure G93Hyp (Γ A L H : Subgroup (GLV V)) (m : ℕ) : Prop where
  quotient : IsQuotientOfSQTKTauCeti ↥Γ
  A_le : A ≤ Γ
  A_elem : IsElemAbelian 2 A
  A_card : Nat.card ↥A = 2 ^ m
  bound : Module.finrank (ZMod 2) V ≤ 2 * (m + 1)
  L_comp : IsComponentOf L Γ
  L_comm : ∃ a ∈ A, ∃ l ∈ L, a * l ≠ l * a
  H_le : H ≤ Γ
  H_normal : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H
  H_irr : IsIrr H ⊤
  H_eq : H = L ∨ ∃ L₂ : Subgroup (GLV V), IsComponentOf L₂ Γ ∧ L₂ ≠ L ∧ H = L ⊔ L₂ ∧
    QuasiEquivalent L L₂

structure G94Hyp (Γ A : Subgroup (GLV V)) (m : ℕ) : Prop where
  quotient : IsQuotientOfSQTKTauCeti ↥Γ
  A_le : A ≤ Γ
  A_elem : IsElemAbelian 2 A
  A_card : Nat.card ↥A = 2 ^ m
  A_ne : 1 ≤ m
  bound : Module.finrank (ZMod 2) V ≤ 2 * (m + 1)
  irreducible : IsIrr Γ ⊤
  faithful : ∀ a ∈ A, (∀ f ∈ (genFittingFitting ↥Γ).map Γ.subtype, a * f = f * a) → a = 1

structure G94PublishedHyp (Γ A : Subgroup (GLV V)) (m : ℕ) : Prop where
  quotient : IsQuotientOfSQTKTauCeti ↥Γ
  A_le : A ≤ Γ
  A_elem : IsElemAbelian 2 A
  A_card : Nat.card ↥A = 2 ^ m
  bound : Module.finrank (ZMod 2) V ≤ 2 * (m + 1)
  irreducible : IsIrr Γ ⊤
  faithful : ∀ a ∈ A, (∀ f ∈ (genFittingFitting ↥Γ).map Γ.subtype, a * f = f * a) → a = 1

theorem G94Hyp.toPublished {Γ A : Subgroup (GLV V)} {m : ℕ}
    (hyp : G94Hyp Γ A m) : G94PublishedHyp Γ A m :=
  ⟨hyp.quotient, hyp.A_le, hyp.A_elem, hyp.A_card, hyp.bound,
    hyp.irreducible, hyp.faithful⟩

theorem G94PublishedHyp.toNontrivial {Γ A : Subgroup (GLV V)} {m : ℕ}
    (hyp : G94PublishedHyp Γ A m) (nontrivial : 1 ≤ m) : G94Hyp Γ A m :=
  ⟨hyp.quotient, hyp.A_le, hyp.A_elem, hyp.A_card, nontrivial, hyp.bound,
    hyp.irreducible, hyp.faithful⟩

@[expose] def G93Case0 (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  (m = 4 ∧ Module.finrank (ZMod 2) V = 10 ∧
      IsPermCoreModule H CFSG.Blueprint.NativeSporadic.M12) ∧
    EndIsField H 1 ∧ SelfDual H ⊤

@[expose] def G93Case1DimensionOnly (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  ((Nonempty (↥H ≃* ↥CFSG.Blueprint.NativeSporadic.M22) ∧ Module.finrank (ZMod 2) V = 10 ∧
        4 ≤ m ∧ m ≤ 5) ∨
      (Nonempty (↥H ≃* ↥CFSG.Blueprint.NativeSporadic.M24) ∧ Module.finrank (ZMod 2) V = 11 ∧
        5 ≤ m ∧ m ≤ 6)) ∧
    EndIsField H 1 ∧ ¬ SelfDual H ⊤

@[expose] def G93Case1 (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  ((Nonempty (↥H ≃* ↥CFSG.Blueprint.NativeSporadic.M22) ∧ Module.finrank (ZMod 2) V = 10 ∧
        4 ≤ m ∧ m ≤ 5 ∧ IsMathieu22CodeOrCocode H) ∨
      (Nonempty (↥H ≃* ↥CFSG.Blueprint.NativeSporadic.M24) ∧ Module.finrank (ZMod 2) V = 11 ∧
        5 ≤ m ∧ m ≤ 6 ∧ IsMathieu24CodeOrCocode H)) ∧
    EndIsField H 1 ∧ ¬ SelfDual H ⊤

theorem G93Case1.toDimensionOnly {H : Subgroup (GLV V)} {m : ℕ}
    (hyp : G93Case1 H m) : G93Case1DimensionOnly H m := by
  rcases hyp with ⟨cases, endField, notSelfDual⟩
  rcases cases with ⟨group, dimension, lower, upper, realization⟩ |
    ⟨group, dimension, lower, upper, realization⟩
  · exact ⟨Or.inl ⟨group, dimension, lower, upper⟩, endField, notSelfDual⟩
  · exact ⟨Or.inr ⟨group, dimension, lower, upper⟩, endField, notSelfDual⟩

@[expose] def G93Case2 (Γ H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  (m = 5 ∧ Module.finrank (ZMod 2) V = 12 ∧
      (∃ N : Subgroup ↥Γ, N.Normal ∧ N.index = 2 ∧
        IsHat ↥N ↥CFSG.Blueprint.NativeSporadic.M22 ∧ H = N.map Γ.subtype) ∧
      Nat.card ↥Γ = 2661120) ∧
    EndIsField H 2 ∧ SelfDual H ⊤

@[expose] def G93Case3 (Γ H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  (1 ≤ m ∧ m ≤ 2 ∧ Module.finrank (ZMod 2) V = 4 ∧
      Nonempty (↥Γ ≃* ↥(alternatingGroup (Fin 7))) ∧ H = Γ) ∧
    EndIsField H 1 ∧ ¬ SelfDual H ⊤

@[expose] def G93Case4 (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  (2 ≤ m ∧ Module.finrank (ZMod 2) V = 6 ∧ m ≤ 3 ∧
      IsPermCoreModule H (alternatingGroup (Fin 7))) ∧
    EndIsField H 1 ∧ SelfDual H ⊤

@[expose] def G93Case5 (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  (2 ≤ m ∧ Module.finrank (ZMod 2) V = 6 ∧ m ≤ 3 ∧
      IsHat ↥H ↥(alternatingGroup (Fin 6))) ∧
    EndIsField H 2 ∧ ¬ SelfDual H ⊤

@[expose] def G93Case6 (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  ∃ n : ℕ, (2 ≤ n ∧ Module.finrank (ZMod 2) V = 2 * n ∧ n ≤ m + 1 ∧ m ≤ n ∧
      IsNaturalMatrixModule H (StatedSL 2 (GaloisField 2 n))) ∧
    EndIsField H n ∧ SelfDual H ⊤

@[expose] def G93Case7 (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  ∃ a : ℕ, (1 ≤ a ∧ Module.finrank (ZMod 2) V = 4 * a ∧ 2 * a ≤ m + 1 ∧ m ≤ 2 * a ∧
      Nonempty (↥H ≃* ↥(StatedSL 2 (GaloisField 2 (2 * a)))) ∧
      ∃ b c : GaloisField 2 a, (∀ s : GaloisField 2 a, s ^ 2 + b * s + c ≠ 0) ∧
        IsNaturalMatrixModule H (StatedOmega (StatedQuadMinus 2 (GaloisField 2 a) b c))) ∧
    EndIsField H a ∧ SelfDual H ⊤

@[expose] def G93Case8 (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  ∃ n : ℕ, (1 ≤ n ∧ Module.finrank (ZMod 2) V = 3 * n ∧ 3 * n ≤ 2 * m + 2 ∧ m ≤ 2 * n ∧
      IsNaturalMatrixModule H (StatedSL 3 (GaloisField 2 n)) ∧ (n = 1 → AutAll H ⊤)) ∧
    EndIsField H n ∧ ¬ SelfDual H ⊤

@[expose] def G93Case9 (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  ∃ n : ℕ, (1 ≤ n ∧ Module.finrank (ZMod 2) V = 4 * n ∧ 2 * n ≤ m + 1 ∧ m ≤ 3 * n ∧
      IsNaturalMatrixModule H ⁅StatedSp 2 (GaloisField 2 n), StatedSp 2 (GaloisField 2 n)⁆ ∧
      (n = 1 → IsPermCoreModule H (alternatingGroup (Fin 6)))) ∧
    EndIsField H n ∧ SelfDual H ⊤

@[expose] def G93Case10 (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  ∃ n : ℕ, (1 ≤ n ∧ Module.finrank (ZMod 2) V = 6 * n ∧ 3 * n ≤ m + 1 ∧ m ≤ 3 * n ∧
      IsG2NaturalModule H
        ⁅CFSG.Open.quasithinG2 (GaloisField 2 n), CFSG.Open.quasithinG2 (GaloisField 2 n)⁆) ∧
    EndIsField H n ∧ SelfDual H ⊤

@[expose] def G93Case11 (Γ H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  (1 ≤ m ∧ Module.finrank (ZMod 2) V = 4 ∧ m ≤ 4 ∧
      IsNaturalMatrixModule Γ (StatedSL 4 (ZMod 2)) ∧ H = Γ ∧ AutAll Γ ⊤) ∧
    EndIsField H 1 ∧ ¬ SelfDual H ⊤

@[expose] def G93Case12 (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  (2 ≤ m ∧ Module.finrank (ZMod 2) V = 6 ∧ m ≤ 4 ∧
      IsPermCoreModule H (alternatingGroup (Fin 8))) ∧
    EndIsField H 1 ∧ SelfDual H ⊤

@[expose] def G93Case13 (Γ H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  (Nonempty (↥Γ ≃* ↥(StatedSL 5 (ZMod 2))) ∧
      ((Module.finrank (ZMod 2) V = 5 ∧ 2 ≤ m ∧ AutAll Γ ⊤) ∨
        (Module.finrank (ZMod 2) V = 10 ∧ 4 ≤ m)) ∧ m ≤ 6 ∧ H = Γ) ∧
    EndIsField H 1 ∧ ¬ SelfDual H ⊤

@[expose] def G93Case14 (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  (m = 4 ∧ Module.finrank (ZMod 2) V = 9 ∧ IsL3L3TensorModule H) ∧
    EndIsField H 1 ∧ ¬ SelfDual H ⊤

@[expose] def G93Case15 (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  ∃ n : ℕ, (2 ≤ n ∧ Module.finrank (ZMod 2) V = 4 * n ∧ 2 * n ≤ m + 1 ∧ m ≤ 2 * n ∧
      IsNaturalMatrixModule H (StatedOmega (StatedQuadPlus 2 (GaloisField 2 n)))) ∧
    EndIsField H n ∧ SelfDual H ⊤

@[expose] def G93Case16 (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  (m = 3 ∧ Module.finrank (ZMod 2) V = 8 ∧ IsL28TwistedTensorModule H) ∧
    EndIsField H 1 ∧ SelfDual H ⊤

@[expose] def G93Case17 (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  ∃ n : ℕ, ((n = 1 ∨ n = 2) ∧ Module.finrank (ZMod 2) V = 9 * n ∧ m = 4 * n ∧
      (IsSL3 (2 ^ (2 * n)) ↥H ∨ IsPSL 3 2 (2 * n) ↥H) ∧ IsHermitianTensorModule H n) ∧
    EndIsField H n ∧ ¬ SelfDual H ⊤

@[expose] def G93Concl (Γ H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  G93Case0 H m ∨ G93Case1 H m ∨ G93Case2 Γ H m ∨ G93Case3 Γ H m ∨ G93Case4 H m ∨
    G93Case5 H m ∨ G93Case6 H m ∨ G93Case7 H m ∨ G93Case8 H m ∨ G93Case9 H m ∨
    G93Case10 H m ∨ G93Case11 Γ H m ∨ G93Case12 H m ∨ G93Case13 Γ H m ∨ G93Case14 H m ∨
    G93Case15 H m ∨ G93Case16 H m ∨ G93Case17 H m

@[expose] def G93Stmt : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (Γ A L H : Subgroup (GLV V)) (m : ℕ), G93Hyp Γ A L H m → G93Concl Γ H m

@[expose] def G94Concl (Γ A : Subgroup (GLV V)) (m : ℕ) : Prop :=
  (m = 1 ∧ G112Concl1 Γ) ∨
  (m = 1 ∧ Module.finrank (ZMod 2) V = 4 ∧
      Nonempty (↥(normalClosure Γ A) ≃* DihedralGroup 5) ∧ 10 ∣ Nat.card ↥Γ) ∨
  (m = 1 ∧ Module.finrank (ZMod 2) V = 4 ∧
      ((IsGammaL24 Γ ∧ 10 ∣ Nat.card ↥Γ) ∨
        (∃ q : V → ZMod 2, IsPlusQuadForm q ∧ pCoreOf 3 (orthogonalSubgroupOf q) ≤ Γ ∧
          Γ ≤ orthogonalSubgroupOf q ∧ 18 ∣ Nat.card ↥Γ))) ∨
  (m = 2 ∧ Module.finrank (ZMod 2) V = 4 ∧
      (∃ q : V → ZMod 2, IsPlusQuadForm q ∧ Γ ≤ orthogonalSubgroupOf q ∧
        Γ.relIndex (orthogonalSubgroupOf q) ≤ 2) ∧ 18 ∣ Nat.card ↥Γ) ∨
  (m = 2 ∧ G112Concl3 Γ)

@[expose] def G94Stmt : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (Γ A : Subgroup (GLV V)) (m : ℕ), G94Hyp Γ A m → G94Concl Γ A m

@[expose] def G94SmallConcl (Γ : Subgroup (GLV V)) (m : ℕ) : Prop :=
  m = 0 ∧ ((Module.finrank (ZMod 2) V = 1 ∧ Γ = ⊥) ∨
    (Module.finrank (ZMod 2) V = 2 ∧
      (Nonempty (↥Γ ≃* Multiplicative (ZMod 3)) ∨
        Nonempty (↥Γ ≃* Equiv.Perm (Fin 3)))))

@[expose] def G94PublishedStmt : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (Γ A : Subgroup (GLV V)) (m : ℕ), G94PublishedHyp Γ A m →
      G94SmallConcl Γ m ∨ G94Concl Γ A m

theorem G94PublishedStmt.toNontrivial (fullTarget : G94PublishedStmt) : G94Stmt := by
  intro V _ _ _ Γ A m hyp
  rcases fullTarget V Γ A m hyp.toPublished with small | large
  · have zeroRank := small.1
    have positiveRank := hyp.A_ne
    omega
  · exact large

@[expose] def G93SelfDualCases (Γ H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  G93Case0 H m ∨ G93Case2 Γ H m ∨ G93Case4 H m ∨ G93Case6 H m ∨ G93Case7 H m ∨ G93Case9 H m ∨
    G93Case10 H m ∨ G93Case12 H m ∨ G93Case15 H m ∨ G93Case16 H m

theorem G93Concl.of_selfDual {Γ H : Subgroup (GLV V)} {m : ℕ} (h : G93Concl Γ H m)
    (hs : SelfDual H ⊤) : G93SelfDualCases Γ H m := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exact absurd hs h.2.2
  · exact Or.inr (Or.inl h)
  · exact absurd hs h.2.2
  · exact Or.inr (Or.inr (Or.inl h))
  · exact absurd hs h.2.2
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · obtain ⟨_, _, _, hd⟩ := h
    exact absurd hs hd
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact absurd hs h.2.2
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  · exact absurd hs h.2.2
  · exact absurd hs h.2.2
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))
  · obtain ⟨_, _, _, hd⟩ := h
    exact absurd hs hd

theorem G93Concl.of_not_selfDual {Γ H : Subgroup (GLV V)} {m : ℕ} (h : G93Concl Γ H m)
    (hs : ¬ SelfDual H ⊤) :
    G93Case1 H m ∨ G93Case3 Γ H m ∨ G93Case5 H m ∨ G93Case8 H m ∨ G93Case11 Γ H m ∨
      G93Case13 Γ H m ∨ G93Case14 H m ∨ G93Case17 H m := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact absurd h.2.2 hs
  · exact Or.inl h
  · exact absurd h.2.2 hs
  · exact Or.inr (Or.inl h)
  · exact absurd h.2.2 hs
  · exact Or.inr (Or.inr (Or.inl h))
  · obtain ⟨_, _, _, hd⟩ := h
    exact absurd hd hs
  · obtain ⟨_, _, _, hd⟩ := h
    exact absurd hd hs
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · obtain ⟨_, _, _, hd⟩ := h
    exact absurd hd hs
  · obtain ⟨_, _, _, hd⟩ := h
    exact absurd hd hs
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact absurd h.2.2 hs
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · obtain ⟨_, _, _, hd⟩ := h
    exact absurd hd hs
  · exact absurd h.2.2 hs
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

theorem G93Concl.finrank_le {Γ H : Subgroup (GLV V)} {m : ℕ} (h : G93Concl Γ H m) :
    Module.finrank (ZMod 2) V ≤ 2 * (m + 1) := by
  rcases h with ⟨⟨hm, hd, -⟩, -⟩ | ⟨⟨-, hd, hm, -⟩ | ⟨-, hd, hm, -⟩, -⟩ | ⟨⟨hm, hd, -⟩, -⟩ |
    ⟨⟨hm, -, hd, -⟩, -⟩ | ⟨⟨hm, hd, -⟩, -⟩ | ⟨⟨hm, hd, -⟩, -⟩ | ⟨n, ⟨-, hd, hm, -⟩, -⟩ |
    ⟨n, ⟨-, hd, hm, -⟩, -⟩ | ⟨n, ⟨-, hd, hm, -⟩, -⟩ | ⟨n, ⟨-, hd, hm, -⟩, -⟩ |
    ⟨n, ⟨-, hd, hm, -⟩, -⟩ | ⟨⟨hm, hd, -⟩, -⟩ | ⟨⟨hm, hd, -⟩, -⟩ | ⟨⟨-, ⟨hd, hm, -⟩ | ⟨hd, hm⟩, -⟩, -⟩ |
    ⟨⟨hm, hd, -⟩, -⟩ | ⟨n, ⟨-, hd, hm, -⟩, -⟩ | ⟨⟨hm, hd, -⟩, -⟩ | ⟨n, ⟨hn, hd, hm, -⟩, -⟩ <;>
    omega

theorem G94Concl.toG112 {Γ A : Subgroup (GLV V)} {m : ℕ} (h : G94Concl Γ A m) :
    G112Concl1 Γ ∨ G112Concl2 Γ ∨ G112Concl3 Γ := by
  rcases h with ⟨-, h⟩ | ⟨-, hd, -, h10⟩ | ⟨-, hd, ⟨-, h10⟩ | ⟨q, -, -, -, h18⟩⟩ |
    ⟨-, hd, -, h18⟩ | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨hd, Or.inl h10⟩)
  · exact Or.inr (Or.inl ⟨hd, Or.inl h10⟩)
  · exact Or.inr (Or.inl ⟨hd, Or.inr h18⟩)
  · exact Or.inr (Or.inl ⟨hd, Or.inr h18⟩)
  · exact Or.inr (Or.inr h)

end G11

end CFSG.Quasithin
