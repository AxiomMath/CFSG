module

public import CFSG.Quasithin.Background.G11BridgeRestrict
public import CFSG.Milestones.ASVolI.G4
public import CFSG.Quasithin.Background.Harris.Holds
import CFSG.Quasithin.Background.G9A8OrthModule
import CFSG.Quasithin.Background.SzG11G94Final
import CFSG.Quasithin.Background.G92Main

public section

namespace CFSG.ASVolI.ChG

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Open CFSG.Assembly.LowTwoRank

@[expose] def piPrimeCore {A : Type*} [Group A] (π : Set ℕ) (H : Subgroup A) : Subgroup A :=
  sSup {N | N ≤ H ∧ (N.subgroupOf H).Normal ∧ ∀ q ∈ π, q.Prime → Nat.Coprime q (Nat.card N)}

section

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

structure HypG91 (G A : Subgroup (GLV V)) (m : ℕ) : Prop where
  A_le : A ≤ G
  A_elem : IsElemAbelian 2 A
  A_card : Nat.card ↥A = 2 ^ m
  bound : Module.finrank (ZMod 2) V ≤ 2 * (m + 1)

@[expose] def IsOrth4Module (G' : Subgroup (GLV V)) (U : Submodule (ZMod 2) V) : Prop :=
  ∃ (φ : ↥G' ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) × Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
    (ψ : ↥U ≃ₗ[ZMod 2] Matrix (Fin 2) (Fin 2) (ZMod 2)),
    ∀ (g : ↥G') (u u' : ↥U), (u' : V) = (g : GLV V) (u : V) →
      ψ u' = ((φ g).1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) * ψ u *
        ((φ g).2 : Matrix (Fin 2) (Fin 2) (ZMod 2)).transpose

end


section Cases

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def G93p0 (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  m = 4 ∧ Module.finrank (ZMod 2) V = 10 ∧ IsPermCoreModule H CFSG.Blueprint.NativeSporadic.M12

@[expose] def G93p1 (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  (Nonempty (↥H ≃* ↥CFSG.Blueprint.NativeSporadic.M22) ∧
    Module.finrank (ZMod 2) V = 10 ∧ 4 ≤ m ∧ IsMathieu22CodeOrCocode H) ∨
    (Nonempty (↥H ≃* ↥CFSG.Blueprint.NativeSporadic.M24) ∧
      Module.finrank (ZMod 2) V = 11 ∧ 5 ≤ m ∧ IsMathieu24CodeOrCocode H)

theorem g93p1_of_case1 {H : Subgroup (GLV V)} {m : ℕ}
    (hyp : G93Case1 H m) : G93p1 H m := by
  rcases hyp.1 with ⟨group, dimension, lower, upper, realization⟩ |
    ⟨group, dimension, lower, upper, realization⟩
  · exact Or.inl ⟨group, dimension, lower, realization⟩
  · exact Or.inr ⟨group, dimension, lower, realization⟩

@[expose] def G93p2 (Γ : Subgroup (GLV V)) (m : ℕ) : Prop :=
  m = 5 ∧ Module.finrank (ZMod 2) V = 12 ∧
    ∃ N : Subgroup ↥Γ, N.Normal ∧ N.index = 2 ∧ IsHat ↥N ↥CFSG.Blueprint.NativeSporadic.M22

@[expose] def G93p3 (Γ : Subgroup (GLV V)) (m : ℕ) : Prop :=
  1 ≤ m ∧ m ≤ 2 ∧ Module.finrank (ZMod 2) V = 4 ∧ Nonempty (↥Γ ≃* ↥(alternatingGroup (Fin 7)))

@[expose] def G93p4 (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  2 ≤ m ∧ Module.finrank (ZMod 2) V = 6 ∧ Nonempty (↥H ≃* ↥(alternatingGroup (Fin 7)))

@[expose] def G93p5 (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  2 ≤ m ∧ Module.finrank (ZMod 2) V = 6 ∧ IsHat ↥H ↥(alternatingGroup (Fin 6))

@[expose] def G93p6 (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  ∃ n : ℕ, Module.finrank (ZMod 2) V = 2 * n ∧ n ≤ m + 1 ∧
    IsNaturalMatrixModule H (StatedSL 2 (GaloisField 2 n))

@[expose] def G93p7 (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  ∃ a : ℕ, Module.finrank (ZMod 2) V = 4 * a ∧ 2 * a ≤ m + 1 ∧
    Nonempty (↥H ≃* ↥(StatedSL 2 (GaloisField 2 (2 * a)))) ∧
    ∃ b c : GaloisField 2 a, (∀ s : GaloisField 2 a, s ^ 2 + b * s + c ≠ 0) ∧
      IsNaturalMatrixModule H (StatedOmega (StatedQuadMinus 2 (GaloisField 2 a) b c))

@[expose] def G93p8 (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  ∃ n : ℕ, Module.finrank (ZMod 2) V = 3 * n ∧ 3 * n ≤ 2 * m + 2 ∧
    IsNaturalMatrixModule H (StatedSL 3 (GaloisField 2 n))

@[expose] def G93p9 (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  ∃ n : ℕ, Module.finrank (ZMod 2) V = 4 * n ∧ 2 * n ≤ m + 1 ∧
    IsNaturalMatrixModule H ⁅StatedSp 2 (GaloisField 2 n), StatedSp 2 (GaloisField 2 n)⁆

@[expose] def G93p10 (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  ∃ n : ℕ, Module.finrank (ZMod 2) V = 6 * n ∧ 3 * n ≤ m + 1 ∧
    IsG2NaturalModule H
      ⁅CFSG.Open.quasithinG2 (GaloisField 2 n), CFSG.Open.quasithinG2 (GaloisField 2 n)⁆

@[expose] def G93p11 (Γ : Subgroup (GLV V)) (m : ℕ) : Prop :=
  1 ≤ m ∧ Module.finrank (ZMod 2) V = 4 ∧ IsNaturalMatrixModule Γ (StatedSL 4 (ZMod 2))

@[expose] def G93p12 (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  2 ≤ m ∧ Module.finrank (ZMod 2) V = 6 ∧
    IsNaturalMatrixModule H (StatedOmega (StatedQuadPlus 3 (ZMod 2))) ∧
    Nonempty (↥H ≃* ↥(alternatingGroup (Fin 8)))

@[expose] def G93p13 (Γ : Subgroup (GLV V)) (m : ℕ) : Prop :=
  Nonempty (↥Γ ≃* ↥(StatedSL 5 (ZMod 2))) ∧
    ((Module.finrank (ZMod 2) V = 5 ∧ 2 ≤ m) ∨ (Module.finrank (ZMod 2) V = 10 ∧ 4 ≤ m))

@[expose] def G93p14 (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  m = 4 ∧ Module.finrank (ZMod 2) V = 9 ∧ IsL3L3TensorModule H

@[expose] def G93p15 (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  ∃ n : ℕ, 1 < n ∧ Module.finrank (ZMod 2) V = 4 * n ∧ 2 * n ≤ m + 1 ∧
    IsNaturalMatrixModule H (StatedOmega (StatedQuadPlus 2 (GaloisField 2 n)))

@[expose] def G93p16 (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  m = 3 ∧ Module.finrank (ZMod 2) V = 8 ∧ IsL28TwistedTensorModule H

@[expose] def G93p17 (H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  ∃ n : ℕ, (n = 1 ∨ n = 2) ∧ Module.finrank (ZMod 2) V = 9 * n ∧ m = 4 * n ∧
    (IsSL3 (2 ^ (2 * n)) ↥H ∨ IsPSL 3 2 (2 * n) ↥H) ∧ IsHermitianTensorModule H n

@[expose] def IsSubSD16Heis (Γ : Subgroup (GLV V)) : Prop :=
  CFSG.Quasithin.IsSubSD16Heis Γ

end Cases

end CFSG.ASVolI.ChG

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.ASVolI.ChG CFSG.Assembly.LowTwoRank
open scoped commutatorElement

@[expose] def G_9_2 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (G A : Subgroup (GLV V)) (m : ℕ),
    HypG91 G A m →
    ∀ X : Subgroup (GLV V), X ≤ G → Group.IsNilpotent ↥X → Odd (Nat.card ↥X) →
      A ≤ Subgroup.normalizer (X : Set (GLV V)) → A ⊓ Subgroup.centralizer (X : Set (GLV V)) = ⊥ →
      (⁅piPrimeCore {3} X, A⁆ = ⊥ → Module.finrank (ZMod 2) V ≤ 2 * m) →
        ⁅piPrimeCore {3, 5} X, A⁆ = ⊥ ∧
        ∃ (r : ℕ) (Gs : Fin r → Subgroup (GLV V)),
          (⨆ i, Gs i) ≤ X ⊔ A ∧ A ≤ ⨆ i, Gs i ∧ iSupIndep Gs ∧
          (∀ i j, i ≠ j → ∀ x ∈ Gs i, ∀ y ∈ Gs j, x * y = y * x) ∧
          (iSupIndep (fun i => commSpace (Gs i) ⊤) ∧ (⨆ i, commSpace (Gs i) ⊤) = ⊤) ∧
          (⁅piPrimeCore {3} X, A⁆ ≠ ⊥ → ∃ h : 0 < r,
            Nonempty (↥(Gs ⟨0, h⟩) ≃* DihedralGroup 5) ∧
              Module.finrank (ZMod 2) ↥(commSpace (Gs ⟨0, h⟩) ⊤) = 4) ∧
          (∀ i : Fin r, (⁅piPrimeCore {3} X, A⁆ ≠ ⊥ → 1 ≤ i.val) →
            ((Nonempty (↥(Gs i) ≃* DihedralGroup 3) ∧
                Module.finrank (ZMod 2) ↥(commSpace (Gs i) ⊤) = 2) ∨
              IsOrth4Module (Gs i) (commSpace (Gs i) ⊤))) ∧
          (⁅piPrimeCore {3} X, A⁆ = ⊥ → Module.finrank (ZMod 2) V = 2 * m) ∧
          (⁅piPrimeCore {3} X, A⁆ ≠ ⊥ → Module.finrank (ZMod 2) V = 2 * (m + 1))

theorem as_G_9_2 : G_9_2 := by
  intro V _ _ _ G A m hyp X hXG hXn hXo hAN hAf hd
  exact CFSG.Quasithin.G92.g92_main A m hyp.A_elem hyp.A_card hyp.bound X hXn hXo hAN hAf hd

@[expose] def G_9_3 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (Γ A L H : Subgroup (GLV V)) (m : ℕ), G93Hyp Γ A L H m →
      G93p0 H m ∨ G93p1 H m ∨ G93p2 Γ m ∨ G93p3 Γ m ∨ G93p4 H m ∨ G93p5 H m ∨ G93p6 H m ∨
      G93p7 H m ∨ G93p8 H m ∨ G93p9 H m ∨ G93p10 H m ∨ G93p11 Γ m ∨ G93p12 H m ∨ G93p13 Γ m ∨
      G93p14 H m ∨ G93p15 H m ∨ G93p16 H m ∨ G93p17 H m

private theorem g93Published_of_stmt (h : G93Stmt) : G_9_3 := by
  intro V _ _ _ Γ A L H m hyp
  rcases h V Γ A L H m hyp with
    ⟨h0, -, -⟩ | h1 | ⟨⟨hm, hd, ⟨N, hN, hi, hhat, -⟩, -⟩, -, -⟩ |
    ⟨⟨h1, h2, h3, h4, -⟩, -, -⟩ | ⟨⟨h1, h2, -, φ, -⟩, -, -⟩ | ⟨⟨h1, h2, -, hhat⟩, -, -⟩ |
    ⟨n, ⟨-, hd, hn, -, hnat⟩, -, -⟩ | ⟨a, ⟨-, hd, hm, -, hiso, b, c, hbc, hnat⟩, -, -⟩ |
    ⟨n, ⟨-, hd, hm, -, hnat, -⟩, -, -⟩ | ⟨n, ⟨-, hd, hm, -, hnat, -⟩, -, -⟩ |
    ⟨n, ⟨-, hd, hm, -, hG2⟩, -, -⟩ | ⟨⟨h1, h2, -, hnat, -, -⟩, -, -⟩ |
    ⟨⟨h1, h2, -, hperm⟩, -, -⟩ | ⟨⟨hΓ, ⟨hd, hm, -⟩ | ⟨hd, hm⟩, -, -⟩, -, -⟩ |
    ⟨⟨h1, h2, h3⟩, -, -⟩ | ⟨n, ⟨hn, hd, hm, -, hnat⟩, -, -⟩ | ⟨⟨h1, h2, h3⟩, -, -⟩ |
    ⟨n, ⟨hn, hd, hm, hsl, hher⟩, -, -⟩
  · exact Or.inl h0
  · exact Or.inr (Or.inl (g93p1_of_case1 h1))
  · iterate 2 right
    exact Or.inl ⟨hm, hd, N, hN, hi, hhat⟩
  · iterate 3 right
    exact Or.inl ⟨h1, h2, h3, h4⟩
  · iterate 4 right
    exact Or.inl ⟨h1, h2, ⟨φ⟩⟩
  · iterate 5 right
    exact Or.inl ⟨h1, h2, hhat⟩
  · iterate 6 right
    exact Or.inl ⟨n, hd, hn, hnat⟩
  · iterate 7 right
    exact Or.inl ⟨a, hd, hm, hiso, b, c, hbc, hnat⟩
  · iterate 8 right
    exact Or.inl ⟨n, hd, hm, hnat⟩
  · iterate 9 right
    exact Or.inl ⟨n, hd, hm, hnat⟩
  · iterate 10 right
    exact Or.inl ⟨n, hd, hm, hG2⟩
  · iterate 11 right
    exact Or.inl ⟨h1, h2, hnat⟩
  · have hnat := isNaturalMatrixModule_omega6_of_isPermCoreModule_alt8 hperm
    obtain ⟨φ, -⟩ := hperm
    iterate 12 right
    exact Or.inl ⟨h1, h2, hnat, ⟨φ⟩⟩
  · iterate 13 right
    exact Or.inl ⟨hΓ, Or.inl ⟨hd, hm⟩⟩
  · iterate 13 right
    exact Or.inl ⟨hΓ, Or.inr ⟨hd, hm⟩⟩
  · iterate 14 right
    exact Or.inl ⟨h1, h2, h3⟩
  · iterate 15 right
    exact Or.inl ⟨n, by omega, hd, hm, hnat⟩
  · iterate 16 right
    exact Or.inl ⟨h1, h2, h3⟩
  · iterate 17 right
    exact ⟨n, hn, hd, hm, hsl, hher⟩

section as_G_9_3

theorem as_G_9_3
    : G_9_3 :=
  g93Published_of_stmt CFSG.Quasithin.G11.Harris.g93Stmt_holds

end as_G_9_3

@[expose] def G_9_4 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (Γ A : Subgroup (GLV V)) (m : ℕ), G94PublishedHyp Γ A m →
      G94SmallConcl Γ m ∨
      (m = 1 ∧ Module.finrank (ZMod 2) V = 2 ∧ Nonempty (↥Γ ≃* Equiv.Perm (Fin 3))) ∨
      (m = 1 ∧ Module.finrank (ZMod 2) V = 4 ∧
        Nonempty (↥(normalClosure Γ A) ≃* DihedralGroup 5)) ∨
      (m = 1 ∧ Module.finrank (ZMod 2) V = 4 ∧
        (IsGammaL24 Γ ∨ ∃ q : V → ZMod 2, IsPlusQuadForm q ∧
          pCoreOf 3 (orthogonalSubgroupOf q) ≤ Γ ∧ Γ ≤ orthogonalSubgroupOf q)) ∨
      (m = 2 ∧ Module.finrank (ZMod 2) V = 4 ∧
        ∃ q : V → ZMod 2, IsPlusQuadForm q ∧ Γ ≤ orthogonalSubgroupOf q ∧
          Γ.relIndex (orthogonalSubgroupOf q) ≤ 2) ∨
      (m = 2 ∧ Module.finrank (ZMod 2) V = 6 ∧ ChG.IsSubSD16Heis Γ)

section SmallZero

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

private theorem g9_eq_bot_of_finrank_one [Finite V] {Γ : Subgroup (GLV V)}
    (hd : Module.finrank (ZMod 2) V = 1) : Γ = ⊥ := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hall := (finrank_eq_one_iff_of_nonzero' v hv).mp hd
  have hfix : ∀ g : GLV V, g v = v := by
    intro g
    have hgv : g v ≠ 0 := by simpa using hv
    obtain ⟨c, hc⟩ := hall (g v)
    have hc1 : c = 1 := by
      rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with h | h
      · exact absurd (by rw [← hc, h, zero_smul]) hgv
      · exact h
    rw [← hc, hc1, one_smul]
  refine (Subgroup.eq_bot_iff_forall Γ).mpr fun g _ => ?_
  ext w
  obtain ⟨c, rfl⟩ := hall w
  simp [map_smul, hfix g]

private def g9Perm (g : GLV V) : Equiv.Perm {v : V // v ≠ 0} :=
  Equiv.subtypeEquiv g.toEquiv fun v => by simp

private def g9PermHom : GLV V →* Equiv.Perm {v : V // v ≠ 0} where
  toFun := g9Perm
  map_one' := by
    ext v
    rfl
  map_mul' g h := by
    ext v
    rfl

private theorem g9PermHom_injective : Function.Injective (g9PermHom (V := V)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  ext v
  by_cases hv : v = 0
  · simp [hv]
  · have := congrArg
      (fun σ : Equiv.Perm {v : V // v ≠ 0} => ((σ ⟨v, hv⟩ : {v : V // v ≠ 0}) : V)) hg
    simpa [g9PermHom, g9Perm] using this

private theorem g9_card_nonzero [Finite V] (h : Nat.card V = 4) :
    Nat.card {v : V // v ≠ 0} = 3 := by
  have h1 : Nat.card {v : V // v ≠ 0} = (({0} : Set V)ᶜ).ncard := by
    rw [← Nat.card_coe_set_eq]
    rfl
  rw [h1, Set.ncard_compl, Set.ncard_singleton, h]

private theorem g9_false_of_fixed {Γ : Subgroup (GLV V)}
    (hirr : CFSG.Quasithin.G11.IsIrr Γ ⊤) (hd : Module.finrank (ZMod 2) V = 2)
    {v : V} (hv0 : v ≠ 0) (hfix : ∀ g ∈ Γ, g v = v) : False := by
  have hinv : CFSG.Quasithin.G11.Invariant Γ (Submodule.span (ZMod 2) {v}) := by
    intro k hk u hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hu
    rw [map_smul, hfix k hk]
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self v)
  rcases hirr.2.2 _ hinv bot_le le_top with h | h
  · have hv' : v ∈ (⊥ : Submodule (ZMod 2) V) := h ▸ Submodule.mem_span_singleton_self v
    exact hv0 (by simpa using hv')
  · have h1 := finrank_span_singleton (K := ZMod 2) hv0
    rw [h, finrank_top] at h1
    omega

private theorem g9_false_of_two_group [Finite V] {Γ : Subgroup (GLV V)}
    (hirr : CFSG.Quasithin.G11.IsIrr Γ ⊤) (hd : Module.finrank (ZMod 2) V = 2)
    (hP : IsPGroup 2 ↥Γ) : False := by
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  obtain ⟨v, hv0, hfix⟩ := CFSG.Quasithin.G11.exists_ne_zero_fixed_of_isPGroup Γ hP
  exact g9_false_of_fixed hirr hd hv0 hfix

private theorem g9_small_two [Finite V] {Γ : Subgroup (GLV V)}
    (hirr : CFSG.Quasithin.G11.IsIrr Γ ⊤) (hd : Module.finrank (ZMod 2) V = 2) :
    Nonempty (↥Γ ≃* Multiplicative (ZMod 3)) ∨ Nonempty (↥Γ ≃* Equiv.Perm (Fin 3)) := by
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hV : Nat.card V = 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hd]
    norm_num
  have hS : Nat.card {v : V // v ≠ 0} = 3 := g9_card_nonzero hV
  set φ : ↥Γ →* Equiv.Perm {v : V // v ≠ 0} := (g9PermHom (V := V)).comp Γ.subtype with hφdef
  have hφ : Function.Injective φ := g9PermHom_injective.comp Γ.subtype_injective
  have hperm : Nat.card (Equiv.Perm {v : V // v ≠ 0}) = 6 := by
    rw [Nat.card_perm, hS]
    rfl
  have hdvd : Nat.card ↥Γ ∣ 6 := hperm ▸ Subgroup.card_dvd_of_injective φ hφ
  have hle : Nat.card ↥Γ ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < Nat.card ↥Γ := by
    apply Nat.pos_of_ne_zero
    intro h0
    rw [h0, zero_dvd_iff] at hdvd
    norm_num at hdvd
  obtain ⟨n, hn⟩ : ∃ n, Nat.card ↥Γ = n := ⟨_, rfl⟩
  rw [hn] at hdvd hle hpos
  interval_cases n
  · exact (g9_false_of_two_group hirr hd (IsPGroup.of_card (n := 0) (by simp [hn]))).elim
  · exact (g9_false_of_two_group hirr hd (IsPGroup.of_card (n := 1) (by simp [hn]))).elim
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hm : Nat.card (Multiplicative (ZMod 3)) = 3 := by
      simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    haveI : IsCyclic (Multiplicative (ZMod 3)) := isCyclic_of_prime_card hm
    haveI : IsCyclic ↥Γ := isCyclic_of_prime_card hn
    exact Or.inl ⟨mulEquivOfCyclicCardEq (hn.trans hm.symm)⟩
  · omega
  · omega
  · have hbij : Function.Bijective φ := hφ.bijective_of_nat_card_le (by rw [hn, hperm])
    exact Or.inr ⟨(MulEquiv.ofBijective φ hbij).trans (Finite.equivFinOfCardEq hS).permCongrHom⟩

private theorem g9_small_zero [Finite V] {Γ A : Subgroup (GLV V)}
    (hyp : G94PublishedHyp Γ A 0) : G94SmallConcl Γ 0 := by
  have hirr : CFSG.Quasithin.G11.IsIrr Γ ⊤ := hyp.irreducible
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hnt : Nontrivial V := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hirr.2.1.ne' (Subsingleton.elim _ _)
  have hpos : 0 < Module.finrank (ZMod 2) V := Module.finrank_pos
  have hle : Module.finrank (ZMod 2) V ≤ 2 := by
    have := hyp.bound
    omega
  unfold G94SmallConcl
  refine ⟨rfl, ?_⟩
  rcases (by omega : Module.finrank (ZMod 2) V = 1 ∨ Module.finrank (ZMod 2) V = 2) with h | h
  · exact Or.inl ⟨h, g9_eq_bot_of_finrank_one h⟩
  · exact Or.inr ⟨h, g9_small_two hirr h⟩

private theorem g94Published_of_stmt (h : G94Stmt) : G_9_4 := by
  intro V _ _ _ Γ A m hyp
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    exact Or.inl (g9_small_zero hyp)
  · right
    rcases h V Γ A m (hyp.toNontrivial hm) with ⟨h1, hc⟩ | ⟨h1, hd, hN, -⟩ |
        ⟨h1, hd, hc3⟩ | ⟨h2, hd, ⟨q, hq, hle, hrel⟩, -⟩ | ⟨h2, hc⟩
    · exact Or.inl ⟨h1, hc.1, hc.2⟩
    · exact Or.inr (Or.inl ⟨h1, hd, hN⟩)
    · rcases hc3 with ⟨hg, -⟩ | ⟨q, hq, hpc, hle, -⟩
      · exact Or.inr (Or.inr (Or.inl ⟨h1, hd, Or.inl hg⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨h1, hd, Or.inr ⟨q, hq, hpc, hle⟩⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, hd, q, hq, hle, hrel⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h2, hc.1, hc.2⟩)))

end SmallZero

theorem as_G_9_4 : G_9_4 := g94Published_of_stmt CFSG.Quasithin.SzG11.g94Stmt_proved

end CFSG.ASVolI
