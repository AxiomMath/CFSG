module

public import CFSG.Quasithin.Background.E2Hyp
public import CFSG.Quasithin.Background.A1a
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.E2Two

public section

namespace CFSG.Quasithin.ASInputs

open CFSG.Open CFSG.QuasithinUnique

section Corrected

variable {G : Type} [Group G]

@[expose] def IsSp4C (k : ℕ) (X : Type) [Group X] : Prop :=
  IsPSp4 2 k X ∨ (k = 1 ∧ Nonempty (X ≃* Equiv.Perm (Fin 6)))

@[expose] def twoGen {Y : Type*} [Group Y] (P : Subgroup Y) : Subgroup Y :=
  Subgroup.closure {x : Y | x ∈ P ∧ ∃ k : ℕ, x ^ 2 ^ k = 1}

@[expose] def rootGroupOf {Y : Type*} [Group Y] (P : Subgroup Y) : Subgroup Y :=
  twoGen P ⊓ Subgroup.centralizer (twoGen P : Set Y)

@[expose] def IsInIHTVC (H T M V I : Subgroup G) : Prop :=
  I ≤ H ∧ (∃ g ∈ I, I = V ⊔ B6.conjSub g V) ∧ IsSylowTwoOf (T ⊓ I) I ∧
    IsSylowTwoOf (pCoreOf 2 (kerIn (M ⊓ I) I)) (kerIn (M ⊓ I) I) ∧
    ∃ k : ℕ, (∃ m : ℕ, E1.nParam H = ((k * m : ℕ) : ℕ∞)) ∧
      ((1 < k ∧ (IsPSL 2 2 k (E2.StarQuot (M ⊓ I) I) ∨ IsSz k (E2.StarQuot (M ⊓ I) I)) ∧
          E2.IsBorelIn ⊤ (E2.star (M ⊓ I) I (M ⊓ I))) ∨
        (k = 1 ∧ ∃ p a : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ a ∧
          Nonempty (E2.StarQuot (M ⊓ I) I ≃* DihedralGroup (p ^ a))) ∨
        ((∃ n : ℕ, E2.IsSp4Prime n ↥(oTwoUpper (⊤ : Subgroup (E2.StarQuot M H)))) ∧ 1 ≤ k ∧
          IsSp4C k (E2.StarQuot (M ⊓ I) I) ∧ E2.IsBorelIn ⊤ (E2.star (M ⊓ I) I (M ⊓ I)) ∧
          E2.star (M ⊓ I) I V ≤
            Subgroup.centralizer (E2.star (M ⊓ I) I (T ⊓ I) : Set (E2.StarQuot (M ⊓ I) I)) ∧
          ∀ P : Subgroup (E2.StarQuot (M ⊓ I) I), IsMaxParabolic2 ⊤ P →
            E2.star (M ⊓ I) I (M ⊓ I) ≤ P → ¬ E2.star (M ⊓ I) I V ≤ rootGroupOf P))

@[expose] def IsInIHTVNoRootAt (H T M V I : Subgroup G) (N : ℕ∞) : Prop :=
  I ≤ H ∧ (∃ g ∈ I, I = V ⊔ B6.conjSub g V) ∧ IsSylowTwoOf (T ⊓ I) I ∧
    IsSylowTwoOf (pCoreOf 2 (kerIn (M ⊓ I) I)) (kerIn (M ⊓ I) I) ∧
    ∃ k : ℕ, (∃ m : ℕ, N = ((k * m : ℕ) : ℕ∞)) ∧
      ((1 < k ∧ (IsPSL 2 2 k (E2.StarQuot (M ⊓ I) I) ∨ IsSz k (E2.StarQuot (M ⊓ I) I)) ∧
          E2.IsBorelIn ⊤ (E2.star (M ⊓ I) I (M ⊓ I))) ∨
        (k = 1 ∧ ∃ p a : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ a ∧
          Nonempty (E2.StarQuot (M ⊓ I) I ≃* DihedralGroup (p ^ a))) ∨
        ((∃ n : ℕ, E2.IsSp4Prime n ↥(oTwoUpper (⊤ : Subgroup (E2.StarQuot M H)))) ∧ 1 ≤ k ∧
          IsSp4C k (E2.StarQuot (M ⊓ I) I) ∧ E2.IsBorelIn ⊤ (E2.star (M ⊓ I) I (M ⊓ I)) ∧
          E2.star (M ⊓ I) I V ≤
            Subgroup.centralizer (E2.star (M ⊓ I) I (T ⊓ I) : Set (E2.StarQuot (M ⊓ I) I))))

@[expose] def IsInIHTVNoRoot (H T M V I : Subgroup G) : Prop :=
  IsInIHTVNoRootAt H T M V I (E1.nParam H)

theorem isInIHTVNoRoot_of_isInIHTVC {H T M V I : Subgroup G} (h : IsInIHTVC H T M V I) :
    IsInIHTVNoRoot H T M V I := by
  obtain ⟨h1, h2, h3, h4, k, hk, hc⟩ := h
  refine ⟨h1, h2, h3, h4, k, hk, ?_⟩
  rcases hc with hc | hc | ⟨a, b, c, d, e, -⟩
  · exact Or.inl hc
  · exact Or.inr (Or.inl hc)
  · exact Or.inr (Or.inr ⟨a, b, c, d, e⟩)

end Corrected

@[expose] def IsL33Exception {Y : Type} [Group Y] (H V : Subgroup Y) : Prop :=
  IsPSL 3 3 1 ↥(oTwoUpper H) ∧ ¬ V ≤ oTwoUpper H

@[expose] def IsDihL2Sz (X : Type) [Group X] : Prop :=
  (∃ m : ℕ, Odd m ∧ 1 < m ∧ Nonempty (X ≃* DihedralGroup m)) ∨ (∃ k : ℕ, IsPSL 2 2 k X) ∨
    ∃ k : ℕ, IsSz k X

theorem isDihL2Sz_of_eq {G : Type} [Group G] {A B I : Subgroup G} (h : A = B)
    (hA : IsDihL2Sz (E2.StarQuot A I)) : IsDihL2Sz (E2.StarQuot B I) :=
  h ▸ hA

@[expose] def AS_E_2_13_I : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V I : Subgroup G) (g : G) (h : E2.Hyp28 H T M V),
    CharTwo H → IsInIHTVC H T M V I → g ∈ I → I = V ⊔ B6.conjSub g V →
    ((∀ i ∈ I, B6.conjSub i V ≤ T → B6.conjSub i V ≤ Subgroup.centralizer (V : Set G)) →
      ∀ k : ℕ, ¬ IsSp4C k (E2.StarQuot (M ⊓ I) I)) ∧
    (IsDihL2Sz (E2.StarQuot (M ⊓ I) I) →
      (B6.conjSub g V ⊓ pCoreOf 2 I = B6.conjSub g V ⊓ Subgroup.normalizer (V : Set G) ∧
        ⁅⁅⁅V, B6.conjSub g V ⊓ pCoreOf 2 I⁆, B6.conjSub g V ⊓ pCoreOf 2 I⁆,
          B6.conjSub g V ⊓ pCoreOf 2 I⁆ = ⊥ ∧
        ¬ B6.conjSub g V ⊓ pCoreOf 2 I ≤ Subgroup.centralizer (V : Set G) ∧
        B6.conjSub g V ⊓ pCoreOf 2 I ⊓ Subgroup.centralizer (V : Set G) = V ⊓ B6.conjSub g V) ∧
      (V ⊓ B6.conjSub g V = ⊥ → qOf (autI h.elem H) ≤ ((1 : ℚ) : WithTop ℚ)) ∧
      (∀ x ∈ I, (∀ y ∈ (V ⊓ pCoreOf 2 I) ⊔ (B6.conjSub g V ⊓ pCoreOf 2 I),
          x * y * x⁻¹ * y⁻¹ ∈ V ⊓ B6.conjSub g V) → x ∈ pCoreOf 2 I) ∧
        pCoreOf 2 I = kerIn (M ⊓ I) I)

section E214

variable {G : Type} [Group G]

abbrev e214A (V I : Subgroup G) (g : G) : Subgroup G := B6.conjSub g V ⊓ pCoreOf 2 I

abbrev e214B (V I : Subgroup G) : Subgroup G := V ⊓ pCoreOf 2 I

abbrev e214P (V I : Subgroup G) (g : G) : Subgroup G := e214A V I g ⊔ e214B V I

abbrev e214ZT (T M I : Subgroup G) : Subgroup (E2.StarQuot (M ⊓ I) I) :=
  E2.star (M ⊓ I) I (T ⊓ I) ⊓
    Subgroup.centralizer (E2.star (M ⊓ I) I (T ⊓ I) : Set (E2.StarQuot (M ⊓ I) I))

end E214

@[expose] def AS_E_2_14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V I : Subgroup G) (g : G) (h : E2.Hyp28 H T M V),
    CharTwo H → IsTISetIn V M → IsInIHTVC H T M V I → g ∈ I → I = V ⊔ B6.conjSub g V →
    V ⊓ B6.conjSub g V ≠ ⊥ → IsDihL2Sz (E2.StarQuot (M ⊓ I) I) →
    M ⊓ I = I ⊓ Subgroup.normalizer (V : Set G) ∧
    ((e214P V I g = kerIn (M ⊓ I) I ∨ IsSz 3 (E2.StarQuot (M ⊓ I) I)) ∧
      E2.star (M ⊓ I) I V = e214ZT T M I) ∧
    (∀ k : ℕ, 1 < k → IsPSL 2 2 k (E2.StarQuot (M ⊓ I) I) →
      ∀ X : Subgroup G, X ≤ M ⊓ I → Nat.card X = 2 ^ k - 1 →
        ∀ x ∈ e214P V I g, (∀ y ∈ X, y * x * y⁻¹ * x⁻¹ ∈ V ⊓ B6.conjSub g V) →
          x ∈ V ⊓ B6.conjSub g V) ∧
    autI h.elem I ≤ Subgroup.normalizer (autI h.elem (e214A V I g) : Set _) ∧
    (∀ k : ℕ, (IsPSL 2 2 k (E2.StarQuot (M ⊓ I) I) ∨ IsSz k (E2.StarQuot (M ⊓ I) I)) →
      Nat.card (autI h.elem (e214A V I g)) ≤ 2 ^ (2 * k) →
      ((1 : ℚ) : WithTop ℚ) < qOf (autI h.elem I) →
      Nat.card (autI h.elem (e214A V I g)) = 2 ^ (2 * k) ∧
        (V ⊓ B6.conjSub g V).relIndex V = 2 ^ (3 * k)) ∧
    (IsPSL 2 2 2 (E2.StarQuot (M ⊓ I) I) →
      Nat.card (autI h.elem (e214A V I g)) ≤ 2 ^ 6 →
      ((1 : ℚ) : WithTop ℚ) < qOf (autI h.elem I) →
      ∃ s : ℕ, (s = 2 ∨ s = 3) ∧ Nat.card (autI h.elem (e214A V I g)) = 2 ^ (2 * s) ∧
        (V ⊓ B6.conjSub g V).relIndex V = 2 ^ (2 * (s + 1))) ∧
    ∀ k : ℕ, 1 < k → IsPSL 2 2 k (E2.StarQuot (M ⊓ I) I) →
      ∀ X : Subgroup G, X ≤ M ⊓ I → Nat.card X = 2 ^ k - 1 →
        V ⊓ Subgroup.centralizer (X : Set G) = V ⊓ B6.conjSub g V

end CFSG.Quasithin.ASInputs
