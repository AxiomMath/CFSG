module

public import CFSG.Quasithin.Background.B4Models
public import CFSG.Quasithin.Background.E3Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.E3

section H9

variable {W : Type} [CommGroup W]

@[expose] def stabV (U : Subgroup W) : Subgroup (MulAut W) where
  carrier := {g | ∀ u : W, u ∈ U ↔ g u ∈ U}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := fun {a b} ha hb u => (hb u).trans (ha (b u))
  inv_mem' := fun {a} ha u => by
    have h := ha (a⁻¹ u)
    rw [show a (a⁻¹ u) = u from MulAut.apply_inv_self _ _ _] at h
    exact h.symm

@[expose] def IsDualH9 (L : Subgroup (MulAut W)) (W₁ W₂ : Subgroup W) (β : W → W → ZMod 2) :
    Prop :=
  (∀ a ∈ W₁, ∀ b ∈ W₁, ∀ c ∈ W₂, β (a * b) c = β a c + β b c) ∧
    (∀ a ∈ W₁, ∀ c ∈ W₂, ∀ d ∈ W₂, β a (c * d) = β a c + β a d) ∧
    (∀ a ∈ W₁, a ≠ 1 → ∃ c ∈ W₂, β a c = 1) ∧ (∀ c ∈ W₂, c ≠ 1 → ∃ a ∈ W₁, β a c = 1) ∧
    ∀ l ∈ L, ∀ a ∈ W₁, ∀ c ∈ W₂, β (l a) (l c) = β a c

@[expose] def IsNonsingularH9 (W₁ W₂ : Subgroup W) (β : W → W → ZMod 2) (w : W) : Prop :=
  ∃ a ∈ W₁, ∃ c ∈ W₂, w = a * c ∧ β a c = 1

@[expose] def IsTransvOn (g : MulAut W) (W₁ : Subgroup W) : Prop :=
  g ∈ stabV W₁ ∧ (fixV (Subgroup.zpowers g) ⊓ W₁).relIndex W₁ = 2

@[expose] def conjAut (A : Subgroup (MulAut W)) (m : MulAut W) : Subgroup (MulAut W) :=
  A.map (MulAut.conj m).toMonoidHom

structure H9Hyp (n : ℕ) (M L T : Subgroup (MulAut W)) (W₁ W₂ : Subgroup W) : Prop where
  rank : n = 4 ∨ n = 5
  exp : ∀ w : W, w ^ 2 = 1
  aut : Nonempty (↥M ≃* MulAut (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)))
  le : L ≤ M
  index : L.relIndex M = 2
  sylow_le : T ≤ M
  sylow_two : IsPGroup 2 ↥T
  sylow_odd : ¬ 2 ∣ T.relIndex M
  inf : W₁ ⊓ W₂ = ⊥
  sup : W₁ ⊔ W₂ = ⊤
  inv₁ : L ≤ stabV W₁
  inv₂ : L ≤ stabV W₂
  card₁ : Nat.card W₁ = 2 ^ n
  full : ∀ φ : MulAut ↥W₁, ∃ l ∈ L, ∀ w : ↥W₁, l w = φ w
  faith : ∀ l ∈ L, (∀ w ∈ W₁, l w = w) → l = 1
  swap : ∃ t ∈ T, t ∉ L ∧ W₂ = W₁.map t.toMonoidHom

@[expose] noncomputable def orbitPoints (P : Subgroup (Equiv.Perm (Fin 8))) (k : ℕ) : ℕ :=
  Nat.card {x : Fin 8 // Nat.card (MulAction.orbit P x) = k}

end H9

@[expose] def LemH92 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M L T : Subgroup (MulAut W)) (W₁ W₂ : Subgroup W)
    (β : W → W → ZMod 2), H9Hyp 5 M L T W₁ W₂ → IsDualH9 L W₁ W₂ β →
    ((∀ t ∈ M, ∀ u ∈ M, t ∉ L → u ∉ L → orderOf t = 2 → orderOf u = 2 →
        ∃ m ∈ M, u = m * t * m⁻¹) ∧
      ∀ t ∈ M, t ∉ L → orderOf t = 2 →
        Nonempty (↥(L ⊓ Subgroup.centralizer ({t} : Set (MulAut W))) ≃* Equiv.Perm (Fin 6)) ∧
        fixV (Subgroup.zpowers t) = commV (Subgroup.zpowers t) ∧
        (∀ x ∈ fixV (Subgroup.zpowers t), ∃! w, w ∈ W₁ ∧ w * t w = x) ∧
        (∀ w ∈ W₁, w * t w ∈ fixV (Subgroup.zpowers t)) ∧
        ∃ v ∈ fixV (Subgroup.zpowers t), IsNonsingularH9 W₁ W₂ β v ∧
          v ∈ fixV (L ⊓ Subgroup.centralizer ({t} : Set (MulAut W))) ∧
          ∃ K : Subgroup W,
            K = Subgroup.closure {x | ∃ c ∈ L ⊓ Subgroup.centralizer ({t} : Set (MulAut W)),
              ∃ y ∈ fixV (Subgroup.zpowers t), x = c y * y⁻¹} ∧
            Subgroup.zpowers v ⊓ K = ⊥ ∧
            Subgroup.zpowers v ⊔ K = fixV (Subgroup.zpowers t) ∧
            BinaryNaturalSp4 (L ⊓ Subgroup.centralizer ({t} : Set (MulAut W))) K ⊥ 1) ∧
    (∀ A : Subgroup (MulAut W), A ≤ M → IsElemAbelian2 A → 2 ^ 5 ≤ Nat.card A → A ≤ L) ∧
    (∃ U : Subgroup W, U ≤ W₁ ∧ Nat.card U = 2 ^ 3 ∧ T ⊓ stabV W₁ ≤ stabV U ∧
      (∀ A : Subgroup (MulAut W), A ≤ M →
        (IsElemAbelian2 A ∧ Nat.card A = 2 ^ 6 ↔
          ∃ m ∈ M, A = conjAut (pCoreOf 2 (L ⊓ stabV U)) m)) ∧
      (∀ A : Subgroup (MulAut W), A ≤ M → IsElemAbelian2 A → Nat.card A = 2 ^ 5 →
        ∃ m ∈ M, conjAut A m ≤ pCoreOf 2 (L ⊓ stabV U)) ∧
      ∀ A : Subgroup (MulAut W), A ≤ pCoreOf 2 (L ⊓ stabV U) →
        2 * Nat.card A = Nat.card (pCoreOf 2 (L ⊓ stabV U)) →
          fixV A = commV A ∧ fixV A = fixV (pCoreOf 2 (L ⊓ stabV U)) ∧
          fixV A = commV (pCoreOf 2 (L ⊓ stabV U)) ∧
          (∀ x : W, x ∈ fixV A ↔ ∃ u ∈ U, ∃ c ∈ W₂, (∀ u' ∈ U, β u' c = 0) ∧ x = u * c) ∧
          Nat.card (fixV A) = 2 ^ 5) ∧
    ∀ A : Subgroup (MulAut W), A ≤ M → IsElemAbelian2 A → 2 ^ 5 ≤ Nat.card A →
      gammaCheck 3 A = ⊤

@[expose] def LemH93 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M L T : Subgroup (MulAut W)) (W₁ W₂ : Subgroup W),
    H9Hyp 4 M L T W₁ W₂ → ∃ ψ : ↥M ≃* Equiv.Perm (Fin 8),
    ((∀ t : ↥M, (t : MulAut W) ∉ L → orderOf t = 2 →
        ((ψ t).IsSwap ∧ Nonempty (↥(L ⊓ Subgroup.centralizer ({(t : MulAut W)} : Set (MulAut W)))
          ≃* Equiv.Perm (Fin 6))) ∨
        ((ψ t).cycleType = {2, 2, 2} ∧
          Nonempty (↥(L ⊓ Subgroup.centralizer ({(t : MulAut W)} : Set (MulAut W))) ≃*
            Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)))) ∧
      (∀ t u : ↥M, (t : MulAut W) ∉ L → (u : MulAut W) ∉ L → orderOf t = 2 → orderOf u = 2 →
        (ψ t).cycleType = (ψ u).cycleType → ∃ m : ↥M, u = m * t * m⁻¹) ∧
      (∃ t : ↥M, (t : MulAut W) ∉ L ∧ (ψ t).IsSwap) ∧
      ∃ u : ↥M, (u : MulAut W) ∉ L ∧ (ψ u).cycleType = {2, 2, 2}) ∧
    (∀ t ∈ M, t ∉ L → orderOf t = 2 →
      fixV (Subgroup.zpowers t) = commV (Subgroup.zpowers t) ∧
      (∀ x ∈ fixV (Subgroup.zpowers t), ∃! w, w ∈ W₁ ∧ w * t w = x) ∧
      ∀ w ∈ W₁, w * t w ∈ fixV (Subgroup.zpowers t)) ∧
    ∃ A₁ A₂ : Subgroup (MulAut W),
      (∀ A ∈ ({thompsonJ (T ⊓ stabV W₁), A₁, A₂} : Set (Subgroup (MulAut W))),
        A ≤ M ∧ IsElemAbelian2 A ∧ Nat.card A = 2 ^ 4) ∧
      ¬ A₁ ≤ L ∧ ¬ A₂ ≤ L ∧
      (∀ A : Subgroup (MulAut W), A ≤ M → IsElemAbelian2 A → Nat.card A = 2 ^ 4 →
        ∃ m ∈ M, A = conjAut (thompsonJ (T ⊓ stabV W₁)) m ∨ A = conjAut A₁ m ∨
          A = conjAut A₂ m) ∧
      orbitPoints (((thompsonJ (T ⊓ stabV W₁)).subgroupOf M).map ψ.toMonoidHom) 4 = 8 ∧
      orbitPoints ((A₁.subgroupOf M).map ψ.toMonoidHom) 2 = 8 ∧
      orbitPoints ((A₂.subgroupOf M).map ψ.toMonoidHom) 2 = 4 ∧
      orbitPoints ((A₂.subgroupOf M).map ψ.toMonoidHom) 4 = 4 ∧
      (Nat.card (fixV (thompsonJ (T ⊓ stabV W₁))) = 2 ^ 4 ∧
        gammaCheck 2 (thompsonJ (T ⊓ stabV W₁)) = ⊤) ∧
      (Nat.card (fixV A₁) = 2 ∧ ∃ r ∈ A₁, IsTransvOn r W₁ ∧
        (∀ r' ∈ A₁, IsTransvOn r' W₁ → r' = r) ∧ gammaCheck 2 A₁ = fixV (Subgroup.zpowers r) ∧
        Nat.card (fixV (Subgroup.zpowers r)) = 2 ^ 6) ∧
      (∀ a ∈ A₂, a ∉ L →
        (∀ x : W, x ∈ fixV A₂ ↔ ∃ w ∈ W₁ ⊓ fixV (A₂ ⊓ L), x = w * a w) ∧
        Nat.card (fixV A₂) = 2 ^ 2 ∧
        gammaCheck 2 A₂ = fixV (A₂ ⊓ L) ⊔ fixV (Subgroup.zpowers a) ∧
        Nat.card (gammaCheck 2 A₂) = 2 ^ 6) ∧
      (∀ A ∈ ({A₁, A₂} : Set (Subgroup (MulAut W))),
        (∃ b ∈ A ⊓ L, IsTransvOn b W₁) ∧ (∃ b ∈ A ⊓ L, b ≠ 1 ∧ ¬ IsTransvOn b W₁) ∧
          2 ^ 7 ≤ Nat.card (gammaCheck 3 A)) ∧
      ∀ a ∈ A₂, (∀ w ∈ gammaCheck 2 A₂, a w = w) → a = 1

@[expose] def LemH9Comm : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (n : ℕ) (M L T : Subgroup (MulAut W))
    (W₁ W₂ : Subgroup W), H9Hyp n M L T W₁ W₂ → ∀ X : Subgroup (MulAut W), X ≤ M →
      IsElemAbelian2 X → Nat.card (commV X) ≤ 2 ^ 2 → Nat.card X ≤ 2

@[expose] def LemH9Cent : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (n : ℕ) (M L T : Subgroup (MulAut W))
    (W₁ W₂ : Subgroup W), H9Hyp n M L T W₁ W₂ → ∀ X : Subgroup (MulAut W), X ≤ M →
      IsElemAbelian2 X → Nat.card W ≤ 2 ^ 2 * Nat.card (fixV X) → Nat.card X ≤ 2

@[expose] def LemH9Axes : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (n : ℕ) (M L T : Subgroup (MulAut W))
    (W₁ W₂ : Subgroup W), H9Hyp n M L T W₁ W₂ → ∀ B : Subgroup (MulAut W), B ≤ L →
      IsElemAbelian2 B → 2 ^ (n - 2) ≤ Nat.card B →
      (∀ b ∈ B, ∀ c ∈ B, b ≠ 1 → c ≠ 1 →
        fixV (Subgroup.zpowers b) ⊓ W₁ = fixV (Subgroup.zpowers c) ⊓ W₁ ∧
          fixV (Subgroup.zpowers b) ⊓ W₂ = fixV (Subgroup.zpowers c) ⊓ W₂) →
      n = 4 ∧ Nat.card B = 2 ^ 2 ∧
        ∀ b ∈ B, b ≠ 1 → Nat.card ↥(fixV (Subgroup.zpowers b) ⊓ W₁) = 2 ^ 2

@[expose] def LemH9FF5 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M L T : Subgroup (MulAut W)) (W₁ W₂ : Subgroup W),
    H9Hyp 5 M L T W₁ W₂ → ∀ A : Subgroup (MulAut W), A ≤ M → IsElemAbelian2 A → A ≠ ⊥ →
      Nat.card A ≤ 2 ^ 4 → Nat.card W ≤ Nat.card A * Nat.card (fixV A) →
      Nat.card (Subgroup.closure {x : W | ∃ a ∈ A, ∃ w ∈ W₁, x = a w * w⁻¹}) ≤ 2 ^ 2 ∧
        2 ^ 2 ≤ (fixV A ⊓ W₁).relIndex W₁

@[expose] def LemH9Rank4 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M L T : Subgroup (MulAut W)) (W₁ W₂ : Subgroup W),
    H9Hyp 4 M L T W₁ W₂ → ∀ A : Subgroup (MulAut W), A ≤ M → IsElemAbelian2 A →
      Nat.card A ≤ 2 ^ 4

@[expose] def LemH9FF4 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M L T : Subgroup (MulAut W)) (W₁ W₂ : Subgroup W),
    H9Hyp 4 M L T W₁ W₂ → ∀ A : Subgroup (MulAut W), A ≤ M → IsElemAbelian2 A → A ≠ ⊥ →
      Nat.card W ≤ Nat.card A * Nat.card (fixV A) → A ≤ L

@[expose] def LemH93Use : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M L T : Subgroup (MulAut W)) (W₁ W₂ : Subgroup W),
    H9Hyp 4 M L T W₁ W₂ → ∃ A₀ A₁ A₂ : Subgroup (MulAut W),
      (∀ A ∈ ({A₀, A₁, A₂} : Set (Subgroup (MulAut W))),
        A ≤ M ∧ IsElemAbelian2 A ∧ Nat.card A = 2 ^ 4) ∧
      (∀ A : Subgroup (MulAut W), A ≤ M → IsElemAbelian2 A → Nat.card A = 2 ^ 4 →
        ∃ m ∈ M, A = conjAut A₀ m ∨ A = conjAut A₁ m ∨ A = conjAut A₂ m) ∧
      (Nat.card (fixV A₀) = 2 ^ 4 ∧ gammaCheck 2 A₀ = ⊤) ∧
      (Nat.card (fixV A₁) = 2 ∧ Nat.card (gammaCheck 2 A₁) = 2 ^ 6) ∧
      (Nat.card (fixV A₂) = 2 ^ 2 ∧ Nat.card (gammaCheck 2 A₂) = 2 ^ 6 ∧
        ∀ a ∈ A₂, (∀ w ∈ gammaCheck 2 A₂, a w = w) → a = 1) ∧
      ∀ A ∈ ({A₁, A₂} : Set (Subgroup (MulAut W))),
        (∃ b ∈ A ⊓ L, IsTransvOn b W₁) ∧ (∃ b ∈ A ⊓ L, b ≠ 1 ∧ ¬ IsTransvOn b W₁) ∧
          2 ^ 7 ≤ Nat.card (gammaCheck 3 A)

@[expose] def LemH92Use : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M L T : Subgroup (MulAut W)) (W₁ W₂ : Subgroup W)
    (β : W → W → ZMod 2), H9Hyp 5 M L T W₁ W₂ → IsDualH9 L W₁ W₂ β →
    ∀ A : Subgroup (MulAut W), A ≤ M → IsElemAbelian2 A → 2 ^ 5 ≤ Nat.card A →
      A ≤ L ∧ gammaCheck 3 A = ⊤ ∧
        (Nat.card ↥(fixV A ⊓ W₁) ≤ 2 ^ 2 ∨ Nat.card ↥(fixV A ⊓ W₂) ≤ 2 ^ 2)

end CFSG.Quasithin.H13
