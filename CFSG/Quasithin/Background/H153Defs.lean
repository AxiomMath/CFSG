module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Quasithin.AppendixH.H14.Vocab
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

open scoped Pointwise

namespace CFSG.Quasithin.H153

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Open

@[expose] def natHomI' (ι : Type) [Fintype ι] [DecidableEq ι] (K : Type*) [Field K] :
    GL ι K →* MulAut (Multiplicative (ι → K)) where
  toFun g :=
    { toFun := fun v => Multiplicative.ofAdd ((g : Matrix ι ι K).mulVec (Multiplicative.toAdd v))
      invFun := fun v => Multiplicative.ofAdd
        (((g⁻¹ : GL ι K) : Matrix ι ι K).mulVec (Multiplicative.toAdd v))
      left_inv := fun v => by
        apply Multiplicative.toAdd.injective
        simp [Matrix.mulVec_mulVec]
      right_inv := fun v => by
        apply Multiplicative.toAdd.injective
        simp [Matrix.mulVec_mulVec]
      map_mul' := fun v w => by
        apply Multiplicative.toAdd.injective
        simp [Matrix.mulVec_add] }
  map_one' := by
    ext v
    simp
  map_mul' g h := by
    ext v
    simp [Matrix.mulVec_mulVec]

@[expose] def natSubI' (ι : Type) [Fintype ι] [DecidableEq ι] (K : Type*) [Field K]
    (S : Subgroup (GL ι K)) : Subgroup (MulAut (Multiplicative (ι → K))) :=
  S.map (natHomI' ι K)

@[expose] def IsVecOf' {V : Type*} [CommGroup V] (D : FFModel)
    (β : ↥(⊤ : Subgroup V) →* ↥D.sec ⧸ D.ker.subgroupOf D.sec) (e : D.Amb) (v : V) : Prop :=
  ∃ he : e ∈ D.sec, β ⟨v, Subgroup.mem_top v⟩ = QuotientGroup.mk ⟨e, he⟩

@[expose] def IsO23' (G N : Subgroup S24) : Prop :=
  N ≤ G ∧ (∀ g ∈ G, ∀ n ∈ N, g * n * g⁻¹ ∈ N) ∧ pCoreOf 2 G ≤ N ∧
    (∀ n ∈ N, ∃ k : ℕ, n ^ (3 ^ k) ∈ pCoreOf 2 G) ∧
    ∀ N' : Subgroup S24, N' ≤ G → (∀ g ∈ G, ∀ n ∈ N', g * n * g⁻¹ ∈ N') → pCoreOf 2 G ≤ N' →
      (∀ n ∈ N', ∃ k : ℕ, n ^ (3 ^ k) ∈ pCoreOf 2 G) → N' ≤ N

@[expose] def FullTranspCenter' {V : Type*} [CommGroup V] (G X : Subgroup (MulAut V))
    (A V₁ : Subgroup V) : Prop :=
  (∀ g ∈ X, ∀ x ∈ A, g x * x⁻¹ ∈ V₁) ∧
  (∀ τ : MulAut ↥A, (∀ x : ↥A, ((τ x : ↥A) : V) * ((x : ↥A) : V)⁻¹ ∈ V₁) →
    ∃ g ∈ X, ∀ x : ↥A, g (x : V) = ((τ x : ↥A) : V)) ∧
  (∀ g ∈ X, (∀ x ∈ A, g x = x) → g = 1) ∧
  (∀ h ∈ G, ∀ g ∈ X, h * g * h⁻¹ ∈ X)

@[expose] def IsDualOfConj' {V : Type*} [CommGroup V] {Γ : Subgroup S24} (ρ : ↥Γ →* MulAut V)
    (G : Subgroup S24) (A B : Subgroup V) (K : Subgroup S24) : Prop :=
  ∃ pr : V → S24 → ZMod 2,
    (∀ x ∈ A, ∀ k ∈ K, ∀ k' ∈ K, pr x (k * k') = pr x k + pr x k') ∧
    (∀ x ∈ A, ∀ x' ∈ A, ∀ k ∈ K, pr (x * x') k = pr x k + pr x' k) ∧
    (∀ x ∈ B, ∀ k ∈ K, pr x k = 0) ∧
    (∀ x ∈ A, x ∉ B → ∃ k ∈ K, pr x k ≠ 0) ∧ (∀ k ∈ K, k ≠ 1 → ∃ x ∈ A, pr x k ≠ 0) ∧
    ∀ g : ↥Γ, (g : S24) ∈ G → ∀ x ∈ A, ∀ k ∈ K,
      pr (ρ g x) ((g : S24) * k * (g : S24)⁻¹) = pr x k

@[expose] def Chain153' {V : Type*} [CommGroup V] (a b : Fin 24) {Γ : Subgroup S24}
    (β : ↥(⊤ : Subgroup V) →* ↥(mathModel false 24 a b Γ).sec ⧸
      (mathModel false 24 a b Γ).ker.subgroupOf (mathModel false 24 a b Γ).sec)
    (ρ : ↥Γ →* MulAut V) (S : Finset (Finset (Fin 24))) (V₇ : Subgroup V) : Prop :=
  IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ S))) ⊥ (fixV (rImg ρ (KY Γ S))) ∧
  rk ↥(fixV (rImg ρ (KY Γ S))) = 1 ∧
  (∀ B' ∈ S, ∃ v : V, IsVecOf' (mathModel false 24 a b Γ) β (eY B') v ∧
    fixV (rImg ρ (KY Γ S)) = Subgroup.zpowers v) ∧
  IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ S))) (fixV (rImg ρ (KY Γ S))) V₇ ∧
  IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ S))) V₇ ⊤ ∧
  rk ↥V₇ = 1 + 6 ∧ IsDualOfConj' ρ (MY Γ S) V₇ (fixV (rImg ρ (KY Γ S))) (KY Γ S) ∧
  (∃ N : Subgroup S24, IsO23' (MY Γ S) N ∧
    (∃ π : ↥(MY Γ S) →* Equiv.Perm (Fin 6), Function.Surjective π ∧
      π.ker = N.subgroupOf (MY Γ S)) ∧
    (∀ g : ↥Γ, (g : S24) ∈ MY Γ S → ((∀ x : V, ρ g x * x⁻¹ ∈ V₇) ↔ (g : S24) ∈ N)) ∧
    InducesOn (rImg ρ (MY Γ S)) ⊤ V₇ (Multiplicative (Fin 2 ⊕ Fin 2 → ZMod 2))
      (natSubI' (Fin 2 ⊕ Fin 2) (ZMod 2) (CFSG.Open.StatedSp 2 (ZMod 2))))

end CFSG.Quasithin.H153
