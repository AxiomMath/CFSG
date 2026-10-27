module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Quasithin.AppendixH.H14.Vocab
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

open scoped Pointwise Matrix commutatorElement MatrixGroups

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu

@[expose] def natHomI (ι : Type) [Fintype ι] [DecidableEq ι] (K : Type*) [Field K] :
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

@[expose] def natSubI (ι : Type) [Fintype ι] [DecidableEq ι] (K : Type*) [Field K]
    (S : Subgroup (GL ι K)) : Subgroup (MulAut (Multiplicative (ι → K))) :=
  S.map (natHomI ι K)

section OrthGen

variable (F : Type*) [Field F] (ι : Type*)

@[expose] def isometryGroupG (Q : (ι → F) → F) : Subgroup ((ι → F) ≃ₗ[F] (ι → F)) where
  carrier := {g | ∀ x, Q (g x) = Q x}
  mul_mem' {g h} hg hh x := by
    show Q (g (h x)) = Q x
    rw [hg, hh]
  one_mem' _ := rfl
  inv_mem' {g} hg x := by
    show Q (g.symm x) = Q x
    have := hg (g.symm x)
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm

@[expose] def omegaG (Q : (ι → F) → F) : Subgroup (MulAut (Multiplicative (ι → F))) :=
  (⁅isometryGroupG F ι Q, isometryGroupG F ι Q⁆).map (linToMulAut F (ι → F))

end OrthGen

@[expose] noncomputable def omegaN (d : ℕ) (Q : (Fin d → ZMod 2) → ZMod 2) :
    Subgroup (MulAut (Multiplicative (Fin d → ZMod 2))) :=
  omegaG (ZMod 2) (Fin d) Q

@[expose] def qPlus6 (x : Fin 6 → ZMod 2) : ZMod 2 := x 0 * x 1 + x 2 * x 3 + x 4 * x 5

@[expose] def InducesOnVia {V : Type*} [CommGroup V] (G : Subgroup (MulAut V)) (U Z : Subgroup V)
    (A : Type*) [CommGroup A] (Γ : Subgroup (MulAut A)) (β : ↥U →* A) : Prop :=
  Z ≤ U ∧ (∀ g ∈ G, ∀ u ∈ U, g u ∈ U) ∧ (∀ g ∈ G, ∀ z ∈ Z, g z ∈ Z) ∧
    Function.Surjective β ∧ (∀ u : ↥U, β u = 1 ↔ (u : V) ∈ Z) ∧
    (∀ g ∈ G, ∃ γ ∈ Γ, ∀ u u' : ↥U, (u' : V) = g u → β u' = γ (β u)) ∧
    (∀ γ ∈ Γ, ∃ g ∈ G, ∀ u u' : ↥U, (u' : V) = g u → β u' = γ (β u))

@[expose] def InducesOnSub {V : Type*} [CommGroup V] (G : Subgroup (MulAut V)) (U Z : Subgroup V)
    (A : Type*) [CommGroup A] (S : Subgroup A) (Γ : Subgroup (MulAut A)) : Prop :=
  Z ≤ U ∧ (∀ g ∈ G, ∀ u ∈ U, g u ∈ U) ∧ (∀ g ∈ G, ∀ z ∈ Z, g z ∈ Z) ∧
  ∃ β : ↥U →* A, β.range = S ∧ (∀ u : ↥U, β u = 1 ↔ (u : V) ∈ Z) ∧
    (∀ g ∈ G, ∃ γ ∈ Γ, ∀ u u' : ↥U, (u' : V) = g u → β u' = γ (β u)) ∧
    (∀ γ ∈ Γ, ∃ g ∈ G, ∀ u u' : ↥U, (u' : V) = g u → β u' = γ (β u))

structure MCtx (isCode : Bool) (d : ℕ) (a b : Fin 24) (O : Finset (Fin 24))
    (Tr S : Finset (Finset (Fin 24))) (B : Finset (Fin 24)) (T₀ Γ : Subgroup S24)
    {V : Type*} [CommGroup V] (ρ : ↥Γ →* MulAut V)
    (β : ↥(⊤ : Subgroup V) →* ↥(mathModel isCode d a b Γ).sec ⧸
      (mathModel isCode d a b Γ).ker.subgroupOf (mathModel isCode d a b Γ).sec) : Prop where
  cfg : Cfg14 a b O Tr S B T₀
  d_mem : d = 22 ∨ d = 23 ∨ d = 24
  L_le : Ld d a b ≤ Γ
  le_Aut : Γ ≤ AutLd d a b
  sylow : IsSylowIn 2 (T₀ ⊓ Γ) Γ
  real : RealizesBy (mathModel isCode d a b Γ) ρ.range ⊤ ⊥ ρ.rangeRestrict β

set_option linter.unusedVariables false in
@[expose] def AllMCtx (isCode : Bool) (dsel : ℕ → Prop)
    (P : ∀ (d : ℕ) (a b : Fin 24) (O : Finset (Fin 24)) (Tr S : Finset (Finset (Fin 24)))
      (B : Finset (Fin 24)) (T₀ Γ : Subgroup S24) (V : Type) [CommGroup V] (ρ : ↥Γ →* MulAut V)
      (β : ↥(⊤ : Subgroup V) →* ↥(mathModel isCode d a b Γ).sec ⧸
        (mathModel isCode d a b Γ).ker.subgroupOf (mathModel isCode d a b Γ).sec), Prop) : Prop :=
  ∀ (d : ℕ), dsel d → ∀ (a b : Fin 24) (O : Finset (Fin 24)) (Tr S : Finset (Finset (Fin 24)))
    (B : Finset (Fin 24)) (T₀ Γ : Subgroup S24) (V : Type) [CommGroup V] (ρ : ↥Γ →* MulAut V)
    (β : ↥(⊤ : Subgroup V) →* ↥(mathModel isCode d a b Γ).sec ⧸
      (mathModel isCode d a b Γ).ker.subgroupOf (mathModel isCode d a b Γ).sec),
    MCtx isCode d a b O Tr S B T₀ Γ ρ β → P d a b O Tr S B T₀ Γ V ρ β

set_option linter.unusedVariables false in
@[expose] def AllMCtxAt (isCode : Bool) (d : ℕ)
    (P : ∀ (a b : Fin 24) (O : Finset (Fin 24)) (Tr S : Finset (Finset (Fin 24)))
      (B : Finset (Fin 24)) (T₀ Γ : Subgroup S24) (V : Type) [CommGroup V] (ρ : ↥Γ →* MulAut V)
      (β : ↥(⊤ : Subgroup V) →* ↥(mathModel isCode d a b Γ).sec ⧸
        (mathModel isCode d a b Γ).ker.subgroupOf (mathModel isCode d a b Γ).sec), Prop) : Prop :=
  ∀ (a b : Fin 24) (O : Finset (Fin 24)) (Tr S : Finset (Finset (Fin 24)))
    (B : Finset (Fin 24)) (T₀ Γ : Subgroup S24) (V : Type) [CommGroup V] (ρ : ↥Γ →* MulAut V)
    (β : ↥(⊤ : Subgroup V) →* ↥(mathModel isCode d a b Γ).sec ⧸
      (mathModel isCode d a b Γ).ker.subgroupOf (mathModel isCode d a b Γ).sec),
    MCtx isCode d a b O Tr S B T₀ Γ ρ β → P a b O Tr S B T₀ Γ V ρ β

@[expose] def IsVecOf {V : Type*} [CommGroup V] (D : FFModel)
    (β : ↥(⊤ : Subgroup V) →* ↥D.sec ⧸ D.ker.subgroupOf D.sec) (e : D.Amb) (v : V) : Prop :=
  ∃ he : e ∈ D.sec, β ⟨v, Subgroup.mem_top v⟩ = QuotientGroup.mk ⟨e, he⟩

@[expose] def IsO2Vec {V : Type*} [CommGroup V] (d : ℕ) (a b : Fin 24) (Γ : Subgroup S24)
    (β : ↥(⊤ : Subgroup V) →* ↥(mathModel false d a b Γ).sec ⧸
      (mathModel false d a b Γ).ker.subgroupOf (mathModel false d a b Γ).sec) (v : V) : Prop :=
  ∃ i j : Fin 24, i ≠ j ∧ (d = 24 ∨ (d = 23 ∧ i = a) ∨ (d = 22 ∧ (i = a ∨ i = b) ∧ j ≠ a ∧ j ≠ b)) ∧
    IsVecOf (mathModel false d a b Γ) β (pairVec i j) v

@[expose] def Yd (d : ℕ) (a b : Fin 24) (O : Finset (Fin 24)) : Finset (Fin 24) :=
  if d = 24 then O else if d = 23 then O.erase a else (O.erase a).erase b

@[expose] def cenM {V : Type*} [CommGroup V] {Γ : Subgroup S24} (ρ : ↥Γ →* MulAut V)
    (W : Subgroup V) : Subgroup ↥Γ :=
  (centSub W).comap ρ

@[expose] def IsO23 (G N : Subgroup S24) : Prop :=
  N ≤ G ∧ (∀ g ∈ G, ∀ n ∈ N, g * n * g⁻¹ ∈ N) ∧ pCoreOf 2 G ≤ N ∧
    (∀ n ∈ N, ∃ k : ℕ, n ^ (3 ^ k) ∈ pCoreOf 2 G) ∧
    ∀ N' : Subgroup S24, N' ≤ G → (∀ g ∈ G, ∀ n ∈ N', g * n * g⁻¹ ∈ N') → pCoreOf 2 G ≤ N' →
      (∀ n ∈ N', ∃ k : ℕ, n ^ (3 ^ k) ∈ pCoreOf 2 G) → N' ≤ N

@[expose] def IsTranspAxis {V : Type*} [CommGroup V] (g : MulAut V) (U W : Subgroup V) (c : V) : Prop :=
  (∀ x ∈ W, g x * x⁻¹ ∈ U) ∧ ∀ x : V, x ∉ W → g x * x⁻¹ * c⁻¹ ∈ U

@[expose] def FullTranspAxis {V : Type*} [CommGroup V] (G X : Subgroup (MulAut V)) (U W : Subgroup V) :
    Prop :=
  (∀ g ∈ X, ∃ c ∈ W, IsTranspAxis g U W c) ∧ (∀ c ∈ W, ∃ g ∈ X, IsTranspAxis g U W c) ∧
  (∀ g ∈ X, (∀ x : V, g x * x⁻¹ ∈ U) → g = 1) ∧
  (∀ h ∈ G, ∀ g ∈ X, ∀ c : V, IsTranspAxis g U W c → IsTranspAxis (h * g * h⁻¹) U W (h c))

@[expose] def FullTranspCenter {V : Type*} [CommGroup V] (G X : Subgroup (MulAut V)) (A V₁ : Subgroup V) :
    Prop :=
  (∀ g ∈ X, ∀ x ∈ A, g x * x⁻¹ ∈ V₁) ∧
  (∀ τ : MulAut ↥A, (∀ x : ↥A, ((τ x : ↥A) : V) * ((x : ↥A) : V)⁻¹ ∈ V₁) →
    ∃ g ∈ X, ∀ x : ↥A, g (x : V) = ((τ x : ↥A) : V)) ∧
  (∀ g ∈ X, (∀ x ∈ A, g x = x) → g = 1) ∧
  (∀ h ∈ G, ∀ g ∈ X, h * g * h⁻¹ ∈ X)

@[expose] def IsDualOfConj {V : Type*} [CommGroup V] {Γ : Subgroup S24} (ρ : ↥Γ →* MulAut V)
    (G : Subgroup S24) (A B : Subgroup V) (K : Subgroup S24) : Prop :=
  ∃ pr : V → S24 → ZMod 2,
    (∀ x ∈ A, ∀ k ∈ K, ∀ k' ∈ K, pr x (k * k') = pr x k + pr x k') ∧
    (∀ x ∈ A, ∀ x' ∈ A, ∀ k ∈ K, pr (x * x') k = pr x k + pr x' k) ∧
    (∀ x ∈ B, ∀ k ∈ K, pr x k = 0) ∧
    (∀ x ∈ A, x ∉ B → ∃ k ∈ K, pr x k ≠ 0) ∧ (∀ k ∈ K, k ≠ 1 → ∃ x ∈ A, pr x k ≠ 0) ∧
    ∀ g : ↥Γ, (g : S24) ∈ G → ∀ x ∈ A, ∀ k ∈ K, pr (ρ g x) ((g : S24) * k * (g : S24)⁻¹) = pr x k

@[expose] def Chain153 {V : Type*} [CommGroup V] (a b : Fin 24) {Γ : Subgroup S24}
    (β : ↥(⊤ : Subgroup V) →* ↥(mathModel false 24 a b Γ).sec ⧸
      (mathModel false 24 a b Γ).ker.subgroupOf (mathModel false 24 a b Γ).sec)
    (ρ : ↥Γ →* MulAut V) (S : Finset (Finset (Fin 24))) (V₇ : Subgroup V) : Prop :=
  IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ S))) ⊥ (fixV (rImg ρ (KY Γ S))) ∧
  rk ↥(fixV (rImg ρ (KY Γ S))) = 1 ∧
  (∀ B' ∈ S, ∃ v : V, IsVecOf (mathModel false 24 a b Γ) β (eY B') v ∧
    fixV (rImg ρ (KY Γ S)) = Subgroup.zpowers v) ∧
  IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ S))) (fixV (rImg ρ (KY Γ S))) V₇ ∧
  IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ S))) V₇ ⊤ ∧
  rk ↥V₇ = 1 + 6 ∧ IsDualOfConj ρ (MY Γ S) V₇ (fixV (rImg ρ (KY Γ S))) (KY Γ S) ∧
  (∃ N : Subgroup S24, IsO23 (MY Γ S) N ∧
    (∃ π : ↥(MY Γ S) →* Equiv.Perm (Fin 6), Function.Surjective π ∧
      π.ker = N.subgroupOf (MY Γ S)) ∧
    (∀ g : ↥Γ, (g : S24) ∈ MY Γ S → ((∀ x : V, ρ g x * x⁻¹ ∈ V₇) ↔ (g : S24) ∈ N)) ∧
    InducesOn (rImg ρ (MY Γ S)) ⊤ V₇ (Multiplicative (Fin 2 ⊕ Fin 2 → ZMod 2))
      (natSubI (Fin 2 ⊕ Fin 2) (ZMod 2) (CFSG.Open.StatedSp 2 (ZMod 2))))

@[expose] def Chain156 {V : Type*} [CommGroup V] {Γ : Subgroup S24} (ρ : ↥Γ →* MulAut V)
    (Tr : Finset (Finset (Fin 24))) (V₉ : Subgroup V) : Prop :=
  IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ Tr))) ⊥ (fixV (rImg ρ (KY Γ Tr))) ∧
  rk ↥(fixV (rImg ρ (KY Γ Tr))) = 3 ∧
  IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ Tr))) (fixV (rImg ρ (KY Γ Tr))) V₉ ∧
  IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ Tr))) V₉ ⊤ ∧
  V₉ = commV (rImg ρ (perfectCore (MY Γ Tr))) ∧ V₉ = commV (rImg ρ (KY Γ Tr)) ∧ rkIdx V₉ = 2 ∧
  InducesOn (rImg ρ (MY Γ Tr)) (fixV (rImg ρ (KY Γ Tr))) ⊥ (Multiplicative (Fin 3 → ZMod 2))
    (natSub 3 (ZMod 2) ⊤) ∧
  InducesOn (rImg ρ (MY Γ Tr)) ⊤ V₉ (Multiplicative (Fin 2 → ZMod 2)) (natSub 2 (ZMod 2) ⊤) ∧
  InducesOn (rImg ρ (MY Γ Tr)) V₉ (fixV (rImg ρ (KY Γ Tr)))
    (Multiplicative (Matrix (Fin 3) (Fin 2) (ZMod 2))) (Subgroup.closure tensorSet32)

@[expose] def TensorFactors156 {V : Type*} [CommGroup V] {Γ : Subgroup S24}
    (ρ : ↥Γ →* MulAut V) (Tr : Finset (Finset (Fin 24))) (V₉ : Subgroup V) : Prop :=
  ∃ (quotientAction : ↥(MY Γ Tr) →* (GL (Fin 3) (ZMod 2) × GL (Fin 2) (ZMod 2)))
    (tensorIdentification : ↥V₉ →* Multiplicative (Matrix (Fin 3) (Fin 2) (ZMod 2))),
    Function.Surjective quotientAction ∧
    quotientAction.ker = (KY Γ Tr).subgroupOf (MY Γ Tr) ∧
    Function.Surjective tensorIdentification ∧
    tensorIdentification.ker = (fixV (rImg ρ (KY Γ Tr))).subgroupOf V₉ ∧
    ∀ (acting : ↥Γ) (hacting : (acting : S24) ∈ MY Γ Tr)
      (original transported : ↥V₉), (transported : V) = ρ acting (original : V) →
        Multiplicative.toAdd (tensorIdentification transported) =
          ((quotientAction ⟨(acting : S24), hacting⟩).1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
            Multiplicative.toAdd (tensorIdentification original) *
            ((quotientAction ⟨(acting : S24), hacting⟩).2 : Matrix (Fin 2) (Fin 2) (ZMod 2))ᵀ

end CFSG.ASVolI.ChH
