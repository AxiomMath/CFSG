module

public import CFSG.Milestones.ASVolI.H13

public section

open scoped Pointwise Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open CFSG.Monster.Code

@[expose] def conjSubg {X : Type*} [Group X] (g : X) (A : Subgroup X) : Subgroup X :=
  A.map (MulAut.conj g).toMonoidHom

structure Cfg14 (a b : Fin 24) (O : Finset (Fin 24)) (Tr S : Finset (Finset (Fin 24)))
    (B : Finset (Fin 24)) (T₀ : Subgroup S24) : Prop where
  ne : a ≠ b
  octad : IsOctad O
  trio : IsTrio Tr
  sextet : IsSextet S
  O_mem : O ∈ Tr
  trio_union : ∀ P ∈ Tr, ∃ B₁ ∈ S, ∃ B₂ ∈ S, B₁ ≠ B₂ ∧ P = B₁ ∪ B₂
  B_mem : B ∈ S
  a_B : a ∈ B
  b_B : b ∈ B
  a_O : a ∈ O
  b_O : b ∈ O
  sylow : IsSylowIn 2 T₀ M24g
  stab_O : ∀ g ∈ T₀, g • O = O
  stab_Tr : ∀ g ∈ T₀, g • Tr = Tr
  stab_S : ∀ g ∈ T₀, g • S = S

@[expose] def MY {α : Type*} [MulAction S24 α] (Γ : Subgroup S24) (Y : α) : Subgroup S24 :=
  Γ ⊓ MulAction.stabilizer S24 Y

@[expose] def KY {α : Type*} [MulAction S24 α] (Γ : Subgroup S24) (Y : α) : Subgroup S24 :=
  pCoreOf 2 (MY Γ Y)

@[expose] def IsE2k (k : ℕ) (A : Subgroup S24) : Prop := IsElemAbelian 2 A ∧ Nat.card A = 2 ^ k

@[expose] def gammaLset (d : ℕ) (K : Type*) [Field K] : Set (MulAut (Multiplicative (Fin d → K))) :=
  {g | ∃ σ : K ≃+* K, ∀ (c : K) (w : Fin d → K),
    g (Multiplicative.ofAdd (c • w)) =
      Multiplicative.ofAdd (σ c • Multiplicative.toAdd (g (Multiplicative.ofAdd w)))}

@[expose] def IsHyperoval (K : Type*) [Field K] (Ω : Set (Submodule K (Fin 3 → K))) : Prop :=
  Ω.ncard = 6 ∧ (∀ P ∈ Ω, Module.finrank K P = 1) ∧
    ∀ P ∈ Ω, ∀ Q ∈ Ω, ∀ R ∈ Ω, P ≠ Q → P ≠ R → Q ≠ R → Module.finrank K ↥(P ⊔ Q ⊔ R) = 3

@[expose] def PermutesPoints {K : Type*} [Field K] (g : MulAut (Multiplicative (Fin 3 → K)))
    (Ω : Set (Submodule K (Fin 3 → K))) : Prop :=
  ∀ P ∈ Ω, ∃ Q ∈ Ω, ∀ v : Fin 3 → K,
    (∃ w ∈ P, g (Multiplicative.ofAdd w) = Multiplicative.ofAdd v) ↔ v ∈ Q

@[expose] def hatS6set (K : Type*) [Field K] (Ω : Set (Submodule K (Fin 3 → K))) :
    Set (MulAut (Multiplicative (Fin 3 → K))) :=
  {g | g ∈ gammaLset 3 K ∧ PermutesPoints g Ω}

@[expose] def IsKLinearAut {K : Type*} [Field K] {d : ℕ} (γ : MulAut (Multiplicative (Fin d → K))) : Prop :=
  ∀ (c : K) (w : Fin d → K), γ (Multiplicative.ofAdd (c • w)) =
    Multiplicative.ofAdd (c • Multiplicative.toAdd (γ (Multiplicative.ofAdd w)))

@[expose] def tensorSet32 : Set (MulAut (Multiplicative (Matrix (Fin 3) (Fin 2) (ZMod 2)))) :=
  {γ | ∃ (g : GL (Fin 3) (ZMod 2)) (h : GL (Fin 2) (ZMod 2)),
    ∀ X : Matrix (Fin 3) (Fin 2) (ZMod 2),
      Multiplicative.toAdd (γ (Multiplicative.ofAdd X)) =
        (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * X * (h : Matrix (Fin 2) (Fin 2) (ZMod 2))ᵀ}

@[expose] def ConjIso {X : Type*} [Group X] (G K : Subgroup X) (A : Type*) [CommGroup A]
    (Γ : Set (MulAut A)) (φ : ↥K ≃* A) (π : ↥G →* MulAut A) : Prop :=
  K ≤ G ∧ (∀ g, π g ∈ Γ) ∧ (∀ γ ∈ Γ, ∃ g, π g = γ) ∧ (∀ g : ↥G, π g = 1 ↔ (g : X) ∈ K) ∧
    ∀ (g : ↥G) (k k' : ↥K), (k' : X) = (g : X) * k * (g : X)⁻¹ → φ k' = π g (φ k)

@[expose] def ConjIsoModel {X : Type*} [Group X] (G K : Subgroup X) (A : Type*) [CommGroup A]
    (Γ : Set (MulAut A)) : Prop :=
  ∃ (φ : ↥K ≃* A) (π : ↥G →* MulAut A), ConjIso G K A Γ φ π

@[expose] def ConjSymNatural (G K : Subgroup S24) (n : ℕ) (R : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  K ≤ G ∧ ∃ (π : ↥G →* Equiv.Perm (Fin n)) (β : ↥(G6.coreMod n) →* S24),
    π.range = R ∧ π.ker = K.subgroupOf G ∧ β.range = K ∧ β.ker = G6.natKer n ∧
    ∀ (g : ↥G) (u : ↥(G6.coreMod n)), β (G6.coreAct n (π g) u) = (g : S24) * β u * (g : S24)⁻¹

open scoped Classical in
@[expose] noncomputable def fixedSet (z : S24) : Finset (Fin 24) :=
  Finset.univ.filter fun i => z i = i

end CFSG.ASVolI.ChH
