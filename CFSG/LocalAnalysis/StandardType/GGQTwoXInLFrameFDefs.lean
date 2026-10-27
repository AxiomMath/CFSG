module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
public import CFSG.LieType.SemisimpleCentralizers.HeldUnitaryComponents

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.SemisimpleCentralizers.Held

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {R : Type} [Group R]

@[expose] def GGQTwoFRCfg (E : Subgroup R) (x : R) (L D J : Subgroup R) : Prop :=
  IsElemAbelian 3 E ∧ 3 ^ 4 ≤ Nat.card E ∧
    (∀ g ∈ Subgroup.centralizer (E : Set R), g ^ 3 = 1 → g ∈ E) ∧
    x ∈ E ∧ x ≠ 1 ∧ x ∈ L ∧ IsComponentOf L (Subgroup.centralizer ({x} : Set R)) ∧
    E ≤ Subgroup.normalizer (L : Set R) ∧
    E ⊓ Subgroup.centralizer (L : Set R) = Subgroup.zpowers x ∧
    D ≤ E ∧ Nat.card D = 3 ^ 2 ∧ x ∈ D ∧
    IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set R)) ∧
    E ⊓ Subgroup.centralizer (J : Set R) = D

@[expose] def GGQTwoUFrame {n : ℕ} {M : Type} [Field M] {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y}
    (ρ : ↥(heldGU n M τ hτ) →* R) (E : Subgroup R) (x : R) (L : Subgroup R) : Prop :=
  Function.Injective ρ ∧
    (∀ g : R, g ∈ E ↔ ∃ A : ↥(heldGU n M τ hτ),
      (∀ i j, i ≠ j → ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i j = 0) ∧ ρ A = g) ∧
    (∃ (A : ↥(heldGU n M τ hτ)) (c : M), c ≠ 1 ∧
      ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) = Matrix.diagonal (fun _ => c) ∧
      ρ A = x) ∧
    L = ((heldSU n M τ hτ).subgroupOf (heldGU n M τ hτ)).map ρ ∧
    ∀ i : Fin n, ∃ α : MulAut R,
      (∀ A A' : ↥(heldGU n M τ hτ),
        (∀ j k, j ≠ k → ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) j k = 0) →
        (∀ j k, j ≠ k → ((A' : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) j k = 0) →
        ((A' : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i i =
          τ (((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i i) →
        (∀ j, j ≠ i → ((A' : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) j j =
          ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) j j) →
        α (ρ A) = ρ A') ∧
      ∀ A : ↥(heldGU n M τ hτ),
        (∀ j, j ≠ i → ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i j = 0 ∧
          ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) j i = 0) →
        ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i i = 1 → α (ρ A) = ρ A

@[expose] def GGQTwoFRFrame (E : Subgroup R) (x : R) (L D J : Subgroup R) : Prop :=
  ∃ (n : ℕ) (_ : 6 ≤ n) (hx : x ∈ E) (ι : Additive ↥E ≃+ (Fin n → ZMod 3)) (i₀ : Fin n)
    (α : MulAut R), ι (Additive.ofMul ⟨x, hx⟩) = (fun _ => 1) ∧
    (ggAutomizer L E).map (ggLin (p := 3) ι) =
      Subgroup.closure {T | ∃ σ : Equiv.Perm (Fin n), ∀ (v : Fin n → ZMod 3) (i : Fin n),
        T v i = v (σ i)} ∧
    (∀ (e : R) (he : e ∈ E), e ∈ D ↔
      ∃ a b : ZMod 3, ι (Additive.ofMul ⟨e, he⟩) = fun i => a + if i = i₀ then b else 0) ∧
    3 ∣ Nat.card J ∧ (∀ e ∈ E, α e ∈ E) ∧
    (∀ (e : R) (he : e ∈ E) (hae : α e ∈ E), ι (Additive.ofMul ⟨α e, hae⟩) =
      fun i => (if i = i₀ then -1 else 1) * ι (Additive.ofMul ⟨e, he⟩) i) ∧
    ∀ j ∈ J, α j = j

@[expose] def GGQTwoFRConcl (E : Subgroup R) (x : R) (L D J : Subgroup R) : Prop :=
  ∃ (n : ℕ) (_ : 6 ≤ n) (y : R) (K : Subgroup R) (hx : x ∈ E) (hy : y ∈ E)
    (ι : Additive ↥E ≃+ (Fin n → ZMod 3)),
    y ∈ D ∧ y ∉ Subgroup.zpowers x ∧ 3 ∣ Nat.card J ∧
    IsComponentOf K (Subgroup.centralizer ({y} : Set R)) ∧ J ≤ K ∧
    x ∉ Subgroup.centralizer (K : Set R) ∧
    (ggAutomizer L E).map (ggLin (p := 3) ι) =
      Subgroup.closure {T | ∃ σ : Equiv.Perm (Fin n), ∀ (v : Fin n → ZMod 3) (i : Fin n),
        T v i = v (σ i)} ∧
    (ggAutomizer K E).map (ggLin (p := 3) ι) =
      Subgroup.closure {T | ∃ σ : Equiv.Perm (Fin n), ∀ (v : Fin n → ZMod 3) (i : Fin n),
        T v i = ((if i.val = 0 then (-1 : ZMod 3) else 1) *
          (if (σ i).val = 0 then (-1 : ZMod 3) else 1)) * v (σ i)} ∧
    ι (Additive.ofMul ⟨x, hx⟩) = (fun _ => 1) ∧
    ι (Additive.ofMul ⟨y, hy⟩) = (fun i => if i.val = 0 then (-1 : ZMod 3) else 1)

@[expose] noncomputable def ggMarkHom {X : Type*} [Group X] (θ : X ⧸ Subgroup.center X ≃* R) :
    X →* R :=
  θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))

@[expose] def GGQTwoFRRecipe (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  (∀ φ ∈ I, ∃ r : R, φ = MulAut.conj r) ∧
    ∀ (E : Subgroup R) (x : R) (L D J : Subgroup R),
      GGQTwoFRCfg E x L D J → GGQTwoFRConcl E x L D J

end CFSG.StandardType

end
