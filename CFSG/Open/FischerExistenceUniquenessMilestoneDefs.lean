module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Open
open Matrix

universe u

variable {X : Type u} [Group X]

@[expose] def fischerEUIsPair (E : Set X) : Prop :=
  (∃ e₀ : X, E = {g | IsConj e₀ g}) ∧ (∀ e ∈ E, orderOf e = 2) ∧
    (∀ e ∈ E, ∀ f ∈ E, orderOf (e * f) ∈ ({1, 2, 3} : Set ℕ)) ∧ Subgroup.closure E = ⊤

@[expose] def fischerEUIsCenterlessPair (E : Set X) : Prop :=
  fischerEUIsPair E ∧ Subgroup.center X = ⊥ ∧ IsSimpleGroup (commutator X)

@[expose] def fischerEULocalSet (E : Set X) (e : X) : Set X :=
  {f | f ∈ E ∧ f ≠ e ∧ f * e = e * f}

@[expose] def fischerEULocalGroup (E : Set X) (e : X) : Subgroup X :=
  Subgroup.closure (fischerEULocalSet E e)

abbrev fischerEULocalQuotient (E : Set X) (e : X) : Type u :=
  fischerEULocalGroup E e ⧸ Subgroup.center (fischerEULocalGroup E e)

@[expose] def fischerEULocalClass (E : Set X) (e : X) : Set (fischerEULocalQuotient E e) :=
  {y | ∃ f : fischerEULocalGroup E e, (f : X) ∈ fischerEULocalSet E e ∧ y = QuotientGroup.mk f}

@[expose] noncomputable def fischerEUHerm (x y : Fin 6 → GaloisField 2 2) : GaloisField 2 2 :=
  ∑ i, x i * y i ^ 2

@[expose] noncomputable def fischerEUSU : Subgroup (GL (Fin 6) (GaloisField 2 2)) :=
  Subgroup.closure {A | (A : Matrix (Fin 6) (Fin 6) (GaloisField 2 2)).det = 1 ∧
    ∀ x y, fischerEUHerm ((A : Matrix (Fin 6) (Fin 6) (GaloisField 2 2)) *ᵥ x)
      ((A : Matrix (Fin 6) (Fin 6) (GaloisField 2 2)) *ᵥ y) = fischerEUHerm x y}

abbrev fischerEUPSU : Type := fischerEUSU ⧸ Subgroup.center fischerEUSU

@[expose] def fischerEUTransvections : Set fischerEUPSU :=
  {y | ∃ A : fischerEUSU, ∃ v : Fin 6 → GaloisField 2 2, v ≠ 0 ∧ fischerEUHerm v v = 0 ∧
    (∀ x, ((A : GL (Fin 6) (GaloisField 2 2)) : Matrix (Fin 6) (Fin 6) (GaloisField 2 2)) *ᵥ x =
      x + fischerEUHerm x v • v) ∧ y = QuotientGroup.mk A}

@[expose] def fischerEUTypeF22 (E : Set X) : Prop :=
  ∃ e ∈ E, ∃ φ : fischerEULocalQuotient E e ≃* fischerEUPSU,
    φ '' fischerEULocalClass E e = fischerEUTransvections

@[expose] def fischerEUTypeF23 (E : Set X) : Prop :=
  ∃ e ∈ E, fischerEUIsPair (fischerEULocalClass E e) ∧ fischerEUTypeF22 (fischerEULocalClass E e)

@[expose] def fischerEUTypeF24 (E : Set X) : Prop :=
  ∃ e ∈ E, fischerEUIsPair (fischerEULocalClass E e) ∧ fischerEUTypeF23 (fischerEULocalClass E e)

@[expose] def fischerEUType (k : ℕ) (E : Set X) : Prop :=
  (k = 22 ∧ fischerEUTypeF22 E) ∨ (k = 23 ∧ fischerEUTypeF23 E) ∨ (k = 24 ∧ fischerEUTypeF24 E)

@[expose] def fischerEUPerfectCentralizer (d : X) : Prop :=
  commutator (Subgroup.centralizer ({d} : Set X)) = ⊤ ∧
    (Subgroup.center (Subgroup.centralizer ({d} : Set X))).map
      (Subgroup.centralizer ({d} : Set X)).subtype = Subgroup.zpowers d

@[expose] def fischerEULocalStructure (k : ℕ) (d : X) : Prop :=
  (k = 22 → fischerEUPerfectCentralizer d ∧
    Nonempty (Subgroup.centralizer ({d} : Set X) ⧸
      Subgroup.center (Subgroup.centralizer ({d} : Set X)) ≃* fischerEUPSU)) ∧
  (k = 23 → fischerEUPerfectCentralizer d ∧
    ∃ D' : Set (Subgroup.centralizer ({d} : Set X) ⧸
        Subgroup.center (Subgroup.centralizer ({d} : Set X))),
      fischerEUIsCenterlessPair D' ∧ fischerEUTypeF22 D') ∧
  (k = 24 → ∃ K : Subgroup X, K ≤ Subgroup.centralizer ({d} : Set X) ∧
    K ⊓ Subgroup.zpowers d = ⊥ ∧ K ⊔ Subgroup.zpowers d = Subgroup.centralizer ({d} : Set X) ∧
    ∃ D' : Set K, fischerEUIsCenterlessPair D' ∧ fischerEUTypeF23 D')

end CFSG.Open
