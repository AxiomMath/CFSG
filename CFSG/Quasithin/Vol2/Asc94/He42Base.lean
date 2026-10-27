module

public import CFSG.Quasithin.Vol2.Asc94.HeJ13
public import CFSG.Quasithin.Vol2.Asc94.HeJ7
public import CFSG.Quasithin.Vol2.Asc94.HeJ12

public section

namespace CFSG.Quasithin.A94.He42

open Matrix Subgroup CFSG.CGT.M24S CFSG.Open CFSG.Quasithin.A94.HeJ

structure HeSetup (G : Type) [Group G] [Finite G] where
  A : Subgroup G
  A' : Subgroup G
  u : G → V2
  w : G → V2
  m : G → M2
  N : Subgroup G
  T : Subgroup G
  a : G
  x : G
  hD : Data40 A A' u w m N T a
  hD' : Data40 A' A w u (fun y => (m y)ᵀ) N T a
  hN : N = normalizer ((A ⊔ A' : Subgroup G) : Set G)
  hxN : x ∈ N
  hxa : x ∈ centralizer ({a} : Set G)
  hx3 : orderOf x = 3
  h5 : ∀ g : G, orderOf g = 5 → ∃ y ∈ A ⊓ A', g * y ≠ y * g

namespace HeSetup

variable {G : Type} [Group G] [Finite G] (S : HeSetup G)

@[expose] def Z : Subgroup G := S.A ⊓ S.A'

@[expose] def J : Subgroup G := S.A ⊔ S.A'

@[expose] def B : Subgroup G := (S.A ⊓ S.A') ⊓ centralizer ({S.x} : Set G)

@[expose] def L1 : Subgroup G := normalizer (S.A : Set G) ⊓ centralizer (S.B : Set G)

@[expose] def L2 : Subgroup G := normalizer (S.A' : Set G) ⊓ centralizer (S.B : Set G)

@[expose] def K : Subgroup G := S.N ⊓ centralizer (S.B : Set G)

@[expose] def L : Subgroup G := S.L1 ⊔ S.L2

@[expose] noncomputable def rho : ↥S.N →* GL2 × GL2 := S.hD.hT.rho S.N S.hD.hK.norm

@[expose] noncomputable def g : GL2 := (S.rho ⟨S.x, S.hxN⟩).1

open Classical in
@[expose] noncomputable def rhoG (y : G) : GL2 × GL2 :=
  if h : y ∈ S.N then S.rho ⟨y, h⟩ else 1

theorem rhoG_of_mem {y : G} (h : y ∈ S.N) : S.rhoG y = S.rho ⟨y, h⟩ := dif_pos h

end HeSetup

end CFSG.Quasithin.A94.He42
