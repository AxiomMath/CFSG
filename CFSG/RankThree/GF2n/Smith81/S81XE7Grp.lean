module

public import CFSG.RankThree.GF2n.Smith81.S81E7Bruhat
public import CFSG.RankThree.GF2n.Smith81.S81XOps

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.E7X

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.RankThree.GF2n.Smith81.XOps CFSG.RankThree.GF2n.Smith81.E7Model


variable {K : Type} [Field K]

abbrev Gp (K : Type) [Field K] : Type := ↥(e7Data_valid.minGroup K)

abbrev xE (γ : Fin (Tag.rank .E7) → ℤ) (c : K) : Gp K := e7Data_valid.xm K γ c

@[expose] def prodX (L : List (Fin (Tag.rank .E7) → ℤ)) (c : (Fin (Tag.rank .E7) → ℤ) → K) : Gp K :=
  (L.map fun γ => xE γ (c γ)).prod

@[expose] def Phi (a : Fin e7Data.d) : Finset (Fin (Tag.rank .E7) → ℤ) :=
  (rootFinset .E7).filter fun γ => pr a γ = 1

theorem mem_Phi {a : Fin e7Data.d} {γ : Fin (Tag.rank .E7) → ℤ} :
    γ ∈ Phi a ↔ IsRoot .E7 γ ∧ pr a γ = 1 := by
  rw [Phi, Finset.mem_filter, mem_rootFinset]

@[expose] def XA (K : Type) [Field K] (a : Fin e7Data.d) : Set (Gp K) :=
  {g | ∃ γ ∈ Phi a, ∃ c : K, g = xE γ c}

@[expose] def UA (K : Type) [Field K] (a : Fin e7Data.d) : Subgroup (Gp K) :=
  Subgroup.closure (XA K a)

structure IsMon (n : Gp K) (σ : Fin e7Data.d → Fin e7Data.d)
    (ρ : (Fin (Tag.rank .E7) → ℤ) → (Fin (Tag.rank .E7) → ℤ)) : Prop where
  weight : ∀ a, endoE n (Finsupp.single a 1) = Finsupp.single (σ a) 1
  isRoot : ∀ γ, IsRoot .E7 γ → IsRoot .E7 (ρ γ)
  neg : ∀ γ, IsRoot .E7 γ → ρ (-γ) = - ρ γ
  conj : ∀ γ, IsRoot .E7 γ → ∀ c : K, n * xE γ c * n⁻¹ = xE (ρ γ) c
  surj : ∀ γ', IsRoot .E7 γ' → ∃ γ, IsRoot .E7 γ ∧ ρ γ = γ'

end CFSG.RankThree.GF2n.Smith81.E7X
