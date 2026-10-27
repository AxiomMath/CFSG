module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin.S153N

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

structure FormHyp (G : Type) [Group G] (C K M : Subgroup G) (𝒜 : Set (Subgroup G)) : Type 1 where
  Vb : Type
  cg : CommGroup Vb
  fin : Finite Vb
  sq : ∀ v : Vb, v ^ 2 = 1
  ω : MulAut Vb
  σ : MulAut Vb
  ρ : ↥C →* MulAut Vb
  ω3 : ∀ u : Vb, ω (ω (ω u)) = u
  σ2 : ∀ u : Vb, σ (σ u) = u
  ρω : ∀ (c : ↥C) (u : Vb), ρ c (ω u) = ω (ρ c u)
  ρσ : ∀ (c : ↥C) (u : Vb), ρ c (σ u) = σ (ρ c u)
  ker_eq : ρ.ker = K.subgroupOf C
  Vbar : Subgroup Vb
  card_Vbar : Nat.card ↥Vbar = 4
  ω_mem : ∀ u ∈ Vbar, ω u ∈ Vbar
  σ_mem : ∀ u ∈ Vbar, σ u ∈ Vbar
  ω_fpf : ∀ u ∈ Vbar, ω u = u → u = 1
  σω_Vbar : ∀ u ∈ Vbar, σ (ω u) = ω (ω (σ u))
  stab_iff : ∀ c : ↥C, (∀ u ∈ Vbar, ρ c u ∈ Vbar) ↔ (c : G) ∈ M
  gen : Subgroup.closure {u : Vb | ∃ (c : ↥C) (v : Vb), v ∈ Vbar ∧ u = ρ c v} = ⊤
  elem : ∀ A ∈ 𝒜, A ≤ C ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ ∀ a ∈ A, a ^ 2 = 1
  offender : ∀ A ∈ 𝒜, Nat.card Vb ≤ ((A ⊓ K).relIndex A) ^ 2 *
    Nat.card ↥(@fixV Vb cg ((A.subgroupOf C).map ρ))

attribute [instance] FormHyp.cg FormHyp.fin

end CFSG.Quasithin.S153N
