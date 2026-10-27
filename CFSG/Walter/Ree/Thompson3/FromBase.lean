module

public import CFSG.Walter.Ree.Thompson3.Bridge
public import CFSG.Walter.Ree.Thompson2.Alg.Eq211
public import CFSG.Walter.Ree.Thompson2.Alg.Identity

public section

namespace CFSG.Walter.Ree.T2

variable {k : Type} [Field k] [CharP k 3] [Fintype k]

namespace RType

variable {σ : k ≃+* k} {d : k} {G : Type} [Group G] [Finite G] (R : RType G k σ d)

theorem thompsonIdentity_holds :
    ThompsonIdentity R := by
  intro a ha haσ
  obtain ⟨S, hS⟩ := R.exists_isS
  exact Alg.thompsonT_eq_zero_of ha haσ (fun _ hx => R.sigmaTwo_eq_one hx) (fe1C hS ha haσ)
    (fe2C hS) (gf3C hS) (t81C1 hS)

theorem isS_sFormula
    {a : ℕ} (ha : Even a) (haσ : ∀ x : k, (σ x * x) ^ a = x ^ 2) :
    IsS R (Alg.sFormula σ a d) := by
  obtain ⟨S, hS⟩ := R.exists_isS
  have h := Alg.S_eq_sFormula_of_sigmaTwo ha haσ (fun _ hx => R.sigmaTwo_eq_one hx)
    (fe1C hS ha haσ) (fe2C hS) (gf3C hS)
  rwa [← h]

theorem eq211_holds
    {a : ℕ} (ha : Even a) (haσ : ∀ x : k, (σ x * x) ^ a = x ^ 2) :
    Eq211 R a (Alg.c211 σ a) := by
  obtain ⟨S, hS⟩ := R.exists_isS
  exact Alg.eq211_of ha haσ (fe1C hS ha haσ) (fe2C hS) (gf3C hS) (t81C3 hS)

end RType

theorem sExplicit_holds
    (σ : k ≃+* k) (d : k) : ∃ S : k → k × k × k,
    ∀ (G : Type) [Group G] [Finite G] (R : RType G k σ d), IsS R S := by
  by_cases h : ∃ (G : Type) (_ : Group G) (_ : Finite G), Nonempty (RType G k σ d)
  · obtain ⟨G₀, _, _, ⟨R₀⟩⟩ := h
    obtain ⟨a, ha, haσ⟩ := R₀.exists_a'
    exact ⟨Alg.sFormula σ a d, fun G _ _ R => R.isS_sFormula ha haσ⟩
  · exact ⟨fun _ => 0, fun G _ _ R => absurd ⟨G, inferInstance, inferInstance, ⟨R⟩⟩ h⟩

theorem thompson2_of_base
    (hbase : BaseExists) : Thompson2 where
  base := hbase
  thompsonIdentity _ _ _ _ _ _ _ _ _ R := R.thompsonIdentity_holds
  sExplicit _ _ _ _ σ _ d := sExplicit_holds σ d
  eq211 _ _ _ _ σ _ a ha haσ _ := ⟨Alg.c211 σ a, fun _ _ _ _ R => R.eq211_holds ha haσ⟩

end CFSG.Walter.Ree.T2
