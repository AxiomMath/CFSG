module

public import CFSG.Quasithin.EmptyFaithful.SzN31Basic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzN31

open CFSG.Quasithin.G11 CFSG.Open

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem pCoreOf_normal_conj (p : ℕ) (Γ : Subgroup (GLV V)) :
    ∀ γ ∈ Γ, ∀ n ∈ pCoreOf p Γ, γ * n * γ⁻¹ ∈ pCoreOf p Γ := by
  intro γ hγ n hn
  obtain ⟨n', hn', rfl⟩ := Subgroup.mem_map.1 hn
  have hnorm : (Open.pCore p ↥Γ).Normal := by
    exact CFSG.pCore_normal
  exact Subgroup.mem_map.2 ⟨⟨γ, hγ⟩ * n' * ⟨γ, hγ⟩⁻¹, hnorm.conj_mem n' hn' ⟨γ, hγ⟩, by simp⟩

theorem isPGroup_pCoreOf (p : ℕ) (Γ : Subgroup (GLV V)) : IsPGroup p (pCoreOf p Γ) := by
  have h : IsPGroup p (Open.pCore p ↥Γ) := by
    exact CFSG.pCore_isPGroup
  exact h.map Γ.subtype

theorem pCoreOf_two_eq_bot_of_isIrr [Finite V] {Γ : Subgroup (GLV V)} (hirr : IsIrr Γ ⊤) :
    pCoreOf 2 Γ = ⊥ :=
  eq_bot_of_isPGroup_normal hirr (pCoreOf_normal_conj 2 Γ) (isPGroup_pCoreOf 2 Γ)

theorem fixedSpace_pCoreOf_eq_bot_of_isIrr {Γ : Subgroup (GLV V)} (hirr : IsIrr Γ ⊤) {p : ℕ}
    (hne : pCoreOf p Γ ≠ ⊥) : fixedSpace (pCoreOf p Γ) = ⊥ := by
  have hinv : Invariant Γ (fixedSpace (pCoreOf p Γ)) :=
    invariant_fixedSpace (pCoreOf_normal_conj p Γ)
  rcases hirr.eq_bot_or_eq hinv le_top with h | h
  · exact h
  · exfalso
    apply hne
    rw [eq_bot_iff]
    intro n hn
    rw [Subgroup.mem_bot]
    refine LinearEquiv.ext fun u => ?_
    have hu : u ∈ fixedSpace (pCoreOf p Γ) := by rw [h]; trivial
    exact hu n hn

end CFSG.Quasithin.SzN31
