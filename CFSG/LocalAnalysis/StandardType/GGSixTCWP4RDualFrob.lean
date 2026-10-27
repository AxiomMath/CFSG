module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RDual
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RConj
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RWeyl

public section

namespace CFSG.StandardType.TableCRes


open Certificates.TcRes CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

section DualFrob

variable {τ : Tag} {p : ℕ}

theorem tch_frob_root (φ : AddMonoid.End (Fin τ.rank → ℤ)) (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (hρ : ∀ γ, IsRoot τ γ → ρ γ = φ γ) (c : ZMod p) (v : Fin τ.rank → ZMod p)
    (hfrob : ∀ j : Fin τ.rank, ∑ k, (((ρ (Pi.single j 1)) k : ℤ) : ZMod p) * v k = c * v j)
    (γ : Fin τ.rank → ℤ) (hγ : IsRoot τ γ) :
    ∑ i, (((ρ γ) i : ℤ) : ZMod p) * v i = c * ∑ k, ((γ k : ℤ) : ZMod p) * v k := by
  have hφe : ∀ k : Fin τ.rank, φ (Pi.single k 1) = ρ (Pi.single k 1) := fun k =>
    (hρ _ (isRoot_single τ k)).symm
  have hdec : ∀ i : Fin τ.rank, (((ρ γ) i : ℤ) : ZMod p) =
      ∑ k, ((γ k : ℤ) : ZMod p) * (((ρ (Pi.single k 1)) i : ℤ) : ZMod p) := by
    intro i
    rw [hρ γ hγ, tch_map_decomp φ γ, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Int.cast_sum,
      Int.cast_mul, hφe]
  have hk : ∀ k : Fin τ.rank, ∑ i, (γ k : ZMod p) * (((ρ (Pi.single k 1)) i : ℤ) : ZMod p) * v i
      = c * ((γ k : ZMod p) * v k) := by
    intro k
    have h1 : ∑ i, (γ k : ZMod p) * (((ρ (Pi.single k 1)) i : ℤ) : ZMod p) * v i
        = (γ k : ZMod p) * ∑ i, (((ρ (Pi.single k 1)) i : ℤ) : ZMod p) * v i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => mul_assoc _ _ _
    rw [h1, hfrob k]
    ring
  simp_rw [hdec, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => hk k

theorem tcrDual_frob
    (h : WeylGroup τ) (φ : AddMonoid.End (Fin τ.rank → ℤ)) (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (hρ : ∀ γ, IsRoot τ γ → ρ γ = φ γ) (c : ZMod p)
    (P : Submodule (ZMod p) (Fin τ.rank → ZMod p))
    (hfrob : ∀ v ∈ P, ∀ j : Fin τ.rank,
      ∑ k, (((ρ (Pi.single j 1)) k : ℤ) : ZMod p) * v k = c * v j) :
    ∀ v' ∈ P.map (tcrDualLin h p), ∀ j : Fin τ.rank,
      ∑ k, ((((tcrConjPerm h ρ) (Pi.single j 1)) k : ℤ) : ZMod p) * v' k = c * v' j := by
  intro v' hv' j
  obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hv'
  have hroot : IsRoot τ (h⁻¹ • (Pi.single j 1 : Fin τ.rank → ℤ)) :=
    IsRoot.smul (isRoot_single τ j) h⁻¹
  have key := tcrDualVec_pair h (ρ (h⁻¹ • (Pi.single j 1 : Fin τ.rank → ℤ))) v
  rw [tcrDualLin_apply, tcrConjPerm_apply, key, tch_frob_root φ ρ hρ c v (hfrob v hv) _ hroot]
  rfl

theorem tcrConjPerm_root
    (h : WeylGroup τ) (φ : AddMonoid.End (Fin τ.rank → ℤ)) (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (hρ : ∀ γ, IsRoot τ γ → ρ γ = φ γ) (γ : Fin τ.rank → ℤ) (hγ : IsRoot τ γ) :
    tcrConjPerm h ρ γ = (tcrWEnd τ h * φ * tcrWEnd τ h⁻¹) γ := by
  rw [tcrConjPerm_apply, hρ _ (IsRoot.smul hγ h⁻¹)]
  rfl

end DualFrob

end CFSG.StandardType.TableCRes

end
