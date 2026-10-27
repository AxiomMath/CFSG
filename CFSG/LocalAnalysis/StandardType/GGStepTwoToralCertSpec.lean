module

public import CFSG.LocalAnalysis.StandardType.GGExcKGToralFrame
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompKac

public section

namespace CFSG.StandardType.StepTwoToralCert

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar

variable {τ : Tag} {p : ℕ}

@[expose] noncomputable def kacOf : (τ : Tag) → KacData τ
  | .G2 => kacG2
  | .F4 => kacF4
  | .D4 => kacD4
  | .E6 => kacE6
  | .E7 => kacE7
  | .E8 => kacE8

@[expose] noncomputable def cowAct (u : WeylGroup τ) (f : Fin τ.rank → ZMod p) :
    Fin τ.rank → ZMod p :=
  fun i => latChar p f (u⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ))

@[expose] def CommutesPi (π : Equiv.Perm (Fin τ.rank)) (u : WeylGroup τ) : Prop :=
  ∀ α : Fin τ.rank → ℤ, u • latPerm π α = latPerm π (u • α)

@[expose] def annSub (p : ℕ) (Φ : Set (Fin τ.rank → ℤ)) :
    Submodule (ZMod p) (Fin τ.rank → ZMod p) where
  carrier := {f | ∀ α ∈ Φ, latChar p f α = 0}
  add_mem' {f g} hf hg α hα := by
    have h1 : latChar p f α = 0 := hf α hα
    have h2 : latChar p g α = 0 := hg α hα
    simp only [latChar, Pi.add_apply, mul_add, Finset.sum_add_distrib] at h1 h2 ⊢
    rw [h1, h2, add_zero]
  zero_mem' α _ := by simp [latChar]
  smul_mem' c f hf α hα := by
    simp only [latChar, Pi.smul_apply, smul_eq_mul] at hf ⊢
    calc ∑ i, (α i : ZMod p) * (c * f i) = c * ∑ i, (α i : ZMod p) * f i := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      _ = 0 := by rw [hf α hα, mul_zero]

@[expose] def phiSet (p : ℕ) (D : Set (Fin τ.rank → ZMod p)) : Set (Fin τ.rank → ℤ) :=
  {α | IsRoot τ α ∧ ∀ d ∈ D, latChar p d α = 0}

@[expose] def fixedSub (p : ℕ) (π : Equiv.Perm (Fin τ.rank)) :
    Submodule (ZMod p) (Fin τ.rank → ZMod p) where
  carrier := {f | ∀ i, f (π i) = f i}
  add_mem' {f g} hf hg i := by simp only [Pi.add_apply, hf i, hg i]
  zero_mem' _ := rfl
  smul_mem' c f hf i := by simp only [Pi.smul_apply, hf i]

@[expose] def t0Sub (τ : Tag) (p : ℕ) : Submodule (ZMod p) (Fin τ.rank → ZMod p) :=
  Submodule.span (ZMod p) (Set.range fun j : Fin τ.rank => fun i => ((τ.cartan j i : ℤ) : ZMod p))

@[expose] def modP (p : ℕ) (μ : Fin τ.rank → ℤ) : Fin τ.rank → ZMod p := fun i => (μ i : ZMod p)

@[expose] def QualPlane (p : ℕ) (V D : Submodule (ZMod p) (Fin τ.rank → ZMod p)) : Prop :=
  D ≤ V ∧ Nat.card D = p ^ 2 ∧ (phiSet (τ := τ) p (D : Set (Fin τ.rank → ZMod p))).Nonempty ∧
    Nat.card ↥(V ⊓ annSub p (phiSet (τ := τ) p (D : Set (Fin τ.rank → ZMod p)))) ≤ p ^ 3

@[expose] def CertConcl (p : ℕ) (π : Equiv.Perm (Fin τ.rank))
    (V : Submodule (ZMod p) (Fin τ.rank → ZMod p)) (b : Fin τ.rank → ZMod p)
    (O : Set (Fin τ.rank → ℤ)) (D : Submodule (ZMod p) (Fin τ.rank → ZMod p)) : Prop :=
  ∃ s ∈ Submodule.span (ZMod p) (insert b ((V : Set (Fin τ.rank → ZMod p)) ∩
      latEigenCoroot p τ.symmetrizedCartan π O)), s ≠ 0 ∧
    ∃ u : WeylGroup τ, CommutesPi π u ∧ cowAct u s ∈ D

@[expose] def SplitCertSpec (τ : Tag) (p : ℕ) (V : Submodule (ZMod p) (Fin τ.rank → ZMod p)) :
    Prop :=
  ∀ μ : Fin τ.rank → ℤ, (kacOf τ).IsNormal p μ → modP p μ ∈ V → modP p μ ≠ 0 →
    ∀ O : Set (Fin τ.rank → ℤ),
      IsCompOrbit τ.symmetrizedCartan 1 (latPhi {α | IsRoot τ α} p (modP p μ)) O →
      Nat.card ↥(V ⊓ annSub p O) ≤ p ^ 2 →
      ∀ D : Submodule (ZMod p) (Fin τ.rank → ZMod p), QualPlane p V D →
        CertConcl p 1 V (modP p μ) O D

@[expose] def TwistCertSpec (p : ℕ) (γ : Equiv.Perm (Fin Tag.E6.rank)) : Prop :=
  ∀ b ∈ fixedSub p γ, b ≠ 0 →
    ∀ O : Set (Fin Tag.E6.rank → ℤ),
      IsCompOrbit Tag.E6.symmetrizedCartan γ (latPhi {α | IsRoot .E6 α} p b) O →
      Nat.card ↥(fixedSub p γ ⊓ annSub p O) ≤ p ^ 2 →
      ∀ D : Submodule (ZMod p) (Fin Tag.E6.rank → ZMod p), QualPlane p (fixedSub p γ) D →
        CertConcl p γ (fixedSub p γ) b O D

@[expose] def e6Gamma : Equiv.Perm (Fin Tag.E6.rank) :=
  Equiv.swap ⟨0, by decide⟩ ⟨5, by decide⟩ * Equiv.swap ⟨2, by decide⟩ ⟨4, by decide⟩

@[expose] def CertAll : Prop :=
  SplitCertSpec .F4 3 ⊤ ∧
    (SplitCertSpec .E6 3 ⊤ ∧ SplitCertSpec .E6 3 (t0Sub .E6 3) ∧ SplitCertSpec .E6 5 ⊤) ∧
    (SplitCertSpec .E7 3 ⊤ ∧ SplitCertSpec .E7 5 ⊤ ∧ SplitCertSpec .E7 7 ⊤) ∧
    (SplitCertSpec .E8 3 ⊤ ∧ SplitCertSpec .E8 5 ⊤ ∧ SplitCertSpec .E8 7 ⊤) ∧
    (TwistCertSpec 3 e6Gamma ∧ TwistCertSpec 5 e6Gamma)

end CFSG.StandardType.StepTwoToralCert
