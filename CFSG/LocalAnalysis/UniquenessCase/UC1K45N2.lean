module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45R24
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45N2A

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

open Subgroup

variable {p : ℕ} {G : Type} [Group G] [Finite G] {D : Subgroup G}

private noncomputable def n2_quotient_alt5_equiv (c : Ctx45 p G D)
    (hker : Wker G = CFSG.pPrimeCore 3 G) :
    (G ⧸ Wker G) ≃* ↥(alternatingGroup (Fin 5)) :=
  (QuotientGroup.quotientMulEquivOfEq hker).trans c.alt5.some

private lemma n2_eta_kernel {A : Type} [Group A] (η₁ : A →* Equiv.Perm (Fin 5))
    (hη₁ : Function.Injective η₁) (ι : (G ⧸ Wker G) ≃* A) :
    (η₁.comp (ι.toMonoidHom.comp (QuotientGroup.mk' (Wker G)))).ker = Wker G := by
  rw [MonoidHom.ker_comp_of_injective _ _ hη₁,
    MonoidHom.ker_comp_of_injective _ _ ι.injective, QuotientGroup.ker_mk']

private lemma n2_eta_range {A : Type} [Group A] (η₁ : A →* Equiv.Perm (Fin 5))
    (ι : (G ⧸ Wker G) ≃* A) :
    (η₁.comp (ι.toMonoidHom.comp (QuotientGroup.mk' (Wker G)))).range = η₁.range := by
  have hsurj : Function.Surjective (ι.toMonoidHom.comp (QuotientGroup.mk' (Wker G))) :=
    ι.surjective.comp (QuotientGroup.mk'_surjective (Wker G))
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, MonoidHom.range_eq_map]

private lemma n2_psi_surjective {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (f : CFSG.Quasithin.G6.coreMod 5 ≃* Multiplicative W)
    (π : ↥(Xof G) →* Multiplicative W) (hπ : Function.Surjective π) :
    Function.Surjective (f.symm.toMonoidHom.comp π) :=
  f.symm.surjective.comp hπ

private lemma n2_psi_kernel {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (f : CFSG.Quasithin.G6.coreMod 5 ≃* Multiplicative W)
    (π : ↥(Xof G) →* Multiplicative W) :
    (f.symm.toMonoidHom.comp π).ker = π.ker :=
  MonoidHom.ker_comp_of_injective π f.symm.toMonoidHom f.symm.injective

private lemma n2_psi_equivariant {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    {A : Type} [Group A] (φ : (G ⧸ Wker G) →* (W ≃ₗ[ZMod 2] W))
    (π : ↥(Xof G) →* Multiplicative W)
    (hπe : ∀ (g : G) (x : ↥(Xof G)), π (MulAut.conjNormal g x) =
      Multiplicative.ofAdd (φ (QuotientGroup.mk g) (Multiplicative.toAdd (π x))))
    (ι : (G ⧸ Wker G) ≃* A) (ρ : A →* (W ≃ₗ[ZMod 2] W))
    (hρι : ∀ γ, ρ (ι γ) = φ γ) (η₁ : A →* Equiv.Perm (Fin 5))
    (f : CFSG.Quasithin.G6.coreMod 5 ≃* Multiplicative W)
    (hf : ∀ (g : A) (x : CFSG.Quasithin.G6.coreMod 5),
      f (CFSG.Quasithin.G6.coreAct 5 (η₁ g) x) =
        Multiplicative.ofAdd (ρ g (Multiplicative.toAdd (f x))))
    (η : G →* Equiv.Perm (Fin 5))
    (hη : ∀ g, η g = η₁ (ι (QuotientGroup.mk' (Wker G) g)))
    (ψ : ↥(Xof G) →* ↥(CFSG.Quasithin.G6.coreMod 5))
    (hψ : ∀ x, ψ x = f.symm (π x)) :
    ∀ (g : G) (x : ↥(Xof G)),
      ψ (MulAut.conjNormal g x) = CFSG.Quasithin.G6.coreAct 5 (η g) (ψ x) := by
  intro g x
  apply f.injective
  rw [hψ (MulAut.conjNormal g x), hψ x, hη]
  rw [show f (f.symm (π (MulAut.conjNormal g x))) = π (MulAut.conjNormal g x) from
    f.apply_symm_apply (π (MulAut.conjNormal g x))]
  rw [hπe g x, hf]
  rw [show f (f.symm (π x)) = π x from f.apply_symm_apply (π x)]
  rw [hρι]
  rfl

theorem n2_xDelta5 (hSymp : SympData) (c : Ctx45 p G D)
    (hker : Wker G = CFSG.pPrimeCore 3 G) : XDelta5 G := by
  obtain ⟨W, hWadd, hWmod, hWfin, φ, π, hW, hφ, hπs, hπk, hπe, h0, hd⟩ :=
    r24_module hSymp c hker
  letI := hWadd
  letI := hWmod
  letI := hWfin
  let ι : (G ⧸ Wker G) ≃* ↥(alternatingGroup (Fin 5)) := n2_quotient_alt5_equiv c hker
  let ρ : ↥(alternatingGroup (Fin 5)) →* (W ≃ₗ[ZMod 2] W) := φ.comp ι.symm.toMonoidHom
  have hρι : ∀ γ, ρ (ι γ) = φ γ := fun γ => by simp [ρ]
  have hρ : Function.Injective ρ := hφ.comp ι.symm.injective
  have h0' : ∀ w : W, (∀ g, ρ g w = w) → w = 0 := by
    intro w hw
    exact h0 w fun γ => by
      have h := hw (ι γ)
      rwa [hρι γ] at h
  have hd' : ∀ g : ↥(alternatingGroup (Fin 5)), orderOf g = 3 →
      Nat.card {w : W // ρ g w = w} = 4 := by
    intro g hg
    have hg' : orderOf (ι.symm g) = 3 := (MulEquiv.orderOf_eq ι.symm g).trans hg
    have h := hd (ι.symm g) hg'
    simpa [show ρ g = φ (ι.symm g) from rfl] using h
  obtain ⟨η₁, f, hη₁, hη₁r, hf⟩ := a5_module_iso W ρ hρ hW h0' hd'
  let η : G →* Equiv.Perm (Fin 5) :=
    η₁.comp (ι.toMonoidHom.comp (QuotientGroup.mk' (Wker G)))
  let ψ : ↥(Xof G) →* ↥(CFSG.Quasithin.G6.coreMod 5) := f.symm.toMonoidHom.comp π
  have hη_apply : ∀ g, η g = η₁ (ι (QuotientGroup.mk' (Wker G) g)) := fun _ => rfl
  have hψ_apply : ∀ x, ψ x = f.symm (π x) := fun _ => rfl
  refine ⟨η, ψ, ?_, ?_, ?_, ?_, ?_⟩
  · exact (n2_eta_kernel η₁ hη₁ ι).trans hker
  · exact (n2_eta_range η₁ ι).trans hη₁r
  · exact n2_psi_surjective f π hπs
  · exact (n2_psi_kernel f π).trans hπk
  · exact n2_psi_equivariant φ π hπe ι ρ hρι η₁ f hf η hη_apply ψ hψ_apply

end CFSG.LocalAnalysis.UniquenessCase.UCK.UC46
