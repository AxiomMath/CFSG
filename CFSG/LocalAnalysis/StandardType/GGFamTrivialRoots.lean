module

public import CFSG.HardMathSupport.Timmesfeld.Steinberg.KernelComponentSizes
public import CFSG.LocalAnalysis.StandardType.GGFamRatComp
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Timmesfeld.Steinberg
open CFSG.HardMathSupport.Timmesfeld.LangTorus

@[expose] def famTrivial_certE6 : ComponentCert where
  lab := List.replicate 72 0
  mid :=
    [0, 11, 0, 2, 11, 23, 0, 0, 11, 2, 0, 0, 2, 2, 11, 11, 23, 0, 0, 2, 0, 2, 0, 0, 2, 2, 11, 0,
     0, 0, 0, 2, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0,
     2, 0, 2, 0, 0, 2, 0, 2, 2, 11, 11, 20, 20]

theorem famTrivial_certE6_check : famTrivial_certE6.check .E6 (fun _ => true) = true := by
  decide +kernel

theorem famTrivial_certE6_sizes : famTrivial_certE6.sizes .E6 (fun _ => true) = [72] := by
  decide +kernel

@[expose] def famTrivial_certE7 : ComponentCert where
  lab := List.replicate 126 0
  mid :=
    [0, 12, 0, 2, 12, 26, 40, 0, 0, 12, 2, 0, 0, 2, 2, 12, 12, 26, 26, 40, 0, 0, 2, 0, 2, 0, 0, 2,
     2, 12, 12, 26, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 2, 12, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0,
     0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0,
     2, 2, 0, 0, 0, 2, 2, 0, 12, 2, 0, 0, 12, 2, 0, 23, 12, 2, 23, 12, 2, 23, 12, 23, 12, 23, 23,
     23, 23, 12, 12, 2, 2, 0, 0, 0, 0]

theorem famTrivial_certE7_check : famTrivial_certE7.check .E7 (fun _ => true) = true := by
  decide +kernel

theorem famTrivial_certE7_sizes : famTrivial_certE7.sizes .E7 (fun _ => true) = [126] := by
  decide +kernel

@[expose] def famTrivial_certE8 : ComponentCert where
  lab := List.replicate 240 0
  mid :=
    [0, 13, 0, 2, 13, 29, 45, 61, 0, 0, 13, 2, 0, 0, 2, 2, 13, 13, 29, 29, 45, 45, 61, 0, 0, 2, 0,
     2, 0, 0, 2, 2, 13, 13, 29, 29, 45, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 2, 13, 13, 29, 0, 0, 0, 0,
     0, 2, 0, 0, 2, 0, 0, 2, 2, 13, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0,
     0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0,
     0, 2, 2, 0, 0, 13, 2, 2, 0, 0, 0, 0, 0, 13, 2, 2, 0, 0, 26, 13, 2, 2, 0, 0, 0, 26, 13, 2, 2,
     0, 26, 13, 13, 2, 0, 0, 26, 13, 13, 2, 0, 26, 26, 26, 13, 2, 26, 26, 26, 13, 2, 13, 26, 26,
     13, 13, 26, 26, 13, 2, 13, 26, 26, 2, 13, 26, 26, 0, 2, 13, 26, 0, 2, 13, 26, 0, 0, 2, 13, 0,
     0, 2, 13, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2,
     2, 2, 13, 13, 29, 29, 45, 45, 61, 61, 77, 77]

theorem famTrivial_certE8_check : famTrivial_certE8.check .E8 (fun _ => true) = true := by
  decide +kernel

theorem famTrivial_certE8_sizes : famTrivial_certE8.sizes .E8 (fun _ => true) = [240] := by
  decide +kernel

theorem famTrivial_subsingleton_of_trivial {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {M : Type*} [CommGroup M] (χ : Multiplicative (Fin τ.rank → ℤ) →* M)
    (hχ : ∀ γ : Fin τ.rank → ℤ, χ (Multiplicative.ofAdd γ) = 1) :
    Subsingleton (KernelComponent χ) := by
  rcases hτ with rfl | rfl | rfl
  · exact KernelSizes.subsingleton
      ((ComponentCert.kernelSizes_of_check (S := famTrivial_certE6) (inS := fun _ => true)
        (fun k _ => ⟨fun _ => hχ _, fun _ => rfl⟩) famTrivial_certE6_check).of_perm
        (by rw [famTrivial_certE6_sizes]))
  · exact KernelSizes.subsingleton
      ((ComponentCert.kernelSizes_of_check (S := famTrivial_certE7) (inS := fun _ => true)
        (fun k _ => ⟨fun _ => hχ _, fun _ => rfl⟩) famTrivial_certE7_check).of_perm
        (by rw [famTrivial_certE7_sizes]))
  · exact KernelSizes.subsingleton
      ((ComponentCert.kernelSizes_of_check (S := famTrivial_certE8) (inS := fun _ => true)
        (fun k _ => ⟨fun _ => hχ _, fun _ => rfl⟩) famTrivial_certE8_check).of_perm
        (by rw [famTrivial_certE8_sizes]))

theorem famTrivial_componentRoots_eq_univ {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {M : Type*} [CommGroup M] (χ : Multiplicative (Fin τ.rank → ℤ) →* M)
    (hχ : ∀ γ : Fin τ.rank → ℤ, χ (Multiplicative.ofAdd γ) = 1)
    (i : KernelComponent χ) :
    componentRoots χ i = {γ : Fin τ.rank → ℤ | IsRoot τ γ} := by
  haveI := famTrivial_subsingleton_of_trivial hτ χ hχ
  ext γ
  constructor
  · rintro ⟨hγ, -⟩
    exact hγ.1
  · intro hγ
    exact ⟨⟨hγ, hχ γ⟩, Subsingleton.elim _ _⟩

theorem famTrivial_image_roots_eq {τ : Tag} (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (hρ : ∀ γ : Fin τ.rank → ℤ, IsRoot τ (ρ γ) ↔ IsRoot τ γ) :
    (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) '' {γ | IsRoot τ γ} = {γ | IsRoot τ γ} := by
  ext γ
  constructor
  · rintro ⟨δ, hδ, rfl⟩
    exact (hρ δ).2 hδ
  · intro hγ
    exact ⟨ρ.symm γ, (hρ (ρ.symm γ)).1 (by simpa using hγ), by simp⟩

theorem famTrivial_componentOrbitLength_eq_one {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (hρ : ∀ γ : Fin τ.rank → ℤ, IsRoot τ (ρ γ) ↔ IsRoot τ γ)
    {M : Type*} [CommGroup M] (χ : Multiplicative (Fin τ.rank → ℤ) →* M)
    (hχ : ∀ γ : Fin τ.rank → ℤ, χ (Multiplicative.ofAdd γ) = 1)
    (i : KernelComponent χ) :
    componentOrbitLength ρ (componentRoots χ i) = 1 := by
  have hstab : (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) '' componentRoots χ i =
      componentRoots χ i := by
    rw [famTrivial_componentRoots_eq_univ hτ χ hχ i, famTrivial_image_roots_eq ρ hρ]
  have hle : componentOrbitLength ρ (componentRoots χ i) ≤ 1 :=
    Nat.sInf_le ⟨Nat.one_pos, by simpa using hstab⟩
  have hne : {s : ℕ | 0 < s ∧ (ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots χ i =
      componentRoots χ i}.Nonempty := ⟨1, Nat.one_pos, by simpa using hstab⟩
  have hpos : 0 < componentOrbitLength ρ (componentRoots χ i) := by
    simpa [componentOrbitLength] using (Nat.sInf_mem hne).1
  omega

end CFSG.StandardType.TableCRes

end
