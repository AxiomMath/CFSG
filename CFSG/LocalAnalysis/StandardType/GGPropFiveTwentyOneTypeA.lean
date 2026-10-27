module

public import CFSG.LocalAnalysis.StandardType.GGPropFiveTwentyOneDefs
public import CFSG.LocalAnalysis.StandardType.GGPropFiveTwentyOneLevi

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.Assembly.LowTwoRank SpecialLinear

theorem statedLieAdmissible_PSL {m f : ℕ} (hm : 2 ≤ m) (hf : 1 ≤ f) :
    StatedLieAdmissible .PSL (m + 1) 2 f :=
  ⟨Nat.prime_two, hf, by omega, fun h => by simp at h; omega, fun h => by simp at h; omega⟩

variable {G : Type} [Group G] [Finite G]

@[expose] def GGSecFiveTypeA (p : ℕ) (B : Subgroup G) (x : G) (L D J : Subgroup G)
    (m k f : ℕ) : Prop :=
  ∃ (φ : ggSub (rootDatum m (GaloisField 2 f)) (ggSupp (rootDatum m (GaloisField 2 f))
      (typeALeviJ m k)) →* G) (ρ : (coxeterMatrix (isFiniteType_A m)).Group →* G),
    Function.Injective ρ ∧
    (∀ j ∈ typeALeviJ m k, ggExt φ (weylRep m (GaloisField 2 f) j) =
      ρ ((coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple j)) ∧
    (∀ (w : (coxeterMatrix (isFiniteType_A m)).Group),
      ∀ α ∈ ggSupp (rootDatum m (GaloisField 2 f)) (typeALeviJ m k),
        weylAction (isFiniteType_A m) w α = α → ∀ z ∈ rootGroup m (GaloisField 2 f) α,
          ρ w * ggExt φ z * (ρ w)⁻¹ = ggExt φ z) ∧
    (∃ γ ∈ ggSupp (rootDatum m (GaloisField 2 f)) (typeALeviJ m k),
      ∃ z ∈ rootGroup m (GaloisField 2 f) γ, ggExt φ z ≠ 1) ∧
    φ.range ≤ ggG0 p B x L D J ∧ ρ.range ≤ ggG0 p B x L D J ∧
    L ≤ ggClosure (rootDatum m (GaloisField 2 f))
      (fun _ : Unit => ggSupp (rootDatum m (GaloisField 2 f)) (typeALeviJ m k)) (fun _ => φ)
        ρ.range ∧
    ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      K ≤ ggClosure (rootDatum m (GaloisField 2 f))
        (fun _ : Unit => ggSupp (rootDatum m (GaloisField 2 f)) (typeALeviJ m k)) (fun _ => φ)
          ρ.range

theorem ggPresentsG0_of_typeA {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G} {m k f : ℕ}
    (hk : 4 ≤ k) (hkm : k ≤ m) (hf : 1 ≤ f) (h : GGSecFiveTypeA p B x L D J m k f) :
    ∃ ψ : (ggU .PSL (m + 1) f).K →* G,
      GGPresentsG0 (ggG0 p B x L D J) (ggU .PSL (m + 1) f).D .PSL (m + 1) f ψ := by
  obtain ⟨φ, ρ, hρ, hspecial, hcent, hnt, hφG, hρG, hL, hK⟩ := h
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨ψ, -, -, -, hrange, hker, hq, hmodel⟩ := ggPresentation_typeALevi hk hkm hF hf φ
    (R := ρ.range) (δ := (MonoidHom.ofInjective hρ).symm.toMonoidHom)
    (MonoidHom.ofInjective hρ).symm.surjective
    (fun j hj => ⟨MonoidHom.ofInjective hρ
      ((coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple j),
      by rw [MonoidHom.ofInjective_apply hρ, hspecial j hj],
      (MonoidHom.ofInjective hρ).symm_apply_apply _⟩)
    (fun r => forall_range_ofInjective hρ (P := fun g w =>
      ∀ α ∈ ggSupp (rootDatum m (GaloisField 2 f)) (typeALeviJ m k),
        weylAction (isFiniteType_A m) w α = α → ∀ z ∈ rootGroup m (GaloisField 2 f) α,
          g * ggExt φ z * g⁻¹ = ggExt φ z) hcent r)
    hnt
  have hcl := ggClosure_eq_ggG0 (fun _ : Unit => hφG) hρG hL hK
  rw [hcl] at hrange hq hmodel
  exact ⟨ψ, ⟨statedLieAdmissible_PSL (by omega) hf, by change 2 ≤ m; omega⟩, ⟨hrange, hker⟩,
    Group.isPerfect_def.mp hq.1, hmodel⟩

end CFSG.StandardType
