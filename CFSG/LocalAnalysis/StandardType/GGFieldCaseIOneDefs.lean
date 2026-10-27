module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45RestRank
public import CFSG.LocalAnalysis.StandardType.GGFieldNbr

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGL45TorusIOneInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGL45Config p B Bs x L D J X B₂ d y K U U₁ → Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D →
      ∃ s : ℕ, 2 ≤ s ∧
        (∀ a ∈ U₁, ∀ b ∈ U₁, a * b * a⁻¹ * b⁻¹ ∈ U ⊓ Subgroup.centralizer (K : Set G)) ∧
        (∀ u ∈ U₁, u ^ p ^ s ∈ U ⊓ Subgroup.centralizer (K : Set G)) ∧
        (∃ u ∈ U₁, u ^ p ^ (s - 1) ∉ U ⊓ Subgroup.centralizer (K : Set G)) ∧
        ∃ x' : G, Subgroup.zpowers x' = Subgroup.zpowers x ∧
          ∀ u ∈ U₁, (u ^ (1 + p ^ (s - 1)))⁻¹ * (x'⁻¹ * u * x') ∈
            U ⊓ Subgroup.centralizer (K : Set G)

@[expose] def GGL45CyclicD4IOneInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGL45Config p B Bs x L D J X B₂ d y K U U₁ → Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D →
    p = 3 →
    LargeEvenMarking K (fun lab _ _ I _ θ => lab.tag = .D ∧ lab.rank = 4 ∧
      ∀ u ∈ U, u ∈ U₁ ↔ ∃ φ ∈ I, LargeEvenInduces θ (fun k k' => (k' : G) = u⁻¹ * k * u) φ) →
    ∃ g ∈ U, U ≤ Subgroup.zpowers g ⊔ U₁

@[expose] def GGL46CyclicIOneInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁ →
      Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D → ∃ g ∈ U, U ≤ Subgroup.zpowers g ⊔ U₁

@[expose] def GGL47IOneInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁ →
      Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D → GGL46 p Bs x X U U₁ →
      ∀ R : Subgroup G, IsPGroup p R →
        R ≤ Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) →
        (∀ Q : Subgroup G,
          Q ≤ Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) →
          IsPGroup p Q → R ≤ Q → Q = R) →
        U ≤ R → ∀ A ∈ thompsonAbelianSubgroups R, ⁅⁅U₁, A⁆, A⁆ = ⊥ → A ≤ U

@[expose] def GGL48QuotIOneInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁ →
      Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D → GGL46 p Bs x X U U₁ →
      ∀ R : Subgroup G, IsPGroup p R → (∀ Q : Subgroup G, IsPGroup p Q → R ≤ Q → Q = R) →
        U ≤ R → (∀ A ∈ thompsonAbelianSubgroups R, A = U₁) →
        ∃ ψ : Subgroup.normalizer (U₁ : Set G) →* Multiplicative (ZMod p), ψ ≠ 1

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}

theorem GGL45Config.cent_le_of_iOne (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁)
    (h3 : GGNbrSubcomponentInput) (hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D) :
    Bs ⊓ Subgroup.centralizer (X : Set G) ⊓ Subgroup.centralizer (K : Set G) ≤
      Subgroup.zpowers d := by
  intro b hb
  have hJK : J ≤ K :=
    h3 G p B x L D J hcfg.1.1.1 hcfg.1.1.2.2 y K hcfg.2.2.2.2.2.1.2.2.1
  have hbD : b ∈ D := hI1 ⟨hb.1.1, Subgroup.centralizer_le hJK hb.2⟩
  rw [← hcfg.2.2.2.2.2.1.1]
  exact ⟨hbD, hb.1⟩

theorem GGL45Config.exists_cyclic_of_iOne (h : GGRawPCyclicOn GGNotD4Three)
    (hD4 : GGL45CyclicD4IOneInput) (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁)
    (hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D) :
    ∃ g ∈ U, U ≤ Subgroup.zpowers g ⊔ U₁ := by
  have hp : p.Prime := hcfg.prime
  have hp2 : p ≠ 2 := hcfg.odd
  obtain ⟨-, hUp, -, -⟩ := hcfg.2.2.2.2.2.2.1
  obtain ⟨hUN, -, hmk⟩ := hcfg.2.2.2.2.2.2.2.1
  obtain ⟨hK, lab, hlab, hraw⟩ := hmk
  by_cases hD : lab.tag = .D ∧ lab.rank = 4 ∧ p = 3
  · obtain ⟨ht, hr, hp3⟩ := hD
    refine hD4 G p B Bs x L D J X B₂ d y K U U₁ hcfg hI1 hp3 ⟨hK, lab, hlab, ?_⟩
    refine largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨hs, hna, θ, hθ⟩
    exact ⟨hs, hna, θ, ht, hr, hθ⟩
  · have hraw' := h p hp hp2 lab hlab hD _ hraw
    obtain ⟨R, _, I, F, ⟨hs, hna, θ, hθ⟩, hcyc⟩ := largeEvenRawDatum_exists hraw'
    obtain ⟨J', S, hJ', -, hN, hgen, hpS⟩ := hcyc hs hna
    let ρ : U →* MulAut R := (ggLAut K θ).comp (Subgroup.inclusion hUN)
    have hρ : ∀ u : U, ρ u = ggLAut K θ ⟨u, hUN u.2⟩ := fun _ => rfl
    have hρS : ∀ u : U, ρ u ∈ S := fun u => by
      obtain ⟨k, hk⟩ := hUp u
      exact hpS _ ⟨k, by rw [← map_pow, hk, map_one]⟩
    refine exists_le_zpowers_sup_of_cyclic ρ hN hgen hρS (fun u => ?_)
    · rw [hθ u u.2, hρ]
      constructor
      · rintro ⟨φ, hφ, hind⟩
        rw [eq_ggLAut_of_induces K θ (hUN u.2) hind, ← hJ'] at hφ
        have := J'.inv_mem hφ
        rw [← map_inv] at this
        convert this using 2
        exact Subtype.ext (by simp)
      · intro hmem
        refine ⟨ggLAut K θ ⟨(u : G)⁻¹, inv_mem (hUN u.2)⟩, ?_,
          largeEvenInduces_ggLAut_inv K θ (inv_mem (hUN u.2))⟩
        rw [← hJ']
        have := J'.inv_mem hmem
        rw [← map_inv] at this
        convert this using 2

end Config

theorem ggL46CyclicIOneInput_of_l45 (h : GGRawPCyclicOn GGNotD4Three)
    (hD4 : GGL45CyclicD4IOneInput) : GGL46CyclicIOneInput :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hS hI1 =>
    (ggL45Config_of_setup hS).exists_cyclic_of_iOne h hD4 hI1

end CFSG.StandardType

end
