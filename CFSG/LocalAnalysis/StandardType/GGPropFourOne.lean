module

public import CFSG.LocalAnalysis.StandardType.GGPropFourOneThompson
public import CFSG.LocalAnalysis.StandardType.GGOneFiveInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Defs

variable {G : Type} [Group G] [Finite G]

@[expose] def GGFieldCase (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J X : Subgroup G) : Prop :=
  GGConfig p B Bs x L D J ∧ GGFieldNbrCanonical p B Bs x D J ∧
    X ≤ Subgroup.normalizer (Bs : Set G) ∧ Subgroup.centralizer (Bs : Set G) ≤ X ∧
    (X.subgroupOf (Subgroup.normalizer (Bs : Set G))).Normal ∧
    (∀ g ∈ X, ∃ k : ℕ, g ^ p ^ k ∈ Subgroup.centralizer (Bs : Set G)) ∧
    ¬ X ≤ Subgroup.centralizer (Bs : Set G)

@[expose] def GGFieldCaseData (p : ℕ) (Bs X M R U U₁ : Subgroup G) : Prop :=
  M = Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) ∧
    IsPGroup p R ∧ R ≤ M ∧ (∀ Q : Subgroup G, Q ≤ M → IsPGroup p Q → R ≤ Q → Q = R) ∧
    U ≤ R ∧ R ≤ Subgroup.normalizer (U : Set G) ∧
    U₁ ≤ U ∧ IsMulCommutative U₁ ∧ (∀ A ∈ thompsonAbelianSubgroups U, A = U₁) ∧
    (∀ u : G, u ∈ Bs ⊓ Subgroup.centralizer (X : Set G) ↔ u ∈ U₁ ∧ u ^ p = 1) ∧
    (∀ A ∈ thompsonAbelianSubgroups R, ⁅⁅U₁, A⁆, A⁆ = ⊥ → A ≤ U)

end Defs

@[expose] def GGFieldCaseInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J X : Subgroup G),
    GGFieldCase p B Bs x L D J X →
      ∃ M R U U₁ : Subgroup G, GGFieldCaseData p Bs X M R U U₁ ∧
        ∃ ψ : Subgroup.normalizer (U₁ : Set G) →* Multiplicative (ZMod p), ψ ≠ 1

section Proof

variable {G : Type} [Group G] [Finite G]

theorem ggFieldCaseData_false {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hG : IsSimpleGroup G)
    (hnc : ∃ a b : G, a * b ≠ b * a) {Bs X M R U U₁ : Subgroup G}
    (hdata : GGFieldCaseData p Bs X M R U U₁)
    (ψ : Subgroup.normalizer (U₁ : Set G) →* Multiplicative (ZMod p)) (hψ : ψ ≠ 1) : False := by
  obtain ⟨hM, hRp, -, hmax, hUR, hRU, hU₁U, hU₁ab, hJU, hB₁, hrep⟩ := hdata
  obtain ⟨⟨S, rfl⟩, -, hwc⟩ := ggL47 hRp hmax hUR hRU hU₁U hU₁ab hJU hB₁ hM.ge hrep
  exact not_isSimpleGroup_of_isMulCommutative hp2 S (hU₁U.trans hUR) hwc hU₁ab ψ hψ hnc hG

end Proof

theorem ggProp41Input_of_input (h : GGFieldCaseInput) : GGProp41Input := by
  intro G _ _ p B Bs x L D J hcfg hbl5 X hXN hCX hXn hXp
  by_contra hXC
  obtain ⟨M, R, U, U₁, hdata, ψ, hψ⟩ :=
    h G p B Bs x L D J X ⟨hcfg, hbl5, hXN, hCX, hXn, hXp, hXC⟩
  have hI := hcfg.1
  have hβ := hI.2.2.2.2.2.1
  have : Fact p.Prime := ⟨hβ.1⟩
  exact ggFieldCaseData_false hβ.2.1 hI.1 hI.2.1 hdata ψ hψ

end CFSG.StandardType

end
