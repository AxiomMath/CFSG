module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Sporadic.He.Setup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

structure C8KCtx (Γ : Type) [Group Γ] [Finite Γ] (B : Subgroup Γ) (d : Γ) : Prop where
  kgroup : IsKGroup Γ
  l3 : IsL3 (Γ ⧸ CFSG.pPrimeCore 3 Γ) 1
  ne_top : B ≠ ⊤
  prod : B ⊔ CFSG.pPrimeCore 3 Γ = ⊤
  q_le : CFSG.pCore 2 Γ ≤ B
  d_order : orderOf d = 3
  d_cent : centralizer ({d} : Set Γ) ≤ B
  rank : ∀ p : ℕ, p.Prime → 3 < p → pRank p (⊤ : Subgroup Γ) ≤ 2

structure C8HatSetup (Γ : Type) [Group Γ] [Finite Γ] (B : Subgroup Γ) (d : Γ) : Prop
    extends C8KCtx Γ B d where
  no2 : CFSG.pCore 2 Γ = ⊥

structure C8HatMod (p : ℕ) {Γ : Type} [Group Γ] [Finite Γ] (d : Γ)
    (ψ : Γ →* GL (Fin 2) (ZMod p)) (Oh Zh : Subgroup Γ)
    (φ : ↥Oh →* Multiplicative (Fin 2 → ZMod p)) : Prop where
  normal : Oh.Normal
  z_normal : Zh.Normal
  z_le : Zh ≤ Oh
  le_core : Oh ≤ CFSG.pCore p Γ
  surj : Function.Surjective φ
  ker : ∀ x : ↥Oh, φ x = 1 ↔ (x : Γ) ∈ Zh
  equivariant : ∀ (γ x : Γ) (hx : x ∈ Oh) (hx' : γ * x * γ⁻¹ ∈ Oh),
    φ ⟨γ * x * γ⁻¹, hx'⟩ = Multiplicative.ofAdd
      (Matrix.mulVec (ψ γ : Matrix (Fin 2) (Fin 2) (ZMod p)) (Multiplicative.toAdd (φ ⟨x, hx⟩)))
  ngen : ∀ H : Subgroup Γ, H ≤ Oh → H ⊔ Zh = Oh → H = Oh
  d_act : ¬ Oh ≤ centralizer ({d} : Set Γ)

structure C8HatNat (Γ : Type) [Group Γ] [Finite Γ] (d : Γ)
    (ρ : Γ →* ↥(StatedSL 2 (ZMod 7))) (Oh Zh : Subgroup Γ) : Prop where
  surj : Function.Surjective ρ
  ker_le : ρ.ker ≤ CFSG.pPrimeCore 3 Γ
  cent : ∀ n ∈ ρ.ker, ¬ 7 ∣ orderOf n → n ∈ centralizer (CFSG.pCore 7 Γ : Set Γ)
  normal : Oh.Normal
  z_normal : Zh.Normal
  z_le : Zh ≤ Oh
  le_core : Oh ≤ CFSG.pCore 7 Γ
  o_le_ker : Oh ≤ ρ.ker
  index : Zh.relIndex Oh = 49
  comm : ∀ x ∈ Oh, ∀ y ∈ Oh, x * y * x⁻¹ * y⁻¹ ∈ Zh
  pow : ∀ x ∈ Oh, x ^ 7 ∈ Zh
  ngen : ∀ H : Subgroup Γ, H ≤ Oh → H ⊔ Zh = Oh → H = Oh
  d_act : ¬ Oh ≤ centralizer ({d} : Set Γ)
  act_one : ∀ γ : Γ, ρ γ = 1 ↔ ∀ x ∈ Oh, γ * x * γ⁻¹ * x⁻¹ ∈ Zh
  inv : ∀ γ : Γ, ρ γ ≠ 1 → ρ γ ^ 2 = 1 → ∀ x ∈ Oh, γ * x * γ⁻¹ * x ∈ Zh
  irred : ∀ W : Subgroup Γ, Zh ≤ W → W ≤ Oh → (∀ γ : Γ, ∀ w ∈ W, γ * w * γ⁻¹ ∈ W) →
    W = Zh ∨ W = Oh

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
