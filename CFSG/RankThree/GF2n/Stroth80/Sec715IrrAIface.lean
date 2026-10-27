module

public import CFSG.RankThree.GF2n.Stroth80.Sec715LayerForms
public import CFSG.RankThree.GF2n.Stroth80.Sec715LayerPair
public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrALin

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped Matrix commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

@[expose] def IsSymNbr (hc : Ctx M Q Z B) (t : G) (Z0 : Subgroup G) (g : G) : Prop :=
  g ∈ M ∧ conjSubgroup g Z0 ≤ hc.CN t ∧ conjSubgroup g Z0 ≠ Z0 ∧
    Z0 ≤ conjSubgroup g (hc.CN t)

@[expose] def NonOrthNbrsProp {K : Type} [Field K] [Finite K] {γ : G → K}
    (M₀ : Tim79.QuadModel Q Z K γ) (ρ : Mbar M Q →* Multiplicative (AddAut M₀.E))
    (hc : Ctx M Q Z B) (t : G) (Z0 : Subgroup G) : Prop :=
  ∃ g₁ g₂ : G, IsSymNbr hc t Z0 g₁ ∧ IsSymNbr hc t Z0 g₂ ∧
    ∃ v₁ ∈ bar M Q (conjSubgroup g₁ Z0), ∃ v₂ ∈ bar M Q (conjSubgroup g₂ Z0), ∃ e e' : M₀.E,
      M₀.B (S714.dmap ρ v₁ e) (S714.dmap ρ v₂ e') ≠ 0

variable {hc : Ctx M Q Z B} {n : ℕ} {K : Type} [Field K] [Finite K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)} {b : M₀.E}

structure ConfigAData (hS : IsTensorSetup hc n M₀ ρ b) {t : G} (ht : t ∈ LB M Q B)
    {L₃ L₄ : Type} [AddCommGroup L₃] [Module K L₃] [AddCommGroup L₄] [Module K L₄]
    (ρ₃ : ↥(bar M Q (Rt M (LB M Q B) t)) →* (L₃ ≃ₗ[K] L₃))
    (ρ₄ : ↥(bar M Q (Rt M (LB M Q B) t)) →* (L₄ ≃ₗ[K] L₄))
    (eM : wvQ hS t ≃ₗ[K] (Fin 2 → L₃)) (eN : ↥(deltaSub hS t) ≃ₗ[K] (Fin 2 → L₄))
    (μ : L₃ →ₗ[K] L₄ →ₗ[K] ↥(hc.VtSub hS.model t)) (q₃ : QuadraticForm K L₃)
    (q₄ : QuadraticForm K L₄) (φ ψ : Matrix (Fin 2) (Fin 2) K) (κ : K) : Prop where
  finrank₃ : Module.finrank K L₃ = 8
  finrank₄ : Module.finrank K L₄ = 8
  irr₃ : ∀ S : Submodule K L₃, (∀ x, ∀ a ∈ S, ρ₃ x a ∈ S) → S = ⊥ ∨ S = ⊤
  irr₄ : ∀ S : Submodule K L₄, (∀ x, ∀ c ∈ S, ρ₄ x c ∈ S) → S = ⊥ ∨ S = ⊤
  equivM : ∀ x m, eM (wvAct hS ht x m) = fun i => ρ₃ x (eM m i)
  equivN : ∀ x f, eN (deltaAct hS ht x f) = fun i => ρ₄ x (eN f i)
  pair : ∀ (w : ↥(S714.wsub hS t)) (f : ↥(deltaSub hS t)),
    (f : ↥(S714.wsub hS t) →ₗ[K] M₀.E) w =
      ((∑ i, μ (eM (Submodule.Quotient.mk w) i) (eN f i) : ↥(hc.VtSub hS.model t)) : M₀.E)
  μ_equiv : ∀ x a c, μ (ρ₃ x a) (ρ₄ x c) = vAct hS ht x (μ a c)
  μ_ne : μ ≠ 0
  q₃_inv : ∀ x a, q₃ (ρ₃ x a) = q₃ a
  q₃_nd : ∀ a, (∀ a', QuadraticMap.polar q₃ a a' = 0) → a = 0
  q₄_inv : ∀ x c, q₄ (ρ₄ x c) = q₄ c
  q₄_nd : ∀ c, (∀ c', QuadraticMap.polar q₄ c c' = 0) → c = 0
  φ_symm : φ.transpose = φ
  φψ : φ * ψ = 1
  form : ∀ w w' : ↥(S714.wsub hS t), M₀.B (w : M₀.E) (w' : M₀.E) =
    ∑ i, ∑ j, φ i j * QuadraticMap.polar q₃ (eM (Submodule.Quotient.mk w) i)
      (eM (Submodule.Quotient.mk w') j)
  κ_ne : κ ≠ 0
  bN_eq : ∀ f f' : ↥(deltaSub hS t),
    bN hS ht (f : ↥(S714.wsub hS t) →ₗ[K] M₀.E) (f' : ↥(S714.wsub hS t) →ₗ[K] M₀.E) =
      κ * ∑ i, ∑ j, ψ i j * QuadraticMap.polar q₄ (eN f i) (eN f' j)

@[expose] def HasLine (hS : IsTensorSetup hc n M₀ ρ b) (t : G) {L₄ : Type} [AddCommGroup L₄]
    [Module K L₄] (eN : ↥(deltaSub hS t) ≃ₗ[K] (Fin 2 → L₄)) (Z0 : Subgroup G) (g : G)
    (f : Fin 2 → K) (y : L₄) : Prop :=
  ∀ (v : Mbar M Q), v ∈ bar M Q (conjSubgroup g Z0) → ∀ (hvN : v ∈ bar M Q (hc.CN t)),
    ∃ a : K, eN ⟨S714.delta hS t v (S714.mem_bar_H0_of_CN hvN), delta_mem_deltaSub hS hvN⟩ =
      a • pureT f y

@[expose] def HasLineProp (hS : IsTensorSetup hc n M₀ ρ b) (t : G) {L₄ : Type} [AddCommGroup L₄]
    [Module K L₄] (eN : ↥(deltaSub hS t) ≃ₗ[K] (Fin 2 → L₄)) (q₄ : QuadraticForm K L₄)
    (Z0 : Subgroup G) : Prop :=
  ∀ g ∈ M, conjSubgroup g Z0 ≤ hc.CN t → conjSubgroup g Z0 ≠ Z0 →
    ∃ (f : Fin 2 → K) (y : L₄), f ≠ 0 ∧ y ≠ 0 ∧ q₄ y = 0 ∧ HasLine hS t eN Z0 g f y

@[expose] def SameLineOrthProp (hS : IsTensorSetup hc n M₀ ρ b) (t : G) {L₄ : Type}
    [AddCommGroup L₄] [Module K L₄] (eN : ↥(deltaSub hS t) ≃ₗ[K] (Fin 2 → L₄))
    (Z0 : Subgroup G) : Prop :=
  ∀ (g₁ g₂ : G) (f₁ f₂ : Fin 2 → K) (y₁ y₂ : L₄), IsSymNbr hc t Z0 g₁ → IsSymNbr hc t Z0 g₂ →
    f₁ ≠ 0 → f₂ ≠ 0 → y₁ ≠ 0 → y₂ ≠ 0 → HasLine hS t eN Z0 g₁ f₁ y₁ →
    HasLine hS t eN Z0 g₂ f₂ y₂ → det2 f₁ f₂ = 0 →
    ∀ v₁ ∈ bar M Q (conjSubgroup g₁ Z0), ∀ v₂ ∈ bar M Q (conjSubgroup g₂ Z0), ∀ e e' : M₀.E,
      M₀.B (S714.dmap ρ v₁ e) (S714.dmap ρ v₂ e') = 0

@[expose] def RootEltProp (hS : IsTensorSetup hc n M₀ ρ b) (t : G) {L₄ : Type} [AddCommGroup L₄]
    [Module K L₄] (eN : ↥(deltaSub hS t) ≃ₗ[K] (Fin 2 → L₄)) (Z0 : Subgroup G) : Prop :=
  ∀ (g : G) (f : Fin 2 → K) (y : L₄), IsSymNbr hc t Z0 g → f ≠ 0 → y ≠ 0 →
    HasLine hS t eN Z0 g f y → ∀ s : K, ∃ z : G, ∃ hz : z ∈ NormH0 M Z Z0,
      ∀ (x : Mbar M Q) (hx : x ∈ bar M Q (hc.CN t))
        (hzx : QuotientGroup.mk' (Q.subgroupOf M) ⟨z, hz.1.1⟩ * x *
          (QuotientGroup.mk' (Q.subgroupOf M) ⟨z, hz.1.1⟩)⁻¹ ∈ bar M Q (hc.CN t)),
        eN ⟨S714.delta hS t _ (S714.mem_bar_H0_of_CN hzx), delta_mem_deltaSub hS hzx⟩ =
          eN ⟨S714.delta hS t x (S714.mem_bar_H0_of_CN hx), delta_mem_deltaSub hS hx⟩ +
            s • matAct (rootN f)
              (eN ⟨S714.delta hS t x (S714.mem_bar_H0_of_CN hx), delta_mem_deltaSub hS hx⟩)

@[expose] def MatActProp (hS : IsTensorSetup hc n M₀ ρ b) (t : G) {L₄ : Type} [AddCommGroup L₄]
    [Module K L₄] (eN : ↥(deltaSub hS t) ≃ₗ[K] (Fin 2 → L₄)) (Z0 : Subgroup G) : Prop :=
  ∀ (z : G) (hz : z ∈ NormH0 M Z Z0), (∀ r ∈ Rt M (LB M Q B) t, ⁅z, r⁆ ∈ hc.CN t) →
    ∃ A : Matrix (Fin 2) (Fin 2) K,
      ∀ (x : Mbar M Q) (hx : x ∈ bar M Q (hc.CN t))
        (hzx : QuotientGroup.mk' (Q.subgroupOf M) ⟨z, hz.1.1⟩ * x *
          (QuotientGroup.mk' (Q.subgroupOf M) ⟨z, hz.1.1⟩)⁻¹ ∈ bar M Q (hc.CN t)),
        eN ⟨S714.delta hS t _ (S714.mem_bar_H0_of_CN hzx), delta_mem_deltaSub hS hzx⟩ =
          matAct A (eN ⟨S714.delta hS t x (S714.mem_bar_H0_of_CN hx), delta_mem_deltaSub hS hx⟩)

end CFSG.RankThree.GF2n.Stroth80.S715L
