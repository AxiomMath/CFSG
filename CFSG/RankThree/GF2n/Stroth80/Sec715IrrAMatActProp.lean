module

public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrAMatAct
public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrAIface

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank S714
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {hc : Ctx M Q Z B} {n : ℕ} {K : Type} [Field K] [Finite K]
  {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)}
  {b : M₀.E}

theorem matActProp_of (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
    (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement) (hS : IsTensorSetup hc n M₀ ρ b)
    {n' : ℕ} {t r : G} (hs : Sec7Hyp hc n' t) (hr : Sec7A hc t r) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hSΔ : ∀ f ∈ deltaSub hS t, ∃ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)),
      f = delta hS t g (mem_bar_H0_of_CN hg))
    {L₃ L₄ : Type} [AddCommGroup L₃] [Module K L₃] [AddCommGroup L₄] [Module K L₄]
    {ρ₃ : ↥(bar M Q (Rt M (LB M Q B) t)) →* (L₃ ≃ₗ[K] L₃)}
    {ρ₄ : ↥(bar M Q (Rt M (LB M Q B) t)) →* (L₄ ≃ₗ[K] L₄)}
    {eM : wvQ hS t ≃ₗ[K] (Fin 2 → L₃)} {eN : ↥(deltaSub hS t) ≃ₗ[K] (Fin 2 → L₄)}
    {μ : L₃ →ₗ[K] L₄ →ₗ[K] ↥(hc.VtSub hS.model t)} {q₃ : QuadraticForm K L₃}
    {q₄ : QuadraticForm K L₄} {φ ψ : Matrix (Fin 2) (Fin 2) K} {κ : K}
    (hD : ConfigAData hS hs.toSec5.mem ρ₃ ρ₄ eM eN μ q₃ q₄ φ ψ κ)
    (hEnd4 : ∀ T : L₄ →ₗ[K] L₄,
      (∀ x, T ∘ₗ (ρ₄ x : L₄ →ₗ[K] L₄) = (ρ₄ x : L₄ →ₗ[K] L₄) ∘ₗ T) →
        ∃ c : K, T = c • LinearMap.id) :
    MatActProp hS t eN Z0 := by
  intro z hz hzR
  obtain ⟨T, hTΔ, hTeq⟩ := exists_conj_deltaSub h310chi h52a hZt hZcard hS hs hr hZ0 hSΔ hz hzR
  set T' : (Fin 2 → L₄) →ₗ[K] (Fin 2 → L₄) :=
    (eN : ↥(deltaSub hS t) →ₗ[K] (Fin 2 → L₄)) ∘ₗ T ∘ₗ
      (eN.symm : (Fin 2 → L₄) →ₗ[K] ↥(deltaSub hS t)) with hT'
  have hT'app : ∀ f : ↥(deltaSub hS t), T' (eN f) = eN (T f) := fun f => by
    simp only [hT', LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
  have hT'eq : ∀ h x, T' (fun i => ρ₄ h (x i)) = fun i => ρ₄ h (T' x i) := by
    intro h x
    obtain ⟨f, rfl⟩ := eN.surjective x
    rw [← hD.equivN, hT'app, hT'app, hTeq, hD.equivN]
  have hEnd' : ∀ U : L₄ →ₗ[K] L₄, (∀ h y, U (ρ₄ h y) = ρ₄ h (U y)) →
      ∃ c : K, U = c • LinearMap.id := fun U hU =>
    hEnd4 U fun x => LinearMap.ext fun y => by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, hU]
  obtain ⟨A, hA⟩ := exists_eq_matAct_of_commute ρ₄ hEnd' T' hT'eq
  refine ⟨A, fun x hx hzx => ?_⟩
  rw [← hTΔ x hx hzx, ← hT'app, hA]

end CFSG.RankThree.GF2n.Stroth80.S715L
