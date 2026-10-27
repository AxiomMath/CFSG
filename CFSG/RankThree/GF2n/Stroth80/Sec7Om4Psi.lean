module

public import CFSG.RankThree.GF2n.Stroth80.Sec7LinA0
public import CFSG.RankThree.GF2n.Stroth80.Sec7ConjMem
public import CFSG.RankThree.GF2n.Stroth80.Sec7Om4Base

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


@[expose] def Stroth73aOm4PsiCoreStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t → OmegaMinusNat hc t 2 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ (ht : t ∈ LB M Q B) (K : Type) [Field K] [Finite K] (γ : G → K)
      (M₀ : Tim79.QuadModel Q Z K γ)
      (ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)) (b : M₀.E)
      (hS : IsTensorSetup hc n M₀ ρ b) (ψ : M₀.E →ₗ[K] M₀.E),
      (∀ e, ψ e = (ρ (QuotientGroup.mk (⟨t, hc.LB_le_M ht⟩ : ↥M))).toAdd e - e) →
      (∀ e, e ∈ LinearMap.range ψ ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t)) →
      (∀ x ∈ Q, x ∈ Wt Q (Vt M (LB M Q B) B Z t) ↔ ψ (M₀.π x) = 0) →
      (∀ a a' : Mbar M Q, (∀ e, (ρ a).toAdd e = (ρ a').toAdd e) → a = a') →
      (∀ a ∈ bar M Q Z0, ∃ c : K, ∀ e, (ρ a).toAdd e = e + c • ψ e) →
      (∀ c : K, ∃ a ∈ bar M Q Z0, ∀ e, (ρ a).toAdd e = e + c • ψ e) →
      ∀ (m : G) (hm : m ∈ M), m ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) →
        ∃ μ : K, μ ≠ 0 ∧ ∀ e, ψ e = μ • (ρ (QuotientGroup.mk (⟨m, hm⟩ : ↥M))).toAdd
          (ψ ((ρ (QuotientGroup.mk (⟨m, hm⟩ : ↥M))).toAdd.symm e))

theorem stroth73aOm4Base_of_psi (h34 : Stroth34Statement) (h310chi : Stroth310ChiStatement)
    (hZc : Sec7CentreMpStatement) (hZV : Sec7ZVStatement) (hZcard : Sec7ZCardStatement)
    (hCore : Stroth73aOm4PsiCoreStatement) : Stroth73aOm4BaseStatement := by
  intro G _ _ M Q Z B hc n t hs hno hom Z0 hZ0 m hm hmV
  haveI := hc.normal_Q_in_M
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  obtain ⟨K, fK, finK, γ, M₀, ρ, b, hS, ψ, hψ, hrange, hW, hinj, hA5, hA6⟩ :=
    sec7_A0 h34 h310chi hZc hZV hZcard hc hs hZ0
  obtain ⟨μ, hμ, hprop⟩ := hCore G M Q Z B hc n t hs hno hom Z0 hZ0 ht K γ M₀ ρ b hS ψ hψ
    hrange hW hinj hA5 hA6 m hm hmV
  exact sec7_conj_mem_of_proportional M₀ ρ (hc.Q_le_centre ht hZ0) (hc.LB_le_M ht) hm ψ hψ
    hinj hA6 μ hμ hprop

end CFSG.RankThree.GF2n.Stroth80
