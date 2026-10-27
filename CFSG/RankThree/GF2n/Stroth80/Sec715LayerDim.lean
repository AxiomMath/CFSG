module

public import CFSG.RankThree.GF2n.Stroth80.Sec715LayerForms

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.GF2n.Stroth80.S714
open CFSG.ClassicalInvolution.Upgrade (map_statedOmega statedQuadPlus_comp glCongr_mulVec)
open CFSG.Adapters.RankTwoModelTransports (glCongr)
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {hc : Ctx M Q Z B} {n : ℕ} {K : Type} [Field K] [Finite K]
  {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)}
  {b : M₀.E}

theorem exists_phi8 (hS : IsTensorSetup hc n M₀ ρ b) {t : G} (ht : t ∈ LB M Q B)
    (hp : OmegaPlusNat hc t 4) :
    ∃ (φ₈ : ↥(bar M Q (Rt M (LB M Q B) t)) →* GL (Fin 4 ⊕ Fin 4) K)
      (e : ↥(hc.VtSub hS.model t) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)),
      φ₈.range = StatedOmega (StatedQuadPlus 4 K) ∧
      (∀ x, φ₈ x = 1 ↔ (x : Mbar M Q) ∈ bar M Q (hc.CN t)) ∧
      ∀ (x : ↥(bar M Q (Rt M (LB M Q B) t))) (w : ↥(hc.VtSub hS.model t)),
        e ⟨(ρ (x : Mbar M Q)).toAdd w, hc.act_mem_VtSub hS ht x x.2 w w.2⟩ =
          (φ₈ x : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ e w := by
  obtain ⟨K', hF', hFin', hcard, hnat⟩ := hp
  obtain ⟨θ, Ψ, π, hπr, hπk, hΨc, hΨx⟩ := hc.natural_transport hS ht hcard
    (addCommutantScalar_statedOmegaPlus (by norm_num)) hnat
  let e₀ : ↥(hc.VtSub hS.model t) ≃+ (Fin 4 ⊕ Fin 4 → K) :=
    Ψ.trans (AddEquiv.piCongrRight fun _ => θ.symm.toAddEquiv)
  have he₀ : ∀ w, e₀ w = θ.symm ∘ Ψ w := fun w => rfl
  let e : ↥(hc.VtSub hS.model t) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K) :=
    e₀.toLinearEquiv fun c w => by
      rw [he₀, he₀, hΨc]
      funext i
      simp
  refine ⟨(glCongr θ.symm).toMonoidHom.comp π, e, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, hπr]
    exact map_statedOmega θ.symm (statedQuadPlus_comp θ.symm)
  · intro x
    rw [← hπk x]
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
    exact (glCongr θ.symm).map_eq_one_iff
  · intro x w
    show e₀ _ = _ *ᵥ e₀ w
    rw [he₀, he₀, hΨx]
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
    exact (glCongr_mulVec θ.symm (π x) (Ψ w)).symm

theorem finrank_vtSub (hS : IsTensorSetup hc n M₀ ρ b) {t : G} (ht : t ∈ LB M Q B)
    (hp : OmegaPlusNat hc t 4) : Module.finrank K ↥(hc.VtSub hS.model t) = 8 := by
  obtain ⟨-, e, -⟩ := exists_phi8 hS ht hp
  rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]

theorem finrank_wsub (hS : IsTensorSetup hc n M₀ ρ b) {t : G} (ht : t ∈ LB M Q B)
    (hp : OmegaPlusNat hc t 4) (hn : n = 16) : Module.finrank K ↥(wsub hS t) = 24 := by
  haveI : Module.Finite K M₀.E := M₀.fin
  rw [wsub_eq_orthogonal hS t, LinearMap.BilinForm.finrank_orthogonal
    (bilin_nondegenerate_isRefl (M₀ := M₀)).1, hS.dim, finrank_vtSub hS ht hp, hn]

end CFSG.RankThree.GF2n.Stroth80.S715L
