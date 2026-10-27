module

public import CFSG.RankThree.GF2n.Stroth80.Sec7IsometryFixed
public import CFSG.RankThree.GF2n.Stroth80.Sec7Om4PsiCore

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec7_op_data [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ} {K : Type} [Field K]
    [Finite K] {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ)
    (ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)) (b₀ : M₀.E)
    (hS : IsTensorSetup hc n M₀ ρ b₀) {x : G} (hxH : x ∈ H0 M Z) (hx2 : x ^ 2 ∈ Q) :
    ∃ T : M₀.E ≃ₗ[K] M₀.E,
      (∀ e, T e = (ρ (QuotientGroup.mk (⟨x, hxH.1⟩ : ↥M))).toAdd e) ∧ (∀ e, T (T e) = e) ∧
      (∀ e e', M₀.B (T e) (T e') = M₀.B e e') ∧
      (∀ e, e ∈ LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1) ↔ e ∈ M₀.img (Ut Q Z x)) ∧
      LinearMap.ker ((T : M₀.E →ₗ[K] M₀.E) - 1) =
        M₀.B.orthogonal (LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1)) ∧
      (∀ y ∈ Q, M₀.π ⁅x, y⁆ = T (M₀.π y) - M₀.π y) := by
  classical
  haveI : Finite M₀.E := Module.finite_of_finite K
  have hxM : x ∈ M := hxH.1
  have hxbar : (QuotientGroup.mk (⟨x, hxM⟩ : ↥M) : Mbar M Q) ∈ bar M Q (H0 M Z) :=
    Subgroup.mem_map.mpr ⟨⟨x, hxM⟩, Subgroup.mem_subgroupOf.mpr hxH, rfl⟩
  let T : M₀.E ≃ₗ[K] M₀.E :=
    AddEquiv.toLinearEquiv (ρ (QuotientGroup.mk (⟨x, hxM⟩ : ↥M))).toAdd (hS.lin _ hxbar)
  have hT : ∀ y ∈ Q, M₀.π (x * y * x⁻¹) = T (M₀.π y) := fun y hy => hS.conj ⟨x, hxM⟩ y hy
  have hiso : ∀ e e', M₀.B (T e) (T e') = M₀.B e e' := hS.iso _ hxbar
  have hQn : ∀ m ∈ M, ∀ y ∈ Q, m * y * m⁻¹ ∈ Q := fun m hm y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hm) y).mp hy
  have ha : ∀ y ∈ Q, x * y * x⁻¹ ∈ Q := hQn x hxM
  have ha' : ∀ y ∈ Q, x⁻¹ * y * x ∈ Q := fun y hy => by
    have := hQn x⁻¹ (M.inv_mem hxM) y hy
    simpa using this
  obtain ⟨hf, hr⟩ := sec7_model_form M₀
  refine ⟨T, fun e => rfl, ?_, hiso, ?_, ?_, ?_⟩
  · intro e
    have h1 : (QuotientGroup.mk (⟨x, hxM⟩ : ↥M) : Mbar M Q) *
        QuotientGroup.mk (⟨x, hxM⟩ : ↥M) = 1 := by
      rw [← QuotientGroup.mk_mul]
      refine (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr ?_)
      simpa [pow_two] using hx2
    show (ρ (QuotientGroup.mk (⟨x, hxM⟩ : ↥M))).toAdd
      ((ρ (QuotientGroup.mk (⟨x, hxM⟩ : ↥M))).toAdd e) = e
    rw [← act_mul_apply ρ, h1, map_one]
    rfl
  · exact fun e => mem_img_comm_zpowers_sup_iff M₀ hS.model.reg T ha ha' hT e |>.symm
  · exact sec7_ker_sub_one_eq_perp_range M₀.B hf hr T hiso
  · intro y hy
    have hxy : x * y * x⁻¹ ∈ Q := ha y hy
    have e : ⁅x, y⁆ = (x * y * x⁻¹) * y⁻¹ := rfl
    rw [e, M₀.π_mul _ hxy _ (Q.inv_mem hy), M₀.pi_inv hy, hT y hy, sub_eq_add_neg]

end CFSG.RankThree.GF2n.Stroth80
