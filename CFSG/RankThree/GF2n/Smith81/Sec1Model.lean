module

public import CFSG.RankThree.GF2n.Stroth80.GlobalModelData

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

namespace GM

variable {M Q Z : Subgroup G} {K : Type} [Field K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem γ_inv (h : GlobalModelData M Q Z γ M₀) {a : G} (ha : a ∈ Z) : γ a⁻¹ = - γ a := by
  have := h.reg.add a ha a⁻¹ (Z.inv_mem ha)
  rw [mul_inv_cancel, h.reg.one] at this
  exact eq_neg_of_add_eq_zero_right this.symm

theorem eq_of_γ_eq (h : GlobalModelData M Q Z γ M₀) {a b : G} (ha : a ∈ Z) (hb : b ∈ Z)
    (hab : γ a = γ b) : a = b := by
  have h1 : γ (a * b⁻¹) = 0 := by
    rw [h.reg.add a ha b⁻¹ (Z.inv_mem hb), γ_inv h hb, hab]
    ring
  exact mul_inv_eq_one.mp (h.reg.inj _ (Z.mul_mem ha (Z.inv_mem hb)) h1)

theorem comm_eq_one_iff (h : GlobalModelData M Q Z γ M₀) {x y : G} (hx : x ∈ Q) (hy : y ∈ Q) :
    ⁅x, y⁆ = 1 ↔ M₀.B (M₀.π x) (M₀.π y) = 0 := by
  rw [commutatorElement_eq_one_iff_mul_comm]
  exact Tim79.QuadModel.comm_iff_B M₀ h.reg hx hy

theorem sq_eq_one_iff (h : GlobalModelData M Q Z γ M₀) {x : G} (hx : x ∈ Q) :
    x ^ 2 = 1 ↔ M₀.Qf (M₀.π x) = 0 :=
  Tim79.QuadModel.sq_iff_Qf M₀ h.reg hx

theorem exists_comm (h : GlobalModelData M Q Z γ M₀) {c : G} (hc : c ∈ Q) (hcZ : c ∉ Z) {z : G}
    (hz : z ∈ Z) : ∃ q ∈ Q, ⁅c, q⁆ = z := by
  have hπ : M₀.π c ≠ 0 := fun h0 => hcZ ((M₀.π_ker c hc).mp h0)
  obtain ⟨f, hf⟩ : ∃ f, M₀.B (M₀.π c) f ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hπ (M₀.nondeg _ hcon)
  obtain ⟨q, hq, hπq⟩ := M₀.π_surj ((γ z / M₀.B (M₀.π c) f) • f)
  refine ⟨q, hq, eq_of_γ_eq h (M₀.comm_mem c hc q hq) hz ?_⟩
  rw [M₀.comm_eq c hc q hq, hπq, map_smul, smul_eq_mul]
  field_simp

end GM

end CFSG.RankThree.GF2n.Smith81
