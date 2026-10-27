module

public import CFSG.RankThree.GF2n.Stroth80.Sec11CM
import CFSG.RankThree.GF2n.Stroth80.Sec118CommBridge
import CFSG.RankThree.GF2n.Stroth80.Sec83Card

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank Module
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

private theorem Ctx.le_centralizer_commXbarPre (hc : Ctx M Q Z B) {X₁ : Subgroup G}
    (hX₁Q : X₁ ≤ Q) (hX₁ : ⁅X₁, XbarPre M Q Z B⁆ ≤ Z) :
    X₁ ≤ Subgroup.centralizer ((⁅Q, XbarPre M Q Z B⁆ : Subgroup G) : Set G) := by
  have hZQ : ⁅Z, Q⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, hc.hyp.hZ, cen_eq]
    exact inf_le_right
  have hZX : ⁅Z, XbarPre M Q Z B⁆ = ⊥ := by
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact (XbarPre_le_H0 hc).trans inf_le_right
  have hX₁Q' : ⁅X₁, Q⁆ ≤ Z :=
    Subgroup.commutator_le.mpr fun a ha b hb => hc.hyp.toHyp79.comm_mem_V (hX₁Q ha) hb
  have h3 : ⁅⁅Q, XbarPre M Q Z B⁆, X₁⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate
      (eq_bot_iff.mpr ((Subgroup.commutator_mono
        ((Subgroup.commutator_comm _ _).le.trans hX₁) le_rfl).trans hZQ.le))
      (eq_bot_iff.mpr ((Subgroup.commutator_mono hX₁Q' le_rfl).trans hZX.le))
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm X₁]
  exact h3

theorem Ctx.eq_Z_of_le_commXbarPre (hc : Ctx M Q Z B) {X₁ : Subgroup G} (hZX₁ : Z ≤ X₁)
    (hX₁ : X₁ ≤ Z ⊔ ⁅Q, XbarPre M Q Z B⁆) (hX₁c : ⁅X₁, XbarPre M Q Z B⁆ ≤ Z) : X₁ = Z := by
  refine le_antisymm ?_ hZX₁
  have hX₁Q : X₁ ≤ Q := hX₁.trans (sup_le hc.Z_le_Q (commutator_le_Q hc))
  rw [← hc.commXbarPre_sup_inf_centralizer_eq]
  exact le_inf (hX₁.trans (sup_comm _ _).le) (hc.le_centralizer_commXbarPre hX₁Q hX₁c)

theorem Ctx.finrank_cmComm_eq_of_naturalRep (hc : Ctx M Q Z B) {K : Type} [Field K] [Finite K]
    {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    {d : ℕ} {K' : Type} [Field K'] [Finite K'] (hK' : Nat.card K' = Nat.card Z)
    {X : Subgroup (GL (Fin d) K')}
    (hR : NaturalRep (ι := Fin d) K' X (XbarPre M Q Z B) (Z ⊔ ⁅Q, XbarPre M Q Z B⁆) Z Q) :
    finrank K ↥(cmComm M Q Z B K γ M₀ φ) = d := by
  have : Module.Finite K M₀.E := M₀.fin
  have h1 := card_of_naturalRep hR le_sup_left hK'
  rw [hc.card_sup_commXbarPre_eq hD φ hφπ, Fintype.card_fin] at h1
  have h2 : Nat.card ↥(cmComm M Q Z B K γ M₀ φ) = Nat.card Z ^ d :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  rw [Module.natCard_eq_pow_finrank (K := K) (V := ↥(cmComm M Q Z B K γ M₀ φ)), hD.card] at h2
  have hq : 2 ≤ Nat.card Z := by
    have := hc.hyp.q4
    omega
  exact Nat.pow_right_injective hq h2

end CFSG.RankThree.GF2n.Stroth80
