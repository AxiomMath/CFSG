module

public import CFSG.RankThree.GF2n.Smith81.LinCoord
public import CFSG.RankThree.GF2n.Stroth80.Sec34Trilinear

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] {M Q Z A : Subgroup G}

theorem Ctx.exists_ne_one (hA : Ctx M Q Z A) : ∃ a ∈ A, a ≠ 1 := by
  by_contra hne
  simp only [not_exists, not_and, not_not] at hne
  have hA0 : A = ⊥ := (Subgroup.eq_bot_iff_forall A).mpr hne
  obtain ⟨g, hg⟩ := hA.conj
  apply hA.ne
  rw [hA0]
  symm
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have hmem : g * z * g⁻¹ ∈ A := by
    rw [hg]
    exact ⟨z, hz, by simp [MulAut.conj_apply]⟩
  rw [hA0, Subgroup.mem_bot] at hmem
  have : z = g⁻¹ * (g * z * g⁻¹) * g := by group
  rw [this, hmem]
  group

end CFSG.RankThree.GF2n.Stroth80

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
  {M Q Z A B : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G}

theorem LinSetup.conj_eq_of_le_V₁ (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂)
    (hn : 3 ≤ n) (hA : Ctx M Q Z A) (hAV : A ≤ V₁) {t : G} (ht : t ∈ LB M Q A) :
    conjSubgroup t V₁ = V₁ ∧ conjSubgroup t V₂ = V₂ := by
  have htH : t ∈ H0 M Z := hA.LB_le_H0_cb ht
  rcases linSwapStatement_holds G M Q Z B n V₁ V₂ hc hS hn t htH with h | h
  · exact h
  · exfalso
    obtain ⟨K, _, _, -, φ, -, -, hZV₁, hV₁Q, hZV₂, hV₂Q, hint, -, -, -, -, -⟩ := hS
    obtain ⟨a, haA, ha1⟩ := hA.exists_ne_one
    have hcomm : ⁅t, a⁆ ∈ Z := hA.comm_B_mem_Z ht haA
    have hconj : t * a * t⁻¹ = ⁅t, a⁆ * a := by
      rw [commutatorElement_def]
      group
    have h1 : t * a * t⁻¹ ∈ V₁ := by
      rw [hconj]
      exact V₁.mul_mem (hZV₁ hcomm) (hAV haA)
    have h2 : t * a * t⁻¹ ∈ V₂ := by
      rw [← h.1]
      exact ⟨a, hAV haA, by simp [MulAut.conj_apply]⟩
    have h3 : t * a * t⁻¹ ∈ Z := by
      rw [← hint]
      exact ⟨h1, h2⟩
    have htZ : t ∈ Subgroup.centralizer (Z : Set G) := htH.2
    have hcz : t * a * t⁻¹ * t = t * (t * a * t⁻¹) :=
      Subgroup.mem_centralizer_iff.mp htZ _ h3
    have haeq : a = t * a * t⁻¹ := by
      have : t * a = t * (t * a * t⁻¹) := by
        calc t * a = t * a * t⁻¹ * t := by group
          _ = t * (t * a * t⁻¹) := hcz
      exact mul_left_cancel this
    have haZ : a ∈ Z := haeq ▸ h3
    have hbot : a ∈ Z ⊓ A := ⟨haZ, haA⟩
    rw [hA.inf_eq_bot, Subgroup.mem_bot] at hbot
    exact ha1 hbot

end CFSG.RankThree.GF2n.Smith81
