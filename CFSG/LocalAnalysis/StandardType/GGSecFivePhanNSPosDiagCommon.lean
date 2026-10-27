module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosRank
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSCornerDefs
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosCommRank
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDiagCommonAux
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDiagCommonAux2
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosLiftE
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCaseLLift
import CFSG.RankThree.PartOne.CTP.SeitzDiag

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {f n : ℕ} {ψ : Su K 2 f n →* G}

private theorem ggNSPosPE_pow_class_trivial (hC : GGSecFiveNSCornerInput) (h : GGNSLocalHyp p B Bs K f n ψ)
    {b : G} (hb : b ∈ Bs) {g : GL (Fin n) K} (hg : GGInducesUnitary (p := 2) (f := f) ψ b g) :
    ∃ c : Kˣ, g ^ p = GeneralLinearGroup.scalar (Fin n) (c ^ p) := by
  obtain ⟨u, hu⟩ := ggNSPosPE_lift_pow_scalar_aux h hb hg
  by_cases hc : ∃ c : Kˣ, u = c ^ p
  · obtain ⟨c, rfl⟩ := hc
    exact ⟨c, hu⟩
  · obtain ⟨E, hE, hE1, hE2, hmem, hcomap⟩ := ggNSPosLE_exists_E h
    have hcomm : ∀ x ∈ E.comap (QuotientGroup.mk' (Subgroup.center (GL (Fin n) K))),
        ∀ y ∈ E.comap (QuotientGroup.mk' (Subgroup.center (GL (Fin n) K))), x * y = y * x := by
      intro x hx y hy
      obtain ⟨b₁, hb₁, g₁, hg₁, c₁, rfl⟩ := hcomap x hx
      obtain ⟨b₂, hb₂, g₂, hg₂, c₂, rfl⟩ := hcomap y hy
      have hlifts : g₁ * g₂ = g₂ * g₁ := ggNSPosPF_mul_comm_of_commutator_eq_one g₁ g₂
        (ggNSPosPF_commutator_eq_one hC h hb₁ hb₂ hg₁ hg₂)
      have hsc : ∀ (c : Kˣ) (z : GL (Fin n) K),
          Commute (GeneralLinearGroup.scalar (Fin n) c) z :=
        fun c z => Matrix.GeneralLinearGroup.scalar_commute c z
      have hsc' : ∀ (c : Kˣ) (z : GL (Fin n) K),
          Commute z (GeneralLinearGroup.scalar (Fin n) c) :=
        fun c z => (Matrix.GeneralLinearGroup.scalar_commute c z).symm
      exact (Commute.mul_right
        (Commute.mul_left (show Commute g₁ g₂ from hlifts) (hsc c₁ g₂))
        (Commute.mul_left (hsc' c₂ g₁) (hsc' c₂ (GeneralLinearGroup.scalar (Fin n) c₁)))).eq
    have hpK : p ∣ Nat.card Kˣ := by
      rw [Nat.card_units, h.card]
      have h1 : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
        simpa using Nat.sq_sub_sq (2 ^ f) 1
      have hd : 2 ^ f + 1 ∣ (2 ^ f) ^ 2 - 1 := by
        rw [h1]
        exact dvd_mul_right _ _
      exact dvd_trans h.dvd hd
    have hn0 : 0 < n := by have := h.four_le; omega
    obtain ⟨w, hpw, hEw⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen.card_le_of_not_pow
        h.prime hpK hn0 hE hcomm (hmem b hb g hg) hu hc
    have hp3 : 3 ≤ p := by
      have h2 := h.prime.two_le
      have hne := h.odd
      omega
    have h3w : 3 ≤ w := (Nat.pow_le_pow_iff_right h.prime.one_lt).mp (hE2.trans hEw)
    have hn3w : n - 3 ≤ w := (Nat.pow_le_pow_iff_right h.prime.one_lt).mp (hE1.trans hEw)
    have h3w' : 3 * w ≤ n := (Nat.mul_le_mul_right w hp3).trans hpw
    have h4 : 4 ≤ n := h.four_le
    omega

private theorem ggNSPosPE_normalized_lift_exists (hC : GGSecFiveNSCornerInput)
    (h : GGNSLocalHyp p B Bs K f n ψ) :
    ∀ b ∈ Bs, ∃ g : GL (Fin n) K, GGInducesUnitary (p := 2) (f := f) ψ b g ∧ g ^ p = 1 := by
  intro b hb
  obtain ⟨g, hg⟩ := h.acts b hb
  obtain ⟨c, hc⟩ := ggNSPosPE_pow_class_trivial hC h hb hg
  exact ggNSPosPE_normalize_lift (Nat.lt_of_lt_of_le (by norm_num : 0 < 4) h.four_le)
    (ggNSPosPE_unitaryFieldData_aux h.card (ggNSPosPE_one_le_f_aux h.prime h.odd h.dvd))
    h.dvd hg hc rfl

theorem ggNSPosPE_normalized_family (hC : GGSecFiveNSCornerInput) (h : GGNSLocalHyp p B Bs K f n ψ) :
    ∃ g : Bs → GL (Fin n) K, (∀ b : Bs, GGInducesUnitary (p := 2) (f := f) ψ (b : G) (g b)) ∧
      (∀ b : Bs, g b ^ p = 1) ∧ ∀ b₁ b₂ : Bs, g b₁ * g b₂ = g b₂ * g b₁ := by
  classical
  have hcore := ggNSPosPE_normalized_lift_exists hC h
  choose g hg hgp using fun b : Bs => hcore b b.2
  exact ⟨g, hg, hgp, fun b₁ b₂ => ggNSPosPF_mul_comm_of_commutator_eq_one _ _
    (ggNSPosPF_commutator_eq_one hC h b₁.2 b₂.2 (hg b₁) (hg b₂))⟩

end CFSG.StandardType

end
