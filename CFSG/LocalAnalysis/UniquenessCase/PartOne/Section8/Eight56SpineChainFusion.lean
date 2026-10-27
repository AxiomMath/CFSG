module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56Spine

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)

theorem normalizer_le_of_controlsFusionIn {G : Type} [Group G] {M P : Subgroup G}
    (hfus : ControlsFusionIn M P) (hC : centralizer (P : Set G) ≤ M) :
    normalizer (P : Set G) ≤ M := by
  intro g hg
  have hg' : ∀ h : G, h ∈ P ↔ g⁻¹ * h * g ∈ P := (Subgroup.mem_normalizer_iff'').mp hg
  have hmap : P.map (MulAut.conj g⁻¹).toMonoidHom ≤ P := by
    rintro x ⟨y, hy, rfl⟩
    change g⁻¹ * y * (g⁻¹)⁻¹ ∈ P
    rw [inv_inv]
    exact (hg' y).1 hy
  obtain ⟨m, hmM, hm⟩ := hfus P le_rfl g hmap
  have hcomm : ∀ x ∈ P, x * (g * m⁻¹) = (g * m⁻¹) * x := by
    intro x hx
    have h := hm x hx
    calc x * (g * m⁻¹) = g * (g⁻¹ * x * g) * m⁻¹ := by group
      _ = g * (m⁻¹ * x * m) * m⁻¹ := by rw [h]
      _ = (g * m⁻¹) * x := by group
  have hmem : g * m⁻¹ ∈ centralizer (P : Set G) := (Subgroup.mem_centralizer_iff).2 hcomm
  have hgm : g * m⁻¹ ∈ M := hC hmem
  have hg_eq : g = (g * m⁻¹) * m := by group
  rw [hg_eq]
  exact M.mul_mem hgm hmM

theorem sylow_three_ne_bot_of_one_le_pRank {G : Type} [Group G] [Finite G] {M L P : Subgroup G}
    (hLM : L ≤ M) (hr : 1 ≤ CFSG.Open.pRank 3 L) (hP : IsSylowOf 3 P M) : P ≠ ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hEL, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) L
  have h3E : 3 ∣ Nat.card E := by
    rw [hEcard]
    exact dvd_pow_self 3 (by omega)
  have h3M : 3 ∣ Nat.card M := h3E.trans (Subgroup.card_dvd_of_le (hEL.trans hLM))
  have hpos : 0 < (Nat.card M).factorization 3 :=
    Nat.prime_three.factorization_pos_of_dvd Nat.card_pos.ne' h3M
  have hPcard : 3 ≤ Nat.card P := by
    rw [hP.card_eq]
    calc 3 = 3 ^ 1 := (pow_one 3).symm
      _ ≤ 3 ^ (Nat.card M).factorization 3 :=
          Nat.pow_le_pow_right (by norm_num) hpos
  intro hbot
  rw [hbot, Subgroup.card_bot] at hPcard
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
