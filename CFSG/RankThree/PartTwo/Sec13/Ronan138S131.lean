module

public import CFSG.RankThree.PartTwo.Sec13.Item13Inputs
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

private theorem le_zpowers_sup_of_card_inf_nine {A L : Subgroup G} {c : G} (h : Sec13Data G A c L)
    (hcL : c ∉ L) (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) :
    A ≤ Subgroup.zpowers c ⊔ L := by
  have hc3 : c ^ 3 = 1 := h.isElemAbelian.2 c h.mem_A
  have hBL : A ⊓ L ≤ L := inf_le_right
  have hAB : A = Subgroup.zpowers c ⊔ (A ⊓ L) := by
    have hle : Subgroup.zpowers c ⊔ (A ⊓ L) ≤ A :=
      sup_le (Subgroup.zpowers_le.mpr h.mem_A) inf_le_left
    have hcard := (isElemAbelian_zpowers_sup_of_card_nine hc3 (fun hcB => hcL (hBL hcB)) le_rfl h9
      (fun b hb => h.isElemAbelian.2 b hb.1) (fun b hb => h.commute h.mem_A hb.1)).2
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h.card_eq, hcard])).symm
  exact hAB.le.trans (sup_le_sup_left inf_le_right _)

theorem not_le_zpowers_sup_of_isZ3PGLThreePi {A L : Subgroup G} {c : G}
    (h : Sec13Data G A c L) (hPGL : Sec8.IsZ3PGLThreePi (lBarA c L A)) :
    ¬ A ≤ Subgroup.zpowers c ⊔ L := by
  intro hle
  have hL := h.mem_thetaComponentsAt
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hl)
  have hEN : A ≤ Subgroup.normalizer (L : Set G) := h.le_normalizer
  have hEH : A ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := h.A_le_normalizer_zpowers
  have hEc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => h.commute hx hy
  have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer (L : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun l hl => hLc l hl))
  have hinn : ∀ x ∈ A, ∀ hN : x ∈ Subgroup.normalizer (L : Set G),
      ∃ w : L ⧸ aschbacherSolvableCore 3 L, ∀ z,
        Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hN⟩) z = w * z * w⁻¹ := by
    intro x hx hN
    have hx' : x ∈ ((Subgroup.zpowers c ⊔ L : Subgroup G) : Set G) := hle hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hcN] at hx'
    obtain ⟨_, ⟨k, rfl⟩, l, hl, rfl⟩ := hx'
    refine ⟨((⟨l, hl⟩ : L) : L ⧸ aschbacherSolvableCore 3 L), fun z => ?_⟩
    induction z using QuotientGroup.induction_on with
    | H l' =>
      rw [Sec4.thetaQuotMulAut_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      rw [Sec4.normalizerMonoidHom_apply_coe]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc c ^ k * l * (l' : G) * (c ^ k * l)⁻¹ = c ^ k * (l * l' * l⁻¹) * (c ^ k)⁻¹ := by group
        _ = l * l' * l⁻¹ := by
          rw [(Commute.zpow_left (hLc _ (mul_mem (mul_mem hl l'.2) (inv_mem hl))).symm k).eq,
            mul_inv_cancel_right]
  exact false_of_inner_of_isZ3PGLThreePi h hEN hEH hEc
    (fun x hx => exists_lBar_conj_eq_of_inner hL hEN hEH hinn hx) hPGL

theorem facts131_of_isZ3PGLThreePi (h131 : Item131) (hspor : SporadicModels131)
    {A L : Subgroup G} {c : G} (h : Sec13Data G A c L)
    (hPGL : Sec8.IsZ3PGLThreePi (lBarA c L A)) :
    c ∉ L ∧ Nonempty (Sec4.autIn L A ≃* Multiplicative (ZMod 3)) ∧
      ∃ x ∈ A, Sec4.InducesTypeOn L x 3 := by
  rcases cases131 h131 hspor slTwoCenter h with
    ⟨hcL, h9, -, -⟩ | ⟨hcL, h9, -, -⟩ | ⟨hcL, -, hautIn, hx⟩ | ⟨hcmem, -⟩
  · exact absurd (le_zpowers_sup_of_card_inf_nine h hcL h9)
      (not_le_zpowers_sup_of_isZ3PGLThreePi h hPGL)
  · exact absurd (le_zpowers_sup_of_card_inf_nine h hcL h9)
      (not_le_zpowers_sup_of_isZ3PGLThreePi h hPGL)
  · exact ⟨hcL, hautIn, hx⟩
  · exact absurd hcmem (not_mem_of_center_eq_bot h (facts_of_isZ3PGLThreePi h hPGL).2.1)

end CFSG.RankThree.PartTwo.Sec13.Ronan138S
