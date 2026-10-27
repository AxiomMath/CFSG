module

public import CFSG.LocalAnalysis.WeakClosure81.FourteenFiveLift
public import CFSG.LocalAnalysis.WeakClosure81.FourteenEightBender

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.GH74.Uniqueness.Bender
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace FourteenFive

variable {n : ℕ} {M V₀ V : Subgroup G} {g : G}

section Certified


theorem exists_torusData (h : Hyp65 n M V₀ V g) [((KOf M V g).subgroupOf (LOf V g)).Normal]
    (h2 : 2 ≤ E3.mQuot V (conjSubgroup M g)) {l : G} (hlL : l ∈ LOf V g)
    (hlV : conjSubgroup V g = conjSubgroup V l) :
    ∃ T : Subgroup (↥(LOf V g) ⧸ (KOf M V g).subgroupOf (LOf V g)),
      TorusData (imgK M V g V)
        (QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) ⟨l, hlL⟩) T := by
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1
    (imgK_isElemAbelian M V g h.elemAbelian).isPGroup
  have hm : E3.mQuot V (conjSubgroup M g) = k := by
    unfold E3.mQuot
    rw [← h.card_imgK, hk]
    exact padicValNat.prime_pow k
  have hcardm : Nat.card (imgK M V g V) = 2 ^ E3.mQuot V (conjSubgroup M g) := by
    rw [hm]
    exact hk
  have hconj : imgK M V g (conjSubgroup V g) =
      conjSubgroup (imgK M V g V)
        (QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) ⟨l, hlL⟩) := by
    unfold imgK
    exact map_subgroupOf_conjSubgroup_eq (K := KOf M V g) hlL hlV
  have hsup : imgK M V g V ⊔
      conjSubgroup (imgK M V g V)
        (QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) ⟨l, hlL⟩) = ⊤ := by
    rw [← hconj]
    exact imgK_sup M V g
  obtain ⟨hshape, htwo⟩ := h.quotShape
  rcases hshape with ⟨r, hL2⟩ | ⟨r, hSz⟩ | hdi
  · have hrtwo : twoRank (↥(LOf V g) ⧸ (KOf M V g).subgroupOf (LOf V g)) = r :=
      CFSG.GH74.twoRank_eq_of_lieModel_PSL_two_two hL2
    have hrm : r = E3.mQuot V (conjSubgroup M g) := by rw [← hrtwo, htwo]
    have hr2 : 2 ≤ r := by omega
    obtain ⟨e⟩ := nonempty_psl_equiv_of_isL2 (one_le_of_isL2 hL2) hL2
    have hcard : Nat.card (imgK M V g V) = 2 ^ r := by rw [hrm]; exact hcardm
    exact exists_torusData_of_benderType
      (A := imgK M V g V)
      (g₀ := QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) ⟨l, hlL⟩)
      (.linear r hr2 e) (imgK_isElemAbelian M V g h.elemAbelian) hcard hsup
  · obtain ⟨a, ha, rfl, ⟨e⟩⟩ := exists_mulEquiv_sz_of_isSz hSz
    have hrtwo : twoRank (↥(LOf V g) ⧸ (KOf M V g).subgroupOf (LOf V g)) = 2 * a + 1 :=
      twoRank_eq_of_mulEquiv_sz ha e
    have hrm : 2 * a + 1 = E3.mQuot V (conjSubgroup M g) := by rw [← hrtwo, htwo]
    have hcard : Nat.card (imgK M V g V) = 2 ^ (2 * a + 1) := by rw [hrm]; exact hcardm
    exact exists_torusData_of_benderType
      (A := imgK M V g V)
      (g₀ := QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) ⟨l, hlL⟩)
      (.suzuki a ha (e.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm)))
      (imgK_isElemAbelian M V g h.elemAbelian) hcard hsup
  · obtain ⟨m₀, hm₀, ⟨e⟩⟩ := hdi
    have hAle : Nat.card (imgK M V g V) ≤ 2 := by
      have h1 : Nat.card ((imgK M V g V).map e.toMonoidHom) ≤ 2 :=
        nat_card_le_two_of_isElemAbelian_dihedral hm₀
          ((imgK_isElemAbelian M V g h.elemAbelian).map e.toMonoidHom)
      rwa [Subgroup.card_map_of_injective e.injective] at h1
    have hle2 : 2 ^ E3.mQuot V (conjSubgroup M g) ≤ 2 := by
      rw [← hcardm]; exact hAle
    have hge4 : 4 ≤ 2 ^ E3.mQuot V (conjSubgroup M g) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ E3.mQuot V (conjSubgroup M g) := Nat.pow_le_pow_right (by norm_num) h2
    omega

theorem exists_torus (h : Hyp65 n M V₀ V g) (h2 : 2 ≤ E3.mQuot V (conjSubgroup M g)) :
    ∃ Y : Subgroup G, Y ≤ LOf V g ⊓ M ∧
      Nat.card Y = 2 ^ E3.mQuot V (conjSubgroup M g) - 1 ∧
      ∀ y ∈ Y, y ≠ 1 → ∀ v ∈ V, y * v * y⁻¹ = v → v ∈ NOf M V g := by
  haveI := h.K_normal
  obtain ⟨l, hlL, hlV⟩ := h.exists_conj
  obtain ⟨T, hT⟩ := exists_torusData h h2 hlL hlV
  exact exists_torus_of_torusData h h.genHyp hlL hlV hT

end Certified

end FourteenFive

end CFSG.LocalAnalysis.WeakClosure81
