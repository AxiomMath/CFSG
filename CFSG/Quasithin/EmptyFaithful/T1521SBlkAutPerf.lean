module

public import CFSG.Quasithin.EmptyFaithful.T1521SBlkBasic
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtL2BlockBorel

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

theorem commutator_eq_self_of_isShort2_lin2_1521 {L : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (hshort : IsShort2 L) (hLn : IsLin2Type L n) : ⁅L, L⁆ = L := by
  have hpsl := isPSL_of_isLin2Type1521 hn hLn
  have h3 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) ≠ 3 := GoldMLA.card_ne_three_of_isPSL hpsl
  have hqs : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := hshort.2.2.2.1.resolve_right h3
  have hperf : commutator (↥L ⧸ CFSG.pCore 2 ↥L) = ⊤ := Group.isPerfect_def.1 hqs.1
  have hmap : (commutator ↥L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _
      (QuotientGroup.mk'_surjective _)]
    exact hperf
  have hN : commutator ↥L = ⊤ := by
    refine hshort.1 (commutator ↥L) ?_
    intro x
    induction x using QuotientGroup.induction_on with
    | H y =>
      have hy : QuotientGroup.mk' (CFSG.pCore 2 ↥L) y ∈
          (commutator ↥L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
        rw [hmap]; trivial
      obtain ⟨c, hc, hcy⟩ := hy
      have hp : c⁻¹ * y ∈ CFSG.pCore 2 ↥L := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hcy
        exact QuotientGroup.eq.1 hcy
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨c⁻¹ * y, hp⟩
      refine ⟨k, ?_⟩
      have hk' : (c⁻¹ * y) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have hyc : (QuotientGroup.mk y : ↥L ⧸ commutator ↥L) = QuotientGroup.mk (c⁻¹ * y) := by
        have e : y = c * (c⁻¹ * y) := by group
        conv_lhs => rw [e]
        rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff c).2 hc, one_mul]
      show (QuotientGroup.mk y : ↥L ⧸ commutator ↥L) ^ 2 ^ k = 1
      rw [hyc, ← QuotientGroup.mk_pow, hk', QuotientGroup.mk_one]
  have h1 : (commutator ↥L).map L.subtype = ⁅L, L⁆ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  rw [← h1, hN, Subgroup.map_top, Subgroup.range_subtype]



end CFSG.Quasithin
