module

public import CFSG.LocalAnalysis.WeakClosure81.SixTwelveQuotB
public import CFSG.LocalAnalysis.WeakClosure81.SixTwelveAbs
public import CFSG.LocalAnalysis.WeakClosure81.SixFiveF

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Hyp612Sym

variable {n : ℕ} {M V : Subgroup G} {g : G}

theorem centralizer_V_B_eq (h : Hyp612Sym n M V g) :
    V ⊓ centralizer ((conjSubgroup V g ⊓ M : Subgroup G) : Set G) =
      (V ⊓ conjSubgroup V g) ⊔ ⊥ := by
  rw [sup_bot_eq]
  refine le_antisymm ?_ ?_
  · intro x hx
    exact ⟨hx.1, h.centralizer_le hx⟩
  · intro x hx
    refine Subgroup.mem_inf.2 ⟨hx.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact h.elemAbelian_conj.comm (Subgroup.mem_inf.1 hb).1 hx.2

theorem inf_sup_bot_ne_conjM (h : Hyp612Sym n M V g) :
    (V ⊓ conjSubgroup V g) ⊔ ⊥ ≠ V ⊓ conjSubgroup M g := by
  rw [sup_bot_eq, ← h.NOf_eq_inf]
  exact ne_of_lt h.NOf_lt_UOf

end Hyp612Sym

section Certified


namespace Hyp612

variable {n : ℕ} {M V : Subgroup G} {g : G}

theorem exists_conj_sup (h : Hyp612 n M V g)
    (hd : H3Cond n (conjSubgroup M g) (conjSubgroup V g) g⁻¹) :
    ∃ l ∈ LOf V g, conjSubgroup V g = conjSubgroup V l := by
  haveI := h.normal_KOf
  obtain ⟨z, hz⟩ := (h.abs612 hd).exists_conj_eq
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective ((KOf M V g).subgroupOf (LOf V g)) z
  rw [imgK_conj M V g u V] at hz
  have hl : (u : G)⁻¹ ∈ LOf V g := (LOf V g).inv_mem u.2
  have hle : conjSubgroup V g ≤ conjSubgroup V (u : G)⁻¹ ⊔ KOf M V g := by
    intro w hw
    have hwL : w ∈ LOf V g := (le_sup_right : conjSubgroup V g ≤ LOf V g) hw
    have hπ : QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) ⟨w, hwL⟩ ∈
        imgK M V g (conjSubgroup V g) :=
      (mem_imgK_iff M V g).2 ⟨⟨w, hwL⟩, hw, rfl⟩
    rw [hz] at hπ
    exact mem_sup_K_of_mk_mem_imgK M V g hπ
  have hex : ∃ b ∈ conjSubgroup V g, b ∉ KOf M V g := by
    by_contra hcon
    have hleK : conjSubgroup V g ≤ KOf M V g := by
      intro b hb
      by_contra hbK
      exact hcon ⟨b, hb, hbK⟩
    exact h.toHyp612Sym.not_conjV_le_M (by
      intro b hb
      have hbB : b ∈ BOf M V g := by
        rw [← h.toHyp612Sym.conjV_inf_KOf]
        exact Subgroup.mem_inf.2 ⟨hb, hleK hb⟩
      exact (Subgroup.mem_inf.1 hbB).2)
  obtain ⟨b, hb, hbK⟩ := hex
  have hbl : ∀ w ∈ conjSubgroup V (u : G)⁻¹,
      b * w * b⁻¹ ∈ conjSubgroup V (u : G)⁻¹ ⊔ KOf M V g := by
    intro w hw
    have hbS : b ∈ conjSubgroup V (u : G)⁻¹ ⊔ KOf M V g := hle hb
    have hwS : w ∈ conjSubgroup V (u : G)⁻¹ ⊔ KOf M V g := Subgroup.mem_sup_left hw
    have hbS' : b⁻¹ ∈ conjSubgroup V (u : G)⁻¹ ⊔ KOf M V g :=
      (conjSubgroup V (u : G)⁻¹ ⊔ KOf M V g).inv_mem hbS
    exact (conjSubgroup V (u : G)⁻¹ ⊔ KOf M V g).mul_mem
      ((conjSubgroup V (u : G)⁻¹ ⊔ KOf M V g).mul_mem hbS hwS) hbS'
  have hB := h.toHyp612H3.BOf_eq_conjSubgroup_UOf hb hbK hl hbl
  exact ⟨(u : G)⁻¹, hl, h.toHyp612Sym.conjSubgroup_conjV_eq_of_le_sup hl hB hle⟩

theorem quotShape (h : Hyp612 n M V g)
    (hd : H3Cond n (conjSubgroup M g) (conjSubgroup V g) g⁻¹)
    [((KOf M V g).subgroupOf (LOf V g)).Normal] :
    QuotShape (LOf V g) (KOf M V g) (E3.mQuot V (conjSubgroup M g)) := by
  obtain ⟨hshape, hcard⟩ := (h.abs612 hd).quotPair.quotShape
  unfold QuotShape
  refine ⟨hshape, ?_⟩
  change twoRank (↥(LOf V g) ⧸ (KOf M V g).subgroupOf (LOf V g)) =
    padicValNat 2 ((conjSubgroup M g).relIndex V)
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  have hrel : (conjSubgroup M g).relIndex V =
      2 ^ twoRank (↥(LOf V g) ⧸ (KOf M V g).subgroupOf (LOf V g)) := by
    rw [← h.card_imgK_V, hcard]
  rw [hrel, padicValNat.prime_pow]

theorem inCalOStar (h : Hyp612 n M V g)
    (hd : H3Cond n (conjSubgroup M g) (conjSubgroup V g) g⁻¹) :
    InCalOStar n M ⊥ V g := by
  haveI := h.normal_KOf
  refine ⟨h.inCalO, KOf M V g, h.normal_KOf, h.coe_KOf_eq_BOf_mul_UOf, quotShape h hd,
    exists_conj_sup h hd, ?_, h.centralizer_V_B_eq, h.inf_sup_bot_ne_conjM⟩
  rw [E3.conjSubgroup_bot, Subgroup.commutator_bot_left]

end Hyp612

end Certified

end CFSG.LocalAnalysis.WeakClosure81
