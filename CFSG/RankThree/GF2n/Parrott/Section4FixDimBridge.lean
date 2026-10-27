module

public import CFSG.RankThree.GF2n.Parrott.ActionQA
public import CFSG.RankThree.GF2n.Parrott.FixDim
public import CFSG.RankThree.GF2n.Parrott.LocalData
public import Certificates.Data.ParrottSpin
public import CFSG.RankThree.GF2n.Parrott.FixCardConj
public import CFSG.RankThree.GF2n.Parrott.LiftOrderThree

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable {G : Type} [Group G] [Finite G] {z : G}

section Bridge

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

theorem actionQA45_qH (h : Tim79a.ParrottHyp z) (x : ↥(H z)) :
    actionQA45 (z := z) h D (qH D x) = mulAutVEquivGL h (conjV h x) := by
  rw [actionQA45_apply]
  have h1 : (QuotientData.toQA45 (z := z) (hN := hN) D).symm (qH D x) =
      QuotientGroup.mk' ((J z).subgroupOf (H z)) x := by
    simp [qH]
  rw [h1, actionGL_mk]

theorem card_autFixedSubgroup_conjV_eq_fixCard (h : Tim79a.ParrottHyp z) (x : ↥(H z)) :
    Nat.card (autFixedSubgroup (conjV h x)) =
      fixCard (((actionQA45 (z := z) h D (qH D x) :
        Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2))) := by
  rw [actionQA45_qH D h x, fixCard, ← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  refine
    { toFun := fun v => ⟨Multiplicative.toAdd (mulEquivV h v.1), ?_⟩
      invFun := fun w => ⟨(mulEquivV h).symm (Multiplicative.ofAdd w.1), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [mulVec_mulAutVEquivGL h (conjV h x) v.1]
    exact congrArg (fun y => Multiplicative.toAdd (mulEquivV h y)) (mem_autFixedSubgroup.mp v.2)
  · have h1 := mulVec_mulAutVEquivGL h (conjV h x) ((mulEquivV h).symm (Multiplicative.ofAdd w.1))
    rw [MulEquiv.apply_symm_apply] at h1
    rw [mem_autFixedSubgroup]
    apply (mulEquivV h).injective
    apply Multiplicative.toAdd.injective
    rw [← h1]
    simpa using w.2
  · intro v
    apply Subtype.ext
    simp
  · intro w
    apply Subtype.ext
    simp

set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : ↥QA45.originalSubgroup)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : ↥QA45.originalSubgroup)

theorem two_pow_fixDimV_eq_of_conj_rep (h : Tim79a.ParrottHyp z)
    (ρ : QA45.originalSubgroup →* Matrix.GeneralLinearGroup (Fin 8) (ZMod 2))
    (P : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2))
    (hP : ∀ a, actionQA45 (z := z) h D a = P * ρ a * P⁻¹) (x : ↥(H z)) :
    2 ^ fixDimV h x = fixCard (((ρ (qH D x) : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) :
      Matrix (Fin 8) (Fin 8) (ZMod 2))) := by
  rw [← card_fix h x, card_autFixedSubgroup_conjV_eq_fixCard D h x, hP, fixCard_conj]

theorem fixDimV_eq_four_of_conj_rep (h : Tim79a.ParrottHyp z)
    (ρ : QA45.originalSubgroup →* Matrix.GeneralLinearGroup (Fin 8) (ZMod 2))
    (P : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2))
    (hP : ∀ a, actionQA45 (z := z) h D a = P * ρ a * P⁻¹)
    (hρ : ∀ a : ↥QA45.originalSubgroup, IsConj a (uA * tA) →
      fixCard (((ρ a : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) :
        Matrix (Fin 8) (Fin 8) (ZMod 2))) = 16) :
    ∀ x : ↥(H z), IsConj (qH D x) (uA * tA) → fixDimV h x = 4 := by
  intro x hx
  have h1 := two_pow_fixDimV_eq_of_conj_rep D h ρ P hP x
  rw [hρ _ hx] at h1
  exact Nat.pow_right_injective (le_refl 2) (h1.trans (by norm_num))

end Bridge

end CFSG.RankThree.GF2n.Parrott
