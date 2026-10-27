module

public import CFSG.LocalAnalysis.WeakClosure81.W16PLemmaQBAImg

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise MatrixGroups

variable {G : Type} [Group G] [Finite G]

namespace CfgLemmaQ

variable {M V₀ V C : Subgroup G} {h : G}

private theorem card_specialLinearGroup_two (F : Type) [Field F] [Finite F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have h := Matrix.card_SL_field (𝔽 := F) 2
  rw [Fin.prod_univ_two] at h
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one] at h
  rw [h, Nat.card_eq_fintype_card (α := F)]
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  apply Nat.div_eq_of_eq_mul_left (by omega)
  have e1 : Fintype.card F ^ 2 - Fintype.card F = Fintype.card F * (Fintype.card F - 1) := by
    rw [Nat.mul_sub_one, sq]
  rw [e1]
  ring

private theorem relIndex_mul_card_map_eq_card {K : Type} [Group K]
    (ψ : ↥(V₀ ⊔ conjSubgroup V₀ h) →* K)
    (hψs : Function.Surjective ψ)
    (hψk : ψ.ker = (nVSub V₀ h ⊔ bSub V₀ h).subgroupOf (V₀ ⊔ conjSubgroup V₀ h)) :
    ((V₀ ⊔ (nVSub V₀ h ⊔ bSub V₀ h)).relIndex (V₀ ⊔ conjSubgroup V₀ h)) *
      Nat.card ((V₀.subgroupOf (V₀ ⊔ conjSubgroup V₀ h)).map ψ) = Nat.card K := by
  let X : Subgroup G := V₀ ⊔ conjSubgroup V₀ h
  let Y : Subgroup G := nVSub V₀ h ⊔ bSub V₀ h
  let T : Subgroup ↥X := (V₀ ⊔ Y).subgroupOf X
  have hYX : Y ≤ X :=
    sup_le ((inf_le_left : nVSub V₀ h ≤ V₀).trans le_sup_left)
      ((inf_le_left : bSub V₀ h ≤ conjSubgroup V₀ h).trans le_sup_right)
  have hker_le : ψ.ker ≤ T := by
    rw [hψk]
    exact Subgroup.subgroupOf_mono X le_sup_right
  have hTmap : T.map ψ = (V₀.subgroupOf X).map ψ := by
    have hT : T = (V₀.subgroupOf X) ⊔ (Y.subgroupOf X) :=
      Subgroup.subgroupOf_sup le_sup_left hYX
    rw [hT, Subgroup.map_sup]
    have hY : (Y.subgroupOf X).map ψ = ⊥ :=
      (Subgroup.map_eq_bot_iff (H := Y.subgroupOf X) (f := ψ)).mpr (le_of_eq hψk.symm)
    rw [hY, sup_bot_eq]
  show T.index * Nat.card ((V₀.subgroupOf X).map ψ) = Nat.card K
  calc T.index * Nat.card ((V₀.subgroupOf X).map ψ)
      = T.index * Nat.card (T.map ψ) := by rw [← hTmap]
    _ = (T.map ψ).index * Nat.card (T.map ψ) := by
        rw [← Subgroup.index_map_eq T hψs hker_le]
    _ = Nat.card K := Subgroup.index_mul_card (T.map ψ)

theorem odd_relIndex_of_surjective_sl (q : CfgLemmaQ M V₀ V h C) {f : ℕ} (hf : 2 ≤ f)
    (hrel : (nVSub V₀ h).relIndex V₀ = 2 ^ f) {F : Type} [Field F] [Finite F] [CharP F 2]
    (ψ : ↥(V₀ ⊔ conjSubgroup V₀ h) →* SL(2, F)) (hcard : Nat.card F = 2 ^ f)
    (hψs : Function.Surjective ψ)
    (hψk : ψ.ker = (nVSub V₀ h ⊔ bSub V₀ h).subgroupOf (V₀ ⊔ conjSubgroup V₀ h)) :
    Odd ((V₀ ⊔ (nVSub V₀ h ⊔ bSub V₀ h)).relIndex (V₀ ⊔ conjSubgroup V₀ h)) := by
  have hmap := card_map_subgroupOf_eq_relIndex q ψ hψk
  have hcount := relIndex_mul_card_map_eq_card ψ hψs hψk
  rw [hmap, hrel] at hcount
  have hK : Nat.card (SL(2, F)) = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
    simp only [card_specialLinearGroup_two F, hcard]
  rw [hK] at hcount
  have hT : (V₀ ⊔ (nVSub V₀ h ⊔ bSub V₀ h)).relIndex (V₀ ⊔ conjSubgroup V₀ h)
      = (2 ^ f) ^ 2 - 1 :=
    Nat.mul_right_cancel (m := 2 ^ f) (by positivity)
      (hcount.trans (Nat.mul_comm (2 ^ f) ((2 ^ f) ^ 2 - 1)))
  rw [hT]
  refine Nat.Even.sub_odd (n := 1) (m := (2 ^ f) ^ 2) ?_ ?_ odd_one
  · exact one_le_pow₀ (one_le_pow₀ (show (1 : ℕ) ≤ 2 by norm_num))
  · exact Even.pow_of_ne_zero (Even.pow_of_ne_zero even_two (by omega)) (by norm_num)

theorem odd_relIndex_of_dihedral (q : CfgLemmaQ M V₀ V h C) {m : ℕ} (hm : Odd m)
    (hrel : (nVSub V₀ h).relIndex V₀ = 2)
    [hN : ((nVSub V₀ h ⊔ bSub V₀ h).subgroupOf (V₀ ⊔ conjSubgroup V₀ h)).Normal]
    (e : ↥(V₀ ⊔ conjSubgroup V₀ h) ⧸
      (nVSub V₀ h ⊔ bSub V₀ h).subgroupOf (V₀ ⊔ conjSubgroup V₀ h) ≃* DihedralGroup m) :
    Odd ((V₀ ⊔ (nVSub V₀ h ⊔ bSub V₀ h)).relIndex (V₀ ⊔ conjSubgroup V₀ h)) := by
  let ψ : ↥(V₀ ⊔ conjSubgroup V₀ h) →* DihedralGroup m :=
    e.toMonoidHom.comp (QuotientGroup.mk' ((nVSub V₀ h ⊔ bSub V₀ h).subgroupOf
      (V₀ ⊔ conjSubgroup V₀ h)))
  have hψs : Function.Surjective ψ :=
    e.surjective.comp (QuotientGroup.mk'_surjective
      ((nVSub V₀ h ⊔ bSub V₀ h).subgroupOf (V₀ ⊔ conjSubgroup V₀ h)))
  have hψk : ψ.ker = (nVSub V₀ h ⊔ bSub V₀ h).subgroupOf (V₀ ⊔ conjSubgroup V₀ h) :=
    (MonoidHom.ker_mulEquiv_comp (QuotientGroup.mk'
        ((nVSub V₀ h ⊔ bSub V₀ h).subgroupOf (V₀ ⊔ conjSubgroup V₀ h))) e).trans
      (QuotientGroup.ker_mk' _)
  have hmap := card_map_subgroupOf_eq_relIndex q ψ hψk
  have hcount := relIndex_mul_card_map_eq_card ψ hψs hψk
  rw [hmap, hrel] at hcount
  rw [DihedralGroup.nat_card] at hcount
  have hT : (V₀ ⊔ (nVSub V₀ h ⊔ bSub V₀ h)).relIndex (V₀ ⊔ conjSubgroup V₀ h) = m :=
    Nat.mul_right_cancel (m := 2) (by norm_num) (hcount.trans (Nat.mul_comm 2 m))
  rw [hT]
  exact hm

end CfgLemmaQ

end CFSG.LocalAnalysis.WeakClosure81

end
