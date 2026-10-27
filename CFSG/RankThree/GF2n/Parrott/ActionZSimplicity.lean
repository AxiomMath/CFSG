module

public import CFSG.RankThree.GF2n.Parrott.ActionZ
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo2U42
public import CFSG.RankThree.GF2n.Parrott.LocalData

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

@[expose] noncomputable def actQ :
    QP45.originalSubgroup →* MulAut ↥(centerIn (J z)) :=
  (actionZQA45 (z := z) D).comp (Subgroup.inclusion QP45_le_QA45)

theorem actQ_apply (a : QP45.originalSubgroup) :
    actQ (z := z) D a =
      actionZQA45 (z := z) D (Subgroup.inclusion QP45_le_QA45 a) := rfl

theorem isSimpleGroup_QP45_of_model : IsSimpleGroup QP45.originalSubgroup :=
  CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp
    QP45.originalSubgroup 2 3 1
    (CFSG.HardMathSupport.Dickson.I271.statedModel_QP45)

theorem isKleinFour_centerIn_J (h : Tim79a.ParrottHyp z) :
    IsKleinFour ↥(centerIn (J z)) where
  card_four := card_centerIn_J h
  exponent_two := by
    haveI : Nontrivial ↥(centerIn (J z)) :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [card_centerIn_J h]; norm_num)
    rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
    intro x hx
    refine orderOf_eq_prime ?_ hx
    apply Subtype.ext
    simpa [pow_two] using centerIn_J_sq h x.2

theorem card_mulAut_centerIn_J (h : Tim79a.ParrottHyp z) :
    Nat.card (MulAut ↥(centerIn (J z))) = 6 := by
  haveI : IsKleinFour ↥(centerIn (J z)) := isKleinFour_centerIn_J (z := z) h
  exact CFSG.kleinFour_automorphism_card ↥(centerIn (J z))

theorem actQ_ker_eq_bot_or_top :
    (actQ (z := z) D).ker = ⊥ ∨ (actQ (z := z) D).ker = ⊤ := by
  haveI : IsSimpleGroup QP45.originalSubgroup := isSimpleGroup_QP45_of_model
  exact Subgroup.Normal.eq_bot_or_eq_top (actQ (z := z) D).ker

theorem actQ_eq_one (h : Tim79a.ParrottHyp z) :
    actQ (z := z) D = 1 := by
  rcases actQ_ker_eq_bot_or_top (z := z) D with hbot | htop
  · exfalso
    have hinj : Function.Injective (actQ (z := z) D) :=
      (MonoidHom.ker_eq_bot_iff (actQ (z := z) D)).mp hbot
    haveI : Finite ↥(centerIn (J z)) := inferInstance
    haveI : Finite (MulAut ↥(centerIn (J z))) := inferInstance
    have hle : Nat.card QP45.originalSubgroup ≤ Nat.card (MulAut ↥(centerIn (J z))) :=
      Nat.card_le_card_of_injective (actQ (z := z) D) hinj
    rw [card_QP45, card_mulAut_centerIn_J (z := z) h] at hle
    omega
  · apply MonoidHom.ext
    intro a
    have ha : a ∈ (actQ (z := z) D).ker := by
      rw [htop]
      exact Subgroup.mem_top a
    simpa using (MonoidHom.mem_ker.mp ha)

theorem toQA45_symm_qH (x : ↥(H z)) :
    (QuotientData.toQA45 (z := z) (hN := hN) D).symm (qH (z := z) D x) =
      QuotientGroup.mk' ((J z).subgroupOf (H z)) x := by
  apply (QuotientData.toQA45 (z := z) (hN := hN) D).injective
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem actQ_apply_preimage (x : ↥(H z))
    (hx : qH (z := z) D x ∈
      QP45.originalSubgroup.subgroupOf QA45.originalSubgroup) :
    actQ (z := z) D
        ⟨(qH (z := z) D x : Equiv.Perm (Fin 45)), Subgroup.mem_subgroupOf.mp hx⟩ =
      actionZ z (QuotientGroup.mk' ((J z).subgroupOf (H z)) x) := by
  rw [actQ_apply, actionZQA45_apply]
  congr 1
  exact toQA45_symm_qH (z := z) D x

theorem conjZ_eq_one_of_mem_Q (h : Tim79a.ParrottHyp z) (x : ↥(H z))
    (hx : qH (z := z) D x ∈
      QP45.originalSubgroup.subgroupOf QA45.originalSubgroup) :
    conjZ z x = 1 := by
  have h1 : actQ (z := z) D
      ⟨(qH (z := z) D x : Equiv.Perm (Fin 45)), Subgroup.mem_subgroupOf.mp hx⟩ = 1 := by
    have h2 := congrArg
      (fun f : QP45.originalSubgroup →* MulAut ↥(centerIn (J z)) =>
        f ⟨(qH (z := z) D x : Equiv.Perm (Fin 45)),
          Subgroup.mem_subgroupOf.mp hx⟩)
      (actQ_eq_one (z := z) D h)
    simpa using h2
  rw [actQ_apply_preimage (z := z) D x hx, actionZ_mk] at h1
  exact h1

theorem conjZ_eq_one_of_qH_mem_QP45 (h : Tim79a.ParrottHyp z) (x : ↥(H z))
    (hx : (qH (z := z) D x : Equiv.Perm (Fin 45)) ∈ QP45.originalSubgroup) :
    conjZ z x = 1 :=
  conjZ_eq_one_of_mem_Q (z := z) D h x (Subgroup.mem_subgroupOf.mpr hx)

theorem centerIn_le_centralizer_of_conjZ_eq_one {x : ↥(H z)}
    (hx : conjZ z x = 1) :
    centerIn (J z) ≤ Subgroup.centralizer ({(x : G)} : Set G) := by
  intro y hy
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hfix := congrArg (fun a : MulAut ↥(centerIn (J z)) => a ⟨y, hy⟩) hx
  have hcoe : ((conjZ z x ⟨y, hy⟩ : centerIn (J z)) : G) = (y : G) := by
    simpa using congrArg (fun t : centerIn (J z) => (t : G)) hfix
  rw [conjZ_apply_coe] at hcoe
  calc
    (y : G) * (x : G) = ((x : G) * (y : G) * (x : G)⁻¹) * (x : G) := by rw [hcoe]
    _ = (x : G) * (y : G) := by group

theorem card_center_subgroupOf_J (h : Tim79a.ParrottHyp z) :
    Nat.card ↥(Subgroup.center (J z)) = 4 := by
  rw [← QuotientV.centerIn_subgroupOf_eq_center]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (inf_le_left : centerIn (J z) ≤ J z)).toEquiv).trans (card_centerIn_J h)

end CFSG.RankThree.GF2n.Parrott
