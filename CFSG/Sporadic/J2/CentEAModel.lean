module

public import CFSG.Sporadic.J2.CentEAFacts
public import Certificates.Certificate1053001

public section

namespace CFSG.Sporadic.J2

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.GH74.Generic.S45.EvSpor CFSG.GH74.GLS.C3.Layer1.Bk.J2C
open scoped commutatorElement

private theorem j2CentEACheck_parts :
    j2CommSqOK = true ∧ j2ERankOK = true ∧ j2C2BSqOK = true := by
  have h := Certificates.certificate1053001
  simp only [j2CentEACheck, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem exists_comm_sq_ne_one_of_mem_Ysub
    {g : Equiv.Perm (Fin 315)}
    (hg : g ∈ Ysub) (hgE : g ∉ Esub) (hg2 : orderOf g = 2) :
    ∃ e ∈ Esub, ⁅e, g⁆ * ⁅e, g⁆ ≠ 1 := by
  obtain ⟨hYE, hYinv, -⟩ := Y_facts
  obtain ⟨hE, -, hEinv, -⟩ := E_facts Certificates.certificate5153.1
  obtain ⟨G, hG, hrep⟩ := hYE.rep_mem hg
  have h : (!involOK 315 G || memT 315 j2E G ||
      j2E.any fun e => !tblEq 315 (commSqT e G) (idT 315)) = true :=
    Array.all_eq_true_iff_forall_mem.1 j2CentEACheck_parts.1 G hG
  have hmem : memT 315 j2E G = false :=
    Bool.eq_false_iff.2 fun h' => hgE ((hE.mem_iff hrep).1 h')
  rw [involOK_of_orderOf hn315 hrep hg2, hmem, Bool.not_true, Bool.false_or, Bool.false_or,
    Array.any_eq_true'] at h
  obtain ⟨T, hT, hne⟩ := h
  obtain ⟨e, he, hrepe⟩ := rep_of_mem_enums hE hT
  refine ⟨e, he, fun h1 => ?_⟩
  have hc := rep_commutatorT hrepe hrep (inv_rep_of_mem hEinv hT hrepe)
    (inv_rep_of_mem hYinv hG hrep)
  have h2 : tblEq 315 (commSqT T G) (idT 315) = true :=
    (tblEq_iff_eq (Rep.compT hc hc) (Rep.idT hn315)).2 h1
  rw [h2] at hne
  exact Bool.false_ne_true hne

private theorem exists_mem_j2EInvs (hE : EnumsSub 315 j2E Esub)
    {A : Subgroup (Equiv.Perm (Fin 315))} (hA : A ≤ Esub) (hAe : CFSG.Open.IsElemAbelian 2 A)
    {a : Equiv.Perm (Fin 315)} (ha : a ∈ A) (ha1 : a ≠ 1) : ∃ T ∈ j2EInvs, Rep 315 T a := by
  obtain ⟨T, hT, hrep⟩ := hE.rep_mem (hA ha)
  exact ⟨T, Array.mem_filter.2
    ⟨hT, involOK_of_orderOf hn315 hrep (orderOf_eq_prime (hAe.2 a ha) ha1)⟩, hrep⟩

private theorem j2ERank_entry {X Y Z : Table}
    (hX : X ∈ j2EInvs) (hY : Y ∈ j2EInvs) (hZ : Z ∈ j2EInvs) :
    (!(commTT 315 X Y && commTT 315 X Z && commTT 315 Y Z) || tblEq 315 Y X || tblEq 315 Z X ||
      tblEq 315 Z Y || tblEq 315 Z (compT 315 X Y)) = true := by
  have h := j2CentEACheck_parts.2.1
  rw [j2ERankOK, Array.all_eq_true_iff_forall_mem] at h
  have h := h X hX
  rw [Array.all_eq_true_iff_forall_mem] at h
  have h := h Y hY
  rw [Array.all_eq_true_iff_forall_mem] at h
  exact h Z hZ

private theorem tblEq_eq_false_of_ne {S T : Table} {g h : Equiv.Perm (Fin 315)}
    (hS : Rep 315 S g) (hT : Rep 315 T h) (hne : g ≠ h) : tblEq 315 S T = false :=
  Bool.eq_false_iff.2 fun e => hne ((tblEq_iff_eq hS hT).1 e)

theorem card_le_four_of_le_Esub
    {A : Subgroup (Equiv.Perm (Fin 315))} (hA : A ≤ Esub)
    (hAe : CFSG.Open.IsElemAbelian 2 A) : Nat.card A ≤ 4 := by
  obtain ⟨hE, -⟩ := E_facts Certificates.certificate5153.1
  refine card_le_four_of_forall_eq_mul fun x hx y hy z hz hx1 hy1 hz1 hyx hzx hzy => ?_
  obtain ⟨X, hX, hrx⟩ := exists_mem_j2EInvs hE hA hAe hx hx1
  obtain ⟨Y, hY, hry⟩ := exists_mem_j2EInvs hE hA hAe hy hy1
  obtain ⟨Z, hZ, hrz⟩ := exists_mem_j2EInvs hE hA hAe hz hz1
  have hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAe.1.is_comm.comm (⟨a, ha⟩ : A) ⟨b, hb⟩)
  have h := j2ERank_entry hX hY hZ
  simp only [(commTT_iff hrx hry).2 (hc x hx y hy), (commTT_iff hrx hrz).2 (hc x hx z hz),
    (commTT_iff hry hrz).2 (hc y hy z hz), tblEq_eq_false_of_ne hry hrx hyx,
    tblEq_eq_false_of_ne hrz hrx hzx, tblEq_eq_false_of_ne hrz hry hzy, Bool.and_true,
    Bool.not_true, Bool.false_or] at h
  exact (tblEq_iff_eq hrz (Rep.compT hrx hry)).1 h

theorem orderOf_ne_four_of_mem_cent_tB
    {y : Equiv.Perm (Fin 315)}
    (hy : y ∈ j2P ⊓ centralizer ({tp 315 j2Row2B.rep} : Set (Equiv.Perm (Fin 315)))) :
    orderOf y ≠ 4 := by
  obtain ⟨hE, -⟩ := j2_C2B_enums Certificates.certificate5150.2.2.1
  obtain ⟨T, hT, hrep⟩ := hE.rep_mem hy
  have h : (!tblEq 315 (powT 315 4 T) (idT 315) || tblEq 315 (powT 315 2 T) (idT 315)) = true :=
    Array.all_eq_true_iff_forall_mem.1 j2CentEACheck_parts.2.2 T hT
  intro h4
  have hy4 : y ^ 4 = 1 := by rw [← h4]; exact pow_orderOf_eq_one y
  rw [(tblEq_iff_eq (Rep.powT hn315 hrep 4) (Rep.idT hn315)).2 hy4, Bool.not_true,
    Bool.false_or, tblEq_iff_eq (Rep.powT hn315 hrep 2) (Rep.idT hn315)] at h
  have := orderOf_dvd_of_pow_eq_one h
  rw [h4] at this
  norm_num at this

theorem j2CentEAFacts_model :
    J2CentEAFacts ↥j2P tAj Ej := by
  have hEP : Esub ≤ j2P :=
    (E_facts Certificates.certificate5153.1).2.2.2.2.2.1.trans inf_le_left
  refine ⟨fun g hg hgE hg2 => ?_, fun A hA hAe => ?_⟩
  · have hg1 : g ≠ 1 := fun h1 => hgE (by rw [h1]; exact Ej.one_mem)
    have hg2' : orderOf (g : Equiv.Perm (Fin 315)) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_eq_prime (by rw [pow_two]; exact hg2) hg1
    obtain ⟨e, he, hne⟩ := exists_comm_sq_ne_one_of_mem_Ysub ((mem_cent_tAj g).1 hg) hgE hg2'
    refine ⟨⟨e, hEP he⟩, he, ⟨e, hEP he⟩, he, Or.inr fun h1 => hne ?_⟩
    have := congrArg j2P.subtype h1
    rwa [map_mul, map_commutatorElement, map_one] at this
  · have hA' : A.map j2P.subtype ≤ Esub := by
      rintro _ ⟨a, ha, rfl⟩
      exact hA ha
    have := card_le_four_of_le_Esub hA' (hAe.map j2P.subtype)
    rwa [Subgroup.card_map_of_injective j2P.subtype_injective] at this

end CFSG.Sporadic.J2
