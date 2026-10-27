module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCentralizerTUPerfect
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotClassRepsCenter
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCentralizerTBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open CFSG.SeitzReduction.F4Pilot.ClassReps (frameT weylEltC weylWordT weylEltC_conj_frame
  exists_eq_f4x_44_mul_f4x_47_of_commute exists_rootChar_eq rootDiagUnit_conj_f4x_44_mul_f4x_47)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootChar)


variable {k : Type} [Field k]

theorem commutator_centralizer_frameT [Finite k] [CharP k 2] (hq : 4 ≤ Nat.card k) :
    ⁅centralizer ({frameT k} : Set (adjointGroup .F4 k)),
        centralizer ({frameT k} : Set (adjointGroup .F4 k))⁆ =
      centralizer ({frameT k} : Set (adjointGroup .F4 k)) := by
  have h := F4Pilot.factF3Perfect hq F4Pilot.TwoCentral.t
  rw [← (weylEltC_conj_frame (K := k)).1, centralizer_conj_eq_map, ← map_commutator] at h
  exact map_injective (fun a b hab => (MulAut.conj (weylEltC k weylWordT)).injective hab) h

theorem mem_centralizer_frameT_of_mem_posUnipotent [CharP k 2] {u : ModGL .F4 k}
    (hu : u ∈ posUnipotent .F4 k) :
    (⟨u, posUnipotent_le_adjointGroup hu⟩ : adjointGroup .F4 k) ∈
      centralizer ({frameT k} : Set (adjointGroup .F4 k)) := by
  rw [mem_centralizer_singleton_iff]
  exact Subtype.ext (f4x_central (Or.inr rfl) 1 hu)

theorem rootDiagUnit_mem_adjointGroup_F4 (a : Fin Tag.F4.rank → kˣ) :
    rootDiagUnit .F4 a ∈ adjointGroup .F4 k := by
  obtain ⟨⟨M, hM, -⟩, hrest⟩ := G2_F4_root_character_diagonals_inner .F4 (Or.inr rfl) k
  exact (hrest M hM a).2.2.1

theorem eq_one_or_isConj_frameT_of_forall_commute [Finite k] [CharP k 2] (hq : 3 ≤ Nat.card k)
    {z : adjointGroup .F4 k}
    (hz : ∀ w ∈ centralizer ({frameT k} : Set (adjointGroup .F4 k)), z * w = w * z) :
    z = 1 ∨ IsConj z (frameT k) := by
  have h47 : IsRoot .F4 (orbitCertRoot .F4 47) :=
    (f4_isRoot_pos (i := 47) ⟨by norm_num, by norm_num⟩).1
  have hU : ∀ u ∈ posUnipotent .F4 k, (z : ModGL .F4 k) * u = u * z := fun u hu =>
    congrArg Subtype.val (hz _ (mem_centralizer_frameT_of_mem_posUnipotent hu))
  obtain ⟨c, d, hcd⟩ := exists_eq_f4x_44_mul_f4x_47_of_commute hU
  have : Nontrivial kˣ := by
    rw [← Finite.one_lt_card_iff_nontrivial, Nat.card_units]
    omega
  obtain ⟨B, hB⟩ := exists_ne (1 : kˣ)
  obtain ⟨a, har, has⟩ := exists_rootChar_eq (1 : kˣ) B
  set h : adjointGroup .F4 k := ⟨rootDiagUnit .F4 a, rootDiagUnit_mem_adjointGroup_F4 a⟩
  have hhC : h ∈ centralizer ({frameT k} : Set (adjointGroup .F4 k)) := by
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    change rootDiagUnit .F4 a * f4x k 47 1 = f4x k 47 1 * rootDiagUnit .F4 a
    have h1 := rootDiagUnit_conj_pinnedX a h47 (1 : k)
    rw [har, Units.val_one, one_mul] at h1
    calc rootDiagUnit .F4 a * f4x k 47 1 =
          rootDiagUnit .F4 a * f4x k 47 1 * (rootDiagUnit .F4 a)⁻¹ * rootDiagUnit .F4 a := by group
      _ = f4x k 47 1 * rootDiagUnit .F4 a := by rw [f4x, h1]
  have hzh := congrArg Subtype.val (hz h hhC)
  change (z : ModGL .F4 k) * rootDiagUnit .F4 a = rootDiagUnit .F4 a * z at hzh
  have hconj : rootDiagUnit .F4 a * (z : ModGL .F4 k) * (rootDiagUnit .F4 a)⁻¹ =
      (z : ModGL .F4 k) := by
    rw [← hzh]
    group
  rw [hcd, rootDiagUnit_conj_f4x_44_mul_f4x_47, har, has, Units.val_one, one_mul] at hconj
  have hc : (B : k) * c = c :=
    pinnedX_injective (τ := .F4) (R := k) _ (mul_right_cancel hconj)
  have hB1 : (B : k) - 1 ≠ 0 := fun h0 =>
    hB (Units.ext (by rw [Units.val_one]; exact sub_eq_zero.1 h0))
  have hc0 : c = 0 := by
    have h2 : ((B : k) - 1) * c = 0 := by linear_combination hc
    exact (mul_eq_zero.1 h2).resolve_left hB1
  rw [hc0, f4x_zero, one_mul] at hcd
  by_cases hd : d = 0
  · left
    apply Subtype.ext
    rw [hcd, hd, f4x_zero]
    rfl
  · right
    obtain ⟨a', har', -⟩ := exists_rootChar_eq (Units.mk0 d hd)⁻¹ (1 : kˣ)
    refine isConj_iff.2 ⟨⟨rootDiagUnit .F4 a', rootDiagUnit_mem_adjointGroup_F4 a'⟩, ?_⟩
    apply Subtype.ext
    change rootDiagUnit .F4 a' * (z : ModGL .F4 k) * (rootDiagUnit .F4 a')⁻¹ = f4x k 47 1
    rw [hcd, f4x, rootDiagUnit_conj_pinnedX a' h47, har', Units.val_inv_eq_inv_val, Units.val_mk0,
      inv_mul_cancel₀ hd]
    rfl

end CFSG.SeitzReduction.TwistedE6Pilot
