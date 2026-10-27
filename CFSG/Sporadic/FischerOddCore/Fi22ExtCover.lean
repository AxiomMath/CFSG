
module

public import CFSG.Sporadic.FischerOddCore.Fi22ExtCoverBase1

public import CFSG.Sporadic.FischerOddCore.Fi22ExtSylow
public import CFSG.Sporadic.FischerOddCore.Fi22ExtCoverCheck
public import CFSG.Sporadic.FischerOddCore.LabelSpec
import Mathlib.Tactic.Group
public import CFSG.Sporadic.FischerOddCore.Fi22ExtCheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtData
public meta import CFSG.Monster.B.Fischer.Fi22OuterCheck
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Sporadic.FischerOddCore.Fi22ExtCoverCheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheck
public meta import Certificates.Data.CFSGNative.FischerOddCore.Checks
public import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtCheck
public meta import CFSG.Monster.B.Fischer.Fi22CoverCheck
public meta import CFSG.Monster.B.Fischer.Fi22OrderCheck
public meta import CFSG.Monster.B.Fischer.Fi22GraphCheck
public import CFSG.Monster.B.Fischer.Fi22GraphCheckInputs
public import CFSG.Monster.B.Fischer.Fi22OuterCheckInputs
public import CFSG.Monster.B.Fischer.PinnedChainInputs
public import CFSG.Monster.B.Fischer.Fi22OrderCheckInputs
public import CFSG.Monster.B.Fischer.Fi22OuterArrays
public import CFSG.Monster.B.Fischer.Fi22OrderCheck
public import CFSG.Monster.B.Fischer.Fi22CoverCheckInputs
public import CFSG.Monster.B.Fischer.Fi22GraphCheck
public import CFSG.Monster.B.Fischer.Fi22Cover

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore.Native

theorem fi22ExtLabel_facts :
    (∀ x : fi22ExtS, orderOf x = 2 → ∃ j < fi22ExtRoots.size, ∃ g : fi22ExtS,
      g * fi22ExtE fi22ExtRoots[j]! * g⁻¹ = x) ∧
    (∀ j < fi22ExtRoots.size, ∀ j' < fi22ExtRoots.size,
      (∃ g : fi22ExtS, g * fi22ExtE fi22ExtRoots[j]! * g⁻¹ = fi22ExtE fi22ExtRoots[j']!) → j = j') ∧
    (∀ j < fi22ExtRoots.size, orderOf (fi22ExtE fi22ExtRoots[j]!) = 2) ∧
    (∀ j < fi22ExtRoots.size, Nat.card {x : fi22ExtS // ∃ g : fi22ExtS,
      g * fi22ExtE fi22ExtRoots[j]! * g⁻¹ = x} = labCount fi22ExtLabels.lab 262144 j) := by
  have hroots : ∀ j < fi22ExtRoots.size, fi22ExtRoots[j]! < 262144 ∧
      fi22ExtLabels.lab[fi22ExtRoots[j]!]! = j := fun j hj =>
    fi22ExtCover_check.2.1 j (by simpa [fi22ExtRoots, fi22ExtRootsRec] using hj)
  exact labelOK_spec fi22ExtRes_injective (fun I hI => rep_fi22ExtResArr hI)
    (fun s hs => rep_fi22ExtSteps hs) closure_fi22ExtGen
    (parLt_spec (by norm_num) fi22ExtCover_check.1) hroots fi22ExtE_surj
    (fun I hI J hJ h => fi22ExtE_inj hI hJ h)

theorem fi22ExtE_root
    {j : ℕ} (hj : j < 79) :
    (fi22ExtE fi22ExtRoots[j]! : Equiv.Perm (Fin 3510)) = fi22ExtSylowRep j :=
  eq_of_eqA (rep_fi22ExtFullArr (fi22ExtCover_check.2.1 j hj).1)
    (rep_fi22ExtPerm (L := 27 + j) (by omega)) (fi22ExtCover_check.2.2.2.1 j hj)

theorem fi22ExtSylowRep_mem
    {j : ℕ} (hj : j < 79) : fi22ExtSylowRep j ∈ fi22ExtS := by
  rw [← fi22ExtE_root hj]
  exact (fi22ExtE _).2

theorem fi22ExtE_root_eq
    {j : ℕ} (hj : j < 79) :
    fi22ExtE fi22ExtRoots[j]! = ⟨fi22ExtSylowRep j, fi22ExtSylowRep_mem hj⟩ :=
  Subtype.ext (fi22ExtE_root hj)

theorem fi22ExtConj_spec
    {j : ℕ} (hj : j < 79) :
    fi22ExtConj j ∈ fi22P ∧
      fi22ExtConj j * fi22ExtSylowRep j * (fi22ExtConj j)⁻¹ =
        fi22ExtRep (fi22ExtGlobalClass j) := by
  obtain ⟨hP, heq⟩ := fi22ExtCover_check.2.2.2.2.2.1 j hj
  have hgc : fi22ExtGlobalClass j < 6 :=
    CTUC_Fi22_extension_involution_data.2.2.2.2.2.2.2.2.2.2.2.2.2.2 j hj
  refine ⟨(fi22InP_iff (rep_fi22ExtPerm (L := 106 + j) (by omega))).1 hP, ?_⟩
  have := eq_of_eqA (rep_compA (rep_fi22ExtPerm (L := 106 + j) (by omega))
    (rep_fi22ExtPerm (L := 27 + j) (by omega)))
    (rep_compA (rep_fi22ExtRep hgc) (rep_fi22ExtPerm (L := 106 + j) (by omega))) (by
      rw [fi22ExtGlobalClass] at hgc ⊢
      exact heq)
  rw [fi22ExtConj, fi22ExtSylowRep, this, mul_inv_cancel_right]

theorem orderOf_fi22ExtRep
    {k : ℕ} (hk : k < 6) : orderOf (fi22ExtRep k) = 2 := by
  have h := (isInvArr_iff (rep_fi22ExtRep hk)).1 (fi22ExtCover_check.2.2.2.2.2.2.2.2.1 k hk)
  exact (orderOf_eq_two_iff' _).2 h

theorem fi22ExtRep_fixed :
    ((List.range 6).map fun k => (Finset.univ.filter fun p => fi22ExtRep k p = p).card) =
      [54, 182, 694, 72, 360, 64] := by
  rw [← fi22ExtCover_check.2.2.2.2.2.2.2.2.2.1]
  apply List.map_congr_left
  intro k hk
  exact card_fixed_eq_fixCount (rep_fi22ExtRep (List.mem_range.1 hk))

theorem fi22R_involution_conj
    {τ : Equiv.Perm (Fin 3510)} (hτ : τ ∈ fi22R) (ho : orderOf τ = 2) :
    ∃ k < 6, ∃ r ∈ fi22R, r * τ * r⁻¹ = fi22ExtRep k := by
  obtain ⟨P2, hP2⟩ := fi22ExtS_sylow
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set τ' : fi22R := ⟨τ, hτ⟩
  have ho' : orderOf τ' = 2 := by rw [← Subgroup.orderOf_coe]; exact ho
  have hp : IsPGroup 2 (Subgroup.zpowers τ') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ho', pow_one])
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq fi22R Q P2
  have hmem : c * τ' * c⁻¹ ∈ (P2 : Subgroup fi22R) := by
    rw [← hc, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj c) _ (hQ (Subgroup.mem_zpowers _))
  rw [hP2, Subgroup.mem_subgroupOf] at hmem
  set s : Equiv.Perm (Fin 3510) := ((c * τ' * c⁻¹ : fi22R) : Equiv.Perm (Fin 3510))
  have hso : orderOf (⟨s, hmem⟩ : fi22ExtS) = 2 := by
    have h1 : orderOf (⟨s, hmem⟩ : fi22ExtS) = orderOf s := Subgroup.orderOf_mk s hmem
    have h2 : orderOf s = orderOf (c * τ' * c⁻¹) := Subgroup.orderOf_coe _
    have h3 : orderOf (c * τ' * c⁻¹) = orderOf τ' := by
      rw [show c * τ' * c⁻¹ = MulAut.conj c τ' from rfl]
      exact MulEquiv.orderOf_eq _ _
    rw [h1, h2, h3, ho']
  obtain ⟨j, hj, g, hg⟩ := fi22ExtLabel_facts.1 _ hso
  rw [fi22ExtRoots_size] at hj
  rw [fi22ExtE_root_eq hj] at hg
  have hg' : (g : Equiv.Perm (Fin 3510)) * fi22ExtSylowRep j * (g : Equiv.Perm (Fin 3510))⁻¹ = s :=
    congrArg Subtype.val hg
  obtain ⟨hhP, hh⟩ := fi22ExtConj_spec hj
  refine ⟨fi22ExtGlobalClass j,
    CTUC_Fi22_extension_involution_data.2.2.2.2.2.2.2.2.2.2.2.2.2.2 j hj,
    fi22ExtConj j * (g : Equiv.Perm (Fin 3510))⁻¹ * (c : Equiv.Perm (Fin 3510)),
    fi22R.mul_mem (fi22R.mul_mem (fi22P_le_R hhP) (fi22R.inv_mem (fi22ExtS_le_R g.2))) c.2, ?_⟩
  rw [← hh, show fi22ExtSylowRep j = (g : Equiv.Perm (Fin 3510))⁻¹ * s * g by rw [← hg']; group]
  simp only [s, Subgroup.coe_mul, Subgroup.coe_inv, τ']
  group

theorem CTUC_Fi22_all_extension_involutions_covered :
    (∀ k < 3, fi22ExtRep k ∈ fi22P) ∧
    (∀ k < 3, fi22ExtRep (3 + k) ∈ fi22R ∧ fi22ExtRep (3 + k) ∉ fi22P) ∧
    (∀ k < 6, orderOf (fi22ExtRep k) = 2) ∧
    ((List.range 6).map fun k => (Finset.univ.filter fun p => fi22ExtRep k p = p).card) =
      [54, 182, 694, 72, 360, 64] ∧
    (∀ i < 3, fi22ExtRep i = fi22OuterXRep i) ∧ fi22ExtRep 2 = fi22OuterZ ∧ fi22ExtRep 3 = fi22U ∧
    Nat.card {s : fi22ExtS // orderOf s = 2} = 6143 ∧
    (∀ j < 79, fi22ExtSylowRep j ∈ fi22ExtS) ∧
    (∀ j < 79, ∀ j' < 79, (∃ g ∈ fi22ExtS, g * fi22ExtSylowRep j * g⁻¹ = fi22ExtSylowRep j') →
      j = j') ∧
    (∀ s ∈ fi22ExtS, orderOf s = 2 → ∃ j < 79, ∃ g ∈ fi22ExtS, g * fi22ExtSylowRep j * g⁻¹ = s) ∧
    (∀ (j : ℕ) (hj : j < 79), Nat.card {s : fi22ExtS // ∃ g : fi22ExtS,
      g * ⟨fi22ExtSylowRep j, fi22ExtSylowRep_mem hj⟩ * g⁻¹ = s} = fi22ExtClassSize j) ∧
    (∀ j < 79, fi22ExtConj j ∈ fi22P ∧
      fi22ExtConj j * fi22ExtSylowRep j * (fi22ExtConj j)⁻¹ = fi22ExtRep (fi22ExtGlobalClass j)) ∧
    (∀ τ ∈ fi22R, orderOf τ = 2 → ∃ k < 6, ∃ r ∈ fi22R, r * τ * r⁻¹ = fi22ExtRep k) := by
  obtain ⟨hcov, hdisj, -, hcount⟩ := fi22ExtLabel_facts
  rw [fi22ExtRoots_size] at hcov hdisj hcount
  have hxrep : ∀ i < 3, fi22ExtRep i = fi22OuterXRep i := fun i hi =>
    eq_of_eqA (rep_fi22ExtRep (by omega)) (rep_fi22OuterXRep hi)
      (fi22ExtCover_check.2.2.2.2.2.2.1 i hi)
  refine ⟨fun k hk => (fi22InP_iff (rep_fi22ExtRep (by omega))).1
      (fi22ExtCover_check.2.2.2.2.2.2.2.2.2.2.1 k hk), fun k hk => ?_,
    fun k hk => orderOf_fi22ExtRep hk, fi22ExtRep_fixed, hxrep,
    (hxrep 2 (by norm_num)).trans fi22OuterXRep_two,
    eq_of_eqA (rep_fi22ExtRep (by norm_num)) rep_fi22U fi22ExtCover_check.2.2.2.2.2.2.2.1,
    ?_, fun j hj => fi22ExtSylowRep_mem hj, fun j hj j' hj' h => ?_, fun s hs ho => ?_,
    fun j hj => ?_, fun j hj => fi22ExtConj_spec hj, fun τ hτ ho => fi22R_involution_conj hτ ho⟩
  · obtain ⟨h1, h2⟩ := fi22ExtCover_check.2.2.2.2.2.2.2.2.2.2.2.1 k hk
    refine ⟨(mem_fi22R_iff _).2 (Or.inr ((fi22InP_iff (rep_compA rep_fi22U
      (rep_fi22ExtRep_outer hk))).1 h2)), fun hm => ?_⟩
    rw [(fi22InP_iff (rep_fi22ExtRep_outer hk)).2 hm] at h1
    exact Bool.noConfusion h1
  · rw [← fi22ExtCover_check.2.2.2.2.2.2.2.2.2.2.2.2, labelledCount, ← card_fin_subtype_eq_countP]
    symm
    refine Nat.card_congr
      { toFun := fun I => ⟨fi22ExtE I, ?_⟩
        invFun := fun x => ⟨⟨_, (fi22ExtE_surj x).choose_spec.1⟩, ?_⟩
        left_inv := fun I => ?_
        right_inv := fun x => ?_ }
    · have := (orderOf_eq_two_iff_lab_lt fi22ExtRes_injective (fun I hI => rep_fi22ExtResArr hI)
        (parLt_spec (by norm_num) fi22ExtCover_check.1) I.1.2).2 (by
          rw [fi22ExtRoots_size]; simpa using I.2)
      exact this
    · have h := (orderOf_eq_two_iff_lab_lt fi22ExtRes_injective (fun I hI => rep_fi22ExtResArr hI)
        (parLt_spec (by norm_num) fi22ExtCover_check.1) (fi22ExtE_surj x).choose_spec.1).1 (by
          rw [(fi22ExtE_surj x).choose_spec.2]; exact x.2)
      rw [fi22ExtRoots_size] at h
      simpa using h
    · apply Subtype.ext; apply Fin.ext
      exact fi22ExtE_inj (fi22ExtE_surj _).choose_spec.1 I.1.2 (fi22ExtE_surj _).choose_spec.2
    · exact Subtype.ext (fi22ExtE_surj x).choose_spec.2
  · obtain ⟨g, hg, hgw⟩ := h
    refine hdisj j hj j' hj' ⟨⟨g, hg⟩, ?_⟩
    rw [fi22ExtE_root_eq hj, fi22ExtE_root_eq hj']
    exact Subtype.ext hgw
  · have ho' : orderOf (⟨s, hs⟩ : fi22ExtS) = 2 := by rw [← Subgroup.orderOf_coe]; exact ho
    obtain ⟨j, hj, g, hg⟩ := hcov _ ho'
    rw [fi22ExtE_root_eq hj] at hg
    exact ⟨j, hj, g, g.2, congrArg Subtype.val hg⟩
  · rw [fi22ExtClassSize, ← fi22ExtCover_check.2.2.1 j hj, ← hcount j hj, fi22ExtE_root_eq hj]

end CFSG.Sporadic.FischerOddCore
