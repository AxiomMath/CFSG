module

public import CFSG.GH74.GLS.C3.Prop121.Card7SylInputs
import Certificates.Kernel.Card7Syl.Checks
import CFSG.Certificates.Kernel.PermCent.ForceCVSound

public section

open CFSG.Certificates.Kernel.PkCV CFSG.GH74.GLS.C3.Prop121.Card7.Syl Certificates.Kernel.Card7Syl

namespace Certificates

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Prop121 in
open CFSG.GH74.GLS.C3.Prop121.Card7 in
open CFSG.GH74.GLS.C3.Prop121.Card7.Syl in
open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Prop121.Card7.HC in
theorem certificate5083 : (decide (SL.length = 128) = true)
    ∧ (decide SL.Nodup = true)
    ∧ ((SL.all fun σ => decide (sign σ = 1)) = true)
    ∧ (decide ((1 : P11) ∈ SL) = true)
    ∧ ((SL.all fun a => SL.all fun b => decide (a * b ∈ SL)) = true)
    ∧ ((SL.all fun a => decide (a⁻¹ ∈ SL)) = true)
    ∧ (decide (SL.countP (fun σ => decide (σ * σ = 1 ∧ σ ≠ 1 ∧ numMoved σ = 4)) = 14) = true) := by
  obtain ⟨h1, h2, h3⟩ := groupF_perm SL sl_groupF
  refine ⟨sl_length, decide_eq_true h1, ?_, sl_one, h2, h3, sl_count⟩
  rw [List.all_eq_true]
  intro σ h
  unfold SL at h
  exact (List.mem_filter.1 h).2

end Certificates
