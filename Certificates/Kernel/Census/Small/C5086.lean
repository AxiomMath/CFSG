module

public import CFSG.GH74.GLS.C3.Prop121.CzCoordInputs
public import CFSG.Certificates.Kernel.PermCent.Ok122CSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelCensus

namespace C5086

open Equiv Equiv.Perm CFSG.GH74.GLS.C3.Prop121 CFSG.Certificates.Kernel.PkCV

@[expose] noncomputable def oddInvP : List (CV 7) :=
  ((allPermsP 7 inferInstance).filter fun x => x.2 && powOneC x.1 2).map Prod.fst

@[expose] noncomputable def odd7F : Bool :=
  forceCL ord3P fun O => forceCL oddInvP fun I => O.all fun a => I.any fun ρ => cmC ρ a

theorem odd7F_ok : odd7F = true := by quickRfl

theorem oddInv_eq : ((allPerms 7).filter fun ρ => decide (ρ * ρ = 1) && decide (sign ρ = -1)) =
    oddInvP.map ev := by
  unfold oddInvP
  rw [allPerms_eq 7 inferInstance, List.filter_map, List.map_map]
  refine congrArg₂ List.map rfl (List.filter_congr fun x hx => ?_)
  rw [Function.comp_apply, par_of_mem_allPermsP hx, powOneC_eq, pow_two]
  simp only [ev_mul', one_eq_ev, ev_eq_iff]
  exact Bool.and_comm _ _

theorem okOdd_hoist (n : ℕ) : okOdd n = (allPerms n).all fun σ =>
    !(decide (σ * σ * σ = 1 ∧ σ ≠ 1)) ||
      ((allPerms n).filter fun ρ => decide (ρ * ρ = 1) && decide (sign ρ = -1)).any
        fun ρ => decide (ρ * σ = σ * ρ) := by
  unfold okOdd
  simp only [List.any_filter, Bool.decide_and, Bool.and_assoc]

theorem okOdd7_ord3 : okOdd 7 = ord3.all fun σ => (oddInvP.map ev).any fun ρ =>
    decide (ρ * σ = σ * ρ) := by
  rw [okOdd_hoist, oddInv_eq, ord3, List.all_filter]

theorem okOdd7_eq : okOdd 7 = odd7F := by
  rw [okOdd7_ord3, ord3_eq, odd7F, forceCL_eq, forceCL_eq]
  simp only [List.all_map, List.any_map, Function.comp_def, ev_mul', ev_eq_iff, cmC_eq]

end C5086

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Prop121 in
open Subgroup Equiv Perm CFSG.GH74.GLS in
theorem check5086 : (okOdd 5 = true)
    ∧ (okOdd 6 = true)
    ∧ (okOdd 7 = true) := by
  refine ⟨?_, ?_, C5086.okOdd7_eq.trans C5086.odd7F_ok⟩
  all_goals decide +kernel

end CertificateChecks.KernelCensus
