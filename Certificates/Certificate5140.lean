
module

public import Certificates.Certificate5140Base
import all Certificates.Certificate5140Base

public import CFSG.GH74.KGroups.L34TablesBase
public import CFSG.GH74.Uniqueness.SU.KI1r4L34ModelInputs
import CFSG.Certificates.Kernel.PermCent.CVSound
import Certificates.Kernel.PermCent.K5140
import Certificates.Kernel.PermCent.K5140Side

public section

open CFSG.GH74.Uniqueness.SU.K.R4.L34M CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups
  CFSG.GH74.KGroups.L34 CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkCV.L34Mod
  CFSG.Certificates.Kernel.PkEnum

namespace CertificateChecks.Batch5140

open CFSG.GH74.Uniqueness.SU.K.R4.L34M CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups
  CFSG.GH74.KGroups.L34 CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkCV.L34Mod
  CFSG.Certificates.Kernel.PkEnum

end CertificateChecks.Batch5140

namespace Certificates

open CertificateChecks.Batch5140

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.Uniqueness in
open CFSG.GH74.Uniqueness.SU in
open CFSG.GH74.Uniqueness.SU.K in
open CFSG.GH74.Uniqueness.SU.K.R4 in
open CFSG.GH74.Uniqueness.SU.K.R4.L34M in
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups CFSG.GH74.KGroups.L34 in
local notation "Pm" => Equiv.Perm (Fin 42)

theorem certificate5140 : (s0list.length = 64)
    ∧ (s0list.Nodup)
    ∧ ((1 : Equiv.Perm (Fin 42)) ∈ s0list)
    ∧ (modelCheck (elemsT QA) (elemsT QP) = true)
    ∧ (y0 ^ 3 = 1)
    ∧ ((s0list.all fun a => s0list.all fun b => decide (a * b ∈ s0list)) = true)
    ∧ ((s0list.all fun a => decide (a⁻¹ ∈ s0list)) = true)
    ∧ ((s0list.all fun g => QP.sift g 0) = true)
    ∧ (QP.sift y0 0 = true)
    ∧ ((s0list.all fun s => decide (y0 * s * y0⁻¹ ∈ s0list)) = true)
    ∧ ((s0list.all fun s => !decide (y0 * s = s * y0) || decide (s = 1)) = true) := by
  have hk := kSide
  unfold sideC at hk
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hk
  obtain ⟨hNd, h1, hgS, hy3, hmul, hinv, hsift, hys, hyn, hyf⟩ := hk
  simp only [List.all_eq_true, decide_eq_true_eq] at hgS hmul hinv hyn
  have cOf_mem : ∀ x ∈ s0list, cOf x ∈ sC := fun x hx => by
    rw [← s0_map]
    exact List.mem_map.2 ⟨x, hx, rfl⟩
  have mem_of_cOf : ∀ x, cOf x ∈ sC → x ∈ s0list := fun x hx => by
    rw [← s0_map] at hx
    obtain ⟨t, ht, e⟩ := List.mem_map.1 hx
    rwa [cOf_injective e] at ht
  have hone : (1 : Pm) ∈ s0list := mem_of_cOf 1 (by rw [cOf_one']; exact h1)
  have hmulP : ∀ a ∈ s0list, ∀ b ∈ s0list, a * b ∈ s0list := fun a ha b hb =>
    mem_of_cOf _ (by rw [cOf_mul]; exact hmul _ (cOf_mem a ha) _ (cOf_mem b hb))
  have hinvP : ∀ a ∈ s0list, a⁻¹ ∈ s0list := fun a ha =>
    mem_of_cOf _ (by rw [cOf_inv]; exact hinv _ (cOf_mem a ha))
  have hsub : ∀ s ∈ s0gens, s ∈ s0list := fun s hs =>
    mem_of_cOf s (hgS _ (by unfold gS; exact List.mem_map.2 ⟨s, hs, rfl⟩))
  have hcl : ∀ x ∈ s0list, x ∈ Subgroup.closure {s | s ∈ s0gens} := by
    have := bfs_mem s0gens (Subgroup.closure {s | s ∈ s0gens})
      (fun s hs => Subgroup.subset_closure hs) 200 [1] [1]
      (by simp [Subgroup.one_mem]) (by simp [Subgroup.one_mem])
    unfold s0list
    exact this
  have hC : ∀ g : Pm, (s0list.all fun s => decide (g * s = s * g)) =
      s0gens.all fun s => decide (g * s = s * g) := by
    intro g
    rw [Bool.eq_iff_iff]
    simp only [List.all_eq_true, decide_eq_true_eq]
    refine ⟨fun h s hs => h s (hsub s hs), fun h s hs => ?_⟩
    have : Commute g s := by
      refine Subgroup.closure_induction (p := fun x _ => Commute g x) (fun x hx => h x hx)
        (Commute.one_right g) (fun x y _ _ hx hy => hx.mul_right hy)
        (fun x _ hx => hx.inv_right) (hcl s hs)
    exact this
  have hN : ∀ g : Pm, (s0list.all fun s => decide (g * s * g⁻¹ ∈ s0list)) =
      s0gens.all fun s => decide (g * s * g⁻¹ ∈ s0list) := by
    intro g
    rw [Bool.eq_iff_iff]
    simp only [List.all_eq_true, decide_eq_true_eq]
    refine ⟨fun h s hs => h s (hsub s hs), fun h s hs => ?_⟩
    refine Subgroup.closure_induction (p := fun x _ => g * x * g⁻¹ ∈ s0list) (fun x hx => h x hx)
      (by rw [mul_one, mul_inv_cancel]; exact hone)
      (fun x y _ _ hx hy => by
        have e : g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
        rw [e]
        exact hmulP _ hx _ hy)
      (fun x _ hx => by
        have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
        rw [e]
        exact hinvP _ hx) (hcl s hs)
  have hG : ∀ c : CV 42, ([PA, PB, sg0, sg1, sg2].all fun a =>
      QP.sift (a * ev c * a⁻¹ * (ev c)⁻¹) 0) =
        ([PA, PB, sg0, sg1, sg2].map cOf).all fun a => siftC QP (a * c * a⁻¹ * c⁻¹) 0 := by
    intro c
    rw [List.all_map]
    simp only [Function.comp_def, ← sift_ev, ev_mul, ev_inv, ev_cOf]
  have cOf_ev : ∀ c : CV 42, cOf (ev c) = c := fun c => ev_injective (ev_cOf _)
  have hM : modelCheck (elemsT QA) (elemsT QP) = modelC (elemsC QA) (elemsC QP) sC gS := by
    unfold modelCheck modelC gA gS
    simp only [hC, hN]
    rw [elemsT_eq_elemsC, elemsT_eq_elemsC, List.all_map]
    simp only [hG, List.all_map, List.filter_map, List.length_map, Function.comp_def,
      decide_comm_ev, comm_fast, decide_mem_ev, decide_conj_mem_ev, s0_map, ev_pow', one_eq_ev,
      decide_ev_eq, pow_fast, sift_ev, ev_mul', cOf_ev]
  refine ⟨?_, ?_, hone, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← List.length_map (f := cOf), s0_map]
    exact kS
  · rw [← List.nodup_map_iff cOf_injective, s0_map]
    exact hNd
  · rw [hM]
    exact kScan
  · have h := congrArg ev (of_decide_eq_true ((powOneC_eq _ _).symm.trans hy3))
    rwa [← ev_pow', ev_cOf, ev_one] at h
  · simp only [List.all_eq_true, decide_eq_true_eq]
    exact hmulP
  · simp only [List.all_eq_true, decide_eq_true_eq]
    exact hinvP
  · simp only [List.all_eq_true]
    intro s hs
    rw [← ev_cOf s, sift_ev]
    exact List.all_eq_true.1 hsift _ (cOf_mem s hs)
  · rw [← ev_cOf y0, sift_ev]
    exact hys
  · simp only [List.all_eq_true, decide_eq_true_eq]
    intro s hs
    exact mem_of_cOf _ (by rw [cOf_mul, cOf_mul, cOf_inv]; exact hyn _ (cOf_mem s hs))
  · simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      decide_eq_true_eq]
    intro s hs
    have h := List.all_eq_true.1 hyf _ (cOf_mem s hs)
    simp only [Bool.or_eq_true, Bool.not_eq_true', eq22C_eq, decide_eq_false_iff_not,
      decide_eq_true_eq] at h
    rcases h with h | h
    · left
      intro e
      apply h
      rw [← cOf_mul, e, cOf_mul]
    · right
      exact cOf_injective (h.trans cOf_one'.symm)

end Certificates
