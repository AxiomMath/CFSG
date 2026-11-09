module

public import Mathlib
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.CharacterTheory.Burnside
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutFusion
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverLiftClasses
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12Check
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12Data
public import CFSG.GH74.KGroups.TwoM12CheckInputs
import CFSG.Certificates.Kernel.PermCent.CVSound
import Certificates.Kernel.PermCent.K5131
public import Certificates.Data.Kernel.PermCent.CV

public section

open CFSG.GH74.KGroups CFSG.GH74.KGroups.TwoM12 CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.M12Cover CFSG.Certificates.Kernel.PkCV

namespace Certificates

theorem comm_mem_of_gens {G : Type*} [Group G] [Finite G] (E : Subgroup G) (S : Set G)
    (hN : ∀ s ∈ S, ∀ h ∈ E, s * h * s⁻¹ ∈ E)
    (hC : ∀ s ∈ S, ∀ t ∈ S, s * t * s⁻¹ * t⁻¹ ∈ E) :
    ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, a * b * a⁻¹ * b⁻¹ ∈ E := by
  have hS : Subgroup.closure S ≤ Subgroup.normalizer (E : Set G) := by
    rw [Subgroup.closure_le]
    intro s hs
    exact Subgroup.mem_normalizer_fintype (hN s hs)
  have hc : ∀ x ∈ Subgroup.closure S, ∀ h ∈ E, x * h * x⁻¹ ∈ E := fun x hx h hh =>
    (Subgroup.mem_normalizer_iff.1 (hS hx) h).1 hh
  have h1 : ∀ a ∈ Subgroup.closure S, ∀ t ∈ S, a * t * a⁻¹ * t⁻¹ ∈ E := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem x hx => exact hC x hx
    | one =>
      intro t _
      simp
    | mul x y hx hy ihx ihy =>
      intro t ht
      have e : x * y * t * (x * y)⁻¹ * t⁻¹ =
          x * (y * t * y⁻¹ * t⁻¹) * x⁻¹ * (x * t * x⁻¹ * t⁻¹) := by group
      rw [e]
      exact E.mul_mem (hc x hx _ (ihy t ht)) (ihx t ht)
    | inv x hx ihx =>
      intro t ht
      have e : x⁻¹ * t * x⁻¹⁻¹ * t⁻¹ = x⁻¹ * (x * t * x⁻¹ * t⁻¹)⁻¹ * x⁻¹⁻¹ := by group
      rw [e]
      exact hc _ (inv_mem hx) _ (E.inv_mem (ihx t ht))
  intro a ha b hb
  induction hb using Subgroup.closure_induction with
  | mem t ht => exact h1 a ha t ht
  | one => simp
  | mul y z hy hz ihy ihz =>
    have e : a * (y * z) * a⁻¹ * (y * z)⁻¹ =
        (a * y * a⁻¹ * y⁻¹) * (y * (a * z * a⁻¹ * z⁻¹) * y⁻¹) := by group
    rw [e]
    exact E.mul_mem ihy (hc y hy _ ihz)
  | inv y hy ihy =>
    have e : a * y⁻¹ * a⁻¹ * y⁻¹⁻¹ = y⁻¹ * (a * y * a⁻¹ * y⁻¹)⁻¹ * y⁻¹⁻¹ := by group
    rw [e]
    exact hc _ (inv_mem hy) _ (E.inv_mem ihy)

set_option compiler.extract_closed false in
open CFSG in
open CFSG.GH74 in
open CFSG.GH74.KGroups in
open CFSG.GH74.KGroups.TwoM12 in
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu in
open CFSG.ComponentClassification.M12Cover CFSG.Blueprint Subgroup in
open scoped commutatorElement in
theorem certificate5131 : commCheckOn fixedDQ.orbitTables (elemsT m12CentQ2) = true := by
  have e : ∀ L, commCheckOn fixedDQ.orbitTables L = L.all fun a => L.all fun b =>
      fixedDQ.sift (gzPerm * (a * b * a⁻¹ * b⁻¹) * gzPerm⁻¹) 0 := fun _ => rfl
  have hg : m12CentWords2.map (evalCodes [m12gA, m12gB]) =
      (m12CentWords2.map (evCodesB ([m12gA, m12gB].map cOf))).map ev := by
    have hev : ∀ w, ev (evCodesB ([m12gA, m12gB].map cOf) w) = evalCodes [m12gA, m12gB] w := by
      intro w
      induction w with
      | nil => rw [evCodesB, evalCodes, ev_one]
      | cons z w ih =>
        have h1 : (1 : CV 12) = cOf 1 := ev_injective (by rw [ev_cOf, ev_one])
        rw [evCodesB, evalCodes, ev_mul, ih, h1, List.getD_map, List.getD_map]
        split
        · rw [ev_cOf]
        · rw [ev_inv, ev_cOf]
    rw [List.map_map]
    exact List.map_congr_left fun w _ => (hev w).symm
  have hNP : (m12CentWords2.map (evalCodes [m12gA, m12gB])).all (fun s =>
      (elemsT fixedDQ).all fun d =>
        fixedDQ.sift (gzPerm * s * gzPerm⁻¹ * d * (gzPerm * s * gzPerm⁻¹)⁻¹) 0) = true := by
    rw [elemsT_eq_elemsC, eq_ev_cOf gzPerm, hg]
    simp only [List.all_map, Function.comp_def, ev_mul', ev_inv', sift_ev]
    exact K5131.k5131N
  have hGP : (m12CentWords2.map (evalCodes [m12gA, m12gB])).all (fun s =>
      (m12CentWords2.map (evalCodes [m12gA, m12gB])).all fun t =>
        fixedDQ.sift (gzPerm * (s * t * s⁻¹ * t⁻¹) * gzPerm⁻¹) 0) = true := by
    rw [eq_ev_cOf gzPerm, hg]
    simp only [List.all_map, Function.comp_def, ev_mul', ev_inv', sift_ev]
    exact K5131.k5131G
  let E : Subgroup (Equiv.Perm (Fin 12)) :=
    Subgroup.comap (MulAut.conj gzPerm).toMonoidHom fixedDQ.originalSubgroup
  have hE : ∀ x, x ∈ E ↔ gzPerm * x * gzPerm⁻¹ ∈ fixedDQ.originalSubgroup := fun x => by
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hcl : m12CentQ2.originalSubgroup =
      Subgroup.closure {g | g ∈ m12CentWords2.map (evalCodes [m12gA, m12gB])} := by
    rw [m12CentQ2, certificate_originalSubgroup]
  have hQ2 : ValidSchreier m12CentQ2 := m12_oddcore_cent2.1
  have hm := comm_mem_of_gens E {g | g ∈ m12CentWords2.map (evalCodes [m12gA, m12gB])}
    (fun s hs h hh => by
      rw [hE] at hh ⊢
      have hd := List.all_eq_true.1 (List.all_eq_true.1 hNP s hs) _
        ((mem_elemsT fixedDQ fixedDQ_valid _).2 hh)
      rw [← mem_iff_sift fixedDQ fixedDQ_valid] at hd
      have e2 : gzPerm * (s * h * s⁻¹) * gzPerm⁻¹ = gzPerm * s * gzPerm⁻¹ *
          (gzPerm * h * gzPerm⁻¹) * (gzPerm * s * gzPerm⁻¹)⁻¹ := by group
      rw [e2]
      exact hd)
    (fun s hs t ht => by
      rw [hE, mem_iff_sift fixedDQ fixedDQ_valid]
      exact List.all_eq_true.1 (List.all_eq_true.1 hGP s hs) t ht)
  rw [e, List.all_eq_true]
  intro a ha
  rw [List.all_eq_true]
  intro b hb
  rw [mem_elemsT m12CentQ2 hQ2, hcl] at ha hb
  have hab := hm a ha b hb
  rw [hE, mem_iff_sift fixedDQ fixedDQ_valid] at hab
  exact hab

end Certificates
