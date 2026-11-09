module

public import CFSG.GH74.GLS.C3.Layer2.L5B0
public import CFSG.GH74.GLS.C3.Layer2.L5B2Inputs
import CFSG.Certificates.Kernel.PermCent.CVSound
meta import Mathlib.GroupTheory.SpecificGroups.Alternating
meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
meta import CFSG.GH74.GLS.C3.Layer2.L5A1
meta import CFSG.GH74.GLS.C3.Layer2.L5B2Inputs

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

namespace CertificateChecks.Batch5049

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem Wl_cover_chk_0 : allT5.all (fun t => Wl.any fun w => decide (evalW gT w = t)) = true := by
  decide +kernel

private theorem Rels_chk_1 : Rels.all (fun r => decide (evalW gT r = 1)) = true := by
  decide +kernel

private theorem gT_mem_chk_2 : T5b (gT 0) = true ∧ T5b (gT 1) = true ∧ T5b (gT 2) = true := by
  decide +kernel

private instance small9 : CFSG.Certificates.Kernel.PkCV.Small 9 := ⟨by decide⟩
private instance small54 : CFSG.Certificates.Kernel.PkCV.Small (5 + 4) := ⟨by decide⟩

private def evalWG {G : Type*} [Monoid G] (g : Fin 3 → G) (w : List (Fin 3)) : G :=
  w.foldl (fun a i => a * g i) 1

private def m27G {G H : Type*} [Group G] [Group H] (eqG : G → G → Bool) (eqH : H → H → Bool)
    (P Q T R : List G) (gT : Fin 3 → G) (f1 : G) (e : G → H) (a0 : H) : Bool :=
  P.all fun xa => Q.all fun xc => T.all fun xb =>
    !((Rels.all fun r => eqG (evalWG ![xa, xb, xc] r) 1) &&
      (Wl.all fun w => imp (P.any fun y => eqG (evalWG gT w) y)
          (Q.any fun y => eqG (evalWG ![xa, xb, xc] w) y) &&
        imp (Q.any fun y => eqG (evalWG gT w) y) (P.any fun y => eqG (evalWG ![xa, xb, xc] w) y) &&
        imp (eqG (evalWG gT w) f1) (!eqG (evalWG ![xa, xb, xc] w) f1)) &&
      (T.all fun t => (Wl.map (evalWG ![xa, xb, xc])).any fun y => eqG y t)) ||
    Wl.all fun w =>
      !(R.any fun y => eqG (evalWG gT w) y) ||
      !(eqG (evalWG ![xa, xb, xc] w) (evalWG gT w) &&
        (List.finRange 3).all fun i => Wl.any fun w' =>
          eqG (evalWG gT w') (![xa, xb, xc] i) &&
            eqG (evalWG ![xa, xb, xc] w') (evalWG gT w * gT i * (evalWG gT w)⁻¹)) ||
      T.any fun t₀ =>
        eqH (e (evalWG gT w)) (e t₀ * a0 * e t₀ * a0) &&
          (List.finRange 3).all fun i =>
            eqH (e (![xa, xb, xc] i)) (e t₀ * a0 * e (gT i) * a0⁻¹ * (e t₀)⁻¹)

set_option maxHeartbeats 400000 in
private theorem decide_mem_any {α : Type*} [DecidableEq α] (x : α) (L : List α)
    {inst : Decidable (x ∈ L)} : @decide (x ∈ L) inst = L.any fun y => decide (x = y) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, List.any_eq_true]
  simp only [decide_eq_true_eq, exists_eq_right']

set_option maxHeartbeats 400000 in
private theorem decide_ne_eq' {α : Type*} [DecidableEq α] (a b : α) {inst : Decidable (a ≠ b)} :
    @decide (a ≠ b) inst = !decide (a = b) := by
  by_cases h : a = b <;> simp [h]

private theorem evalW_eq : evalW = evalWG (G := Amb 5) := by
  funext g w
  rfl

set_option maxHeartbeats 400000 in
private theorem main27_eq_G : main27 = m27G (fun a b => decide (a = b)) (fun a b => decide (a = b))
    Pml Qml allT5 Rml gT f1 (emb 5) (a0perm 5) := by
  simp only [main27, candChk, xChk, uChk, gensRel, m27G, evalW_eq, decide_mem_any, decide_ne_eq']

set_option maxHeartbeats 400000 in
private theorem evalWG_map {G G' : Type*} [Monoid G] [Monoid G'] (φ : G →* G') (g : Fin 3 → G)
    (w : List (Fin 3)) : evalWG (fun i => φ (g i)) w = φ (evalWG g w) := by
  unfold evalWG
  suffices h : ∀ (acc : G), w.foldl (fun a i => a * φ (g i)) (φ acc) =
      φ (w.foldl (fun a i => a * g i) acc) by
    rw [← h 1, map_one]
  induction w with
  | nil => intro acc; rfl
  | cons i w ih =>
    intro acc
    simp only [List.foldl_cons]
    rw [← map_mul]
    exact ih (acc * g i)

set_option maxHeartbeats 400000 in
private theorem m27G_map {G H G' H' : Type*} [Group G] [Group H] [Group G'] [Group H']
    (eqG : G → G → Bool) (eqH : H → H → Bool) (eqG' : G' → G' → Bool) (eqH' : H' → H' → Bool)
    (φ : G →* G') (ψ : H →* H') (hG : ∀ a b, eqG' (φ a) (φ b) = eqG a b)
    (hH : ∀ a b, eqH' (ψ a) (ψ b) = eqH a b)
    (P Q T R : List G) (gT : Fin 3 → G) (f1 : G) (e : G → H) (e' : G' → H')
    (he : ∀ a, e' (φ a) = ψ (e a)) (a0 : H) :
    m27G eqG' eqH' (P.map φ) (Q.map φ) (T.map φ) (R.map φ) (fun i => φ (gT i)) (φ f1) e' (ψ a0) =
      m27G eqG eqH P Q T R gT f1 e a0 := by
  have hx : ∀ xa xb xc : G, (![φ xa, φ xb, φ xc] : Fin 3 → G') = fun i => φ (![xa, xb, xc] i) := by
    intro xa xb xc
    funext i
    fin_cases i <;> rfl
  unfold m27G
  simp only [List.all_map, List.any_map, List.map_map, Function.comp_def, hx, evalWG_map,
    ← map_mul, ← map_inv, ← map_one φ, hG, he, hH]

set_option maxHeartbeats 400000 in
private theorem φ_eq (a b : Amb 5) :
    decide (CFSG.Certificates.Kernel.PkCV.cOf (emb 5 a) = CFSG.Certificates.Kernel.PkCV.cOf (emb 5 b)) =
      decide (a = b) := by
  by_cases h : a = b
  · subst h
    simp
  · have h' : CFSG.Certificates.Kernel.PkCV.cOf (emb 5 a) ≠ CFSG.Certificates.Kernel.PkCV.cOf (emb 5 b) :=
      fun e => h (emb_injective 5 (by
        rw [← CFSG.Certificates.Kernel.PkCV.ev_cOf (emb 5 a), e, CFSG.Certificates.Kernel.PkCV.ev_cOf]))
    simp [h, h']

private noncomputable def cOfHom : Equiv.Perm (Fin 9) →* CFSG.Certificates.Kernel.PkCV.CV 9 where
  toFun := CFSG.Certificates.Kernel.PkCV.cOf
  map_one' := CFSG.Certificates.Kernel.PkCV.ev_injective (by
    rw [CFSG.Certificates.Kernel.PkCV.ev_cOf, CFSG.Certificates.Kernel.PkCV.ev_one])
  map_mul' a b := CFSG.Certificates.Kernel.PkCV.ev_injective (by
    rw [CFSG.Certificates.Kernel.PkCV.ev_mul, CFSG.Certificates.Kernel.PkCV.ev_cOf,
      CFSG.Certificates.Kernel.PkCV.ev_cOf, CFSG.Certificates.Kernel.PkCV.ev_cOf])

set_option maxHeartbeats 400000 in
private theorem cOf_eq (a b : Equiv.Perm (Fin 9)) :
    decide (cOfHom a = cOfHom b) = decide (a = b) := by
  by_cases h : a = b
  · subst h
    simp
  · have h' : cOfHom a ≠ cOfHom b := fun e => h (by
      rw [← CFSG.Certificates.Kernel.PkCV.ev_cOf a, ← CFSG.Certificates.Kernel.PkCV.ev_cOf b]
      exact congrArg CFSG.Certificates.Kernel.PkCV.ev e)
    simp [h, h']

set_option maxHeartbeats 400000 in
private theorem main27_eq_C : main27 = m27G (fun a b => decide (a = b)) (fun a b => decide (a = b))
    (Pml.map (cOfHom.comp (emb 5))) (Qml.map (cOfHom.comp (emb 5)))
    (allT5.map (cOfHom.comp (emb 5))) (Rml.map (cOfHom.comp (emb 5)))
    (fun i => cOfHom.comp (emb 5) (gT i)) (cOfHom.comp (emb 5) f1) id (cOfHom (a0perm 5)) := by
  rw [main27_eq_G, m27G_map _ _ _ _ (cOfHom.comp (emb 5)) cOfHom (by intro a b; exact φ_eq a b) cOf_eq]
  intro a
  rfl

private theorem main27C_true : m27G (fun a b => decide (a = b)) (fun a b => decide (a = b))
    (Pml.map (cOfHom.comp (emb 5))) (Qml.map (cOfHom.comp (emb 5)))
    (allT5.map (cOfHom.comp (emb 5))) (Rml.map (cOfHom.comp (emb 5)))
    (fun i => cOfHom.comp (emb 5) (gT i)) (cOfHom.comp (emb 5) f1) id (cOfHom (a0perm 5)) = true := by
  decide +kernel

private theorem main27_true_3 : main27 = true := by
  rw [main27_eq_C]
  exact main27C_true

private theorem nm_id_chk_4 : allT5.all (fun t => imp (decide (t * t = 1)) (imp (decide (t ≠ 1))
    (decide (nmE t = 8 ↔ (t ∈ Rml ∧ t ∉ Pml ∧ t ∉ Qml))))) = true := by
  decide +kernel

private theorem a0_conj_PQ_chk_5 : Pml.all (fun p => Qml.any fun q =>
    decide (a0perm 5 * emb 5 p * (a0perm 5)⁻¹ = emb 5 q)) = true := by
  decide +kernel

private theorem a0_conj_QP_chk_6 : Qml.all (fun q => Pml.any fun p =>
    decide (a0perm 5 * emb 5 q * (a0perm 5)⁻¹ = emb 5 p)) = true := by
  decide +kernel

end CertificateChecks.Batch5049

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Layer2 in
open CFSG.GH74.GLS.C3.Layer2.L5 in
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model in
theorem certificate5049 : (allT5.all (fun t => Wl.any fun w => decide (evalW gT w = t)) = true)
    ∧ (Rels.all (fun r => decide (evalW gT r = 1)) = true)
    ∧ (T5b (gT 0) = true ∧ T5b (gT 1) = true ∧ T5b (gT 2) = true)
    ∧ (main27 = true)
    ∧ (allT5.all (fun t => imp (decide (t * t = 1)) (imp (decide (t ≠ 1))
    (decide (nmE t = 8 ↔ (t ∈ Rml ∧ t ∉ Pml ∧ t ∉ Qml))))) = true)
    ∧ (Pml.all (fun p => Qml.any fun q =>
    decide (a0perm 5 * emb 5 p * (a0perm 5)⁻¹ = emb 5 q)) = true)
    ∧ (Qml.all (fun q => Pml.any fun p =>
    decide (a0perm 5 * emb 5 q * (a0perm 5)⁻¹ = emb 5 p)) = true) := by
  exact ⟨CertificateChecks.Batch5049.Wl_cover_chk_0, CertificateChecks.Batch5049.Rels_chk_1, CertificateChecks.Batch5049.gT_mem_chk_2, CertificateChecks.Batch5049.main27_true_3, CertificateChecks.Batch5049.nm_id_chk_4, CertificateChecks.Batch5049.a0_conj_PQ_chk_5, CertificateChecks.Batch5049.a0_conj_QP_chk_6⟩

end Certificates
