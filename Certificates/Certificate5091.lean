
module

public import Certificates.Certificate5091Base
import all Certificates.Certificate5091Base

public import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public import CFSG.GH74.GLS.C3.Layer2.NumMoved
public import CFSG.GH74.GLS.C3.Layer2.FinModelCard
public import Mathlib.Data.List.FinRange
public import Mathlib.GroupTheory.Perm.Fin
public import CFSG.GH74.GLS.C3.Prop121.ModelFiveInputs
import CFSG.GH74.GLS.C3.Prop121.ModelFiveBase
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveBase
meta import Mathlib.GroupTheory.SpecificGroups.Alternating
meta import Mathlib.GroupTheory.Perm.Fin
meta import Mathlib.Logic.Equiv.Fin.Basic
meta import Mathlib.Logic.Equiv.Option
meta import Mathlib.Data.List.FinRange
meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveInputs

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Prop121
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

namespace CertificateChecks.Batch5091

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Prop121
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

set_option maxRecDepth 100000

end CertificateChecks.Batch5091

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Prop121 in
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model in
theorem certificate5091 : (allT5.length = 32 ∧ allT5.Nodup)
    ∧ (T5b e1 = true ∧ T5b e2 = true ∧ T5b f1 = true ∧ T5b f2 = true ∧
    T5b (e1 * f1) = true ∧ T5b (e2 * f1) = true ∧ T5b (e1 * e2) = true ∧
    T5b (f1 * f2) = true)
    ∧ (e1 * e1 = 1 ∧ e2 * e2 = 1 ∧ (e1 * f1) * (e1 * f1) = 1 ∧ (e2 * f1) * (e2 * f1) = 1 ∧
    (e1 * e2) * (e1 * e2) = 1)
    ∧ (f1 * f1 = 1)
    ∧ (e1 ≠ 1 ∧ e2 ≠ 1 ∧ e1 * f1 ≠ 1 ∧ e2 * f1 ≠ 1 ∧ e1 * e2 ≠ 1)
    ∧ (f1 ≠ 1 ∧ f2 ≠ 1 ∧ f1 * f2 ≠ 1 ∧ e1 ≠ f1 ∧ e1 ≠ e2)
    ∧ (e1 ≠ f2 ∧ f1 ≠ f2)
    ∧ (f2 * e2 = e2 * f2 ∧ f2 * (e1 * e2) = (e1 * e2) * f2 ∧
    f1.1 = 1 ∧ f2.1 = 1 ∧ (f1 * f2).1 = 1)
    ∧ (e1.2 = 1 ∧ e2.2 = 1 ∧ (e1 * e2).2 = 1)
    ∧ ((((swap (1 : Fin 5) 2, swap (0 : Fin 4) 1) : Amb 5).2 * x4 =
        x4 * ((swap (1 : Fin 5) 2, swap (0 : Fin 4) 1) : Amb 5).2 ∧
      sign ((swap (1 : Fin 5) 2, swap (0 : Fin 4) 1) : Amb 5).1 =
        sign ((swap (1 : Fin 5) 2, swap (0 : Fin 4) 1) : Amb 5).2) ∧
    ((swap (1 : Fin 5) 2, swap (0 : Fin 4) 1) : Amb 5) * e1 *
        ((swap (1 : Fin 5) 2, swap (0 : Fin 4) 1) : Amb 5)⁻¹ = e2 ∧
    ((swap (1 : Fin 5) 2, swap (0 : Fin 4) 1) : Amb 5) * (e1 * f1) *
      ((swap (1 : Fin 5) 2, swap (0 : Fin 4) 1) : Amb 5)⁻¹ = e2 * f1)
    ∧ ((((swap (1 : Fin 5) 3, swap (0 : Fin 4) 1) : Amb 5).2 * x4 =
        x4 * ((swap (1 : Fin 5) 3, swap (0 : Fin 4) 1) : Amb 5).2 ∧
      sign ((swap (1 : Fin 5) 3, swap (0 : Fin 4) 1) : Amb 5).1 =
        sign ((swap (1 : Fin 5) 3, swap (0 : Fin 4) 1) : Amb 5).2) ∧
    ((swap (1 : Fin 5) 3, swap (0 : Fin 4) 1) : Amb 5) * e1 *
        ((swap (1 : Fin 5) 3, swap (0 : Fin 4) 1) : Amb 5)⁻¹ = e1 * e2)
    ∧ (∀ t ∈ allT5, e1 * t = t * e1)
    ∧ (∀ u ∈ allT5, (∀ s ∈ allT5, u * s = s * u) →
    u = 1 ∨ u = e1 ∨ u = f1 ∨ u = e1 * f1)
    ∧ (∀ q ∈ allT5, q.1 = 1 → q = 1 ∨ q = f1 ∨ q = f2 ∨ q = f1 * f2)
    ∧ (∀ u₁ ∈ [e1, e1 * f1], ∀ w ∈ allT5, W1P u₁ w)
    ∧ (∀ w ∈ [e2, e1 * e2], ∀ u ∈ allT5, U1P w u)
    ∧ (∀ q' ∈ [1, f1, f2, f1 * f2], ∃ v' ∈ [1, e1, e2, e1 * e2],
    a0perm 5 * emb 5 q' * (a0perm 5)⁻¹ = emb 5 v')
    ∧ (∀ v' ∈ [1, e1, e2, e1 * e2], T5b v' = true ∧ v'.2 = 1)
    ∧ (nmE f1 = 4) := by
  exact ⟨CertificateChecks.Batch5091.allT5_facts_0, CertificateChecks.Batch5091.elt_mem_1, CertificateChecks.Batch5091.elt_invol_2, CertificateChecks.Batch5091.f1_sq_3, CertificateChecks.Batch5091.elt_ne_4, CertificateChecks.Batch5091.elt_ne'_5, CertificateChecks.Batch5091.elt_ne''_6, CertificateChecks.Batch5091.elt_misc_7, CertificateChecks.Batch5091.elt_misc'_8, CertificateChecks.Batch5091.conj_e1_e2_9, CertificateChecks.Batch5091.conj_e1_e12_10, CertificateChecks.Batch5091.e1_central_11, CertificateChecks.Batch5091.center_T5_12, CertificateChecks.Batch5091.Q0_T5_13, CertificateChecks.Batch5091.W1_14, CertificateChecks.Batch5091.U1_15, CertificateChecks.Batch5091.a0_conj_Q0_16, CertificateChecks.Batch5091.V1_facts_17, CertificateChecks.Batch5091.nmE_f1_18⟩

end Certificates
