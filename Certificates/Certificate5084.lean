module

public import CFSG.GH74.GLS.C3.Prop121.CentK7Inputs
import CFSG.Certificates.Kernel.PermCent.CentK6CSound
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.Assembly.ComponentTypeDefs
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Prop121
open Subgroup Equiv Perm CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer2.Model

namespace CertificateChecks.Batch5084

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Prop121
open Subgroup Equiv Perm CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer2.Model

section Generic

variable {G : Type*} [Group G] [DecidableEq G]

private def gWG (a1 a2 c : G) : Bool :=
  decide (c * a1 = a1 * c ∧ c ≠ 1 ∧ c ≠ a1 ∧ c ≠ a2 ∧ c ≠ a1 * a2)

private def wWG (a1 a2 β : G) : Bool := gWG a1 a2 (β * a2 * β⁻¹ * a1 * a2 * β)

private def oBG (a1 a2 τ b : G) : Bool := wWG a1 a2 b || wWG a1 a2 (b * τ) || wWG a1 a2 (b * τ⁻¹)

private def cEG (E : List G) (τ : G) : List G :=
  E.filter fun b => b * τ = τ * b ∧ b ≠ 1 ∧ b ≠ τ ∧ b ≠ τ⁻¹

private def oPG (C : List G) (τ a1 a2 : G) : Bool :=
  if (τ * a1 * τ⁻¹ = a2 ∨ τ * a1 * τ⁻¹ = a1 * a2) ∧
      (τ * a2 * τ⁻¹ = a1 ∨ τ * a2 * τ⁻¹ = a2 ∨ τ * a2 * τ⁻¹ = a1 * a2) then
    C.all fun b => oBG a1 a2 τ b
  else true

private def oTCG (I C : List G) (τ : G) : Bool :=
  I.all fun a1 => I.all fun a2 => if a1 * a2 = a2 * a1 ∧ a1 ≠ a2 then oPG C τ a1 a2 else true

private def oTG (I E : List G) (τ : G) : Bool := oTCG I (cEG E τ) τ

private theorem oTG_map {H : Type*} [Group H] [DecidableEq H] (f : H → G)
    (hmul : ∀ a b, f (a * b) = f a * f b) (hinv : ∀ a, f a⁻¹ = (f a)⁻¹) (hone : f 1 = 1)
    (hf : Function.Injective f) (I E : List H) (t : H) :
    oTG (I.map f) (E.map f) (f t) = oTG I E t := by
  simp only [oTG, oTCG, oPG, oBG, wWG, gWG, cEG, List.all_map, List.filter_map,
    Function.comp_def, ← hmul, ← hinv, ← hone, ne_eq, hf.eq_iff]

end Generic

private theorem okTau7_eq (τ : Perm (Fin 7)) : okTau7 τ = oTG inv7 even7 τ := rfl

open CFSG.Certificates.Kernel.PkCV in
private theorem even7_eq : even7 = (evenP (allPermsP 7 inferInstance)).map ev := by
  unfold even7
  exact evenP_eq 7 inferInstance

set_option maxHeartbeats 0 in
open CFSG.Certificates.Kernel.PkCV in
private theorem okSearch7_true_0 : okSearch7 = true := by
  rw [okSearch7, okTau7_eq, okTau7_eq, inv7_eq, even7_eq, ← ev_cOf tauA7, ← ev_cOf tauB7,
    oTG_map ev ev_mul ev_inv ev_one ev_injective, oTG_map ev ev_mul ev_inv ev_one ev_injective]
  decide +kernel

end CertificateChecks.Batch5084

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Prop121 in
open Subgroup Equiv Perm CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer2.Model in
theorem certificate5084 : okSearch7 = true := by
  exact CertificateChecks.Batch5084.okSearch7_true_0

end Certificates

