module

public import Certificates.Data.P43Twin
import CFSG.Certificates.Kernel.ONanSmall.MapSound
import CFSG.Certificates.Kernel.ONanSmall.CoverSound
import CFSG.Certificates.Kernel.ONanSmall.CVGlue
import Certificates.Kernel.ONanSmall.P43T
public import Certificates.Data.Kernel.ONanSmall.P43Gen
public import Certificates.Data.Kernel.PermCent.CV

public section

namespace Certificates

open CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.ONanSmall CFSG.KC.ONanSmall
  CFSG.ClassicalInvolution.Q3.TA3.Check CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall
  Certificates.Kernel.ONanSmall Certificates.P43Twin Certificates.P43Gen

private theorem p43_check_eq : check () = checkG (elemsT PSp43.QP45) (elemsT PSp43.QA45) (tA ())
    (tB ()) (t36 ()) (t540 ()) (a1 ()) (b1 ()) (a2 ()) (b2 ()) (x1 ()) (x2 ()) := by
  have e1 : ∀ l m : List (Equiv.Perm (Fin 45)), setEqB l m = setEqG l m := fun _ _ => rfl
  have e2 : ∀ τ a b : Equiv.Perm (Fin 45), pairOK τ a b = pairOKG (tA ()) (Q1 ()) (Q2 ()) τ a b :=
    fun τ a b => by unfold pairOK pairOKG; rw [e1, e1]
  have e3 : ∀ (τ : Equiv.Perm (Fin 45)) C, pairChk τ C = pairChkG (tA ()) (Q1 ()) (Q2 ()) τ C :=
    fun τ C => by unfold pairChk pairChkG; simp only [e2]
  have e4 : ∀ L (τ : Equiv.Perm (Fin 45)), localChk L τ = localChkG (tA ()) (Q1 ()) (Q2 ()) L τ :=
    fun L τ => by unfold localChk localChkG; simp only [e3]
  have e5 : ∀ L Q : List (Equiv.Perm (Fin 45)), centQ L Q = centQG L Q := fun _ _ => rfl
  have e6 : ∀ L, sigmaChk L = sigmaChkG (Q1 ()) (Q2 ()) (a1 ()) (a2 ()) (x1 ()) (x2 ()) L :=
    fun L => by unfold sigmaChk sigmaChkG; simp only [e5]
  unfold check checkG
  simp only [e4, e6]
  rfl

theorem certificate397501 : P43Twin.check () = true := by
  have hm : ∀ L : List (CV 45), L.map ev = L.map (evHom 45) := fun _ => rfl
  have hc : ∀ σ : Equiv.Perm (Fin 45), σ = (evHom 45) (cOf σ) := fun σ => (ev_cOf σ).symm
  rw [p43_check_eq, elemsT_eq_elemsC, elemsT_eq_elemsC, hm, hm, hc (tA ()), hc (tB ()),
    hc (t36 ()), hc (t540 ()), hc (a1 ()), hc (b1 ()), hc (a2 ()), hc (b2 ()), hc (x1 ()),
    hc (x2 ()), p43_checkG_map (evHom 45) ev_injective]
  have hC0 : P43T.reps0.map (centB (elemsC PSp43.QP45)) = P43T.cents0 := by
    exact (map_centB_eq _ _).trans P43T.cent0_ok
  have hCA : P43T.repsA.map (centB (elemsC PSp43.QA45)) = P43T.centsA := by
    exact (map_centB_eq _ _).trans P43T.centA_ok
  unfold checkG
  simp only [Bool.and_eq_true, localChkG]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, P43T.sig⟩
  · exact coverB_of_pickRun _ invC conjC (genC PSp43.QP45) invC_eq conjC_eq (genC_mem PSp43.QP45)
      P43T.one0_mem _ _ P43T.cov0
  · rw [List.all_eq_true]
    intro τ hτ
    exact List.all_eq_true.1 (all_cent_of
      (fun τ C => noOddB 12 C && pairChkG (cOf (tA ())) P43T.Q1 P43T.Q2 τ C) hC0 P43T.loc0) τ hτ
  · exact coverB_of_pickRun _ invC conjC (genC PSp43.QA45) invC_eq conjC_eq (genC_mem PSp43.QA45)
      P43T.oneA_mem _ _ P43T.covA
  · rw [List.all_eq_true]
    intro τ hτ
    exact List.all_eq_true.1 (all_cent_of
      (fun τ C => noOddB 12 C && pairChkG (cOf (tA ())) P43T.Q1 P43T.Q2 τ C) hCA P43T.locA) τ hτ

end Certificates
