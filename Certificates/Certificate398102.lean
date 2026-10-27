module

public import Certificates.Kernel.OmegaEight.Bridge3009
public import Certificates.Kernel.OmegaEight.Curtis398102K
public import Certificates.Certificate3119

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight
  CFSG.Monster.B.Co2.Native CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6

theorem curtis_gen {i : Nat} (hi : i < 8) :
    pm (AP.S i) = true ∧ cn (pinv (AP.S i)) = true := by
  have hk := kCurtis
  simp only [bAnd_iff] at hk
  have h := allN_spec hk.1 i hi
  simp only [bAnd_iff] at h
  exact h

theorem cn_AP {i : Nat} (hi : i < 10) : cn (AP.S i) = true := by
  have h := kStrC
  simp only [bAnd_iff] at h
  exact allN_spec h.1 i hi

theorem curtis_letter (l : Fin 8 × Bool) :
    (if l.2 then genArrs[l.1.val]! else invCand 360 genArrs[l.1.val]!) =
      unpack 360 9 (curtisL l) ∧ cn (curtisL l) = true := by
  obtain ⟨⟨i, hi⟩, b⟩ := l
  obtain ⟨hp, hc⟩ := curtis_gen hi
  rw [gen_get (by omega)]
  cases b
  · exact ⟨invCand_pinv hp, hc⟩
  · exact ⟨rfl, cn_AP (by omega)⟩

theorem curtis_word (w : List (Fin 8 × Bool)) : ∀ acc, cn acc = true →
    w.foldl (fun a l => compA 360 a (if l.2 then genArrs[l.1.val]! else invCand 360 genArrs[l.1.val]!))
        (unpack 360 9 acc) = unpack 360 9 (curtisK acc w) ∧ cn (curtisK acc w) = true := by
  induction w with
  | nil => exact fun acc h => ⟨rfl, h⟩
  | cons l w ih =>
    intro acc h
    obtain ⟨el, cl⟩ := curtis_letter l
    rw [List.foldl_cons, el, compA_pc h cl]
    exact ih (pc acc (curtisL l)) (cn_pc h cl)

theorem curtisPerm_k : curtisPermCheck = true := by
  have hk := kCurtis
  simp only [bAnd_iff] at hk
  unfold curtisPermCheck
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨?_, fun w hw => ?_⟩
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro i hi
    obtain ⟨hp, -⟩ := curtis_gen hi
    rw [gen_get (by omega)]
    exact isInvA_of hp
  · obtain ⟨e, c⟩ := curtis_word w pid cn_pid
    unfold curtisWordArr
    rw [idA_eq, e, eqA_pc c cn_pid]
    exact List.all_eq_true.1 hk.2 w hw

end CertificateChecks.KernelO8

namespace Certificates

open CertificateChecks

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6 in
theorem certificate398102 : curtisPermCheck = true :=
  KernelO8.curtisPerm_k

end Certificates
