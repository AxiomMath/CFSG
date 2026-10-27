module

public import Certificates.Kernel.Bounds.HS.Rels
public import Certificates.Kernel.Bounds.HS.Facts
public import CFSG.Certificates.Kernel.HSKillSound
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Checks.B_H_0
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Checks.Pair
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Data.M
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelHS

open CFSG.KC CFSG.KC.LceS CFSG.KC.HOrb CFSG.KC.HSK CFSG.Certificates CFSG.Certificates.LCE
  CertificateChecks.KernelCo2

noncomputable abbrev HB : Subgroup (PresentedGroup P.relatorSet) :=
  Subgroup.closure ((fun j => bval tg (wWord (CFSG.KD.HSKB.selST j)) (wLen (CFSG.KD.HSKB.selST j))) ''
    {j | j < nat_lit 5})

theorem bray_walk : ∃ rep : ℕ → PresentedGroup P.relatorSet, rep 0 = 1 ∧
    ∀ w x R y, x < 2 ^ 20 → walkTo CFSG.KD.HSKB.blk (nat_lit 62354) w x R y = true →
      rep x * bval tg (wWord w) (wLen w) * (rep y)⁻¹ ∈ HB := by
  have h := factsOk_intro (nR := nat_lit 13) (nS := nat_lit 5) (nf := nat_lit 62354)
    CFSG.KD.HSKB.sH1 CFSG.KD.HSKB.sH0 (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)
    (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) Bfacts
  exact HO.walkTo_sound tg HB h (fun r hr => rel_val r hr)
    (fun j hj => Subgroup.subset_closure ⟨j, hj, rfl⟩)

theorem a_cent : ∀ x ∈ HB, x * tg 0 = tg 0 * x := by
  have hle : HB ≤ Subgroup.centralizer {tg 0} := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, -, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact (bray_cent j).symm
  intro x hx
  exact (Subgroup.mem_centralizer_iff.mp (hle hx) (tg 0) rfl).symm

theorem pi_rel : ∀ r < 87, bval (fun k => bval tg (wWord (HSK.gen (k + 1))) (wLen (HSK.gen (k + 1))))
    (wWord (CFSG.KD.HSKM.XRs r)) (wLen (CFSG.KD.HSKM.XRs r)) = 1 := by
  obtain ⟨rep, h0, hw⟩ := bray_walk
  have hsub : ∀ j, HO.entOK (HSK.subB j) (nat_lit 4) (nat_lit 18) = true ∧
      bval tg (wWord (HSK.subB j)) (wLen (HSK.subB j)) ∈ HB := by
    intro j
    by_cases hj : j < 5
    · refine ⟨by interval_cases j <;> quickRfl, Subgroup.subset_closure ⟨j, hj, rfl⟩⟩
    · rw [subB_ge (by omega), bval_zero]
      exact ⟨by quickRfl, HB.one_mem⟩
  have key := fun {XRk i j m w R1 c ρ hl hn R2 : ℕ}
      (hargs : HSKill.pairArgsOK (nat_lit 30) w hn m = true)
      (h : pairOK CFSG.KD.HSKB.blk HSK.gen HSK.subB (nat_lit 30) (nat_lit 62354) XRk i j m w R1 c ρ hl
        hn R2 = true) =>
    HSKill.pairOK_sound tg HB rep h0 hw hsub a_cent a_sq (by quickRfl) (by decide) root_val hargs h
  intro r hr
  interval_cases r
  · exact key (by quickRfl) CFSG.KD.HSKM.pr0
  · exact key (by quickRfl) CFSG.KD.HSKM.pr1
  · exact key (by quickRfl) CFSG.KD.HSKM.pr2
  · exact key (by quickRfl) CFSG.KD.HSKM.pr3
  · exact key (by quickRfl) CFSG.KD.HSKM.pr4
  · exact key (by quickRfl) CFSG.KD.HSKM.pr5
  · exact key (by quickRfl) CFSG.KD.HSKM.pr6
  · exact key (by quickRfl) CFSG.KD.HSKM.pr7
  · exact key (by quickRfl) CFSG.KD.HSKM.pr8
  · exact key (by quickRfl) CFSG.KD.HSKM.pr9
  · exact key (by quickRfl) CFSG.KD.HSKM.pr10
  · exact key (by quickRfl) CFSG.KD.HSKM.pr11
  · exact key (by quickRfl) CFSG.KD.HSKM.pr12
  · exact key (by quickRfl) CFSG.KD.HSKM.pr13
  · exact key (by quickRfl) CFSG.KD.HSKM.pr14
  · exact key (by quickRfl) CFSG.KD.HSKM.pr15
  · exact key (by quickRfl) CFSG.KD.HSKM.pr16
  · exact key (by quickRfl) CFSG.KD.HSKM.pr17
  · exact key (by quickRfl) CFSG.KD.HSKM.pr18
  · exact key (by quickRfl) CFSG.KD.HSKM.pr19
  · exact key (by quickRfl) CFSG.KD.HSKM.pr20
  · exact key (by quickRfl) CFSG.KD.HSKM.pr21
  · exact key (by quickRfl) CFSG.KD.HSKM.pr22
  · exact key (by quickRfl) CFSG.KD.HSKM.pr23
  · exact key (by quickRfl) CFSG.KD.HSKM.pr24
  · exact key (by quickRfl) CFSG.KD.HSKM.pr25
  · exact key (by quickRfl) CFSG.KD.HSKM.pr26
  · exact key (by quickRfl) CFSG.KD.HSKM.pr27
  · exact key (by quickRfl) CFSG.KD.HSKM.pr28
  · exact key (by quickRfl) CFSG.KD.HSKM.pr29
  · exact key (by quickRfl) CFSG.KD.HSKM.pr30
  · exact key (by quickRfl) CFSG.KD.HSKM.pr31
  · exact key (by quickRfl) CFSG.KD.HSKM.pr32
  · exact key (by quickRfl) CFSG.KD.HSKM.pr33
  · exact key (by quickRfl) CFSG.KD.HSKM.pr34
  · exact key (by quickRfl) CFSG.KD.HSKM.pr35
  · exact key (by quickRfl) CFSG.KD.HSKM.pr36
  · exact key (by quickRfl) CFSG.KD.HSKM.pr37
  · exact key (by quickRfl) CFSG.KD.HSKM.pr38
  · exact key (by quickRfl) CFSG.KD.HSKM.pr39
  · exact key (by quickRfl) CFSG.KD.HSKM.pr40
  · exact key (by quickRfl) CFSG.KD.HSKM.pr41
  · exact key (by quickRfl) CFSG.KD.HSKM.pr42
  · exact key (by quickRfl) CFSG.KD.HSKM.pr43
  · exact key (by quickRfl) CFSG.KD.HSKM.pr44
  · exact key (by quickRfl) CFSG.KD.HSKM.pr45
  · exact key (by quickRfl) CFSG.KD.HSKM.pr46
  · exact key (by quickRfl) CFSG.KD.HSKM.pr47
  · exact key (by quickRfl) CFSG.KD.HSKM.pr48
  · exact key (by quickRfl) CFSG.KD.HSKM.pr49
  · exact key (by quickRfl) CFSG.KD.HSKM.pr50
  · exact key (by quickRfl) CFSG.KD.HSKM.pr51
  · exact key (by quickRfl) CFSG.KD.HSKM.pr52
  · exact key (by quickRfl) CFSG.KD.HSKM.pr53
  · exact key (by quickRfl) CFSG.KD.HSKM.pr54
  · exact key (by quickRfl) CFSG.KD.HSKM.pr55
  · exact key (by quickRfl) CFSG.KD.HSKM.pr56
  · exact key (by quickRfl) CFSG.KD.HSKM.pr57
  · exact key (by quickRfl) CFSG.KD.HSKM.pr58
  · exact key (by quickRfl) CFSG.KD.HSKM.pr59
  · exact key (by quickRfl) CFSG.KD.HSKM.pr60
  · exact key (by quickRfl) CFSG.KD.HSKM.pr61
  · exact key (by quickRfl) CFSG.KD.HSKM.pr62
  · exact key (by quickRfl) CFSG.KD.HSKM.pr63
  · exact key (by quickRfl) CFSG.KD.HSKM.pr64
  · exact key (by quickRfl) CFSG.KD.HSKM.pr65
  · exact key (by quickRfl) CFSG.KD.HSKM.pr66
  · exact key (by quickRfl) CFSG.KD.HSKM.pr67
  · exact key (by quickRfl) CFSG.KD.HSKM.pr68
  · exact key (by quickRfl) CFSG.KD.HSKM.pr69
  · exact key (by quickRfl) CFSG.KD.HSKM.pr70
  · exact key (by quickRfl) CFSG.KD.HSKM.pr71
  · exact key (by quickRfl) CFSG.KD.HSKM.pr72
  · exact key (by quickRfl) CFSG.KD.HSKM.pr73
  · exact key (by quickRfl) CFSG.KD.HSKM.pr74
  · exact key (by quickRfl) CFSG.KD.HSKM.pr75
  · exact key (by quickRfl) CFSG.KD.HSKM.pr76
  · exact key (by quickRfl) CFSG.KD.HSKM.pr77
  · exact key (by quickRfl) CFSG.KD.HSKM.pr78
  · exact key (by quickRfl) CFSG.KD.HSKM.pr79
  · exact key (by quickRfl) CFSG.KD.HSKM.pr80
  · exact key (by quickRfl) CFSG.KD.HSKM.pr81
  · exact key (by quickRfl) CFSG.KD.HSKM.pr82
  · exact key (by quickRfl) CFSG.KD.HSKM.pr83
  · exact key (by quickRfl) CFSG.KD.HSKM.pr84
  · exact key (by quickRfl) CFSG.KD.HSKM.pr85
  · exact key (by quickRfl) CFSG.KD.HSKM.pr86

end CertificateChecks.KernelHS

end
