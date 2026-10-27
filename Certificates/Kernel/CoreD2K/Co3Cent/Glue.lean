module

public import Certificates.Kernel.CoreD2K.Co3Cent.Checks
public import Certificates.Kernel.CoreD2K.Co3.Glue
public import CFSG.Certificates.Kernel.CoreD2K.Cent
public import CFSG.Certificates.Kernel.CoreD2K.Parts

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCoreD2K.Co3Cent

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Open CFSG.KS.MaxD2 CFSG.KS.CoreD2K CFSG.KD.CoreD2K
  CFSG.Sporadic.Schreier.Co3 Certificates.CoreD2Perm
open CertificateChecks.KernelCoreD2K.Co3 (GP GPI)

theorem eW_eq : co3CentK.base.eW = co3LinesData.base.eW := rfl

theorem hyps : KHypsC 276 9 co3CentK co3CentReps co3CentSteps GP GPI GT GTI Co3.RE.G Co3.RE.GI Co3.RE.T Co3.RE.PL
    Co3.RE.POS Co3.RE.SRT Co3.RE.SRI Co3.RE.cnt 125 125 where
  hn := Co3.k_sz
  hgp := gensK_perm Co3.k_gens
  hE := by
    rw [eW_eq]
    exact gensK_eW Co3.k_gens
  hG := fun j hj => PK.allN_iff.1 k_g j hj
  hh := Co3.k_eh
  hsl := by
    rw [eW_eq, ← Nat.eq_of_beq_eq_true Co3.k_ek]
    exact Co3.k_esl
  hlen := by rw [Nat.eq_of_beq_eq_true Co3.k_ecnt]
  hcnt := by
    rw [Nat.eq_of_beq_eq_true Co3.k_ecnt]
    rfl
  hnab := by
    rw [eW_eq]
    exact Co3.k_nab
  hcen := by
    rw [eW_eq]
    exact Co3.k_cen
  hlines := by
    rw [linesK_congr (V := co3CentK) (V' := co3LinesData) rfl (congrArg List.length eW_eq)]
    exact Co3.k_lines
  hkinds := k_kinds
  hreps := by
    intro i hi
    simp only [co3CentReps, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact k_rep1
    · exact k_rep3
  hsteps := List.all_eq_true.1 k_steps
  hchain := k_chain

theorem exists_cent_gens_co3P :
    ∃ E : Subgroup ↥co3P, Nat.card E = 5 ^ 3 ∧
      ∀ A : Subgroup ↥co3P, A ≤ E → IsElemAbelian 5 A → Nat.card A = 5 ^ 2 →
        ∃ Γ : Set ↥co3P, Subgroup.closure Γ = ⊤ ∧ ∀ g ∈ Γ, ∃ y ∈ A, y ≠ 1 ∧ g * y = y * g := by
  rw [Co3.co3P_eq_pair]
  exact exists_cent_gens_of_kchecks hyps Nat.prime_five (by decide) (by decide) Co3.tab0 Co3.tab1

end CertificateChecks.KernelCoreD2K.Co3Cent

end
