module

public import Certificates.Kernel.CoreD2K.Co2Cent.Checks
public import Certificates.Kernel.CoreD2K.Co2.Glue
public import CFSG.Certificates.Kernel.CoreD2K.Cent

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCoreD2K.Co2Cent

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Open CFSG.KS.MaxD2 CFSG.KS.CoreD2K CFSG.KD.CoreD2K
  CFSG.Sporadic.Co2Cert Certificates.CoreD2Perm
open CertificateChecks.KernelCoreD2K.Co2 (GP GPI)

theorem eW_eq : co2CentK.base.eW = co2LinesData.base.eW := rfl

theorem hyps : KHypsC 2300 12 co2CentK co2CentReps co2CentSteps GP GPI GT GTI Co2.RE.G Co2.RE.GI Co2.RE.T
    Co2.RE.PL Co2.RE.POS Co2.RE.SRT Co2.RE.SRI Co2.RE.cnt 125 125 where
  hn := Co2.k_sz
  hgp := gensK_perm Co2.k_gens
  hE := by
    rw [eW_eq]
    exact gensK_eW Co2.k_gens
  hG := fun j hj => PK.allN_iff.1 k_g j hj
  hh := Co2.k_eh
  hsl := by
    rw [eW_eq, ← Nat.eq_of_beq_eq_true Co2.k_ek]
    exact Co2.k_esl
  hlen := by rw [Nat.eq_of_beq_eq_true Co2.k_ecnt]
  hcnt := by
    rw [Nat.eq_of_beq_eq_true Co2.k_ecnt]
    rfl
  hnab := by
    rw [eW_eq]
    exact Co2.k_nab
  hcen := by
    rw [eW_eq]
    exact Co2.k_cen
  hlines := by
    rw [linesK_congr (V := co2CentK) (V' := co2LinesData) rfl (congrArg List.length eW_eq)]
    exact Co2.k_lines
  hkinds := k_kinds
  hreps := by
    intro i hi
    simp only [co2CentReps, List.mem_cons, List.not_mem_nil, or_false] at hi
    rw [hi]
    exact k_rep4
  hsteps := List.all_eq_true.1 k_steps
  hchain := k_chain

theorem exists_cent_gens_co2P :
    ∃ E : Subgroup ↥co2P, Nat.card E = 5 ^ 3 ∧
      ∀ A : Subgroup ↥co2P, A ≤ E → IsElemAbelian 5 A → Nat.card A = 5 ^ 2 →
        ∃ Γ : Set ↥co2P, Subgroup.closure Γ = ⊤ ∧ ∀ g ∈ Γ, ∃ y ∈ A, y ≠ 1 ∧ g * y = y * g :=
  exists_cent_gens_of_kchecks hyps Nat.prime_five (by decide) (by decide) Co2.tab0 Co2.tab1

end CertificateChecks.KernelCoreD2K.Co2Cent

end
