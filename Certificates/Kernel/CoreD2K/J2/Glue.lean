module

public import Certificates.Kernel.CoreD2K.J2.Checks
public import Certificates.Kernel.CoreD2K.J2.Bind
public import CFSG.Certificates.Kernel.CoreD2K.Sound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCoreD2K.J2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Open CFSG.KS.MaxD2 CFSG.KD.CoreD2K CFSG.ComponentClassification.PSL3Four
  CFSG.Sporadic.Schreier CertificateChecks.KernelSpor Certificates.CoreD2Perm

theorem hyps : KHyps 315 9 j2LinesData GP GPI GT GTI RE.G RE.GI RE.T RE.PL RE.POS RE.SRT RE.SRI
    RE.cnt 27 27 where
  hn := k_sz
  hgens := k_gens
  hh := k_eh
  hsl := by
    rw [← Nat.eq_of_beq_eq_true k_ek]
    exact k_esl
  hlen := by rw [Nat.eq_of_beq_eq_true k_ecnt]
  hcnt := by
    rw [Nat.eq_of_beq_eq_true k_ecnt]
    rfl
  hnab := k_nab
  hcen := k_cen
  hlines := k_lines
  hkinds := k_kinds
  hwords := k_words

theorem tab0 : TabRep (unpack 315 9 (GP 0)) (j2Gen 0) := by
  rw [Nat.eq_of_beq_eq_true gp0_eq]
  exact ⟨size_u _, CFSG.KS.Raw.Orb.rep_unpack
    (CFSG.KS.Raw.Orb.prep_PS J2PC.bindsP J2PC.permP (j := 0) (by norm_num)).1⟩

theorem tab1 : TabRep (unpack 315 9 (GP 1)) (j2Gen 1) := by
  rw [Nat.eq_of_beq_eq_true gp1_eq]
  exact ⟨size_u _, CFSG.KS.Raw.Orb.rep_unpack
    (CFSG.KS.Raw.Orb.prep_PS J2PC.bindsP J2PC.permP (j := 1) (by norm_num)).1⟩

theorem exists_normalizer_gens_j2P :
    ∃ E : Subgroup ↥j2P, Nat.card E = 3 ^ 3 ∧
      ∀ A : Subgroup ↥j2P, A ≤ E → IsElemAbelian 3 A → Nat.card A = 3 ^ 2 →
        ∃ Γ : Set ↥j2P, Subgroup.closure Γ = ⊤ ∧ ∀ g ∈ Γ, ∃ Q, Q ≤ A ∧ Q ≠ ⊥ ∧
          g ∈ Subgroup.normalizer (Q : Set ↥j2P) :=
  exists_normalizer_gens_of_kchecks hyps Nat.prime_three (by decide) tab0 tab1

end CertificateChecks.KernelCoreD2K.J2

end
