module

public import Certificates.Kernel.CoreD2K.Co3.Checks
public import Certificates.Kernel.CoreD2K.Co3.Bind
public import CFSG.Certificates.Kernel.CoreD2K.Sound
public import CFSG.Sporadic.Schreier.Co3Faithful

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCoreD2K.Co3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Open CFSG.KS.MaxD2 CFSG.KD.CoreD2K CFSG.ComponentClassification.PSL3Four
  CFSG.Sporadic.Schreier.Co3 CertificateChecks.KernelSpor Certificates.CoreD2Perm

theorem hyps : KHyps 276 9 co3LinesData GP GPI GT GTI RE.G RE.GI RE.T RE.PL RE.POS RE.SRT RE.SRI
    RE.cnt 125 125 where
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

theorem tab0 : TabRep (unpack 276 9 (GP 0)) (co3GenPerm 0) := by
  rw [Nat.eq_of_beq_eq_true gp0_eq]
  exact ⟨size_u _, CFSG.KS.Raw.Orb.rep_unpack
    (CFSG.KS.Raw.Orb.prep_PS Co3C.binds Co3C.perm (j := 0) (by norm_num)).1⟩

theorem tab1 : TabRep (unpack 276 9 (GP 1)) (co3GenPerm 1) := by
  rw [Nat.eq_of_beq_eq_true gp1_eq]
  exact ⟨size_u _, CFSG.KS.Raw.Orb.rep_unpack
    (CFSG.KS.Raw.Orb.prep_PS Co3C.binds Co3C.perm (j := 1) (by norm_num)).1⟩

theorem co3P_eq_pair :
    co3P = Subgroup.closure ({co3GenPerm 0, co3GenPerm 1} : Set (Equiv.Perm (Fin 276))) := by
  rw [co3P_eq]
  congr 1
  ext x
  simp only [Set.mem_range, Fin.exists_fin_two, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩

theorem exists_normalizer_gens_co3P :
    ∃ E : Subgroup ↥co3P, Nat.card E = 5 ^ 3 ∧
      ∀ A : Subgroup ↥co3P, A ≤ E → IsElemAbelian 5 A → Nat.card A = 5 ^ 2 →
        ∃ Γ : Set ↥co3P, Subgroup.closure Γ = ⊤ ∧ ∀ g ∈ Γ, ∃ Q, Q ≤ A ∧ Q ≠ ⊥ ∧
          g ∈ Subgroup.normalizer (Q : Set ↥co3P) := by
  rw [co3P_eq_pair]
  exact exists_normalizer_gens_of_kchecks hyps Nat.prime_five (by decide) tab0 tab1

end CertificateChecks.KernelCoreD2K.Co3

end
