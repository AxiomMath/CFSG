module

public import Certificates.Kernel.CoreD2K.Co2.Checks
public import Certificates.Kernel.CoreD2K.Co2.Bind
public import Certificates.Kernel.Sporadic.Co2.Order
public import CFSG.Certificates.Kernel.CoreD2K.Sound
public import CFSG.Certificates.Kernel.CoreD2K.Parts

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCoreD2K.Co2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.CoreD2K CFSG.KD.CoreD2K
  CFSG.Open
  CFSG.ComponentClassification.PSL3Four CFSG.Sporadic.Co2Cert CFSG.Monster.B.Co2
  CertificateChecks.KernelSpor Certificates.CoreD2Perm

theorem hyps : KHyps 2300 12 co2LinesData GP GPI GT GTI RE.G RE.GI RE.T RE.PL RE.POS RE.SRT
    RE.SRI RE.cnt 125 125 where
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

theorem perm_gp : allN (nat_lit 2)
    (fun j => permOK 2300 12 (mask 12) (Nat.mul 2300 12) (GP j) (GPI j)) = true :=
  gensK_perm k_gens

theorem tab_gp {j : Nat} (hj : j < 2) {P : Nat} (hP : co2OrigArrs[j]! = unpack 2300 12 P)
    (hb : Nat.beq (GP j) P = true) : TabRep (unpack 2300 12 (GP j)) (co2Gen j) := by
  have hperm : invEqK 2300 12 (mask 12) (2300 * 12) (GP j) (GPI j) = true :=
    PK.allN_iff.1 perm_gp j hj
  rw [co2Gen, hP, ← Nat.eq_of_beq_eq_true hb]
  exact ⟨size_u _, (rep_permOfArr (invEqK_sound hperm).2).1⟩

theorem tab0 : TabRep (unpack 2300 12 (GP 0)) (co2Gen 0) :=
  tab_gp (by norm_num) (Co2Order.a_eq 0 (by norm_num)) gp0_eq

theorem tab1 : TabRep (unpack 2300 12 (GP 1)) (co2Gen 1) :=
  tab_gp (by norm_num) (Co2Order.a_eq 1 (by norm_num)) gp1_eq

theorem exists_normalizer_gens_co2P :
    ∃ E : Subgroup ↥co2P, Nat.card E = 5 ^ 3 ∧
      ∀ A : Subgroup ↥co2P, A ≤ E → IsElemAbelian 5 A → Nat.card A = 5 ^ 2 →
        ∃ Γ : Set ↥co2P, Subgroup.closure Γ = ⊤ ∧ ∀ g ∈ Γ, ∃ Q, Q ≤ A ∧ Q ≠ ⊥ ∧
          g ∈ Subgroup.normalizer (Q : Set ↥co2P) :=
  exists_normalizer_gens_of_kchecks hyps Nat.prime_five (by decide) tab0 tab1

end CertificateChecks.KernelCoreD2K.Co2

end
