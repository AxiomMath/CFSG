module

public import CFSG.CGT.Stroth77.NonSplit.StrothTInputs
import Certificates.Kernel.Stroth77.MnsChecks
import Certificates.Kernel.Stroth77.MnsUniqChecks
import Certificates.Kernel.Stroth77.MnsBfsChecks
import CFSG.Certificates.Kernel.Stroth77.MnsNorm
import CFSG.Certificates.Kernel.Stroth77.MnsUniq

public section

open CFSG.KC.Stroth77MN CertificateChecks.KernelMns778702 CertificateChecks.KernelMnsU778702
  CertificateChecks.KernelMnsB778702

namespace Certificates

open CFSG.CGT.Stroth77 in
theorem certificate778702 : StrothRel mnsX1 mnsY1 mnsUV mnsT mnsX mnsY mnsU mnsW
    ∧ StrothRhoRel mnsX1 mnsY1 mnsUV mnsT mnsX mnsY mnsW mnsU mnsRho
    ∧ Stroth21Rel mnsW mnsX mnsY mnsUV mnsT mnsU mnsRho
    ∧ Eg = Qns
    ∧ Nat.card Tg = 256
    ∧ Nat.card Ag = 32
    ∧ Nat.card Lg = 24
    ∧ (∀ g : Mns, g ∈ Ag ↔ g ∈ bfsList gensA 60)
    ∧ (∀ g : Mns, g ∈ Lg ↔ g ∈ bfsList gensL 40)
    ∧ IsMulCommutative Ag
    ∧ (∀ g ∈ Ag, g * g * g * g = 1)
    ∧ Nat.card {g : Mns // g ∈ Ag ∧ g * g = 1} = 8
    ∧ (∀ B : Subgroup Mns, B ≤ Tg → IsMulCommutative B → Nat.card B = 32 → B = Ag)
    ∧ Lg ⊓ Ag = ⊥
    ∧ Ag ⊔ Lg = NAg := by
  obtain ⟨r1, r2, r3⟩ := rels_of ch778702_rel
  exact ⟨r1, r2, r3, Eg_eq_Qns_of ch778702_tab ch778702_cl, card_Tg ch778702_tab,
    card_Ag ch778702_tab ch778702_cl ch778702_a, card_Lg_of ch778702b_bfs,
    mem_Ag_bfs ch778702b_bfs, mem_Lg_bfs ch778702b_bfs, Ag_commutative_of ch778702b_bfs,
    Ag_exponent_of ch778702b_bfs, Ag_involutions_of ch778702b_bfs,
    Ag_unique ch778702_tab ch778702_cl ch778702_a ch778702u_red ch778702u_cen ch778702u_pair,
    Lg_inf_Ag_of ch778702b_bfs,
    Ag_sup_Lg_of ch778702_tab ch778702_cl ch778702_a ch778702_na ch778702b_bfs⟩

end Certificates
