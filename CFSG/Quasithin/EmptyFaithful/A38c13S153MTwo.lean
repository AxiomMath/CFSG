module

public import CFSG.Quasithin.EmptyFaithful.A38c13S1565B
public import CFSG.Quasithin.Background.F918C8
public import CFSG.Quasithin.EmptyFaithful.S153MC1d
public import CFSG.Quasithin.EmptyFaithful.S153MTwoE

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.S1565

namespace S153M

section Two

attribute [local instance] commGroupOfFact

theorem noStrongTwo_holdsC (hA21 : AsA21SQTKSection) (h56 : AsB56)
    (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) : Input15365NoStrongFFTwoC := by
  intro G _ _ T Mc M V₁ V₂ H K t D hK0 I hV₁I hIU W hW hirr hne hs
  have hn := D.n_gt
  obtain ⟨hker, n, hn2, hKs, hB⟩ := e22CasesW_one_data D.e22 hn hK0
  obtain ⟨hn3, hnodd⟩ := D.n_odd n hn2 (hKs.elim Or.inl fun h => Or.inr (Or.inl h)) hB
  have hIT := isIrrPlusTildeT_of_ambient D.hF hIU W hW hirr
  have hI := isIrrPlusTilde_of_module D.hF hV₁I hIU hIT
  have hWK := D.hF.tilde_commutator_conjClosure hIU hI
  have hW0 := tildeOf_conjClosure_ne_bot D.hF hIU hI
  exact noStrong_two_of_hyp hA21 h56 hA37 hA38 D.hF (H ⊓ M) D.H_eq D.sqtk hK0 hker hn3 hnodd hKs hB
    hIU hWK hW0 hs

theorem eltTwo_holdsC (hA21 : AsA21SQTKSection) (h56 : AsB56)
    (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hNS : Input15365NoStrongFFTwoC) :
    Input15365FFnatEltTwoC := by
  intro G _ _ T Mc M V₁ V₂ H K t D hK0 I hV₁I hIU W hW hirr hne hFF
  have hn := D.n_gt
  obtain ⟨hker, n, hn2, hKs, hB⟩ := e22CasesW_one_data D.e22 hn hK0
  obtain ⟨hn3, hnodd⟩ := D.n_odd n hn2 (hKs.elim Or.inl fun h => Or.inr (Or.inl h)) hB
  have hIT := isIrrPlusTildeT_of_ambient D.hF hIU W hW hirr
  have hI := isIrrPlusTilde_of_module D.hF hV₁I hIU hIT
  have hWK := D.hF.tilde_commutator_conjClosure hIU hI
  have hTM : T ≤ M := by
    have hmem : H ⊓ M ∈ maxOver H T := by
      rw [D.minPar.uniqueMax]
      exact Set.mem_singleton _
    exact hmem.2.trans inf_le_right
  have hEFF : IsFFInt (tildeOf (conjClosure I H) (conjClosure K T ⊔ T))
      (tildeOf (conjClosure I H) (conjClosure (ZS153 T M V₁) H))
      (D.hF.isElemAbelian_quotient (conjClosure I H)) := by
    rcases hFF with ⟨-, hE⟩ | hs | hs
    · exact hE
    · exact (hNS G T Mc M V₁ V₂ H K t D hK0 I hV₁I hIU W hW hirr hne hs).elim
    · exact F9.IsStrongFFInt.isFFInt hs
  exact eltTwo_of_E_ff hA21 h56 hA37 hA38 D.hF M D.H_eq D.sqtk hK0 hTM hker hn3 hnodd hKs hB hV₁I
    hIU hWK hne hEFF

theorem eltTwo_unconditionalC (hA21 : AsA21SQTKSection) (h56 : AsB56)
    (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) : Input15365FFnatEltTwoC :=
  eltTwo_holdsC hA21 h56 hA37 hA38 (noStrongTwo_holdsC hA21 h56 hA37 hA38)

end Two

end S153M

end CFSG.Quasithin
