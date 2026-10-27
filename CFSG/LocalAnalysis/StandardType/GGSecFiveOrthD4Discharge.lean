module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthD4JoinType
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthD4Join
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthAInf
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthD4KStruct
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthWeylOrdD
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthCount

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint CFSG.LieType.Universal TauCeti CFSG.StandardType.OrthF3

theorem ggSecFiveOrthD4ExclInput_of_inputs
    (hFix : GGSecFiveFixInput) (hStruct : GGSecFiveOrthD4KStructInput) :
    GGSecFiveOrthD4ExclInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hsplit hC hp3 V _ _ Q hQ _ ι hd hA hD y K hnb hK8 hJcomp hJmodel hjoin
  subst hp3
  have S : GGOrthSetup B Bs x L D J 𝒦 Q ι := ⟨hcfg, hsplit, hC, hQ, Or.inr hd, hA⟩
  obtain ⟨hKB, hKfix, hKstar⟩ := hStruct G 3 B Bs x L D J 𝒦 hcfg hsplit hC rfl V Q hQ ι hd hA hD y K
    hnb hK8 hJcomp hJmodel
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hKinf : ggAutomizer K Bs ≤ ggAInf 3 B Bs x L D J :=
    ((le_iSup (fun _ : GGNbr 3 B x D J y K => ggAutomizer K Bs) hnb).trans
      (le_iSup₂ (f := fun (y : G) (K : Subgroup G) =>
        ⨆ (_ : GGNbr 3 B x D J y K), ggAutomizer K Bs) y K)).trans le_sup_right
  have hsup : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAInf 3 B Bs x L D J :=
    sup_le le_sup_left hKinf
  have hLcard : Nat.card ↥(ggAutomizer L Bs) = 192 := by
    obtain ⟨e, -⟩ := hD
    rw [← Nat.card_congr e.toEquiv, card_coxeterD_eq 4 le_rfl]
    norm_num [Nat.factorial]
  have h192 : 192 ∣ Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
    rw [← hLcard]
    exact Subgroup.card_dvd_of_le le_sup_left
  have hdvd : Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) ∣ 103680 := by
    have h1 : Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) ∣
        Nat.card ↥(ggAInf 3 B Bs x L D J) := Subgroup.card_dvd_of_le hsup
    rw [S.card_ggAInf, card_orthogonalGroup_of_finrank_eq_five Q S.nondeg hd] at h1
    exact h1
  rcases ggOrthD4_joinType hjoin h192 hdvd with h | h | h
  · exact ggOrthD4_rankFour_false S hFix hd hnb hKfix (Or.inl h)
  · exact ggOrthD4_rankFour_false S hFix hd hnb hKfix (Or.inr h)
  · exact ggOrthD4_b5_false S hd hnb hKinf hD hKB hKstar h

end CFSG.StandardType

end
