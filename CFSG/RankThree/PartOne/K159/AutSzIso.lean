module

public import CFSG.RankThree.PartOne.K159.AutSzModel
public import CFSG.RankThree.PartOne.K159.AutSzRow
public import CFSG.RankThree.PartOne.CTP.SeitzExcModels

public section

namespace CFSG.RankThree.PartOne.K159.SzAbs

open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem szSylow_of_isoLie
    {S : Type} [Group S] (hiso : IsoLie S (.suzuki 2)) : SzSylow S := by
  obtain ⟨-, a, -, F, _, _, hfa, hF, ⟨e⟩⟩ := CFSG.RankThree.PartOne.CTP.suzukiModel_of_isoLie 2 hiso
  have ha2 : a = 2 := by omega
  subst ha2
  have hF' : Nat.card F = 2 ^ (2 * 2 + 1) := by rw [hF, hfa]
  exact SzSylow.of_mulEquiv e (szSylow_model hF')

theorem not_sLike_of_isoLie_suzuki
    {H : Type} [Group H] [Finite H] {S : Subgroup H} (hS : S.Normal) (hsimple : IsSimpleGroup ↥S)
    (hiso : IsoLie ↥S (.suzuki 2)) (hC : Subgroup.centralizer (S : Set H) = ⊥) {P : Subgroup H}
    (hP : CFSG.RankThree.PartOne.IsSylowOf 5 P ⊤)
    (hΩel : CFSG.IsElementaryAbelian 5 (CFSG.RankThree.PartOne.omegaOne 5 P))
    (hΩ : Nat.card (CFSG.RankThree.PartOne.omegaOne 5 P) = 5 ^ 2) :
    ¬ (Nat.card ↥(CFSG.RankThree.PartOne.torusImage (CFSG.RankThree.PartOne.omegaOne 5 P) S) ∣ 24 ∧
      ∀ g ∈ CFSG.RankThree.PartOne.torusImage (CFSG.RankThree.PartOne.omegaOne 5 P) S,
        orderOf g ≤ 4) := by
  rintro ⟨-, hord⟩
  exact sz_row hS (szSylow_of_isoLie hiso) hsimple hC hP hΩel (by simpa using hΩ) hord

end CFSG.RankThree.PartOne.K159.SzAbs
