module

public import CFSG.Blueprint.Catalog
public import CFSG.Foundations.Catalog
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.RankThree.PartTwo.Sec16.Item167StepsProofNonsolv
import CFSG.RankThree.PartTwo.Sec16.Item167StepsProofComp
import CFSG.RankThree.PartTwo.Sec16.Item16KFactsProofNoSz

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

open CFSG CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

section Cert113


theorem exists_orderOf_eq_five_of_suzukiModel {T : Type} [Group T] {n : ℕ}
    (hT : CFSG.Blueprint.SuzukiModel T 2 n) : ∃ t : T, orderOf t = 5 := by
  have h5 := Sec16.KSL3PiNoSzProof.five_dvd_card_of_suzukiModel hT
  obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := hT
  haveI : Finite (CFSG.Blueprint.suzukiGroup a K) := (CFSG.LieType.Ree.suzuki_simple (K := K) ha hK).1
  haveI : Finite T := Finite.of_equiv _ e.symm.toEquiv
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact exists_prime_orderOf_dvd_card' 5 h5

end Cert113

section CertSzComp


theorem suzukiModel_of_isComponent {Y : Type} [Group Y] [Finite Y] (hKY : CFSG.IsKGroup Y)
    (h3 : ¬ 3 ∣ Nat.card Y) (h2 : CFSG.pCore 2 Y = ⊥) {K : Subgroup Y} (hK : IsComponent K) :
    ∃ n, CFSG.Blueprint.SuzukiModel ↥K 2 n := by
  have hz := (Sec16.suzuki_component_facts hKY h3 h2 hK).1
  have : Group.IsPerfect K := hK.1.1
  have : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hK.1.2.1
  obtain ⟨f, hSz⟩ := KFacts.KS14.suzukiModel_of_isKGroup_section hKY h3 K (Subgroup.center K)
    hK.1.2.2
  have e : ↥K ≃* (↥K ⧸ Subgroup.center K) :=
    (QuotientGroup.quotientBot (G := ↥K)).symm.trans (QuotientGroup.quotientMulEquivOfEq hz.symm)
  exact ⟨f, Sec16.suzukiModel_of_mulEquiv e hSz⟩

theorem isComponent_map_eq_of_suzuki {Y : Type} [Group Y] [Finite Y] (hKY : CFSG.IsKGroup Y)
    (h3 : ¬ 3 ∣ Nat.card Y) (h2 : CFSG.pCore 2 Y = ⊥)
    (h5 : CFSG.Open.pRank 5 (⊤ : Subgroup Y) ≤ 2) (σ : MulAut Y) (hσ : σ ^ 3 = 1)
    {K : Subgroup Y} (hK : IsComponent K) : K.map σ.toMonoidHom = K :=
  Sec16.Comp167.map_eq_of_isComponent h5
    (fun K hK => ⟨(Sec16.suzuki_component_facts hKY h3 h2 hK).1,
      (Sec16.suzuki_component_facts hKY h3 h2 hK).2.1⟩) (n := 1) (by simpa using hσ) hK

end CertSzComp

end CFSG.RankThree.PartTwo.Sec18.Item187Proof
