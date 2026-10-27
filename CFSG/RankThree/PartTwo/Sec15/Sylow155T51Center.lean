module

public import CFSG.RankThree.PartTwo.Sec4.Item41Narrow
public import CFSG.RankThree.PartTwo.Sec4.Census.Open46
import CFSG.RankThree.PartTwo.Sec4.Census.Cover46
import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThreeTools
import CFSG.RankThree.PartTwo.KFacts.KS12SLCenter
import CFSG.RankThree.PartTwo.KFacts.K72SLPiElems

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155T51

open CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts.OutFixCentralThree (centerThreePrime centerThreePrime_le_center
  not_three_dvd_card_centerThreePrime isPGroup_center_quotient_centerThreePrime
  mem_centerThreePrime)

private theorem card_center_of_isSLThreePiAt {X : Type} [Group X] {p e : ℕ} (hp : p.Prime)
    (he : 1 ≤ e) (hX : Sec4.IsSLThreePiAt X (p ^ e)) : Nat.card (Subgroup.center X) = 3 := by
  obtain ⟨K, _, _, ⟨hK, hq, ⟨φ⟩⟩ | ⟨hK, hq, ⟨φ⟩⟩⟩ := hX
  · have hK' : Sec4.PiField true p e K := ⟨hp, he, hK⟩
    rw [Nat.card_congr (Subgroup.centerCongr φ).toEquiv]
    exact KFacts.card_center_slPi (π := true) hK' hq
  · have hK' : Sec4.PiField false p e K := ⟨hp, he, hK⟩
    rw [Nat.card_congr (Subgroup.centerCongr φ).toEquiv]
    exact KFacts.card_center_slPi (π := false) hK' hq

theorem false_of_nine_dvd_card_center (h2 : Sec4.Item4_1ThreeCover) (h43 : Sec4.Item4_3)
    (hin : Sec4.Census.CoverInputs46) {X : Type} [Group X] [Finite X] (hX : SectionFourHyp X)
    (hq : CFSG.IsQuasisimple X) (hZ3 : IsPGroup 3 (Subgroup.center X))
    (h9 : 9 ∣ Nat.card (Subgroup.center X)) : False := by
  have h3 : 3 ∣ Nat.card (Subgroup.center X) := dvd_trans (by norm_num) h9
  have hZ : Subgroup.center X ≠ ⊥ := fun h0 => by
    rw [h0, Subgroup.card_bot] at h3
    norm_num at h3
  have hS : SectionFourHyp (X ⧸ Subgroup.center X) :=
    Sec4.Item41Narrow.sectionFourHyp_quotient_center_of_isPGroup h2 hX hq hZ3
  have hnd : ¬ Nat.card (Subgroup.center X) ∣ 3 := fun hd =>
    absurd (h9.trans hd) (by norm_num)
  have hcen := hin.centerThree X hq hZ3
  rcases h43 X hX hq h3 with ⟨p, e, _, he, hpi⟩ | hA6 | hA7 | hG2 | hU43 | hM22 | hJ3 | hMcL | hON
  ·
    have hmod : p ^ e % 3 = 1 ∨ p ^ e % 3 = 2 := by
      rcases hpi with ⟨h, -⟩ | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr h
    have hbd := Sec4.Census.two_or_le_two_of_isoLThreePi hS he hpi
    have hEps := hin.slThree X hq hZ3 hZ p e he hbd hpi
    have hc3 := card_center_of_isSLThreePiAt Fact.out he
      (KFacts.isSLThreePiAt_of_isSLThreeEpsAt he hEps hmod hZ)
    exact hnd (dvd_of_eq hc3)
  · exact hnd (hcen (Or.inl hA6))
  · exact hnd (hcen (Or.inr (Or.inl hA7)))
  · exact hnd (hcen (Or.inr (Or.inr (Or.inl hG2))))
  ·
    obtain ⟨f⟩ := hU43
    have h9' : Nat.card (Subgroup.center X) = 9 := Nat.dvd_antisymm (hin.u43 X hq hZ3 ⟨f⟩) h9
    have h4 := hin.u43Rank X hq h9' ⟨f⟩
    have h3' := Sec4.Census.SectionFourHyp.localRank_three_le hX
    omega
  · exact hnd (hcen (Or.inr (Or.inr (Or.inr (Or.inl hM22)))))
  · exact hnd (hcen (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hJ3))))))
  · exact hnd (hcen (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hMcL)))))))
  · exact hnd (hcen (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hON)))))))

theorem false_of_elemAbelian_le_center (h1 : Sec4.Item4_1LargePrime)
    (h2 : Sec4.Item4_1ThreeCover) (h43 : Sec4.Item4_3) (hin : Sec4.Census.CoverInputs46)
    {Y : Type} [Group Y] [Finite Y] (hY : SectionFourHyp Y) (hq : CFSG.IsQuasisimple Y)
    {B : Subgroup Y} (hB : CFSG.Assembly.IsElemAbelian 3 B) (hB9 : Nat.card B = 9)
    (hBZ : B ≤ Subgroup.center Y) : False := by
  obtain ⟨hqX, -, hcen⟩ := CFSG.LocalCores.quasisimple_central_quotient hq (centerThreePrime Y)
    centerThreePrime_le_center
  have hXhyp : SectionFourHyp (Y ⧸ centerThreePrime Y) :=
    Sec4.Item41Narrow.sectionFourHyp_quotient h1 hY (centerThreePrime Y)
      not_three_dvd_card_centerThreePrime hqX
  have hZ3 : IsPGroup 3 (Subgroup.center (Y ⧸ centerThreePrime Y)) :=
    isPGroup_center_quotient_centerThreePrime hq
  let f : B →* Y ⧸ centerThreePrime Y :=
    (QuotientGroup.mk' (centerThreePrime Y)).comp B.subtype
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxK : (x : Y) ∈ centerThreePrime Y :=
      (QuotientGroup.eq_one_iff (x : Y)).mp hx
    have hord : orderOf (x : Y) ∣ 3 := orderOf_dvd_of_pow_eq_one (hB.2 x x.2)
    rcases (Nat.dvd_prime Nat.prime_three).mp hord with h | h
    · exact Subtype.ext (orderOf_eq_one_iff.mp h)
    · exact absurd (dvd_of_eq h.symm) (mem_centerThreePrime.mp hxK).2
  have hle : f.range ≤ Subgroup.center (Y ⧸ centerThreePrime Y) := by
    rintro _ ⟨x, rfl⟩
    rw [hcen]
    exact ⟨(x : Y), hBZ x.2, rfl⟩
  have hcard : Nat.card f.range = 9 :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm.trans hB9
  exact false_of_nine_dvd_card_center h2 h43 hin hXhyp hqX hZ3
    (hcard ▸ Subgroup.card_dvd_of_le hle)

end CFSG.RankThree.PartTwo.Sec15.Sylow155T51
