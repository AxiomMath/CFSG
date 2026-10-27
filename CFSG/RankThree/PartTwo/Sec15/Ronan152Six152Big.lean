module

public import CFSG.RankThree.PartTwo.Sec15.Ronan152SixBigDefs
public import CFSG.RankThree.PartTwo.Sec17.RouteForms
import CFSG.RankThree.PartOne.N143.CaseB1Theta
import CFSG.RankThree.PartTwo.Sec15.F153L3C2Quot
import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal

public section

namespace CFSG.RankThree.PartTwo.Sec15.Ronan152Six

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem not_big152_of_sl25
    {A : Subgroup G} {LB : Subgroup G → Subgroup G} {Y X : Subgroup G}
    (hY : Y ∈ scriptY4 A LB) (hYX : Y ≤ X)
    (hXq : IsQuasisimple (↥X ⧸ aschbacherSolvableCore 3 ↥X)) (hsl : Sec15.IsSL25Case X) :
    ¬ Big152 Y := by
  intro hbig
  have h60 : Nat.card (↥X ⧸ aschbacherSolvableCore 3 ↥X) = 60 := by
    rcases hsl with he | he
    · obtain ⟨e⟩ := he
      exact (sl25_theta hXq e).1
    · obtain ⟨e⟩ := he
      exact (sl25_theta hXq e).1
  set θ := aschbacherSolvableCore 3 ↥X with hθdef
  have hθs : Group.IsSolvable θ :=
    (solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three).1
  let φ : ↥Y →* ↥X ⧸ θ := (QuotientGroup.mk' θ).comp (Subgroup.inclusion hYX)
  set N : Subgroup ↥Y := φ.ker with hN
  have hNs : Group.IsSolvable N := by
    have hmem : ∀ n : N, (Subgroup.inclusion hYX).comp N.subtype n ∈ θ := fun n =>
      (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp n.2)
    let ι : N →* θ := ((Subgroup.inclusion hYX).comp N.subtype).codRestrict θ hmem
    have hι : Function.Injective ι := by
      intro a b hab
      have h2 : ((ι a : ↥X) : G) = ((ι b : ↥X) : G) := by rw [hab]
      exact Subtype.ext (Subtype.ext h2)
    exact Group.isSolvable_of_isSolvable_injective hι
  set O := CFSG.pCore 2 ↥Y with hO
  have hbig' : 8 ∣ Nat.card (↥Y ⧸ O) := hbig
  have hQ : CFSG.IsQuasisimple (↥Y ⧸ O) := hY.2.2.2
  set N' : Subgroup (↥Y ⧸ O) := N.map (QuotientGroup.mk' O) with hN'
  have hN'n : N'.Normal :=
    Subgroup.Normal.map (MonoidHom.normal_ker φ) _ (QuotientGroup.mk'_surjective O)
  have hN's : Group.IsSolvable N' := by
    have hsurj : Function.Surjective (((QuotientGroup.mk' O).comp N.subtype).codRestrict N'
        (fun n => ⟨(n : ↥Y), n.2, rfl⟩)) := by
      rintro ⟨q, n, hn, rfl⟩
      exact ⟨⟨n, hn⟩, rfl⟩
    exact Group.isSolvable_of_surjective hsurj
  have hN'c : N' ≤ Subgroup.center (↥Y ⧸ O) :=
    CFSG.RankThree.PartOne.N143.normal_solvable_le_center hQ hN'n hN's
  have hodd : Odd (Nat.card N') := by
    have hZ : Odd (Nat.card (Subgroup.center (↥Y ⧸ O))) :=
      CFSG.RankThree.PartTwo.Sec15.F153L3C2.odd_card_center_of_pCore_eq_bot
        (CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot (p := 2) (H := ↥Y))
    exact Odd.of_dvd_nat hZ (Subgroup.card_dvd_of_le hN'c)
  let ψ : ↥Y →* (↥Y ⧸ O) ⧸ N' := (QuotientGroup.mk' N').comp (QuotientGroup.mk' O)
  have hψs : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective N').comp (QuotientGroup.mk'_surjective O)
  have hNψ : N ≤ ψ.ker := fun n hn => by
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨n, hn, rfl⟩
  have hdvd60 : Nat.card ((↥Y ⧸ O) ⧸ N') ∣ 60 := by
    have h1 : ψ.ker.index = Nat.card ((↥Y ⧸ O) ⧸ N') := by
      rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hψs, Subgroup.card_top]
    have h2 : N.index = Nat.card φ.range := Subgroup.index_ker φ
    rw [← h1, ← h60]
    exact (Subgroup.index_dvd_of_le hNψ).trans (h2 ▸ Subgroup.card_subgroup_dvd_card φ.range)
  have hQcard : Nat.card (↥Y ⧸ O) = Nat.card ((↥Y ⧸ O) ⧸ N') * Nat.card N' :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup N'
  have hcop : Nat.Coprime 8 (Nat.card N') :=
    (Nat.Coprime.pow_left 3 (Nat.coprime_two_left.mpr hodd) : Nat.Coprime (2 ^ 3) _)
  have h8 : 8 ∣ Nat.card ((↥Y ⧸ O) ⧸ N') :=
    hcop.dvd_of_dvd_mul_right (hQcard ▸ hbig')
  exact absurd (h8.trans hdvd60) (by norm_num)

theorem item152Big_of
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h44 : Sec4.Item4_4) (hcomp : Step152Comp A (lB A)) (hexcl : Step152Excl A (lB A)) :
    Item152Big A (lB A) := by
  intro Y hY hbig M hM hYM hF
  obtain ⟨X, hX, hYX, hΔ⟩ := hcomp Y hY M hM hYM hF
  have hAX : A ≤ Subgroup.normalizer (X : Set G) :=
    le_normalizer_of_mem_thetaComponentsIn hM.1.2 hX hYX (isPerfect_of_mem_scriptY4 hY)
      (ne_bot_of_mem_scriptY4 hY) hY.1.2
  by_cases hq : IsQuasisimple (↥X ⧸ CFSG.pCore 2 ↥X)
  · exact ⟨X, hX, hYX, mem_scriptY0_of_isQuasisimple hY hM hF hX hYX hAX hΔ hq⟩
  · exfalso
    have hsl := (isQuasisimple_or_isSL25Case h.toTheoremFourHyp h44 hexcl hY hM hYM hF hX hYX
      hΔ).resolve_left hq
    exact not_big152_of_sl25 hY hYX (isQuasisimple_theta_of_mem_thetaComponentsIn hX) hsl hbig

theorem item152BigR_of
    (h44 : Sec4.Item4_4) (hcomp : Step152CompR) (hexcl : Step152ExclR) : Item152BigR :=
  fun G _ _ A c L hR => item152Big_of hR.toSec14Std h44 (hcomp G A c L hR) (hexcl G A c L hR)

end CFSG.RankThree.PartTwo.Sec15.Ronan152Six
