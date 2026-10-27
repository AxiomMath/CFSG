module

public import CFSG.RankThree.PartTwo.Sec21.HeringFFPaperReduce
public import CFSG.RankThree.PartTwo.Sec21.HeringFFNormal
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Open (IsElemAbelian)

theorem ffCentCyclic_of_kE9 (hK : FFKE9) : FFCentCyclic := by
  intro G _ _ A a X hpt hX hXq _hN
  unfold FFCentCyclicSylow
  generalize hC : Subgroup.centralizer (X : Set G) = C
  intro P
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hcyc
  haveI : Fact (IsPGroup 3 ↥(P : Subgroup ↥C)) := ⟨P.isPGroup'⟩
  obtain ⟨S, -, hS9, hSel⟩ := CFSG.lemma_4_5_a (p := 3) (by norm_num) hcyc
  have hSab : IsElemAbelian 3 S :=
    CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr hSel
  obtain ⟨D, hD⟩ : ∃ D : Subgroup G,
      D = (S.map (P : Subgroup ↥C).subtype).map C.subtype := ⟨_, rfl⟩
  have hDab : IsElemAbelian 3 D := by
    rw [hD]
    exact CFSG.Open.IsElemAbelian.map
      (CFSG.Open.IsElemAbelian.map hSab (P : Subgroup ↥C).subtype) C.subtype
  have hD9 : Nat.card D = 9 := by
    rw [hD, Subgroup.card_map_of_injective C.subtype_injective,
      Subgroup.card_map_of_injective (P : Subgroup ↥C).subtype_injective]
    norm_num [hS9]
  have hDC : D ≤ C := by
    rw [hD]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨s, -, rfl⟩ := hy
    exact s.1.2
  have hCc : ∀ y ∈ C, ∀ h ∈ X, h * y = y * h := by
    intro y hy h hh
    rw [← hC] at hy
    exact Subgroup.mem_centralizer_iff.1 hy h (SetLike.mem_coe.2 hh)
  have hst := hpt.standing
  have hQ : CFSG.IsQuasisimple (lBar X) :=
    Sec6.isQuasisimple_of_mem_thetaComponentsAt hpt.mem_theta
  have hmodel := ff_statedModel_center hXq hX hQ
  have hZ3 := ff_not_three_dvd_card_center hXq hX hQ
  obtain ⟨E₀, V₀, hE₀, hE₀9, hV₀, hV₀2, hE₀V₀⟩ := hK ↥X hXq hZ3 hmodel
  obtain ⟨E, hE⟩ : ∃ E : Subgroup G, E = E₀.map X.subtype := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V : Subgroup G, V = V₀.map X.subtype := ⟨_, rfl⟩
  have hEX : E ≤ X := by
    rw [hE]
    exact Subgroup.map_subtype_le E₀
  have hVX : V ≤ X := by
    rw [hV]
    exact Subgroup.map_subtype_le V₀
  have hEab : IsElemAbelian 3 E := by
    rw [hE]
    exact CFSG.Open.IsElemAbelian.map hE₀ X.subtype
  have hE9 : Nat.card E = 9 := by
    rw [hE, Subgroup.card_map_of_injective X.subtype_injective]
    exact hE₀9
  have hVne : V ≠ ⊥ := by
    intro h
    rw [hV] at h
    exact hV₀ ((Subgroup.map_eq_bot_iff_of_injective V₀ X.subtype_injective).mp h)
  have hV2 : IsPGroup 2 V := by
    rw [hV]
    exact hV₀2.map X.subtype
  have hEV : E ≤ Subgroup.normalizer (V : Set G) := by
    rw [hE, hV]
    exact (Subgroup.map_mono hE₀V₀).trans (Subgroup.le_normalizer_map X.subtype)
  have hcomm : ∀ x ∈ E, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    hCc y (hDC hy) x (hEX hx)
  have hDV : D ≤ Subgroup.centralizer (V : Set G) := fun y hy =>
    Subgroup.mem_centralizer_iff.2 fun h hh => hCc y (hDC hy) h (hVX hh)
  have hdisj : ∀ x ∈ E, x ∈ D → x = 1 := by
    intro x hxE hxD
    have hxX : x ∈ X := hEX hxE
    have hz : (⟨x, hxX⟩ : ↥X) ∈ Subgroup.center ↥X := by
      rw [Subgroup.mem_center_iff]
      intro k
      exact Subtype.ext (hCc x (hDC hxD) k k.2)
    by_contra hx1
    obtain ⟨z, hzdef⟩ : ∃ z : ↥(Subgroup.center ↥X), z = ⟨⟨x, hxX⟩, hz⟩ := ⟨_, rfl⟩
    have hz3 : z ^ 3 = 1 := by
      rw [hzdef]
      exact Subtype.ext (Subtype.ext (hEab.2 x hxE))
    have hz1 : z ≠ 1 := by
      intro h
      apply hx1
      rw [hzdef] at h
      exact congrArg (fun w : ↥(Subgroup.center ↥X) => (w : ↥X).1) h
    have hdvd := orderOf_dvd_natCard z
    rw [orderOf_eq_prime hz3 hz1] at hdvd
    exact hZ3 hdvd
  exact ff_false_of_two_nines hst.evenRank_eq hVne hV2 hEab hE9 hDab hD9 hEV hDV hcomm hdisj

end CFSG.RankThree.PartTwo.Sec21
