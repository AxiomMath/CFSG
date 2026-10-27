module

public import CFSG.RankThree.PartTwo.Sec21.HeringFFRank
public import CFSG.RankThree.PartTwo.Sec21.HeringFFReduce
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.Open (IsElemAbelian)

@[expose] def FFKE9 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → ¬ 3 ∣ Nat.card (Subgroup.center X) →
    (StatedClassicalModel (X ⧸ Subgroup.center X) .PSL 4 2 1 ∨
      StatedClassicalModel (X ⧸ Subgroup.center X) .PSL 5 2 1 ∨
      StatedClassicalModel (X ⧸ Subgroup.center X) .PSp 3 2 1) →
    ∃ E V : Subgroup X, IsElemAbelian 3 E ∧ Nat.card E = 9 ∧ V ≠ ⊥ ∧ IsPGroup 2 V ∧
      E ≤ Subgroup.normalizer (V : Set X)

theorem ffCentralizerNormalizes_of_kE9 (hK : FFKE9) : FFCentralizerNormalizes := by
  intro G _ _ A a X hpt hX hXq g hg
  by_contra hgX
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hst := hpt.standing
  have hQ : CFSG.IsQuasisimple (lBar X) :=
    Sec6.isQuasisimple_of_mem_thetaComponentsAt hpt.mem_theta
  have hmodel := ff_statedModel_center hXq hX hQ
  have hZ3 := ff_not_three_dvd_card_center hXq hX hQ
  obtain ⟨E₀, V₀, hE₀, hE₀9, hV₀, hV₀2, hE₀V₀⟩ := hK ↥X hXq hZ3 hmodel
  obtain ⟨X', hX', hX'X⟩ := hpt.mem_theta
  have hX'q : CFSG.IsQuasisimple ↥X' := by
    refine CFSG.LocalCores.isQuasisimple_of_mulEquiv ?_ hXq
    exact ((X'.equivMapOfInjective (Subgroup.centralizer ({a} : Set G)).subtype
      (Subgroup.centralizer ({a} : Set G)).subtype_injective).trans
      (MulEquiv.subgroupCongr hX'X)).symm
  have hX'comp : CFSG.IsComponent X' := ⟨hX'q, hX'.2.1⟩
  set g' : ↥(Subgroup.centralizer ({a} : Set G)) := ⟨g, hg⟩ with hg'
  set Y' : Subgroup ↥(Subgroup.centralizer ({a} : Set G)) :=
    X'.map (MulAut.conj g').toMonoidHom with hY'
  have hY'q : CFSG.IsQuasisimple ↥Y' :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (X'.equivMapOfInjective (MulAut.conj g').toMonoidHom (MulAut.conj g').injective) hX'q
  have hY'comp : CFSG.IsComponent Y' :=
    ⟨hY'q, hX'.2.1.map (f := (MulAut.conj g').toMonoidHom) (MulAut.conj g').surjective⟩
  have hne : X' ≠ Y' := by
    intro heq
    apply hgX
    have hg'n : g' ∈ Subgroup.normalizer (X' : Set ↥(Subgroup.centralizer ({a} : Set G))) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact heq.symm
    rw [← hX'X]
    exact Subgroup.le_normalizer_map (Subgroup.centralizer ({a} : Set G)).subtype ⟨g', hg'n, rfl⟩
  have hcommXY : ∀ k ∈ X', ∀ k' ∈ Y', k * k' = k' * k := by
    rcases CFSG.LocalCores.distinct_components_commute hX'comp hY'comp with h | h
    · exact absurd h hne
    · intro k hk k' hk'
      have := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h hk
      exact (Subgroup.mem_centralizer_iff.1 this k' hk').symm
  set Y : Subgroup G := Y'.map (Subgroup.centralizer ({a} : Set G)).subtype with hY
  have hcommG : ∀ k ∈ X, ∀ k' ∈ Y, k * k' = k' * k := by
    intro k hk k' hk'
    rw [← hX'X] at hk
    obtain ⟨k₁, hk₁, rfl⟩ := hk
    obtain ⟨k₂, hk₂, rfl⟩ := hk'
    exact congrArg Subtype.val (hcommXY k₁ hk₁ k₂ hk₂)
  set E : Subgroup G := E₀.map X.subtype with hE
  set V : Subgroup G := V₀.map X.subtype with hV
  set E' : Subgroup G := E.map (MulAut.conj g).toMonoidHom with hE'
  have hEX : E ≤ X := Subgroup.map_subtype_le E₀
  have hVX : V ≤ X := Subgroup.map_subtype_le V₀
  have hE'Y : E' ≤ Y := by
    rintro _ ⟨e, he, rfl⟩
    have heX : e ∈ X := hEX he
    rw [← hX'X] at heX
    obtain ⟨e₁, he₁, rfl⟩ := heX
    exact ⟨g' * e₁ * g'⁻¹, ⟨e₁, he₁, rfl⟩, by simp [hg', MulAut.conj_apply]⟩
  have hEab : IsElemAbelian 3 E := CFSG.Open.IsElemAbelian.map hE₀ X.subtype
  have hE9 : Nat.card E = 9 := by
    rw [hE, Subgroup.card_map_of_injective X.subtype_injective]; exact hE₀9
  have hVne : V ≠ ⊥ := fun h =>
    hV₀ ((Subgroup.map_eq_bot_iff_of_injective V₀ X.subtype_injective).mp h)
  have hV2 : IsPGroup 2 V := hV₀2.map X.subtype
  have hEV : E ≤ Subgroup.normalizer (V : Set G) :=
    (Subgroup.map_mono hE₀V₀).trans (Subgroup.le_normalizer_map X.subtype)
  have hE'ab : IsElemAbelian 3 E' := CFSG.Open.IsElemAbelian.map hEab _
  have hE'9 : Nat.card E' = 9 := by
    rw [hE', Subgroup.card_map_of_injective (MulAut.conj g).injective]; exact hE9
  have hE'V : E' ≤ Subgroup.centralizer (V : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun h hh => hcommG h (hVX hh) x (hE'Y hx)
  have hcomm : ∀ x ∈ E, ∀ y ∈ E', x * y = y * x := fun x hx y hy =>
    hcommG x (hEX hx) y (hE'Y hy)
  have hdisj : ∀ x ∈ E, x ∈ E' → x = 1 := by
    intro x hxE hxE'
    have hxX : x ∈ X := hEX hxE
    have hz : (⟨x, hxX⟩ : ↥X) ∈ Subgroup.center ↥X := by
      rw [Subgroup.mem_center_iff]
      intro k
      exact Subtype.ext (hcommG k k.2 x (hE'Y hxE'))
    by_contra hx1
    set z : ↥(Subgroup.center ↥X) := ⟨⟨x, hxX⟩, hz⟩ with hzdef
    have hz3 : z ^ 3 = 1 := Subtype.ext (Subtype.ext (hEab.2 x hxE))
    have hz1 : z ≠ 1 := fun h => hx1 (congrArg (fun w : ↥(Subgroup.center ↥X) => (w : ↥X).1) h)
    exact hZ3 ((orderOf_eq_prime hz3 hz1) ▸ orderOf_dvd_natCard z)
  exact ff_false_of_two_nines hst.evenRank_eq hVne hV2 hEab hE9 hE'ab hE'9 hEV hE'V hcomm hdisj

end CFSG.RankThree.PartTwo.Sec21
