module

public import CFSG.Quasithin.Vol2.KGFactInsp4316Split
public import CFSG.Quasithin.Vol2.KGFactInspOddCore
public import CFSG.Quasithin.Vol2.KGFactInspModelU
public import CFSG.Quasithin.Vol2.KGFactInspE16Base

public section

namespace CFSG.Quasithin.H13.KGInsp4316

open CFSG.Open hiding StatedSL StatedSp StatedClassicalModel StatedLieTag StatedProj StatedSU
open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.KGL3Even (LConf lconf_subgroupOf map_map_symm)
open CFSG.Quasithin.H13.KGInspOdd (InvCentModel core_eq invCentModel_psl invCentModel_psu)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped MatrixGroups

namespace Cfg4316

variable {X : Type} [Group X] [Finite X] {S R K : Subgroup X} {n : ℕ} {x : X}

theorem eq_five (h : Cfg4316 S R K n x) (hRS : R ≤ S) {P : Type*}
    [Group P] [Finite P] (e : ↥S ≃* P) {F₀ : Type} [Field F₀] [Finite F₀]
    (hM : InvCentModel P F₀) (hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F₀))
    (hrank : CFSG.Open.pRank 2 (⊤ : Subgroup P) ≤ 2) : n = 2 ∧ Nat.card F₀ = 5 := by
  have hc := (lconf_subgroupOf hRS h.le h.le_normalizer h.normalizer_le h.core).map e
  have hR2 : IsPGroup 2 ((R.subgroupOf S).map e.toMonoidHom) :=
    (h.isPGroup.comap_of_injective S.subtype S.subtype_injective).map _
  have hR1 : (R.subgroupOf S).map e.toMonoidHom ≠ ⊥ := by
    intro hb
    apply h.ne_bot
    have h3 : R.subgroupOf S = ⊥ := by
      rw [← map_map_symm e (R.subgroupOf S), hb, Subgroup.map_bot]
    rw [← Subgroup.map_subgroupOf_eq_of_le hRS, h3, Subgroup.map_bot]
  have hKp : ⁅(K.subgroupOf S).map e.toMonoidHom, (K.subgroupOf S).map e.toMonoidHom⁆ =
      (K.subgroupOf S).map e.toMonoidHom := by
    rw [← Subgroup.map_commutator, h.perfect_subgroupOf]
  have hK1 : (K.subgroupOf S).map e.toMonoidHom ≠ ⊥ := by
    intro hb
    apply h.K_ne_bot
    have h3 : K.subgroupOf S = ⊥ := by
      rw [← map_map_symm e (K.subgroupOf S), hb, Subgroup.map_bot]
    rw [← Subgroup.map_subgroupOf_eq_of_le h.le, h3, Subgroup.map_bot]
  obtain ⟨F', _, _, hF', χ, hχ, hχk⟩ := h.chi
  let eK : ↥((K.subgroupOf S).map e.toMonoidHom) ≃* ↥K :=
    ((K.subgroupOf S).equivMapOfInjective e.toMonoidHom e.injective).symm.trans
      (Subgroup.subgroupOfEquivOfLe h.le)
  refine core_eq hM hodd hrank hc hR1 hR2 hKp hK1 h.two_le hF' (χ.comp eK.toMonoidHom)
    (hχ.comp eK.surjective) ?_
  rw [← MonoidHom.comap_ker]
  exact hχk.comap_of_injective _ eK.injective

theorem eq_five_psl (h : Cfg4316 S R K n x) (hRS : R ≤ S)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : StatedClassicalModel ↥S .PSL 3 p f) :
    n = 2 ∧ p ^ f = 5 := by
  have hrank := KGInsp4316.pRank_two_le_two_of_psl3_odd hp hp2 hm
  obtain ⟨⟨-, hf, -⟩, F, _, _, hF, ⟨e₁⟩⟩ := hm
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : F) ≠ 0 := CFSG.Wreathed.OddLinearThreeCentralizerCore.two_ne_zero F hodd
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e₁] at hrank
  obtain ⟨hn, h5⟩ := h.eq_five hRS e₁ (invCentModel_psl h2)
    ⟨p, f, hp, hp.odd_of_ne_two hp2, hf, hF⟩ hrank
  exact ⟨hn, by rw [← hF]; exact h5⟩

theorem eq_five_psu (h : Cfg4316 S R K n x) (hRS : R ≤ S)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : StatedClassicalModel ↥S .PSU 3 p f) :
    n = 2 ∧ p ^ f = 5 := by
  have hrank := KGInsp4316.pRank_two_le_two_of_psu3_odd hp hp2 hm
  obtain ⟨⟨-, hf, -⟩, K₀, _, _, hK, ⟨e₁⟩⟩ := hm
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K₀ :=
    ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K₀ p := hU.charP
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e₁] at hrank
  have hcard := CFSG.LieType.Steinberg.card_fixedSubfield hK
  obtain ⟨hn, h5⟩ := h.eq_five hRS e₁ (invCentModel_psu hU hp2 hK)
    ⟨p, f, hp, hp.odd_of_ne_two hp2, hf, hcard⟩ hrank
  exact ⟨hn, by rw [← hcard]; exact h5⟩

end Cfg4316

theorem insp4316L3epsOdd_holds : Insp4316L3epsOdd := by
  intro X _ _ S R K n x h hRS _ _ _ _ s p e hp hp2 _ hcong hL
  cases s
  · obtain ⟨hn, h5⟩ := h.eq_five_psu hRS hp hp2 hL
    obtain ⟨rfl, rfl⟩ := ((by norm_num : Nat.Prime 5).pow_eq_iff).mp h5
    exact ⟨hn, Or.inr hL⟩
  · obtain ⟨-, h5⟩ := h.eq_five_psl hRS hp hp2 hL
    rw [h5] at hcong
    exact absurd hcong (by decide)

theorem insp4316OutLieOdd_holds : Insp4316OutLieOdd := by
  intro X _ _ S R K n x h hRS p₀ hp₀ hp₀2 hm x' _ p hp hp2 _ hx'o hx'S
  rcases hm with hm | hm
  · exfalso
    obtain ⟨-, h5⟩ := h.eq_five_psl hRS hp₀ hp₀2 hm
    obtain ⟨rfl, -⟩ := ((by norm_num : Nat.Prime 5).pow_eq_iff).mp h5
    have := h.normal
    have hdvd := dvd_card_outer_of_not_mem h.cent hx'S hp hx'o
    obtain ⟨hout, -⟩ :=
      CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
        (T := ↥S) (Or.inl rfl) (le_refl 3) hp₀ le_rfl hm
    have h2 : CFSG.RankThree.OuterOrder.determinantParameter .PSL 3 (5 ^ 1) = 1 := by
      simp [CFSG.RankThree.OuterOrder.determinantParameter]
    rw [h2] at hout
    have := Nat.le_of_dvd (by norm_num) (hdvd.trans hout)
    have := hp.two_le
    omega
  · obtain ⟨hn, h5⟩ := h.eq_five_psu hRS hp₀ hp₀2 hm
    obtain ⟨rfl, -⟩ := ((by norm_num : Nat.Prime 5).pow_eq_iff).mp h5
    exact ⟨hn, Or.inr hm⟩

end CFSG.Quasithin.H13.KGInsp4316
