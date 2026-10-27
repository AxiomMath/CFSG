module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_CycThreeCent_barSub_card
    (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (h : Setting16 D V₀ V L)
    {E : Subgroup G} (hEM : E ≤ D.M) (hEab : IsElemAbelian 3 E) (hEcard : Nat.card ↥E = 3 ^ 3)
    (hct : ¬ 3 ∣ Nat.card ↥(F11.CTilde D.M V₀ V)) :
    IsElemAbelian 3 (barSub V₀ V hV E) ∧ Nat.card ↥(barSub V₀ V hV E) = 3 ^ 3 := by
  have hp := h.hyp151.hyp125.pairFacts
  have hEstab : E ≤ stabTil V₀ V :=
    le_stabTil (hEM.trans hp.le_normalizer) (hEM.trans hp.le_normalizer₀)
  refine ⟨(hEab.subgroupOf (stabTil V₀ V)).map (actTil V₀ V hV), ?_⟩
  let f : ↥E →* MulAut (Vtil V₀ V hV) :=
    (actTil V₀ V hV).comp (Subgroup.inclusion hEstab)
  have hrange : f.range = barSub V₀ V hV E := by
    ext φ
    rw [MonoidHom.mem_range, mem_barSub]
    constructor
    · rintro ⟨e, rfl⟩
      exact ⟨⟨(e : G), hEstab e.2⟩, e.2, rfl⟩
    · rintro ⟨g, hgE, rfl⟩
      exact ⟨⟨(g : G), hgE⟩, rfl⟩
  have hker : f.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro e he
    rw [MonoidHom.mem_ker] at he
    have hC : (e : G) ∈ F11.CTilde D.M V₀ V := by
      rw [mem_cTilde_iff hV hp.le_normalizer]
      refine ⟨hEM e.2, hEstab e.2, ?_⟩
      have hsub : Subgroup.inclusion hEstab e = ⟨(e : G), hEstab e.2⟩ := Subtype.ext rfl
      change actTil V₀ V hV (Subgroup.inclusion hEstab e) = 1 at he
      rwa [hsub] at he
    have hordE : orderOf e ∣ Nat.card ↥E := by
      simpa only [Subgroup.orderOf_coe] using Subgroup.orderOf_dvd_natCard E e.2
    have hordC : orderOf (e : G) ∣ Nat.card ↥(F11.CTilde D.M V₀ V) :=
      Subgroup.orderOf_dvd_natCard _ hC
    rw [Subgroup.orderOf_coe] at hordC
    have hnot3 : ¬ 3 ∣ orderOf e := fun h3 => hct (h3.trans hordC)
    rw [hEcard] at hordE
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hordE
    have hk0 : k = 0 := by
      by_contra hk0
      exact hnot3 (hk.symm ▸ dvd_pow_self 3 hk0)
    rw [hk0, pow_zero] at hk
    exact orderOf_eq_one_iff.1 hk
  have hcard : Nat.card ↥(barSub V₀ V hV E) = f.ker.index := by
    rw [Subgroup.index_ker f, hrange]
  rw [hcard, hker, Subgroup.index_bot, hEcard]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
