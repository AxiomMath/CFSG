module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Descent
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThree (Real3)

theorem listRow_of_pRank_eq_one {S : Type} [Group S] [Finite S]
    (h : CFSG.Open.pRank 3 (⊤ : Subgroup S) = 1) : ListRow S :=
  fun _ _ _ => Or.inl h

theorem listRow_of_forall_orderOf_ne_three {S : Type} [Group S] [Finite S]
    (h : ∀ z : S, orderOf z ≠ 3) : ListRow S :=
  fun z hz _ => absurd hz (h z)

theorem listRow_of_not_three_dvd {S : Type} [Group S] [Finite S] (h : ¬ 3 ∣ Nat.card S) :
    ListRow S :=
  listRow_of_forall_orderOf_ne_three fun z hz => h (hz ▸ orderOf_dvd_natCard z)

theorem listRow_of_forall_not_weaklyClosed {S : Type} [Group S] [Finite S]
    (h : ∀ z : S, orderOf z = 3 → ¬ WeaklyClosed (Subgroup.zpowers z)) : ListRow S :=
  fun z hz hw => absurd hw (h z hz)

theorem not_weaklyClosed_of_commute_conj {G : Type} [Group G] {z g : G}
    (hc : (g * z * g⁻¹) * z = z * (g * z * g⁻¹)) (hnot : g * z * g⁻¹ ∉ Subgroup.zpowers z) :
    ¬ WeaklyClosed (Subgroup.zpowers z) := by
  intro h
  have hmap : (Subgroup.zpowers z).map (MulAut.conj g).toMonoidHom =
      Subgroup.zpowers (g * z * g⁻¹) := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hle : (Subgroup.zpowers z).map (MulAut.conj g).toMonoidHom ≤
      Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
    rw [hmap, Subgroup.zpowers_le]
    exact mem_normalizer_zpowers_of_commute hc
  have := h g hle
  rw [hmap] at this
  exact hnot (this ▸ Subgroup.mem_zpowers _)

theorem not_autWeaklyClosed_of_commute_conj {S : Type} [Group S] {σ : MulAut S} {x : S}
    (hc : (MulAut.conj x * σ * (MulAut.conj x)⁻¹) * σ = σ * (MulAut.conj x * σ * (MulAut.conj x)⁻¹))
    (hnot : MulAut.conj x * σ * (MulAut.conj x)⁻¹ ∉ Subgroup.zpowers σ) :
    ¬ AutWeaklyClosed σ := by
  intro h
  exact hnot (h x (mem_normalizer_zpowers_of_commute hc))

theorem outerRow_of_forall_pow_three_inner {S : Type} [Group S] [Finite S]
    (h : ∀ σ : MulAut S, σ ^ 3 = 1 → σ ∈ (MulAut.conj : S →* MulAut S).range) : OuterRow S :=
  fun _ σ hσ hout _ => hout (h σ hσ)

end CFSG.RankThree.PartTwo.Sec4.RonanK432
