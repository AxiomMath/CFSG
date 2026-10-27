module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallFiKCKFacts
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch22SemiQS
import CFSG.LocalAnalysis.GL83PartI.I_24_3.CoverCentre
import CFSG.RankThree.OddKernel.TransitiveCoverKernel
import CFSG.GH74.BNPair.Lemma3013

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch22

theorem exists_surjective_subgroup_of_comap {G : Type*} [Group G] (H : Subgroup G)
    {S : Type*} [Group S] (π : H →* S) (hπ : Function.Surjective π) (K : Subgroup S) :
    ∃ (H' : Subgroup G) (π' : H' →* K), Function.Surjective π' := by
  classical
  let H₀ : Subgroup H := K.comap π
  let φ : H₀ →* K :=
    { toFun := fun x => ⟨π x.1, x.2⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp }
  have hφ : Function.Surjective φ := by
    intro k
    obtain ⟨h, hh⟩ := hπ k.1
    refine ⟨⟨h, ?_⟩, ?_⟩
    · change π h ∈ K
      rw [hh]
      exact k.2
    · ext
      exact hh
  let e : H₀.map H.subtype ≃* H₀ :=
    (Subgroup.equivMapOfInjective H₀ H.subtype H.subtype_injective).symm
  exact ⟨H₀.map H.subtype, φ.comp e.toMonoidHom, hφ.comp e.surjective⟩

theorem not_dvd_card_center_of_layer_eq_top (hC5 : CFSG.AGLEmbedding.KFactCoverRankFive)
    {G : Type} [Group G] [Finite G] (hK : CFSG.Open.IsKGroup G) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hrk : CFSG.Open.pRank p (⊤ : Subgroup G) ≤ 3) (H : Subgroup G)
    {S : Type} [Group S] (π : H →* S) (hπ : Function.Surjective π)
    (hE : CFSG.layer S = ⊤) : ¬ p ∣ Nat.card (Subgroup.center S) := by
  classical
  have hSfin : Finite S := Finite.of_surjective π hπ
  have hFact : Fact p.Prime := ⟨hp⟩
  intro hdvd
  obtain ⟨J, hJ, hdvdJ⟩ :=
    CFSG.RankThree.OddKernel.exists_component_dvd_card_center hE hp hdvd
  have hJq : CFSG.Open.IsQuasisimple J := ⟨hJ.1.1.commutator_eq_top, hJ.1.2.1⟩
  have hcore : CFSG.pCore p J ≠ ⊥ := fun h =>
    CFSG.GH74.BNPair.not_dvd_card_center (p := p) h hdvdJ
  have hZp : IsPGroup p (Subgroup.center (J ⧸ GL83.I243.Cover.primeCentre p J)) :=
    GL83.I243.Cover.isPGroup_center_quotient (p := p) hJq
  have hZne : Subgroup.center (J ⧸ GL83.I243.Cover.primeCentre p J) ≠ ⊥ :=
    GL83.I243.Cover.center_quotient_ne_bot (p := p) hJq hcore
  let W : Subgroup J := GL83.I243.Cover.primeCentre p J
  have hKq : CFSG.Open.IsQuasisimple (J ⧸ W) :=
    GL83.I243.Cover.isQuasisimple_quotient (p := p) hJq
  obtain ⟨H', π', hπ'⟩ := exists_surjective_subgroup_of_comap H π hπ J
  let π'' : H' →* (J ⧸ W) := (QuotientGroup.mk' W).comp π'
  have hπ'' : Function.Surjective π'' :=
    (QuotientGroup.mk'_surjective W).comp hπ'
  exact false_of_quasisimple_section hC5 hK hp hp5 hrk H' π'' hπ'' hKq hZne hZp

end CFSG.LocalAnalysis.WeakClosure81.Asch22
