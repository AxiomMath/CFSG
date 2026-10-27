module

public import CFSG.LocalAnalysis.StandardType.GGTWZK
public import CFSG.LocalAnalysis.StandardType.GGTWZKE6Kac
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGK0MarkedKacCoverProducer
public import CFSG.LocalAnalysis.StandardType.GGK0MarkedComponents
public import CFSG.LocalAnalysis.StandardType.GGK0RationalProducerHolds
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentKLocal
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentJLevel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open CFSG.StandardType.GGK0MarkedKacIface1587

section Certs


theorem not_ggResHyp_of_E6_of_three_dvd_rank_add_three
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {labJ labK : LargeEvenLabel}
    (hJΛ : LargeEvenInLambda2 labJ) (hKΛ : LargeEvenInLambda2 labK)
    (hJHas : GGHasLabel labJ (J ⧸ Subgroup.center J))
    (hKHas : GGHasLabel labK (K ⧸ Subgroup.center K))
    (hJtag : labJ.tag = .A ∨ labJ.tag = .twA)
    (hpJ : 3 ∣ labJ.rank + 3)
    (hKtag : labK.tag = .E6 ∨ labK.tag = .twE6) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Omega := AlgebraicClosure (ZMod 2)
  have hpair : GGKacExcPair labK 3 :=
    ⟨Nat.prime_three, by decide, ltrcov_three_dvd labK.n,
      hKtag.elim Or.inl (fun h => Or.inr (Or.inl h))⟩
  have hcover : CoverProducerOn Omega labK.tag := by
    rcases hKtag with ht | ht
    · rw [ht]
      exact coverProducerOn_of_rationalProducerOn Omega .E6 e6Producer_holds
    · rw [ht]
      exact coverProducerOn_of_rationalProducerOn Omega .twE6 twE6Producer_holds
  have hmark := ggInnerDiagOn_relabel hRig (hH.2.2.1.2 y K hH.2.2.2.2.1) hKΛ hKHas
  obtain ⟨hKperf, lab, hΛ, hraw⟩ := hmark
  have hrawLab : LargeEvenRawDatum labK (fun R _ I F =>
      IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      ∃ θ : K ⧸ Subgroup.center K ≃* R,
        Bs ≤ Subgroup.normalizer (K : Set G) ∧
          ∀ b ∈ Bs, ∃ φ ∈ I,
            LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) := by
    obtain ⟨R, _, I, F, hs, hna, θ, heq, hN, hInd⟩ := largeEvenRawDatum_exists hraw
    have hlab : lab = labK := heq
    subst lab
    exact largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ, heq, hN, hInd⟩ => ⟨hs, hna, θ, hN, hInd⟩) hraw
  have hrawCover := hcover 3 labK hKΛ hpair rfl _ hrawLab
  obtain ⟨R, _, I, F, ⟨hs, hna, θ, hN, hInd⟩, hP⟩ := largeEvenRawDatum_exists hrawCover
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := hN hxBs
  let e : MulAut K := K.normalizerMonoidHom ⟨x, hxN⟩
  have hJK : J ≤ K := hH.J_le_K_of_typeA hLB hJΛ hJHas hJtag hpJ
  have hcomp := ggIsComponentOf_inf_centralizer_nbr hH.1 hH.2.2.2.2.1 hJK
  have hJcomp : IsComponentOf (J.subgroupOf K) (ggFixSub e) :=
    ggIsComponentOf_ggFixSub_normalizerMonoidHom hxN hcomp
  have hLocal : GGTPNLocalCore 3 (ggAutsOf K Bs hN) e (J.subgroupOf K) :=
    ggTPNTrLocalCore_holds G 3 B Bs x L D J y K hH.1 hH.2.2.1.1
      (hH.2.2.1.2 y K hH.2.2.2.2.1) hH.2.2.2.2.1 hJK hN hxN
  have he : e ≠ 1 := hLocal.2.2.1
  have hep : e ^ 3 = 1 := hLocal.1.2 e hLocal.2.1
  let ψ : K →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hψ : Function.Surjective ψ := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ψ.ker ≤ Subgroup.center K := by
    intro k hk
    have h0 : θ (QuotientGroup.mk' (Subgroup.center K) k) = 1 := hk
    have h1 : QuotientGroup.mk' (Subgroup.center K) k = 1 :=
      θ.injective (h0.trans (map_one θ).symm)
    exact (QuotientGroup.eq_one_iff k).mp h1
  let φ : MulAut R := ggInducedAut θ e
  have hφI : φ ∈ I := (ggInducedInn_of_clause3 hN θ hInd) e hLocal.2.1
  have hφe : ∀ k : K, φ (ψ k) = ψ (e k) := ggInducedAut_apply θ e
  obtain ⟨φ', hφ'I, hφ'e, ⟨ρ⟩⟩ := hP K ψ hψ hker hKperf e (orderOf_eq_prime hep he)
    ⟨φ, hφI, hφe⟩
  obtain ⟨o, ho, hqs, hn, hoΛ, hoHas⟩ :=
    (GGK0MarkedComponents.cover_comps_of_realization Nat.prime_three (by decide)
      ρ ψ hψ hker e hep hφ'e).1 (J.subgroupOf K) hJcomp
  exact ggTWZKE6Kac_false hH hJΛ hKΛ hJHas hJtag hKtag hpJ ρ.row.valid ho hoΛ
    (ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK) hoHas) hRig

end Certs

end CFSG.StandardType

end
