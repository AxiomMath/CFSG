module

public import CFSG.LocalAnalysis.StandardType.GGSixStepOneCompDiag
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneCompCentre

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section General

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_le_component {H Kd J : Subgroup G} {y : G} (hKd : IsComponentOf Kd H)
    (hJ : CFSG.Assembly.IsQuasisimple ↥J) (hJK : J ≤ Kd) (hyH : y ∈ H)
    (hyJ : y ∈ Subgroup.centralizer (J : Set G)) : y ∈ Subgroup.normalizer (Kd : Set G) := by
  by_contra hn
  have h1 := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hKd y
  have e : H.map (MulAut.conj y).toMonoidHom = H :=
    CFSG.LocalAnalysis.ComponentInitial.conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hyH)
  rw [e] at h1
  rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute h1 hKd with h | h
  · exact hn (mem_normalizer_of_map_conj_eq h)
  · apply CFSG.LocalAnalysis.ComponentInitial.not_le_centralizer_self_of_isQuasisimple hJ
    have hJK' : J ≤ Kd.map (MulAut.conj y).toMonoidHom := by
      intro j hj
      refine ⟨j, hJK hj, ?_⟩
      have := Subgroup.mem_centralizer_iff.mp hyJ j hj
      change y * j * y⁻¹ = j
      rw [← this]
      group
    exact (hJK'.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h)).trans
      (Subgroup.centralizer_le hJK)

theorem ggClosure_pair_eq {p : ℕ} (hp : p.Prime) {D : Subgroup G} (hD : Nat.card D = p ^ 2)
    {d y : G} (hd : d ∈ D) (hy : y ∈ D) (hd1 : d ≠ 1) (hdp : d ^ p = 1)
    (hyd : y ∉ Subgroup.zpowers d) : Subgroup.closure {d, y} = D := by
  have : Fact p.Prime := ⟨hp⟩
  set C := Subgroup.closure ({d, y} : Set G) with hC
  have hCD : C ≤ D := (Subgroup.closure_le D).mpr (by
    intro g hg
    rcases hg with rfl | rfl
    · exact hd
    · exact hy)
  have hdC : d ∈ C := Subgroup.subset_closure (Set.mem_insert d {y})
  have hyC : y ∈ C := Subgroup.subset_closure (Set.mem_insert_of_mem d rfl)
  have hzC : Subgroup.zpowers d ≤ C := Subgroup.zpowers_le.mpr hdC
  have hzcard : Nat.card (Subgroup.zpowers d) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hdp hd1]
  obtain ⟨k, hk, hkC⟩ := (Nat.dvd_prime_pow hp).mp (hD ▸ Subgroup.card_dvd_of_le hCD)
  have hpC : p ∣ Nat.card C := hzcard ▸ Subgroup.card_dvd_of_le hzC
  interval_cases k
  · rw [hkC, pow_zero] at hpC
    exact absurd (Nat.le_of_dvd one_pos hpC) (by have := hp.two_le; omega)
  · exfalso
    apply hyd
    have heq : Subgroup.zpowers d = C :=
      Subgroup.eq_of_le_of_card_ge hzC (by rw [hkC, hzcard, pow_one])
    exact heq ▸ hyC
  · exact Subgroup.eq_of_le_of_card_ge hCD (by rw [hD, hkC])

omit [Finite G] in
theorem ggCentralizer_closure_pair (d y : G) :
    Subgroup.centralizer (Subgroup.closure ({d, y} : Set G) : Set G) =
      Subgroup.centralizer {d} ⊓ Subgroup.centralizer {y} := by
  rw [Subgroup.centralizer_closure]
  ext g
  simp only [Subgroup.mem_centralizer_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq, Subgroup.mem_inf]

end General

section Ctx

variable {G : Type} [Group G] [Finite G] {U : Type} [Group U] {p : ℕ} {B Bs : Subgroup G}
  {x : G} {L D J : Subgroup G} {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ}
  {ψ : U →* G}

theorem GGSixCtxV2.components_normal (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ)
    (hJD : ∀ K : Subgroup G, IsComponentOf K (Subgroup.centralizer (D : Set G)) → K = J)
    (hcomp : ∀ d ∈ D, d ≠ 1 → IsComponentOf (ggKd p B x L D J d) (Subgroup.centralizer {d})) :
    ∀ d ∈ D, d ≠ 1 → ∀ K : Subgroup G, IsComponentOf K (Subgroup.centralizer {d}) →
      D ≤ Subgroup.normalizer (K : Set G) := by
  intro d hd hd1 K hK y hy
  by_contra hyK
  have hyH : y ∈ Subgroup.centralizer {d} := h.d_le_centralizer hd hy
  have hyp : y ^ p = 1 := h.d_elem.2 y hy
  obtain ⟨Δ', hΔ, hΔc⟩ := exists_diagonal_component h.prime hK hyH hyp hyK
  have hdK : Subgroup.zpowers d ≤ Subgroup.normalizer (K : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hK.1 hk))
  have hyd : y ∉ Subgroup.zpowers d := fun hyz => hyK (hdK hyz)
  have hDcl := ggClosure_pair_eq h.prime h.card_d hd hy hd1 (h.d_elem.2 d hd) hyd
  have hCD : Subgroup.centralizer (D : Set G) =
      Subgroup.centralizer {d} ⊓ Subgroup.centralizer {y} := by
    rw [← hDcl, ggCentralizer_closure_pair]
  rw [← hCD] at hΔ
  have hΔJ := hJD Δ' hΔ
  have hKd := hcomp d hd hd1
  have hyKd := mem_normalizer_of_le_component hKd h.j_comp.2.2 (le_ggKd p B x L D J d) hyH
    (h.le_centralizer_J hy)
  have hJc := hΔc _ hKd hyKd
  rw [hΔJ] at hJc
  exact CFSG.LocalAnalysis.ComponentInitial.not_le_centralizer_self_of_isQuasisimple h.j_comp.2.2
    (hJc.trans (Subgroup.centralizer_le (le_ggKd p B x L D J d)))

end Ctx

section CtxU

@[expose] def GGSixLayerCDInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    Odd (Nat.card (Subgroup.centralizer (ggG0 p B x L D J : Set G))) →
      ∀ K : Subgroup G,
        IsComponentOf K (ggG0 p B x L D J ⊓ Subgroup.centralizer (D : Set G)) → K = J

@[expose] def GGSixLayerCXInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
      ∀ K : Subgroup G,
        IsComponentOf K (ggG0 p B x L D J ⊓ Subgroup.centralizer {x}) → K = L

theorem ggSixLayerCDInput_of_layerCX (hlp : GGLayerPerfectInput) (hCX : GGSixLayerCXInput) :
    GGSixLayerCDInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx hodd K hK
  have hxD : Subgroup.zpowers x ≤ D := Subgroup.zpowers_le.mpr hctx.x_mem_d
  have hlp' := hlp G t n f ψ _ hctx.presents hodd p hctx.prime hctx.ne_two (Subgroup.zpowers x)
    (hctx.d_isPGroup.to_le hxD) (fun a ha b hb => hctx.d_comm a (hxD ha) b (hxD hb))
    (hxD.trans hctx.d_le_ggM) (fun e he => hctx.d_innerDiag e (hxD he))
  rw [ggCentralizer_zpowers_eq] at hlp'
  have hDx : Subgroup.centralizer (D : Set G) ≤ Subgroup.centralizer {x} :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hctx.x_mem_d)
  have hKE := hlp' K (hK.1.trans (inf_le_inf_left _ hDx))
    (commutator_self_eq_of_commutator_eq_top hK.2.2.1)
  have hEL : LargeEvenLayer (ggG0 p B x L D J ⊓ Subgroup.centralizer {x}) ≤ L :=
    sSup_le fun K' hK' => (hCX G p B Bs x L D J t n f ψ hctx K' hK').le
  have hKL : K ≤ L ⊓ Subgroup.centralizer (D : Set G) :=
    le_inf (hKE.trans hEL) (hK.1.trans inf_le_right)
  have hLD : L ⊓ Subgroup.centralizer (D : Set G) ≤
      ggG0 p B x L D J ⊓ Subgroup.centralizer (D : Set G) :=
    inf_le_inf_right _ (le_sup_left : L ≤ ggG0 p B x L D J)
  have hK' : IsComponentOf K (L ⊓ Subgroup.centralizer (D : Set G)) :=
    CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hK hKL hLD
  rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hK' hctx.j_comp with h | h
  · exact h
  · exfalso
    have hKJ : K ≤ J := by
      rw [hctx.stdSub.1.2.2.2.2.1]
      exact le_largeEvenLayer hK'
    exact CFSG.LocalAnalysis.ComponentInitial.not_le_centralizer_self_of_isQuasisimple hK.2.2
      ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp h).trans (Subgroup.centralizer_le hKJ))

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
  {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G}

theorem GGSixCtxV2.components_centralizer_eq (hS : GGSchreierPerfectInput)
    (hLD : GGSixLayerCDInput) (h : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    (hC2 : Subgroup.centralizer (D : Set G) ≤ ggM p B x L D J)
    (hodd : Odd (Nat.card (Subgroup.centralizer (ggG0 p B x L D J : Set G)))) :
    ∀ K : Subgroup G, IsComponentOf K (Subgroup.centralizer (D : Set G)) → K = J := by
  intro K hK
  have hKG0 : K ≤ ggG0 p B x L D J :=
    hS G t n f ψ _ h.presents hodd K (hK.1.trans hC2)
      (commutator_self_eq_of_commutator_eq_top hK.2.2.1)
  exact hLD G p B Bs x L D J t n f ψ h hodd K
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hK (le_inf hKG0 hK.1) inf_le_right)

theorem ggSixComponentsNormalInput_of_layer (hS : GGSchreierPerfectInput)
    (hLD : GGSixLayerCDInput) : GGSixComponentsNormalInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx hC2 hodd hcomp
  exact hctx.components_normal (hctx.components_centralizer_eq hS hLD hC2 hodd) hcomp

end CtxU

end CFSG.StandardType
