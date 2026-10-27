module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429CfgForward
public import CFSG.Quasithin.Vol2.F134LieD4
public import CFSG.RankThree.PartTwo.Sec4.RonanK429Rows

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts

section Covers

theorem center_eq_bot_of_alternating_ten {L : Type} [Group L]
    [Finite L] (hq : IsQuasisimple L) (hZ : IsPGroup 3 (Subgroup.center L))
    (e : L ⧸ Subgroup.center L ≃* alternatingGroup (Fin 10)) : Subgroup.center L = ⊥ := by
  have hdvd := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq e
  rw [(CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput 10 (by norm_num)).2] at hdvd
  simp only [show ¬ (10 = 6 ∨ 10 = 7) by omega, if_false] at hdvd
  obtain ⟨k, hk⟩ := hZ.exists_card_eq
  rw [hk] at hdvd
  have hk0 : k = 0 := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exact h
    · exfalso
      have h3 : 3 ∣ 3 ^ k := dvd_pow_self 3 h.ne'
      have := Nat.dvd_trans h3 hdvd
      omega
  rw [hk0, pow_zero] at hk
  exact Subgroup.eq_bot_of_card_eq _ hk

theorem center_eq_bot_of_trialityD4 {L : Type} [Group L] [Finite L] (hq : IsQuasisimple L)
    (hZ : IsPGroup 3 (Subgroup.center L)) {n : ℕ}
    (h : Blueprint.ChevalleyExceptionalModel (L ⧸ Subgroup.center L) .trialityD4 2 n) :
    Subgroup.center L = ⊥ := by
  haveI : Group.IsPerfect L := hq.1
  have hodd : Odd (Nat.card (QuotientGroup.mk' (Subgroup.center L)).ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨k, hk⟩ := hZ.exists_card_eq
    rw [hk]
    exact Odd.pow (by decide)
  have hker := CFSG.SectionRank.triality_even_perfect_odd_cover_trivial h
    (QuotientGroup.mk' (Subgroup.center L)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']) hodd
  rwa [QuotientGroup.ker_mk'] at hker

end Covers

section Kinds

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

@[expose] noncomputable def quotCenterEquivOfEqBot {X : Type*} [Group X]
    (h : Subgroup.center X = ⊥) : X ≃* X ⧸ Subgroup.center X :=
  (QuotientGroup.quotientBot (G := X)).symm.trans (QuotientGroup.quotientMulEquivOfEq h).symm

@[expose] noncomputable def thetaCenterEquiv (hθ : aschbacherSolvableCore 3 L = ⊥)
    (hZ : Subgroup.center L = ⊥) : L ⧸ aschbacherSolvableCore 3 L ≃* L ⧸ Subgroup.center L :=
  (thetaBotEquiv hθ).trans (quotCenterEquivOfEqBot hZ)

theorem thetaCenterEquiv_mk (hθ : aschbacherSolvableCore 3 L = ⊥) (hZ : Subgroup.center L = ⊥)
    (l : L) :
    thetaCenterEquiv hθ hZ (l : L ⧸ aschbacherSolvableCore 3 L) = (l : L ⧸ Subgroup.center L) :=
  rfl

theorem congr_thetaQuotMulAut_eq_descAut (hθ : aschbacherSolvableCore 3 L = ⊥)
    (hZ : Subgroup.center L = ⊥) (n : Subgroup.normalizer (L : Set G)) :
    MulAut.congr (thetaCenterEquiv hθ hZ) (thetaQuotMulAut L (compAction L n)) = descAut L n := by
  ext y
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
  have hs : (thetaCenterEquiv hθ hZ).symm (l : L ⧸ Subgroup.center L) =
      (l : L ⧸ aschbacherSolvableCore 3 L) := by
    rw [MulEquiv.symm_apply_eq, thetaCenterEquiv_mk]
  show thetaCenterEquiv hθ hZ (thetaQuotMulAut L (compAction L n)
    ((thetaCenterEquiv hθ hZ).symm (l : L ⧸ Subgroup.center L))) = descAut L n l
  rw [hs, thetaQuotMulAut_mk, thetaCenterEquiv_mk, descAut_mk]
  rfl

theorem inducedAutHom_thetaCenterEquiv (hθ : aschbacherSolvableCore 3 L = ⊥)
    (hZ : Subgroup.center L = ⊥) {M : Type*} [Group M] (e : L ⧸ Subgroup.center L ≃* M)
    (n : Subgroup.normalizer (L : Set G)) :
    inducedAutHom L ((thetaCenterEquiv hθ hZ).trans e) n = MulAut.congr e (descAut L n) := by
  rw [inducedAutHom_apply, ← congr_thetaQuotMulAut_eq_descAut hθ hZ n]
  ext m
  rfl

theorem inducesStdKind_field_of_isFieldAutL3 (hθ : aschbacherSolvableCore 3 L = ⊥)
    (hZ : Subgroup.center L = ⊥) {c : G} (hc : c ∈ Subgroup.normalizer (L : Set G))
    (h : IsFieldAutL3 (descAut L ⟨c, hc⟩)) : InducesStdKind L c .field := by
  rcases h with ⟨F, _, _, e, he⟩ | ⟨p, f, F, _, hF, hq, e, he⟩
  · exact .psl 3 F le_rfl ⟨(thetaCenterEquiv hθ hZ).trans e, hc, by
      rw [inducedAutHom_thetaCenterEquiv]; exact he⟩
  · exact .psu3 hF hq ⟨(thetaCenterEquiv hθ hZ).trans e, hc, by
      rw [inducedAutHom_thetaCenterEquiv]; exact he⟩

theorem inducesStdKind_graphField_of_not_inner (hθ : aschbacherSolvableCore 3 L = ⊥)
    (hZ : Subgroup.center L = ⊥) {c : G} (hc : c ∈ Subgroup.normalizer (L : Set G))
    (hc3 : c ^ 3 = 1) {n : ℕ} (hD4 : Blueprint.ChevalleyExceptionalModel L .trialityD4 2 n)
    (hout : ¬ IsInnerAut (descAut L ⟨c, hc⟩)) : InducesStdKind L c .graphField := by
  obtain ⟨hn, F, _, _, τ, hF, hτ, ⟨φ⟩⟩ :=
    CFSG.Quasithin.F134.LieD4.exists_mulEquiv_graphFixedRootGroup hD4
  have hout' : InducesOuterTheta c L := by
    refine ⟨hc, fun hin => hout ?_⟩
    rw [← congr_thetaQuotMulAut_eq_descAut hθ hZ, isInnerAut_congr]
    exact hin
  exact .triality n hn F hF τ hτ
    (inducesKindTriality_graphField hn hF hτ L hc3 hout' ((thetaBotEquiv hθ).trans φ))

end Kinds

section Transfer

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem autFix_normalizerMonoidHom_eq {L : Subgroup G} {c : G}
    (hc : c ∈ Subgroup.normalizer (L : Set G)) :
    autFix (L.normalizerMonoidHom ⟨c, hc⟩) = (L ⊓ Subgroup.centralizer {c}).subgroupOf L := by
  ext l
  rw [mem_autFix, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    refine ⟨l.2, ?_⟩
    show (l : G) ∈ Subgroup.centralizer {c}
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h' : c * (l : G) * c⁻¹ = l := congrArg Subtype.val h
    calc (l : G) * c = c * l * c⁻¹ * c := by rw [h']
      _ = c * l := by group
  · intro h
    apply Subtype.ext
    change c * (l : G) * c⁻¹ = l
    rw [← Subgroup.mem_centralizer_singleton_iff.mp h.2, mul_inv_cancel_right]

theorem normalizer_le_of_item4_5 (h45 : Item4_5) (hG : SectionFourHyp G) {A : Subgroup G}
    (hA : Late.IsE27 A) {c : G} (hc : c ∈ A) {L : Subgroup G} (hL : IsComponent L)
    {K' : Subgroup G} (hK'M : K' ≤ L ⊓ Subgroup.centralizer {c}) (hK'q : IsQuasisimple K')
    (hK'sn : (K'.subgroupOf (L ⊓ Subgroup.centralizer {c})).IsSubnormal) :
    A ≤ Subgroup.normalizer (K' : Set G) := by
  set C : Subgroup G := Subgroup.centralizer {c} with hC
  have hAC : A ≤ C := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨c, hc⟩)
  have hK'C : K' ≤ C := hK'M.trans inf_le_right
  have hMC : ((L ⊓ C).subgroupOf C).IsSubnormal := by
    have heq : (L ⊓ C).subgroupOf C = L.subgroupOf C := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
    rw [heq]
    exact hL.2.subgroupOf
  have hsn : (K'.subgroupOf C).IsSubnormal :=
    isSubnormal_subgroupOf_trans hK'M inf_le_right hK'sn hMC
  have hmem : K' ∈ thetaComponentsIn C := by
    refine mem_thetaComponentsIn_iff.mpr ⟨hK'C, mem_thetaComponents_of_isComponent3 ⟨?_, hsn⟩⟩
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hK'C).symm hK'q
  exact Sec6.le_normalizer_of_mem_thetaComponentsIn_of_item4_5 h45
    (Sec4.sectionFourHyp_subgroup hG C) hAC hA.1 ⟨3, le_rfl, by rw [hA.2]; norm_num⟩ K' hmem

theorem row429_of_gen (h45 : Item4_5) {S : Type} [Group S]
    (h : ∀ (S' : Type) [Group S'] [Finite S'], IsSimpleGroup S' → (∃ a b : S', a * b ≠ b * a) →
      Nonempty (S' ≃* S) → ∀ (A : Subgroup (MulAut S')) (σ : MulAut S') (K : Subgroup S'),
        CfgS429 S' A σ K → SurvA10D4 S' σ K ∨ (SurvL3 S' σ K ∧ K429CoverL3)) :
    Row429 S := by
  intro G _ _ hG hθ hE A hA c hc hc1 L hL hLS hAN hAC hLc K hK K' hK' htype hcent
  have hK'M : K' ≤ L ⊓ Subgroup.centralizer {c} := hK' ▸ Subgroup.map_subtype_le K
  have hK'L : K' ≤ L := hK'M.trans inf_le_left
  have eK : K ≃* K' := (K.equivMapOfInjective _ (Subgroup.subtype_injective _)).trans
    (MulEquiv.subgroupCongr hK'.symm)
  have hK'q : IsQuasisimple K' := CFSG.LocalCores.isQuasisimple_of_mulEquiv eK hK.1
  have hK'sn : (K'.subgroupOf (L ⊓ Subgroup.centralizer {c})).IsSubnormal := by
    rw [hK', Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
      (Subgroup.subtype_injective _)]
    exact hK.2
  have hK'type : IsType429 (K' ⧸ CFSG.pCore 2 K') :=
    isType429_of_mulEquiv (quotPCoreTwoCongr eK).symm htype
  have hAK' := normalizer_le_of_item4_5 h45 hG hA hc hL hK'M hK'q hK'sn
  obtain ⟨hinf, hcfg⟩ :=
    cfgS429_of hθ hA hc hL hAN hAC hLc hK'M hK'q hK'sn hK'type hAK' hcent
  haveI : IsSimpleGroup (L ⧸ Subgroup.center L) := hL.1.2.1
  have hconc := h (L ⧸ Subgroup.center L) hL.1.2.1 hL.1.2.2 hLS _ _ _ hcfg
  have hθL := theta_eq_bot_of_isComponent hθ hL
  have hZ3 := isPGroup_center_of_isComponent hθ hL
  have hc3 : c ^ 3 = 1 := hA.1.2 c hc
  have eKb := eK.trans (equivBar hK'L hinf)
  rcases hconc with hsurv | ⟨hsurv, hcov⟩
  · rcases hsurv with ⟨⟨φ⟩, ⟨ψ⟩⟩ | ⟨n, hn, hKn, hD4, hout⟩
    ·
      have hZ := center_eq_bot_of_alternating_ten hL.1 hZ3 ψ
      exact Or.inl ⟨⟨eKb.trans φ⟩, ⟨(quotCenterEquivOfEqBot hZ).trans ψ⟩⟩
    ·
      have hZ := center_eq_bot_of_trialityD4 hL.1 hZ3 hD4
      have hD4L : Blueprint.ChevalleyExceptionalModel L .trialityD4 2 n :=
        CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv (quotCenterEquivOfEqBot hZ) hD4
      exact Or.inr (Or.inr ⟨n, hn, isoLThreePi_of_mulEquiv eKb hKn, hD4L,
        inducesStdKind_graphField_of_not_inner hθL hZ (hAN hc) hc3 hD4L hout⟩)
  ·
    obtain ⟨n, hn, hKn, hSn, hfield⟩ := hsurv
    set α := L.normalizerMonoidHom ⟨c, hAN hc⟩ with hα
    have hα3 : α ^ 3 = 1 := by
      rw [hα, ← map_pow]
      have : (⟨c, hAN hc⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 := Subtype.ext hc3
      rw [this, map_one]
    have hfix : autFix α = (L ⊓ Subgroup.centralizer {c}).subgroupOf L :=
      autFix_normalizerMonoidHom_eq (hAN hc)
    have hfixK : K'.subgroupOf L ≤ autFix α := by
      rw [hfix]
      exact Subgroup.subgroupOf_mono L hK'M
    have hsnK : ((K'.subgroupOf L).subgroupOf (autFix α)).IsSubnormal := by
      rw [hfix]
      set e := Subgroup.subgroupOfEquivOfLe (inf_le_left : L ⊓ Subgroup.centralizer {c} ≤ L)
      have heq : (K'.subgroupOf L).subgroupOf ((L ⊓ Subgroup.centralizer {c}).subgroupOf L) =
          (K'.subgroupOf (L ⊓ Subgroup.centralizer {c})).comap e.toMonoidHom := by
        ext x
        simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
        rfl
      rw [heq]
      exact hK'sn.comap _
    have hK₁q : IsQuasisimple (K'.subgroupOf L) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hK'L).symm hK'q
    have hZ := hcov L hL.1 hZ3 n hn hSn α hα3 hfield _ hfixK hK₁q hsnK hinf
    exact Or.inr (Or.inl ⟨n, hn, isoLThreePi_of_mulEquiv eKb hKn,
      isoLThreePi_of_mulEquiv (quotCenterEquivOfEqBot hZ) hSn,
      inducesStdKind_field_of_isFieldAutL3 hθL hZ (hAN hc) hfield⟩)

theorem rowOf429_of_rowS (h45 : Item4_5) (hcov : K429CoverL3) {X : Type} [Group X]
    (h : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* X) → RowS429 S) : RowOf429 X := by
  intro S _ _ _ _ ⟨eSX⟩
  refine row429_of_gen h45 fun S' _ _ hs hna ⟨e'⟩ A σ K hc => ?_
  exact ((h S' hs hna ⟨e'.trans eSX⟩ A σ K hc).2).imp id fun h => ⟨h, hcov⟩

end Transfer

end CFSG.RankThree.PartTwo.Sec4.RonanK429
