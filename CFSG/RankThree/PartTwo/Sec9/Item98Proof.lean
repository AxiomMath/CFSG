module

public import CFSG.RankThree.PartTwo.Sec11.Item116
import CFSG.RankThree.PartTwo.Sec9.Hyp92Never
import CFSG.RankThree.PartTwo.Sec8.TransferExtremal
import CFSG.RankThree.PartTwo.KFacts.K71bOutAbelian

public section

namespace CFSG.RankThree.PartTwo.Sec9

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

section General

variable {G : Type} [Group G] [Finite G]

theorem commutator_mem_innerPreimage_of_isInnerAut {L : Subgroup G}
    (hOut : ∀ σ τ : MulAut (L ⧸ aschbacherSolvableCore 3 L),
      KFacts.IsInnerAut (σ * τ * σ⁻¹ * τ⁻¹)) {n y : G}
    (hn : n ∈ Subgroup.normalizer (L : Set G)) (hy : y ∈ Subgroup.normalizer (L : Set G)) :
    n * y * n⁻¹ * y⁻¹ ∈ Sec11.innerPreimage L := by
  set ρ := (Sec4.thetaQuotMulAut L).comp (Sec4.compAction L)
  have hm : n * y * n⁻¹ * y⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hn hy)
      (Subgroup.inv_mem _ hn)) (Subgroup.inv_mem _ hy)
  refine Sec11.mem_innerPreimage_iff.mpr ⟨hm, ?_⟩
  have e : (⟨n * y * n⁻¹ * y⁻¹, hm⟩ : Subgroup.normalizer (L : Set G)) =
      ⟨n, hn⟩ * ⟨y, hy⟩ * (⟨n, hn⟩ : Subgroup.normalizer (L : Set G))⁻¹ *
        (⟨y, hy⟩ : Subgroup.normalizer (L : Set G))⁻¹ := rfl
  change ρ _ ∈ _
  rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
  exact hOut _ _

end General


section Hyp

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R : Subgroup G}

theorem Hyp91.thetaQuot_facts_of_item96 (h96 : Item96) (h : Hyp91 G A c L a R) :
    Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ ∧
      3 ∣ Nat.card (L ⧸ aschbacherSolvableCore 3 L) ∧
      ∀ σ τ : MulAut (L ⧸ aschbacherSolvableCore 3 L),
        KFacts.IsInnerAut (σ * τ * σ⁻¹ * τ⁻¹) := by
  rcases h96 G A c L a R h with he | hl
  · obtain ⟨e⟩ := he
    set e' := e.trans (Sec4.projSLEquivPSL (GaloisField 3 3))
    refine ⟨KFacts.center_eq_bot_of_mulEquiv_of_center_eq_bot e'
        (GorensteinWalter.psl2_center_eq_bot _), ?_,
      KFacts.isInnerAut_commutator_of_mulEquiv_psl2_all e'⟩
    rw [Nat.card_congr e'.toEquiv]
    exact KFacts.three_dvd_card_psl2 _
  · exact ⟨Sec11.center_eq_bot_of_isList1016 hl, Sec11.three_dvd_card_of_isList1016 hl,
      KFacts.isInnerAut_commutator_of_isList1016_all hl⟩

theorem Hyp91.normalizer_zpowers_le_normalizer_of_center (h45 : Sec4.Item4_5)
    (h : Hyp91 G A c L a R) (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥)
    (h3 : 3 ∣ Nat.card (L ⧸ aschbacherSolvableCore 3 L)) :
    Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  by_contra hne
  set Ln := L.map (MulAut.conj n).toMonoidHom with hLn
  have hcn : Subgroup.centralizer ({(MulAut.conj n) c} : Set G) =
      Subgroup.centralizer ({c} : Set G) := by
    have hz : Subgroup.zpowers ((MulAut.conj n) c) = Subgroup.zpowers c := by
      have h1 := Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
      rw [MonoidHom.map_zpowers] at h1
      exact h1
    rw [GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers,
      GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers, hz]
  have hLnc : Ln ∈ thetaComponentsAt 3 c := by
    have h1 := map_mem_thetaComponentsAt (MulAut.conj n) h.mem_thetaComponentsAt
    rw [thetaComponentsAt_eq_thetaComponentsIn, hcn] at h1
    exact h1
  have hZn : Subgroup.center (Ln ⧸ aschbacherSolvableCore 3 Ln) = ⊥ :=
    KFacts.center_eq_bot_of_mulEquiv_of_center_eq_bot
      (Sec13.thetaQuotEquiv (MulAut.conj n) L).symm hZ
  have h3n : 3 ∣ Nat.card Ln := by
    rw [hLn, Subgroup.card_map_of_injective (MulAut.conj n).injective]
    exact h3.trans (Subgroup.card_quotient_dvd_card _)
  exact Sec11.not_three_dvd_of_mem_thetaComponentsAt_ne h45 h hLnc hne hZn h3n

end Hyp

theorem item98_of (h45 : Sec4.Item4_5) (h96 : Item96) : Item98 := by
  intro G _ _ A c L a R h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hZ, h3, hOut⟩ := h.thetaQuot_facts_of_item96 h96
  have hHL := h.normalizer_zpowers_le_normalizer_of_center h45 hZ h3
  by_contra hcon
  push Not at hcon
  have hAel : CFSG.Assembly.IsElemAbelian 3 A := h.mem_partTwoF.1
  have hAmax := h.mem_partTwoF.2.1
  have hexp : ∀ x ∈ A, x ^ 3 = 1 := hAel.2
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAel.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hcA := h.mem_A
  have haA := h.a_mem
  have hco : orderOf c = 3 := orderOf_eq_prime (hexp c hcA) h.ne_one
  have hAR : A ≤ R := Sec10.le_of_hyp91 h
  have hRH := h.isSylowOf.le
  have hRC : R ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec11.le_centralizer_of_le_normalizer_zpowers hco h.isSylowOf.isPGroup hRH
  have hc3 : ∀ g : G, (g * c * g⁻¹) ^ 3 = 1 := fun g => by
    rw [conj_pow, hexp c hcA, mul_one, mul_inv_cancel]
  have hH : ∀ g : G, (∀ x ∈ A, g * c * g⁻¹ * x = x * (g * c * g⁻¹)) →
      g ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    intro g hg
    have hgA := mem_of_commute_of_maximal hAel hAmax (hc3 g) hg
    have h1 : (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom =
        Subgroup.zpowers (g * c * g⁻¹) := by
      rw [MonoidHom.map_zpowers]
      rfl
    have h2 := hcon g (by rw [h1, Subgroup.zpowers_le]; exact hgA)
    rw [h1] at h2
    apply Sec10.mem_normalizer_zpowers_of_conj_mem
    rw [← h2]
    exact Subgroup.mem_zpowers _
  have hconj : ∀ g : G, (∀ x ∈ A, g⁻¹ * x * g ∈ R) →
      ∀ x ∈ A, g * c * g⁻¹ * x = x * (g * c * g⁻¹) := by
    intro g hg x hx
    have h2 : (g⁻¹ * x * g) * c = c * (g⁻¹ * x * g) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hRC (hg x hx))
    calc g * c * g⁻¹ * x = g * (c * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * c) * g⁻¹ := by rw [h2]
      _ = x * (g * c * g⁻¹) := by group
  have hRG : IsSylowOf 3 R ⊤ := by
    refine Sec12.isSylowOf_of_normalizer_le h.isSylowOf le_top ?_
    rintro g ⟨-, hg⟩
    refine hH g (hconj g fun x hx => ?_)
    have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) x).mp (hAR hx)
    simpa using h1
  obtain ⟨P, hP⟩ := exists_sylow_coe_eq hRG
  have htop : commutator G = ⊤ := by
    have hG := h.toTheoremFourHyp
    have := hG.isSimpleGroup
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h1 | h1
    · obtain ⟨x, y, hxy⟩ := hG.nonabelian
      exact absurd ((commutator_eq_bot_iff G).mp h1) fun hc => hxy (hc.is_comm.comm x y)
    · exact h1
  have haN : a ∈ Subgroup.normalizer (L : Set G) := hHL (hRH (hAR haA))
  have habel : ∀ y ∈ (P : Subgroup G), ∀ z ∈ (P : Subgroup G),
      y * z * y⁻¹ * z⁻¹ ∈ Sec11.innerPreimage L := by
    intro y hy z hz
    rw [hP] at hy hz
    exact commutator_mem_innerPreimage_of_isInnerAut hOut (hHL (hRH hy)) (hHL (hRH hz))
  have haI : a ∉ Sec11.innerPreimage L := by
    intro ha
    obtain ⟨haN₁, hinn⟩ := Sec11.mem_innerPreimage_iff.mp ha
    obtain ⟨haN₂, hout⟩ := h.toHyp81.inducesOuterTheta
    exact hout hinn
  have hfus : ∀ g : G,
      (∀ y ∈ (P : Subgroup G) ⊓ Subgroup.centralizer {a}, g⁻¹ * y * g ∈ (P : Subgroup G)) →
        a⁻¹ * (g⁻¹ * a * g) ∈ Sec11.innerPreimage L := by
    intro g hg
    rw [hP] at hg
    have hgH := hH g (hconj g fun x hx => hg x
      ⟨hAR hx, Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx a haA)⟩)
    have h1 := commutator_mem_innerPreimage_of_isInnerAut hOut (Subgroup.inv_mem _ haN)
      (Subgroup.inv_mem _ (hHL hgH))
    simpa [mul_assoc] using h1
  exact Sec8.commutator_ne_top_of_extremal P habel (by rw [hP]; exact hAR haA) haI (hexp a haA)
    hfus htop

end CFSG.RankThree.PartTwo.Sec9
