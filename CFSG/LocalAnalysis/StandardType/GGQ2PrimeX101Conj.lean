module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeSplit
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIICoverU62Model
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankClsUnitary
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Plane
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport
public import CFSG.ClassicalGroups.Unitary.Simple
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import Certificates.Certificate1003
public import Certificates.Certificate1009
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614PrimeDefs

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open CFSG.Models CFSG.Assembly CFSG.StandardType CFSG.Fischer

private theorem x101_centralizer_le_normalizer {G : Type} [Group G] (L : Subgroup G) :
    centralizer (L : Set G) ≤ normalizer (L : Set G) := by
  intro c hc
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have e1 : h * c = c * h := mem_centralizer_iff.1 hc h hh
    have e2 : c * h * c⁻¹ = h := by rw [← e1]; group
    rw [e2]
    exact hh
  · intro hh
    have e2 : c * h * c⁻¹ * c = c * (c * h * c⁻¹) := mem_centralizer_iff.1 hc _ hh
    have e3 : h = c * h * c⁻¹ := by
      calc h = c⁻¹ * (c * h * c⁻¹ * c) := by group
        _ = c⁻¹ * (c * (c * h * c⁻¹)) := by rw [e2]
        _ = c * h * c⁻¹ := by group
    rw [e3]
    exact hh

private theorem x101_mem_centralizer_of_conj {G : Type} [Group G] (L : Subgroup G) {s e : G}
    (hs : ∀ l ∈ L, s * l * s⁻¹ = e * l * e⁻¹) : e⁻¹ * s ∈ centralizer (L : Set G) := by
  rw [mem_centralizer_iff]
  intro l hl
  have h2 : s * l = e * l * e⁻¹ * s := by
    calc s * l = s * l * s⁻¹ * s := by group
      _ = e * l * e⁻¹ * s := by rw [hs l hl]
  calc l * (e⁻¹ * s) = e⁻¹ * (e * l * e⁻¹ * s) := by group
    _ = e⁻¹ * (s * l) := by rw [h2]
    _ = e⁻¹ * s * l := by group

private theorem x101_not_isCyclic_card_nine {H : Type} [Group H]
    (hc : Nat.card H = 9) (he : ∀ h : H, h ^ 3 = 1) : ¬IsCyclic H := by
  intro hcyc
  have hexp : Monoid.exponent H ∣ 3 := Monoid.exponent_dvd_of_forall_pow_eq_one he
  rw [IsCyclic.exponent_eq_card, hc] at hexp
  norm_num at hexp

private theorem x101_false_of_split_embedding {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hcyc : ∀ S : Subgroup G, S ≤ centralizer (L : Set G) → IsPGroup 3 S → IsCyclic S)
    {X : Type} [Group X] (ψ : X →* G) (hψN : ∀ y, ψ y ∈ normalizer (L : Set G))
    (hdec : ∀ y, ∃ e ∈ L, ∃ c ∈ centralizer (L : Set G), ψ y = e * c)
    (hinj : ∀ y, ψ y ∈ L → y = 1) (E : Subgroup X) (hEcard : Nat.card E = 9)
    (hEexp : ∀ e ∈ E, e ^ 3 = 1) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let f0 := (QuotientGroup.mk' (L.subgroupOf (normalizer (L : Set G)))).comp
    (Subgroup.inclusion (x101_centralizer_le_normalizer L))
  let φQ := (QuotientGroup.mk' (L.subgroupOf (normalizer (L : Set G)))).comp
    (ψ.codRestrict (normalizer (L : Set G)) hψN)
  have hmem : ∀ y, φQ y ∈ f0.range := by
    intro y
    obtain ⟨e, he, c, hc, hyc⟩ := hdec y
    refine MonoidHom.mem_range.2 ⟨⟨c, hc⟩, ?_⟩
    have hcomm : e * c = c * e := mem_centralizer_iff.1 hc e he
    refine QuotientGroup.eq.2 ?_
    rw [Subgroup.mem_subgroupOf]
    show c⁻¹ * ψ y ∈ L
    rw [hyc, hcomm, inv_mul_cancel_left]
    exact he
  let h' := φQ.codRestrict f0.range hmem
  have hinj' : Function.Injective h' := by
    refine (MonoidHom.ker_eq_bot_iff h').1 (eq_bot_iff.2 fun a ha => ?_)
    have h1 : φQ a = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 ha)
    have h2 := (QuotientGroup.eq_one_iff _).1 h1
    exact Subgroup.mem_bot.2 (hinj a (Subgroup.mem_subgroupOf.1 h2))
  let F := E.map h'
  have hFcard : Nat.card F = 9 := (Subgroup.card_map_of_injective hinj').trans hEcard
  have hFexp : ∀ f : F, f ^ 3 = 1 := by
    rintro ⟨f, hf⟩
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hf
    apply Subtype.ext
    show h' e ^ 3 = 1
    rw [← map_pow, hEexp e he, map_one]
  have hFp : IsPGroup 3 F := fun f => ⟨1, by rw [pow_one]; exact hFexp f⟩
  obtain ⟨S, hSC, hSp, hSnc⟩ := CFSG.StandardType.exists_noncyclic_of_noncyclic_quot
    f0.rangeRestrict f0.rangeRestrict_surjective hFp
    (x101_not_isCyclic_card_nine hFcard hFexp)
  exact hSnc (hcyc S hSC hSp)

open CFSG.ComponentClassification.OuterAutomorphisms in
private theorem x101_outer_hom_trivial
    {G : Type} [Group G] {L : Subgroup G} [Group.IsPerfect L]
    (hm : CFSG.Blueprint.LieModel (L ⧸ center L) .PSU 6 2 1) {X : Type} [Group X]
    [IsSimpleGroup X] (hcard : 6 < Nat.card X) (Φ : X →* Outer L) : ∀ y, Φ y = 1 := by
  obtain ⟨e0⟩ := CFSG.LieType.Multipliers.U62.nonempty_mulEquiv_T46 hm
  have hdvd := CFSG.ComponentClassification.RankTwoHypIICover.U62.card_outer_T46_dvd
  haveI : Finite (Outer T46) := Nat.finite_of_card_ne_zero fun h0 => by
    rw [h0] at hdvd
    norm_num at hdvd
  have hker : MonoidHom.ker Φ = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MonoidHom.ker Φ) with hb | ht
    · exfalso
      have hinj : Function.Injective fun y => equivalence e0 (centerQuotientOuterHom L (Φ y)) :=
        (equivalence e0).injective.comp ((centerQuotient_outer_injective L).comp
          ((MonoidHom.ker_eq_bot_iff Φ).1 hb))
      have h1 := Nat.card_le_card_of_injective _ hinj
      have h2 := Nat.le_of_dvd (by norm_num) hdvd
      omega
    · exact ht
  intro y
  exact MonoidHom.mem_ker.1 (by rw [hker]; exact Subgroup.mem_top y)

private theorem x101_psu52_data {G : Type} [Group G] {X : Subgroup G}
    (hX : LieModel X .PSU 5 2 1) :
    IsSimpleGroup X ∧ ∃ E : Subgroup X, Nat.card E = 9 ∧ ∀ e ∈ E, e ^ 3 = 1 := by
  have hc : StatedClassicalModel X .PSU 5 2 1 := by
    rcases hX with ⟨-, h | ⟨h0, -⟩⟩
    · exact h
    · exact absurd h0 (by norm_num)
  obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := hc.2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := ringChar.of_eq (CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq
    (f := 2) Nat.prime_two (by norm_num) (hK.trans (by norm_num)))
  have hsimp : IsSimpleGroup X := (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity X 5 2 1 hc).2
  have hrank :=
    CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankCls.psu_two_le_pRank_three_of_four_le
      (p := 2) (f := 1) hK le_rfl (by norm_num) (n := 5) (by norm_num)
  obtain ⟨E0, -, hE0ab, hE0card⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.exists_isElemAbelian_of_le_pRank Nat.prime_three hrank
  have hinjE : Function.Injective e.symm.toMonoidHom := e.symm.injective
  refine ⟨hsimp, E0.map e.symm.toMonoidHom, ?_, fun g hg => ?_⟩
  · exact (Subgroup.card_map_of_injective hinjE).trans (hE0card.trans (by norm_num))
  · obtain ⟨g0, hg0, rfl⟩ := Subgroup.mem_map.1 hg
    rw [← map_pow, hE0ab.2 g0 hg0, map_one]

open CFSG.ComponentClassification.OuterAutomorphisms in
theorem le_map_conj_of_lieModel
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L : Subgroup G} (h : Q2pSetting B Bs x L) (g : G) {X : Subgroup G}
    (hX : LieModel X .PSU 5 2 1) (hXz : X ≤ centralizer ({g * x * g⁻¹} : Set G)) :
    X ≤ L.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨-, -, -, -, hcyc, hperf, -, -⟩ := ggThmIHyp_unpack h.hyp
  haveI : Group.IsPerfect L := ⟨hperf⟩
  have hN : centralizer ({x} : Set G) ≤ normalizer (L : Set G) := L_norm_of_U62 h.hyp h.model
  obtain ⟨ψ, hψ⟩ : ∃ ψ : X →* G, ∀ y : X, ψ y = g⁻¹ * (y : G) * g :=
    ⟨(MulAut.conj g⁻¹).toMonoidHom.comp X.subtype, fun y => by simp [MulAut.conj_apply]⟩
  have hψC : ∀ y : X, ψ y ∈ centralizer ({x} : Set G) := by
    intro y
    have hc := mem_centralizer_singleton_iff.1 (hXz y.2)
    rw [mem_centralizer_singleton_iff, hψ y]
    calc g⁻¹ * (y : G) * g * x = g⁻¹ * ((y : G) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (y : G)) * g := by rw [hc]
      _ = x * (g⁻¹ * (y : G) * g) := by group
  have hψN : ∀ y : X, ψ y ∈ normalizer (L : Set G) := fun y => hN (hψC y)
  obtain ⟨hsimp, E, hEcard, hEexp⟩ := x101_psu52_data hX
  haveI : IsSimpleGroup X := hsimp
  have hcard : 6 < Nat.card X := by
    have hle : Nat.card E ≤ Nat.card X := by apply Subgroup.card_le_card_group
    omega
  let φN : X →* normalizer (L : Set G) := ψ.codRestrict (normalizer (L : Set G)) hψN
  let act : X →* MulAut L := L.normalizerMonoidHom.comp φN
  have hactG : ∀ (y : X) (l : L), ((act y l : L) : G) = ψ y * (l : G) * (ψ y)⁻¹ :=
    fun y l => rfl
  let Φ : X →* Outer L := (QuotientGroup.mk' (inner L)).comp act
  have hΦ : ∀ y, Φ y = 1 := x101_outer_hom_trivial h.model hcard Φ
  have hact : ∀ y : X, ∃ e : L, MulAut.conj e = act y := by
    intro y
    have h1 : (QuotientGroup.mk (act y) : MulAut L ⧸ inner L) = 1 := hΦ y
    exact MonoidHom.mem_range.1 ((QuotientGroup.eq_one_iff _).1 h1)
  have hdec : ∀ y : X, ∃ e ∈ L, ∃ c ∈ centralizer (L : Set G), ψ y = e * c := by
    intro y
    obtain ⟨e, he⟩ := hact y
    have hs : ∀ l ∈ L, ψ y * l * (ψ y)⁻¹ = (e : G) * l * (e : G)⁻¹ := by
      intro l hl
      have h1 := congrArg (fun t : MulAut L => ((t ⟨l, hl⟩ : L) : G)) he
      exact (hactG y ⟨l, hl⟩).symm.trans h1.symm
    exact ⟨(e : G), e.2, (e : G)⁻¹ * ψ y, x101_mem_centralizer_of_conj L hs, by group⟩
  haveI hKn : (L.comap ψ).Normal := ⟨fun k hk y => by
    rw [Subgroup.mem_comap] at hk ⊢
    rw [map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.1 (hψN y) (ψ k)).1 hk⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (L.comap ψ) with hbot | htop
  · have hinj : ∀ y : X, ψ y ∈ L → y = 1 := fun y hy => by
      have hyK : y ∈ L.comap ψ := Subgroup.mem_comap.2 hy
      rw [hbot] at hyK
      exact Subgroup.mem_bot.1 hyK
    exact (x101_false_of_split_embedding hcyc ψ hψN hdec hinj E hEcard hEexp).elim
  · intro y hy
    have hyK : (⟨y, hy⟩ : X) ∈ L.comap ψ := by
      rw [htop]
      exact Subgroup.mem_top _
    refine Subgroup.mem_map.2 ⟨ψ ⟨y, hy⟩, Subgroup.mem_comap.1 hyK, ?_⟩
    rw [hψ]
    show g * (g⁻¹ * y * g) * g⁻¹ = y
    group

end CFSG.GGQ2Prime
