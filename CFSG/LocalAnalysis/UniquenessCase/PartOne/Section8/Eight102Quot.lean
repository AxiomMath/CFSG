module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsFive
import CFSG.LocalAnalysis.UniquenessCase.UC6R869T3
import CFSG.LocalAnalysis.UniquenessCase.UC6C636a
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ParabolicTransfer
import CFSG.GroupTheory.SteinbergBSQuotientLifting

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd rhoL)

variable {G : Type} [Group G] [Finite G]

theorem sec7Hyp_centralizer_of_notationA8103 {D : Data G} (hSg : SigmaStd D)
    {L P A : Subgroup G} {p n : ℕ} (hH : F08.Hyp8102 D L P p n)
    (hA : F08.NotationA8103 L P p n A) (hAM : ¬ centralizer (A : Set G) ≤ D.M) :
    F07.Sec7Hyp D p (centralizer (A : Set G)) := by
  obtain ⟨hp, hp2, -⟩ := prime_of_hyp8102 hSg hH
  have hns : ¬ Group.IsSolvable ↥D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.not_solvable_of_mem_calC hH.1
  have hsp : IsStronglyPEmbedded p D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.sp_of_mem_sig hSg hns hH.2.2.2.1
  have hA3 : Nat.card A = 3 := hA.1
  have hAne : A ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hA3
    omega
  have hCne : centralizer (A : Set G) ≠ ⊤ := by
    intro htop
    haveI : IsSimpleGroup G := D.standing.simple
    have hAle : A ≤ Subgroup.center G := by
      intro a ha
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ centralizer (A : Set G) := htop ▸ Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_iff.mp hg a ha).symm
    have hcenter : Subgroup.center G = ⊥ :=
      CFSG.GorensteinWalter.Helpers.center_eq_bot_of_noncommutative D.standing.nonab
    have : A = ⊥ := le_bot_iff.mp (hcenter ▸ hAle)
    exact hAne this
  have hrank : 1 < Open.pRank p (centralizer (A : Set G) ⊓ D.M) := by
    have hmono : Open.pRank p (L ⊓ centralizer (A : Set G)) ≤
        Open.pRank p (centralizer (A : Set G) ⊓ D.M) := by
      refine CFSG.SectionRank.pRank_mono hp.one_lt ?_
      intro x hx
      exact ⟨hx.2, hH.1.1.le hx.1⟩
    rwa [hA.2.2.2] at hmono
  exact ⟨hp, hp2, hsp, hCne, hAM, hrank⟩

theorem solvable_or_altTen_of_sec7Hyp {D : Data G} (h72 : F07.R72 D)
    (hKF7 : KStrongEmbedded72) {p : ℕ} {H : Subgroup G} (hS : F07.Sec7Hyp D p H) :
    Group.IsSolvable ↥(F07.ImageModK p H (H ⊓ D.M)) ∨
      (p = 5 ∧ (F07.ImageModK p H (Opp p H)).Normal ∧
        genFittingFStar (F07.QuotK7 p H) ≤ F07.ImageModK p H (Opp p H) ∧
        IsAlt ↥(F07.ImageModK p H (Opp p H)) 10 ∧
        ∀ Y : Subgroup (F07.QuotK7 p H), Y ≤ F07.ImageModK p H (H ⊓ D.M) → ⁅Y, Y⁆ = Y →
          ∀ (S : Type) [Group S], IsSimpleGroup S → ∀ f : ↥Y →* S, Function.Surjective f →
            IsAlt S 5) := by
  classical
  have hp : p.Prime := hS.1
  have hp2 : p ≠ 2 := hS.2.1
  have hM : IsStronglyPEmbedded p D.M := hS.2.2.1
  have hHM : ¬ H ≤ D.M := hS.2.2.2.2.1
  have hrank : 2 ≤ Open.pRank p (H ⊓ D.M) := by
    have := hS.2.2.2.2.2
    omega
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hFstar, hshape⟩ := r72Shape_of_r72 h72 hS
  have hLHnorm : (F07.ImageModK p H (Opp p H)).Normal := by
    have hOppH : ((Opp p H).subgroupOf H).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have hg : (g : G) ∈ Subgroup.normalizer (Opp p H : Set G) :=
        CFSG.LocalAnalysis.UniquenessCase.UC6.mem_normalizer_Opp_uc6
          (Subgroup.le_normalizer g.2) p
      exact (Subgroup.mem_normalizer_iff.mp hg n).mp hn
    have h := hOppH.map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))
      (QuotientGroup.mk'_surjective _)
    simpa [F07.ImageModK] using h
  have hNstrong : IsStronglyPEmbedded p (F07.ImageModK p H (H ⊓ D.M)) :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.R869S.isStronglyPEmbedded_map_quotient_pPrimeCore
      hp hM hHM hrank
  have hOp : CFSG.pPrimeCore p (F07.QuotK7 p H) = ⊥ := CFSG.pPrimeCore_quotient_eq_bot hp
  have hKF := hKF7 p hp hp2 (F07.QuotK7 p H) hOp (F07.ImageModK p H (Opp p H)) hLHnorm
    hFstar hshape (F07.ImageModK p H (H ⊓ D.M)) hNstrong
  rcases hKF with hsol | ⟨hp5, hAlt, hquot⟩
  · exact Or.inl hsol
  · exact Or.inr ⟨hp5, hLHnorm, hFstar, hAlt, hquot⟩

theorem le_pPrimeCoreIn_of_isSolvable {p : ℕ} {H N J : Subgroup G} (hNH : N ≤ H)
    (hJN : J ≤ N) (hJ : ⁅J, J⁆ = J) (hsol : Group.IsSolvable ↥(F07.ImageModK p H N)) :
    J ≤ F07.PPrimeCoreIn p H := by
  classical
  have hJH : J ≤ H := hJN.trans hNH
  haveI : (CFSG.pPrimeCore p ↥H).Normal := CFSG.pPrimeCore_normal
  let π : ↥H →* F07.QuotK7 p H := QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)
  have hYle : (J.subgroupOf H).map π ≤ F07.ImageModK p H N :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono H hJN)
  have hJJ : ⁅J.subgroupOf H, J.subgroupOf H⁆ = J.subgroupOf H := by
    refine Subgroup.map_injective H.subtype_injective ?_
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hJH, hJ]
  have hYperf : ⁅(J.subgroupOf H).map π, (J.subgroupOf H).map π⁆ =
      (J.subgroupOf H).map π := by
    rw [← Subgroup.map_commutator, hJJ]
  have hYbot : (J.subgroupOf H).map π = ⊥ := by
    by_contra hne
    haveI : Group.IsSolvable ↥(F07.ImageModK p H N) := hsol
    have hYne : ((J.subgroupOf H).map π).subgroupOf (F07.ImageModK p H N) ≠ ⊥ := by
      intro h0
      apply hne
      rw [← Subgroup.map_subgroupOf_eq_of_le hYle, h0, Subgroup.map_bot]
    have hlt := Group.IsSolvable.commutator_lt_of_ne_bot hYne
    have heq : ⁅((J.subgroupOf H).map π).subgroupOf (F07.ImageModK p H N),
        ((J.subgroupOf H).map π).subgroupOf (F07.ImageModK p H N)⁆ =
        ((J.subgroupOf H).map π).subgroupOf (F07.ImageModK p H N) := by
      refine Subgroup.map_injective (F07.ImageModK p H N).subtype_injective ?_
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hYle]
      exact hYperf
    rw [heq] at hlt
    exact lt_irrefl _ hlt
  intro x hx
  have hxH : x ∈ H := hJH hx
  have hxmap : π (⟨x, hxH⟩ : ↥H) ∈ (J.subgroupOf H).map π :=
    Subgroup.mem_map_of_mem (f := π) (Subgroup.mem_subgroupOf.mpr hx)
  rw [hYbot] at hxmap
  have hx1 : π ⟨x, hxH⟩ = 1 := by simpa using hxmap
  have hxker : (⟨x, hxH⟩ : ↥H) ∈ π.ker := MonoidHom.mem_ker.mpr hx1
  rw [show π.ker = CFSG.pPrimeCore p ↥H from QuotientGroup.ker_mk' _] at hxker
  exact Subgroup.mem_map_of_mem H.subtype hxker

private theorem ker_mk'_comp_inclusion {p : ℕ} {H J : Subgroup G} (hJH : J ≤ H) :
    ((QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)).comp (Subgroup.inclusion hJH)).ker =
      (F07.PPrimeCoreIn p H).subgroupOf J := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    exact Subgroup.mem_map_of_mem H.subtype ((QuotientGroup.eq_one_iff _).mp h)
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have hy' : Subgroup.inclusion hJH x = y := Subtype.ext hyx.symm
    exact (QuotientGroup.eq_one_iff _).mpr (hy' ▸ hy)

private theorem pPrimeCoreIn_subgroupOf_le_pCore {p : ℕ} (hp : p.Prime) {H J : Subgroup G}
    (hJH : J ≤ H) (hsimp : IsSimpleGroup (Bar2 J)) (hpJ : p ∣ Nat.card (Bar2 J)) :
    (F07.PPrimeCoreIn p H).subgroupOf J ≤ CFSG.pCore 2 ↥J := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsSimpleGroup (Bar2 J) := hsimp
  haveI : (CFSG.pCore 2 ↥J).Normal := CFSG.pCore_normal
  haveI hKbarNorm : ((F07.PPrimeCoreIn p H).subgroupOf J).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have hconj : (⟨(g : G), hJH g.2⟩ : ↥H) * y * (⟨(g : G), hJH g.2⟩ : ↥H)⁻¹ ∈
        CFSG.pPrimeCore p ↥H := CFSG.pPrimeCore_normal.conj_mem y hy _
    have hval : H.subtype ((⟨(g : G), hJH g.2⟩ : ↥H) * y * (⟨(g : G), hJH g.2⟩ : ↥H)⁻¹) =
        (g : G) * (x : G) * (g : G)⁻¹ := by
      rw [← hyx]
      rfl
    have hcoe : ((g * x * g⁻¹ : ↥J) : G) = (g : G) * (x : G) * (g : G)⁻¹ := rfl
    rw [hcoe, ← hval]
    exact Subgroup.mem_map_of_mem H.subtype hconj
  by_contra hle
  have hnen : Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥J))
      ((F07.PPrimeCoreIn p H).subgroupOf J) ≠ ⊥ := by
    intro hbot
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    exact hle hbot
  have hnorm : (Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥J))
      ((F07.PPrimeCoreIn p H).subgroupOf J)).Normal :=
    Subgroup.Normal.map hKbarNorm _ (QuotientGroup.mk'_surjective _)
  rcases hnorm.eq_bot_or_eq_top with hbot | htop
  · exact hnen hbot
  · have hdvd : Nat.card ↥(Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥J))
        ((F07.PPrimeCoreIn p H).subgroupOf J)) ∣
        Nat.card ↥((F07.PPrimeCoreIn p H).subgroupOf J) := Subgroup.card_map_dvd _ _
    have hcardsub : Nat.card ↥((F07.PPrimeCoreIn p H).subgroupOf J) =
        Nat.card ↥(F07.PPrimeCoreIn p H ⊓ J) := by
      have h := Subgroup.card_map_of_injective
        (K := (F07.PPrimeCoreIn p H).subgroupOf J) J.subtype_injective
      rw [Subgroup.subgroupOf_map_subtype] at h
      exact h.symm
    have hcopK : p.Coprime (Nat.card ↥(F07.PPrimeCoreIn p H)) := by
      rw [F07.PPrimeCoreIn, Subgroup.card_map_of_injective H.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
    have hcop : p.Coprime (Nat.card ↥((F07.PPrimeCoreIn p H).subgroupOf J)) := by
      rw [hcardsub]
      exact Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hcopK
    have hpbar : p.Coprime (Nat.card (Bar2 J)) := by
      have h := Nat.Coprime.of_dvd_right hdvd hcop
      rwa [htop, Subgroup.card_top] at h
    exact (hp.coprime_iff_not_dvd.mp hpbar) hpJ

private theorem exists_surjective_imageModK_bar2 {p : ℕ} {H J : Subgroup G} (hJH : J ≤ H)
    (hK : (F07.PPrimeCoreIn p H).subgroupOf J ≤ CFSG.pCore 2 ↥J) :
    ∃ f : ↥(F07.ImageModK p H J) →* Bar2 J, Function.Surjective f := by
  classical
  haveI : (CFSG.pPrimeCore p ↥H).Normal := CFSG.pPrimeCore_normal
  haveI : (CFSG.pCore 2 ↥J).Normal := CFSG.pCore_normal
  let Y : Subgroup (F07.QuotK7 p H) := F07.ImageModK p H J
  let πH : ↥H →* F07.QuotK7 p H := QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)
  let φ : ↥J →* F07.QuotK7 p H := πH.comp (Subgroup.inclusion hJH)
  let ψ : ↥J →* Bar2 J := QuotientGroup.mk' (CFSG.pCore 2 ↥J)
  have hψ : Function.Surjective ψ := QuotientGroup.mk'_surjective _
  have hkerle : φ.ker ≤ ψ.ker := by
    rw [ker_mk'_comp_inclusion hJH]
    intro x hx
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff x).mpr (hK hx)
  have hYmem : ∀ x : ↥J, φ x ∈ Y := fun x =>
    Subgroup.mem_map_of_mem (f := πH) (Subgroup.mem_subgroupOf.mpr x.2)
  let q : ↥J →* ↥Y := φ.codRestrict Y hYmem
  have hqker : q.ker = (F07.PPrimeCoreIn p H).subgroupOf J := by
    have hqφ : q.ker = φ.ker := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext (by simpa [q] using h)⟩
    rw [hqφ, ker_mk'_comp_inclusion hJH]
  have hqle : q.ker ≤ ψ.ker := by
    rw [hqker, ← ker_mk'_comp_inclusion hJH]
    exact hkerle
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨z, hzK, hzy⟩ := Subgroup.mem_map.mp y.2
    refine ⟨⟨(z : G), Subgroup.mem_subgroupOf.mp hzK⟩, ?_⟩
    have hinc : (Subgroup.inclusion hJH ⟨(z : G), Subgroup.mem_subgroupOf.mp hzK⟩ : ↥H) = z :=
      Subtype.ext rfl
    exact Subtype.ext (by
      simpa only [q, φ, MonoidHom.codRestrict_apply, MonoidHom.comp_apply, hinc] using hzy)
  let f₀ : (↥J ⧸ q.ker) →* Bar2 J := QuotientGroup.lift q.ker ψ hqle
  have hf₀ : Function.Surjective f₀ :=
    QuotientGroup.lift_surjective_of_surjective q.ker ψ hψ hqle
  let e := QuotientGroup.quotientKerEquivOfSurjective q hq
  refine ⟨f₀.comp e.symm.toMonoidHom, ?_⟩
  intro y
  obtain ⟨x, hx⟩ := hf₀ y
  exact ⟨e x, by simpa [e] using hx⟩

theorem isAlt_five_bar2_of_perfect {p : ℕ} (hp : p.Prime) {H N J : Subgroup G} (hNH : N ≤ H)
    (hJN : J ≤ N) (hJ : ⁅J, J⁆ = J) (hsimp : IsSimpleGroup (Bar2 J))
    (hpJ : p ∣ Nat.card (Bar2 J))
    (hA5 : ∀ Y : Subgroup (F07.QuotK7 p H), Y ≤ F07.ImageModK p H N → ⁅Y, Y⁆ = Y →
      ∀ (S : Type) [Group S], IsSimpleGroup S → ∀ f : ↥Y →* S, Function.Surjective f →
        IsAlt S 5) :
    IsAlt (Bar2 J) 5 := by
  have hJH : J ≤ H := hJN.trans hNH
  have hK : (F07.PPrimeCoreIn p H).subgroupOf J ≤ CFSG.pCore 2 ↥J :=
    pPrimeCoreIn_subgroupOf_le_pCore hp hJH hsimp hpJ
  obtain ⟨f, hf⟩ := exists_surjective_imageModK_bar2 hJH hK
  have hYle : F07.ImageModK p H J ≤ F07.ImageModK p H N :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono H hJN)
  have hJJ : ⁅J.subgroupOf H, J.subgroupOf H⁆ = J.subgroupOf H := by
    refine Subgroup.map_injective H.subtype_injective ?_
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hJH, hJ]
  have hYperf : ⁅F07.ImageModK p H J, F07.ImageModK p H J⁆ = F07.ImageModK p H J := by
    show ⁅(J.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)),
      (J.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))⁆ =
      (J.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))
    rw [← Subgroup.map_commutator, hJJ]
  exact hA5 (F07.ImageModK p H J) hYle hYperf (Bar2 J) hsimp f hf

private theorem centralizer_imageModK {p : ℕ} (hp : p.Prime) {H U : Subgroup G} (hUH : U ≤ H)
    (hU : IsPGroup p U) (hcop : ¬ p ∣ Nat.card ↥(CFSG.pPrimeCore p ↥H)) :
    centralizer (((U.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)) :
        Subgroup (F07.QuotK7 p H)) : Set (F07.QuotK7 p H)) =
      ((H ⊓ centralizer (U : Set G)).subgroupOf H).map
        (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : (CFSG.pPrimeCore p ↥H).Normal := CFSG.pPrimeCore_normal
  have hU' : IsPGroup p ↥(U.subgroupOf H) :=
    hU.of_equiv (Subgroup.subgroupOfEquivOfLe hUH).symm
  have h := CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq (p := p)
    (N := CFSG.pPrimeCore p ↥H) hcop (Q := U.subgroupOf H) hU'
  rw [h]
  congr 1
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
    Subgroup.mem_centralizer_iff]
  constructor
  · intro hx
    refine ⟨x.2, fun z hz => ?_⟩
    exact congrArg Subtype.val (hx ⟨z, hUH hz⟩ (Subgroup.mem_subgroupOf.mpr hz))
  · rintro ⟨-, hx⟩ y hy
    exact Subtype.ext (hx (y : G) (Subgroup.mem_subgroupOf.mp hy))

private theorem exists_lift_imageModK {p : ℕ} (hp : p.Prime) {H E : Subgroup G} (hEH : E ≤ H)
    (hE : IsPGroup p E) (hcop : ¬ p ∣ Nat.card ↥(CFSG.pPrimeCore p ↥H))
    {Ũ : Subgroup (F07.QuotK7 p H)} (hŨ : Ũ ≤ F07.ImageModK p H E) :
    ∃ U : Subgroup G, U ≤ E ∧ Nat.card U = Nat.card Ũ ∧
      (U.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)) = Ũ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : (CFSG.pPrimeCore p ↥H).Normal := CFSG.pPrimeCore_normal
  have hE' : IsPGroup p ↥(E.subgroupOf H) :=
    hE.of_equiv (Subgroup.subgroupOfEquivOfLe hEH).symm
  let f : ↥(E.subgroupOf H) →* F07.QuotK7 p H :=
    (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)).comp (E.subgroupOf H).subtype
  have hfinj : Function.Injective f :=
    CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype hcop hE'
  have hfrange : f.range = F07.ImageModK p H E := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  let K : Subgroup ↥(E.subgroupOf H) := Ũ.comap f
  have hKmap : K.map f = Ũ := by
    show Subgroup.map f (Subgroup.comap f Ũ) = Ũ
    rw [Subgroup.map_comap_eq, hfrange, inf_eq_right.mpr hŨ]
  let g : ↥(E.subgroupOf H) →* G := H.subtype.comp (E.subgroupOf H).subtype
  have hgrange : g.range = E := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, Subgroup.map_subgroupOf_eq_of_le hEH]
  have hUE : K.map g ≤ E := (Subgroup.map_le_range g K).trans (le_of_eq hgrange)
  have hUg : (K.map g).subgroupOf H = K.map (E.subgroupOf H).subtype := by
    refine Subgroup.map_injective H.subtype_injective ?_
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hUE.trans hEH), Subgroup.map_map]
  refine ⟨K.map g, hUE, ?_, ?_⟩
  · have h1 : Nat.card ↥(K.map g) = Nat.card ↥K :=
      Subgroup.card_map_of_injective (f := g) (fun x y h => Subtype.ext (H.subtype_injective h))
    have h2 : Nat.card ↥(K.map f) = Nat.card ↥K :=
      Subgroup.card_map_of_injective (K := K) hfinj
    rw [h1, ← h2, hKmap]
  · rw [hUg, Subgroup.map_map, hKmap]

private theorem dvd_card_derInf_centralizer {p : ℕ} (hp : p.Prime) {H U : Subgroup G}
    (hUH : U ≤ H) (hU : IsPGroup p U) (hcop : ¬ p ∣ Nat.card ↥(CFSG.pPrimeCore p ↥H))
    {Ũ : Subgroup (F07.QuotK7 p H)}
    (hbar : (U.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)) = Ũ)
    (hd : p ∣ Nat.card (Hinf (centralizer (Ũ : Set (F07.QuotK7 p H))))) :
    p ∣ Nat.card (Hinf (H ⊓ centralizer (U : Set G))) := by
  have hC := centralizer_imageModK hp hUH hU hcop (U := U)
  have hCtilde : centralizer (Ũ : Set (F07.QuotK7 p H)) =
      ((H ⊓ centralizer (U : Set G)).subgroupOf H).map
        (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)) := by
    rw [← hbar]
    exact hC
  have hdvd : Nat.card (Hinf (centralizer (Ũ : Set (F07.QuotK7 p H)))) ∣
      Nat.card (Hinf (H ⊓ centralizer (U : Set G))) := by
    have h1 : Hinf (centralizer (Ũ : Set (F07.QuotK7 p H))) =
        (Hinf ((H ⊓ centralizer (U : Set G)).subgroupOf H)).map
          (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)) := by
      rw [hCtilde, Hinf_map]
    have h2 : (Hinf ((H ⊓ centralizer (U : Set G)).subgroupOf H)).map H.subtype =
        Hinf (H ⊓ centralizer (U : Set G)) := by
      rw [Hinf_map, Subgroup.map_subgroupOf_eq_of_le inf_le_left]
    rw [h1, ← h2, Subgroup.card_map_of_injective H.subtype_injective]
    exact Subgroup.card_map_dvd _ _
  exact hd.trans hdvd

theorem exists_two_centralizers_of_isAlt_ten (hK8 : KAltTen) {H E : Subgroup G} (hEH : E ≤ H)
    (hE : IsElemAbelian 5 E) (hEc : Nat.card E = 25)
    (hΛ : (F07.ImageModK 5 H (Opp 5 H)).Normal)
    (hF : genFittingFStar (F07.QuotK7 5 H) ≤ F07.ImageModK 5 H (Opp 5 H))
    (hAlt : IsAlt ↥(F07.ImageModK 5 H (Opp 5 H)) 10) :
    ∃ U₁ U₂ : Subgroup G, U₁ ≤ E ∧ U₂ ≤ E ∧ Nat.card U₁ = 5 ∧ Nat.card U₂ = 5 ∧ U₁ ≠ U₂ ∧
      5 ∣ Nat.card (F08.DerInf8 (H ⊓ centralizer (U₁ : Set G))) ∧
      5 ∣ Nat.card (F08.DerInf8 (H ⊓ centralizer (U₂ : Set G))) := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : (CFSG.pPrimeCore 5 ↥H).Normal := CFSG.pPrimeCore_normal
  let πH : ↥H →* F07.QuotK7 5 H := QuotientGroup.mk' (CFSG.pPrimeCore 5 ↥H)
  have hcop : ¬ 5 ∣ Nat.card ↥(CFSG.pPrimeCore 5 ↥H) :=
    (Nat.prime_five.coprime_iff_not_dvd).mp CFSG.pPrimeCore_coprime_card
  have hE5 : IsPGroup 5 E := hE.isPGroup
  have hEbar_el : IsElemAbelian 5 (F07.ImageModK 5 H E) := by
    have h := (hE.subgroupOf H).map πH
    simpa [F07.ImageModK] using h
  have hEbar_card : Nat.card (F07.ImageModK 5 H E) = 25 := by
    have hE' : IsPGroup 5 ↥(E.subgroupOf H) :=
      hE5.of_equiv (Subgroup.subgroupOfEquivOfLe hEH).symm
    have hinj := CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype
      (p := 5) (N := CFSG.pPrimeCore 5 ↥H) hcop (Q := E.subgroupOf H) hE'
    have h := Subgroup.card_map_of_injective (K := ⊤)
      (f := (QuotientGroup.mk' (CFSG.pPrimeCore 5 ↥H)).comp (E.subgroupOf H).subtype) hinj
    rw [Subgroup.map_top, MonoidHom.range_comp, Subgroup.range_subtype, Subgroup.card_top] at h
    have hI : F07.ImageModK 5 H E =
        Subgroup.map (QuotientGroup.mk' (CFSG.pPrimeCore 5 ↥H)) (E.subgroupOf H) := rfl
    rw [hI, h, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv, hEc]
  obtain ⟨Ũ₁, Ũ₂, hŨ₁, hŨ₂, hc₁, hc₂, hne, hd₁, hd₂⟩ :=
    hK8 (F07.QuotK7 5 H) (F07.ImageModK 5 H (Opp 5 H)) hΛ hF hAlt
      (F07.ImageModK 5 H E) hEbar_el hEbar_card
  obtain ⟨U₁, hU₁E, hcard₁, hbar₁⟩ := exists_lift_imageModK Nat.prime_five hEH hE5 hcop hŨ₁
  obtain ⟨U₂, hU₂E, hcard₂, hbar₂⟩ := exists_lift_imageModK Nat.prime_five hEH hE5 hcop hŨ₂
  refine ⟨U₁, U₂, hU₁E, hU₂E, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcard₁, hc₁]
  · rw [hcard₂, hc₂]
  · intro hEq
    exact hne (by rw [← hbar₁, ← hbar₂, hEq])
  · exact dvd_card_derInf_centralizer Nat.prime_five (hU₁E.trans hEH)
      (hE5.to_le hU₁E) hcop hbar₁ hd₁
  · exact dvd_card_derInf_centralizer Nat.prime_five (hU₂E.trans hEH)
      (hE5.to_le hU₂E) hcop hbar₂ hd₂

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
