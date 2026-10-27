module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36EqlStarCat
public import CFSG.LocalAnalysis.UniquenessCase.UC6K38Main
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Gls3PlusSporadic
import CFSG.LocalAnalysis.StronglyEmbedded.Normalizer
import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.RankThree.PartOne.StrongP (conjSub)
open CFSG.RankThree.PartOne.Census3 (sporadicsThm3)

@[expose] def K36SporSixNoStrongThree : Prop :=
  ∀ s : TauCeti.SporadicName, s ∉ sporadicsThm3 →
    Finite (TauCeti.CFSGIndex.sporadic s).Group → IsSimpleGroup (TauCeti.CFSGIndex.sporadic s).Group →
      3 ∣ Nat.card (TauCeti.CFSGIndex.sporadic s).Group ∧
        ∀ Y : Subgroup (TauCeti.CFSGIndex.sporadic s).Group, ¬ IsStronglyPEmbedded 3 Y

theorem isStronglyPEmbedded_map_mulEquiv {H H' : Type*} [Group H] [Group H'] {p : ℕ} (e : H ≃* H')
    {Y : Subgroup H} (hY : IsStronglyPEmbedded p Y) : IsStronglyPEmbedded p (Y.map e.toMonoidHom) := by
  obtain ⟨hne, hdvd, hint⟩ := hY
  refine ⟨fun htop => hne ?_, ?_, fun g' hg' => ?_⟩
  · have h1 : (Y.map e.toMonoidHom).comap e.toMonoidHom = Y :=
      Subgroup.comap_map_eq_self_of_injective e.injective Y
    rw [← h1, htop, Subgroup.comap_top]
  · rwa [Subgroup.card_map_of_injective e.injective]
  · set g : H := e.symm g' with hg
    have hgY : g ∉ Y := by
      intro hgY
      exact hg' ⟨g, hgY, by simp [hg]⟩
    have hconj : (Y.map e.toMonoidHom).map (MulAut.conj g').toMonoidHom =
        (Y.map (MulAut.conj g).toMonoidHom).map e.toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext x
      simp [hg, MulAut.conj_apply]
    have hinf : Y.map e.toMonoidHom ⊓ (Y.map e.toMonoidHom).map (MulAut.conj g').toMonoidHom =
        (Y ⊓ Y.map (MulAut.conj g).toMonoidHom).map e.toMonoidHom := by
      rw [hconj, Subgroup.map_inf_eq _ _ _ e.injective]
    rw [hinf, Subgroup.card_map_of_injective e.injective]
    exact hint g hgY

theorem exists_isStronglyPEmbedded_quotient_center {q : ℕ} [Fact q.Prime] {G : Type} [Group G] [Finite G]
    {N : Subgroup G} (hN : IsStronglyPEmbedded q N) {L : Subgroup G} [L.Normal] (hqL : q ∣ Nat.card L) :
    ∃ Y : Subgroup (↥L ⧸ Subgroup.center ↥L), IsStronglyPEmbedded q Y := by
  obtain ⟨R⟩ : Nonempty (Sylow q ↥L) := inferInstance
  have hR1 : (R : Subgroup ↥L) ≠ ⊥ := R.ne_bot_of_dvd_card hqL
  set R' : Subgroup G := (R : Subgroup ↥L).map L.subtype with hR'
  have hR'p : IsPGroup q R' := R.isPGroup'.map _
  have hR'1 : R' ≠ ⊥ := fun h0 => hR1 ((Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).1 h0)
  obtain ⟨P, hRP⟩ := hR'p.exists_le_sylow
  have hP : CFSG.RankThree.PartOne.IsSylowOf q (P : Subgroup G) ⊤ :=
    ⟨le_top, P.isPGroup', by
      rw [Subgroup.relIndex_top_right]
      exact P.not_dvd_index⟩
  obtain ⟨g, hg⟩ := hN.exists_conj_ge hP
  have hN' : IsStronglyPEmbedded q (conjSub g N) := hN.conj g
  have hR'N : R' ≤ conjSub g N := hRP.trans hg
  have hLN : ¬ L ≤ conjSub g N := fun hLN => hN'.not_dvd_card_of_normal_le hLN hqL
  have hdvd : q ∣ Nat.card (L ⊓ conjSub g N : Subgroup G) := by
    have hle : R' ≤ L ⊓ conjSub g N := le_inf (Subgroup.map_subtype_le _) hR'N
    refine Dvd.dvd.trans ?_ (Subgroup.card_dvd_of_le hle)
    rw [hR', Subgroup.card_map_of_injective L.subtype_injective]
    exact R.dvd_card_of_dvd_card hqL
  have hY₀ := hN'.subgroupOf hLN hdvd
  have hcen : Subgroup.center ↥L ≤ (L ⊓ conjSub g N).subgroupOf L := by
    intro z hz
    refine Subgroup.mem_subgroupOf.2 ⟨z.2, ?_⟩
    refine hN'.centralizer_le_of_isPGroup hR'1 hR'p hR'N (Subgroup.mem_centralizer_iff.2 fun r hr => ?_)
    obtain ⟨r₀, hr₀, rfl⟩ := hr
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz r₀)
  haveI : (Subgroup.center ↥L).Normal := inferInstance
  have hpZ : ¬ q ∣ Nat.card (Subgroup.center ↥L) := hY₀.not_dvd_card_of_normal_le hcen
  exact ⟨_, hY₀.map_quotient hcen hpZ⟩

theorem not_isStronglyPEmbedded_of_glbCore_eq_top {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (hΓ : ∀ T : Sylow p K, GLBCore p 1 (T : Subgroup K) = ⊤) (Y : Subgroup K) : ¬ IsStronglyPEmbedded p Y := by
  intro hY
  obtain ⟨P, hP, hPY⟩ := hY.exists_isSylowOf_le
  have hPi : ¬ p ∣ P.index := by simpa [Subgroup.relIndex_top_right] using hP.2.2
  refine hY.1 (eq_top_iff.2 ?_)
  rw [← hΓ (hP.2.1.toSylow hPi)]
  refine CFSG.HardMathSupport.Solomon.Proving.GLBCore_le_of_forall fun Q hQP hQ => ?_
  have hQP' : Q ≤ P := hQP
  obtain ⟨E, hEQ, -, hEc⟩ := CFSG.SectionRank.exists_pRank (Fact.out : p.Prime).one_lt Q
  have hpQ : p ∣ Nat.card Q := by
    refine Dvd.dvd.trans ?_ (Subgroup.card_dvd_of_le hEQ)
    rw [hEc]
    exact dvd_pow_self p (by omega)
  have hQ1 : Q ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hpQ
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1 hpQ)
  exact hY.normalizer_le hQ1 (hP.2.1.to_le hQP') (hQP'.trans hPY)

theorem dvd_card_of_glbCore_eq_top {K : Type} [Group K] [Finite K] [Nontrivial K] {p : ℕ} [Fact p.Prime]
    {T : Subgroup K} (hΓ : GLBCore p 1 T = ⊤) : p ∣ Nat.card K := by
  by_contra hp
  have hle : GLBCore p 1 T ≤ ⊥ := by
    refine CFSG.HardMathSupport.Solomon.Proving.GLBCore_le_of_forall fun Q _ hQ => ?_
    exfalso
    obtain ⟨E, -, -, hEc⟩ := CFSG.SectionRank.exists_pRank (Fact.out : p.Prime).one_lt Q
    refine hp (Dvd.dvd.trans ?_ (Subgroup.card_subgroup_dvd_card E))
    rw [hEc]
    exact dvd_pow_self p (by omega)
  rw [hΓ] at hle
  exact bot_ne_top (le_bot_iff.1 hle).symm

section SporSix


theorem k36SporSixNoStrongThree_holds : K36SporSixNoStrongThree := by
  intro s hs _ _
  have h11 : s ≠ .M11 := by
    rintro rfl
    exact hs (by decide)
  have hJ1 : s ≠ .J1 := by
    rintro rfl
    exact hs (by decide)
  have hΓ := CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.sporGammaOneAt_three s h11 hJ1
    (TauCeti.CFSGIndex.sporadic s).Group ⟨MulEquiv.refl _⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T⟩ : Nonempty (Sylow 3 (TauCeti.CFSGIndex.sporadic s).Group) := inferInstance
  exact ⟨dvd_card_of_glbCore_eq_top (hΓ T), not_isStronglyPEmbedded_of_glbCore_eq_top hΓ⟩

end SporSix

section Ge4



theorem k36EqlStarSporGe4_of_six
    (hR6 : K36SporSixNoStrongThree) : K36EqlStarSporGe4 := by
  intro G _ _ hG hq M p E h hS L hL hLc hne hX s hs hφ
  obtain ⟨φ⟩ := hφ
  haveI : L.Normal := hL
  exfalso
  have hfin : Finite (TauCeti.CFSGIndex.sporadic s).Group := Finite.of_equiv _ φ.toEquiv
  have hsimple : IsSimpleGroup (TauCeti.CFSGIndex.sporadic s).Group :=
    (φ.isSimpleGroup_congr).1 hLc.1.2.1
  obtain ⟨h3K, hno⟩ := hR6 s hs hfin hsimple
  have h3L : 3 ∣ Nat.card L := by
    have h1 : Nat.card (↥L ⧸ Subgroup.center ↥L) = Nat.card (TauCeti.CFSGIndex.sporadic s).Group :=
      Nat.card_congr φ.toEquiv
    exact (h1 ▸ h3K).trans (Subgroup.index_dvd_card (Subgroup.center ↥L))
  have h3G : 3 ∣ Nat.card G := h3L.trans (Subgroup.card_subgroup_dvd_card L)
  rcases k38_of_star hG hS with h1 | h2 | ⟨N, hN⟩
  · obtain ⟨q, hq, hq2, h4⟩ := hq
    exact absurd (h1 q hq hq2) (not_le.2 h4)
  · exact h2 h3G
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨Y, hY⟩ := exists_isStronglyPEmbedded_quotient_center hN h3L
    exact hno _ (isStronglyPEmbedded_map_mulEquiv φ hY)

theorem k36EqlStarSporGe4_holds :
    K36EqlStarSporGe4 :=
  k36EqlStarSporGe4_of_six k36SporSixNoStrongThree_holds

end Ge4

end CFSG.LocalAnalysis.UniquenessCase.UCK
