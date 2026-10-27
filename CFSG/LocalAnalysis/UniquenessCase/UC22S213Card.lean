module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.LocalAnalysis.UniquenessCase.UC6R869NS

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22s213_card_simple_dvd_card_range {P S Q : Type*} [Group P] [Group S] [Group Q]
    [Finite P] [IsSimpleGroup S] (φ : P →* S) (hφ : Function.Surjective φ) (f : P →* Q)
    {p : ℕ} (hpS : p ∣ Nat.card S) (hker : ¬ p ∣ Nat.card f.ker) :
    Nat.card S ∣ Nat.card f.range := by
  haveI : (f.ker.map φ).Normal := Subgroup.Normal.map inferInstance φ hφ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (f.ker.map φ) with h | h
  ·
    obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le ((Subgroup.map_eq_bot_iff _).mp h)
    have h1 := Subgroup.card_ker_mul_card_range f
    have h2 := Subgroup.card_ker_mul_card_range φ
    rw [MonoidHom.range_eq_top.mpr hφ, Subgroup.card_top, hc, ← h1, mul_assoc] at h2
    exact ⟨c, (Nat.eq_of_mul_eq_mul_left Nat.card_pos h2).symm.trans (Nat.mul_comm _ _)⟩
  ·
    refine absurd (hpS.trans ?_) hker
    rw [← Subgroup.card_top (G := S), ← h]
    exact Subgroup.card_map_dvd _ _

theorem uc22s213_card_barInf_dvd {L Y H : Subgroup G} (hq : CFSG.Open.IsQuasisimple (Bar2 L))
    (hYL : Y ≤ L) (hYH : Y ≤ H) (hY : Y ⊔ pCoreOf 2 L = L) (hLperf : ⁅L, L⁆ = L)
    (N : Subgroup ↥H) [N.Normal] {p : ℕ} (hpL : p ∣ Nat.card (BarInf L))
    (hN : ¬ p ∣ Nat.card N) :
    Nat.card (BarInf L) ∣
      Nat.card (CFSG.Quasithin.perfectCore ((Y.subgroupOf H).map (QuotientGroup.mk' N))) := by
  obtain ⟨e⟩ := uc22p21k_barInf_equiv hq
  haveI : IsSimpleGroup (Bar2 L ⧸ center (Bar2 L)) := hq.2
  have hsub : ∀ {K : Subgroup G}, Y ≤ K → (CFSG.Quasithin.perfectCore Y).subgroupOf K =
      CFSG.Quasithin.perfectCore (Y.subgroupOf K) := fun {K} hYK => by
    apply Subgroup.map_injective K.subtype_injective
    rw [CFSG.Quasithin.map_perfectCore, Subgroup.map_subgroupOf_eq_of_le hYK,
      Subgroup.map_subgroupOf_eq_of_le ((CFSG.Quasithin.perfectCore_le Y).trans hYK)]
  have hPY : CFSG.Quasithin.perfectCore Y ≤ Y := CFSG.Quasithin.perfectCore_le Y
  let f : ↥(CFSG.Quasithin.perfectCore Y) →* ↥H ⧸ N :=
    (QuotientGroup.mk' N).comp (Subgroup.inclusion (hPY.trans hYH))
  have hrange : f.range =
      CFSG.Quasithin.perfectCore ((Y.subgroupOf H).map (QuotientGroup.mk' N)) := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range, hsub hYH, CFSG.Quasithin.map_perfectCore]
  have hker : ¬ p ∣ Nat.card f.ker := by
    have hle : f.ker.map (Subgroup.inclusion (hPY.trans hYH)) ≤ N := by
      rintro _ ⟨x, hx, rfl⟩
      have h1 : QuotientGroup.mk' N (Subgroup.inclusion (hPY.trans hYH) x) = 1 := hx
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective (Subgroup.inclusion_injective _)] at h2
    exact fun h => hN (h.trans h2)
  let φ : ↥(CFSG.Quasithin.perfectCore Y) →* Bar2 L ⧸ center (Bar2 L) :=
    (QuotientGroup.mk' (center (Bar2 L))).comp
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion (hPY.trans hYL)))
  have hφ : Function.Surjective φ := by
    have h1 : ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp
        (Subgroup.inclusion (hPY.trans hYL))).range = ⊤ := by
      rw [MonoidHom.range_comp, Subgroup.inclusion_range, hsub hYL,
        CFSG.Quasithin.map_perfectCore, UC6.R869S.map_subgroupOf_eq_top hYL hY,
        CFSG.Quasithin.perfectCore_eq_self_of_perfect (UC6.R869S.bar2_perfect hLperf)]
    exact (QuotientGroup.mk'_surjective _).comp (MonoidHom.range_eq_top.mp h1)
  have hcard : Nat.card (BarInf L) = Nat.card (Bar2 L ⧸ center (Bar2 L)) :=
    Nat.card_congr e.toEquiv
  have h := uc22s213_card_simple_dvd_card_range φ hφ f (hcard ▸ hpL) hker
  rwa [hrange, ← hcard] at h

theorem uc22s213_normalizer_le_of_card_barInf (hG : IsSimpleGroup G) {p r : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {M L A : Subgroup G} (hLM : L ≤ M) (hLperf : ⁅L, L⁆ = L)
    (hq : CFSG.Open.IsQuasisimple (Bar2 L)) (h2 : 2 ≤ CFSG.Open.pRank p L)
    (hpL : p ∣ Nat.card (BarInf L)) (h3600 : 3600 < Nat.card (BarInf L)) (hr : r.Prime)
    (hAM : A ≤ M) (hAr : Nat.card A = r)
    (hY : (L ⊓ centralizer (A : Set G)) ⊔ pCoreOf 2 L = L)
    (hK : ∀ H : Subgroup G, H ≠ ⊤ → ¬ H ≤ M → 2 ≤ CFSG.Open.pRank p (H ⊓ M) →
      ∀ Y : Subgroup (↥H ⧸ CFSG.pPrimeCore p ↥H),
        Y ≤ ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)) →
        ⁅Y, Y⁆ = Y → Nat.card Y ≤ 3600) :
    normalizer (A : Set G) ≤ M := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hHM
  have hYL : L ⊓ centralizer (A : Set G) ≤ L := inf_le_left
  have hYH : L ⊓ centralizer (A : Set G) ≤ normalizer (A : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
  have hYM : L ⊓ centralizer (A : Set G) ≤ M := hYL.trans hLM
  have hrank : 2 ≤ CFSG.Open.pRank p (normalizer (A : Set G) ⊓ M) :=
    h2.trans ((UC6.R869S.pRank_le_of_sup_pCore hYL hY hp hp2).trans
      (CFSG.SectionRank.pRank_mono hp.one_lt (le_inf hYH hYM)))
  have htop : normalizer (A : Set G) ≠ ⊤ := fun htop => by
    haveI : A.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal A with hA | hA
    · rw [hA, Subgroup.card_bot] at hAr
      exact hr.one_lt.ne hAr
    · exact hHM (le_top.trans (hA ▸ hAM))
  have hdvd := uc22s213_card_barInf_dvd hq hYL hYH hY hLperf
    (CFSG.pPrimeCore p ↥(normalizer (A : Set G))) hpL
    ((Nat.Prime.coprime_iff_not_dvd hp).mp CFSG.pPrimeCore_coprime_card)
  have hle := hK _ htop hHM hrank
    (CFSG.Quasithin.perfectCore (((L ⊓ centralizer (A : Set G)).subgroupOf
      (normalizer (A : Set G))).map
        (QuotientGroup.mk' (CFSG.pPrimeCore p ↥(normalizer (A : Set G))))))
    ((CFSG.Quasithin.perfectCore_le _).trans
      (Subgroup.map_mono (Subgroup.comap_mono (le_inf hYH hYM))))
    (CFSG.Quasithin.perfectCore_perfect _)
  have := Nat.le_of_dvd Nat.card_pos hdvd
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
