module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36Induct
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36StarSub
import CFSG.LocalAnalysis.StronglyEmbedded.Normalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (Star36)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem centralizer_le_of_isComponent {q : ℕ} [Fact q.Prime] {H K : Subgroup G} (hH : IsStronglyPEmbedded q H)
    {P : Sylow q G} (hPH : (P : Subgroup G) ≤ H) (hK : CFSG.IsComponent K) (hqK : q ∣ Nat.card K) :
    centralizer (K : Set G) ≤ H := by
  obtain ⟨R, hR⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal P hK.2
  have hR1 : (R : Subgroup ↥K) ≠ ⊥ := R.ne_bot_of_dvd_card hqK
  have hPK : (P : Subgroup G) ⊓ K ≠ ⊥ := by
    rw [← hR]
    intro hb
    exact hR1 ((Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).1 hb)
  have hle : centralizer (K : Set G) ≤ centralizer ((P : Subgroup G) ⊓ K : Subgroup G) :=
    Subgroup.centralizer_le inf_le_right
  exact hle.trans (hH.centralizer_le_of_isPGroup hPK P.isPGroup'.to_inf_left (inf_le_left.trans hPH))

theorem eq_of_isComponent_of_isStronglyPEmbedded {q : ℕ} [Fact q.Prime] {H K₀ K₁ : Subgroup G}
    (hH : IsStronglyPEmbedded q H) {P : Sylow q G} (hPH : (P : Subgroup G) ≤ H) (h₀ : CFSG.IsComponent K₀)
    (h₁ : CFSG.IsComponent K₁) (hq₀ : q ∣ Nat.card K₀) (hq₁ : q ∣ Nat.card K₁) : K₀ = K₁ := by
  by_contra hne
  have hcomm : ⁅K₁, K₀⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute h₁ h₀).resolve_left (Ne.symm hne)
  have hle : K₁ ≤ centralizer (K₀ : Set G) := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  exact not_le_of_isComponent hH h₁ hq₁ (hle.trans (centralizer_le_of_isComponent hH hPH h₀ hq₀))

theorem not_dvd_card_of_le_centralizer {q : ℕ} [Fact q.Prime] {H K C : Subgroup G} [C.Normal]
    (hH : IsStronglyPEmbedded q H) {P : Sylow q G} (hPH : (P : Subgroup G) ≤ H) (hK : CFSG.IsComponent K)
    (hqK : q ∣ Nat.card K) (hC : C ≤ centralizer (K : Set G)) : ¬ q ∣ Nat.card C :=
  hH.not_dvd_card_of_normal_le (hC.trans (centralizer_le_of_isComponent hH hPH hK hqK))

namespace Hyp36

variable {M E : Subgroup G} {p : ℕ} (h : Hyp36 G M p E)
include h

theorem exists_stronglyThree (hp3 : p = 3) (hS : Star36 G) (h4 : 3 < twoLocalPrimeRank 3 G) :
    ∃ (P : Sylow 3 G) (H : Subgroup G), IsStronglyPEmbedded 3 H ∧ E ≤ P ∧ (P : Subgroup G) ≤ H ∧ M ≤ H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hEP, hPM⟩ := h.exists_sylow_three hp3
  have hP : CFSG.ABGLocalTools.IsSylowOf 3 (P : Subgroup G) ⊤ :=
    (CFSG.ABGLocalTools.isSylowOf_iff).2 ⟨le_top, P.isPGroup', by
      rw [Subgroup.relIndex_top_right]
      exact P.not_dvd_index⟩
  have hP1 : (P : Subgroup G) ≠ ⊥ :=
    P.ne_bot_of_dvd_card (dvd_card_of_three_lt_twoLocalPrimeRank Nat.prime_three h4)
  rcases hS 3 Nat.prime_three (by norm_num) h4 P hP with ha | ⟨hlt, -⟩
  · have hH : IsStronglyPEmbedded 3 (star36Sup 3 (P : Subgroup G)) := isStronglyPEmbedded_star36Sup hP hP1 ha
    have hE2 : 1 < CFSG.Open.pRank 3 E := by
      have := CFSG.SectionRank.le_pRank (p := 3) (by norm_num) (le_refl E) (hp3 ▸ h.elem) (k := 2)
        (by rw [h.card, hp3])
      omega
    have hMH : M ≤ star36Sup 3 (P : Subgroup G) :=
      le_star36Sup_of_mem_calMOf hEP hE2 (by rw [h.uniq]; rfl)
    exact ⟨P, _, hH, hEP, hPM.trans hMH, hMH⟩
  · exact absurd hlt (lt_irrefl 3)

theorem eq_singleton_of_stronglyThree (hp3 : p = 3) {P : Sylow 3 G} {H : Subgroup G}
    (hH : IsStronglyPEmbedded 3 H) (hPH : (P : Subgroup G) ≤ H) {K₀ : Subgroup G} (hK₀ : K₀ ∈ comps36 M) :
    comps36 M = {K₀} := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine Set.eq_singleton_iff_unique_mem.2 ⟨hK₀, fun K hK => ?_⟩
  exact (eq_of_isComponent_of_isStronglyPEmbedded hH hPH hK₀.1 hK.1 (hp3 ▸ h.dvd_card_component hK₀.1 hK₀.2)
    (hp3 ▸ h.dvd_card_component hK.1 hK.2)).symm

theorem normalizer_lam36_eq_top_of_stronglyThree (hp3 : p = 3) {H : Subgroup G} (hH : IsStronglyPEmbedded 3 H)
    (hMH : M ≤ H) : normalizer (lam36 M : Set G) = ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine h.normalizer_lam36_eq_top fun g K hK => ?_
  by_contra hEN
  have hK' : CFSG.IsComponent (K.map (MulAut.conj g).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hK.1
  have hpK' : p ∣ Nat.card (K.map (MulAut.conj g).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact h.dvd_card_component hK.1 hK.2
  exact not_le_of_isComponent hH hK' (hp3 ▸ hpK') ((h.le_of_component_of_not_normalizes hK' hpK' hEN).trans hMH)

theorem centralizer_lam36_le_of_stronglyThree (hp3 : p = 3) [(lam36 M).Normal] {P : Sylow 3 G} {H : Subgroup G}
    (hH : IsStronglyPEmbedded 3 H) (hPH : (P : Subgroup G) ≤ H) {K₀ : Subgroup G} (hK₀ : K₀ ∈ comps36 M) :
    centralizer (lam36 M : Set G) ≤ M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hCn : (centralizer (lam36 M : Set G)).Normal := Subgroup.normal_centralizer (H := lam36 M)
  have hC3 : ¬ 3 ∣ Nat.card (centralizer (lam36 M : Set G)) :=
    not_dvd_card_of_le_centralizer hH hPH hK₀.1 (hp3 ▸ h.dvd_card_component hK₀.1 hK₀.2)
      (Subgroup.centralizer_le (le_sSup hK₀))
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hle : centralizer (lam36 M : Set G) ≤ relPPrimeCore p (⊤ : Subgroup G) :=
    le_sSup ⟨le_top, hCn.subgroupOf ⊤, (Nat.Prime.coprime_iff_not_dvd h.prime).2 (hp3 ▸ hC3)⟩
  exact hle.trans h.pPrimeCore_le

theorem concl_of_forall_ne_top_three (O : Oracle36 M E p) (hS : Star36 G) (h4 : 3 < twoLocalPrimeRank 3 G)
    (hOF : L34OuterFree) (hall : ∀ K ∈ comps36 M, E ⊔ pCoreOf 2 M ⊔ K ≠ ⊤) : K36Concl M p := by
  obtain ⟨K₀, hK₀c, hK₀ne⟩ := h.exists_component
  have hK₀ : K₀ ∈ comps36 M := ⟨hK₀c, hK₀ne⟩
  obtain ⟨hp3, t, ht, hQt, hK₀shape⟩ := h.shapeComp_of_component O hK₀c hK₀ne (hall K₀ hK₀)
  have hshape : ∀ K ∈ comps36 M, ShapeComp t K := by
    intro K hK'
    obtain ⟨-, t', ht', hQt', hs⟩ := h.shapeComp_of_component O hK'.1 hK'.2 (hall K hK')
    have : t' = t := eq_of_zpowers_eq_of_orderOf_two ht' ht (hQt'.symm.trans hQt)
    exact this ▸ hs
  obtain ⟨P, H, hH, -, hPH, hMH⟩ := h.exists_stronglyThree hp3 hS h4
  have hs : comps36 M = {K₀} := h.eq_singleton_of_stronglyThree hp3 hH hPH hK₀
  have hΛn : normalizer (lam36 M : Set G) = ⊤ := h.normalizer_lam36_eq_top_of_stronglyThree hp3 hH hMH
  haveI hΛ : (lam36 M).Normal := Subgroup.normalizer_eq_top_iff.1 hΛn
  have hCM : centralizer (lam36 M : Set G) ≤ M := h.centralizer_lam36_le_of_stronglyThree hp3 hH hPH hK₀
  have hED : E ≤ lam36 M ⊔ centralizer (lam36 M : Set G) := fun e he' =>
    h.mem_lam36_sup_centralizer_of_singleton hp3 hOF ht hQt hshape hs he'
  exact h.concl_of_normal_lam36 hp3 ht hQt hK₀ hK₀shape hΛ hCM hED (Or.inl hs)

theorem frame_312_three (O : Oracle36 M E p) (hS : Star36 G) (h4 : 3 < twoLocalPrimeRank 3 G)
    (hOF : L34OuterFree) :
    K36Concl M p ∨ ∃ L : Subgroup G, L.Normal ∧ CFSG.IsComponent L ∧ ⁅L, pCoreOf 2 M⁆ ≠ ⊥ ∧
      E ⊔ pCoreOf 2 M ⊔ L = ⊤ :=
  h.frame_of_forall_ne_top (fun hall => h.concl_of_forall_ne_top_three O hS h4 hOF hall)

end Hyp36

end CFSG.LocalAnalysis.UniquenessCase.UCK
