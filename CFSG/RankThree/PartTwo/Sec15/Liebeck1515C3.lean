module

public import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfCtx
public import CFSG.RankThree.PartTwo.Sec14.Ronan148QDefs
import CFSG.RankThree.PartTwo.Sec15.Liebeck1515D
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec15.Liebeck1515ShapeA6
import CFSG.RankThree.PartTwo.Sec15.Liebeck1515ShapeON
import CFSG.RankThree.PartTwo.Sec15.Liebeck1515Img
import CFSG.RankThree.PartTwo.Sec12.Hering129Setup
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck1515

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem not_case148Three
    (h134 : Item134) (h48 : Sec4.Item4_8)
    (h45 : Sec4.Item4_5) (h143 : Ronan148Q.Item143QS14) {A : Subgroup G} {c : G}
    {L : Subgroup G} {d : G} (h : Gagen1515Fpf.Ctx A c L d)
    (hΩB : ∀ F ∈ omegaA A, F ≤ Subgroup.closure {c, d}) {T T₀ : Subgroup G}
    (hTX : T ≤ Gagen1515Fpf.x₀ L d) (hT : T ≠ ⊥) (hTT₀ : T ≤ T₀) (hT₀ : IsPGroup 2 T₀)
    (hAT₀ : A ≤ Subgroup.normalizer (T₀ : Set G))
    (hY : Subgroup.normalizer (T₀ : Set G) ∈ scriptY A) :
    letI := ker148_normal hY.2
    ¬ Case148Three A (lB A) (Subgroup.normalizer (T₀ : Set G)) := by
  letI := ker148_normal hY.2
  rintro ⟨c', d', L', hc'Ω, hL', hJ', hd'A, hd'1, hd'c, hX, htypes⟩
  set Y₀ := Subgroup.normalizer (T₀ : Set G) with hY₀
  have htypes' : IsType1483 ↥(img148 A Y₀ (deltaZero A (lB A) Y₀)) := htypes
  have hCd : Subgroup.centralizer ({d'} : Set G) = Subgroup.centralizer ({d} : Set G) :=
    Sec12.centralizer_singleton_eq_of_zpowers_eq
      (zpowers_eq_of_point h134 h48 h hΩB hc'Ω hL' hJ' hd'A hd'1 hd'c)
  rw [hCd] at hX
  obtain ⟨𝒳, h𝒳, -, hx₀X, hΔ₀, hmeet, hperf, hshape⟩ := exists_xd h134 h48 h45 h143 h hΩB
  set C := Subgroup.centralizer ({d} : Set G) with hC
  set M := pPrimeCoreOf 3 C with hM
  set Xd := sSup 𝒳 with hXd
  set D := deltaZero A (lB A) (Y₀ ⊓ C) with hD
  set F' := inSubgroup perfectResidual D with hF'
  have hXdC : Xd ≤ C := sSup_le fun K hK => by
    obtain ⟨K', -, rfl⟩ := h𝒳 hK
    exact Subgroup.map_subtype_le K'
  have hXdM : Xd ≤ Subgroup.normalizer (M : Set G) :=
    hXdC.trans (le_normalizer_pPrimeCoreOf 3 C)
  have hDH : D ≤ Xd ⊔ M := (deltaZero_mono inf_le_right).trans (hΔ₀.trans (sup_comm _ _).le)
  have hF'D : F' ≤ D := Subgroup.map_subtype_le _
  have hF'H : F' ≤ Xd ⊔ M := hF'D.trans hDH
  have hDY : D ≤ Y₀ := (deltaZero_le _).trans inf_le_left
  have hF'Y : F' ≤ Y₀ := hF'D.trans hDY
  have hF'perf : Group.IsPerfect ↥F' :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.isPerfect_perfectResidual_map D
  set Xα := img148 A Y₀ (deltaZero A (lB A) Y₀) with hXα
  have hno := noNormal3_of_isType1483 htypes'
  have hXαD : Xα = img148 A Y₀ D :=
    img148_eq_of_noNormal3 ((deltaZero_le Y₀).trans le_sup_left) (deltaZero_mono inf_le_left) hX
      hno
  have hXαp : Group.IsPerfect ↥Xα :=
    isPerfect_of_isType1483 htypes' fun N _ h3 => eq_top_of_isPGroup_three N h3
  have hF'α : img148 A Y₀ F' = Xα := by
    rw [img148_inSubgroup_perfectResidual (hDY.trans le_sup_left) (hXαD ▸ hXαp), hXαD]
  have hF'YA : F' ≤ Y₀ ⊔ A := hF'Y.trans le_sup_left
  let φ₀ : ↥F' →* ↥(Y₀ ⊔ A) ⧸ ker148 A Y₀ :=
    (QuotientGroup.mk' (ker148 A Y₀)).comp (Subgroup.inclusion hF'YA)
  have hφ₀ : ∀ x : ↥F', φ₀ x ∈ Xα := fun x => by
    rw [← hF'α]
    exact ⟨Subgroup.inclusion hF'YA x, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
  let φ : ↥F' →* ↥Xα := φ₀.codRestrict Xα hφ₀
  have hφs : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    rw [← hF'α] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨⟨z, Subgroup.mem_subgroupOf.mp hz⟩, rfl⟩
  set H := Xd ⊔ M with hH
  obtain ⟨ρ, hρs, hρk⟩ := exists_hom_of_inf_eq_theta hXdM hmeet
  let ρF : ↥F' →* ↥Xd ⧸ aschbacherSolvableCore 3 ↥Xd := ρ.comp (Subgroup.inclusion hF'H)
  have hker : ρF.ker ≤ φ.ker := by
    have hle : ρF.ker.map F'.subtype ≤ M := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : Subgroup.inclusion hF'H x ∈ ρ.ker := hx
      rw [hρk, Subgroup.mem_subgroupOf] at hx'
      exact hx'
    have hn : (ρF.ker.map φ).Normal := Subgroup.Normal.map inferInstance φ hφs
    have h3 : ¬ 3 ∣ Nat.card (ρF.ker.map φ) := by
      intro h3
      have hdvd : Nat.card ρF.ker ∣ Nat.card M := by
        rw [← Subgroup.card_map_of_injective F'.subtype_injective]
        exact Subgroup.card_dvd_of_le hle
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 C)
        ((h3.trans (Subgroup.card_map_dvd _ _)).trans hdvd)
    exact (Subgroup.map_eq_bot_iff _).mp (hno _ hn h3)
  obtain ⟨g, hg⟩ :=
    CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523ON.exists_surj_of_ker_le ρF φ hker hφs
  set V : Subgroup (↥Xd ⧸ aschbacherSolvableCore 3 ↥Xd) := ((T₀ ⊓ H).subgroupOf H).map ρ with hV
  have hV2 : IsPGroup 2 V :=
    ((hT₀.to_le inf_le_left).comap_of_injective H.subtype Subtype.val_injective).map ρ
  have hV1 : V ≠ ⊥ := by
    obtain ⟨t, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hT
    have htH : (t : G) ∈ H := Subgroup.mem_sup_left (hx₀X (hTX t.2))
    intro hVb
    have hmem : ρ ⟨t, htH⟩ ∈ V :=
      ⟨⟨t, htH⟩, Subgroup.mem_subgroupOf.mpr ⟨hTT₀ t.2, htH⟩, rfl⟩
    rw [hVb, Subgroup.mem_bot] at hmem
    have htM : (t : G) ∈ M := by
      have h1 : (⟨t, htH⟩ : ↥H) ∈ ρ.ker := hmem
      rw [hρk, Subgroup.mem_subgroupOf] at h1
      exact h1
    have h2 : (t : G) ∈ Gagen1515Fpf.x₀ L d ⊓ M := ⟨hTX t.2, htM⟩
    rw [h.inf_pPrimeCoreOf_eq_bot, Subgroup.mem_bot] at h2
    exact ht1 (Subtype.ext h2)
  have hFV : ρF.range ≤ Subgroup.normalizer (V : Set _) := by
    rintro _ ⟨x, rfl⟩
    refine Subgroup.le_normalizer_map ρ ⟨Subgroup.inclusion hF'H x, ?_, rfl⟩
    have hxN : (x : G) ∈ Subgroup.normalizer ((T₀ ⊓ H : Subgroup G) : Set G) :=
      Late.le_normalizer_inf (Subgroup.zpowers_le.mpr (hF'Y x.2))
        (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer (hF'H x.2))) (Subgroup.mem_zpowers _)
    rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp hxN (y : G)
  have hcardX : Nat.card ↥Xα ≤ Nat.card ↥ρF.range := Nat.card_le_card_of_surjective g hg
  have h2520 := card_ge_of_isType1483 htypes'
  have hFperf : Group.IsPerfect ↥ρF.range := Group.IsPerfect.range ρF
  rcases hshape with hON | hA6 | hA6A6
  · have hQp : Group.IsPerfect (↥Xd ⧸ aschbacherSolvableCore 3 ↥Xd) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
    exact false_of_isTripleCover_ON hON hQp hV2 hV1 hFV g hg htypes'
  · have := card_le_of_isPerfect_le_normalizer (Or.inl hA6) hFperf hV2 hV1 hFV
    omega
  · have := card_le_of_isPerfect_le_normalizer (Or.inr hA6A6) hFperf hV2 hV1 hFV
    omega

end CFSG.RankThree.PartTwo.Sec15.Liebeck1515
