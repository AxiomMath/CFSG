module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R912A5
public import CFSG.Quasithin.Background.C1Basic
import CFSG.Quasithin.EmptyFaithful.SzF53A2
import CFSG.Quasithin.EmptyFaithful.S152He9W

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_map_eq_four {X : Type} [Group X] [Finite X] {V : Subgroup X}
    (φ : X →* alternatingGroup (Fin 5)) (hφ : Function.Surjective φ) (hker : φ.ker ≤ V)
    (hV : IsPGroup 2 V) (hodd : ¬ 2 ∣ V.index) : Nat.card (V.map φ) = 4 := by
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 (hV.map φ)
  have h60 := card_mul_index (V.map φ)
  rw [index_map_eq V hφ hker, ha, CFSG.Quasithin.SzF53A2.card_alternatingGroup] at h60
  rw [ha]
  have ha2 : a ≤ 2 := by
    by_contra h
    have h8 : 2 ^ 3 ∣ 60 := (pow_dvd_pow 2 (by omega)).trans (Dvd.intro _ h60)
    norm_num at h8
  interval_cases a <;> norm_num at h60 ⊢ <;> omega

theorem cgsIn_ne_of_isAlt {X Y S : Subgroup G} (hXY : X ≤ Y) (hYX : Y ≤ normalizer (X : Set G))
    (hidx : ∃ k : ℕ, (X.subgroupOf Y).index = 2 ^ k) (hSY : IsSylowOf 2 S Y)
    (hA5 : IsAlt (Bar2 X) 5)
    (hB : ∀ C : Subgroup G, C ≤ S → C ≠ ⊥ → (C.subgroupOf S).Characteristic →
      ¬ Y ≤ normalizer (C : Set G)) :
    CFSG.Quasithin.cgsIn Y S ≠ Y := by
  obtain ⟨e⟩ := hA5
  let φ : X →* alternatingGroup (Fin 5) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 X))
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hSX : IsSylowOf 2 (S ⊓ X) X := hSY.inf_of_le_normalizer hXY hYX
  have hO2 : pCoreOf 2 X ≤ S ⊓ X :=
    CFSG.Quasithin.pCoreOf_two_le_of_sylowIn inf_le_right hSX.isPGroup (isSylowOf_iff.1 hSX).2.2
  have hker : φ.ker ≤ S.subgroupOf X := fun x hx => by
    have hx' : e (QuotientGroup.mk' (CFSG.pCore 2 X) x) = 1 := hx
    have hx'' : ((x : X) : Bar2 X) = 1 := e.map_eq_one_iff.1 hx'
    exact mem_subgroupOf.2
      (mem_inf.1 (hO2 (mem_map_of_mem X.subtype ((QuotientGroup.eq_one_iff x).1 hx'')))).1
  have hVodd : ¬ 2 ∣ (S.subgroupOf X).index := by
    have := (isSylowOf_iff.1 hSX).2.2
    rwa [relIndex, inf_subgroupOf_right] at this
  have h4 := card_map_eq_four φ hφ hker hSY.isPGroup.comap_subtype hVodd
  have hstep : ∀ C : Subgroup G, C ≤ S → C ≠ ⊥ → (C.subgroupOf S).Characteristic →
      Y ⊓ normalizer (C : Set G) ≤ normalizer ((S ⊓ X : Subgroup G) : Set G) := by
    intro C hCS hC hchar
    have hSC : S ≤ normalizer (C : Set G) :=
      le_normalizer.trans (normalizer_le_normalizer_of_char hCS hchar)
    have hVK : S.subgroupOf X ≤ (Y ⊓ normalizer (C : Set G)).subgroupOf X := fun x hx =>
      mem_subgroupOf.2 (mem_inf.2 ⟨hSY.le (mem_subgroupOf.1 hx), hSC (mem_subgroupOf.1 hx)⟩)
    have hmap : ((Y ⊓ normalizer (C : Set G)).subgroupOf X).map φ ≠ ⊤ := by
      intro h
      refine hB C hCS hC hchar (le_of_le_of_isSylowOf (fun x hx => ?_) hSC hSY hidx)
      have h' := comap_map_eq φ ((Y ⊓ normalizer (C : Set G)).subgroupOf X)
      rw [h, comap_top, sup_eq_left.2 (hker.trans hVK)] at h'
      have hx' : (⟨x, hx⟩ : X) ∈ (Y ⊓ normalizer (C : Set G)).subgroupOf X := by
        rw [← h']
        exact mem_top _
      exact (mem_inf.1 (mem_subgroupOf.1 hx')).2
    have hKV : (Y ⊓ normalizer (C : Set G)).subgroupOf X ≤
        normalizer ((S.subgroupOf X : Subgroup X) : Set X) := by
      have h1 := (le_comap_map (f := φ) ((Y ⊓ normalizer (C : Set G)).subgroupOf X)).trans
        (comap_mono (CFSG.Quasithin.SzF53A2.le_normalizer_of_overgroup h4 (map_mono hVK) hmap))
      rwa [comap_normalizer_eq_of_surjective _ hφ, comap_map_eq, sup_eq_left.2 hker] at h1
    have hKXN : Y ⊓ normalizer (C : Set G) ⊓ X ≤ normalizer ((S ⊓ X : Subgroup G) : Set G) := by
      have h1 := (map_mono (f := X.subtype) hKV).trans (le_normalizer_map X.subtype)
      rwa [subgroupOf_map_subtype, subgroupOf_map_subtype] at h1
    have hSXK : S ⊓ X ≤ Y ⊓ normalizer (C : Set G) ⊓ X := inf_le_inf_right _ (le_inf hSY.le hSC)
    have hcore : pCoreOf 2 (Y ⊓ normalizer (C : Set G) ⊓ X) = S ⊓ X := le_antisymm
      (CFSG.Quasithin.pCoreOf_two_le_of_sylowIn hSXK hSX.isPGroup
        (isSylowOf_iff.1 (hSX.of_le hSXK inf_le_right)).2.2)
      (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hSXK hKXN hSX.isPGroup)
    have hKK : Y ⊓ normalizer (C : Set G) ≤
        normalizer ((Y ⊓ normalizer (C : Set G) ⊓ X : Subgroup G) : Set G) :=
      fun k hk => mem_normalizer_iff.2 fun h =>
        (mem_inf.trans (and_congr (mem_normalizer_iff.1 (le_normalizer hk) h)
          (mem_normalizer_iff.1 (hYX (mem_inf.1 hk).1) h))).trans mem_inf.symm
    rw [← hcore]
    exact hKK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  intro hcgs
  have hcgsle : CFSG.Quasithin.cgsIn Y S ≤ normalizer ((S ⊓ X : Subgroup G) : Set G) := by
    unfold CFSG.Quasithin.cgsIn
    exact iSup_le fun C => iSup_le fun hCS => iSup_le fun hC => iSup_le fun hchar =>
      hstep C hCS hC hchar
  have hn : (S.subgroupOf X).Normal :=
    normal_subgroupOf_iff_le_normalizer_inf.2 (hXY.trans (hcgs.symm.le.trans hcgsle))
  haveI : ((S.subgroupOf X).map φ).Normal := hn.map φ hφ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((S.subgroupOf X).map φ) with h | h <;>
    rw [h] at h4
  · rw [card_bot] at h4
    omega
  · rw [card_top, CFSG.Quasithin.SzF53A2.card_alternatingGroup] at h4
    omega

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
