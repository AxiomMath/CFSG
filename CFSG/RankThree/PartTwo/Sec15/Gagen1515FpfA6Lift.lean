module

public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
import CFSG.RankThree.PartTwo.Sec15.LiebeckA6Normalizer

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf

open CFSG CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem le_of_isPerfect_le_normalizer {X₀ V F U T : Subgroup G}
    (hX₀ : Sec4.IsTripleCover ↥X₀ (alternatingGroup (Fin 6)))
    (hX₀V : X₀ ≤ Subgroup.normalizer (V : Set G)) (hX₀V1 : X₀ ⊓ V = ⊥)
    (hF : Group.IsPerfect ↥F) (hFX : F ≤ X₀ ⊔ V) (hU : IsPGroup 2 ↥U) (hUX : U ≤ X₀ ⊔ V)
    (hFU : F ≤ Subgroup.normalizer (U : Set G)) (hTX : T ≤ X₀) (hTU : T ≤ U) (hT : T ≠ ⊥) :
    F ≤ V := by
  let P : Subgroup G := X₀ ⊔ V
  have hFP : F ≤ P := hFX
  have hUP : U ≤ P := hUX
  have hVP : P ≤ Subgroup.normalizer (V : Set G) := by
    dsimp only [P]
    exact sup_le hX₀V Subgroup.le_normalizer
  letI : (V.subgroupOf X₀).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hX₀V
  letI : (V.subgroupOf P).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hVP
  have hVX₀ : V.subgroupOf X₀ = ⊥ :=
    Subgroup.subgroupOf_eq_bot.mpr (disjoint_iff.mpr (by rw [inf_comm]; exact hX₀V1))
  have e₁ := QuotientGroup.quotientInfEquivProdNormalizerQuotient X₀ V hX₀V
  have e₂ : ↥X₀ ⧸ V.subgroupOf X₀ ≃* ↥X₀ :=
    (QuotientGroup.quotientMulEquivOfEq hVX₀).trans QuotientGroup.quotientBot
  have e : ↥P ⧸ V.subgroupOf P ≃* ↥X₀ := e₁.symm.trans e₂
  have hX₀' : Sec4.IsTripleCover (↥P ⧸ V.subgroupOf P) (alternatingGroup (Fin 6)) := by
    obtain ⟨hcard, ⟨φ⟩⟩ := hX₀
    refine ⟨?_, ⟨(QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).trans φ⟩⟩
    have h := Subgroup.card_map_of_injective
      (f := (e : (↥P ⧸ V.subgroupOf P) →* ↥X₀))
      (K := Subgroup.center (↥P ⧸ V.subgroupOf P)) e.injective
    rw [Subgroup.map_center_eq e] at h
    rw [← h, hcard]
  let ρ : ↥P →* ↥P ⧸ V.subgroupOf P := QuotientGroup.mk' (V.subgroupOf P)
  have hF' : Group.IsPerfect ↥(F.subgroupOf P) := by
    haveI : Group.IsPerfect ↥F := hF
    exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hFP).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hFP).symm.surjective
  have hU' : IsPGroup 2 ↥(U.subgroupOf P) :=
    IsPGroup.of_equiv hU (Subgroup.subgroupOfEquivOfLe hUP).symm
  have hFU' : F.subgroupOf P ≤ Subgroup.normalizer (U.subgroupOf P : Set ↥P) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hUP]
    exact Subgroup.subgroupOf_mono P hFU
  have hFbar_perf : Group.IsPerfect ↥((F.subgroupOf P).map ρ) := by
    haveI : Group.IsPerfect ↥(F.subgroupOf P) := hF'
    exact Group.IsPerfect.map ρ
  have hUbar : IsPGroup 2 ↥((U.subgroupOf P).map ρ) := IsPGroup.map hU' ρ
  have hFUbar : (F.subgroupOf P).map ρ ≤
      Subgroup.normalizer ((U.subgroupOf P).map ρ : Set _) :=
    (Subgroup.map_mono hFU').trans (Subgroup.le_normalizer_map ρ)
  have hUbar1 : (U.subgroupOf P).map ρ ≠ ⊥ := by
    intro hbot
    have hUle : U.subgroupOf P ≤ V.subgroupOf P := by
      have h := (Subgroup.map_eq_bot_iff (U.subgroupOf P) (f := ρ)).mp hbot
      dsimp only [ρ] at h
      rwa [QuotientGroup.ker_mk'] at h
    refine hT (le_bot_iff.mp ?_)
    intro t ht
    have htP : t ∈ P := hUP (hTU ht)
    have hmem : (⟨t, htP⟩ : ↥P) ∈ U.subgroupOf P := hTU ht
    have hV : (⟨t, htP⟩ : ↥P) ∈ V.subgroupOf P := hUle hmem
    rw [Subgroup.mem_subgroupOf] at hV
    have hinf : t ∈ X₀ ⊓ V := ⟨hTX ht, hV⟩
    rw [hX₀V1] at hinf
    exact hinf
  have hFbar : (F.subgroupOf P).map ρ = ⊥ :=
    CFSG.RankThree.PartTwo.Sec15.LiebeckA6.eq_bot_of_isPerfect_le_normalizer_tripleA6
      hX₀' hFbar_perf hUbar hUbar1 hFUbar
  have hle : F.subgroupOf P ≤ ρ.ker := (Subgroup.map_eq_bot_iff (F.subgroupOf P) (f := ρ)).mp hFbar
  intro x hx
  have hxP : x ∈ P := hFP hx
  have hxF' : (⟨x, hxP⟩ : ↥P) ∈ F.subgroupOf P := hx
  have hxker : (⟨x, hxP⟩ : ↥P) ∈ ρ.ker := hle hxF'
  dsimp only [ρ] at hxker
  rw [QuotientGroup.ker_mk'] at hxker
  simpa only [Subgroup.mem_subgroupOf] using hxker

end CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf
