module

public import CFSG.Quasithin.Background.RonanE42FStarA
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CentralCoreReduction
public import CFSG.Quasithin.Background.RonanE42Defs

public section

namespace CFSG.Quasithin.RonanE42

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem fStarPre_le {K Y T : Subgroup G} (hT2 : IsPGroup 2 T) (hTK : T ≤ K)
    (hF : CFSG.IsQuasisimple ↥(fStarMod K) ∨ ∃ p : ℕ, p.Prime ∧ Nat.card ↥(fStarMod K) = p)
    (hY : Y ≤ K) (hYn : ∀ h ∈ K, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y)
    (hYT : ¬ (Y ⊓ T ≤ pCoreOf 2 K)) :
    fStarPre K ≤ Y ⊔ pCoreOf 2 K := by
  have hO2 : CFSG.pCore 2 (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCore_quotient_eq_bot (G := ↥K) 2
  have hY'n : (Y.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff hY).mpr fun h k hh hk => hYn k hk h hh
  have hYbn : ((Y.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).Normal :=
    Subgroup.Normal.map hY'n _ (QuotientGroup.mk'_surjective _)
  obtain ⟨b, hbYT, hb⟩ := SetLike.not_le_iff_exists.mp hYT
  obtain ⟨hbY, hbT⟩ := Subgroup.mem_inf.mp hbYT
  have hbK : b ∈ K := hTK hbT
  have hy0Y : QuotientGroup.mk' (CFSG.pCore 2 ↥K) (⟨b, hbK⟩ : ↥K) ∈
      (Y.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hbY)
  have hy0ne : QuotientGroup.mk' (CFSG.pCore 2 ↥K) (⟨b, hbK⟩ : ↥K) ≠ 1 := by
    intro h1
    apply hb
    rw [QuotientGroup.mk'_apply] at h1
    have hx0N : (⟨b, hbK⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := (QuotientGroup.eq_one_iff _).mp h1
    exact Subgroup.mem_map.mpr ⟨⟨b, hbK⟩, hx0N, rfl⟩
  obtain ⟨k, hk⟩ := hT2 (⟨b, hbT⟩ : T)
  have hbk : b ^ 2 ^ k = 1 := by
    have := congr_arg Subtype.val hk
    simpa using this
  have hx0k : (⟨b, hbK⟩ : ↥K) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hbk)
  have hy0n : QuotientGroup.mk' (CFSG.pCore 2 ↥K) (⟨b, hbK⟩ : ↥K) ^ 2 ^ k = 1 := by
    rw [← map_pow, hx0k, map_one]
  have hsub : CFSG.generalizedFitting (↥K ⧸ CFSG.pCore 2 ↥K) ≤
      (Y.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) :=
    generalizedFitting_le_of_normal hO2 hF hy0Y hy0ne hy0n
  intro x hx
  unfold fStarPre at hx
  obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
  have hx'' : QuotientGroup.mk' (CFSG.pCore 2 ↥K) x' ∈
      CFSG.generalizedFitting (↥K ⧸ CFSG.pCore 2 ↥K) :=
    Subgroup.mem_comap.mp hx'
  obtain ⟨y', hy'Y, hy'eq⟩ := Subgroup.mem_map.mp (hsub hx'')
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hy'eq
  have hr : y'⁻¹ * x' ∈ CFSG.pCore 2 ↥K := QuotientGroup.eq.mp hy'eq
  have hy'K : (y' : G) ∈ Y := Subgroup.mem_subgroupOf.mp hy'Y
  have hrmem : K.subtype (y'⁻¹ * x') ∈ pCoreOf 2 K := Subgroup.mem_map.mpr ⟨y'⁻¹ * x', hr, rfl⟩
  have hx_eq : K.subtype x' = K.subtype y' * K.subtype (y'⁻¹ * x') := by
    rw [← map_mul, mul_inv_cancel_left]
  rw [hx_eq]
  exact Subgroup.mul_mem_sup hy'K hrmem

end CFSG.Quasithin.RonanE42
