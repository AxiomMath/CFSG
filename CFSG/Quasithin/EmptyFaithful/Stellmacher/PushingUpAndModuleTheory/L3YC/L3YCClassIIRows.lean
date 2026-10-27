module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCClassII
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.L3YC.Survivors
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.SBd7

namespace Stellmacher.PU.L3YC

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def toModO2Image {H L : Subgroup G} (hLH : L ≤ H) :
    ↥L →* ↥(modO2Image H L) :=
  ((QuotientGroup.mk' (CFSG.pCore 2 ↥H)).comp (Subgroup.inclusion hLH)).codRestrict _ fun x =>
    ⟨Subgroup.inclusion hLH x, x.2, rfl⟩

omit [Finite G] in
theorem toModO2Image_surjective {H L : Subgroup G} (hLH : L ≤ H) :
    Function.Surjective (toModO2Image hLH) := by
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x.1, hx⟩, rfl⟩

omit [Finite G] in
theorem isPGroup_ker_toModO2Image {H L : Subgroup G} (hLH : L ≤ H) :
    IsPGroup 2 (toModO2Image hLH).ker := by
  intro x
  have hx : (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) (Subgroup.inclusion hLH (x : ↥L)) = 1 :=
    congrArg Subtype.val x.2
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
  obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (G := ↥H) (p := 2)) ⟨_, hx⟩
  refine ⟨m, Subtype.ext ?_⟩
  have h1 : (Subgroup.inclusion hLH (x : ↥L)) ^ (2 ^ m) = 1 := congrArg Subtype.val hm
  have h2 : Subgroup.inclusion hLH ((x : ↥L) ^ (2 ^ m)) = 1 := by rw [map_pow]; exact h1
  have h3 : ((x : ↥L) ^ (2 ^ m)) = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val h2
    simpa using this
  simpa using h3

theorem card_L32 {X : Type} [Group X] (h : IsPSL 3 2 1 X) : Nat.card X = 168 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two h

theorem card_pCore_modO2Image_le
    {H G₀ R L : Subgroup G} (hLH : L ≤ H) (hLG : L ≤ G₀)
    (hGL : G₀ ≤ Subgroup.normalizer (L : Set G)) (hq : IsLnTwoQuot L 3) (hperf : ⁅L, L⁆ = L)
    (h : MS93.IsC134Case4Corr G₀ R L) :
    Nat.card (CFSG.pCore 2 ↥(modO2Image H L)) ≤
        2 * Nat.card ↥(((c134Q G₀ L).subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) ∧
      ((c134Q G₀ L).subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ≤
        (CFSG.pCore 2 ↥(modO2Image H L)).map (modO2Image H L).subtype := by
  obtain ⟨h1, h2⟩ := card_pCore_le_two_mul_map_c134Q hLG hGL hq hperf h (toModO2Image hLH)
    (toModO2Image_surjective hLH) (isPGroup_ker_toModO2Image hLH)
  have hQL : c134Q G₀ L ≤ L := (MS93.commutator_le_pCoreOf hLG hGL).trans (pCoreOf_le 2 L)
  have heq : ((c134Q G₀ L).subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) =
      (((c134Q G₀ L).subgroupOf L).map (toModO2Image hLH)).map (modO2Image H L).subtype := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨toModO2Image hLH ⟨x.1, hQL hx⟩, ⟨⟨x.1, hQL hx⟩, hx, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨Subgroup.inclusion hLH x, hx, rfl⟩
  rw [heq, Subgroup.card_map_of_injective (modO2Image H L).subtype_injective]
  exact ⟨h1, Subgroup.map_mono h2⟩

theorem classII_row_false
    {H G₀ R L : Subgroup G} (hLH : L ≤ H) (hLG : L ≤ G₀)
    (hGL : G₀ ≤ Subgroup.normalizer (L : Set G)) (hq : IsLnTwoQuot L 3) (hperf : ⁅L, L⁆ = L)
    (h : MS93.IsC134Case4Corr G₀ R L)
    (hrow : IsExt ↥(modO2Image H L) (fun V _ => IsExtraspecial2 3 V)
      (fun Y' _ => IsPSL 3 2 1 Y')) : False := by
  classical
  have h3 : IsPSL 3 2 1 (ModO2 (modO2Image H L)) :=
    Stellmacher.CD.L3YC.isPSL_modO2_modO2Image hLH hq
  obtain ⟨V, hVn, ⟨hVe, hVc⟩, hVq⟩ := hrow
  have hVe' : CFSG.IsExtraspecial 2 ↥V := hVe
  have := hVe'
  have hVp : IsPGroup 2 V := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact CFSG.IsExtraspecial.isPGroup 2 V
  have hVle : V ≤ CFSG.pCore 2 ↥(modO2Image H L) := le_pCore_two' hVn hVp
  have hVcard : Nat.card V = 2 ^ 7 := by rw [hVc]
  have h1 : Nat.card ↥(modO2Image H L) = Nat.card (↥(modO2Image H L) ⧸ V) * Nat.card V :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup V
  have h2 : Nat.card ↥(modO2Image H L) = Nat.card (↥(modO2Image H L) ⧸ CFSG.pCore 2 ↥(modO2Image H L)) * Nat.card (CFSG.pCore 2 ↥(modO2Image H L)) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥(modO2Image H L))
  rw [card_L32 hVq, hVcard] at h1
  rw [card_L32 h3] at h2
  have hcard : Nat.card (CFSG.pCore 2 ↥(modO2Image H L)) = Nat.card V := by omega
  have hVeq : V = CFSG.pCore 2 ↥(modO2Image H L) := Subgroup.eq_of_le_of_card_ge hVle hcard.le
  refine classII_false hLG hGL hq hperf h (toModO2Image hLH) (toModO2Image_surjective hLH)
    (isPGroup_ker_toModO2Image hLH) ?_ ?_
  · rw [← hVeq]; exact hVe
  · rw [← hVeq]; exact hVcard

theorem classII_row_false_of_ctx
    {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hq : IsLnTwoQuot L 3)
    (hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G))
    (h4 : MS93.IsC134Case4Corr (L ⊔ Sgp153 T V₁) (Sgp153 T V₁) L) {H : Subgroup G} (hLH : L ≤ H)
    (hrow : IsExt ↥(modO2Image H L) (fun V _ => IsExtraspecial2 3 V)
      (fun Y' _ => IsPSL 3 2 1 Y')) : False := by
  have hLc : L ∈ cComp (thompsonJ I) := by
    obtain ⟨h, -⟩ := c.conc
    exact h
  exact classII_row_false hLH le_sup_left (Stellmacher.CD.L3YC.sup_le_normalizer hSL) hq
    (perfect_of_mem_cComp hLc) h4 hrow

end Stellmacher.PU.L3YC

end CFSG.Quasithin
