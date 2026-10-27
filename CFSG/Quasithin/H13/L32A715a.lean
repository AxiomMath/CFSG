module

public import CFSG.Quasithin.H13.L32A520d
public import CFSG.Quasithin.EmptyFaithful.R3c5Gen

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

section Quot

variable {G : Type} [Group G]

theorem pCoreOf_eq_inf_pCoreOf [Finite G] {Y H : Subgroup G} (hYH : Y ≤ H)
    (hHY : H ≤ Subgroup.normalizer (Y : Set G)) : pCoreOf 2 Y = Y ⊓ pCoreOf 2 H := by
  apply le_antisymm
  · refine le_inf (pCoreOf_le 2 Y) ?_
    refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Y).trans hYH) ?_ (pCoreOf_isPGroup 2 Y)
    exact hHY.trans (normalizer_le_normalizer_pCoreOf 2 Y)
  · refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
      ((pCoreOf_isPGroup 2 H).to_le inf_le_right)
    intro g hg
    have hgH : g ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H (hYH hg)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxY, hxH⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hHY (hYH hg)) x).mp hxY,
        (Subgroup.mem_normalizer_iff.mp hgH x).mp hxH⟩
    · rintro ⟨hxY, hxH⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hHY (hYH hg)) x).mpr hxY,
        (Subgroup.mem_normalizer_iff.mp hgH x).mpr hxH⟩

@[expose] noncomputable def toStar (H K : Subgroup G) (hKH : K ≤ H) :
    ↥K →* ↥H ⧸ CFSG.pCore 2 ↥H :=
  (QuotientGroup.mk' (CFSG.pCore 2 ↥H)).comp (Subgroup.inclusion hKH)

theorem range_toStar {H K : Subgroup G} (hKH : K ≤ H) :
    (toStar H K hKH).range = modO2Image H K := by
  rw [toStar, MonoidHom.range_comp, Subgroup.inclusion_range]
  rfl

theorem mem_ker_toStar {H K : Subgroup G} (hKH : K ≤ H) {k : ↥K} :
    k ∈ (toStar H K hKH).ker ↔ (k : G) ∈ pCoreOf 2 H := by
  rw [MonoidHom.mem_ker, toStar, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, pCoreOf]
  constructor
  · intro h
    exact ⟨Subgroup.inclusion hKH k, h, rfl⟩
  · rintro ⟨x, hx, hxk⟩
    have : Subgroup.inclusion hKH k = x := Subtype.ext hxk.symm
    rw [this]
    exact hx

@[expose] noncomputable def quotEquivStar [Finite G] {H K : Subgroup G} (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) :
    (↥K ⧸ (pCoreOf 2 K).subgroupOf K) ≃* ↥(modO2Image H K) :=
  have hker : (pCoreOf 2 K).subgroupOf K = (toStar H K hKH).ker := by
    ext k
    rw [Subgroup.mem_subgroupOf, mem_ker_toStar, pCoreOf_eq_inf_pCoreOf hKH hHK]
    exact ⟨fun h => h.2, fun h => ⟨k.2, h⟩⟩
  (QuotientGroup.quotientMulEquivOfEq hker).trans
    ((QuotientGroup.quotientKerEquivRange (toStar H K hKH)).trans
      (MulEquiv.subgroupCongr (range_toStar hKH)))

theorem modO2Image_oTwoUpper [Finite G] (H : Subgroup G) :
    modO2Image H (oTwoUpper H) = oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  have h1 : (oTwoUpper H).subgroupOf H = oTwoUpper (⊤ : Subgroup ↥H) := by
    have e := R3c5.map_oTwoUpper_subgroupOf (G := G) (le_refl H)
    rw [Subgroup.subgroupOf_self] at e
    apply Subgroup.map_injective H.subtype_injective
    rw [e, Subgroup.map_subgroupOf_eq_of_le (oTwoUpper_le H)]
  rw [modO2Image, h1, ← oTwoUpper_map, Subgroup.map_top_of_surjective _
    (QuotientGroup.mk'_surjective _)]

end Quot

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

theorem isPOnePlusTwo_K
    (hK : IsPOnePlusTwo 3 ↥(oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)))) :
    IsPOnePlusTwo 3 (↥(oTwoUpper H) ⧸ (pCoreOf 2 (oTwoUpper H)).subgroupOf (oTwoUpper H)) := by
  refine isPOnePlusTwo_of_mulEquiv
    ((MulEquiv.subgroupCongr (modO2Image_oTwoUpper H)).symm.trans
      (quotEquivStar (oTwoUpper_le H) (le_normalizer_oTwoUpper H)).symm) hK

theorem pow_three_mem_K
    (hK : IsPOnePlusTwo 3 ↥(oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)))) :
    ∀ k ∈ oTwoUpper H, k ^ 3 ∈ pCoreOf 2 (oTwoUpper H) := by
  intro k hk
  have h := (isPOnePlusTwo_K hK).2.2 (QuotientGroup.mk ⟨k, hk⟩)
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h
  exact Subgroup.mem_subgroupOf.mp h

theorem lemma14_7_15_one (h331 : Stmt3_3_1) (hThm : Thm14_5_3) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (S : Setting147 G T L V H)
    (hK : IsPOnePlusTwo 3 ↥(oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)))) :
    l1 T L V ≤ oTwoUpper H ∧ l1 T L V = oTwoUpper (o2z (oTwoUpper H)) ∧
      l1 T L V = oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (L : Set G)) ∧
      (∀ W : Subgroup G, l1 T L V ⊔ pCoreOf 2 (oTwoUpper H) ≤ W → W ≤ oTwoUpper H →
        T ≤ Subgroup.normalizer (W : Set G) →
        W = l1 T L V ⊔ pCoreOf 2 (oTwoUpper H) ∨ W = oTwoUpper H) ∧
      H ≤ Subgroup.normalizer (l1 T L V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := oTwoUpper H with hKdef
  have hKH : K ≤ H := oTwoUpper_le H
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := le_normalizer_oTwoUpper H
  have hP := isPOnePlusTwo_K hK
  have hK3 := pow_three_mem_K hK
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  have hL1H : l1 T L V ≤ H := le_sup_left.trans S.hz.1.1
  have hQK : pCoreOf 2 K ≤ K := pCoreOf_le 2 K
  have hQZ : pCoreOf 2 K ≤ o2z K := fun q hq => mem_o2z_iff.mpr ⟨hQK hq, fun y hy => by
    have h1 : y * q⁻¹ * y⁻¹ ∈ pCoreOf 2 K :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 K hy) _).mp (inv_mem hq)
    rw [show q * y * q⁻¹ * y⁻¹ = q * (y * q⁻¹ * y⁻¹) by group]
    exact mul_mem hq h1⟩
  have hZ3 : ∀ z ∈ o2z K, z ^ 3 ∈ pCoreOf 2 K := fun z hz => hK3 z (o2z_le K hz)
  have hK03 : (pCoreOf 2 (oTwoUpper (o2z K))).relIndex (oTwoUpper (o2z K)) = 3 := by
    rw [relIndex_oTwoUpper_eq hQZ (o2z_le K) hZ3, relIndex_o2z hP]
  have hHK0 : H ≤ Subgroup.normalizer (oTwoUpper (o2z K) : Set G) :=
    (hHK.trans (normalizer_le_normalizer_o2z K)).trans (normalizer_le_normalizer_oTwoUpper _)
  have hK0H : oTwoUpper (o2z K) ≤ H := (oTwoUpper_le _).trans ((o2z_le K).trans hKH)
  have hK0M : oTwoUpper (o2z K) ≤ Subgroup.normalizer (L : Set G) :=
    le_M_of_index_three h331 hThm h1222 h1332 h1334 S hK0H (oTwoUpper_oTwoUpper _)
      (hTH.trans hHK0) hK03 (Subgroup.set_mul_normalizer_comm _ _ (hL1H.trans hHK0)).symm
  have hL1K : l1 T L V ≤ K := by
    rcases lemma14_5_20A h1222 h1332 h1334 S Nat.prime_three hKH hHK hK3 with h | ⟨-, h⟩
    · exfalso
      have hK0K : oTwoUpper (o2z K) ≤ K := (oTwoUpper_le _).trans (o2z_le K)
      have hle : oTwoUpper (o2z K) ≤ pCoreOf 2 K := h ▸ le_inf hK0K hK0M
      have h2 : IsPGroup 2 ↥(oTwoUpper (o2z K)) := (pCoreOf_isPGroup 2 K).to_le hle
      have hO : pCoreOf 2 (oTwoUpper (o2z K)) = oTwoUpper (o2z K) :=
        le_antisymm (pCoreOf_le 2 _)
          (le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer h2)
      rw [hO, Subgroup.relIndex_self] at hK03
      norm_num at hK03
    · exact h
  obtain ⟨h₁, h₂, h₃⟩ := lemma14_5_20_ii h331 hThm h1222 h1332 h1334 S hKH hHK hK3 hL1K hP
  refine ⟨hL1K, h₁, h₂, h₃, ?_⟩
  rw [h₁]
  exact hHK0

end CFSG.Quasithin.H13.L32A
