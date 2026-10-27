module

public import CFSG.Quasithin.H13.GoldschmidtCTKAbs

public section

namespace CFSG.Quasithin.H13.CTK

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

section Img

variable {G : Type} [Group G]

abbrev projJ (J : Subgroup G) : ↥J →* ↥J ⧸ Subgroup.center ↥J := QuotientGroup.mk' _

@[expose] def imgJ (J X : Subgroup G) : Subgroup (↥J ⧸ Subgroup.center ↥J) :=
  (X.subgroupOf J).map (projJ J)

theorem mem_imgJ {J X : Subgroup G} {s : ↥J ⧸ Subgroup.center ↥J} :
    s ∈ imgJ J X ↔ ∃ x : ↥J, (x : G) ∈ X ∧ projJ J x = s := by
  simp [imgJ, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem imgJ_mono {J X Y : Subgroup G} (h : X ≤ Y) : imgJ J X ≤ imgJ J Y := by
  intro s hs
  obtain ⟨x, hx, rfl⟩ := mem_imgJ.1 hs
  exact mem_imgJ.2 ⟨x, h hx, rfl⟩

theorem imgJ_sup {J X Y : Subgroup G} (hX : X ≤ J) (hY : Y ≤ J) :
    imgJ J (X ⊔ Y) = imgJ J X ⊔ imgJ J Y := by
  unfold imgJ
  rw [Subgroup.subgroupOf_sup hX hY, Subgroup.map_sup]

theorem imgJ_inf {J X : Subgroup G} : imgJ J (X ⊓ J) = imgJ J X := by
  unfold imgJ
  rw [Subgroup.inf_subgroupOf_right]

theorem le_normalizer_of_conj {T H : Subgroup G} (h : ∀ t ∈ T, ∀ x ∈ H, t * x * t⁻¹ ∈ H) :
    T ≤ Subgroup.normalizer (H : Set G) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨fun hx => h t ht x hx, fun hx => by simpa [mul_assoc] using h t⁻¹ (T.inv_mem ht) _ hx⟩

end Img

section Setup

variable {G : Type} [Group G]

structure A5Setup (J D K V T₁ T₂ : Subgroup G) : Prop where
  card_D : Nat.card ↥D = 2
  D_le : D ≤ Subgroup.centralizer (J : Set G)
  pCore_JD : pCoreOf 2 (J ⊔ D) = D
  K_le : K ≤ J
  short : IsShort2 K
  alt : IsAltType K 5
  pCore_K : pCoreOf 2 K = V
  card_V : Nat.card ↥V = 16
  D_le_T₁ : D ≤ T₁
  T₁_le : T₁ ≤ J ⊔ D
  T₁_norm : T₁ ≤ Subgroup.normalizer (K : Set G)
  norm_V : (J ⊔ D) ⊓ Subgroup.normalizer ((V ⊔ D : Subgroup G) : Set G) = K ⊔ T₁
  sylow₁ : IsSylowTwoOf T₁ (K ⊔ T₁)
  sylow₂ : IsSylowTwoOf T₂ (J ⊔ D)
  T₁_le_T₂ : T₁ ≤ T₂
  relIndex_le : T₁.relIndex T₂ ≤ 2

variable [Finite G] {J D K V T₁ T₂ : Subgroup G}

namespace A5Setup

variable (h : A5Setup J D K V T₁ T₂)
include h

omit [Finite G] in
theorem V_le : V ≤ K := h.pCore_K ▸ CFSG.LieType.BorelTits.pCoreOf_le 2 K

theorem elemAbelian : IsElemAbelian 2 V :=
  isElemAbelian_V h.short h.alt h.pCore_K h.card_V

omit [Finite G] in
theorem comm_D {x : G} (hx : x ∈ J) {d : G} (hd : d ∈ D) : x * d = d * x :=
  Subgroup.mem_centralizer_iff.1 (h.D_le hd) x hx

theorem eq_one_of_mem_K {x : ↥J} (hxK : (x : G) ∈ K) (hx : x ∈ Subgroup.center ↥J) : x = 1 := by
  have hU := blockU_eq_of_alt5 h.short h.alt h.pCore_K h.card_V
  have hZ := AppC.blockZ_eq_bot_of_alt5 h.short h.alt
  have hcK : (x : G) ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have := Subgroup.mem_center_iff.1 hx ⟨k, h.K_le hk⟩
    exact congrArg Subtype.val this
  have hcV : (x : G) ∈ Subgroup.centralizer (pCoreOf 2 K : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.2
      (CFSG.LieType.BorelTits.pCoreOf_le 2 K)) hcK
  have hxV : (x : G) ∈ pCoreOf 2 K := h.short.2.1 ⟨hxK, hcV⟩
  have hxZ : (x : G) ∈ blockZ K := ⟨hU ▸ h.pCore_K ▸ hxV, hcK⟩
  rw [hZ, Subgroup.mem_bot] at hxZ
  exact Subtype.ext hxZ

omit [Finite G] in
theorem mem_D_of_central {z : ↥J} (hz : z ∈ Subgroup.center ↥J) (hz2 : z ^ 2 = 1) :
    (z : G) ∈ D := by
  set X := Subgroup.zpowers (z : G) with hX
  have hXJ : X ≤ J ⊔ D := (Subgroup.zpowers_le.2 z.2).trans le_sup_left
  have hXp : IsPGroup 2 X := by
    intro y
    refine ⟨1, ?_⟩
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 y.2
    apply Subtype.ext
    have h2 : (z : G) ^ 2 = 1 := congrArg Subtype.val hz2
    show (y : G) ^ 2 ^ 1 = 1
    rw [← hi, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    simp [h2]
  have hcomm : J ⊔ D ≤ Subgroup.centralizer {(z : G)} := by
    refine sup_le ?_ ?_
    · intro j hj
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨j, hj⟩)
    · intro d hd
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (h.comm_D z.2 hd).symm
  have hnorm : J ⊔ D ≤ Subgroup.normalizer (X : Set G) := by
    refine le_normalizer_of_conj fun t ht x hx => ?_
    have ht' := Subgroup.mem_centralizer_singleton_iff.1 (hcomm ht)
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have : t * (z : G) ^ i * t⁻¹ = (z : G) ^ i := by
      have hc : Commute t (z : G) := ht'
      rw [(hc.zpow_right i).eq]
      group
    rw [this]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
  have := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hXJ hnorm hXp
  rw [h.pCore_JD] at this
  exact this (Subgroup.mem_zpowers _)

omit [Finite G] in
theorem exists_mul_of_mem_sup {x : ↥J} (hx : (x : G) ∈ K ⊔ T₁) :
    ∃ k t : ↥J, (k : G) ∈ K ∧ (t : G) ∈ T₁ ∧ x = k * t := by
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left K T₁ h.T₁_norm
  have hx' : (x : G) ∈ (K : Set G) * (T₁ : Set G) := by
    rw [← hmul]
    exact hx
  obtain ⟨k, hk, t, ht, hkt⟩ := hx'
  have htJ : t ∈ J := by
    have : t = k⁻¹ * (x : G) := by rw [← hkt]; group
    rw [this]
    exact J.mul_mem (J.inv_mem (h.K_le hk)) x.2
  exact ⟨⟨k, h.K_le hk⟩, ⟨t, htJ⟩, hk, ht, Subtype.ext hkt.symm⟩

omit [Finite G] in
theorem V_le_normalizer_D : V ≤ Subgroup.normalizer (D : Set G) := fun _ hv =>
  Subgroup.centralizer_le_normalizer (D : Set G)
    (Subgroup.mem_centralizer_iff.2 fun _ hd => (h.comm_D (h.K_le (h.V_le hv)) hd).symm)

theorem conj_sup_of_img {x : ↥J}
    (hx : ∀ v : ↥J, (v : G) ∈ V → projJ J (x * v * x⁻¹) ∈ imgJ J V) :
    ∀ y ∈ V ⊔ D, (x : G) * y * (x : G)⁻¹ ∈ V ⊔ D := by
  have hel := h.elemAbelian
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right V D h.V_le_normalizer_D
  intro y hy
  have hy' : y ∈ (V : Set G) * (D : Set G) := by
    rw [← hmul]
    exact hy
  obtain ⟨v, hv, d, hd, rfl⟩ := hy'
  have hvJ : v ∈ J := h.K_le (h.V_le hv)
  have hxv : (x : G) * v * (x : G)⁻¹ ∈ V ⊔ D := by
    obtain ⟨v', hv', hvv'⟩ := mem_imgJ.1 (hx ⟨v, hvJ⟩ hv)
    set w : ↥J := x * ⟨v, hvJ⟩ * x⁻¹ with hw
    have hzc : v'⁻¹ * w ∈ Subgroup.center ↥J := by
      have h1 : projJ J (v'⁻¹ * w) = 1 := by rw [map_mul, map_inv, hvv', inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).1 h1
    have hv'2 : v' ^ 2 = 1 := Subtype.ext (hel.2 _ hv')
    have hw2 : w ^ 2 = 1 := by
      have hv2 : (⟨v, hvJ⟩ : ↥J) ^ 2 = 1 := Subtype.ext (hel.2 _ hv)
      rw [hw, conj_pow, hv2, mul_one, mul_inv_cancel]
    have hwz : w = v' * (v'⁻¹ * w) := by simp
    have hcomm : Commute v' (v'⁻¹ * w) := Subgroup.mem_center_iff.1 hzc v'
    have hz2 : (v'⁻¹ * w) ^ 2 = 1 := by
      have := hcomm.mul_pow 2
      rw [← hwz, hv'2, hw2, one_mul] at this
      exact this.symm
    have hzD := h.mem_D_of_central hzc hz2
    have : ((x : G) * v * (x : G)⁻¹) = (v' : G) * ((v'⁻¹ * w : ↥J) : G) :=
      congrArg Subtype.val hwz
    rw [this]
    exact Subgroup.mul_mem_sup hv' hzD
  have hxd : (x : G) * d * (x : G)⁻¹ = d := by
    rw [h.comm_D x.2 hd]
    group
  have : (x : G) * (v * d) * (x : G)⁻¹ = ((x : G) * v * (x : G)⁻¹) * ((x : G) * d * (x : G)⁻¹) := by
    group
  rw [this, hxd]
  exact (V ⊔ D).mul_mem hxv (Subgroup.mem_sup_right hd)

omit [Finite G] in
theorem conj_img_of_mem_normalizer {x : ↥J}
    (hx : (x : G) ∈ Subgroup.normalizer ((V ⊔ D : Subgroup G) : Set G)) :
    ∀ v : ↥J, (v : G) ∈ V → projJ J (x * v * x⁻¹) ∈ imgJ J V := by
  intro v hv
  have hw : (x : G) * v * (x : G)⁻¹ ∈ V ⊔ D :=
    (Subgroup.mem_normalizer_iff.1 hx (v : G)).1 (Subgroup.mem_sup_left hv)
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right V D h.V_le_normalizer_D
  have hw' : (x : G) * v * (x : G)⁻¹ ∈ (V : Set G) * (D : Set G) := by
    rw [← hmul]
    exact hw
  obtain ⟨v', hv', d, hd, hvd⟩ := hw'
  have hv'J : v' ∈ J := h.K_le (h.V_le hv')
  have hdJ : d ∈ J := by
    have : d = v'⁻¹ * ((x : G) * v * (x : G)⁻¹) := by rw [← hvd]; group
    rw [this]
    exact J.mul_mem (J.inv_mem hv'J) (J.mul_mem (J.mul_mem x.2 v.2) (J.inv_mem x.2))
  have hdc : (⟨d, hdJ⟩ : ↥J) ∈ Subgroup.center ↥J := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (h.comm_D g.2 hd)
  refine mem_imgJ.2 ⟨⟨v', hv'J⟩, hv', ?_⟩
  have hxe : x * v * x⁻¹ = ⟨v', hv'J⟩ * ⟨d, hdJ⟩ := Subtype.ext hvd.symm
  have h1 : projJ J ⟨d, hdJ⟩ = 1 := (QuotientGroup.eq_one_iff _).2 hdc
  rw [hxe, map_mul, h1, mul_one]

end A5Setup

end Setup

end CFSG.Quasithin.H13.CTK
