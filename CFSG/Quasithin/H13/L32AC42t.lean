module

public import CFSG.Quasithin.H13.L32AM50b

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped IsMulCommutative Pointwise

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

namespace TopW

variable {W : Subgroup G} (C : TopW T L V H W)
include C

theorem hTH : T ≤ H := Setting147.TH' C.S

variable [IsMulCommutative ↥(conjClosure V H)]

@[expose] noncomputable def autOf (X : Subgroup G) : Subgroup (MulAut (Hat V H W)) :=
  (X.subgroupOf H).map C.act

omit C in
theorem finite_mulAut : Finite (MulAut (Hat V H W)) :=
  Finite.of_injective (fun σ : MulAut (Hat V H W) => (σ : Hat V H W → Hat V H W))
    DFunLike.coe_injective

theorem autOf_le (X : Subgroup G) : C.autOf X ≤ C.act.range := Subgroup.map_le_range _ _

theorem hexp (v : Hat V H W) : v ^ 2 = 1 := by
  rw [pow_two]
  exact C.sec_sq v

variable {K : Subgroup G}

theorem range_le_normalizer_autOf (hKH : K ≤ H) (hKn : H ≤ Subgroup.normalizer (K : Set G)) :
    C.act.range ≤ Subgroup.normalizer (C.autOf K : Set (MulAut (Hat V H W))) := by
  rw [← map_subgroupOf_self_eq_range]
  exact map_le_normalizer_map_of_le_normalizer C.act hKH hKn

theorem isSylowTwoOf_autOf : IsSylowTwoOf (C.autOf T) C.act.range := by
  have : Finite (MulAut (Hat V H W)) := finite_mulAut
  have h := isSylowTwoOf_map_subgroupOf C.act
    (isSylowTwoOf_of_quasithinIsSylowTwo C.S.hyp.fsu.sylow C.hTH)
  rwa [map_subgroupOf_self_eq_range] at h

theorem isPGroup_autOf : IsPGroup 2 ↥(C.autOf T) :=
  ((C.S.hyp.fsu.sylow.1 : IsPGroup 2 ↥T).of_equiv
    (Subgroup.subgroupOfEquivOfLe C.hTH).symm).map C.act

theorem autOf_T_le_normalizer (hKH : K ≤ H) (hKn : H ≤ Subgroup.normalizer (K : Set G)) :
    C.autOf T ≤ Subgroup.normalizer (C.autOf K : Set (MulAut (Hat V H W))) :=
  (C.autOf_le T).trans (C.range_le_normalizer_autOf hKH hKn)

theorem autOf_perfect (hK : K ∈ cComp H) : ⁅C.autOf K, C.autOf K⁆ = C.autOf K := by
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hK' : ⁅K.subgroupOf H, K.subgroupOf H⁆ = K.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKH, perfect_of_mem_cComp hK]
  rw [autOf, ← Subgroup.map_commutator, hK']

theorem isQuasisimple_autOf (hK : K ∈ cComp H) (hq : CFSG.IsQuasisimple (cStar K))
    (hne : C.autOf K ≠ ⊥) : CFSG.IsQuasisimple ↥(C.autOf K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hO2K : pCoreOf 2 K ≤ pCoreOf 2 H :=
    A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK)
  let ψ : ↥K →* ↥(C.autOf K) := (C.act.comp (Subgroup.inclusion hKH)).codRestrict _
    (fun k => ⟨⟨(k : G), hKH k.2⟩, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩)
  have hker : (pCoreOf 2 K).subgroupOf K ≤ ψ.ker := by
    intro k hk
    rw [MonoidHom.mem_ker]
    exact Subtype.ext (C.act_eq_one_of_mem (h := ⟨k, hKH k.2⟩)
      (hO2K (Subgroup.mem_subgroupOf.mp hk)))
  let ψq : cStar K →* ↥(C.autOf K) := QuotientGroup.lift _ ψ hker
  have hsurj : Function.Surjective ψq := by
    intro y
    obtain ⟨x, hx, hxy⟩ := y.2
    exact ⟨QuotientGroup.mk ⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, Subtype.ext hxy⟩
  obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  obtain ⟨x, hxK, hx⟩ := y.2
  refine CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hq hsurj
    ⟨QuotientGroup.mk ⟨(x : G), Subgroup.mem_subgroupOf.mp hxK⟩, fun h => hy1 ?_⟩
  rw [← h]
  exact Subtype.ext hx.symm

theorem pCoreOf_autOf (hKH : K ≤ H) (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hO2 : pCoreOf 2 C.act.range = ⊥) : pCoreOf 2 (C.autOf K) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut (Hat V H W)) := finite_mulAut
  have hle : pCoreOf 2 (C.autOf K) ≤ pCoreOf 2 C.act.range :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans (C.autOf_le K))
      ((C.range_le_normalizer_autOf hKH hKn).trans (normalizer_le_normalizer_pCoreOf 2 _))
      (pCoreOf_isPGroup 2 _)
  rw [hO2] at hle
  exact le_bot_iff.mp hle

theorem commV_autOf_ne_bot (hne : C.autOf K ≠ ⊥) : commV (C.autOf K) ≠ ⊥ := by
  obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  obtain ⟨v, hv⟩ : ∃ v, (y : MulAut (Hat V H W)) v ≠ v := by
    by_contra hcon
    push Not at hcon
    exact hy1 (Subtype.ext (MulEquiv.ext hcon))
  intro h
  apply hv
  have h1 : (y : MulAut (Hat V H W)) v * v⁻¹ ∈ commV (C.autOf K) :=
    Subgroup.subset_closure ⟨_, y.2, v, rfl⟩
  rw [h, Subgroup.mem_bot, mul_inv_eq_one] at h1
  exact h1

theorem exists_irrPlusOn (hK : K ∈ cComp H) (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hne : C.autOf K ≠ ⊥) : ∃ Vs : Subgroup (Hat V H W),
      Vs ∈ IrrPlusOn (C.autOf K) (orbSup (C.autOf T) Vs) (C.autOf T) := by
  have hKH : K ≤ H := le_of_mem_cComp hK
  obtain ⟨I₀, hI₀⟩ := B1Red.exists_mem_irrPlus (C.autOf_perfect hK) (C.commV_autOf_ne_bot hne)
  obtain ⟨V₀, hV₀⟩ := irrPlusOn_nonempty C.hexp (C.autOf_T_le_normalizer hKH hKn)
    C.isPGroup_autOf hI₀
  refine ⟨V₀, ?_⟩
  rw [orbSup_eq_biSup_smul]
  have hc : ∀ X : Subgroup (MulAut (Hat V H W)),
      ActCompat (MonoidHom.id (Hat V H W)) X X :=
    fun X => ⟨fun b hb => ⟨b, hb, fun _ => rfl⟩, fun a ha => ⟨a, ha, fun _ => rfl⟩⟩
  refine ActCompat.mem_irrPlusOn_of_map (Wq := ⨆ y ∈ C.autOf T, y • I₀) (I := V₀)
    (fun _ _ h => h) (hc _) (hc _) (C.autOf_T_le_normalizer hKH hKn)
    (C.autOf_T_le_normalizer hKH hKn) (fun t ht w hw => smul_mem_biSup_smul ht hw) ?_
  rw [Subgroup.map_id]
  exact hV₀

theorem iSup_map_eq_top {Vs : Subgroup (Hat V H W)} (hVs : Vs ≠ ⊥) :
    (⨆ m ∈ C.act.range, Vs.map m.toMonoidHom) = ⊤ := by
  set J := ⨆ m ∈ C.act.range, Vs.map (m : MulAut (Hat V H W)).toMonoidHom with hJ
  have hH : ∀ h : ↥H, ∀ y ∈ J, C.act h y ∈ J := by
    intro h y hy
    have hle : J.map (C.act h).toMonoidHom ≤ J := by
      rw [hJ, Subgroup.map_iSup]
      refine iSup_le fun m => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hm => ?_
      rw [Subgroup.map_map]
      exact le_iSup₂_of_le (C.act h * m) (C.act.range.mul_mem ⟨h, rfl⟩ hm) le_rfl
    exact hle ⟨y, hy, rfl⟩
  rcases C.irr J hH with h0 | h1
  · exfalso
    apply hVs
    rw [eq_bot_iff, ← h0]
    exact fun v hv => Subgroup.mem_iSup_of_mem 1
      (Subgroup.mem_iSup_of_mem C.act.range.one_mem ⟨v, hv, rfl⟩)
  · exact h1

theorem d31 (hK : K ∈ cComp H) (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hq : CFSG.IsQuasisimple (cStar K)) (hne : C.autOf K ≠ ⊥)
    (hO2 : pCoreOf 2 C.act.range = ⊥) {Vs : Subgroup (Hat V H W)}
    (hVs : Vs ∈ IrrPlusOn (C.autOf K) (orbSup (C.autOf T) Vs) (C.autOf T)) :
    D31 C.act.range (C.autOf K) (C.autOf T) (C.autOf K) Vs := by
  have : Finite (MulAut (Hat V H W)) := finite_mulAut
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := C.hTH.trans hKn
  have hVs1 : Vs ∈ IrrPlus (C.autOf K) ⊤ := ⟨le_top, hVs.1.2⟩
  have hVs0 : Vs ≠ ⊥ := by
    obtain ⟨-, -, hlt, -⟩ := mem_irrPlus_top_iff.mp hVs1
    exact fun h => (lt_irrefl _ (lt_of_le_of_lt bot_le (h ▸ hlt))).elim
  refine ⟨C.hexp, ?_, C.isSylowTwoOf_autOf, ?_, C.isQuasisimple_autOf hK hq hne, ?_,
    C.range_le_normalizer_autOf hKH hKn, hVs1, ?_, C.iSup_map_eq_top hVs0⟩
  · exact isQuotientOfSQTK_range C.act (sqtkGroup_of_setting C.S)
  · have h := map_subgroupOf_mem_cComp C.act hK hne
    rwa [map_subgroupOf_self_eq_range] at h
  · have h := map_subgroupOf_conjClosure C.act hKH C.hTH
    rw [conjClosure_T_eq_self hTK] at h
    exact h
  · have hsyl : IsSylowTwoOf (C.autOf T) (C.autOf K ⊔ C.autOf T) :=
      F7.isSylowTwoOf_mono_right C.isSylowTwoOf_autOf le_sup_right
        (sup_le (C.autOf_le K) (C.autOf_le T))
    exact o2inv_of_irrPlusOn (C.autOf_T_le_normalizer hKH hKn) hsyl
      (C.pCoreOf_autOf hKH hKn hO2) hVs

theorem card_autOf {B : Subgroup G} (hBH : B ≤ H)
    (hf : ∀ b ∈ B, (∀ u ∈ conjClosure V H, b * u * b⁻¹ * u⁻¹ ∈ W) → b ∈ pCoreOf 2 H) :
    Nat.card (C.autOf B) = (B ⊓ pCoreOf 2 H).relIndex B := by
  have hE : C.autOf B = autSec (autOn B (conjClosure V H)) ⊤
      (W.subgroupOf (conjClosure V H)) := by
    ext ψ
    rw [A6.A6Mod.mem_autSec_iff (le_normalizer_conjClosure V H) C.hHUW hBH]
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact ⟨f, Subgroup.mem_subgroupOf.mp hf, rfl⟩
    · rintro ⟨f, hf, rfl⟩
      exact ⟨f, Subgroup.mem_subgroupOf.mpr hf, rfl⟩
  rw [hE]
  exact A6.A6Mod.card_autSec_eq (le_normalizer_conjClosure V H) C.hHUW hBH fun f hfB => by
    refine ⟨fun h => ?_, fun h => hf f hfB h⟩
    rw [← C.act_eq_one_iff_comm ⟨f, hBH hfB⟩]
    exact C.act_eq_one_of_mem h

theorem isA2_autOf {B : Subgroup G} (hB : QCrit (fsuV1 T V) V H B)
    (hf : ∀ b ∈ B, (∀ u ∈ conjClosure V H, b * u * b⁻¹ * u⁻¹ ∈ W) → b ∈ pCoreOf 2 H) :
    IsA2 C.act.range (C.autOf B) := by
  obtain ⟨hBH, hBe, hBQ, -, -⟩ := hB
  refine ⟨Subgroup.map_le_range _ _, ?_, ?_, ?_⟩
  · obtain ⟨b, hb, hbQ⟩ := Set.not_subset.mp hBQ
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    refine ⟨⟨C.act ⟨b, hBH hb⟩, ⟨b, hBH hb⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩, ?_⟩
    intro h1
    apply hbQ
    have h2 : C.act ⟨b, hBH hb⟩ = 1 := congrArg Subtype.val h1
    exact hf b hb ((C.act_eq_one_iff_comm _).mp h2)
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    have := hBe.1
    have h1 : (x : G) * y = y * x := congrArg Subtype.val
      (mul_comm (⟨x, Subgroup.mem_subgroupOf.mp hx⟩ : ↥B) ⟨y, Subgroup.mem_subgroupOf.mp hy⟩)
    exact Subtype.ext h1
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    have h2 : x ^ 2 = 1 := Subtype.ext (hBe.2 _ (Subgroup.mem_subgroupOf.mp hx))
    rw [h2, map_one]

theorem index_fixV_autOf_le {B : Subgroup G} (hB : QCrit (fsuV1 T V) V H B)
    (hf : ∀ b ∈ B, (∀ u ∈ conjClosure V H, b * u * b⁻¹ * u⁻¹ ∈ W) → b ∈ pCoreOf 2 H) :
    (fixV (C.autOf B)).index ≤ Nat.card (C.autOf B) ^ 2 := by
  obtain ⟨hBH, -, -, -, hidx⟩ := hB
  set U := conjClosure V H with hU
  set q := InternalSec.secMk (W.subgroupOf U) with hq
  set Z := (centralizerMod (fsuV1 T V) U B).subgroupOf U with hZ
  have hZf : Z.map q ≤ fixV (C.autOf B) := by
    rintro _ ⟨z, hz, rfl⟩ _ ⟨f, hf, rfl⟩
    have hz' : (z : G) ∈ centralizerMod (fsuV1 T V) U B := hz
    have hf' : (f : G) ∈ B := hf
    have hc := (mem_centralizerMod.mp hz').2.2 (f : G) hf'
    rw [C.act_secMk]
    have h1 : (f : G) * z * (f : G)⁻¹ * (z : G)⁻¹ ∈ W := by
      apply C.hV₁W
      have := inv_mem hc
      rwa [show ((z : G) * f * (z : G)⁻¹ * (f : G)⁻¹)⁻¹ = (f : G) * z * (f : G)⁻¹ * (z : G)⁻¹ by
        group] at this
    rw [← mul_inv_eq_one, ← map_inv, ← map_mul, A6.A6Mod.secMk_eq_one_iff]
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Setup.rho_apply_coe]
    exact h1
  have hpos : ∀ X : Subgroup (Hat V H W), 0 < X.index := fun X =>
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hposU : 0 < Z.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have h1 : (fixV (C.autOf B)).index ≤ (Z.map q).index :=
    Nat.le_of_dvd (hpos _) (Subgroup.index_dvd_of_le hZf)
  have h2 : (Z.map q).index ≤ Z.index :=
    Nat.le_of_dvd hposU (Subgroup.index_map_dvd _ (InternalSec.secMk_surjective _))
  calc (fixV (C.autOf B)).index ≤ Z.index := h1.trans h2
    _ = (centralizerMod (fsuV1 T V) U B).relIndex U := rfl
    _ ≤ ((B ⊓ pCoreOf 2 H).relIndex B) ^ 2 := hidx
    _ = Nat.card (C.autOf B) ^ 2 := by rw [C.card_autOf hBH hf]

theorem isQuadratic_autOf {B : Subgroup G} (hB : QCrit (fsuV1 T V) V H B) :
    IsQuadratic (C.autOf B) := by
  obtain ⟨hBH, -, -, hq, -⟩ := hB
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨_, ⟨b₁, hb₁, rfl⟩, v, rfl⟩ _ ⟨b₂, hb₂, rfl⟩
  obtain ⟨u, rfl⟩ := InternalSec.secMk_surjective (W.subgroupOf (conjClosure V H)) v
  have hb₁' : (b₁ : G) ∈ B := hb₁
  have hb₂' : (b₂ : G) ∈ B := hb₂
  rw [C.act_secMk, ← map_inv, ← map_mul, C.act_secMk, ← mul_inv_eq_one, ← map_inv, ← map_mul,
    A6.A6Mod.secMk_eq_one_iff]
  apply C.hV₁W
  have h := hq _ hb₁' _ hb₂' (u : G) u.2
  simpa [Setup.rho_apply_coe, mul_assoc] using h

theorem qOff {B : Subgroup G} (hB : QCrit (fsuV1 T V) V H B) (hBT : B ≤ T)
    (hf : ∀ b ∈ B, (∀ u ∈ conjClosure V H, b * u * b⁻¹ * u⁻¹ ∈ W) → b ∈ pCoreOf 2 H)
    (hMp : ∀ b : ↥H, (b : G) ∈ B → (∀ k : ↥H, (k : G) ∈ K → C.act b * C.act k =
      C.act k * C.act b) → (b : G) ∈ pCoreOf 2 H)
    {Vs : Subgroup (Hat V H W)} (hVT : C.autOf B ⊓ centSub (orbSup (C.autOf T) Vs) = ⊥) :
    QOff (C.autOf K) (C.autOf T) (C.autOf B) (orbSup (C.autOf T) Vs) := by
  have hA := C.isA2_autOf hB hf
  refine ⟨Subgroup.map_mono fun x hx => hBT hx, hA.2.1, hA.2.2,
    (isQuadratic_iff_commSeries_two _).mp (C.isQuadratic_autOf hB), ?_, ?_, hVT⟩
  · rw [rAV_le_two_iff C.hexp hA]
    have h1 := C.index_fixV_autOf_le hB hf
    have h2 := (fixV (C.autOf B)).card_mul_index
    calc Nat.card (Hat V H W) = Nat.card ↥(fixV (C.autOf B)) * (fixV (C.autOf B)).index := h2.symm
      _ ≤ Nat.card ↥(fixV (C.autOf B)) * Nat.card ↥(C.autOf B) ^ 2 := Nat.mul_le_mul_left _ h1
      _ = Nat.card ↥(C.autOf B) ^ 2 * Nat.card ↥(fixV (C.autOf B)) := mul_comm _ _
  · rintro _ ⟨b, hb, rfl⟩ hc
    exact C.act_eq_one_of_mem (hMp b hb fun k hk => hc _ ⟨k, Subgroup.mem_subgroupOf.mpr hk, rfl⟩)

theorem d310 (h310 : D310) (hK : K ∈ cComp H) (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hq : CFSG.IsQuasisimple (cStar K)) (hne : C.autOf K ≠ ⊥)
    (hO2 : pCoreOf 2 C.act.range = ⊥) {B : Subgroup G} (hB : QCrit (fsuV1 T V) V H B)
    (hBT : B ≤ T)
    (hf : ∀ b ∈ B, (∀ u ∈ conjClosure V H, b * u * b⁻¹ * u⁻¹ ∈ W) → b ∈ pCoreOf 2 H)
    (hMp : ∀ b : ↥H, (b : G) ∈ B → (∀ k : ↥H, (k : G) ∈ K → C.act b * C.act k =
      C.act k * C.act b) → (b : G) ∈ pCoreOf 2 H)
    (hVT : ∀ Vs : Subgroup (Hat V H W),
      Vs ∈ IrrPlusOn (C.autOf K) (orbSup (C.autOf T) Vs) (C.autOf T) →
      C.autOf B ⊓ centSub (orbSup (C.autOf T) Vs) = ⊥) :
    ∃ Vs : Subgroup (Hat V H W), Vs ∈ IrrPlusOn (C.autOf K) (orbSup (C.autOf T) Vs) (C.autOf T) ∧
      ((∀ t ∈ C.autOf T, t ∈ stabSub Vs) ∨ D310Two (C.autOf T) (C.autOf K) Vs) := by
  obtain ⟨Vs, hVs⟩ := C.exists_irrPlusOn hK hKn hne
  have hD := C.d31 hK hKn hq hne hO2 hVs
  have hA := C.qOff hB hBT hf hMp (hVT Vs hVs)
  have hD3 : D3Std C.act.range (C.autOf K) (C.autOf T) (C.autOf K) Vs :=
    ⟨hD, hA.qhat_VT C.hexp, hVs⟩
  exact ⟨Vs, hVs, h310 _ _ _ _ _ _ hD3 rfl (hA.qhat_M (C.autOf_le T))⟩

end TopW

end CFSG.Quasithin.H13.L32A.C
