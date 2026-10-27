module

public import CFSG.Quasithin.EmptyFaithful.S153Y
public import CFSG.Quasithin.EmptyFaithful.S153YAbs
public import CFSG.Quasithin.EmptyFaithful.S14118RestStar
public import CFSG.Quasithin.Background.A3Structure36BCaseAux

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

section Star

variable {G : Type} [Group G]

theorem imageOTwoQuot_conj_mem {M X Y : Subgroup G} (hXM : X ≤ M)
    (h : X ≤ Subgroup.normalizer (Y : Set G)) {x : G} (hx : x ∈ X) {v : OTwoQuot M}
    (hv : v ∈ imageOTwoQuot M Y) :
    (QuotientGroup.mk ⟨x, hXM hx⟩ : OTwoQuot M) * v * (QuotientGroup.mk ⟨x, hXM hx⟩)⁻¹ ∈
      imageOTwoQuot M Y := by
  obtain ⟨y, hyM, hyY, rfl⟩ := mem_imageOTwoQuot_iff.mp hv
  have hxy : x * y * x⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (h hx) y).mp hyY
  refine mem_imageOTwoQuot_iff.mpr ⟨x * y * x⁻¹,
    M.mul_mem (M.mul_mem (hXM hx) hyM) (M.inv_mem (hXM hx)), hxy, ?_⟩
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  rfl

theorem imageOTwoQuot_le_normalizer {M X Y : Subgroup G} (hXM : X ≤ M)
    (h : X ≤ Subgroup.normalizer (Y : Set G)) :
    imageOTwoQuot M X ≤ Subgroup.normalizer (imageOTwoQuot M Y : Set (OTwoQuot M)) := by
  intro u hu
  obtain ⟨x, hxM, hxX, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
  rw [Subgroup.mem_normalizer_iff]
  intro v
  refine ⟨fun hv => imageOTwoQuot_conj_mem hXM h hxX hv, fun hv => ?_⟩
  have h1 := imageOTwoQuot_conj_mem hXM h (X.inv_mem hxX) hv
  have e : (QuotientGroup.mk ⟨x⁻¹, hXM (X.inv_mem hxX)⟩ : OTwoQuot M) *
      ((QuotientGroup.mk ⟨x, hxM⟩ : OTwoQuot M) * v * (QuotientGroup.mk ⟨x, hxM⟩)⁻¹) *
        (QuotientGroup.mk ⟨x⁻¹, hXM (X.inv_mem hxX)⟩)⁻¹ = v := by
    have e1 : (QuotientGroup.mk ⟨x⁻¹, hXM (X.inv_mem hxX)⟩ : OTwoQuot M) =
        (QuotientGroup.mk ⟨x, hxM⟩)⁻¹ := QuotientGroup.mk_inv (CFSG.Open.pCore 2 ↥M) (⟨x, hxM⟩ : ↥M)
    rw [e1]
    group
  rwa [e] at h1

theorem isPGroup_imageOTwoQuot {M X : Subgroup G} (hX : IsPGroup 2 X) :
    IsPGroup 2 ↥(imageOTwoQuot M X) := by
  intro u
  obtain ⟨x, hxM, hxX, hu⟩ := mem_imageOTwoQuot_iff.mp u.2
  obtain ⟨k, hk⟩ := hX ⟨x, hxX⟩
  refine ⟨k, Subtype.ext ?_⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : (QuotientGroup.mk (⟨x, hxM⟩ : ↥M) : OTwoQuot M) ^ 2 ^ k = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : (⟨x, hxM⟩ : ↥M) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
    rw [this, QuotientGroup.mk_one]
  show (u : OTwoQuot M) ^ 2 ^ k = 1
  rw [← hu]
  exact h1

end Star

theorem imageOTwoQuot_self' {G : Type} [Group G] (M : Subgroup G) : imageOTwoQuot M M = ⊤ := by
  unfold imageOTwoQuot
  rw [Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

@[expose] def O2Z {G : Type} [Group G] (Y : Subgroup G) : Subgroup G :=
  ((Subgroup.center (OTwoQuot Y)).comap (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥Y))).map
    Y.subtype

theorem mem_O2Z_iff {G : Type} [Group G] {Y : Subgroup G} {y : G} :
    y ∈ O2Z Y ↔ ∃ hy : y ∈ Y, (QuotientGroup.mk ⟨y, hy⟩ : OTwoQuot Y) ∈
      Subgroup.center (OTwoQuot Y) := by
  unfold O2Z
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hy, hc⟩
    exact ⟨⟨y, hy⟩, hc, rfl⟩

section Iso

variable {G : Type} [Group G] [Finite G]

theorem exists_mulEquiv_imageOTwoQuot {M Y : Subgroup G} (hYM : Y ≤ M)
    (hMY : M ≤ Subgroup.normalizer (Y : Set G)) :
    ∃ φ : OTwoQuot Y ≃* ↥(imageOTwoQuot M Y), ∀ y : ↥Y,
      ((φ (QuotientGroup.mk y) : ↥(imageOTwoQuot M Y)) : OTwoQuot M) =
        QuotientGroup.mk (⟨(y : G), hYM y.2⟩ : ↥M) := by
  classical
  have hnormY : (CFSG.Open.pCore 2 ↥Y).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  let f₀ : ↥Y →* OTwoQuot M :=
    (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥M)).comp (Subgroup.inclusion hYM)
  have hf₀mem : ∀ y : ↥Y, f₀ y ∈ imageOTwoQuot M Y := fun y =>
    mem_imageOTwoQuot_iff.mpr ⟨(y : G), hYM y.2, y.2, rfl⟩
  let f : ↥Y →* ↥(imageOTwoQuot M Y) := f₀.codRestrict (imageOTwoQuot M Y) hf₀mem
  have hfsurj : Function.Surjective f := by
    rintro ⟨u, hu⟩
    obtain ⟨x, hxM, hxY, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
    exact ⟨⟨x, hxY⟩, rfl⟩
  have hker : f.ker = CFSG.Open.pCore 2 ↥Y := by
    ext y
    have h1 : y ∈ f.ker ↔ (y : G) ∈ pCoreOf 2 M := by
      rw [MonoidHom.mem_ker, Subtype.ext_iff]
      exact mk_eq_one_iff_mem_pCoreOf (⟨(y : G), hYM y.2⟩ : ↥M)
    have h2 : y ∈ CFSG.Open.pCore 2 ↥Y ↔ (y : G) ∈ pCoreOf 2 Y :=
      (Subgroup.mem_map_iff_mem Y.subtype_injective).symm
    rw [h1, h2]
    constructor
    · intro hy
      have hYN : Y ≤ Subgroup.normalizer ((Y ⊓ pCoreOf 2 M : Subgroup G) : Set G) := fun g hg =>
        Subgroup.inf_normalizer_le_normalizer_inf
          ⟨hMY (hYM hg), le_normalizer_pCoreOf 2 M (hYM hg)⟩
      exact le_pCoreOf_of_le_normalizer 2 (inf_le_left : Y ⊓ pCoreOf 2 M ≤ Y) hYN
        ((pCoreOf_isPGroup 2 M).to_le inf_le_right) ⟨y.2, hy⟩
    · intro hy
      exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Y).trans hYM)
        (fun m hm => normalizer_le_normalizer_pCoreOf 2 Y (hMY hm)) (pCoreOf_isPGroup 2 Y) hy
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hfsurj), fun y => ?_⟩
  rfl

end Iso

namespace Hyp153

variable {G : Type} [Group G] [Finite G] {T Mc M : Subgroup G}

theorem Ystar_structure (h113 : StageLemma14113) (h : Hyp153 G T Mc M) :
    (ClassLeTwo (⊤ : Subgroup ↥(imageOTwoQuot M (Y153 Mc M))) ∧
      Subgroup.closure {x : ↥(imageOTwoQuot M (Y153 Mc M)) | x ^ 3 = 1} = ⊤ ∧
      ∀ x : ↥(imageOTwoQuot M (Y153 Mc M)), x ^ 3 = 1) ∧
    ∀ y ∈ imageOTwoQuot M (Y153 Mc M),
      starAct M (VZ T M) h.le_normalizer h.hyp14117.pCoreOf_le_centralizer y = 1 →
        ∀ y' ∈ imageOTwoQuot M (Y153 Mc M), y' * y = y * y' := by
  obtain ⟨q, L₁, L₂, t, -, -, -, -, hS, -⟩ := h.exists_ofourStruct
  have hMV : M ≤ Subgroup.normalizer (VZ T M : Set G) := h.le_normalizer
  have hOC : pCoreOf 2 M ≤ Subgroup.centralizer (VZ T M : Set G) :=
    h.hyp14117.pCoreOf_le_centralizer
  have hRcM : pCoreOf 2 (Mc ⊓ M) ≤ M := (pCoreOf_le 2 _).trans inf_le_right
  have hYM : Y153 Mc M ≤ M := Y153_le Mc M
  have hconj : conjClosure (pCoreOf 2 (Mc ⊓ M)) M ≤ M :=
    conjClosure_le fun g hg z hz => M.mul_mem (M.mul_mem hg (hRcM hz)) (M.inv_mem hg)
  have hYq : imageOTwoQuot M (Y153 Mc M) =
      oTwoUpper (conjClosure (imageOTwoQuot M (pCoreOf 2 (Mc ⊓ M))) ⊤) := by
    show imageOTwoQuot M (oTwoUpper (conjClosure (pCoreOf 2 (Mc ⊓ M)) M)) = _
    rw [imageOTwoQuot_oTwoUpper hconj, imageOTwoQuot_conjClosure hRcM]
  have h3 := lemma_14_1_17_three h.qtfe h.hyp14117 (Y₀ := M) le_rfl
  rw [sup_eq_left.mpr h.T_le] at h3
  obtain ⟨h3a, h3b⟩ := h3
  change ⁅imageOTwoQuot M (M ⊓ Subgroup.centralizer (VZ T M : Set G)),
    imageOTwoQuot M (Y153 Mc M) ⊔ imageOTwoQuot M (pCoreOf 2 (Mc ⊓ M))⁆ = ⊥ at h3a
  change ∀ u ∈ imageOTwoQuot M (Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G)),
    u ∈ imageOTwoQuot M ((M ⊓ Subgroup.centralizer (VZ T M : Set G)) ⊔ pCoreOf 2 (Mc ⊓ M)) ∧
      Odd (orderOf u) ∧ ∀ w ∈ imageOTwoQuot M ((M ⊓ Subgroup.centralizer (VZ T M : Set G)) ⊔
        pCoreOf 2 (Mc ⊓ M)), w * u = u * w at h3b
  rw [Subgroup.commutator_comm] at h3a
  have hcent := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3a
  have hker : (starAct M (VZ T M) hMV hOC).ker =
      imageOTwoQuot M (M ⊓ Subgroup.centralizer (VZ T M : Set G)) := ker_starAct hMV hOC
  have hmapY : (imageOTwoQuot M (Y153 Mc M)).map (starAct M (VZ T M) hMV hOC) =
      oTwoUpper (autOn M (VZ T M)) := by
    rw [map_starAct hMV hOC hYM]
    exact h.autOn_Y153 h113
  have hPmem : ∀ u ∈ imageOTwoQuot M (Y153 Mc M),
      starAct M (VZ T M) hMV hOC u ∈ oTwoUpper (autOn M (VZ T M)) := fun u hu =>
    hmapY ▸ Subgroup.mem_map_of_mem _ hu
  obtain ⟨r, -, -, hrR, hrinv⟩ := h.exists_central_mem_autOn_Rc h113
  have hrR' : r ∈ (imageOTwoQuot M (pCoreOf 2 (Mc ⊓ M))).map (starAct M (VZ T M) hMV hOC) := by
    rw [map_starAct hMV hOC hRcM]
    exact hrR
  obtain ⟨ρ₀, hρ₀, hρ₀r⟩ := Subgroup.mem_map.mp hrR'
  have hRY : imageOTwoQuot M (pCoreOf 2 (Mc ⊓ M)) ≤
      Subgroup.normalizer (imageOTwoQuot M (Y153 Mc M) : Set (OTwoQuot M)) :=
    imageOTwoQuot_le_normalizer hRcM fun r hr => le_normalizer_Y153 Mc M (hRcM hr)
  have hZodd : ∀ y ∈ imageOTwoQuot M (Y153 Mc M), starAct M (VZ T M) hMV hOC y = 1 →
      Odd (orderOf y) := by
    intro u hu hρu
    obtain ⟨y, hyM, hyY, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
    exact (h3b _ (mem_imageOTwoQuot_iff.mpr ⟨y, hyM,
      ⟨hyY, (A4.actionOn_eq_one_iff hMV ⟨y, hyM⟩).mp hρu⟩, rfl⟩)).2.1
  have hZc : ∀ y ∈ imageOTwoQuot M (Y153 Mc M), starAct M (VZ T M) hMV hOC y = 1 →
      ∀ y' ∈ imageOTwoQuot M (Y153 Mc M), y' * y = y * y' := by
    intro y hy hρy y' hy'
    have hyC : y ∈ imageOTwoQuot M (M ⊓ Subgroup.centralizer (VZ T M : Set G)) := hker ▸ hρy
    exact (Subgroup.mem_centralizer_iff.mp (hcent (Subgroup.mem_sup_left hy')) y hyC).symm
  have hZR : ∀ y ∈ imageOTwoQuot M (Y153 Mc M), starAct M (VZ T M) hMV hOC y = 1 →
      ∀ ρ ∈ imageOTwoQuot M (pCoreOf 2 (Mc ⊓ M)), ρ * y = y * ρ := by
    intro y hy hρy ρ hρ
    have hyC : y ∈ imageOTwoQuot M (M ⊓ Subgroup.centralizer (VZ T M : Set G)) := hker ▸ hρy
    exact (Subgroup.mem_centralizer_iff.mp (hcent (Subgroup.mem_sup_right hρ)) y hyC).symm
  have hP3 : ∀ y ∈ imageOTwoQuot M (Y153 Mc M), starAct M (VZ T M) hMV hOC y ^ 3 = 1 :=
    fun y hy => hS.pow_three_of_mem_oTwoUpper (hPmem y hy)
  have hPab : ∀ y ∈ imageOTwoQuot M (Y153 Mc M), ∀ y' ∈ imageOTwoQuot M (Y153 Mc M),
      starAct M (VZ T M) hMV hOC y * starAct M (VZ T M) hMV hOC y' =
        starAct M (VZ T M) hMV hOC y' * starAct M (VZ T M) hMV hOC y :=
    fun y hy y' hy' => hS.comm_oTwoUpper (hPmem y hy) (hPmem y' hy')
  have hinv : ∀ y ∈ imageOTwoQuot M (Y153 Mc M),
      starAct M (VZ T M) hMV hOC ρ₀ * starAct M (VZ T M) hMV hOC y *
        (starAct M (VZ T M) hMV hOC ρ₀)⁻¹ = (starAct M (VZ T M) hMV hOC y)⁻¹ := by
    intro y hy
    rw [hρ₀r]
    exact hrinv _ (oTwoUpper_le _ (hPmem y hy)) (hS.odd_orderOf_of_mem_oTwoUpper (hPmem y hy))
  have hYodd : Odd (Nat.card ↥(imageOTwoQuot M (Y153 Mc M))) := by
    refine odd_card_of_forall_odd_orderOf fun y => ?_
    have hy3 : (y : OTwoQuot M) ^ 3 ∈ imageOTwoQuot M (Y153 Mc M) :=
      (imageOTwoQuot M (Y153 Mc M)).pow_mem y.2 3
    have hρ3 : starAct M (VZ T M) hMV hOC ((y : OTwoQuot M) ^ 3) = 1 := by
      rw [map_pow]
      exact hP3 y y.2
    have hodd3 := hZodd _ hy3 hρ3
    have hd : orderOf (y : OTwoQuot M) ∣ 3 * orderOf ((y : OTwoQuot M) ^ 3) := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [pow_mul, pow_orderOf_eq_one]
    rw [← Subgroup.orderOf_coe]
    exact Odd.of_dvd_nat (Odd.mul (by decide) hodd3) hd
  have hTsY : imageOTwoQuot M T ≤ Subgroup.normalizer (imageOTwoQuot M (Y153 Mc M) : Set _) :=
    imageOTwoQuot_le_normalizer h.T_le fun t ht => le_normalizer_Y153 Mc M (h.T_le ht)
  have hTsR : imageOTwoQuot M T ≤
      Subgroup.normalizer (imageOTwoQuot M (pCoreOf 2 (Mc ⊓ M)) : Set _) :=
    imageOTwoQuot_le_normalizer h.T_le fun t ht =>
      le_normalizer_pCoreOf 2 (Mc ⊓ M) (h.hyp14117.le_inf ht)
  have hdecomp : ∀ q : OTwoQuot M, ∃ x ∈ imageOTwoQuot M (Y153 Mc M) ⊔ imageOTwoQuot M T,
      ∃ c ∈ imageOTwoQuot M (M ⊓ Subgroup.centralizer (VZ T M : Set G)), q = x * c := by
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    have hmapYT : ((imageOTwoQuot M (Y153 Mc M) ⊔ imageOTwoQuot M T).map
        (starAct M (VZ T M) hMV hOC)) = autOn M (VZ T M) := by
      rw [Subgroup.map_sup, map_starAct hMV hOC hYM, map_starAct hMV hOC h.T_le,
        ← autOn_sup (hYM.trans hMV) (h.T_le.trans hMV)]
      exact h.autOn_Y153_sup_T h113
    have hm : starAct M (VZ T M) hMV hOC (QuotientGroup.mk m) ∈
        (imageOTwoQuot M (Y153 Mc M) ⊔ imageOTwoQuot M T).map (starAct M (VZ T M) hMV hOC) := by
      rw [hmapYT]
      exact (mem_autOn_iff_exists).2 ⟨m, hMV m.2, m.2, rfl⟩
    obtain ⟨x, hx, hxm⟩ := Subgroup.mem_map.mp hm
    refine ⟨x, hx, x⁻¹ * QuotientGroup.mk m, ?_, by group⟩
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hxm, inv_mul_cancel]
  have hA : conjClosure (imageOTwoQuot M (pCoreOf 2 (Mc ⊓ M))) ⊤ =
      conjClosure (imageOTwoQuot M (pCoreOf 2 (Mc ⊓ M)))
        (imageOTwoQuot M (Y153 Mc M) ⊔ imageOTwoQuot M T) := by
    apply le_antisymm
    · refine conjClosure_le fun q _ z hz => ?_
      obtain ⟨x, hx, c, hc, rfl⟩ := hdecomp q
      have hcz : c * z = z * c :=
        Subgroup.mem_centralizer_iff.mp (hcent (Subgroup.mem_sup_right hz)) c hc
      have e : x * c * z * (x * c)⁻¹ = x * z * x⁻¹ := by
        calc x * c * z * (x * c)⁻¹ = x * (c * z) * c⁻¹ * x⁻¹ := by group
          _ = x * (z * c) * c⁻¹ * x⁻¹ := by rw [hcz]
          _ = x * z * x⁻¹ := by group
      rw [e]
      exact mem_conjClosure hx hz
    · exact conjClosure_mono le_rfl le_top
  have hRs2 : IsPGroup 2 ↥(imageOTwoQuot M (pCoreOf 2 (Mc ⊓ M))) :=
    isPGroup_imageOTwoQuot (pCoreOf_isPGroup 2 _)
  have hgenEq : imageOTwoQuot M (Y153 Mc M) =
      ⁅imageOTwoQuot M (Y153 Mc M), imageOTwoQuot M (pCoreOf 2 (Mc ⊓ M))⁆ := by
    calc imageOTwoQuot M (Y153 Mc M)
        = oTwoUpper (conjClosure (imageOTwoQuot M (pCoreOf 2 (Mc ⊓ M))) ⊤) := hYq
      _ = oTwoUpper (conjClosure (imageOTwoQuot M (pCoreOf 2 (Mc ⊓ M)))
            (imageOTwoQuot M (Y153 Mc M) ⊔ imageOTwoQuot M T)) := by rw [hA]
      _ = oTwoUpper (⁅imageOTwoQuot M (Y153 Mc M), imageOTwoQuot M (pCoreOf 2 (Mc ⊓ M))⁆ ⊔
            imageOTwoQuot M (pCoreOf 2 (Mc ⊓ M))) := by
          rw [conjClosure_sup_eq_commutator_sup hTsY hTsR]
      _ = ⁅imageOTwoQuot M (Y153 Mc M), imageOTwoQuot M (pCoreOf 2 (Mc ⊓ M))⁆ :=
          oTwoUpper_commutator_sup hYodd hRs2 hRY
  exact ⟨three_group_of_inv (starAct M (VZ T M) hMV hOC) (imageOTwoQuot M (Y153 Mc M))
    (imageOTwoQuot M (pCoreOf 2 (Mc ⊓ M))) ρ₀ hRY hρ₀ hZodd hZc hZR hP3 hPab hinv hgenEq.le, hZc⟩

theorem pRank_Ystar_le (h : Hyp153 G T Mc M) :
    CFSG.Open.pRank 3 (⊤ : Subgroup ↥(imageOTwoQuot M (Y153 Mc M))) ≤ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N : Subgroup ↥M := CFSG.Open.pCore 2 ↥M with hN
  have hrankM : CFSG.Open.pRank 3 (⊤ : Subgroup (OTwoQuot M)) ≤ 2 := by
    have hnd : ¬ 3 ∣ Nat.card N := by
      intro hd
      obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥M) 2).exists_card_eq
      rw [hk] at hd
      exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow hd)) (by norm_num)
    have h1 := CFSG.SectionRank.pRank_quotient_eq (p := 3) N hnd
    have h2 := pRank_top_subtype (p := 3) M
    have h3 := pRank_le_two_of_isTwoLocal h.qtfe.qtke h.inM.1.1 Nat.prime_three (by norm_num)
    calc CFSG.Open.pRank 3 (⊤ : Subgroup (OTwoQuot M)) = CFSG.Open.pRank 3 (⊤ : Subgroup ↥M) := h1
      _ = CFSG.Open.pRank 3 M := h2
      _ ≤ 2 := h3
  calc CFSG.Open.pRank 3 (⊤ : Subgroup ↥(imageOTwoQuot M (Y153 Mc M)))
      = CFSG.Open.pRank 3 (imageOTwoQuot M (Y153 Mc M)) := pRank_top_subtype (p := 3) _
    _ ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (OTwoQuot M)) :=
        CFSG.SectionRank.pRank_mono (by norm_num) le_top
    _ ≤ 2 := hrankM

theorem lemma_15_3_7_cases (h113 : StageLemma14113) (h : Hyp153 G T Mc M) :
    (pCoreOf 2 (Y153 Mc M) = Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G) ∧
        IsElemAbelianOfRank 3 2 (OTwoQuot (Y153 Mc M))) ∨
      (IsPOnePlusTwo 3 (OTwoQuot (Y153 Mc M)) ∧
        O2Z (Y153 Mc M) = Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G)) := by
  obtain ⟨q, L₁, L₂, t, -, -, -, -, hS, -⟩ := h.exists_ofourStruct
  have hMV : M ≤ Subgroup.normalizer (VZ T M : Set G) := h.le_normalizer
  have hOC : pCoreOf 2 M ≤ Subgroup.centralizer (VZ T M : Set G) :=
    h.hyp14117.pCoreOf_le_centralizer
  have hYM : Y153 Mc M ≤ M := Y153_le Mc M
  have hMY := le_normalizer_Y153 Mc M
  obtain ⟨⟨hcl, hΩ, hexp⟩, hZc⟩ := Ystar_structure h113 h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Ys := imageOTwoQuot M (Y153 Mc M) with hYs
  let f : ↥Ys →* MulAut ↥(VZ T M) := (starAct M (VZ T M) hMV hOC).comp Ys.subtype
  have hrange : f.range = oTwoUpper (autOn M (VZ T M)) := by
    show ((starAct M (VZ T M) hMV hOC).comp Ys.subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype, map_starAct hMV hOC hYM]
    exact h.autOn_Y153 h113
  have hcardP : Nat.card f.range = 9 := by
    rw [hrange]
    exact hS.card_oTwoUpper h.isSylowTwoOf_autI
  have hcardYs : Nat.card f.ker * 9 = Nat.card ↥Ys := by
    have h1 := Subgroup.card_mul_index f.ker
    rw [Subgroup.index_ker f, hcardP] at h1
    exact h1
  have h9dvd : 9 ∣ Nat.card ↥Ys := hcardP ▸ Subgroup.card_range_dvd f
  have hexpPG : IsPGroup 3 ↥Ys := fun x => ⟨1, by simpa using hexp x⟩
  have hrank2 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥Ys) = 2 := by
    by_contra hne
    have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥Ys) ≤ 1 := by
      have := pRank_Ystar_le h
      omega
    have hbot : (⊤ : Subgroup ↥Ys) ≠ ⊥ := by
      intro hb
      have hc : Nat.card ↥Ys = 1 := by rw [← Subgroup.card_top, hb, Subgroup.card_bot]
      rw [hc] at h9dvd
      omega
    obtain ⟨z, -, hz, hz3⟩ := exists_eq_zpowers_of_pRank_le_one hexpPG hbot (fun x _ => hexp x) h1
    have hc : Nat.card ↥Ys = 3 := by
      rw [← Subgroup.card_top, hz, Nat.card_zpowers, hz3]
    rw [hc] at h9dvd
    omega
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_imageOTwoQuot hYM hMY
  rcases isElemAbelianOfRank_two_or_isPOnePlusTwo (by norm_num : (3 : ℕ) ≠ 2) hexpPG hΩ hrank2
    hcl with he | hp
  · left
    obtain ⟨e⟩ := he
    have hcard9 : Nat.card ↥Ys = 9 := by
      rw [Nat.card_congr e.toEquiv,
        Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 2 → ZMod 3) ≃ (Fin 2 → ZMod 3))]
      simp
    have hker1 : Nat.card f.ker = 1 := by omega
    refine ⟨?_, ⟨φ.trans e⟩⟩
    apply pCoreOf_eq_inf_centralizer_of_le hYM hMY hOC
    intro y hyY hyC
    have hu : (QuotientGroup.mk (⟨y, hYM hyY⟩ : ↥M) : OTwoQuot M) ∈ Ys :=
      mem_imageOTwoQuot_iff.mpr ⟨y, hYM hyY, hyY, rfl⟩
    have hρu : starAct M (VZ T M) hMV hOC (QuotientGroup.mk (⟨y, hYM hyY⟩ : ↥M)) = 1 :=
      (A4.actionOn_eq_one_iff hMV ⟨y, hYM hyY⟩).mpr hyC
    have hmem : (⟨_, hu⟩ : ↥Ys) ∈ f.ker := hρu
    have hb : f.ker = ⊥ := Subgroup.card_eq_one.mp hker1
    rw [hb, Subgroup.mem_bot] at hmem
    exact (mk_eq_one_iff_mem_pCoreOf ⟨y, hYM hyY⟩).mp (congrArg Subtype.val hmem)
  · right
    refine ⟨A36B.isPOnePlusTwo_of_mulEquiv φ.symm hp, ?_⟩
    have hcard27 : Nat.card ↥Ys = 27 := by rw [hp.2.1]; norm_num
    have hker3 : Nat.card f.ker = 3 := by omega
    have hZ3 : Nat.card (Subgroup.center ↥Ys) = 3 := by
      have := hp.1
      exact CFSG.IsExtraspecial.center_order_p 3 ↥Ys
    have hkerc : f.ker ≤ Subgroup.center ↥Ys := by
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hZc (x : OTwoQuot M) x.2 hx (g : OTwoQuot M) g.2)
    have hkeq : f.ker = Subgroup.center ↥Ys :=
      Subgroup.eq_of_le_of_card_ge hkerc (by rw [hker3, hZ3])
    ext y
    constructor
    · intro hy
      obtain ⟨hyY, hyc⟩ := mem_O2Z_iff.mp hy
      refine ⟨hyY, ?_⟩
      have hcen : φ (QuotientGroup.mk ⟨y, hyY⟩) ∈ Subgroup.center ↥Ys := by
        rw [Subgroup.mem_center_iff]
        intro g
        obtain ⟨a, rfl⟩ := φ.surjective g
        rw [← map_mul, ← map_mul]
        exact congrArg φ (Subgroup.mem_center_iff.mp hyc a)
      rw [← hkeq] at hcen
      have hρ1 : starAct M (VZ T M) hMV hOC
          ((φ (QuotientGroup.mk ⟨y, hyY⟩) : ↥Ys) : OTwoQuot M) = 1 := hcen
      rw [hφ ⟨y, hyY⟩] at hρ1
      exact (A4.actionOn_eq_one_iff hMV ⟨y, hYM hyY⟩).mp hρ1
    · rintro ⟨hyY, hyC⟩
      refine mem_O2Z_iff.mpr ⟨hyY, ?_⟩
      rw [Subgroup.mem_center_iff]
      intro g
      apply φ.injective
      rw [map_mul, map_mul]
      have hmem : φ (QuotientGroup.mk ⟨y, hyY⟩) ∈ f.ker := by
        show starAct M (VZ T M) hMV hOC
          ((φ (QuotientGroup.mk ⟨y, hyY⟩) : ↥Ys) : OTwoQuot M) = 1
        rw [hφ ⟨y, hyY⟩]
        exact (A4.actionOn_eq_one_iff hMV ⟨y, hYM hyY⟩).mpr hyC
      exact Subgroup.mem_center_iff.mp (hkerc hmem) (φ g)


end Hyp153

end CFSG.Quasithin
