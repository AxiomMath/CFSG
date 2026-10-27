module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5ze
public import CFSG.Quasithin.Vol2.Ch12Sec7L5zb
public import CFSG.Quasithin.Vol2.Ch12Sec7L5zc

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.S127.L715.Set714

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.ASInputs S127 S127.L715 S127.L716
  G31
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {t z : G}

abbrev D0 (T L V : Subgroup G) (z : G) : Subgroup G :=
  Subgroup.normalizer (U714 T L V z : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ⊓
    Subgroup.normalizer (V1 T L V : Set G)

omit [Finite G] in
theorem D0_le_N : D0 T L V z ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) :=
  fun _ hd => centralizer_le_normalizer_zpowers z hd.1.2

omit [Finite G] in
theorem tmk_mem_normalizer_Ut {d : G} (hdN : d ∈ Subgroup.normalizer (Subgroup.zpowers z : Set G))
    (hdU : d ∈ Subgroup.normalizer (U714 T L V z : Set G)) :
    tmk (Subgroup.zpowers z) ⟨d, hdN⟩ ∈ Subgroup.normalizer (Ut T L V z : Set (Gt z)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    obtain ⟨u, hu, rfl⟩ := mem_secImg.1 hw
    have e : tmk (Subgroup.zpowers z) ⟨d, hdN⟩ * secMk _ _ u *
        (tmk (Subgroup.zpowers z) ⟨d, hdN⟩)⁻¹ = secMk _ _ (⟨d, hdN⟩ * u * ⟨d, hdN⟩⁻¹) := by
      simp only [map_mul, map_inv]
    rw [e]
    exact secMk_mem_secImg ((Subgroup.mem_normalizer_iff.mp hdU u).mp hu)
  · intro hw
    obtain ⟨u, hu, hwu⟩ := mem_secImg.1 hw
    have hd' : d⁻¹ ∈ Subgroup.normalizer (U714 T L V z : Set G) := Subgroup.inv_mem _ hdU
    have hu' : (⟨d, hdN⟩⁻¹ * u * ⟨d, hdN⟩ : Subgroup.normalizer (Subgroup.zpowers z : Set G)).1 ∈
        U714 T L V z := by
      have := (Subgroup.mem_normalizer_iff.mp hd' u).mp hu
      simpa using this
    have e : w = secMk _ _ (⟨d, hdN⟩⁻¹ * u * ⟨d, hdN⟩) := by
      have h1 : secMk _ _ u = tmk (Subgroup.zpowers z) ⟨d, hdN⟩ * w *
          (tmk (Subgroup.zpowers z) ⟨d, hdN⟩)⁻¹ := hwu
      simp only [map_mul, map_inv]
      rw [h1]
      group
    rw [e]
    exact secMk_mem_secImg hu'

@[expose] noncomputable def rhoD : ↥(D0 T L V z) →* MulAut ↥(Ut T L V z) :=
  (conjAct (Ut T L V z)).comp
    (((tmk (Subgroup.zpowers z)).comp (Subgroup.inclusion D0_le_N)).codRestrict _
      fun d => tmk_mem_normalizer_Ut _ d.2.1.1)

omit [Finite G] in
theorem rhoD_apply (d : ↥(D0 T L V z)) (w : ↥(Ut T L V z)) :
    ((rhoD d w : ↥(Ut T L V z)) : Gt z) =
      tmk (Subgroup.zpowers z) (Subgroup.inclusion D0_le_N d) * (w : Gt z) *
        (tmk (Subgroup.zpowers z) (Subgroup.inclusion D0_le_N d))⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe _ _ w

omit [Finite G] in
theorem rhoD_map_X1_le (d : ↥(D0 T L V z)) :
    (X1 T L V z).map (rhoD d).toMonoidHom ≤ X1 T L V z := by
  rintro _ ⟨w, hw, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hw
  show ((rhoD d w : ↥(Ut T L V z)) : Gt z) ∈ tildeOf (Subgroup.zpowers z) (V1 T L V)
  obtain ⟨v, hv, hvw⟩ := mem_secImg.1 hw
  rw [rhoD_apply, ← hvw]
  set y := Subgroup.inclusion D0_le_N d with hy
  have e : tmk (Subgroup.zpowers z) y * secMk _ _ v * (tmk (Subgroup.zpowers z) y)⁻¹ =
      tmk (Subgroup.zpowers z) (y * v * y⁻¹) := by
    simp only [map_mul, map_inv]
  rw [e]
  exact secMk_mem_secImg ((Subgroup.mem_normalizer_iff.mp d.2.2 v).mp hv)

theorem rhoD_map_X1 (d : ↥(D0 T L V z)) :
    (X1 T L V z).map (rhoD d).toMonoidHom = X1 T L V z :=
  Subgroup.eq_of_le_of_card_ge (rhoD_map_X1_le d)
    (by rw [Subgroup.card_map_of_injective (MulEquiv.injective _)])

@[expose] noncomputable def rho1 [IsMulCommutative ↥(Ut T L V z)] :
    ↥(D0 T L V z) →* MulAut (↥(Ut T L V z) ⧸ X1 T L V z) where
  toFun d := QuotientGroup.congr _ _ (rhoD d) (rhoD_map_X1 d)
  map_one' := by
    refine MulEquiv.ext fun q => ?_
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (X1 T L V z) q
    show QuotientGroup.mk' _ (rhoD 1 w) = QuotientGroup.mk' _ w
    rw [map_one]
    rfl
  map_mul' a b := by
    refine MulEquiv.ext fun q => ?_
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (X1 T L V z) q
    show QuotientGroup.mk' _ (rhoD (a * b) w) = QuotientGroup.mk' _ (rhoD a (rhoD b w))
    rw [map_mul]
    rfl

theorem rho1_mk [IsMulCommutative ↥(Ut T L V z)] (d : ↥(D0 T L V z)) (w : ↥(Ut T L V z)) :
    rho1 d (QuotientGroup.mk' _ w) = QuotientGroup.mk' _ (rhoD d w) := rfl

variable (s : Set714 G T L V t z)
include s

theorem NH_le_D0 (h1222 : Stmt12_2_2) :
    H714 T L V z ⊓ Subgroup.normalizer (V1 T L V : Set G) ≤ D0 T L V z :=
  fun _ hh => ⟨⟨s.H_le_normalizer_U h1222 hh.1, s.H_le_Gz h1222 hh.1⟩, hh.2⟩

theorem C_le_D0 : Subgroup.centralizer (V1 T L V : Set G) ≤ D0 T L V z := by
  have hCz : Subgroup.centralizer (V1 T L V : Set G) ≤ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr s.mem)
  have hCV1 : Subgroup.centralizer (V1 T L V : Set G) ≤ Subgroup.normalizer (V1 T L V : Set G) :=
    Subgroup.centralizer_le_normalizer _
  exact fun c hc => ⟨⟨le_normalizer_conjClosure_of hCV1 (hCz.trans Gz_le_normalizer_K) hc,
    hCz hc⟩, hCV1 hc⟩

theorem rhoD_eq_rho
    (h1222 : Stmt12_2_2) {h : G} (hH : h ∈ H714 T L V z) (hD : h ∈ D0 T L V z) :
    rhoD ⟨h, hD⟩ = s.rho h1222 ⟨h, hH⟩ :=
  MulEquiv.ext fun w => Subtype.ext (by rw [rhoD_apply, s.rho_apply]; rfl)

theorem rho1_surj_NH
    [IsMulCommutative ↥(Ut T L V z)] (h1222 : Stmt12_2_2) (hHs : Hs T L V z = ⊤)
    (φ : MulAut (↥(Ut T L V z) ⧸ X1 T L V z)) :
    ∃ (h : G) (hD : h ∈ D0 T L V z), h ∈ H714 T L V z ∧ rho1 ⟨h, hD⟩ = φ := by
  have hV : ∀ v : ↥(Ut T L V z), v ^ 2 = 1 := fun v =>
    Subtype.ext ((s.elemAbelian_Ut h1222).2 _ v.2)
  obtain ⟨g, hgX, hgφ⟩ := Lift3.exists_lift hV (X1 T L V z) φ
  have hg : g ∈ (s.rho h1222).range := by
    rw [s.range_rho h1222, hHs]
    exact Subgroup.mem_top g
  obtain ⟨⟨h, hH⟩, rfl⟩ := hg
  have hzV1 : Subgroup.zpowers z ≤ V1 T L V := Subgroup.zpowers_le_of_mem s.mem
  have hconj : ∀ v ∈ V1 T L V, h * v * h⁻¹ ∈ V1 T L V := by
    intro v hv
    have hvN : v ∈ Subgroup.normalizer (Subgroup.zpowers z : Set G) := s.V1_le_N h1222 hv
    have hvU : tmk (Subgroup.zpowers z) ⟨v, hvN⟩ ∈ Ut T L V z :=
      secMk_mem_secImg (le_conjClosure _ _ hv)
    have hvX : (⟨_, hvU⟩ : ↥(Ut T L V z)) ∈ X1 T L V z := by
      rw [Subgroup.mem_subgroupOf]
      exact secMk_mem_secImg hv
    have hmem : s.rho h1222 ⟨h, hH⟩ ⟨_, hvU⟩ ∈ X1 T L V z := by
      rw [← hgX]
      exact Subgroup.mem_map_of_mem _ hvX
    rw [Subgroup.mem_subgroupOf, s.rho_apply] at hmem
    have hhN := s.H_le_N h1222 hH
    have e : tmk (Subgroup.zpowers z) (Subgroup.inclusion (s.H_le_N h1222) ⟨h, hH⟩) *
        tmk (Subgroup.zpowers z) ⟨v, hvN⟩ *
          (tmk (Subgroup.zpowers z) (Subgroup.inclusion (s.H_le_N h1222) ⟨h, hH⟩))⁻¹ =
        tmk (Subgroup.zpowers z) (⟨h, hhN⟩ * ⟨v, hvN⟩ * ⟨h, hhN⟩⁻¹) := by
      simp only [map_mul, map_inv]
      rfl
    rw [e] at hmem
    exact (secMk_mem_secImg_iff hzV1).mp hmem
  have hhV1 : h ∈ Subgroup.normalizer (V1 T L V : Set G) :=
    Subgroup.mem_normalizer_fintype fun v hv => hconj v hv
  refine ⟨h, s.NH_le_D0 h1222 ⟨hH, hhV1⟩, hH, ?_⟩
  rw [← hgφ]
  refine MulEquiv.ext fun q => ?_
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (X1 T L V z) q
  show _ = QuotientGroup.mk' _ ((s.rho h1222 ⟨h, hH⟩) w)
  rw [rho1_mk, s.rhoD_eq_rho h1222 hH]

theorem rhoD_fix_X1
    (h1222 : Stmt12_2_2) (d : ↥(D0 T L V z)) {w : ↥(Ut T L V z)} (hw : w ∈ X1 T L V z) :
    rhoD d w = w := by
  have h2 := s.card_X1 h1222
  have hmem : rhoD d w ∈ X1 T L V z := rhoD_map_X1_le d (Subgroup.mem_map_of_mem _ hw)
  by_contra hne
  have h1 : w ≠ 1 := fun h => hne (by rw [h, map_one])
  have h1' : rhoD d w ≠ 1 := fun h => h1 ((MulEquiv.map_eq_one_iff _).mp h)
  have h3 : 3 ≤ Nat.card ↥(X1 T L V z) := by
    classical
    have : Fintype ↥(X1 T L V z) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card]
    have hs : ({⟨1, Subgroup.one_mem _⟩, ⟨w, hw⟩, ⟨rhoD d w, hmem⟩} :
        Finset ↥(X1 T L V z)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair]
      · exact fun h => hne (congrArg Subtype.val h).symm
      · simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, not_or]
        exact ⟨fun h => h1 h.symm, fun h => h1' h.symm⟩
    rw [← hs]
    exact Finset.card_le_univ _
  omega

theorem sq_mem_C
    [IsMulCommutative ↥(Ut T L V z)] (h1222 : Stmt12_2_2) (d : ↥(D0 T L V z)) :
    ((d : G) ^ 2) ∈ Subgroup.centralizer (V1 T L V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hvN : v ∈ Subgroup.normalizer (Subgroup.zpowers z : Set G) := s.V1_le_N h1222 hv
  have hvU : tmk (Subgroup.zpowers z) ⟨v, hvN⟩ ∈ Ut T L V z :=
    secMk_mem_secImg (le_conjClosure _ _ hv)
  have hvX : (⟨_, hvU⟩ : ↥(Ut T L V z)) ∈ X1 T L V z := by
    rw [Subgroup.mem_subgroupOf]
    exact secMk_mem_secImg hv
  have hfix := congrArg Subtype.val (s.rhoD_fix_X1 h1222 d hvX)
  rw [rhoD_apply] at hfix
  set y := Subgroup.inclusion D0_le_N d with hy
  have e : tmk (Subgroup.zpowers z) y * tmk (Subgroup.zpowers z) ⟨v, hvN⟩ *
      (tmk (Subgroup.zpowers z) y)⁻¹ = tmk (Subgroup.zpowers z) (y * ⟨v, hvN⟩ * y⁻¹) := by
    simp only [map_mul, map_inv]
  rw [e] at hfix
  have ha := secMk_eq_secMk_iff.mp hfix
  set a : G := (y * ⟨v, hvN⟩ * y⁻¹ : Subgroup.normalizer (Subgroup.zpowers z : Set G)).1⁻¹ * v
    with ha_def
  have haz : a ∈ Subgroup.zpowers z := ha
  have hdz : (d : G) * z = z * d := Subgroup.mem_centralizer_singleton_iff.mp d.2.1.2
  have hz2 : z ^ 2 = 1 := by rw [← s.orderOf_z]; exact pow_orderOf_eq_one z
  have hda : (d : G) * a = a * d := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp haz
    rw [← hk]
    exact ((Commute.zpow_right (show Commute (d : G) z from hdz) k)).eq
  have haa : a * a = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp haz
    rcases Lift3.mem_zpowers_two (W := ↥(Subgroup.zpowers z)) (e := ⟨z, Subgroup.mem_zpowers z⟩)
      (Subtype.ext (by simpa using hz2)) (x := ⟨a, haz⟩)
      (by
        refine Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
        simpa using hk) with h0 | h0
    · have : a = 1 := congrArg Subtype.val h0
      rw [this, one_mul]
    · have : a = z := congrArg Subtype.val h0
      rw [this, ← pow_two, hz2]
  have hdv : (d : G) * v * (d : G)⁻¹ = v * a⁻¹ := by
    have : a = ((d : G) * v * (d : G)⁻¹)⁻¹ * v := rfl
    rw [this]
    group
  have ha' : a⁻¹ = a := by
    calc a⁻¹ = a⁻¹ * (a * a) := by rw [haa, mul_one]
      _ = a := by group
  have hdv' : (d : G) * v * (d : G)⁻¹ = v * a := by rw [hdv, ha']
  have hda' : (d : G) * a * (d : G)⁻¹ = a := by rw [hda, mul_inv_cancel_right]
  have h1 : (d : G) * (v * a) * (d : G)⁻¹ = v * a * a := by
    rw [show (d : G) * (v * a) * (d : G)⁻¹ = ((d : G) * v * (d : G)⁻¹) * ((d : G) * a * (d : G)⁻¹)
      by group, hdv', hda']
  have h2 : (d : G) ^ 2 * v * ((d : G) ^ 2)⁻¹ = v := by
    calc (d : G) ^ 2 * v * ((d : G) ^ 2)⁻¹ = (d : G) * ((d : G) * v * (d : G)⁻¹) * (d : G)⁻¹ := by
          rw [pow_two]
          group
      _ = (d : G) * (v * a) * (d : G)⁻¹ := by rw [hdv']
      _ = v * a * a := h1
      _ = v := by rw [mul_assoc, haa, mul_one]
  calc v * (d : G) ^ 2 = ((d : G) ^ 2 * v * ((d : G) ^ 2)⁻¹) * (d : G) ^ 2 := by rw [h2]
    _ = (d : G) ^ 2 * v := by rw [inv_mul_cancel_right]

theorem quot_facts
    [IsMulCommutative ↥(Ut T L V z)] (h1222 : Stmt12_2_2) (hd : Nat.card ↥(Ut T L V z) = 2 ^ 5) :
    (∀ q : ↥(Ut T L V z) ⧸ X1 T L V z, q ^ 2 = 1) ∧
      Nat.card (↥(Ut T L V z) ⧸ X1 T L V z) = 2 ^ 4 := by
  have hV : ∀ v : ↥(Ut T L V z), v ^ 2 = 1 := fun v =>
    Subtype.ext ((s.elemAbelian_Ut h1222).2 _ v.2)
  refine ⟨fun q => ?_, ?_⟩
  · obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (X1 T L V z) q
    rw [← map_pow, hV, map_one]
  · have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (X1 T L V z)
    rw [hd, s.card_X1 h1222] at h
    omega

theorem mulAut_quot_simple
    [IsMulCommutative ↥(Ut T L V z)] (h1222 : Stmt12_2_2) (hd : Nat.card ↥(Ut T L V z) = 2 ^ 5) :
    IsSimpleGroup (MulAut (↥(Ut T L V z) ⧸ X1 T L V z)) ∧
      ∃ a b : MulAut (↥(Ut T L V z) ⧸ X1 T L V z), a * b ≠ b * a := by
  obtain ⟨hq2, hq4⟩ := s.quot_facts h1222 hd
  exact ⟨G31.isSimpleGroup_mulAut hq2 hq4 (by norm_num),
    G31.nonabelian_mulAut hq2 hq4 (by norm_num)⟩

theorem rho1_C_surj
    [IsMulCommutative ↥(Ut T L V z)] (h1222 : Stmt12_2_2) (hHs : Hs T L V z = ⊤)
    (hd : Nat.card ↥(Ut T L V z) = 2 ^ 5) :
    Function.Surjective (rho1.comp (Subgroup.inclusion s.C_le_D0)) := by
  obtain ⟨hsimple, hnab⟩ := s.mulAut_quot_simple h1222 hd
  obtain ⟨hq2, hq4⟩ := s.quot_facts h1222 hd
  set S := Subgroup.closure
    (Set.range fun φ : MulAut (↥(Ut T L V z) ⧸ X1 T L V z) => φ ^ 2) with hS
  have hSR : S ≤ (rho1.comp (Subgroup.inclusion s.C_le_D0)).range := by
    rw [hS, Subgroup.closure_le]
    rintro _ ⟨φ, rfl⟩
    obtain ⟨h, hD, -, hφ⟩ := s.rho1_surj_NH h1222 hHs φ
    have hsq := s.sq_mem_C h1222 ⟨h, hD⟩
    refine ⟨⟨h ^ 2, hsq⟩, ?_⟩
    have e : (⟨h ^ 2, s.C_le_D0 hsq⟩ : ↥(D0 T L V z)) = ⟨h, hD⟩ ^ 2 := Subtype.ext (by simp)
    show rho1 ⟨h ^ 2, s.C_le_D0 hsq⟩ = (fun φ => φ ^ 2) φ
    rw [e, map_pow, hφ]
  have hSn : S.Normal := by
    refine ⟨fun x hx g => ?_⟩
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨φ, rfl⟩ := hx
      exact Subgroup.subset_closure ⟨g * φ * g⁻¹, by
        show (g * φ * g⁻¹) ^ 2 = g * φ ^ 2 * g⁻¹
        rw [pow_two, pow_two]
        group⟩
    | one =>
      rw [mul_one, mul_inv_cancel]
      exact Subgroup.one_mem _
    | mul a b _ _ ha hb =>
      have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ ha
  have hSne : S ≠ ⊥ := by
    obtain ⟨Y, -, hY3, -, -, -, hcard⟩ := Lift3.exists_mulAut hq2 hq4 (k := 1) (by norm_num)
    have hY1 : Y 0 ≠ 1 := by
      intro h1
      have hle : Subgroup.closure (Set.range Y) ≤ ⊥ := by
        rw [Subgroup.closure_le]
        rintro _ ⟨i, rfl⟩
        rw [Fin.fin_one_eq_zero i, h1]
        exact Subgroup.one_mem _
      have := Subgroup.card_le_of_le hle
      rw [Subgroup.card_bot] at this
      omega
    intro hbot
    apply hY1
    have hsq : Y 0 ^ 2 ∈ S := Subgroup.subset_closure ⟨Y 0, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hsq
    calc Y 0 = Y 0 ^ 3 * (Y 0 ^ 2)⁻¹ := by group
      _ = 1 := by rw [hY3, hsq]; group
  have hStop : S = ⊤ := (IsSimpleGroup.eq_bot_or_eq_top_of_normal S).resolve_left hSne
  intro φ
  exact hSR (hStop ▸ Subgroup.mem_top φ)

omit s in
theorem cCompSpan_top_of {K : Subgroup G} (hy : Hyp1223 G T L V) (h39 : A39ForSQTK)
    (hK : pCoreOf 2 K ≠ ⊥) : cCompSpan (⊤ : Subgroup ↥K) = perfectCore (⊤ : Subgroup ↥K) := by
  have hspan0 := CFSG.Quasithin.lemma_1_2_1_one hy.qtke hy.simple hy.nonabelian h39 hK
  have h1 : perfectCore (⊤ : Subgroup ↥K) = (perfectCore K).subgroupOf K := by
    rw [← C124.perfectCore_subgroupOf' (le_refl K), Subgroup.subgroupOf_self]
  rw [h1, ← hspan0, cCompSpan_eq_map_subtype K, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _)]

theorem V1_le_pCoreOf_C
    (h1222 : Stmt12_2_2) : V1 T L V ≤ pCoreOf 2 (Subgroup.centralizer (V1 T L V : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcomm, -, -⟩ := S127.card_eq_of_1222 h1222 s.setting.hyp
  have := hcomm
  have hV1V : V1 T L V ≤ V := inf_le_left
  have hV1C : V1 T L V ≤ Subgroup.centralizer (V1 T L V : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun b hb =>
      congrArg Subtype.val (hcomm.is_comm.comm ⟨b, hV1V hb⟩ ⟨a, hV1V ha⟩)
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hV1C
    (Subgroup.centralizer_le_normalizer _) ?_
  have h4 : Nat.card ↥(V1 T L V) = 4 := (S127.Mod.lemma12_7_2_two h1222 s.setting.hyp).1.2
  exact IsPGroup.of_card (n := 2) (by rw [h4]; norm_num)

theorem pCoreOf_C_ne_bot
    (h1222 : Stmt12_2_2) : pCoreOf 2 (Subgroup.centralizer (V1 T L V : Set G)) ≠ ⊥ := fun hb =>
  s.ne_one (by
    have := s.V1_le_pCoreOf_C h1222 s.mem
    rwa [hb, Subgroup.mem_bot] at this)

theorem exists_cComp_C
    [IsMulCommutative ↥(Ut T L V z)] (h1222 : Stmt12_2_2) (h39 : A39ForSQTK)
    (hHs : Hs T L V z = ⊤) (hd : Nat.card ↥(Ut T L V z) = 2 ^ 5) :
    ∃ I ∈ cComp (⊤ : Subgroup ↥(Subgroup.centralizer (V1 T L V : Set G))),
      I.map (rho1.comp (Subgroup.inclusion s.C_le_D0)) = ⊤ := by
  obtain ⟨hsimple, hnab⟩ := s.mulAut_quot_simple h1222 hd
  exact Lift3.exists_cComp_map_top hnab _ (s.rho1_C_surj h1222 hHs hd)
    (cCompSpan_top_of s.setting.hyp.hyp h39 (s.pCoreOf_C_ne_bot h1222))

end CFSG.Quasithin.H13.S127.L715.Set714
