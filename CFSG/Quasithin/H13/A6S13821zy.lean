module

public import CFSG.Quasithin.H13.A6S13821zx
public import CFSG.Quasithin.EmptyFaithful.S1565A
public import CFSG.Quasithin.H13.A6S13821zw

public section

namespace CFSG.Quasithin.H13.A6.A6S20

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7

attribute [local instance] commGroupOfFact

theorem fix_of_sum_of_inf {M : Type} [CommGroup M] {K B : Subgroup (MulAut M)} (hBK : B ≤ K)
    {I I' : Subgroup M} (hKI : ∀ k ∈ K, ∀ a ∈ I, k a ∈ I) (hKI' : ∀ k ∈ K, ∀ a ∈ I', k a ∈ I')
    (hI : ∀ a ∈ I, (∀ b ∈ B, b a * a⁻¹ ∈ fixV K) → a ∈ fixV K)
    (hI' : ∀ a ∈ I', (∀ b ∈ B, b a * a⁻¹ ∈ fixV K) → a ∈ fixV K) (hA : I ⊓ I' ≤ fixV K) :
    ∀ v ∈ I ⊔ I', (∀ b ∈ B, b v = v) → v ∈ fixV K := by
  intro v hv hvB
  obtain ⟨a, ha, a', ha', rfl⟩ := Subgroup.mem_sup.mp hv
  have hfixK : ∀ k ∈ K, ∀ c ∈ fixV K, k c = c := fun k hk c hc => hc k hk
  have h1 : ∀ b ∈ B, b a' * a'⁻¹ ∈ fixV K := by
    intro b hb
    apply hA
    have e : b a' * a'⁻¹ = (b a * a⁻¹)⁻¹ := by
      have := hvB b hb
      rw [map_mul] at this
      calc b a' * a'⁻¹ = (b a)⁻¹ * (b a * b a') * a'⁻¹ := by group
        _ = (b a)⁻¹ * (a * a') * a'⁻¹ := by rw [this]
        _ = (b a)⁻¹ * a := by group
        _ = (b a * a⁻¹)⁻¹ := by rw [_root_.mul_inv_rev, inv_inv, mul_comm]
    refine ⟨?_, I'.mul_mem (hKI' b (hBK hb) a' ha') (I'.inv_mem ha')⟩
    rw [e]
    exact I.inv_mem (I.mul_mem (hKI b (hBK hb) a ha) (I.inv_mem ha))
  have ha'K := hI' a' ha' h1
  have h2 : ∀ b ∈ B, b a * a⁻¹ ∈ fixV K := by
    intro b hb
    have := hvB b hb
    rw [map_mul, hfixK b (hBK hb) a' ha'K] at this
    have e : b a = a := mul_right_cancel this
    rw [e, mul_inv_cancel]
    exact (fixV K).one_mem
  exact (fixV K).mul_mem (hI a ha h2) ha'K

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_modMk_of_mem_subM {V₁ IH J : Subgroup G}
    (hIHN : IH ≤ Subgroup.normalizer (V₁ : Set G)) (hV₁J : V₁ ≤ J) {w : ↥(tildeOf V₁ IH)}
    (hw : w ∈ subM V₁ IH J) : ∃ (a : G) (ha : a ∈ IH), a ∈ J ∧ w = modMk hIHN a ha := by
  obtain ⟨a, haIH, haw⟩ := exists_mk_of_mem_tilde w
  have h1 : (w : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) ∈ tildeOf V₁ J := hw
  rw [← haw] at h1
  exact ⟨a, haIH, (secMk_mem_tildeOf_iff hV₁J).mp h1, Subtype.ext haw.symm⟩

theorem modMk_mem_fixV_autIH_iff {T V L V₁ Vp H K I : Subgroup G}
    (hF : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))] {X : Subgroup G} (hXH : X ≤ H) {u : G}
    (hu : u ∈ conjClosure I H) :
    modMk (hF.conjClosure_le_normalizer_V₁ hIU) u hu ∈ fixV (autIH V₁ I H X) ↔
      ∀ x ∈ X, x * u * x⁻¹ * u⁻¹ ∈ V₁ := by
  have hIHN := hF.conjClosure_le_normalizer_V₁ hIU
  have hIH := le_normalizer_conjClosure I H
  have hxu : ∀ x ∈ X, x * u * x⁻¹ ∈ conjClosure I H := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (hIH (hXH hx)) u).mp hu
  rw [autIH_eq_map hF hXH]
  constructor
  · intro h x hx
    have h1 := h (actH hF.H_le_normalizer_V₁ hIH ⟨x, hXH hx⟩)
      ⟨⟨x, hXH hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rw [actH_modMk hF.H_le_normalizer_V₁ hIHN hIH ⟨x, hXH hx⟩ hu] at h1
    exact (A6Tv.modMk_conj_eq_iff' hIHN hu (hxu x hx)).mp h1
  · intro h g hg
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg
    have hy' : (y : G) ∈ X := Subgroup.mem_subgroupOf.mp hy
    rw [actH_modMk hF.H_le_normalizer_V₁ hIHN hIH y hu]
    exact (A6Tv.modMk_conj_eq_iff' hIHN hu (hxu _ hy')).mpr (h _ hy')

omit [Finite G] in
theorem odd_index_of_sylow {K T₀ B : Subgroup G} (hsyl : IsSylowTwoOf T₀ K) (hTB : T₀ ≤ B) :
    Odd (B.subgroupOf K).index := by
  have h1 : (B.subgroupOf K).index ∣ (T₀.subgroupOf K).index :=
    Subgroup.index_dvd_of_le fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hTB (Subgroup.mem_subgroupOf.mp hx))
  have h2 : ¬ 2 ∣ (T₀.subgroupOf K).index := hsyl.2.2
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h => h2 (h.trans h1))

theorem fixProp_sup_of_fpf {T V L V₁ Vp H K I : Subgroup G} (hF : HypF918 T V L V₁ Vp H K)
    (hK₀ : conjClosure K T = K) (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H)
    (hirr : IsIrrPlusTilde V₁ (conjClosure K T) I)
    [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure Vp H)))] {c : G} (hcH : c ∈ H)
    (hII : I ⊓ conjSub c I ≤ centralizerMod V₁ I K) {B₀ : Subgroup G} (hB₀K : B₀ ≤ K) {k : G}
    (hkB : k ∈ B₀)
    (hkI : ∀ i ∈ I, k * i * k⁻¹ * i⁻¹ ∈ centralizerMod V₁ I (conjClosure K T) →
      i ∈ centralizerMod V₁ I (conjClosure K T))
    (hk'I : ∀ i ∈ I, c⁻¹ * k * c * i * (c⁻¹ * k * c)⁻¹ * i⁻¹ ∈
      centralizerMod V₁ I (conjClosure K T) → i ∈ centralizerMod V₁ I (conjClosure K T)) :
    S1565.FixProp ((actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H)).comp
        (Subgroup.inclusion (le_of_mem_cComp hF.K_cComp))) (B₀.subgroupOf K) ⊥
      (subM V₁ (conjClosure Vp H) (I ⊔ conjSub c I)) := by
  classical
  have h1 := hF.toHypF98.toHypF91
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hHV₁ : H ≤ Subgroup.normalizer (V₁ : Set G) := hF.H_le_normalizer_V₁
  have hUH : conjClosure Vp H ≤ H := h1.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)
  have hUab := hF.toHypF98.F911_3
  have hKn : ∀ h ∈ H, h ∈ Subgroup.normalizer (K : Set G) := fun h hh => by
    have := hF.K₀_normal hh
    rwa [hK₀] at this
  have hcK := hKn c hcH
  have hcV₁ : c ∈ Subgroup.normalizer (V₁ : Set G) := hHV₁ hcH
  have hKI : K ≤ Subgroup.normalizer (I : Set G) := (le_conjClosure K T).trans hirr.1
  have hHU : H ≤ Subgroup.normalizer ((conjClosure Vp H : Subgroup G) : Set G) :=
    le_normalizer_conjClosure Vp H
  have hIc : conjSub c I ≤ conjClosure Vp H := by
    rw [← conjSub_eq_of_mem_normalizer (hHU hcH)]
    exact conjSub_mono c hIU
  have hV₁c : V₁ ≤ conjSub c I := by
    have h2 := conjSub_mono c hV₁I
    rwa [conjSub_eq_of_mem_normalizer hcV₁] at h2
  have hcKc : ∀ x ∈ K, c⁻¹ * x * c ∈ K := fun x hx => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hcK) x).mp hx
    simpa using this
  have hKIc : K ≤ Subgroup.normalizer ((conjSub c I : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_conjSub (hKI (hcKc x hx))
  have hPconj : ∀ g ∈ Subgroup.normalizer (V₁ : Set G), g ∈ Subgroup.normalizer (K : Set G) →
      ∀ z : G, (∀ x ∈ K, x * z * x⁻¹ * z⁻¹ ∈ V₁) →
        ∀ x ∈ K, x * (g * z * g⁻¹) * x⁻¹ * (g * z * g⁻¹)⁻¹ ∈ V₁ := by
    intro g hgV hgK z hz x hx
    have hx' : g⁻¹ * x * g ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgK) x).mp hx
      simpa using this
    have h2 := (Subgroup.mem_normalizer_iff.mp hgV _).mp (hz _ hx')
    have e : g * (g⁻¹ * x * g * z * (g⁻¹ * x * g)⁻¹ * z⁻¹) * g⁻¹ =
        x * (g * z * g⁻¹) * x⁻¹ * (g * z * g⁻¹)⁻¹ := by group
    rwa [e] at h2
  have hPC : ∀ y ∈ I, (∀ x ∈ K, x * y * x⁻¹ * y⁻¹ ∈ V₁) ↔
      y ∈ centralizerMod V₁ I (conjClosure K T) := by
    intro y hy
    rw [hK₀]
    constructor
    · intro h
      refine ⟨hy, hHV₁ (hUH (hIU hy)), fun x hx => ?_⟩
      have h2 := V₁.inv_mem (h x hx)
      have e : (x * y * x⁻¹ * y⁻¹)⁻¹ = y * x * y⁻¹ * x⁻¹ := by group
      rwa [e] at h2
    · intro h x hx
      have h2 := V₁.inv_mem (h.2.2 x hx)
      have e : (y * x * y⁻¹ * x⁻¹)⁻¹ = x * y * x⁻¹ * y⁻¹ := by group
      rwa [e] at h2
  have hkK : k ∈ K := hB₀K hkB
  have hUN : conjClosure Vp H ≤ Subgroup.normalizer (V₁ : Set G) :=
    hF.conjClosure_le_normalizer_V₁ (le_conjClosure Vp H)
  have hfix := fun {y : G} (hy : y ∈ conjClosure Vp H) =>
    modMk_mem_fixV_autIH_iff hF (le_conjClosure Vp H) hKH hy
  have hB₀H : B₀ ≤ H := hB₀K.trans hKH
  have hBMK : autIH V₁ Vp H B₀ ≤ autIH V₁ Vp H K := autOn_le_autOn _ (secImg_mono hB₀K)
  have hψk : actH hHV₁ hHU ⟨k, hKH hkK⟩ ∈ autIH V₁ Vp H B₀ := by
    rw [autIH_eq_map hF hB₀H]
    exact ⟨⟨k, hKH hkK⟩, Subgroup.mem_subgroupOf.mpr hkB, rfl⟩
  have hcommk : ∀ (a : G) (ha : a ∈ conjClosure Vp H),
      ∃ hka : k * a * k⁻¹ * a⁻¹ ∈ conjClosure Vp H,
        actH hHV₁ hHU ⟨k, hKH hkK⟩ (modMk hUN a ha) * (modMk hUN a ha)⁻¹ =
          modMk hUN (k * a * k⁻¹ * a⁻¹) hka := by
    intro a ha
    have hka : k * a * k⁻¹ ∈ conjClosure Vp H :=
      (Subgroup.mem_normalizer_iff.mp (hHU (hKH hkK)) a).mp ha
    refine ⟨(conjClosure Vp H).mul_mem hka ((conjClosure Vp H).inv_mem ha), ?_⟩
    rw [actH_modMk hHV₁ hUN hHU ⟨k, hKH hkK⟩ ha, ← modMk_inv hUN ha,
      ← modMk_mul hUN hka ((conjClosure Vp H).inv_mem ha)]
  have hstab : ∀ {J : Subgroup G}, V₁ ≤ J → J ≤ conjClosure Vp H →
      K ≤ Subgroup.normalizer (J : Set G) → ∀ g ∈ autIH V₁ Vp H K,
        ∀ a ∈ subM V₁ (conjClosure Vp H) J, g a ∈ subM V₁ (conjClosure Vp H) J := by
    intro J hV₁J hJU hKJ g hg a ha
    rw [autIH_eq_map hF hKH] at hg
    obtain ⟨x, hx, rfl⟩ := hg
    exact ((actH_mem_stabSub_subM_iff hHV₁ hUN hHU hV₁J hJU x).mpr
      (hKJ (Subgroup.mem_subgroupOf.mp hx)) a).mpr ha
  have hnoI : ∀ a ∈ subM V₁ (conjClosure Vp H) I,
      (∀ b ∈ autIH V₁ Vp H B₀, b a * a⁻¹ ∈ fixV (autIH V₁ Vp H K)) →
        a ∈ fixV (autIH V₁ Vp H K) := by
    intro a ha hab
    obtain ⟨i, hiU, hiI, rfl⟩ := exists_modMk_of_mem_subM hUN hV₁I ha
    obtain ⟨hka, hb⟩ := hcommk i hiU
    have h2 := hab _ hψk
    rw [hb, hfix hka] at h2
    have hkiI : k * i * k⁻¹ * i⁻¹ ∈ I :=
      I.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKI hkK) i).mp hiI) (I.inv_mem hiI)
    have hiC := hkI i hiI ((hPC _ hkiI).mp h2)
    rw [hfix hiU]
    exact (hPC i hiI).mpr hiC
  have hnoIc : ∀ a ∈ subM V₁ (conjClosure Vp H) (conjSub c I),
      (∀ b ∈ autIH V₁ Vp H B₀, b a * a⁻¹ ∈ fixV (autIH V₁ Vp H K)) →
        a ∈ fixV (autIH V₁ Vp H K) := by
    intro a ha hab
    obtain ⟨i', hiU, hiI', rfl⟩ := exists_modMk_of_mem_subM hUN hV₁c ha
    obtain ⟨hka, hb⟩ := hcommk i' hiU
    have h2 := hab _ hψk
    rw [hb, hfix hka] at h2
    have hiI : c⁻¹ * i' * c ∈ I := mem_conjSub.mp hiI'
    have h3 := hPconj c⁻¹ (Subgroup.inv_mem _ hcV₁) (Subgroup.inv_mem _ hcK) _ h2
    have e : c⁻¹ * (k * i' * k⁻¹ * i'⁻¹) * c⁻¹⁻¹ =
        c⁻¹ * k * c * (c⁻¹ * i' * c) * (c⁻¹ * k * c)⁻¹ * (c⁻¹ * i' * c)⁻¹ := by group
    rw [e] at h3
    have hk'iI : c⁻¹ * k * c * (c⁻¹ * i' * c) * (c⁻¹ * k * c)⁻¹ * (c⁻¹ * i' * c)⁻¹ ∈ I :=
      I.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKI (hcKc k hkK)) _).mp hiI) (I.inv_mem hiI)
    have hiC := hk'I _ hiI ((hPC _ hk'iI).mp h3)
    have h4 := hPconj c hcV₁ hcK _ ((hPC _ hiI).mpr hiC)
    have e2 : c * (c⁻¹ * i' * c) * c⁻¹ = i' := by group
    rw [e2] at h4
    rw [hfix hiU]
    exact h4
  have hA : subM V₁ (conjClosure Vp H) I ⊓ subM V₁ (conjClosure Vp H) (conjSub c I) ≤
      fixV (autIH V₁ Vp H K) := by
    rintro w ⟨hw1, hw2⟩
    obtain ⟨y, hyU, hyI, rfl⟩ := exists_modMk_of_mem_subM hUN hV₁I hw1
    have hyc : y ∈ conjSub c I := (modMk_mem_subM_iff hUN hV₁c hyU).mp hw2
    have hyC := hII ⟨hyI, hyc⟩
    rw [hfix hyU]
    exact (hPC y hyI).mpr (by rw [hK₀]; exact hyC)
  have hIIc : I ≤ Subgroup.normalizer ((conjSub c I : Subgroup G) : Set G) :=
    hIU.trans (HypF91.le_normalizer_of_isElemAbelian_le hUab hIc)
  have hJM : subM V₁ (conjClosure Vp H) (I ⊔ conjSub c I) ≤
      subM V₁ (conjClosure Vp H) I ⊔ subM V₁ (conjClosure Vp H) (conjSub c I) := by
    intro w hw
    obtain ⟨y, hyU, hyJ, rfl⟩ := exists_modMk_of_mem_subM hUN (hV₁I.trans le_sup_left) hw
    obtain ⟨a, ha, b, hb, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_le_normalizer hIIc).mp hyJ
    rw [modMk_mul hUN (hIU ha) (hIc hb)]
    exact Subgroup.mul_mem_sup ((modMk_mem_subM_iff hUN hV₁I _).mpr ha)
      ((modMk_mem_subM_iff hUN hV₁c _).mpr hb)
  intro w hw hwB x _
  have hwB' : ∀ b ∈ autIH V₁ Vp H B₀, b w = w := by
    intro b hb
    rw [autIH_eq_map hF hB₀H] at hb
    obtain ⟨y, hy, rfl⟩ := hb
    have hy' : (y : G) ∈ B₀ := Subgroup.mem_subgroupOf.mp hy
    have h2 := hwB ⟨(y : G), hB₀K hy'⟩ (Subgroup.mem_subgroupOf.mpr hy')
    rw [Subgroup.mem_bot, mul_inv_eq_one] at h2
    exact h2
  have hwK := fix_of_sum_of_inf hBMK (hstab hV₁I hIU hKI) (hstab hV₁c hIc hKIc) hnoI hnoIc hA
    w (hJM hw) hwB'
  have hxK : actH hHV₁ hHU ⟨(x : G), hKH x.2⟩ ∈ autIH V₁ Vp H K := by
    rw [autIH_eq_map hF hKH]
    exact ⟨⟨(x : G), hKH x.2⟩, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
  have h2 : actH hHV₁ hHU ⟨(x : G), hKH x.2⟩ w = w := hwK _ hxK
  rw [Subgroup.mem_bot, mul_inv_eq_one]
  exact h2

theorem false_of_fixProp {T V L V₁ Vp H K I : Subgroup G} (hF : HypF918 T V L V₁ Vp H K)
    (hK₀ : conjClosure K T = K) (hIU : I ≤ conjClosure Vp H)
    (hirr : IsIrrPlusTilde V₁ (conjClosure K T) I)
    [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure Vp H)))] {B₀ : Subgroup G}
    (hB₀ : ∀ b ∈ B₀, ∀ u ∈ Vp, b * u * b⁻¹ * u⁻¹ ∈ V₁)
    (hfix : S1565.FixProp ((actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H)).comp
        (Subgroup.inclusion (le_of_mem_cComp hF.K_cComp))) (B₀.subgroupOf K) ⊥ ⊤) : False := by
  classical
  have h1 := hF.toHypF98.toHypF91
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hHV₁ : H ≤ Subgroup.normalizer (V₁ : Set G) := hF.H_le_normalizer_V₁
  have hUH : conjClosure Vp H ≤ H := h1.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)
  have hKn : ∀ h ∈ H, h ∈ Subgroup.normalizer (K : Set G) := fun h hh => by
    have := hF.K₀_normal hh
    rwa [hK₀] at this
  have hHU : H ≤ Subgroup.normalizer ((conjClosure Vp H : Subgroup G) : Set G) :=
    le_normalizer_conjClosure Vp H
  have hUN : conjClosure Vp H ≤ Subgroup.normalizer (V₁ : Set G) :=
    hF.conjClosure_le_normalizer_V₁ (le_conjClosure Vp H)
  have hPconj : ∀ g ∈ Subgroup.normalizer (V₁ : Set G), g ∈ Subgroup.normalizer (K : Set G) →
      ∀ z : G, (∀ x ∈ K, x * z * x⁻¹ * z⁻¹ ∈ V₁) →
        ∀ x ∈ K, x * (g * z * g⁻¹) * x⁻¹ * (g * z * g⁻¹)⁻¹ ∈ V₁ := by
    intro g hgV hgK z hz x hx
    have hx' : g⁻¹ * x * g ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgK) x).mp hx
      simpa using this
    have h2 := (Subgroup.mem_normalizer_iff.mp hgV _).mp (hz _ hx')
    have e : g * (g⁻¹ * x * g * z * (g⁻¹ * x * g)⁻¹ * z⁻¹) * g⁻¹ =
        x * (g * z * g⁻¹) * x⁻¹ * (g * z * g⁻¹)⁻¹ := by group
    rwa [e] at h2
  have hPC : ∀ y ∈ I, (∀ x ∈ K, x * y * x⁻¹ * y⁻¹ ∈ V₁) →
      y ∈ centralizerMod V₁ I (conjClosure K T) := by
    intro y hy h
    rw [hK₀]
    refine ⟨hy, hHV₁ (hUH (hIU hy)), fun x hx => ?_⟩
    have h2 := V₁.inv_mem (h x hx)
    have e : (x * y * x⁻¹ * y⁻¹)⁻¹ = y * x * y⁻¹ * x⁻¹ := by group
    rwa [e] at h2
  have hV3 : ∀ u ∈ Vp, ∀ x ∈ K, x * u * x⁻¹ * u⁻¹ ∈ V₁ := by
    intro u hu x hx
    have huU := le_conjClosure Vp H hu
    have hB : S1565.FixMod ((actH hHV₁ hHU).comp (Subgroup.inclusion hKH)) (B₀.subgroupOf K) ⊥
        (modMk hUN u huU) := by
      intro s hs
      have hsB : (s : G) ∈ B₀ := Subgroup.mem_subgroupOf.mp hs
      have hsu : (s : G) * u * (s : G)⁻¹ ∈ conjClosure Vp H :=
        (Subgroup.mem_normalizer_iff.mp (hHU (hKH s.2)) u).mp huU
      rw [Subgroup.mem_bot, mul_inv_eq_one]
      change actH hHV₁ hHU ⟨(s : G), hKH s.2⟩ (modMk hUN u huU) = modMk hUN u huU
      rw [actH_modMk hHV₁ hUN hHU _ huU]
      exact (A6Tv.modMk_conj_eq_iff' hUN huU hsu).mpr (hB₀ _ hsB u hu)
    have hw := hfix _ (Subgroup.mem_top _) hB ⟨x, hx⟩ (Subgroup.mem_top _)
    rw [Subgroup.mem_bot, mul_inv_eq_one] at hw
    have hxu : x * u * x⁻¹ ∈ conjClosure Vp H :=
      (Subgroup.mem_normalizer_iff.mp (hHU (hKH hx)) u).mp huU
    change actH hHV₁ hHU ⟨x, hKH hx⟩ (modMk hUN u huU) = modMk hUN u huU at hw
    rw [actH_modMk hHV₁ hUN hHU ⟨x, hKH hx⟩ huU] at hw
    exact (A6Tv.modMk_conj_eq_iff' hUN huU hxu).mp hw
  have hZ : conjClosure Vp H ≤ centralizerMod V₁ (conjClosure Vp H) K := by
    refine conjClosure_le fun h hh u hu => ?_
    have hhu : h * u * h⁻¹ ∈ conjClosure Vp H :=
      (Subgroup.mem_normalizer_iff.mp (hHU hh) u).mp (le_conjClosure Vp H hu)
    refine ⟨hhu, hUN hhu, fun x hx => ?_⟩
    have h2 := V₁.inv_mem (hPconj h (hHV₁ hh) (hKn h hh) u (hV3 u hu) x hx)
    have e : (x * (h * u * h⁻¹) * x⁻¹ * (h * u * h⁻¹)⁻¹)⁻¹ =
        h * u * h⁻¹ * x * (h * u * h⁻¹)⁻¹ * x⁻¹ := by group
    rwa [e] at h2
  have hIC : I ≤ centralizerMod V₁ I (conjClosure K T) := by
    intro i hi
    refine hPC i hi fun x hx => ?_
    have h2 := V₁.inv_mem ((hZ (hIU hi)).2.2 x hx)
    have e : (i * x * i⁻¹ * x⁻¹)⁻¹ = x * i * x⁻¹ * i⁻¹ := by group
    rwa [e] at h2
  exact (not_le_of_gt hirr.2.2.1) hIC

theorem false_of_natural {T V L V₁ Vp H K I : Subgroup G} (hF : HypF918 T V L V₁ Vp H K)
    (hK₀ : conjClosure K T = K) (hS' : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K)) {n : ℕ}
    (hn : 2 ≤ n) {F : Type} [Field F] [Finite F] (hFn : Nat.card F = 2 ^ n)
    (eK : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H) (hirr : IsIrrPlusTilde V₁ (conjClosure K T) I)
    [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))] {m : ℕ}
    (hnat : BinaryNaturalSL (autSec (autSub (autIH V₁ I H K) (subM V₁ (conjClosure I H) I)) ⊤
        ((subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T))).subgroupOf
          (subM V₁ (conjClosure I H) I))) ⊤ ⊥ 2 m)
    {c : G} (hcH : c ∈ H) (hII : I ⊓ conjSub c I ≤ centralizerMod V₁ I K)
    (hUJ : ⁅conjClosure Vp H, K⁆ ≤ I ⊔ conjSub c I) {T₀ : Subgroup G}
    (hsyl : IsSylowTwoOf T₀ K)
    (hB₀ : ∀ b ∈ K ⊓ Subgroup.normalizer (T₀ : Set G), ∀ u ∈ Vp, b * u * b⁻¹ * u⁻¹ ∈ V₁) :
    False := by
  classical
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hHV₁ : H ≤ Subgroup.normalizer (V₁ : Set G) := hF.H_le_normalizer_V₁
  have hKn : ∀ h ∈ H, h ∈ Subgroup.normalizer (K : Set G) := fun h hh => by
    have := hF.K₀_normal hh
    rwa [hK₀] at this
  have hcK := hKn c hcH
  have hHU : H ≤ Subgroup.normalizer ((conjClosure Vp H : Subgroup G) : Set G) :=
    le_normalizer_conjClosure Vp H
  have hcKc : ∀ x ∈ K, c⁻¹ * x * c ∈ K := fun x hx => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hcK) x).mp hx
    simpa using this
  have hmk : ∀ x : ↥K, (QuotientGroup.mk x : ↥K ⧸ CFSG.pCore 2 ↥K) = 1 ↔
      (x : G) ∈ pCoreOf 2 K := by
    intro x
    rw [QuotientGroup.eq_one_iff]
    constructor
    · intro hx
      exact ⟨x, by assumption, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have hyx' : y = x := Subtype.ext hyx
      rw [← hyx']
      exact hy
  obtain ⟨k, hkN, hk2⟩ := exists_borel_sq_ne_one hsyl hn hFn eK
  have hkB : (k : G) ∈ K ⊓ Subgroup.normalizer (T₀ : Set G) := ⟨k.2, hkN⟩
  obtain ⟨k', hk'⟩ : ∃ k' : ↥K, (k' : G) = c⁻¹ * k * c := ⟨⟨_, hcKc _ k.2⟩, rfl⟩
  have hk'2 : (QuotientGroup.mk k' : ↥K ⧸ CFSG.pCore 2 ↥K) ^ 2 ≠ 1 := by
    intro h
    apply hk2
    rw [← QuotientGroup.mk_pow] at h ⊢
    rw [hmk] at h ⊢
    have hcO : c ∈ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
      normalizer_le_normalizer_pCoreOf 2 K hcK
    have h3 := (Subgroup.mem_normalizer_iff.mp hcO _).mp h
    have e : c * ((k' ^ 2 : ↥K) : G) * c⁻¹ = ((k ^ 2 : ↥K) : G) := by
      rw [Subgroup.coe_pow, Subgroup.coe_pow, hk', sq, sq]
      group
    rwa [e] at h3
  have hkI : ∀ i ∈ I, (k : G) * i * (k : G)⁻¹ * i⁻¹ ∈ centralizerMod V₁ I (conjClosure K T) →
      i ∈ centralizerMod V₁ I (conjClosure K T) := fun i hi hki =>
    mem_of_natural hF hK₀ hS' hV₁I hIU hirr hnat hk2 hi hki
  have hk'I : ∀ i ∈ I, c⁻¹ * (k : G) * c * i * (c⁻¹ * (k : G) * c)⁻¹ * i⁻¹ ∈
      centralizerMod V₁ I (conjClosure K T) → i ∈ centralizerMod V₁ I (conjClosure K T) := by
    intro i hi hki
    rw [← hk'] at hki
    exact mem_of_natural hF hK₀ hS' hV₁I hIU hirr hnat hk'2 hi hki
  have hFU : Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure Vp H))) :=
    factElem hF (le_conjClosure Vp H)
  have hUN : conjClosure Vp H ≤ Subgroup.normalizer (V₁ : Set G) :=
    hF.conjClosure_le_normalizer_V₁ (le_conjClosure Vp H)
  have hfix1 := fixProp_sup_of_fpf hF hK₀ hV₁I hIU hirr hcH hII inf_le_left hkB hkI hk'I
  have hfix2 : S1565.FixProp ((actH hHV₁ hHU).comp (Subgroup.inclusion hKH))
      ((K ⊓ Subgroup.normalizer (T₀ : Set G)).subgroupOf K)
      (subM V₁ (conjClosure Vp H) (I ⊔ conjSub c I)) ⊤ := by
    intro w _ _ x _
    obtain ⟨u, huU, -, rfl⟩ := exists_modMk_of_mem_subM hUN (hV₁I.trans hIU)
      (Subgroup.mem_subgroupOf.mpr w.2)
    have hxu : (x : G) * u * (x : G)⁻¹ ∈ conjClosure Vp H :=
      (Subgroup.mem_normalizer_iff.mp (hHU (hKH x.2)) u).mp huU
    change actH hHV₁ hHU ⟨(x : G), hKH x.2⟩ (modMk hUN u huU) * (modMk hUN u huU)⁻¹ ∈ _
    rw [actH_modMk hHV₁ hUN hHU _ huU, ← modMk_inv hUN huU,
      ← modMk_mul hUN hxu ((conjClosure Vp H).inv_mem huU),
      modMk_mem_subM_iff hUN (hV₁I.trans le_sup_left)]
    apply hUJ
    have h2 : u * (x : G) * u⁻¹ * (x : G)⁻¹ ∈ ⁅conjClosure Vp H, K⁆ :=
      Subgroup.commutator_mem_commutator huU x.2
    have h3 := Subgroup.inv_mem _ h2
    have e : (u * (x : G) * u⁻¹ * (x : G)⁻¹)⁻¹ = (x : G) * u * (x : G)⁻¹ * u⁻¹ := by group
    rwa [e] at h3
  have hW2 : ∀ w : ↥(tildeOf V₁ (conjClosure Vp H)), w ^ 2 = 1 := fun w => by
    apply Subtype.ext
    exact hFU.out.2 (w : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) w.2
  have hodd := odd_index_of_sylow hsyl (le_inf hsyl.1 Subgroup.le_normalizer)
  have hbot : S1565.InvSub ((actH hHV₁ hHU).comp (Subgroup.inclusion hKH))
      (⊥ : Subgroup ↥(tildeOf V₁ (conjClosure Vp H))) := fun x a ha => by
    rw [Subgroup.mem_bot] at ha ⊢
    rw [ha, map_one]
  have hfix := S1565.fixProp_compose _ hW2 _ hodd hbot bot_le hfix1 hfix2
  exact false_of_fixProp hF hK₀ hIU hirr hB₀ hfix

end CFSG.Quasithin.H13.A6.A6S20
