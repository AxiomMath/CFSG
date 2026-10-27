module

public import CFSG.LocalAnalysis.StandardType.FS81.Defs
import CFSG.LocalAnalysis.StandardType.FS81.S7Coprime
import CFSG.GroupTheory.CommutingProductFixedSubgroup
import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly

private theorem centralizer_map_conj {G : Type} [Group G] (b x : G) :
    (Subgroup.centralizer ({b} : Set G)).map (MulAut.conj x).toMonoidHom =
      Subgroup.centralizer ({(MulAut.conj x) b} : Set G) := by
  refine le_antisymm ?_ ?_
  · simpa [MulAut.conj_apply] using Subgroup.map_centralizer_le_centralizer_image
      ({b} : Set G) (MulAut.conj x).toMonoidHom
  · intro z hz
    rw [Subgroup.mem_map_equiv]
    rw [Subgroup.mem_centralizer_iff] at hz ⊢
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst h
    have h2 := hz ((MulAut.conj x) b) (by simp)
    rw [MulAut.conj_apply] at h2
    rw [MulAut.conj_symm_apply]
    have key : b * (x⁻¹ * z * x) = (x⁻¹ * z * x) * b := by
      calc b * (x⁻¹ * z * x) = x⁻¹ * ((x * b * x⁻¹) * z) * x := by group
        _ = x⁻¹ * (z * (x * b * x⁻¹)) * x := by rw [h2]
        _ = (x⁻¹ * z * x) * b := by group
    simpa using key

private theorem map_conj_eq_self_of_mem {G : Type} [Group G] {Y : Subgroup G} {y : G}
    (hy : y ∈ Y) : Y.map (MulAut.conj y).toMonoidHom = Y :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hy)

private theorem map_conj_inv_eq_self_of_mem {G : Type} [Group G] {Y : Subgroup G} {y : G}
    (hy : y ∈ Y) : Y.map (MulAut.conj y⁻¹).toMonoidHom = Y :=
  map_conj_eq_self_of_mem (Y := Y) (Y.inv_mem hy)

private theorem centralizer_map_conj_inv_of_eq {G : Type} [Group G] {b₀ b y : G}
    (hb : b = y * b₀ * y⁻¹) :
    (Subgroup.centralizer ({b} : Set G)).map (MulAut.conj y⁻¹).toMonoidHom =
      Subgroup.centralizer ({b₀} : Set G) := by
  rw [centralizer_map_conj b y⁻¹]
  have h : (MulAut.conj y⁻¹) b = b₀ := by
    rw [hb, MulAut.conj_apply]
    group
  rw [h]

private theorem hO2_conj {G : Type} [Group G] {Y : Subgroup G} {b₀ b y : G}
    (hy : y ∈ Y) (hb : b = y * b₀ * y⁻¹)
    (hO2 : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ Subgroup.centralizer ({b₀} : Set G) ⊓ Y →
      Subgroup.centralizer ({b₀} : Set G) ⊓ Y ≤ Subgroup.normalizer (P : Set G) → P = ⊥) :
    ∀ P : Subgroup G, IsPGroup 2 P → P ≤ Subgroup.centralizer ({b} : Set G) ⊓ Y →
      Subgroup.centralizer ({b} : Set G) ⊓ Y ≤ Subgroup.normalizer (P : Set G) → P = ⊥ := by
  intro P hP hPC hPN
  let φ : G →* G := (MulAut.conj y⁻¹).toMonoidHom
  have hCmap : (Subgroup.centralizer ({b} : Set G)).map φ =
      Subgroup.centralizer ({b₀} : Set G) := centralizer_map_conj_inv_of_eq hb
  have hYmap : Y.map φ = Y := map_conj_inv_eq_self_of_mem hy
  have hQp : IsPGroup 2 (P.map φ) := hP.map φ
  have hQle : P.map φ ≤ Subgroup.centralizer ({b₀} : Set G) ⊓ Y := by
    rw [← hCmap, ← hYmap, ← Subgroup.map_inf _ _ _ (MulAut.conj y⁻¹).injective]
    exact Subgroup.map_mono hPC
  have hQnorm : Subgroup.centralizer ({b₀} : Set G) ⊓ Y ≤
      Subgroup.normalizer ((P.map φ : Subgroup G) : Set G) := by
    rw [← hCmap, ← hYmap, ← Subgroup.map_inf _ _ _ (MulAut.conj y⁻¹).injective]
    exact (Subgroup.map_mono (f := φ) hPN).trans (Subgroup.le_normalizer_map φ)
  have hQbot : P.map φ = ⊥ := hO2 (P.map φ) hQp hQle hQnorm
  have hcomp : (MulAut.conj y).toMonoidHom.comp φ = MonoidHom.id G := by
    ext x
    change (MulAut.conj y) ((MulAut.conj y⁻¹) x) = x
    rw [MulAut.conj_apply, MulAut.conj_apply]
    group
  calc P = P.map (MonoidHom.id G) := (Subgroup.map_id P).symm
    _ = P.map ((MulAut.conj y).toMonoidHom.comp φ) := by rw [hcomp]
    _ = (P.map φ).map (MulAut.conj y).toMonoidHom := by rw [Subgroup.map_map]
    _ = ⊥ := by rw [hQbot, Subgroup.map_bot]



private theorem map_conj_eq_self_of_le_centralizer {G : Type} [Group G]
    {R Y : Subgroup G} {y : G} (hRY : R ≤ Subgroup.centralizer (Y : Set G)) (hy : y ∈ Y) :
    R.map (MulAut.conj y).toMonoidHom = R := by
  have hcomm : ∀ r ∈ R, y * r * y⁻¹ = r := by
    intro r hr
    have h := Subgroup.mem_centralizer_iff.mp (hRY hr) y hy
    calc y * r * y⁻¹ = (r * y) * y⁻¹ := by rw [h]
      _ = r := by group
  refine le_antisymm ?_ ?_
  · rintro _ ⟨r, hr, rfl⟩
    change y * r * y⁻¹ ∈ R
    rw [hcomm r hr]
    exact hr
  · intro r hr
    exact Subgroup.mem_map.mpr ⟨r, hr, hcomm r hr⟩

private theorem map_conj_inf_centralizer {G : Type} [Group G] {Y : Subgroup G} {b₀ b y : G}
    (hy : y ∈ Y) (hb : b = y * b₀ * y⁻¹) :
    ((Subgroup.centralizer ({b₀} : Set G) ⊓ Y).map (MulAut.conj y).toMonoidHom) =
      Subgroup.centralizer ({b} : Set G) ⊓ Y := by
  rw [Subgroup.map_inf _ _ _ (MulAut.conj y).injective]
  have h1 : (Subgroup.centralizer ({b₀} : Set G)).map (MulAut.conj y).toMonoidHom =
      Subgroup.centralizer ({b} : Set G) := by
    rw [centralizer_map_conj b₀ y]
    have h : (MulAut.conj y) b₀ = b := by
      rw [hb]
      rfl
    rw [h]
  have h2 : Y.map (MulAut.conj y).toMonoidHom = Y := map_conj_eq_self_of_mem hy
  rw [h1, h2]

theorem centralizer_eq_sup_of_conj {G : Type} [Group G] {Y R : Subgroup G} {b₀ b y : G}
    (hy : y ∈ Y) (hb : b = y * b₀ * y⁻¹)
    (hRY : R ≤ Subgroup.centralizer (Y : Set G))
    (hC : Subgroup.centralizer ({b₀} : Set G) = R ⊔ (Subgroup.centralizer ({b₀} : Set G) ⊓ Y)) :
    Subgroup.centralizer ({b} : Set G) = R ⊔ (Subgroup.centralizer ({b} : Set G) ⊓ Y) := by
  have hCbmap : (Subgroup.centralizer ({b₀} : Set G)).map (MulAut.conj y).toMonoidHom =
      Subgroup.centralizer ({b} : Set G) := by
    rw [centralizer_map_conj b₀ y]
    have h : (MulAut.conj y) b₀ = b := by
      rw [hb]
      rfl
    rw [h]
  calc Subgroup.centralizer ({b} : Set G)
      = (Subgroup.centralizer ({b₀} : Set G)).map (MulAut.conj y).toMonoidHom := hCbmap.symm
    _ = (R ⊔ (Subgroup.centralizer ({b₀} : Set G) ⊓ Y)).map (MulAut.conj y).toMonoidHom := by
        conv_lhs => rw [hC]
    _ = R.map (MulAut.conj y).toMonoidHom ⊔
          (Subgroup.centralizer ({b₀} : Set G) ⊓ Y).map (MulAut.conj y).toMonoidHom :=
        Subgroup.map_sup _ _ _
    _ = R ⊔ (Subgroup.centralizer ({b} : Set G) ⊓ Y) := by
        rw [map_conj_eq_self_of_le_centralizer hRY hy, map_conj_inf_centralizer hy hb]



private theorem centralizer_le_normalizer_centralizer {G : Type} [Group G] (b : G) :
    Subgroup.centralizer ({b} : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer ({b} : Set G) : Set G) := by
  intro d hd
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change (Subgroup.centralizer ({b} : Set G)).map (MulAut.conj d).toMonoidHom =
    Subgroup.centralizer ({b} : Set G)
  rw [centralizer_map_conj b d]
  have hdb : d * b * d⁻¹ = b := by
    have h := Subgroup.mem_centralizer_iff.mp hd b (by simp)
    calc d * b * d⁻¹ = (b * d) * d⁻¹ := by rw [h]
      _ = b := by group
  have hdb' : (MulAut.conj d) b = b := by
    rw [MulAut.conj_apply]
    exact hdb
  rw [hdb']



theorem inf_centralizer_le_R {G : Type} [Group G] {Y R : Subgroup G} {b : G}
    (hRY : R ≤ Subgroup.centralizer (Y : Set G))
    (hZ : Subgroup.centralizer (Y : Set G) ⊓ Y = ⊥)
    (hC : Subgroup.centralizer ({b} : Set G) =
      R ⊔ (Subgroup.centralizer ({b} : Set G) ⊓ Y))
    (hO2 : ∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ Subgroup.centralizer ({b} : Set G) ⊓ Y →
      Subgroup.centralizer ({b} : Set G) ⊓ Y ≤ Subgroup.normalizer (Q : Set G) → Q = ⊥)
    (P : Subgroup G) (hP2 : IsPGroup 2 P)
    (hPN : Y ≤ Subgroup.normalizer (P : Set G)) :
    P ⊓ Subgroup.centralizer ({b} : Set G) ≤ R := by
  have hRleCb : R ≤ Subgroup.centralizer ({b} : Set G) := by
    rw [hC]
    exact le_sup_left
  have hcomm : ∀ r ∈ R, ∀ c ∈ (Subgroup.centralizer ({b} : Set G) ⊓ Y), r * c = c * r := by
    intro r hr c hc
    exact (Subgroup.mem_centralizer_iff.mp (hRY hr) c hc.2).symm
  have hRYinf : R ⊓ Y = ⊥ := by
    have hle : R ⊓ Y ≤ Subgroup.centralizer (Y : Set G) ⊓ Y :=
      le_inf (inf_le_left.trans hRY) inf_le_right
    rw [hZ] at hle
    exact le_bot_iff.mp hle
  let CY : Subgroup G := Subgroup.centralizer ({b} : Set G) ⊓ Y
  let P' : Subgroup G :=
    { carrier := {c | c ∈ CY ∧ ∃ r ∈ R, r * c ∈ P ⊓ Subgroup.centralizer ({b} : Set G)}
      one_mem' := ⟨CY.one_mem, 1, R.one_mem, by simp⟩
      mul_mem' := by
        rintro c₁ c₂ ⟨hc₁Y, r₁, hr₁, hx₁⟩ ⟨hc₂Y, r₂, hr₂, hx₂⟩
        refine ⟨CY.mul_mem hc₁Y hc₂Y, r₁ * r₂, R.mul_mem hr₁ hr₂, ?_⟩
        have hcr : c₁ * r₂ = r₂ * c₁ := (hcomm r₂ hr₂ c₁ hc₁Y).symm
        have hrw : r₁ * r₂ * (c₁ * c₂) = (r₁ * c₁) * (r₂ * c₂) := by
          calc r₁ * r₂ * (c₁ * c₂) = r₁ * (r₂ * c₁) * c₂ := by group
            _ = r₁ * (c₁ * r₂) * c₂ := by rw [← hcr]
            _ = (r₁ * c₁) * (r₂ * c₂) := by group
        rw [hrw]
        exact (P ⊓ Subgroup.centralizer ({b} : Set G)).mul_mem hx₁ hx₂
      inv_mem' := by
        rintro c ⟨hcY, r, hr, hx⟩
        refine ⟨CY.inv_mem hcY, r⁻¹, R.inv_mem hr, ?_⟩
        have hcr : Commute r c := hcomm r hr c hcY
        rw [← hcr.inv]
        exact (P ⊓ Subgroup.centralizer ({b} : Set G)).inv_mem hx }
  have hP'le : P' ≤ CY := fun c hc => hc.1
  have hP'2 : IsPGroup 2 P' := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro c
    obtain ⟨hcY, r, hr, hx⟩ := c.2
    obtain ⟨n, hn⟩ := hP2.exists_pow_pow_eq_one ⟨r * (c : G), hx.1⟩
    refine ⟨n, ?_⟩
    have hxpow : (r * (c : G)) ^ 2 ^ n = 1 := by
      simpa using congrArg Subtype.val hn
    have hcr : Commute r (c : G) := hcomm r hr c hcY
    have hpow : r ^ 2 ^ n * (c : G) ^ 2 ^ n = 1 := by
      rw [← hcr.mul_pow, hxpow]
    have hcR : (c : G) ^ 2 ^ n ∈ R := by
      rw [eq_inv_of_mul_eq_one_right hpow]
      exact R.inv_mem (R.pow_mem hr _)
    have hcYpow : (c : G) ^ 2 ^ n ∈ Y := Y.pow_mem hcY.2 _
    have hbot : (c : G) ^ 2 ^ n ∈ R ⊓ Y := ⟨hcR, hcYpow⟩
    rw [hRYinf] at hbot
    apply Subtype.ext
    exact Subgroup.mem_bot.mp hbot
  have hnorm' : CY ≤ Subgroup.normalizer (P' : Set G) := by
    have hforward : ∀ d ∈ CY, ∀ c ∈ P', d * c * d⁻¹ ∈ P' := by
      intro d hd c hc
      obtain ⟨hcY, r, hr, hx⟩ := hc
      refine ⟨CY.mul_mem (CY.mul_mem hd hcY) (CY.inv_mem hd), r, hr, ?_⟩
      have hdP : d * (r * c) * d⁻¹ ∈ P := by
        exact (Subgroup.mem_normalizer_iff.mp (hPN hd.2) (r * c)).mp hx.1
      have hdCb : d * (r * c) * d⁻¹ ∈ Subgroup.centralizer ({b} : Set G) := by
        exact (Subgroup.mem_normalizer_iff.mp
          (centralizer_le_normalizer_centralizer b hd.1) (r * c)).mp hx.2
      have hrw : r * (d * c * d⁻¹) = d * (r * c) * d⁻¹ := by
        calc r * (d * c * d⁻¹) = (r * d) * c * d⁻¹ := by group
          _ = (d * r) * c * d⁻¹ := by rw [hcomm r hr d hd]
          _ = d * (r * c) * d⁻¹ := by group
      rw [hrw]
      exact ⟨hdP, hdCb⟩
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      exact hforward d hd c hc
    · intro hc
      have hd' : d⁻¹ ∈ CY := CY.inv_mem hd
      have h := hforward d⁻¹ hd' (d * c * d⁻¹) hc
      have hc' : c ∈ P' := by
        simpa [show d⁻¹ * (d * c * d⁻¹) * d = c from by group] using h
      exact hc' 
  have hP'bot : P' = ⊥ := hO2 P' hP'2 hP'le hnorm'
  intro x hx
  have hxsup : x ∈ R ⊔ CY := by
    rw [← hC]
    exact hx.2
  obtain ⟨a, ha, c, hcY, hxc⟩ :=
    CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute (A := R) (B := CY) hcomm hxsup
  have hcP' : c ∈ P' := by
    refine ⟨hcY, a, ha, ?_⟩
    rw [hxc]
    exact hx
  have hc1 : c = 1 := by
    have : c ∈ (⊥ : Subgroup G) := hP'bot ▸ hcP'
    exact Subgroup.mem_bot.mp this
  rw [← hxc, hc1, mul_one]
  exact ha




private theorem s79_R_odd {G : Type} [Group G] [Finite G] {Y R A L : Subgroup G} {b₀ : G}
    (hZ : Subgroup.centralizer (Y : Set G) ⊓ Y = ⊥)
    (hC : Subgroup.centralizer ({b₀} : Set G) = R ⊔ (Subgroup.centralizer ({b₀} : Set G) ⊓ Y))
    (hRY : R ≤ Subgroup.centralizer (Y : Set G))
    (hO2 : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ Subgroup.centralizer ({b₀} : Set G) ⊓ Y →
      Subgroup.centralizer ({b₀} : Set G) ⊓ Y ≤ Subgroup.normalizer (P : Set G) → P = ⊥)
    (hLY : L ≤ Y) (hAL : A ≤ L)
    (hA : IsElemAbelian 3 A) (hAcard : Nat.card A = 27)
    (hAF : ∀ F : Subgroup G, F ≤ A → Nat.card F = 9 → ∃ y ∈ Y, y * b₀ * y⁻¹ ∈ F)
    (hF : ∀ t : G, orderOf t = 2 → t ∈ R →
      Subgroup.centralizer ({t} : Set G) ⊓
          Subgroup.centralizer (pCoreOf 2 (Subgroup.centralizer ({t} : Set G)) : Set G) ≤
        pCoreOf 2 (Subgroup.centralizer ({t} : Set G))) :
    ¬ 2 ∣ Nat.card R := by
  intro h2R
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥R) 2 h2R
  have htG : orderOf (t : G) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact ht
  have htR : (t : G) ∈ R := t.2
  let P : Subgroup G := pCoreOf 2 (Subgroup.centralizer ({(t : G)} : Set G))
  have hP2 : IsPGroup 2 P :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (Subgroup.centralizer ({(t : G)} : Set G)))
  have hYt : Y ≤ Subgroup.centralizer ({(t : G)} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst h
    exact (Subgroup.mem_centralizer_iff.mp (hRY htR) y hy).symm
  have hPN : Y ≤ Subgroup.normalizer (P : Set G) :=
    hYt.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2)
      (Subgroup.centralizer ({(t : G)} : Set G)))
  have h3P : ¬ 3 ∣ Nat.card P := by
    intro h3
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP2
    rw [hn] at h3
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    norm_num at h32
  have hAQ : A ≤ Subgroup.normalizer (P : Set G) :=
    hAL.trans (hLY.trans hPN)
  have hgen := iSup_inf_centralizer_eq_of_card_27 (A := A) (Q := P) hA hAcard hAQ h3P
  have hiSup_le : (⨆ (F : Subgroup G) (_ : F ≤ A) (_ : Nat.card F = 9),
      P ⊓ Subgroup.centralizer (F : Set G)) ≤ R := by
    refine iSup_le fun F => iSup_le fun hFA => iSup_le fun hFcard => ?_
    obtain ⟨y, hy, hby⟩ := hAF F hFA hFcard
    have hCb : Subgroup.centralizer ({y * b₀ * y⁻¹} : Set G) =
        R ⊔ (Subgroup.centralizer ({y * b₀ * y⁻¹} : Set G) ⊓ Y) :=
      centralizer_eq_sup_of_conj hy rfl hRY hC
    have hO2b := hO2_conj (Y := Y) hy rfl hO2
    have hproj := inf_centralizer_le_R (Y := Y) (R := R) (b := y * b₀ * y⁻¹)
      hRY hZ hCb hO2b P hP2 hPN
    refine (inf_le_inf_left P (Subgroup.centralizer_le ?_)).trans hproj
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rwa [hz]
  have hPleR : P ≤ R := by
    rw [← hgen]
    exact hiSup_le
  have hYleP : Y ≤ P := by
    have hYC : Y ≤ Subgroup.centralizer ({(t : G)} : Set G) ⊓
        Subgroup.centralizer (P : Set G) := by
      refine le_inf hYt ?_
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      exact (Subgroup.mem_centralizer_iff.mp (hRY (hPleR hp)) y hy).symm
    exact hYC.trans (hF (t : G) htG htR)
  have hY2 : IsPGroup 2 Y := hP2.to_le hYleP
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hY2
  have h3Y : 3 ∣ Nat.card Y := by
    have h3A : 3 ∣ Nat.card A := by rw [hAcard]; norm_num
    exact h3A.trans (Subgroup.card_dvd_of_le (hAL.trans hLY))
  rw [hn] at h3Y
  have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3Y
  norm_num at h32




private theorem eq_one_of_mem_R_of_two_element {G : Type} [Group G] {R : Subgroup G}
    (hodd : ¬ 2 ∣ Nat.card R) {a : G} (ha : a ∈ R) (h2a : ∃ n, a ^ 2 ^ n = 1) : a = 1 := by
  obtain ⟨n, hn⟩ := h2a
  have hn' : a ^ 2 ^ (n + 1) = 1 := by
    rw [Nat.pow_succ, pow_mul, hn, one_pow]
  have hdvd : orderOf a ∣ 2 ^ (n + 1) := orderOf_dvd_of_pow_eq_one hn'
  have hcard : orderOf a ∣ Nat.card R := R.orderOf_dvd_natCard ha
  have hcop2 : Nat.Coprime 2 (Nat.card R) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd
  have hcop : Nat.Coprime (2 ^ (n + 1)) (Nat.card R) :=
    (Nat.coprime_pow_left_iff (Nat.succ_pos n) 2 (Nat.card R)).mpr hcop2
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvd hcard)

theorem inf_centralizer_le_Y {G : Type} [Group G] {Y R : Subgroup G} {b : G}
    (hRY : R ≤ Subgroup.centralizer (Y : Set G))
    (hZ : Subgroup.centralizer (Y : Set G) ⊓ Y = ⊥)
    (hC : Subgroup.centralizer ({b} : Set G) =
      R ⊔ (Subgroup.centralizer ({b} : Set G) ⊓ Y))
    (hodd : ¬ 2 ∣ Nat.card R)
    (P : Subgroup G) (hP2 : IsPGroup 2 P) :
    P ⊓ Subgroup.centralizer ({b} : Set G) ≤ Y := by
  have hRYinf : R ⊓ Y = ⊥ := by
    have hle : R ⊓ Y ≤ Subgroup.centralizer (Y : Set G) ⊓ Y :=
      le_inf (inf_le_left.trans hRY) inf_le_right
    rw [hZ] at hle
    exact le_bot_iff.mp hle
  have hcomm : ∀ r ∈ R, ∀ c ∈ (Subgroup.centralizer ({b} : Set G) ⊓ Y), r * c = c * r := by
    intro r hr c hc
    exact (Subgroup.mem_centralizer_iff.mp (hRY hr) c hc.2).symm
  let CY : Subgroup G := Subgroup.centralizer ({b} : Set G) ⊓ Y
  intro x hx
  have hxsup : x ∈ R ⊔ CY := by
    rw [← hC]
    exact hx.2
  obtain ⟨a, ha, c, hcY, hxa⟩ :=
    CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute (A := R) (B := CY) hcomm hxsup
  obtain ⟨n, hn⟩ := hP2.exists_pow_pow_eq_one ⟨x, hx.1⟩
  have hxpow : x ^ 2 ^ n = 1 := by
    simpa using congrArg Subtype.val hn
  have hac : Commute a c := hcomm a ha c hcY
  have hxc : Commute x c := hxa ▸ hac.mul_left (Commute.refl c)
  have hcpow : c ^ 2 ^ n = 1 := by
    have hpow : a ^ 2 ^ n * c ^ 2 ^ n = 1 := by
      rw [← hac.mul_pow, hxa, hxpow]
    have hcR : c ^ 2 ^ n ∈ R := by
      rw [eq_inv_of_mul_eq_one_right hpow]
      exact R.inv_mem (R.pow_mem ha _)
    have hcYpow : c ^ 2 ^ n ∈ Y := Y.pow_mem hcY.2 _
    have hbot : c ^ 2 ^ n ∈ R ⊓ Y := ⟨hcR, hcYpow⟩
    rw [hRYinf] at hbot
    exact Subgroup.mem_bot.mp hbot
  have haeq : a = x * c⁻¹ := by
    rw [← hxa]
    group
  have hcinvpow : c⁻¹ ^ 2 ^ n = 1 := by
    rw [inv_pow, hcpow, inv_one]
  have hapow : a ^ 2 ^ n = 1 := by
    rw [haeq, hxc.inv_right.mul_pow, hxpow, hcinvpow, mul_one]
  have ha1 : a = 1 := eq_one_of_mem_R_of_two_element hodd ha ⟨n, hapow⟩
  rw [← hxa, ha1, one_mul]
  exact hcY.2


private theorem s79_O2_eq {G : Type} [Group G] [Finite G] {Y R A L U : Subgroup G} {b₀ t₀ : G}
    (hZ : Subgroup.centralizer (Y : Set G) ⊓ Y = ⊥)
    (hC : Subgroup.centralizer ({b₀} : Set G) = R ⊔ (Subgroup.centralizer ({b₀} : Set G) ⊓ Y))
    (hRY : R ≤ Subgroup.centralizer (Y : Set G))
    (hodd : ¬ 2 ∣ Nat.card R)
    (ht₀ : orderOf t₀ = 2) (hLt₀ : L ≤ Subgroup.centralizer ({t₀} : Set G))
    (hUmax : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ Subgroup.centralizer ({t₀} : Set G) ⊓ Y →
      Subgroup.centralizer ({t₀} : Set G) ⊓ Y ≤ Subgroup.normalizer (P : Set G) → P ≤ U)
    (hirr : ∀ V : Subgroup G, Subgroup.zpowers t₀ ≤ V → V ≤ U →
      L ≤ Subgroup.normalizer (V : Set G) → V = Subgroup.zpowers t₀ ∨ V = U)
    (hA : IsElemAbelian 3 A) (hAcard : Nat.card A = 27) (hAL : A ≤ L)
    (hAF : ∀ F : Subgroup G, F ≤ A → Nat.card F = 9 → ∃ y ∈ Y, y * b₀ * y⁻¹ ∈ F)
    (hF : ∀ t : G, orderOf t = 2 → (t ∈ R ∨ t = t₀) →
      Subgroup.centralizer ({t} : Set G) ⊓
          Subgroup.centralizer (pCoreOf 2 (Subgroup.centralizer ({t} : Set G)) : Set G) ≤
        pCoreOf 2 (Subgroup.centralizer ({t} : Set G))) :
    pCoreOf 2 (Subgroup.centralizer ({t₀} : Set G)) = U := by
  let T : Subgroup G := pCoreOf 2 (Subgroup.centralizer ({t₀} : Set G))
  have hT2 : IsPGroup 2 T :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (Subgroup.centralizer ({t₀} : Set G)))
  have hCtN : Subgroup.centralizer ({t₀} : Set G) ≤ Subgroup.normalizer (T : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2)
      (Subgroup.centralizer ({t₀} : Set G))
  have h3T : ¬ 3 ∣ Nat.card T := by
    intro h3
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT2
    rw [hn] at h3
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    norm_num at h32
  have hAT : A ≤ Subgroup.normalizer (T : Set G) := (hAL.trans hLt₀).trans hCtN
  have hgen := iSup_inf_centralizer_eq_of_card_27 (A := A) (Q := T) hA hAcard hAT h3T
  have hiSup_le : (⨆ (F : Subgroup G) (_ : F ≤ A) (_ : Nat.card F = 9),
      T ⊓ Subgroup.centralizer (F : Set G)) ≤ Y := by
    refine iSup_le fun F => iSup_le fun hFA => iSup_le fun hFcard => ?_
    obtain ⟨y, hy, hby⟩ := hAF F hFA hFcard
    have hCb : Subgroup.centralizer ({y * b₀ * y⁻¹} : Set G) =
        R ⊔ (Subgroup.centralizer ({y * b₀ * y⁻¹} : Set G) ⊓ Y) :=
      centralizer_eq_sup_of_conj hy rfl hRY hC
    have hproj := inf_centralizer_le_Y (Y := Y) (R := R) (b := y * b₀ * y⁻¹)
      hRY hZ hCb hodd T hT2
    refine (inf_le_inf_left T (Subgroup.centralizer_le ?_)).trans hproj
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rwa [hz]
  have hTY : T ≤ Y := by
    rw [← hgen]
    exact hiSup_le
  have hTleU : T ≤ U := by
    refine hUmax T hT2 (le_inf (CFSG.LieType.BorelTits.pCoreOf_le (r := 2) (Subgroup.centralizer ({t₀} : Set G))) hTY) ?_
    exact (inf_le_left : Subgroup.centralizer ({t₀} : Set G) ⊓ Y ≤
      Subgroup.centralizer ({t₀} : Set G)).trans hCtN
  have hct_of : ∀ c ∈ Subgroup.centralizer ({t₀} : Set G), Commute c t₀ := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff] at hc
    exact (hc t₀ (by simp)).symm
  have hzT : Subgroup.zpowers t₀ ≤ T := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2)
      (N := Subgroup.zpowers t₀) (H := Subgroup.centralizer ({t₀} : Set G)) ?_ ?_ ?_
    · refine Subgroup.zpowers_le.mpr ?_
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst h
      rfl
    · intro c hc
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · intro hz
        rw [Subgroup.mem_zpowers_iff] at hz ⊢
        obtain ⟨k, rfl⟩ := hz
        exact ⟨k, ((hct_of c hc).zpow_right k).mul_inv_cancel.symm⟩
      · intro hz
        rw [Subgroup.mem_zpowers_iff] at hz ⊢
        obtain ⟨k, hk⟩ := hz
        refine ⟨k, ?_⟩
        rw [show z = c⁻¹ * (c * z * c⁻¹) * c from by group, ← hk]
        simpa using ((hct_of c hc).inv_left.zpow_right k).mul_inv_cancel.symm
    · refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, ht₀]
      norm_num
  have hLT : L ≤ Subgroup.normalizer (T : Set G) := hLt₀.trans hCtN
  rcases hirr T hzT hTleU hLT with hTz | hTU
  · exfalso
    have hCtT : Subgroup.centralizer ({t₀} : Set G) ≤ T := by
      have h := hF t₀ ht₀ (Or.inr rfl)
      have hCT : Subgroup.centralizer (T : Set G) = Subgroup.centralizer ({t₀} : Set G) := by
        rw [hTz, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      rw [hCT, inf_idem] at h
      exact h
    have hCt2 : IsPGroup 2 (Subgroup.centralizer ({t₀} : Set G)) := hT2.to_le hCtT
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hCt2
    have h3Ct : 3 ∣ Nat.card (Subgroup.centralizer ({t₀} : Set G)) := by
      have h3A : 3 ∣ Nat.card A := by rw [hAcard]; norm_num
      exact h3A.trans (Subgroup.card_dvd_of_le (hAL.trans hLt₀))
    rw [hn] at h3Ct
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3Ct
    norm_num at h32
  · exact hTU





theorem s79_radical {G : Type} [Group G] [Finite G] {Y R A L U : Subgroup G} {b₀ t₀ : G}
    (hZ : Subgroup.centralizer (Y : Set G) ⊓ Y = ⊥)
    (hC : Subgroup.centralizer ({b₀} : Set G) = R ⊔ (Subgroup.centralizer ({b₀} : Set G) ⊓ Y))
    (hRY : R ≤ Subgroup.centralizer (Y : Set G))
    (hO2 : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ Subgroup.centralizer ({b₀} : Set G) ⊓ Y →
      Subgroup.centralizer ({b₀} : Set G) ⊓ Y ≤ Subgroup.normalizer (P : Set G) → P = ⊥)
    (ht₀ : orderOf t₀ = 2) (hLY : L ≤ Y) (hLt₀ : L ≤ Subgroup.centralizer ({t₀} : Set G))
    (hU2 : IsPGroup 2 U) (ht₀U : t₀ ∈ U) (hUY : U ≤ Y)
    (hUt₀ : U ≤ Subgroup.centralizer ({t₀} : Set G))
    (hUmax : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ Subgroup.centralizer ({t₀} : Set G) ⊓ Y →
      Subgroup.centralizer ({t₀} : Set G) ⊓ Y ≤ Subgroup.normalizer (P : Set G) → P ≤ U)
    (hirr : ∀ V : Subgroup G, Subgroup.zpowers t₀ ≤ V → V ≤ U →
      L ≤ Subgroup.normalizer (V : Set G) → V = Subgroup.zpowers t₀ ∨ V = U)
    (hA : IsElemAbelian 3 A) (hAcard : Nat.card A = 27) (hAL : A ≤ L)
    (hAF : ∀ F : Subgroup G, F ≤ A → Nat.card F = 9 → ∃ y ∈ Y, y * b₀ * y⁻¹ ∈ F)
    (hF : ∀ t : G, orderOf t = 2 → (t ∈ R ∨ t = t₀) →
      Subgroup.centralizer ({t} : Set G) ⊓
          Subgroup.centralizer (pCoreOf 2 (Subgroup.centralizer ({t} : Set G)) : Set G) ≤
        pCoreOf 2 (Subgroup.centralizer ({t} : Set G))) :
    R = ⊥ ∧ pCoreOf 2 (Subgroup.centralizer ({t₀} : Set G)) = U := by
  have hodd : ¬ 2 ∣ Nat.card R :=
    s79_R_odd hZ hC hRY hO2 hLY hAL hA hAcard hAF
      (fun t ht htR => hF t ht (Or.inl htR))
  have hT : pCoreOf 2 (Subgroup.centralizer ({t₀} : Set G)) = U :=
    s79_O2_eq hZ hC hRY hodd ht₀ hLt₀ hUmax hirr hA hAcard hAL hAF hF
  have ht₀Y : t₀ ∈ Y := hUY ht₀U
  have : U ≤ Subgroup.centralizer ({t₀} : Set G) := hUt₀
  have hRct : R ≤ Subgroup.centralizer ({t₀} : Set G) := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst h
    exact Subgroup.mem_centralizer_iff.mp (hRY hr) t₀ ht₀Y
  have hRU : R ≤ U := by
    have h1 : R ≤ Subgroup.centralizer ({t₀} : Set G) ⊓
        Subgroup.centralizer (pCoreOf 2 (Subgroup.centralizer ({t₀} : Set G)) : Set G) := by
      refine le_inf hRct ?_
      rw [hT]
      exact hRY.trans (Subgroup.centralizer_le hUY)
    rw [hT] at h1
    have h2 := hF t₀ ht₀ (Or.inr rfl)
    rw [hT] at h2
    exact h1.trans h2
  have hR2 : IsPGroup 2 R := hU2.to_le hRU
  have hcard1 : Nat.card R = 1 := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hR2
    rw [hn]
    cases n with
    | zero => norm_num
    | succ n =>
      exfalso
      exact hodd (by rw [hn]; exact dvd_pow_self 2 (Nat.succ_ne_zero n))
  exact ⟨(Subgroup.eq_bot_iff_card (H := R)).mpr hcard1, hT⟩

end CFSG.StandardType.FrameRoute.FS81
