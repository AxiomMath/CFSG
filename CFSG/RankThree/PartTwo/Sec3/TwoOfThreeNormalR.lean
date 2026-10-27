module

public import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure
public import CFSG.RankThree.PartTwo.Sec3.ThompsonParabolic
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Layer
import CFSG.RankThree.PartTwo.Sec3.TwoOfThreeNormal

public section

namespace CFSG.RankThree.PartTwo.Sec3

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem eq_one_of_mem_sylow_of_pow_three (T : Sylow 2 G) {x : G} (hx3 : x ^ 3 = 1)
    (hxT : x ∈ (T : Subgroup G)) : x = 1 := by
  obtain ⟨k, hk⟩ := T.isPGroup' ⟨x, hxT⟩
  have hk' : x ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h1 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
  have h2 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h3 : orderOf x ∣ Nat.gcd 3 (2 ^ k) := Nat.dvd_gcd h1 h2
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (by norm_num)), Nat.dvd_one,
    orderOf_eq_one_iff] at h3
  exact h3

section Transfer

theorem isComponent_map_of_normal {H : Subgroup G} (hH : H.Normal) {C : Subgroup H}
    (hC : CFSG.IsComponent C) : CFSG.IsComponent (C.map H.subtype) := by
  obtain ⟨hq, hsn⟩ := hC
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (C.equivMapOfInjective H.subtype Subtype.val_injective) hq, ?_⟩
  have hXH : C.map H.subtype ≤ H := Subgroup.map_subtype_le C
  have hsub : (C.map H.subtype).subgroupOf H = C := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨c, hc, hcx⟩
      have hcx' : c = x := Subtype.ext hcx
      exact hcx' ▸ hc
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hX : ((C.map H.subtype).subgroupOf H).IsSubnormal := by
    rw [hsub]
    exact hsn
  exact Subgroup.IsSubnormal.trans hXH hX hH.isSubnormal

theorem layer_map_le_of_normal {H : Subgroup G} (hH : H.Normal) :
    (CFSG.layer H).map H.subtype ≤ CFSG.layer G := by
  rw [CFSG.layer.eq_sSup H, Subgroup.map_le_iff_le_comap]
  refine sSup_le fun C hC => ?_
  exact Subgroup.map_le_iff_le_comap.mp
    (CFSG.LocalCores.component_le_layer (isComponent_map_of_normal hH hC))

theorem fstar_map_le_of_normal {H : Subgroup G} (hH : H.Normal) :
    (CFSG.generalizedFitting H).map H.subtype ≤ CFSG.generalizedFitting G := by
  rw [CFSG.generalizedFitting.eq_sup H, CFSG.generalizedFitting.eq_sup G, Subgroup.map_sup]
  refine sup_le ?_ ?_
  · exact (CFSG.fittingSubgroupOf_le_fittingSubgroup H hH).trans le_sup_left
  · exact (layer_map_le_of_normal hH).trans le_sup_right

end Transfer

section HLocal

theorem pCore_inf_sup_le {T : Sylow 2 G} {B : Sylow 3 G} {R O : Subgroup G}
    (hRT : R ≤ (T : Subgroup G))
    (hRn : ∀ t ∈ (T : Subgroup G), ∀ r ∈ R, t * r * t⁻¹ ∈ R)
    (hOR : O ≤ R) (hOn : O.Normal) (hBOn : ((B : Subgroup G) ⊔ O).Normal)
    (hB3 : ∀ b ∈ (B : Subgroup G), b ^ 3 = 1) :
    CFSG.pCore 2 G ⊓ (R ⊔ (B : Subgroup G)) ≤ R := by
  have heq : R ⊔ ((B : Subgroup G) ⊔ O) = R ⊔ (B : Subgroup G) :=
    le_antisymm (sup_le le_sup_left (sup_le le_sup_right (hOR.trans le_sup_left)))
      (sup_le le_sup_left (le_sup_left.trans le_sup_right))
  have hQT : CFSG.pCore 2 G ≤ (T : Subgroup G) := pCore_two_le_sylow T
  intro x hx
  obtain ⟨hxQ, hxS⟩ := hx
  have hxS' : x ∈ R ⊔ ((B : Subgroup G) ⊔ O) := by
    rw [heq]
    exact hxS
  obtain ⟨r, hr, y, hy, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hxS'
  obtain ⟨b', hb', o', ho', rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
  have hb'T : b' ∈ (T : Subgroup G) := by
    have h := (T : Subgroup G).mul_mem
      ((T : Subgroup G).mul_mem ((T : Subgroup G).inv_mem (hRT hr)) (hQT hxQ))
      ((T : Subgroup G).inv_mem (hRT (hOR ho')))
    convert h using 1
    group
  have hb1 : b' = 1 := eq_one_of_mem_sylow_of_pow_three T (hB3 b' hb') hb'T
  rw [hb1, one_mul]
  exact R.mul_mem hr (hOR ho')

theorem sup_B_normal {T : Sylow 2 G} {B : Sylow 3 G} {R O : Subgroup G}
    (hRn : ∀ t ∈ (T : Subgroup G), ∀ r ∈ R, t * r * t⁻¹ ∈ R)
    (hOR : O ≤ R) (hBOn : ((B : Subgroup G) ⊔ O).Normal)
    (hTB : ∀ g : G, ∃ t ∈ (T : Subgroup G), ∃ b ∈ (B : Subgroup G), g = t * b) :
    (R ⊔ (B : Subgroup G)).Normal := by
  have heq : R ⊔ ((B : Subgroup G) ⊔ O) = R ⊔ (B : Subgroup G) :=
    le_antisymm (sup_le le_sup_left (sup_le le_sup_right (hOR.trans le_sup_left)))
      (sup_le le_sup_left (le_sup_left.trans le_sup_right))
  have hT : ∀ t ∈ (T : Subgroup G), ∀ x ∈ R ⊔ (B : Subgroup G),
      t * x * t⁻¹ ∈ R ⊔ (B : Subgroup G) := by
    intro t ht x hx
    rw [← heq] at hx ⊢
    obtain ⟨r, hr, y, hy, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    rw [show t * (r * y) * t⁻¹ = (t * r * t⁻¹) * (t * y * t⁻¹) by group]
    exact (R ⊔ ((B : Subgroup G) ⊔ O)).mul_mem (Subgroup.mem_sup_left (hRn t ht r hr))
      (Subgroup.mem_sup_right (hBOn.conj_mem y hy t))
  constructor
  intro n hn g
  obtain ⟨t, ht, b, hb, rfl⟩ := hTB g
  have hb' : b * n * b⁻¹ ∈ R ⊔ (B : Subgroup G) :=
    (R ⊔ (B : Subgroup G)).mul_mem
      ((R ⊔ (B : Subgroup G)).mul_mem (Subgroup.mem_sup_right hb) hn)
      ((R ⊔ (B : Subgroup G)).inv_mem (Subgroup.mem_sup_right hb))
  rw [show t * b * n * (t * b)⁻¹ = t * (b * n * b⁻¹) * t⁻¹ by group]
  exact hT t ht _ hb'

theorem centralizer_le_of_fstar_le {H P : Subgroup G} (hH : H.Normal)
    (hFP : CFSG.generalizedFitting G ⊓ H ≤ P) {h : G} (hh : h ∈ H)
    (hc : ∀ p ∈ P, h * p = p * h) : h ∈ P := by
  have hsub : ∀ x : H, x ∈ CFSG.generalizedFitting H → (x : G) ∈ P := by
    intro x hx
    have hmem : (x : G) ∈ (CFSG.generalizedFitting H).map H.subtype :=
      Subgroup.mem_map_of_mem _ hx
    exact hFP ⟨fstar_map_le_of_normal hH hmem, x.2⟩
  have hcent : (⟨h, hh⟩ : H) ∈ Subgroup.centralizer
      ((CFSG.generalizedFitting H : Subgroup H) : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    apply Subtype.ext
    exact (hc x (hsub x hx)).symm
  have hF' : (⟨h, hh⟩ : H) ∈ CFSG.generalizedFitting H :=
    CFSG.centralizer_generalizedFitting_le H hcent
  have hmem : H.subtype ⟨h, hh⟩ ∈ (CFSG.generalizedFitting H).map H.subtype :=
    Subgroup.mem_map_of_mem _ hF'
  exact hFP ⟨fstar_map_le_of_normal hH hmem, hh⟩

end HLocal

section NormalR

theorem pCore_inf_normal_of_normal {T : Sylow 2 G} {B : Sylow 3 G} {R O : Subgroup G}
    (hRT : R ≤ (T : Subgroup G))
    (hRn : ∀ t ∈ (T : Subgroup G), ∀ r ∈ R, t * r * t⁻¹ ∈ R)
    (hOR : O ≤ R) (hOn : O.Normal) (hBOn : ((B : Subgroup G) ⊔ O).Normal)
    (hTB : ∀ g : G, ∃ t ∈ (T : Subgroup G), ∃ b ∈ (B : Subgroup G), g = t * b)
    (hB3 : ∀ b ∈ (B : Subgroup G), b ^ 3 = 1) :
    (CFSG.pCore 2 G ⊓ R).Normal := by
  have hQT : CFSG.pCore 2 G ≤ (T : Subgroup G) := pCore_two_le_sylow T
  have hkey : ∀ x ∈ CFSG.pCore 2 G, x ∈ R ⊔ (B : Subgroup G) → x ∈ R := by
    intro x hxQ hxS
    have hxS' : x ∈ R ⊔ ((B : Subgroup G) ⊔ O) := by
      have heq : R ⊔ ((B : Subgroup G) ⊔ O) = R ⊔ (B : Subgroup G) :=
        le_antisymm (sup_le le_sup_left (sup_le le_sup_right (hOR.trans le_sup_left)))
          (sup_le le_sup_left (le_sup_left.trans le_sup_right))
      rw [heq]
      exact hxS
    obtain ⟨r, hr, y, hy, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hxS'
    obtain ⟨b', hb', o', ho', rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
    have hb'T : b' ∈ (T : Subgroup G) := by
      have h := (T : Subgroup G).mul_mem
        ((T : Subgroup G).mul_mem ((T : Subgroup G).inv_mem (hRT hr)) (hQT hxQ))
        ((T : Subgroup G).inv_mem (hRT (hOR ho')))
      convert h using 1
      group
    have hb1 : b' = 1 := eq_one_of_mem_sylow_of_pow_three T (hB3 b' hb') hb'T
    rw [hb1, one_mul]
    exact R.mul_mem hr (hOR ho')
  constructor
  intro n hn g
  obtain ⟨t, ht, b, hb, rfl⟩ := hTB g
  have hnQ : n ∈ CFSG.pCore 2 G := hn.1
  have hnR : n ∈ R := hn.2
  have hbn : b * n * b⁻¹ ∈ CFSG.pCore 2 G ⊓ R := by
    refine ⟨CFSG.pCore_normal.conj_mem n hnQ b, hkey _ (CFSG.pCore_normal.conj_mem n hnQ b) ?_⟩
    exact (R ⊔ (B : Subgroup G)).mul_mem ((R ⊔ (B : Subgroup G)).mul_mem
      (Subgroup.mem_sup_right hb) (Subgroup.mem_sup_left hnR))
      ((R ⊔ (B : Subgroup G)).inv_mem (Subgroup.mem_sup_right hb))
  rw [show t * b * n * (t * b)⁻¹ = t * (b * n * b⁻¹) * t⁻¹ by group]
  exact ⟨CFSG.pCore_normal.conj_mem _ hbn.1 t, hRn t ht _ hbn.2⟩

end NormalR

section RPort

omit [Finite G] in
theorem conj_mem_jG_of_normalizes {R : Subgroup G} {i : ℕ} {g : G}
    (hg : ∀ r ∈ R, g * r * g⁻¹ ∈ R) {x : G} (hx : x ∈ jG R i) :
    g * x * g⁻¹ ∈ jG R i := by
  have hle : (jG R i).map (MulAut.conj g).toMonoidHom ≤ jG R i := by
    rw [jG, (Subgroup.gc_map_comap (MulAut.conj g).toMonoidHom).l_sSup]
    exact iSup₂_le fun A hA => le_sSup (map_conj_mem_famG hA g
      (fun a ha => hg a (hA.1 ha)))
  exact hle ⟨x, hx, rfl⟩

omit [Finite G] in
theorem conj_mem_omegaG_jG_of_normalizes {T R : Subgroup G} {i : ℕ}
    (hRn : ∀ t ∈ T, ∀ r ∈ R, t * r * t⁻¹ ∈ R) {t : G} (ht : t ∈ T) {e : G}
    (he : e ∈ omegaG (jG R i)) : t * e * t⁻¹ ∈ omegaG (jG R i) :=
  conj_mem_omegaG (fun x hx => conj_mem_jG_of_normalizes (hRn t ht) hx)
    (fun x hx => by
      have := conj_mem_jG_of_normalizes (hRn t⁻¹ (T.inv_mem ht)) hx
      rwa [inv_inv] at this) he

omit [Finite G] in
theorem conj_mem_omegaG_of_normalizes {T R : Subgroup G}
    (hRn : ∀ t ∈ T, ∀ r ∈ R, t * r * t⁻¹ ∈ R) {t : G} (ht : t ∈ T) {e : G}
    (he : e ∈ omegaG R) : t * e * t⁻¹ ∈ omegaG R :=
  conj_mem_omegaG (fun x hx => hRn t ht x hx)
    (fun x hx => by
      have := hRn t⁻¹ (T.inv_mem ht) x hx
      rwa [inv_inv] at this) he

theorem le_pCore_inf_of_normal_sup {T : Sylow 2 G} {B : Sylow 3 G} {R O : Subgroup G}
    (hRT : R ≤ (T : Subgroup G))
    (hRn : ∀ t ∈ (T : Subgroup G), ∀ r ∈ R, t * r * t⁻¹ ∈ R)
    (hOR : O ≤ R) (hOn : O.Normal) (hBOn : ((B : Subgroup G) ⊔ O).Normal)
    (hTB : ∀ g : G, ∃ t ∈ (T : Subgroup G), ∃ b ∈ (B : Subgroup G), g = t * b)
    (hB3 : ∀ b ∈ (B : Subgroup G), b ^ 3 = 1)
    (hF : CFSG.generalizedFitting G = CFSG.pCore 2 G)
    {K : Subgroup G} (hKH : K ≤ R ⊔ (B : Subgroup G))
    (hKn : ∀ h ∈ R ⊔ (B : Subgroup G), ∀ k ∈ K, h * k * h⁻¹ ∈ K) (hK2 : IsPGroup 2 K) :
    K ≤ CFSG.pCore 2 G ⊓ R := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHn : (R ⊔ (B : Subgroup G)).Normal := sup_B_normal hRn hOR hBOn hTB
  set H : Subgroup G := R ⊔ (B : Subgroup G) with hHdef
  have hK'n : (K.subgroupOf H).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hKn g.1 g.2 n hn
  have hK'p : IsPGroup 2 (K.subgroupOf H) := by
    rintro ⟨x, hx⟩
    obtain ⟨k, hk⟩ := hK2 ⟨x, Subgroup.mem_subgroupOf.mp hx⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hk
  have h1 : K.subgroupOf H ≤ CFSG.pCore 2 ↥H := le_sSup ⟨hK'n, hK'p⟩
  have h2 : CFSG.pCore 2 ↥H ≤ CFSG.generalizedFitting ↥H := by
    refine (CFSG.pCore_le_fitting ↥H 2).trans ?_
    rw [CFSG.generalizedFitting.eq_sup ↥H]
    exact le_sup_left
  have hKm : K ≤ (CFSG.pCore 2 ↥H).map H.subtype := by
    intro x hx
    have hmem : (⟨x, hKH hx⟩ : ↥H) ∈ K.subgroupOf H := Subgroup.mem_subgroupOf.mpr hx
    exact Subgroup.mem_map_of_mem H.subtype (h1 hmem)
  have hKF : K ≤ CFSG.generalizedFitting G :=
    hKm.trans ((Subgroup.map_mono h2).trans (fstar_map_le_of_normal hHn))
  rw [hF] at hKF
  have hKR : K ≤ R := fun x hx => pCore_inf_sup_le hRT hRn hOR hOn hBOn hB3 ⟨hKF hx, hKH hx⟩
  exact le_inf hKF hKR

theorem mem_of_stabilizes_R {H P W : Subgroup G} (hP2 : IsPGroup 2 P) (hWP : W ≤ P)
    (hCP : ∀ h ∈ H, (∀ p ∈ P, h * p = p * h) → h ∈ P)
    (hHP : ∀ h ∈ H, ∀ p ∈ P, h * p * h⁻¹ ∈ P) (hHW : ∀ h ∈ H, ∀ w ∈ W, h * w * h⁻¹ ∈ W)
    (hO2 : ∀ K : Subgroup G, K ≤ H → (∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) → IsPGroup 2 K →
      K ≤ P)
    {k : G} (hkH : k ∈ H) (hkW : ∀ w ∈ W, k * w * k⁻¹ = w)
    (hkP : ∀ p ∈ P, k * p * k⁻¹ * p⁻¹ ∈ W) : k ∈ P := by
  let K : Subgroup G :=
    { carrier := {h | h ∈ H ∧ (∀ w ∈ W, h * w * h⁻¹ = w) ∧ ∀ p ∈ P, h * p * h⁻¹ * p⁻¹ ∈ W}
      one_mem' := ⟨H.one_mem, fun w _ => by group, fun p _ => by
        rw [one_mul, inv_one, mul_one, mul_inv_cancel]; exact W.one_mem⟩
      mul_mem' := by
        rintro a b ⟨haH, haW, haP⟩ ⟨hbH, hbW, hbP⟩
        refine ⟨H.mul_mem haH hbH, fun w hw => ?_, fun p hp => ?_⟩
        · calc a * b * w * (a * b)⁻¹ = a * (b * w * b⁻¹) * a⁻¹ := by group
            _ = w := by rw [hbW w hw, haW w hw]
        · have h1 := hbP p hp
          have h2 := haP p hp
          have h3 : a * (b * p * b⁻¹ * p⁻¹) * a⁻¹ = b * p * b⁻¹ * p⁻¹ := haW _ h1
          rw [show a * b * p * (a * b)⁻¹ * p⁻¹ =
              a * (b * p * b⁻¹ * p⁻¹) * a⁻¹ * (a * p * a⁻¹ * p⁻¹) by group, h3]
          exact W.mul_mem h1 h2
      inv_mem' := by
        rintro a ⟨haH, haW, haP⟩
        refine ⟨H.inv_mem haH, fun w hw => ?_, fun p hp => ?_⟩
        · have hw' : a⁻¹ * w * a ∈ W := by
            have := hHW a⁻¹ (H.inv_mem haH) w hw
            rwa [inv_inv] at this
          have := haW _ hw'
          calc a⁻¹ * w * a⁻¹⁻¹ = a⁻¹ * w * a := by group
            _ = a * (a⁻¹ * w * a) * a⁻¹ := this.symm
            _ = w := by group
        · have hp' : a⁻¹ * p * a ∈ P := by
            have := hHP a⁻¹ (H.inv_mem haH) p hp
            rwa [inv_inv] at this
          have h1 := haP _ hp'
          have : a⁻¹ * p * a⁻¹⁻¹ * p⁻¹ = (a * (a⁻¹ * p * a) * a⁻¹ * (a⁻¹ * p * a)⁻¹)⁻¹ := by
            group
          rw [this]
          exact W.inv_mem h1 }
  have hKH : K ≤ H := fun h hh => hh.1
  have hKn : ∀ h ∈ H, ∀ x ∈ K, h * x * h⁻¹ ∈ K := by
    rintro g hg x ⟨hxH, hxW, hxP⟩
    refine ⟨H.mul_mem (H.mul_mem hg hxH) (H.inv_mem hg), fun w hw => ?_, fun p hp => ?_⟩
    · have hw' : g⁻¹ * w * g ∈ W := by
        have := hHW g⁻¹ (H.inv_mem hg) w hw
        rwa [inv_inv] at this
      calc g * x * g⁻¹ * w * (g * x * g⁻¹)⁻¹ = g * (x * (g⁻¹ * w * g) * x⁻¹) * g⁻¹ := by group
        _ = w := by rw [hxW _ hw']; group
    · have hp' : g⁻¹ * p * g ∈ P := by
        have := hHP g⁻¹ (H.inv_mem hg) p hp
        rwa [inv_inv] at this
      have h1 := hHW g hg _ (hxP _ hp')
      have : g * x * g⁻¹ * p * (g * x * g⁻¹)⁻¹ * p⁻¹ =
          g * (x * (g⁻¹ * p * g) * x⁻¹ * (g⁻¹ * p * g)⁻¹) * g⁻¹ := by group
      rw [this]
      exact h1
  have hK2 : IsPGroup 2 K := by
    intro x
    have hne : orderOf (x : G) ≠ 0 := (orderOf_pos (x : G)).ne'
    obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd hne
    set y : G := (x : G) ^ (2 ^ a) with hydef
    have hyK : y ∈ K := K.pow_mem x.2 _
    have hyord : orderOf y = m := by
      rw [hydef, orderOf_pow' _ (by positivity), hord, Nat.gcd_mul_right_left]
      rw [Nat.mul_div_cancel_left _ (by positivity)]
    have hycent : ∀ p ∈ P, y * p * y⁻¹ = p := fun p hp =>
      commute_of_odd_of_stabilizes hP2 hWP (by rw [hyord]; exact hm) hyK.2.2 hyK.2.1 hp
    have hyP : y ∈ P := by
      apply hCP y hyK.1
      intro p hp
      have := hycent p hp
      calc y * p = y * p * y⁻¹ * y := by group
        _ = p * y := by rw [this]
    obtain ⟨j, hj⟩ := hP2 ⟨y, hyP⟩
    have hyj : y ^ 2 ^ j = 1 := by
      have := congrArg Subtype.val hj
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
    have hdvd : m ∣ 2 ^ j := hyord ▸ orderOf_dvd_of_pow_eq_one hyj
    have hm1 : m = 1 := by
      have hcop : Nat.Coprime m (2 ^ j) :=
        Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hm)
      exact Nat.Coprime.eq_one_of_dvd hcop hdvd
    refine ⟨a, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hydef]
    rw [← orderOf_eq_one_iff, hyord, hm1]
  exact hO2 K hKH hKn hK2 ⟨hkH, hkW, hkP⟩

omit [Finite G] in
theorem conj_mem_omegaG_jG_self {R : Subgroup G} {i : ℕ} {p : G} (hp : p ∈ R) {e : G}
    (he : e ∈ omegaG (jG R i)) : p * e * p⁻¹ ∈ omegaG (jG R i) :=
  conj_mem_omegaG_jG_of_normalizes (T := R)
    (fun t ht r hr => R.mul_mem (R.mul_mem ht hr) (R.inv_mem ht)) hp he

theorem omegaG_jG_le_R {R H P A₁ : Subgroup G} (hPR : P ≤ R) (hP2 : IsPGroup 2 P)
    (hCP : ∀ h ∈ H, (∀ p ∈ P, h * p = p * h) → h ∈ P)
    (hHP : ∀ h ∈ H, ∀ p ∈ P, h * p * h⁻¹ ∈ P)
    (hO2 : ∀ K : Subgroup G, K ≤ H → (∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) → IsPGroup 2 K →
      K ≤ P)
    (hEH : omegaG (jG R 1) ≤ H) (hr : 2 ≤ CFSG.pRank 2 R) (hA₁ : A₁ ∈ famG R 1)
    (hA₁P : A₁ ≤ P) : omegaG (jG R 1) ≤ P := by
  intro e he
  have hHW : ∀ h ∈ H, ∀ w ∈ omegaG (pOne R P), h * w * h⁻¹ ∈ omegaG (pOne R P) :=
    fun h hh w hw => conj_mem_omegaG_pOne hPR (hHP h hh)
      (fun p hp => by
        have := hHP h⁻¹ (H.inv_mem hh) p hp
        rwa [inv_inv] at this) hw
  refine mem_of_stabilizes_R hP2 ((omegaG_le _).trans (pOne_le R P)) hCP hHP hHW hO2
    (hEH he) (fun w hw => ?_) (fun p hp => ?_)
  · have := he.2.1 w (pOne_le_jG R P (omegaG_le _ hw))
    rw [this, mul_inv_cancel_right]
  · have hcE : e * p * e⁻¹ * p⁻¹ ∈ omegaG (jG R 1) := by
      have h1 : p * e⁻¹ * p⁻¹ ∈ omegaG (jG R 1) :=
        conj_mem_omegaG_jG_self (hPR hp) ((omegaG (jG R 1)).inv_mem he)
      have : e * p * e⁻¹ * p⁻¹ = e * (p * e⁻¹ * p⁻¹) := by group
      rw [this]
      exact (omegaG (jG R 1)).mul_mem he h1
    have hcP : e * p * e⁻¹ * p⁻¹ ∈ P := P.mul_mem (hHP e (hEH he) p hp) (P.inv_mem hp)
    exact mem_omegaG_pOne hr hA₁ hA₁P hPR hcE hcP

theorem not_centralizes_omegaG_pOne_R {R H P X S A₁ : Subgroup G} (hPR : P ≤ R)
    (hP2 : IsPGroup 2 P) (hCP : ∀ h ∈ H, (∀ p ∈ P, h * p = p * h) → h ∈ P)
    (hHP : ∀ h ∈ H, ∀ p ∈ P, h * p * h⁻¹ ∈ P)
    (hO2 : ∀ K : Subgroup G, K ≤ H → (∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) → IsPGroup 2 K →
      K ≤ P)
    (hEH : omegaG (jG R 1) ≤ H) (hEnS : ∀ t ∈ S, ∀ e ∈ omegaG (jG R 1),
      t * e * t⁻¹ ∈ omegaG (jG R 1))
    (hgen : ∀ N : Subgroup G, (∀ t ∈ S, ∀ n ∈ N, t * n * t⁻¹ ∈ N) →
      (∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) → N.Normal)
    (hr : 2 ≤ CFSG.pRank 2 R) (hA₁ : A₁ ∈ famG R 1) (hA₁P : A₁ ≤ P)
    (hEnn : ¬ (omegaG (jG R 1)).Normal) :
    ¬ ∀ x ∈ X, ∀ w ∈ omegaG (pOne R P), x * w * x⁻¹ = w := by
  intro hX
  apply hEnn
  apply hgen _ hEnS
  intro x hx e he
  have heW : e ∈ omegaG (pOne R P) :=
    mem_omegaG_pOne hr hA₁ hA₁P hPR he (omegaG_jG_le_R hPR hP2 hCP hHP hO2 hEH hr hA₁ hA₁P he)
  rw [hX x hx e heW]
  exact he

theorem le_pCore_of_mem_famG_of_normal (T : Sylow 2 G) (B : Sylow 3 G) {R O : Subgroup G}
    (hRT : R ≤ (T : Subgroup G)) (hRn : ∀ t ∈ (T : Subgroup G), ∀ r ∈ R, t * r * t⁻¹ ∈ R)
    (hOR : O ≤ R) (hOn : O.Normal) (hBOn : ((B : Subgroup G) ⊔ O).Normal)
    (hB9 : Nat.card (B : Subgroup G) = 9)
    (hTB : ∀ g : G, ∃ t ∈ (T : Subgroup G), ∃ b ∈ (B : Subgroup G), g = t * b)
    (hBc : ∀ a ∈ (B : Subgroup G), ∀ b ∈ (B : Subgroup G), a * b = b * a)
    (hB3 : ∀ b ∈ (B : Subgroup G), b ^ 3 = 1)
    (hQ8 : ∃ K : Subgroup (MulAut (B : Subgroup G)),
      K ≤ ((T : Subgroup G).subgroupOf (normalizer ((B : Subgroup G) : Set G))).map
        (B : Subgroup G).normalizerMonoidHom ∧ Nonempty (K ≃* QuaternionGroup 2))
    (hV : ∃ b ∈ (B : Subgroup G), ∃ v ∈ omegaG (CFSG.pCore 2 G ⊓ R), b * v * b⁻¹ ≠ v) {i : ℕ}
    (hi : i ≤ 1) {A : Subgroup G} (hA : A ∈ famG R i) : A ≤ CFSG.pCore 2 G := by
  set Q := CFSG.pCore 2 G with hQdef
  have hQ2 : IsPGroup 2 Q := pCore_two_isPGroup
  have htr := htr_of_quaternion T B hB9 hBc hB3 hQ8
  set V := omegaG (Q ⊓ R) with hVdef
  have hVn : V.Normal := omegaG_normal (pCore_inf_normal_of_normal hRT hRn hOR hOn hBOn hTB hB3)
  have hVQ : V ≤ Q := (omegaG_le _).trans inf_le_left
  have hVR : V ≤ R := (omegaG_le _).trans inf_le_right
  have hVel : IsElemTwo V := isElemTwo_omegaG (Q ⊓ R)
  have hQR : Q ⊓ R ≤ centralizer (V : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact hv.2.1 q hq
  have hAR : A ≤ R := hA.1
  have hAT : A ≤ (T : Subgroup G) := hAR.trans hRT
  have hk4 := relIndex_le_four T B hB9 hTB hBc hB3 hAT hA.2.1.2 hA.2.1.1
  have hkdvd : Q.relIndex A ∣ 2 ^ (CFSG.pRank 2 R - i) :=
    hA.2.2 ▸ Subgroup.relIndex_dvd_card Q A
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hkdvd
  have hstd := relIndex_centralizer_le_of_famG hVR hVel hA
  have hQRA : (Q ⊓ R).relIndex A = Q.relIndex A := by
    have h := Subgroup.relIndex_inf_mul_relIndex (H := Q) (K := R) (L := A)
    rw [Subgroup.relIndex_eq_one.mpr hAR, mul_one, inf_eq_right.mpr hAR] at h
    exact h.symm
  have hcv : (centralizer (V : Set G)).relIndex A ≤ Q.relIndex A := by
    rw [← hQRA]
    exact Subgroup.relIndex_le_of_le_left hQR (relIndex_ne_zero_of_finite _ _)
  have h2i : 2 ^ i ≤ 2 := by
    calc 2 ^ i ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hi
      _ = 2 := by norm_num
  have hjle : j ≤ 2 := by
    rw [hj] at hk4
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp (hk4.trans (by norm_num))
  have hcentA : ∀ t ∈ A, (centralizer ({t} : Set G)).relIndex V ≤
      (centralizer (A : Set G)).relIndex V := fun t ht =>
    Subgroup.relIndex_le_of_le_left (Subgroup.centralizer_le (by simpa using ht))
      (relIndex_ne_zero_of_finite _ _)
  interval_cases j
  · rw [pow_zero] at hj
    exact Subgroup.relIndex_eq_one.mp hj
  · exfalso
    obtain ⟨t, htA, htQ⟩ : ∃ t ∈ A, t ∉ Q := by
      by_contra h
      push Not at h
      rw [Subgroup.relIndex_eq_one.mpr h] at hj
      norm_num at hj
    obtain ⟨d, hdB, hd1, htd⟩ := exists_inv_mod_of_mul_self_mem T B hB9 hTB hBc hB3 (hAT htA)
      htQ (by rw [hA.2.1.2 t htA]; exact Q.one_mem)
    have h8 := eight_le_relIndex_centralizer hQ2 hBc hB3 hB9 htr hdB hd1 htd V hVn hVQ
      hVel.1 hVel.2 hV
    have := (h8.trans (hcentA t htA)).trans hstd
    rw [hj] at hcv
    have : 8 ≤ 2 ^ i * 2 := this.trans (Nat.mul_le_mul_left _ hcv)
    omega
  · exfalso
    obtain ⟨⟨z, hzA, hz⟩, -⟩ := exists_of_relIndex_eq_four T B hB9 hTB hBc hB3 hAT
      hA.2.1.2 hA.2.1.1 hj
    have h16 := sixteen_le_relIndex_centralizer hQ2 hBc hB3 hB9 htr hz V hVn hVQ hVel.1 hVel.2
      hV
    have := (h16.trans (hcentA z hzA)).trans hstd
    rw [hj] at hcv
    have : 16 ≤ 2 ^ i * 4 := this.trans (Nat.mul_le_mul_left _ hcv)
    omega

theorem relIndex_ne_two_of_normal (T : Sylow 2 G) (B : Sylow 3 G) {R O : Subgroup G}
    (hRT : R ≤ (T : Subgroup G)) (hRn : ∀ t ∈ (T : Subgroup G), ∀ r ∈ R, t * r * t⁻¹ ∈ R)
    (hOR : O ≤ R) (hOn : O.Normal) (hBOn : ((B : Subgroup G) ⊔ O).Normal)
    (hTB : ∀ g : G, ∃ t ∈ (T : Subgroup G), ∃ b ∈ (B : Subgroup G), g = t * b)
    (hB9 : Nat.card (B : Subgroup G) = 9)
    (hBc : ∀ a ∈ (B : Subgroup G), ∀ b ∈ (B : Subgroup G), a * b = b * a)
    (hB3 : ∀ b ∈ (B : Subgroup G), b ^ 3 = 1)
    (hF : CFSG.generalizedFitting G = CFSG.pCore 2 G)
    (hQ8 : ∃ K : Subgroup (MulAut (B : Subgroup G)),
      K ≤ ((T : Subgroup G).subgroupOf (normalizer ((B : Subgroup G) : Set G))).map
        (B : Subgroup G).normalizerMonoidHom ∧ Nonempty (K ≃* QuaternionGroup 2))
    (hEnn : ¬ (omegaG (jG R 1)).Normal) {A : Subgroup G} (hA : A ∈ famG R 0) :
    (CFSG.pCore 2 G).relIndex A ≠ 2 := by
  intro h2
  set Q := CFSG.pCore 2 G with hQdef
  have hQ2 : IsPGroup 2 Q := pCore_two_isPGroup
  have hQRn : (Q ⊓ R).Normal := pCore_inf_normal_of_normal hRT hRn hOR hOn hBOn hTB hB3
  have hQR2 : IsPGroup 2 ((Q ⊓ R : Subgroup G)) := hQ2.to_le inf_le_left
  have htr := htr_of_quaternion T B hB9 hBc hB3 hQ8
  have hr : 2 ≤ CFSG.pRank 2 R := by
    by_contra h
    push Not at h
    apply hEnn
    rw [omegaG_jG_one_eq_bot_of_pRank_le (by omega)]
    exact Subgroup.normal_bot
  obtain ⟨t, htA, htQ⟩ : ∃ t ∈ A, t ∉ Q := by
    by_contra h
    push Not at h
    rw [Subgroup.relIndex_eq_one.mpr h] at h2
    norm_num at h2
  have hAQ : A ⊓ Q ∈ famG R 1 := by
    refine ⟨inf_le_left.trans hA.1, ⟨fun a ha b hb => hA.2.1.1 a ha.1 b hb.1,
      fun a ha => hA.2.1.2 a ha.1⟩, ?_⟩
    have h := Subgroup.relIndex_mul_card (H := Q) (K := A)
    rw [h2, hA.2.2, inf_comm] at h
    have h' : 2 ^ (CFSG.pRank 2 R - 0) = 2 * 2 ^ (CFSG.pRank 2 R - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [h'] at h
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h
  have hAQR : A ⊓ (Q ⊓ R) = A ⊓ Q := by
    have hle : A ⊓ Q ≤ R := inf_le_left.trans hA.1
    rw [← inf_assoc, inf_eq_left.mpr hle]
  have hAQ' : A ⊓ (Q ⊓ R) ∈ famG R 1 := by rw [hAQR]; exact hAQ
  have hCP : ∀ h ∈ R ⊔ (B : Subgroup G), (∀ p ∈ Q ⊓ R, h * p = p * h) → h ∈ Q ⊓ R := by
    intro h hh hc
    have hFP : CFSG.generalizedFitting G ⊓ (R ⊔ (B : Subgroup G)) ≤ Q ⊓ R := by
      rintro x ⟨hxF, hxH⟩
      rw [hF] at hxF
      exact ⟨hxF, pCore_inf_sup_le hRT hRn hOR hOn hBOn hB3 ⟨hxF, hxH⟩⟩
    exact centralizer_le_of_fstar_le (sup_B_normal hRn hOR hBOn hTB) hFP hh hc
  have hO2 : ∀ K : Subgroup G, K ≤ R ⊔ (B : Subgroup G) →
      (∀ h ∈ R ⊔ (B : Subgroup G), ∀ k ∈ K, h * k * h⁻¹ ∈ K) → IsPGroup 2 K → K ≤ Q ⊓ R :=
    fun K hKH hKn hK2 => le_pCore_inf_of_normal_sup hRT hRn hOR hOn hBOn hTB hB3 hF hKH hKn hK2
  have hHP : ∀ h ∈ R ⊔ (B : Subgroup G), ∀ p ∈ Q ⊓ R, h * p * h⁻¹ ∈ Q ⊓ R :=
    fun h _ p hp => hQRn.conj_mem p hp h
  have hEH : omegaG (jG R 1) ≤ R ⊔ (B : Subgroup G) := fun e he =>
    Subgroup.mem_sup_left (jG_le _ _ (omegaG_le _ he))
  have hEnS : ∀ s ∈ (T : Subgroup G), ∀ e ∈ omegaG (jG R 1),
      s * e * s⁻¹ ∈ omegaG (jG R 1) :=
    fun s hs e he => conj_mem_omegaG_jG_of_normalizes hRn hs he
  have hgen : ∀ N : Subgroup G, (∀ s ∈ (T : Subgroup G), ∀ n ∈ N, s * n * s⁻¹ ∈ N) →
      (∀ x ∈ (B : Subgroup G), ∀ n ∈ N, x * n * x⁻¹ ∈ N) → N.Normal := by
    intro N hNT hNB
    constructor
    intro n hn g
    obtain ⟨s, hs, b, hb, rfl⟩ := hTB g
    have := hNT s hs _ (hNB b hb n hn)
    rw [show s * b * n * (s * b)⁻¹ = s * (b * n * b⁻¹) * s⁻¹ by group]
    exact this
  have hXnc := not_centralizes_omegaG_pOne_R (R := R) (H := R ⊔ (B : Subgroup G))
    (P := Q ⊓ R) (X := (B : Subgroup G)) (S := (T : Subgroup G)) (A₁ := A ⊓ Q)
    inf_le_right hQR2 hCP hHP hO2 hEH hEnS hgen hr hAQ (fun x hx => ⟨hx.2, hA.1 hx.1⟩) hEnn
  push Not at hXnc
  set W := omegaG (pOne R (Q ⊓ R)) with hWdef
  have hWn : W.Normal := ⟨fun w hw g => conj_mem_omegaG_pOne inf_le_right
    (fun p hp => hQRn.conj_mem p hp g)
    (fun p hp => by
      have := hQRn.conj_mem p hp g⁻¹
      rwa [inv_inv] at this) hw⟩
  have hWQ : W ≤ Q := (omegaG_le _).trans ((pOne_le _ _).trans inf_le_left)
  have hle2 : (centralizer ({t} : Set G)).relIndex W ≤ 2 :=
    relIndex_centralizer_le_two inf_le_right hA hAQ' htA
  obtain ⟨d, hdB, hd1, htd⟩ := exists_inv_mod_of_mul_self_mem T B hB9 hTB hBc hB3
    (hRT (hA.1 htA)) htQ (by rw [hA.2.1.2 t htA]; exact Q.one_mem)
  have h8 := eight_le_relIndex_centralizer hQ2 hBc hB3 hB9 htr hdB hd1 htd W hWn hWQ
    (isElemTwo_omegaG _).1 (isElemTwo_omegaG _).2 hXnc
  omega

theorem relIndex_ne_four_of_normal (T : Sylow 2 G) (B : Sylow 3 G) {R O : Subgroup G}
    (hRT : R ≤ (T : Subgroup G)) (hRn : ∀ t ∈ (T : Subgroup G), ∀ r ∈ R, t * r * t⁻¹ ∈ R)
    (hOR : O ≤ R) (hOn : O.Normal) (hBOn : ((B : Subgroup G) ⊔ O).Normal)
    (hTB : ∀ g : G, ∃ t ∈ (T : Subgroup G), ∃ b ∈ (B : Subgroup G), g = t * b)
    (hB9 : Nat.card (B : Subgroup G) = 9)
    (hBc : ∀ a ∈ (B : Subgroup G), ∀ b ∈ (B : Subgroup G), a * b = b * a)
    (hB3 : ∀ b ∈ (B : Subgroup G), b ^ 3 = 1)
    (hF : CFSG.generalizedFitting G = CFSG.pCore 2 G)
    (hQ8 : ∃ K : Subgroup (MulAut (B : Subgroup G)),
      K ≤ ((T : Subgroup G).subgroupOf (normalizer ((B : Subgroup G) : Set G))).map
        (B : Subgroup G).normalizerMonoidHom ∧ Nonempty (K ≃* QuaternionGroup 2))
    (hEnn : ¬ (omegaG (jG R 1)).Normal) {A : Subgroup G} (hA : A ∈ famG R 0) :
    (CFSG.pCore 2 G).relIndex A ≠ 4 := by
  intro h4
  set Q := CFSG.pCore 2 G with hQdef
  have hQ2 : IsPGroup 2 Q := pCore_two_isPGroup
  have hQn : Q.Normal := CFSG.pCore_normal
  have hQRn : (Q ⊓ R).Normal := pCore_inf_normal_of_normal hRT hRn hOR hOn hBOn hTB hB3
  have hAT : A ≤ (T : Subgroup G) := hA.1.trans hRT
  have hQRB : ∀ x ∈ Q, x ∈ R ⊔ (B : Subgroup G) → x ∈ Q ⊓ R := fun x hxQ hxS =>
    ⟨hxQ, pCore_inf_sup_le hRT hRn hOR hOn hBOn hB3 ⟨hxQ, hxS⟩⟩
  have hr : 2 ≤ CFSG.pRank 2 R := by
    by_contra h
    push Not at h
    apply hEnn
    rw [omegaG_jG_one_eq_bot_of_pRank_le (by omega)]
    exact Subgroup.normal_bot
  obtain ⟨⟨z, hzA, hz⟩, y, hyB, hy1, hpm, ⟨s, hsA, hsy⟩, ⟨c, hcA, hcQ, hcy⟩⟩ :=
    exists_of_relIndex_eq_four T B hB9 hTB hBc hB3 hAT hA.2.1.2 hA.2.1.1 h4
  set π := QuotientGroup.mk' Q with hπ
  have hπQ : ∀ q ∈ Q, π q = 1 := fun q hq => (QuotientGroup.eq_one_iff q).mpr hq
  have hcomm_iff : ∀ g : G, g * y * g⁻¹ * y⁻¹ ∈ Q ↔ π g * π y = π y * π g := fun g => by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, ← hπ, map_mul, map_mul, map_mul,
      map_inv, map_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
  have hinv_iff : ∀ g : G, g * y * g⁻¹ * y ∈ Q ↔ π g * π y * (π g)⁻¹ = (π y)⁻¹ := fun g => by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, ← hπ, map_mul, map_mul, map_mul,
      map_inv, mul_eq_one_iff_eq_inv]
  have hπy1 : π y ≠ 1 := fun h => hy1 (by
    have h' : y ∈ (B : Subgroup G) ⊓ CFSG.pCore 2 G := ⟨hyB, (QuotientGroup.eq_one_iff y).mp h⟩
    rwa [inf_pCore_two_eq_bot B hB9, Subgroup.mem_bot] at h')
  have hπy3 : π y ^ 3 = 1 := by rw [← map_pow, hB3 y hyB, map_one]
  have hπyinv : (π y)⁻¹ ≠ π y := fun h => hπy1 (by
    have h2 : π y * π y = 1 := by
      calc π y * π y = π y * (π y)⁻¹ := by rw [h]
        _ = 1 := mul_inv_cancel _
    calc π y = π y ^ 3 * (π y * π y)⁻¹ := by group
      _ = 1 := by rw [hπy3, h2, inv_one, one_mul])
  set Cy : Subgroup G := (centralizer ({π y} : Set (G ⧸ Q))).comap π with hCydef
  have hmemCy : ∀ g, g ∈ Cy ↔ g * y * g⁻¹ * y⁻¹ ∈ Q := fun g => by
    rw [hCydef, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, hcomm_iff]
  have hQCy : Q ≤ Cy := fun q hq => by
    rw [hmemCy, hcomm_iff, hπQ q hq, one_mul, mul_one]
  set A₀ := A ⊓ Cy with hA₀def
  set P := (Q ⊓ R) ⊔ A₀ with hPdef
  set X := Subgroup.zpowers y with hXdef
  set H := (X ⊔ (Q ⊓ R)) ⊔ A with hHdef
  have hPR : P ≤ R := sup_le inf_le_right (inf_le_left.trans hA.1)
  have hPT : P ≤ (T : Subgroup G) := hPR.trans hRT
  have hP2 : IsPGroup 2 P := T.isPGroup'.to_le hPT
  have hPCy : P ≤ Cy := sup_le (inf_le_left.trans hQCy) inf_le_right
  have hPy : ∀ p ∈ P, p * y * p⁻¹ * y⁻¹ ∈ Q := fun p hp => (hmemCy p).mp (hPCy hp)
  have hPQ : Q.relIndex P ≤ 2 :=
    relIndex_le_two_of_centralizes T B hB9 hTB hBc hB3 hPT hyB hy1 hPy
  have hAP : A ⊓ P = A₀ := by
    apply le_antisymm
    · rintro x ⟨hxA, hxP⟩
      obtain ⟨q, hq, a, ha, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hxP
      exact ⟨hxA, Cy.mul_mem (hQCy hq.1) ha.2⟩
    · exact le_inf inf_le_left le_sup_right
  have hsCy : s ∉ Cy := fun h => hπyinv (by
    have h1 := (hcomm_iff s).mp ((hmemCy s).mp h)
    have h2 := (hinv_iff s).mp hsy
    rw [← h2, h1, mul_inv_cancel_right])
  have hrel2 : Cy.relIndex A = 2 := by
    have hdvd : Cy.relIndex A ∣ 2 := by
      rw [Subgroup.relIndex_dvd_two_iff']
      refine ⟨s, hsA, fun b hb => ?_⟩
      rcases hpm b hb with hcen | hinv
      · exact Or.inr ((hmemCy b).mpr hcen)
      · left
        rw [hmemCy, hcomm_iff]
        have h1 := (hinv_iff s).mp hsy
        have h2 := (hinv_iff b).mp hinv
        have h3 : π (s * b) * π y * (π (s * b))⁻¹ = π y := by
          calc π (s * b) * π y * (π (s * b))⁻¹
              = π s * (π b * π y * (π b)⁻¹) * (π s)⁻¹ := by rw [map_mul]; group
            _ = π s * (π y)⁻¹ * (π s)⁻¹ := by rw [h2]
            _ = (π s * π y * (π s)⁻¹)⁻¹ := by group
            _ = π y := by rw [h1, inv_inv]
        calc π (s * b) * π y = π (s * b) * π y * (π (s * b))⁻¹ * π (s * b) := by group
          _ = π y * π (s * b) := by rw [h3]
    have hne1 : Cy.relIndex A ≠ 1 := fun h => hsCy (Subgroup.relIndex_eq_one.mp h hsA)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd h hne1
    · exact h
  have hA₀ : A₀ ∈ famG R 1 := by
    refine ⟨inf_le_left.trans hA.1, ⟨fun a ha b hb => hA.2.1.1 a ha.1 b hb.1,
      fun a ha => hA.2.1.2 a ha.1⟩, ?_⟩
    have h := Subgroup.relIndex_mul_card (H := Cy) (K := A)
    rw [hrel2, hA.2.2, inf_comm] at h
    have h' : 2 ^ (CFSG.pRank 2 R - 0) = 2 * 2 ^ (CFSG.pRank 2 R - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [h'] at h
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h
  have hAP' : A ⊓ P ∈ famG R 1 := by rw [hAP]; exact hA₀
  have hRB_mul : ∀ g ∈ (R : Subgroup G), ∀ b ∈ (B : Subgroup G),
      g * b * g⁻¹ * b⁻¹ ∈ R ⊔ (B : Subgroup G) := fun g hg b hb =>
    (R ⊔ (B : Subgroup G)).mul_mem
      ((R ⊔ (B : Subgroup G)).mul_mem ((R ⊔ (B : Subgroup G)).mul_mem
        (Subgroup.mem_sup_left hg) (Subgroup.mem_sup_right hb))
        ((R ⊔ (B : Subgroup G)).inv_mem (Subgroup.mem_sup_left hg)))
      ((R ⊔ (B : Subgroup G)).inv_mem (Subgroup.mem_sup_right hb))
  have hRB_word : ∀ g ∈ (R : Subgroup G), ∀ b ∈ (B : Subgroup G),
      g * b * g⁻¹ * b ∈ R ⊔ (B : Subgroup G) := fun g hg b hb =>
    (R ⊔ (B : Subgroup G)).mul_mem
      ((R ⊔ (B : Subgroup G)).mul_mem ((R ⊔ (B : Subgroup G)).mul_mem
        (Subgroup.mem_sup_left hg) (Subgroup.mem_sup_right hb))
        ((R ⊔ (B : Subgroup G)).inv_mem (Subgroup.mem_sup_left hg)))
      (Subgroup.mem_sup_right hb)
  have hyP : ∀ p ∈ P, y * p * y⁻¹ ∈ P := by
    intro p hp
    obtain ⟨q, hq, a, ha, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hp
    have ha' : a⁻¹ * y * a⁻¹⁻¹ * y⁻¹ ∈ Q ⊓ R :=
      hQRB _ ((hmemCy _).mp (Cy.inv_mem ha.2))
        (hRB_mul a⁻¹ (R.inv_mem (hA.1 ha.1)) y hyB)
    have : y * (q * a) * y⁻¹ = (y * q * y⁻¹) * a * (a⁻¹ * y * a⁻¹⁻¹ * y⁻¹) := by group
    rw [this]
    exact P.mul_mem (P.mul_mem (Subgroup.mem_sup_left (hQRn.conj_mem q hq y))
      (Subgroup.mem_sup_right ha)) (Subgroup.mem_sup_left ha')
  have hAPn : ∀ a ∈ A, ∀ p ∈ P, a * p * a⁻¹ ∈ P := by
    intro a ha p hp
    obtain ⟨q, hq, a', ha', rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hp
    have : a * (q * a') * a⁻¹ = (a * q * a⁻¹) * a' := by
      rw [show a * (q * a') * a⁻¹ = (a * q * a⁻¹) * (a * a' * a⁻¹) by group,
        hA.2.1.1 a ha a' ha'.1, mul_inv_cancel_right]
    rw [this]
    exact P.mul_mem (Subgroup.mem_sup_left (hQRn.conj_mem q hq a)) (Subgroup.mem_sup_right ha')
  have hHN : H ≤ normalizer (P : Set G) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · exact Subgroup.zpowers_le.mpr (mem_normalizer_of_conj_mem hyP)
    · intro q hq
      exact mem_normalizer_of_conj_mem fun p hp =>
        P.mul_mem (P.mul_mem (Subgroup.mem_sup_left hq) hp) (P.inv_mem (Subgroup.mem_sup_left hq))
    · intro a ha
      exact mem_normalizer_of_conj_mem (hAPn a ha)
  have hHP : ∀ h ∈ H, ∀ p ∈ P, h * p * h⁻¹ ∈ P := fun h hh p hp =>
    (Subgroup.mem_normalizer_iff.mp (hHN hh) p).mp hp
  have hAXQ : A ≤ normalizer ((X ⊔ (Q ⊓ R) : Subgroup G) : Set G) := by
    intro a ha
    apply mem_normalizer_of_conj_mem
    intro u hu
    obtain ⟨x, hx, q, hq, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hu
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hay : a * y * a⁻¹ ∈ X ⊔ (Q ⊓ R) := by
      rcases hpm a ha with hcen | hinv
      · have : a * y * a⁻¹ = (a * y * a⁻¹ * y⁻¹) * y := by group
        rw [this]
        exact (X ⊔ (Q ⊓ R)).mul_mem
          (Subgroup.mem_sup_right (hQRB _ hcen (hRB_mul a (hA.1 ha) y hyB)))
          (Subgroup.mem_sup_left (Subgroup.mem_zpowers y))
      · have : a * y * a⁻¹ = (a * y * a⁻¹ * y) * y⁻¹ := by group
        rw [this]
        exact (X ⊔ (Q ⊓ R)).mul_mem
          (Subgroup.mem_sup_right (hQRB _ hinv (hRB_word a (hA.1 ha) y hyB)))
          (Subgroup.mem_sup_left (X.inv_mem (Subgroup.mem_zpowers y)))
    have : a * (y ^ m * q) * a⁻¹ = (a * y * a⁻¹) ^ m * (a * q * a⁻¹) := by
      rw [conj_zpow]; group
    rw [this]
    exact (X ⊔ (Q ⊓ R)).mul_mem ((X ⊔ (Q ⊓ R)).zpow_mem hay m)
      (Subgroup.mem_sup_right (hQRn.conj_mem q hq a))
  have hHRB : H ≤ R ⊔ (B : Subgroup G) :=
    sup_le (sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right hyB))
      (fun x hx => Subgroup.mem_sup_left hx.2)) (fun a ha => Subgroup.mem_sup_left (hA.1 ha))
  have hO2 : ∀ K : Subgroup G, K ≤ H → (∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) →
      IsPGroup 2 K → K ≤ P := by
    intro K hKH hKn hK2 k hk
    have hdec : (H : Set G) = (A : Set G) * ((X ⊔ (Q ⊓ R) : Subgroup G) : Set G) := by
      rw [hHdef, sup_comm, Subgroup.coe_mul_of_left_le_normalizer_right A (X ⊔ (Q ⊓ R)) hAXQ]
    have hk' : k ∈ (A : Set G) * ((X ⊔ (Q ⊓ R) : Subgroup G) : Set G) := by
      rw [← hdec]; exact hKH hk
    obtain ⟨a, ha, u, hu, rfl⟩ := Set.mem_mul.mp hk'
    obtain ⟨x, hx, q, hq, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hu
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hπk : π (a * (y ^ m * q)) = π a * π y ^ m := by
      rw [map_mul, map_mul, hπQ q hq.1, mul_one, map_zpow]
    have hc : a * (y ^ m * q) * y * (a * (y ^ m * q))⁻¹ * y⁻¹ ∈ K := by
      have h1 : y * (a * (y ^ m * q))⁻¹ * y⁻¹ ∈ K :=
        hKn y (Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers y))) _
          (K.inv_mem hk)
      have : a * (y ^ m * q) * y * (a * (y ^ m * q))⁻¹ * y⁻¹ =
          (a * (y ^ m * q)) * (y * (a * (y ^ m * q))⁻¹ * y⁻¹) := by group
      rw [this]
      exact K.mul_mem hk h1
    have hπc : π (a * (y ^ m * q) * y * (a * (y ^ m * q))⁻¹ * y⁻¹) =
        π a * π y * (π a)⁻¹ * (π y)⁻¹ := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hπk]
      group
    have haCy : a ∈ Cy := by
      rcases hpm a ha with hcen | hinv
      · exact (hmemCy a).mpr hcen
      · exfalso
        have h1 := (hinv_iff a).mp hinv
        have hval : π a * π y * (π a)⁻¹ * (π y)⁻¹ = π y := by
          rw [h1]
          calc (π y)⁻¹ * (π y)⁻¹ = (π y)⁻¹ * (π y)⁻¹ * π y ^ 3 := by rw [hπy3, mul_one]
            _ = π y := by group
        obtain ⟨j, hj⟩ := hK2 ⟨_, hc⟩
        have hj' : π y ^ 2 ^ j = 1 := by
          have := congrArg (fun x : K => π (x : G)) hj
          simp only [Subgroup.coe_pow, Subgroup.coe_one, map_pow, map_one] at this
          rwa [hπc, hval] at this
        have hdvd : orderOf (π y) ∣ Nat.gcd 3 (2 ^ j) :=
          Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hπy3) (orderOf_dvd_of_pow_eq_one hj')
        rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right j (by norm_num)), Nat.dvd_one,
          orderOf_eq_one_iff] at hdvd
        exact hπy1 hdvd
    have hπaπy : Commute (π a) (π y) := (hcomm_iff a).mp ((hmemCy a).mp haCy)
    have hπaym : Commute (π a) (π y ^ m) := hπaπy.zpow_right m
    have hπa2 : π a * π a = 1 := by rw [← map_mul, hA.2.1.2 a ha, map_one]
    obtain ⟨j, hj⟩ := hK2 ⟨_, hk⟩
    have hπkj : (π a * π y ^ m) ^ 2 ^ (j + 1) = 1 := by
      have := congrArg (fun x : K => π (x : G)) hj
      simp only [Subgroup.coe_pow, Subgroup.coe_one, map_pow, map_one] at this
      rw [hπk] at this
      rw [pow_succ, pow_mul, this, one_pow]
    have hπan : π a ^ 2 ^ (j + 1) = 1 := by
      rw [pow_succ', pow_mul, pow_two, hπa2, one_pow]
    have hym : (π y ^ m) ^ 2 ^ (j + 1) = 1 := by
      have := hπaym.mul_pow (2 ^ (j + 1))
      rw [hπkj, hπan, one_mul] at this
      exact this.symm
    have hym3 : (π y ^ m) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hπy3, one_zpow]
    have hdvd : orderOf (π y ^ m) ∣ Nat.gcd 3 (2 ^ (j + 1)) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hym3) (orderOf_dvd_of_pow_eq_one hym)
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right (j + 1) (by norm_num)), Nat.dvd_one,
      orderOf_eq_one_iff, ← map_zpow] at hdvd
    have hymQ : y ^ m ∈ Q := (QuotientGroup.eq_one_iff _).mp hdvd
    have hymR : y ^ m ∈ Q ⊓ R :=
      hQRB _ hymQ (Subgroup.mem_sup_right ((B : Subgroup G).zpow_mem hyB m))
    have : a * (y ^ m * q) = (a * (y ^ m * q) * a⁻¹) * a := by group
    rw [this]
    exact P.mul_mem (Subgroup.mem_sup_left (hQRn.conj_mem _ ((Q ⊓ R).mul_mem hymR hq) a))
      (Subgroup.mem_sup_right ⟨ha, haCy⟩)
  have hgen : ∀ N : Subgroup G, (∀ t ∈ (T : Subgroup G), ∀ n ∈ N, t * n * t⁻¹ ∈ N) →
      (∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) → N.Normal := by
    intro N hNT hNX
    have hNB : ∀ b ∈ (B : Subgroup G), ∀ n ∈ N, b * n * b⁻¹ ∈ N := by
      intro b hb n hn
      by_cases hb1 : b = 1
      · rw [hb1, one_mul, inv_one, mul_one]; exact hn
      obtain ⟨g, hgT, -, hgy⟩ :=
        exists_conj_eq_of_quaternion T B hB9 hBc hB3 hQ8 hyB hb hy1 hb1
      have h1 : g⁻¹ * n * g⁻¹⁻¹ ∈ N := hNT _ ((T : Subgroup G).inv_mem hgT) n hn
      have h2 := hNX y (Subgroup.mem_zpowers y) _ h1
      have h3 := hNT g hgT _ h2
      rw [← hgy, show g * y * g⁻¹ * n * (g * y * g⁻¹)⁻¹ =
        g * (y * (g⁻¹ * n * g⁻¹⁻¹) * y⁻¹) * g⁻¹ by group]
      exact h3
    constructor
    intro n hn g
    obtain ⟨t, ht, b, hb, rfl⟩ := hTB g
    have := hNT t ht _ (hNB b hb n hn)
    rw [show t * b * n * (t * b)⁻¹ = t * (b * n * b⁻¹) * t⁻¹ by group]
    exact this
  have hER : omegaG (jG R 1) ≤ R := (omegaG_le _).trans (jG_le _ _)
  have hEnS : ∀ t ∈ (T : Subgroup G), ∀ e ∈ omegaG (jG R 1), t * e * t⁻¹ ∈ omegaG (jG R 1) :=
    fun t ht e he => conj_mem_omegaG_jG_of_normalizes hRn ht he
  have hEH : omegaG (jG R 1) ≤ H := by
    intro e he
    have heT : e ∈ (T : Subgroup G) := hRT (hER he)
    rcases forall_mod_of_normal_elem T B hB9 hTB hBc hB3 hQ8
        (F := omegaG (jG R 1)) (fun t ht f hf => conj_mem_omegaG_jG_of_normalizes hRn ht hf)
        (fun f hf => hf.2.2) (fun f hf g hg => (isElemTwo_omegaG _).1 f hf g hg) he with
      hcen | hinv
    · have heQ : e ∈ Q := mem_of_forall_commute_mod T B hB9 hTB hBc hB3 heT hcen
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_right ⟨heQ, hER he⟩)
    · have hez : e * z⁻¹ ∈ Q :=
        mem_of_forall_commute_mod T B hB9 hTB hBc hB3
          ((T : Subgroup G).mul_mem heT ((T : Subgroup G).inv_mem (hRT (hA.1 hzA))))
          (fun b hb => mul_inv_conj_mem_of_inv hQn (hinv b hb) (hz b hb))
      have hezR : e * z⁻¹ ∈ R := R.mul_mem (hER he) (R.inv_mem (hA.1 hzA))
      have : e = (e * z⁻¹) * z := by group
      rw [this]
      exact H.mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_right ⟨hez, hezR⟩))
        (Subgroup.mem_sup_right hzA)
  have hWH : ∀ h ∈ H, ∀ w ∈ omegaG (pOne R P), h * w * h⁻¹ ∈ omegaG (pOne R P) :=
    fun h hh w hw => conj_mem_omegaG_pOne hPR (hHP h hh) (fun p hp => by
      have := hHP h⁻¹ (H.inv_mem hh) p hp
      rwa [inv_inv] at this) hw
  have hFP : CFSG.generalizedFitting G ⊓ (R ⊔ (B : Subgroup G)) ≤ P := by
    intro x hx
    rw [hF] at hx
    exact Subgroup.mem_sup_left ⟨hx.1, pCore_inf_sup_le hRT hRn hOR hOn hBOn hB3 hx⟩
  have hCP : ∀ h ∈ H, (∀ p ∈ P, h * p = p * h) → h ∈ P := fun h hh hc =>
    centralizer_le_of_fstar_le (sup_B_normal hRn hOR hBOn hTB) hFP (hHRB hh) hc
  have htX : ∀ x ∈ X, s * x * s⁻¹ * x ∈ Q ⊓ R := by
    intro x hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h1 := (hinv_iff s).mp hsy
    have hQs : s * y ^ m * s⁻¹ * y ^ m ∈ Q := by
      rw [← QuotientGroup.eq_one_iff]
      change π (s * y ^ m * s⁻¹ * y ^ m) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_zpow, ← conj_zpow, h1, inv_zpow,
        inv_mul_cancel]
    exact hQRB _ hQs (hRB_word s (hA.1 hsA) _ ((B : Subgroup G).zpow_mem hyB m))
  have hX3 : ∀ x ∈ X, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hB3 y hyB, one_zpow]
  have hXnc := not_centralizes_omegaG_pOne_R (R := R) (H := H) (P := P) (X := X)
    (S := (T : Subgroup G)) (A₁ := A ⊓ P) hPR hP2 hCP hHP hO2 hEH hEnS hgen hr hAP'
    inf_le_right hEnn
  have hQRp2 : IsPGroup 2 ((Q ⊓ R : Subgroup G)) := hQ2.to_le inf_le_left
  have hA' := sup_mem_famG (Q := (Q ⊓ R : Subgroup G)) hPR hQRp2 hA hAP' hsA htX hX3
    (fun x hx => hWH x (Subgroup.mem_sup_left (Subgroup.mem_sup_left hx)))
    (fun q hq => hWH q (Subgroup.mem_sup_left (Subgroup.mem_sup_right hq))) hXnc
  have hA'P : (A ⊓ P) ⊔ omegaG (pOne R P) ≤ P :=
    sup_le inf_le_right ((omegaG_le _).trans (pOne_le R P))
  have hcA' : c ∈ (A ⊓ P) ⊔ omegaG (pOne R P) :=
    Subgroup.mem_sup_left ⟨hcA, Subgroup.mem_sup_right ⟨hcA, (hmemCy c).mpr hcy⟩⟩
  have hrel : Q.relIndex ((A ⊓ P) ⊔ omegaG (pOne R P)) = 2 := by
    have hle := (Subgroup.relIndex_le_of_le_right hA'P (relIndex_ne_zero_of_finite Q P)).trans hPQ
    have hne1 : Q.relIndex ((A ⊓ P) ⊔ omegaG (pOne R P)) ≠ 1 := fun h =>
      hcQ (Subgroup.relIndex_eq_one.mp h hcA')
    have hne0 := relIndex_ne_zero_of_finite Q ((A ⊓ P) ⊔ omegaG (pOne R P))
    omega
  exact relIndex_ne_two_of_normal T B hRT hRn hOR hOn hBOn hTB hB9 hBc hB3 hF hQ8 hEnn hA' hrel

theorem omegaG_le_pCore_inf_of_normal {T : Sylow 2 G} {B : Sylow 3 G} {R O : Subgroup G}
    (hRT : R ≤ (T : Subgroup G))
    (hRn : ∀ t ∈ (T : Subgroup G), ∀ r ∈ R, t * r * t⁻¹ ∈ R)
    (hOR : O ≤ R) (hOn : O.Normal) (hBOn : ((B : Subgroup G) ⊔ O).Normal)
    (hTB : ∀ g : G, ∃ t ∈ (T : Subgroup G), ∃ b ∈ (B : Subgroup G), g = t * b)
    (hB3 : ∀ b ∈ (B : Subgroup G), b ^ 3 = 1)
    (hF : CFSG.generalizedFitting G = CFSG.pCore 2 G) :
    omegaG R ≤ omegaG (CFSG.pCore 2 G ⊓ R) := by
  have hHn : (R ⊔ (B : Subgroup G)).Normal := sup_B_normal hRn hOR hBOn hTB
  have hFP : CFSG.generalizedFitting G ⊓ (R ⊔ (B : Subgroup G)) ≤ CFSG.pCore 2 G ⊓ R := by
    intro x hx
    obtain ⟨hxF, hxH⟩ := Subgroup.mem_inf.mp hx
    rw [hF] at hxF
    exact Subgroup.mem_inf.mpr ⟨hxF,
      pCore_inf_sup_le hRT hRn hOR hOn hBOn hB3 (Subgroup.mem_inf.mpr ⟨hxF, hxH⟩)⟩
  intro z hz
  have hzQR : z ∈ CFSG.pCore 2 G ⊓ R :=
    centralizer_le_of_fstar_le hHn hFP (Subgroup.mem_sup_left hz.1)
      (fun p hp => hz.2.1 p (Subgroup.mem_inf.mp hp).2)
  exact ⟨hzQR, fun x hx => hz.2.1 x (Subgroup.mem_inf.mp hx).2, hz.2.2⟩

end RPort

theorem jG_normal_of_not_E {T : Sylow 2 G} {B : Sylow 3 G} {R O : Subgroup G}
    (hRT : R ≤ (T : Subgroup G))
    (hRn : ∀ t ∈ (T : Subgroup G), ∀ r ∈ R, t * r * t⁻¹ ∈ R)
    (hOR : O ≤ R) (hOn : O.Normal) (hBOn : ((B : Subgroup G) ⊔ O).Normal)
    (hTB : ∀ g : G, ∃ t ∈ (T : Subgroup G), ∃ b ∈ (B : Subgroup G), g = t * b)
    (hB9 : Nat.card (B : Subgroup G) = 9)
    (hBc : ∀ a ∈ (B : Subgroup G), ∀ b ∈ (B : Subgroup G), a * b = b * a)
    (hB3 : ∀ b ∈ (B : Subgroup G), b ^ 3 = 1)
    (hF : CFSG.generalizedFitting G = CFSG.pCore 2 G)
    (hQ8 : ∃ K : Subgroup (MulAut (B : Subgroup G)),
      K ≤ ((T : Subgroup G).subgroupOf (normalizer ((B : Subgroup G) : Set G))).map
        (B : Subgroup G).normalizerMonoidHom ∧ Nonempty (K ≃* QuaternionGroup 2))
    (hEnn : ¬ (omegaG (jG R 1)).Normal) : (jG R 0).Normal := by
  have hQRn : (CFSG.pCore 2 G ⊓ R).Normal :=
    pCore_inf_normal_of_normal hRT hRn hOR hOn hBOn hTB hB3
  apply jG_normal
  intro g A hA a ha
  have hAQ : A ≤ CFSG.pCore 2 G := by
    have hAT : A ≤ (T : Subgroup G) := hA.1.trans hRT
    have hk4 := relIndex_le_four T B hB9 hTB hBc hB3 hAT hA.2.1.2 hA.2.1.1
    have hkdvd : (CFSG.pCore 2 G).relIndex A ∣ 2 ^ (CFSG.pRank 2 R - 0) :=
      hA.2.2 ▸ Subgroup.relIndex_dvd_card (CFSG.pCore 2 G) A
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hkdvd
    have hjle : j ≤ 2 := by
      rw [hj] at hk4
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp (hk4.trans (by norm_num))
    interval_cases j
    · rw [pow_zero] at hj
      exact Subgroup.relIndex_eq_one.mp hj
    · exact (relIndex_ne_two_of_normal T B hRT hRn hOR hOn hBOn hTB hB9 hBc hB3 hF hQ8 hEnn
        hA (by simpa using hj)).elim
    · exact (relIndex_ne_four_of_normal T B hRT hRn hOR hOn hBOn hTB hB9 hBc hB3 hF hQ8 hEnn
        hA (by simpa using hj)).elim
  have haQR : a ∈ CFSG.pCore 2 G ⊓ R := Subgroup.mem_inf.mpr ⟨hAQ ha, hA.1 ha⟩
  exact (Subgroup.mem_inf.mp (hQRn.conj_mem a haQR g)).2

theorem rank3II_3_17_of_normal (T : Sylow 2 G) (B : Sylow 3 G) (R O : Subgroup G)
    (hRT : R ≤ (T : Subgroup G))
    (hRn : ∀ t ∈ (T : Subgroup G), ∀ r ∈ R, t * r * t⁻¹ ∈ R)
    (hOR : O ≤ R) (hOn : O.Normal) (hBOn : ((B : Subgroup G) ⊔ O).Normal)
    (hTB : ((T : Subgroup G) : Set G) * ((B : Subgroup G) : Set G) = Set.univ)
    (hB : CFSG.Assembly.IsElemAbelian 3 (B : Subgroup G)) (hB9 : Nat.card (B : Subgroup G) = 9)
    (hF : CFSG.generalizedFitting G = CFSG.pCore 2 G)
    (hQ8 : ∃ K : Subgroup (MulAut (B : Subgroup G)),
      K ≤ ((T : Subgroup G).subgroupOf (normalizer ((B : Subgroup G) : Set G))).map
        (B : Subgroup G).normalizerMonoidHom ∧ Nonempty (K ≃* QuaternionGroup 2)) :
    (omegaG R).Normal ∧ (jG R 0).Normal ∨ (omegaG R).Normal ∧ (omegaG (jG R 1)).Normal ∨
      (jG R 0).Normal ∧ (omegaG (jG R 1)).Normal := by
  have hTB' : ∀ g : G, ∃ t ∈ (T : Subgroup G), ∃ b ∈ (B : Subgroup G), g = t * b := by
    intro g
    have hg : g ∈ ((T : Subgroup G) : Set G) * ((B : Subgroup G) : Set G) := by
      rw [hTB]; exact Set.mem_univ g
    obtain ⟨t, ht, b, hb, h⟩ := Set.mem_mul.mp hg
    exact ⟨t, ht, b, hb, h.symm⟩
  have hBc : ∀ a ∈ (B : Subgroup G), ∀ b ∈ (B : Subgroup G), a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hB.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hB3 : ∀ b ∈ (B : Subgroup G), b ^ 3 = 1 := hB.2
  have hQRn : (CFSG.pCore 2 G ⊓ R).Normal :=
    pCore_inf_normal_of_normal hRT hRn hOR hOn hBOn hTB' hB3
  by_cases hV : ∃ b ∈ (B : Subgroup G), ∃ v ∈ omegaG (CFSG.pCore 2 G ⊓ R), b * v * b⁻¹ ≠ v
  ·
    have hall : ∀ i ≤ 1, ∀ g : G, ∀ A ∈ famG R i, ∀ a ∈ A, g * a * g⁻¹ ∈ R := by
      intro i hi g A hA a ha
      have haQR : a ∈ CFSG.pCore 2 G ⊓ R :=
        Subgroup.mem_inf.mpr ⟨le_pCore_of_mem_famG_of_normal T B hRT hRn hOR hOn hBOn hB9 hTB'
          hBc hB3 hQ8 hV hi hA ha, hA.1 ha⟩
      exact (Subgroup.mem_inf.mp (hQRn.conj_mem a haQR g)).2
    exact Or.inr (Or.inr ⟨jG_normal (hall 0 (Nat.zero_le 1)),
      omegaG_normal (jG_normal (hall 1 le_rfl))⟩)
  ·
    push Not at hV
    have hZQ : omegaG R ≤ omegaG (CFSG.pCore 2 G ⊓ R) :=
      omegaG_le_pCore_inf_of_normal hRT hRn hOR hOn hBOn hTB' hB3 hF
    have hZn : (omegaG R).Normal := by
      constructor
      intro z hz g
      obtain ⟨t, ht, b, hb, rfl⟩ := hTB' g
      rw [show t * b * z * (t * b)⁻¹ = t * (b * z * b⁻¹) * t⁻¹ by group,
        hV b hb z (hZQ hz)]
      exact conj_mem_omegaG_of_normalizes hRn ht hz
    by_cases hJn : (jG R 0).Normal
    · exact Or.inl ⟨hZn, hJn⟩
    · refine Or.inr (Or.inl ⟨hZn, ?_⟩)
      by_contra hEnn
      exact hJn (jG_normal_of_not_E hRT hRn hOR hOn hBOn hTB' hB9 hBc hB3 hF hQ8 hEnn)

end CFSG.RankThree.PartTwo.Sec3

end
