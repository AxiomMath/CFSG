module

public import CFSG.Quasithin.Recognition.HSTypeOutS5
public import CFSG.Quasithin.Recognition.HSType129e

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique

theorem perm_five_center : ∀ ρ : Equiv.Perm (Fin 5), ρ * Equiv.swap 0 1 = Equiv.swap 0 1 * ρ →
    ρ * Equiv.swap 1 2 = Equiv.swap 1 2 * ρ → ρ * Equiv.swap 2 3 = Equiv.swap 2 3 * ρ →
    ρ * Equiv.swap 3 4 = Equiv.swap 3 4 * ρ → ρ = 1 := by
  decide +kernel

theorem perm_four_center : ∀ ρ : Equiv.Perm (Fin 4), ρ * Equiv.swap 0 1 = Equiv.swap 0 1 * ρ →
    ρ * Equiv.swap 1 2 = Equiv.swap 1 2 * ρ → ρ * Equiv.swap 2 3 = Equiv.swap 2 3 * ρ →
    ρ = 1 := by
  decide +kernel

theorem perm_four_even_invol_conj : ∀ σ : Equiv.Perm (Fin 4), Equiv.Perm.sign σ = 1 →
    σ * σ = 1 → σ ≠ 1 →
      ∃ ρ : Equiv.Perm (Fin 4), ρ * σ * ρ⁻¹ = Equiv.swap 0 1 * Equiv.swap 2 3 := by
  decide +kernel

theorem perm_five_odd_mul_le_three : ∀ σ τ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = -1 →
    σ * σ = 1 → Equiv.Perm.sign τ = -1 → τ * τ = 1 → (σ * τ) ^ 2 = 1 ∨ (σ * τ) ^ 3 = 1 := by
  decide +kernel

theorem perm_four_odd_mul_le_three : ∀ σ τ : Equiv.Perm (Fin 4), Equiv.Perm.sign σ = -1 →
    σ * σ = 1 → Equiv.Perm.sign τ = -1 → τ * τ = 1 → (σ * τ) ^ 2 = 1 ∨ (σ * τ) ^ 3 = 1 := by
  decide +kernel

structure PermFacts (n : ℕ) : Prop where
  center : ∀ ρ : Equiv.Perm (Fin n), (∀ σ, ρ * σ = σ * ρ) → ρ = 1
  inner : ∀ φ : Equiv.Perm (Fin n) ≃* Equiv.Perm (Fin n), ∃ ρ, ∀ σ, φ σ = ρ * σ * ρ⁻¹
  even : ∀ σ τ : Equiv.Perm (Fin n), Equiv.Perm.sign σ = 1 → σ * σ = 1 → σ ≠ 1 →
    Equiv.Perm.sign τ = 1 → τ * τ = 1 → τ ≠ 1 → ∃ ρ, ρ * σ * ρ⁻¹ = τ
  odd : ∀ σ τ : Equiv.Perm (Fin n), Equiv.Perm.sign σ = -1 → σ * σ = 1 →
    Equiv.Perm.sign τ = -1 → τ * τ = 1 → (σ * τ) ^ 2 = 1 ∨ (σ * τ) ^ 3 = 1

theorem permFacts_five : PermFacts 5 where
  center ρ hρ := perm_five_center ρ (hρ _) (hρ _) (hρ _) (hρ _)
  inner := perm_five_aut_inner
  even σ τ hσ hσ2 hσ1 hτ hτ2 hτ1 := by
    obtain ⟨a, -, ha⟩ := alt_five_invol_conj σ hσ hσ2 hσ1
    obtain ⟨b, -, hb⟩ := alt_five_invol_conj τ hτ hτ2 hτ1
    refine ⟨b⁻¹ * a, ?_⟩
    calc b⁻¹ * a * σ * (b⁻¹ * a)⁻¹ = b⁻¹ * (a * σ * a⁻¹) * b := by group
      _ = b⁻¹ * (b * τ * b⁻¹) * b := by rw [ha, hb]
      _ = τ := by group
  odd := perm_five_odd_mul_le_three

theorem permFacts_four : PermFacts 4 where
  center ρ hρ := perm_four_center ρ (hρ _) (hρ _) (hρ _)
  inner := perm_four_aut_inner
  even σ τ hσ hσ2 hσ1 hτ hτ2 hτ1 := by
    obtain ⟨a, ha⟩ := perm_four_even_invol_conj σ hσ hσ2 hσ1
    obtain ⟨b, hb⟩ := perm_four_even_invol_conj τ hτ hτ2 hτ1
    refine ⟨b⁻¹ * a, ?_⟩
    calc b⁻¹ * a * σ * (b⁻¹ * a)⁻¹ = b⁻¹ * (a * σ * a⁻¹) * b := by group
      _ = b⁻¹ * (b * τ * b⁻¹) * b := by rw [ha, hb]
      _ = τ := by group
  odd := perm_four_odd_mul_le_three

section Conj

variable {G : Type*} [Group G] {x t : G}

theorem inv_conj_of_inverts (htx : t * x * t⁻¹ = x⁻¹) : t⁻¹ * x * t = x⁻¹ := by
  calc t⁻¹ * x * t = (t⁻¹ * x⁻¹ * t)⁻¹ := by group
    _ = (t⁻¹ * (t * x * t⁻¹) * t)⁻¹ := by rw [htx]
    _ = x⁻¹ := by group

theorem conj_mem_centralizer_of_inverts (htx : t * x * t⁻¹ = x⁻¹) {c : G}
    (hc : c ∈ Subgroup.centralizer ({x} : Set G)) :
    t * c * t⁻¹ ∈ Subgroup.centralizer ({x} : Set G) := by
  have hcx : c * x = x * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  have hcx' : c * x⁻¹ = x⁻¹ * c := by
    calc c * x⁻¹ = x⁻¹ * (x * c) * x⁻¹ := by group
      _ = x⁻¹ * (c * x) * x⁻¹ := by rw [hcx]
      _ = x⁻¹ * c := by group
  have h' := inv_conj_of_inverts htx
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  calc t * c * t⁻¹ * x = t * (c * (t⁻¹ * x * t)) * t⁻¹ := by group
    _ = t * (c * x⁻¹) * t⁻¹ := by rw [h']
    _ = t * (x⁻¹ * c) * t⁻¹ := by rw [hcx']
    _ = (t * x * t⁻¹)⁻¹ * (t * c * t⁻¹) := by group
    _ = x * (t * c * t⁻¹) := by rw [htx, inv_inv]

@[expose] def cenConjC (htx : t * x * t⁻¹ = x⁻¹) :
    ↥(Subgroup.centralizer ({x} : Set G)) ≃* ↥(Subgroup.centralizer ({x} : Set G)) where
  toFun c := ⟨t * c * t⁻¹, conj_mem_centralizer_of_inverts htx c.2⟩
  invFun c := ⟨t⁻¹ * c * t, by
    have := conj_mem_centralizer_of_inverts (t := t⁻¹)
      (by rw [inv_inv]; exact inv_conj_of_inverts htx) c.2
    rwa [inv_inv] at this⟩
  left_inv c := Subtype.ext (by simp only; group)
  right_inv c := Subtype.ext (by simp only; group)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem cenConjC_coe (htx : t * x * t⁻¹ = x⁻¹) (c : ↥(Subgroup.centralizer ({x} : Set G))) :
    ((cenConjC htx c : ↥(Subgroup.centralizer ({x} : Set G))) : G) = t * c * t⁻¹ := rfl

theorem map_cenX_cenConjC (htx : t * x * t⁻¹ = x⁻¹) :
    (cenX x).map (cenConjC htx).toMonoidHom = cenX x := by
  have hpow : ∀ k : ℤ, t * x ^ k * t⁻¹ = x ^ (-k) := fun k => by
    rw [← conj_zpow, htx, inv_zpow, zpow_neg]
  ext y
  constructor
  · rintro ⟨c, hc, rfl⟩
    have hc' : (c : G) ∈ Subgroup.zpowers x := mem_cenX.mp hc
    refine mem_cenX.mpr ?_
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc'
    rw [MulEquiv.coe_toMonoidHom, cenConjC_coe, ← hk, hpow]
    exact Subgroup.zpow_mem_zpowers x (-k)
  · intro hy
    have hy' : (y : G) ∈ Subgroup.zpowers x := mem_cenX.mp hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy'
    have hmem : x ^ (-k) ∈ Subgroup.centralizer ({x} : Set G) :=
      Subgroup.zpow_mem _ (Subgroup.mem_centralizer_singleton_iff.mpr rfl) _
    refine ⟨⟨x ^ (-k), hmem⟩, mem_cenX.mpr (Subgroup.zpow_mem_zpowers x (-k)), ?_⟩
    apply Subtype.ext
    rw [MulEquiv.coe_toMonoidHom, cenConjC_coe, hpow, neg_neg, hk]

@[expose] noncomputable def cenConj (htx : t * x * t⁻¹ = x⁻¹) : cenQuot x ≃* cenQuot x :=
  QuotientGroup.congr (cenX x) (cenX x) (cenConjC htx) (map_cenX_cenConjC htx)

theorem cenConj_mk (htx : t * x * t⁻¹ = x⁻¹) (c : ↥(Subgroup.centralizer ({x} : Set G))) :
    cenConj htx (QuotientGroup.mk c) = QuotientGroup.mk (cenConjC htx c) :=
  QuotientGroup.congr_mk _ _ _ _ c

end Conj

namespace HSSetting

variable {G : Type*} [Group G] {z : G} {V : Subgroup G}

theorem not_fix_mk_d [Finite G] (h : HSSetting z V) {x : G} (hxH : x ∈ hsH z)
    (hx3 : orderOf x = 3) {d u t : G} (hdH : d ∈ hsH z) (hdK : d ∉ hsK z) (hd2 : d * d = 1)
    (hdx : d * x = x * d) (huZ : u ∈ hsZQ z) (huu : u * u = z)
    (htx : t * x * t⁻¹ = x⁻¹) {g : G} (hgt : g * z * g⁻¹ = t)
    (hd : cenConj htx (QuotientGroup.mk ⟨d, Subgroup.mem_centralizer_singleton_iff.mpr hdx⟩) =
      QuotientGroup.mk ⟨d, Subgroup.mem_centralizer_singleton_iff.mpr hdx⟩)
    (hdu : ∀ hdu : d * u ∈ Subgroup.centralizer ({x} : Set G),
      cenConj htx (QuotientGroup.mk ⟨d * u, hdu⟩) = QuotientGroup.mk ⟨d * u, hdu⟩) : False := by
  set C := Subgroup.centralizer ({x} : Set G) with hC
  have hdC : d ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hdx
  have huC : u ∈ C := by
    have hle := h.hsD_le hxH hx3 hdH hdx
    exact (hle (Subgroup.mem_sup_left huZ)).2
  have hduC : d * u ∈ C := C.mul_mem hdC huC
  have hcomm : ∀ (a : G) (ha : a ∈ C), a * a = 1 →
      cenConj htx (QuotientGroup.mk ⟨a, ha⟩) = QuotientGroup.mk ⟨a, ha⟩ → t * a * t⁻¹ = a := by
    intro a ha ha2 hfix
    rw [cenConj_mk] at hfix
    have := eq_of_mk_eq_of_mul_self hx3 (a := cenConjC htx ⟨a, ha⟩) (b := ⟨a, ha⟩)
      (by
        rw [cenConjC_coe, show t * a * t⁻¹ * (t * a * t⁻¹) = t * (a * a) * t⁻¹ by group, ha2,
          mul_one, mul_inv_cancel])
      ha2 hfix
    exact congrArg Subtype.val this
  have hdu2 : d * u * (d * u) = 1 := by
    have hinv := h.inv_of_not_mem_K hdH hdK huZ
    calc d * u * (d * u) = (d * u * d⁻¹) * (d * d) * u := by group
      _ = 1 := by rw [hinv, hd2, mul_one, inv_mul_cancel]
  have htd := hcomm d hdC hd2 hd
  have htdu := hcomm (d * u) hduC hdu2 (hdu hduC)
  have htu : t * u * t⁻¹ = u := by
    calc t * u * t⁻¹ = (t * d * t⁻¹)⁻¹ * (t * (d * u) * t⁻¹) := by group
      _ = u := by rw [htd, htdu]; group
  have htH : t ∈ hsH z := by
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc t * z = t * (u * u) * t⁻¹ * t := by rw [huu]; group
      _ = (t * u * t⁻¹) * (t * u * t⁻¹) * t := by group
      _ = z * t := by rw [htu, huu]
  have htK : t ∈ hsK z := by
    refine ⟨htH, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    rw [← h.zpowers_eq_ZQ huZ (by
      intro hz
      rcases eq_one_or_eq_of_mem_zpowers h.orderOf_z hz with h1 | h1
      · rw [h1, one_mul] at huu
        exact h.z_ne_one huu.symm
      · rw [h1, h.z_mul_z] at huu
        exact h.z_ne_one huu.symm)] at hv
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    have : t * u ^ k * t⁻¹ = u ^ k := by rw [← conj_zpow, htu]
    calc u ^ k * t = t * u ^ k * t⁻¹ * t := by rw [this]
      _ = t * u ^ k := by group
  have htQ : t ∈ hsQ z := by
    rw [← hgt]
    exact h.mem_Q_of_conj_mem_K (hgt ▸ htK)
  have hxN : x ∈ Subgroup.normalizer (hsQ z : Set G) :=
    le_normalizer_quasithinGenFitting (hsH z) hxH
  have hmem : x * t⁻¹ * x⁻¹ ∈ hsQ z :=
    (Subgroup.mem_normalizer_iff.mp hxN t⁻¹).mp ((hsQ z).inv_mem htQ)
  have hc : t * (x * t⁻¹ * x⁻¹) ∈ hsQ z := (hsQ z).mul_mem htQ hmem
  have e : t * (x * t⁻¹ * x⁻¹) = x⁻¹ * x⁻¹ := by
    calc t * (x * t⁻¹ * x⁻¹) = (t * x * t⁻¹) * x⁻¹ := by group
      _ = x⁻¹ * x⁻¹ := by rw [htx]
  rw [e] at hc
  have hX : x⁻¹ * x⁻¹ ∈ Subgroup.zpowers x ⊓ hsQ z :=
    ⟨(Subgroup.zpowers x).mul_mem ((Subgroup.zpowers x).inv_mem (Subgroup.mem_zpowers x))
      ((Subgroup.zpowers x).inv_mem (Subgroup.mem_zpowers x)), hc⟩
  rw [h.zpowers_inf_Q hx3, Subgroup.mem_bot] at hX
  have hx2 : x ^ 2 = 1 := by
    rw [sq]
    calc x * x = (x⁻¹ * x⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv]
      _ = 1 := by rw [hX, inv_one]
  have hdvd := orderOf_dvd_of_pow_eq_one hx2
  rw [hx3] at hdvd
  norm_num at hdvd

theorem cenConj_conj {x t : G} (htx : t * x * t⁻¹ = x⁻¹)
    (k : ↥(Subgroup.centralizer ({x} : Set G)))
    (htx' : (k : G) * t * (k : G)⁻¹ * x * ((k : G) * t * (k : G)⁻¹)⁻¹ = x⁻¹) (y : cenQuot x) :
    cenConj htx' y = QuotientGroup.mk k *
      cenConj htx ((QuotientGroup.mk k)⁻¹ * y * QuotientGroup.mk k) * (QuotientGroup.mk k)⁻¹ := by
  obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, cenConj_mk,
    cenConj_mk, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  simp only [cenConjC_coe, Subgroup.coe_mul, Subgroup.coe_inv]
  group

theorem exists_inner_odd [Finite G] (h : HSSetting z V) {x : G} (hxH : x ∈ hsH z)
    (hx3 : orderOf x = 3) {n : ℕ} (hP : PermFacts n) (e : cenQuot x ≃* Equiv.Perm (Fin n))
    {t : G} (htt : t * t = 1) (htx : t * x * t⁻¹ = x⁻¹) {g : G} (hgt : g * z * g⁻¹ = t) :
    ∃ c : cenQuot x, (∀ y, cenConj htx y = c * y * c⁻¹) ∧ c * c = 1 ∧
      Equiv.Perm.sign (e c) = -1 := by
  classical
  set C := Subgroup.centralizer ({x} : Set G) with hC
  obtain ⟨ρ, hρ⟩ := hP.inner (e.symm.trans ((cenConj htx).trans e))
  obtain ⟨c, hc⟩ : ∃ c : cenQuot x, e c = ρ := ⟨e.symm ρ, e.apply_symm_apply ρ⟩
  have hcy : ∀ y, cenConj htx y = c * y * c⁻¹ := by
    intro y
    have := hρ (e y)
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at this
    apply e.injective
    rw [this, map_mul, map_mul, map_inv, hc]
  have hinvol : ∀ y, cenConj htx (cenConj htx y) = y := by
    intro y
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
    rw [cenConj_mk, cenConj_mk]
    congr 1
    apply Subtype.ext
    rw [cenConjC_coe, cenConjC_coe, show t * (t * (y' : G) * t⁻¹) * t⁻¹ =
      (t * t) * y' * (t * t)⁻¹ by group, htt]
    group
  have hcc : c * c = 1 := by
    have hcen : ∀ σ, e (c * c) * σ = σ * e (c * c) := by
      intro σ
      obtain ⟨y, rfl⟩ := e.surjective σ
      have h2 := hinvol y
      rw [hcy, hcy] at h2
      rw [← map_mul, ← map_mul]
      congr 1
      calc c * c * y = c * (c * y * c⁻¹) * c⁻¹ * (c * c) := by group
        _ = y * (c * c) := by rw [h2]
    have := hP.center _ hcen
    exact e.injective (by rw [this, map_one])
  refine ⟨c, hcy, hcc, ?_⟩
  rcases Int.units_eq_one_or (Equiv.Perm.sign (e c)) with hs | hs
  · exfalso
    obtain ⟨d, hdH, hdK, hd2, hdx⟩ := h.exists_invol_centralizer_three hxH hx3
    obtain ⟨u, huZ, hu1, huz, huu⟩ := h.exists_mem_ZQ_ne
    have hle := h.hsD_le hxH hx3 hdH hdx
    have hdC : d ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hdx
    have huC : u ∈ C := (hle (Subgroup.mem_sup_left huZ)).2
    have hzC : z ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hxH).symm
    set zb : cenQuot x := QuotientGroup.mk (⟨z, hzC⟩ : ↥C) with hzb
    have hzu : zb = QuotientGroup.mk (⟨u, huC⟩ : ↥C) * QuotientGroup.mk (⟨u, huC⟩ : ↥C) := by
      rw [hzb, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext huu.symm
    have hzb1 : zb ≠ 1 := by
      intro h1
      rw [hzb, cenQuot_mk_eq_one_iff] at h1
      have hz : z ∈ Subgroup.zpowers x ⊓ hsQ z := ⟨h1, h.mem_Q⟩
      rw [h.zpowers_inf_Q hx3, Subgroup.mem_bot] at hz
      exact h.z_ne_one hz
    have hzb2 : zb * zb = 1 := by
      rw [hzb, ← QuotientGroup.mk_mul, show (⟨z, hzC⟩ : ↥C) * ⟨z, hzC⟩ = 1 from
        Subtype.ext h.z_mul_z, QuotientGroup.mk_one]
    have hzs : Equiv.Perm.sign (e zb) = 1 := by
      rw [hzu, map_mul, Equiv.Perm.sign_mul, Int.units_mul_self]
    have hzcomm : ∀ (a : G) (ha : a ∈ C), a ∈ hsH z →
        zb * QuotientGroup.mk (⟨a, ha⟩ : ↥C) * zb⁻¹ = QuotientGroup.mk (⟨a, ha⟩ : ↥C) := by
      intro a ha haH
      rw [hzb, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← Subgroup.mem_centralizer_singleton_iff.mp haH]
      group
    have hduH : d * u ∈ hsH z := (hsH z).mul_mem hdH (h.Q_le_H huZ.1)
    obtain ⟨k, hk⟩ : ∃ k : ↥C, QuotientGroup.mk k * c * (QuotientGroup.mk k)⁻¹ = 1 ∨
        QuotientGroup.mk k * c * (QuotientGroup.mk k)⁻¹ = zb := by
      by_cases hc1 : e c = 1
      · refine ⟨1, Or.inl ?_⟩
        rw [QuotientGroup.mk_one, one_mul, inv_one, mul_one]
        exact e.injective (by rw [hc1, map_one])
      · have he2 : e c * e c = 1 := by rw [← map_mul, hcc, map_one]
        have hz1 : e zb ≠ 1 := fun h1 => hzb1 (e.injective (by rw [h1, map_one]))
        have hz2 : e zb * e zb = 1 := by rw [← map_mul, hzb2, map_one]
        obtain ⟨ρ', hρ'⟩ := hP.even _ _ hs he2 hc1 hzs hz2 hz1
        obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (e.symm ρ')
        refine ⟨k, Or.inr (e.injective ?_)⟩
        rw [map_mul, map_mul, map_inv, hk, MulEquiv.apply_symm_apply, hρ']
    have hkx : (k : G) * x = x * k := Subgroup.mem_centralizer_singleton_iff.mp k.2
    have htx' : (k : G) * t * (k : G)⁻¹ * x * ((k : G) * t * (k : G)⁻¹)⁻¹ = x⁻¹ := by
      have hkx' : (k : G)⁻¹ * x * k = x := by
        calc (k : G)⁻¹ * x * k = (k : G)⁻¹ * (x * k) := by group
          _ = (k : G)⁻¹ * (k * x) := by rw [hkx]
          _ = x := by group
      calc (k : G) * t * (k : G)⁻¹ * x * ((k : G) * t * (k : G)⁻¹)⁻¹ =
          k * (t * ((k : G)⁻¹ * x * k) * t⁻¹) * (k : G)⁻¹ := by group
        _ = k * x⁻¹ * (k : G)⁻¹ := by rw [hkx', htx]
        _ = (k * x * (k : G)⁻¹)⁻¹ := by group
        _ = x⁻¹ := by rw [hkx, mul_inv_cancel_right]
    have hgt' : (k * g) * z * (k * g)⁻¹ = (k : G) * t * (k : G)⁻¹ := by
      rw [← hgt]
      group
    have hact : ∀ y, cenConj htx' y =
        (QuotientGroup.mk k * c * (QuotientGroup.mk k)⁻¹) * y *
          (QuotientGroup.mk k * c * (QuotientGroup.mk k)⁻¹)⁻¹ := by
      intro y
      rw [cenConj_conj htx k htx' y, hcy]
      group
    have hfix : ∀ (a : G) (ha : a ∈ C), a ∈ hsH z →
        cenConj htx' (QuotientGroup.mk (⟨a, ha⟩ : ↥C)) = QuotientGroup.mk (⟨a, ha⟩ : ↥C) := by
      intro a ha haH
      rw [hact]
      rcases hk with hk | hk
      · rw [hk]
        group
      · rw [hk]
        exact hzcomm a ha haH
    exact h.not_fix_mk_d hxH hx3 hdH hdK hd2 hdx huZ huu htx' hgt'
      (hfix d hdC hdH) (fun hdu => hfix (d * u) hdu hduH)
  · exact hs

theorem mk_mul_pow_eq_one [Finite G] (h : HSSetting z V) {x : G} (hxH : x ∈ hsH z)
    (hx3 : orderOf x = 3) {n : ℕ} (hP : PermFacts n) (e : cenQuot x ≃* Equiv.Perm (Fin n))
    {t₁ t₂ : G} (ht₁ : t₁ * t₁ = 1) (ht₂ : t₂ * t₂ = 1) (ht₁x : t₁ * x * t₁⁻¹ = x⁻¹)
    (ht₂x : t₂ * x * t₂⁻¹ = x⁻¹) {g₁ g₂ : G} (hg₁ : g₁ * z * g₁⁻¹ = t₁)
    (hg₂ : g₂ * z * g₂⁻¹ = t₂) (hp : t₁ * t₂ ∈ Subgroup.centralizer ({x} : Set G)) :
    (QuotientGroup.mk (⟨t₁ * t₂, hp⟩ : ↥(Subgroup.centralizer ({x} : Set G))) : cenQuot x) ^ 2 = 1 ∨
      (QuotientGroup.mk (⟨t₁ * t₂, hp⟩ : ↥(Subgroup.centralizer ({x} : Set G))) :
        cenQuot x) ^ 3 = 1 := by
  obtain ⟨c₁, hc₁, hc₁₁, hs₁⟩ := h.exists_inner_odd hxH hx3 hP e ht₁ ht₁x hg₁
  obtain ⟨c₂, hc₂, hc₂₂, hs₂⟩ := h.exists_inner_odd hxH hx3 hP e ht₂ ht₂x hg₂
  set p : cenQuot x := QuotientGroup.mk (⟨t₁ * t₂, hp⟩ : ↥(Subgroup.centralizer ({x} : Set G)))
  have hpc : p = c₁ * c₂ := by
    have hcen : ∀ σ, e (p * (c₁ * c₂)⁻¹) * σ = σ * e (p * (c₁ * c₂)⁻¹) := by
      intro σ
      obtain ⟨y, rfl⟩ := e.surjective σ
      rw [← map_mul, ← map_mul]
      congr 1
      have hpy : ∀ y, p * y * p⁻¹ = cenConj ht₁x (cenConj ht₂x y) := by
        intro y
        obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
        rw [cenConj_mk, cenConj_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
          ← QuotientGroup.mk_mul]
        congr 1
        apply Subtype.ext
        simp only [cenConjC_coe, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      calc p * (c₁ * c₂)⁻¹ * y = p * ((c₁ * c₂)⁻¹ * y * (c₁ * c₂)) * p⁻¹ *
            (p * (c₁ * c₂)⁻¹) := by group
        _ = c₁ * (c₂ * ((c₁ * c₂)⁻¹ * y * (c₁ * c₂)) * c₂⁻¹) * c₁⁻¹ *
            (p * (c₁ * c₂)⁻¹) := by rw [hpy, hc₁, hc₂]
        _ = y * (p * (c₁ * c₂)⁻¹) := by group
    have := hP.center _ hcen
    have h1 : p * (c₁ * c₂)⁻¹ = 1 := e.injective (by rw [this, map_one])
    calc p = p * (c₁ * c₂)⁻¹ * (c₁ * c₂) := by group
      _ = c₁ * c₂ := by rw [h1, one_mul]
  have he₁ : e c₁ * e c₁ = 1 := by rw [← map_mul, hc₁₁, map_one]
  have he₂ : e c₂ * e c₂ = 1 := by rw [← map_mul, hc₂₂, map_one]
  rcases hP.odd _ _ hs₁ he₁ hs₂ he₂ with h2 | h3
  · left
    apply e.injective
    rw [map_pow, hpc, map_mul, h2, map_one]
  · right
    apply e.injective
    rw [map_pow, hpc, map_mul, h3, map_one]

end HSSetting

end CFSG.Quasithin.HSType
