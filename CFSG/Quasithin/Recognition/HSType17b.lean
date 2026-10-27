module

public import CFSG.Quasithin.Recognition.HSType17a

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique

section General

variable {G : Type*} [Group G]

abbrev cenMk {x : G} (y : G) (hy : y ∈ Subgroup.centralizer ({x} : Set G)) : cenQuot x :=
  QuotientGroup.mk (⟨y, hy⟩ : ↥(Subgroup.centralizer ({x} : Set G)))

theorem cenMk_eq_iff {x a b : G} (ha : a ∈ Subgroup.centralizer ({x} : Set G))
    (hb : b ∈ Subgroup.centralizer ({x} : Set G)) :
    cenMk a ha = cenMk b hb ↔ a⁻¹ * b ∈ Subgroup.zpowers x := by
  rw [QuotientGroup.eq, mem_cenX]
  rfl

theorem mem_centralizer_of_inverts_mul {x t c : G} (htx : t * x * t⁻¹ = x⁻¹)
    (hc : c ∈ Subgroup.centralizer ({x} : Set G)) :
    c * t * x * (c * t)⁻¹ = x⁻¹ := by
  have hcx : c * x = x * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  have hcx' : c * x⁻¹ = x⁻¹ * c := by
    calc c * x⁻¹ = x⁻¹ * (x * c) * x⁻¹ := by group
      _ = x⁻¹ * (c * x) * x⁻¹ := by rw [hcx]
      _ = x⁻¹ * c := by group
  calc c * t * x * (c * t)⁻¹ = c * (t * x * t⁻¹) * c⁻¹ := by group
    _ = c * x⁻¹ * c⁻¹ := by rw [htx]
    _ = x⁻¹ := by rw [hcx']; group

theorem exists_t1 {x i : G} (hx3 : orderOf x = 3) (hii : i * i = 1) (hix : i * x * i⁻¹ = x⁻¹)
    {c : cenQuot x} (hc : ∀ y, cenConj hix y = c * y * c⁻¹) (hcc : c * c = 1) :
    ∃ c₀ : G, ∃ hc₀ : c₀ ∈ Subgroup.centralizer ({x} : Set G), cenMk c₀ hc₀ = c ∧
      (c₀⁻¹ * i) * (c₀⁻¹ * i) = 1 ∧ (c₀⁻¹ * i) * x * (c₀⁻¹ * i)⁻¹ = x⁻¹ ∧
      ∀ y ∈ Subgroup.centralizer ({x} : Set G),
        y⁻¹ * ((c₀⁻¹ * i) * y * (c₀⁻¹ * i)⁻¹) ∈ Subgroup.zpowers x := by
  obtain ⟨⟨c₀, hc₀⟩, rfl⟩ := QuotientGroup.mk_surjective c
  have hc₀' : c₀⁻¹ ∈ Subgroup.centralizer ({x} : Set G) := Subgroup.inv_mem _ hc₀
  have htx : (c₀⁻¹ * i) * x * (c₀⁻¹ * i)⁻¹ = x⁻¹ := mem_centralizer_of_inverts_mul hix hc₀'
  have hcx : c₀ * x = x * c₀ := Subgroup.mem_centralizer_singleton_iff.mp hc₀
  have hck : ∀ m : ℤ, c₀⁻¹ * x ^ m * c₀ = x ^ m := fun m => by
    rw [mul_assoc, ← (Commute.zpow_right (show Commute c₀ x from hcx) m).eq,
      inv_mul_cancel_left]
  have hii' : i⁻¹ = i := inv_eq_of_mul_eq_one_left hii
  have hact : ∀ y ∈ Subgroup.centralizer ({x} : Set G),
      y⁻¹ * ((c₀⁻¹ * i) * y * (c₀⁻¹ * i)⁻¹) ∈ Subgroup.zpowers x := by
    intro y hy
    have h1 := hc (QuotientGroup.mk ⟨y, hy⟩)
    rw [cenConj_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      QuotientGroup.eq, mem_cenX] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, cenConjC_coe] at h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    have ha : i * y * i⁻¹ = c₀ * y * c₀⁻¹ * x ^ (-k) := by
      rw [zpow_neg, hk]
      group
    refine Subgroup.mem_zpowers_iff.mpr ⟨-k, ?_⟩
    calc x ^ (-k) = c₀⁻¹ * x ^ (-k) * c₀ := (hck _).symm
      _ = y⁻¹ * c₀⁻¹ * (c₀ * y * c₀⁻¹ * x ^ (-k)) * c₀ := by group
      _ = y⁻¹ * c₀⁻¹ * (i * y * i⁻¹) * c₀ := by rw [ha]
      _ = y⁻¹ * ((c₀⁻¹ * i) * y * (c₀⁻¹ * i)⁻¹) := by group
  have ht2 : (c₀⁻¹ * i) * (c₀⁻¹ * i) = 1 := by
    set T2 : ↥(Subgroup.centralizer ({x} : Set G)) :=
      ⟨c₀⁻¹, hc₀'⟩ * cenConjC hix ⟨c₀⁻¹, hc₀'⟩ with hT2
    have hT2c : (T2 : G) = (c₀⁻¹ * i) * (c₀⁻¹ * i) := by
      rw [hT2, Subgroup.coe_mul, cenConjC_coe, hii']
      group
    have hT2m : (QuotientGroup.mk T2 : cenQuot x) = 1 := by
      rw [hT2, QuotientGroup.mk_mul, ← cenConj_mk, hc,
        show (QuotientGroup.mk ⟨c₀⁻¹, hc₀'⟩ : cenQuot x) =
          (QuotientGroup.mk ⟨c₀, hc₀⟩ : cenQuot x)⁻¹ from rfl]
      calc (QuotientGroup.mk ⟨c₀, hc₀⟩ : cenQuot x)⁻¹ *
            ((QuotientGroup.mk ⟨c₀, hc₀⟩ : cenQuot x) * (QuotientGroup.mk ⟨c₀, hc₀⟩)⁻¹ *
              (QuotientGroup.mk ⟨c₀, hc₀⟩)⁻¹) =
          ((QuotientGroup.mk ⟨c₀, hc₀⟩ : cenQuot x) * QuotientGroup.mk ⟨c₀, hc₀⟩)⁻¹ := by
            group
        _ = 1 := by rw [hcc, inv_one]
    have hcl : (c₀⁻¹ * i) * (c₀⁻¹ * i) ∈ Subgroup.zpowers x := by
      rw [← hT2c]
      exact (cenQuot_mk_eq_one_iff T2).mp hT2m
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcl
    have hinv : (c₀⁻¹ * i) * x ^ k * (c₀⁻¹ * i)⁻¹ = (x ^ k)⁻¹ := by
      rw [← conj_zpow, htx, inv_zpow]
    have hcomm : (c₀⁻¹ * i) * x ^ k * (c₀⁻¹ * i)⁻¹ = x ^ k := by
      rw [hk]; group
    have hh : (x ^ k)⁻¹ = x ^ k := hinv.symm.trans hcomm
    have h2 : x ^ k * x ^ k = 1 := by
      calc x ^ k * x ^ k = x ^ k * (x ^ k)⁻¹ := by rw [hh]
        _ = 1 := mul_inv_cancel _
    have h1 : x ^ k = 1 := by
      have h3 : (x ^ k) ^ 3 = 1 := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hx3,
          pow_orderOf_eq_one, one_zpow]
      calc x ^ k = (x ^ k) ^ 3 * (x ^ k * x ^ k)⁻¹ := by group
        _ = 1 := by rw [h3, h2]; group
    rw [← hk, h1]
  exact ⟨c₀, hc₀, rfl, ht2, htx, hact⟩

end General

theorem perm_five_exists_tau : ∀ σ : Equiv.Perm (Fin 5), σ ^ 4 = 1 → σ ^ 2 ≠ 1 →
    ∃ τ : Equiv.Perm (Fin 5), τ * τ = 1 ∧ Equiv.Perm.sign τ = -1 ∧ τ * σ ^ 2 = σ ^ 2 * τ ∧
      ∃ ρ : Equiv.Perm (Fin 5), ρ ^ 3 = 1 ∧ ρ ≠ 1 ∧ ρ * τ = τ * ρ := by
  decide +kernel

theorem perm_five_exists_s : ∀ σ : Equiv.Perm (Fin 5), σ ^ 4 = 1 → σ ^ 2 ≠ 1 →
    ∃ ρ : Equiv.Perm (Fin 5), ρ * ρ = 1 ∧ Equiv.Perm.sign ρ = 1 ∧ ρ ≠ 1 ∧ ρ ≠ σ ^ 2 ∧
      ρ * σ ^ 2 = σ ^ 2 * ρ ∧ ρ * σ * ρ⁻¹ = σ⁻¹ := by
  decide +kernel

theorem perm_five_odd_invol_conj_swap : ∀ σ : Equiv.Perm (Fin 5), σ * σ = 1 →
    Equiv.Perm.sign σ = -1 → ∃ ρ : Equiv.Perm (Fin 5), ρ * σ * ρ⁻¹ = Equiv.swap 0 1 := by
  decide +kernel

theorem perm_five_odd_invol_conj' (σ τ : Equiv.Perm (Fin 5)) (hσ : σ * σ = 1)
    (hσs : Equiv.Perm.sign σ = -1) (hτ : τ * τ = 1) (hτs : Equiv.Perm.sign τ = -1) :
    ∃ ρ : Equiv.Perm (Fin 5), ρ * σ * ρ⁻¹ = τ := by
  obtain ⟨a, ha⟩ := perm_five_odd_invol_conj_swap σ hσ hσs
  obtain ⟨b, hb⟩ := perm_five_odd_invol_conj_swap τ hτ hτs
  refine ⟨b⁻¹ * a, ?_⟩
  calc b⁻¹ * a * σ * (b⁻¹ * a)⁻¹ = b⁻¹ * (a * σ * a⁻¹) * b := by group
    _ = b⁻¹ * (b * τ * b⁻¹) * b := by rw [ha, hb]
    _ = τ := by group

section Y

variable {G : Type*} [Group G]

abbrev cenY (x t : G) : Subgroup G :=
  Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({t} : Set G)

@[expose] noncomputable def cenYProj (x t : G) : ↥(cenY x t) →* cenQuot x :=
  (QuotientGroup.mk' (cenX x)).comp (Subgroup.inclusion inf_le_left)

theorem cenYProj_apply (x t : G) (y : ↥(cenY x t)) :
    cenYProj x t y = cenMk (y : G) y.2.1 := rfl

theorem cenYProj_bijective {x t : G} (hx3 : orderOf x = 3) (htx : t * x * t⁻¹ = x⁻¹)
    (htriv : ∀ y ∈ Subgroup.centralizer ({x} : Set G),
      y⁻¹ * (t * y * t⁻¹) ∈ Subgroup.zpowers x) :
    Function.Bijective (cenYProj x t) := by
  have hpow3 : ∀ k : ℤ, (x ^ k) ^ 3 = 1 := fun k => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hx3,
      pow_orderOf_eq_one, one_zpow]
  have hinvk : ∀ k : ℤ, t * x ^ k * t⁻¹ = (x ^ k)⁻¹ := fun k => by
    rw [← conj_zpow, htx, inv_zpow]
  constructor
  · rw [injective_iff_map_eq_one]
    intro y hy
    rw [cenYProj_apply, cenMk, cenQuot_mk_eq_one_iff] at hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hyt : (y : G) * t = t * y := Subgroup.mem_centralizer_singleton_iff.mp y.2.2
    have h2 : x ^ k * x ^ k = 1 := by
      have e : t * x ^ k * t⁻¹ = x ^ k := by
        rw [hk, ← hyt]; group
      rw [hinvk] at e
      calc x ^ k * x ^ k = x ^ k * (x ^ k)⁻¹ := by rw [e]
        _ = 1 := mul_inv_cancel _
    have h1 : x ^ k = 1 := by
      calc x ^ k = (x ^ k) ^ 3 * (x ^ k * x ^ k)⁻¹ := by group
        _ = 1 := by rw [hpow3, h2]; group
    exact Subtype.ext (by rw [← hk, h1]; rfl)
  · intro c
    obtain ⟨⟨c, hc⟩, rfl⟩ := QuotientGroup.mk_surjective c
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (htriv c hc)
    have hxC : x ∈ Subgroup.centralizer ({x} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr rfl
    have hcx : c * x = x * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    have hc' : c * x ^ (2 * k) ∈ cenY x t := by
      refine ⟨Subgroup.mul_mem _ hc (Subgroup.zpow_mem _ hxC _), ?_⟩
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have htc : t * c * t⁻¹ = c * x ^ k := by rw [hk]; group
      have e : t * (c * x ^ (2 * k)) * t⁻¹ = c * x ^ (2 * k) := by
        calc t * (c * x ^ (2 * k)) * t⁻¹ = (t * c * t⁻¹) * (t * x ^ (2 * k) * t⁻¹) := by group
          _ = c * x ^ k * (x ^ (2 * k))⁻¹ := by rw [htc, hinvk]
          _ = c * x ^ (2 * k) * ((x ^ k) ^ 3)⁻¹ := by
              rw [← zpow_natCast, ← zpow_mul, ← zpow_neg]; group
          _ = c * x ^ (2 * k) := by rw [hpow3, inv_one, mul_one]
      calc c * x ^ (2 * k) * t = t * (c * x ^ (2 * k)) * t⁻¹ * t := by rw [e]
        _ = t * (c * x ^ (2 * k)) := by group
    refine ⟨⟨_, hc'⟩, ?_⟩
    rw [cenYProj_apply, cenMk_eq_iff]
    refine Subgroup.mem_zpowers_iff.mpr ⟨-(2 * k), ?_⟩
    simp only [mul_inv_rev, zpow_neg]
    group

@[expose] noncomputable def cenYEquiv {x t : G} (hx3 : orderOf x = 3) (htx : t * x * t⁻¹ = x⁻¹)
    (htriv : ∀ y ∈ Subgroup.centralizer ({x} : Set G),
      y⁻¹ * (t * y * t⁻¹) ∈ Subgroup.zpowers x) : ↥(cenY x t) ≃* cenQuot x :=
  MulEquiv.ofBijective (cenYProj x t) (cenYProj_bijective hx3 htx htriv)

end Y

namespace HSSetting

variable {G : Type} [Group G] {z : G} {V : Subgroup G}

theorem t1_facts [Finite G] (h : HSSetting z V) {x : G} (hxH : x ∈ hsH z) (hx3 : orderOf x = 3)
    (e : cenQuot x ≃* Equiv.Perm (Fin 5)) {t : G} (htt : t * t = 1) (htx : t * x * t⁻¹ = x⁻¹)
    (htriv : ∀ y ∈ Subgroup.centralizer ({x} : Set G),
      y⁻¹ * (t * y * t⁻¹) ∈ Subgroup.zpowers x) :
    t ∈ hsK z ∧ t ∉ hsQ z ∧ (∀ g : G, g * z * g⁻¹ ≠ t) := by
  have hzz : z * z = 1 := h.z_mul_z
  have htz : ∀ g : G, g * z * g⁻¹ ≠ t := by
    intro g hg
    obtain ⟨c, hc, -, hsc⟩ := h.exists_inner_odd hxH hx3 permFacts_five e htt htx hg
    have hfix : ∀ y : cenQuot x, cenConj htx y = y := by
      intro y
      obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective y
      rw [cenConj_mk]
      apply (QuotientGroup.eq).mpr
      rw [mem_cenX]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, cenConjC_coe]
      have := Subgroup.inv_mem _ (htriv y hy)
      rwa [show (y⁻¹ * (t * y * t⁻¹))⁻¹ = (t * y * t⁻¹)⁻¹ * y by group] at this
    have hcen : ∀ σ, e c * σ = σ * e c := by
      intro σ
      obtain ⟨y, rfl⟩ := e.surjective σ
      have h1 := hc y
      rw [hfix] at h1
      rw [← map_mul, ← map_mul]
      congr 1
      calc c * y = c * y * c⁻¹ * c := by group
        _ = y * c := by rw [← h1]
    have := permFacts_five.center (e c) hcen
    rw [this, Equiv.Perm.sign_one] at hsc
    exact absurd hsc (by decide)
  have hzC : z ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp hxH).symm
  have htzC := conj_mem_centralizer_of_inverts htx hzC
  have htzt : t * z * t⁻¹ = z := by
    have hz2 : z * z = 1 := hzz
    have htz2 : t * z * t⁻¹ * (t * z * t⁻¹) = 1 := by
      calc t * z * t⁻¹ * (t * z * t⁻¹) = t * (z * z) * t⁻¹ := by group
        _ = 1 := by rw [hzz, mul_one, mul_inv_cancel]
    have := eq_of_mk_eq_of_mul_self hx3 (a := ⟨t * z * t⁻¹, htzC⟩) (b := ⟨z, hzC⟩) htz2 hz2
      ((cenMk_eq_iff htzC hzC).mpr (by
        have := Subgroup.inv_mem _ (htriv z hzC)
        rwa [show (z⁻¹ * (t * z * t⁻¹))⁻¹ = (t * z * t⁻¹)⁻¹ * z by group] at this))
    exact congrArg Subtype.val this
  have htH : t ∈ hsH z := by
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc t * z = t * z * t⁻¹ * t := by group
      _ = z * t := by rw [htzt]
  obtain ⟨w, hwZ, hw1, hwz', hww⟩ := h.exists_mem_ZQ_ne
  have hwz : w ∉ Subgroup.zpowers z := by
    intro hwz
    rcases eq_one_or_eq_of_mem_zpowers h.orderOf_z hwz with h1 | h1
    · exact hw1 h1
    · exact hwz' h1
  have hwC : w ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [← h.centralizer_Q_eq_ZQ_of_orderOf_three hxH hx3] at hwZ
    exact hwZ.2
  have htwt : t * w * t⁻¹ = w := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (htriv w hwC)
    have hwk : t * w * t⁻¹ = w * x ^ k := by rw [hk]; group
    have hwx : Commute w (x ^ k) :=
      Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp hwC) k
    have hw4 : w ^ 4 = 1 := by
      have e4 : w ^ 4 = (w ^ 2) ^ 2 := by rw [← pow_mul]
      rw [e4, sq w, hww, sq, hzz]
    have hx3k : (x ^ k) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hx3,
        pow_orderOf_eq_one, one_zpow]
    have h4 : (t * w * t⁻¹) ^ 4 = 1 := by rw [conj_pow, hw4]; group
    rw [hwk, hwx.mul_pow, hw4, one_mul, show (4 : ℕ) = 3 + 1 from rfl, pow_succ, hx3k,
      one_mul] at h4
    rw [hwk, h4, mul_one]
  have htK : t ∈ hsK z := by
    refine ⟨htH, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    rw [← h.zpowers_eq_ZQ hwZ hwz] at hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    have hc : Commute t w := by
      show t * w = w * t
      calc t * w = t * w * t⁻¹ * t := by group
        _ = w * t := by rw [htwt]
    exact (hc.zpow_right k).eq.symm
  have ht1 : t ≠ 1 := by
    intro h1
    rw [h1, one_mul, inv_one, mul_one] at htx
    have : x * x = 1 := by
      calc x * x = x * x⁻¹ := by rw [← htx]
        _ = 1 := mul_inv_cancel x
    have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact this)
    rw [hx3] at h2
    exact absurd h2 (by decide)
  have htQ : t ∉ hsQ z := by
    intro htQ
    by_cases htZ : t ∈ hsZQ z
    · apply htz 1
      rw [h.eq_z_of_mem_ZQ htZ htt ht1]
      group
    · obtain ⟨c, hc⟩ := h.exists_conj_z_of_invol_Q htQ htt htZ
      exact htz c hc
  exact ⟨htK, htQ, htz⟩

theorem exists_t_data
    [Finite G] (h : HSSetting z V) :
    ∃ t : G, t ∈ hsK z ∧ t ∉ hsQ z ∧ t * t = 1 ∧ (∀ g : G, g * z * g⁻¹ ≠ t) ∧
      ∃ A : Subgroup G, A ≤ Subgroup.centralizer ({t} : Set G) ∧
        Nonempty (↥A ≃* alternatingGroup (Fin 5)) ∧ z ∈ A ∧
        A ≤ Subgroup.closure {g : G | g ∈ Subgroup.centralizer ({t} : Set G) ∧ orderOf g = 3} ∧
        (∃ s ∈ A, s * s = 1 ∧ s ≠ 1 ∧ s ≠ z ∧ s * z = z * s ∧ s ∉ hsK z) ∧
        ∃ τ y : G, τ * τ = 1 ∧ τ * z = z * τ ∧ τ * t = t * τ ∧ y * t = t * y ∧
          y * τ = τ * y ∧ orderOf y = 3 ∧ ∃ g : G, g * z * g⁻¹ = t * τ := by
  classical
  have hzz : z * z = 1 := h.z_mul_z
  obtain ⟨x, hxH, hx3, ⟨e⟩, i, hii, hix, gi, hgi⟩ := h.exists_three_s5
  obtain ⟨c, hc, hcc, hsc⟩ := h.exists_inner_odd hxH hx3 permFacts_five e hii hix hgi
  obtain ⟨c₀, hc₀, hc₀c, htt, htx, htriv⟩ := exists_t1 hx3 hii hix hc hcc
  set t := c₀⁻¹ * i with ht
  obtain ⟨htK, htQ, htz⟩ := h.t1_facts hxH hx3 e htt htx htriv
  set ψ : ↥(cenY x t) ≃* Equiv.Perm (Fin 5) := (cenYEquiv hx3 htx htriv).trans e with hψ
  have hψapp : ∀ y : ↥(cenY x t), ψ y = e (cenMk (y : G) y.2.1) := fun _ => rfl
  obtain ⟨w, hwZ, hw1, hwz', hww⟩ := h.exists_mem_ZQ_ne
  have hzC : z ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp hxH).symm
  have hzt : z ∈ Subgroup.centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp htK.1).symm
  have hwC : w ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [← h.centralizer_Q_eq_ZQ_of_orderOf_three hxH hx3] at hwZ
    exact hwZ.2
  have hwt : w ∈ Subgroup.centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp htK.2 w hwZ)
  set zY : ↥(cenY x t) := ⟨z, hzC, hzt⟩
  set wY : ↥(cenY x t) := ⟨w, hwC, hwt⟩
  have hzw : zY = wY ^ 2 := Subtype.ext (by simp [zY, wY, sq, hww])
  have hw4 : wY ^ 4 = 1 := Subtype.ext (by
    have e4 : w ^ 4 = (w ^ 2) ^ 2 := by rw [← pow_mul]
    simp only [Subgroup.coe_pow, Subgroup.coe_one, wY]
    rw [e4, sq w, hww, sq, hzz])
  have hzY1 : zY ≠ 1 := fun h1 => h.z_ne_one (congrArg Subtype.val h1)
  have hσ4 : ψ wY ^ 4 = 1 := by rw [← map_pow, hw4, map_one]
  have hσ2 : ψ wY ^ 2 ≠ 1 := by
    rw [← map_pow, ← hzw]
    exact fun h1 => hzY1 (ψ.injective (by rw [h1, map_one]))
  have hψz : ψ zY = ψ wY ^ 2 := by rw [hzw, map_pow]
  obtain ⟨τσ, hτ2, hτs, hτz, ρ, hρ3, hρ1, hρτ⟩ := perm_five_exists_tau (ψ wY) hσ4 hσ2
  obtain ⟨σs, hs2, hss, hs1, hsz, hszc, hsw⟩ := perm_five_exists_s (ψ wY) hσ4 hσ2
  set τY := ψ.symm τσ
  set yY := ψ.symm ρ
  set sY := ψ.symm σs
  have hψτ : ψ τY = τσ := ψ.apply_symm_apply _
  have hψy : ψ yY = ρ := ψ.apply_symm_apply _
  have hψs : ψ sY = σs := ψ.apply_symm_apply _
  have lift : ∀ a b : ↥(cenY x t), ψ a = ψ b → (a : G) = b := fun a b hab =>
    congrArg Subtype.val (ψ.injective hab)
  set A' : Subgroup ↥(cenY x t) := (alternatingGroup (Fin 5)).map ψ.symm.toMonoidHom
  set A : Subgroup G := A'.map (cenY x t).subtype with hA
  have hmemA : ∀ σ ∈ alternatingGroup (Fin 5), ((ψ.symm σ : ↥(cenY x t)) : G) ∈ A :=
    fun σ hσ => ⟨ψ.symm σ, ⟨σ, hσ, rfl⟩, rfl⟩
  have hAt : A ≤ Subgroup.centralizer ({t} : Set G) := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2.2
  have hAiso : Nonempty (↥A ≃* alternatingGroup (Fin 5)) := by
    refine ⟨(((alternatingGroup (Fin 5)).equivMapOfInjective ψ.symm.toMonoidHom
      ψ.symm.injective).trans (A'.equivMapOfInjective (cenY x t).subtype
        (cenY x t).subtype_injective)).symm⟩
  have hzA : z ∈ A := by
    have e1 : zY = ψ.symm (ψ wY ^ 2) := by rw [← hψz, ψ.symm_apply_apply]
    have : (zY : G) ∈ A := by
      rw [e1]
      exact hmemA _ (by rw [Equiv.Perm.mem_alternatingGroup, map_pow, Int.units_sq])
    exact this
  have hAcl : A ≤ Subgroup.closure
      {g : G | g ∈ Subgroup.centralizer ({t} : Set G) ∧ orderOf g = 3} := by
    rw [hA, Subgroup.map_map, ← Equiv.Perm.closure_three_cycles_eq_alternating,
      MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨σ, hσ, rfl⟩
    refine ⟨(ψ.symm σ).2.2, ?_⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      MulEquiv.coe_toMonoidHom]
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hσ.orderOf]
  have hsA : (sY : G) ∈ A := hmemA _ (by rw [Equiv.Perm.mem_alternatingGroup]; exact hss)
  have hsY2 : (sY : G) * sY = 1 := by
    have := lift (sY * sY) 1 (by rw [map_mul, hψs, hs2, map_one])
    simpa using this
  have hsY1 : (sY : G) ≠ 1 := fun h1 => hs1 (by
    rw [← hψs, show sY = 1 from Subtype.ext h1, map_one])
  have hsYz : (sY : G) ≠ z := fun h1 => hsz (by
    rw [← hψs, show sY = zY from Subtype.ext h1, hψz])
  have hsYzc : (sY : G) * z = z * sY := by
    have := lift (sY * zY) (zY * sY) (by rw [map_mul, map_mul, hψs, hψz, hszc])
    simpa using this
  have hsYw : (sY : G) * w * (sY : G)⁻¹ = w⁻¹ := by
    have := lift (sY * wY * sY⁻¹) wY⁻¹ (by
      rw [map_mul, map_mul, map_inv, map_inv, hψs, hsw])
    simpa using this
  have hsK : (sY : G) ∉ hsK z := by
    intro hsK
    have hc := Subgroup.mem_centralizer_iff.mp hsK.2 w hwZ
    have : w = w⁻¹ := by rw [← hsYw, ← hc, mul_inv_cancel_right]
    apply hw1
    have hw2 : w * w = 1 := by
      calc w * w = w * w⁻¹ := by rw [← this]
        _ = 1 := mul_inv_cancel w
    rw [hww] at hw2
    exact absurd hw2 h.z_ne_one
  have hτY2 : (τY : G) * τY = 1 := by
    have := lift (τY * τY) 1 (by rw [map_mul, hψτ, hτ2, map_one])
    simpa using this
  have hτYz : (τY : G) * z = z * τY := by
    have := lift (τY * zY) (zY * τY) (by rw [map_mul, map_mul, hψτ, hψz, hτz])
    simpa using this
  have hyτ : (yY : G) * τY = τY * yY := by
    have := lift (yY * τY) (τY * yY) (by rw [map_mul, map_mul, hψτ, hψy, hρτ])
    simpa using this
  have hy3 : orderOf (yY : G) = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq ψ, hψy]
    exact orderOf_eq_prime hρ3 hρ1
  have hτt : (τY : G) * t = t * τY := Subgroup.mem_centralizer_singleton_iff.mp τY.2.2
  have hyt : (yY : G) * t = t * yY := Subgroup.mem_centralizer_singleton_iff.mp yY.2.2
  set τ₀Y := (cenYEquiv hx3 htx htriv).symm c
  have hτ₀c : cenMk (τ₀Y : G) τ₀Y.2.1 = c := (cenYEquiv hx3 htx htriv).apply_symm_apply c
  have hψτ₀ : ψ τ₀Y = e c := by rw [hψapp, hτ₀c]
  have hcc' : e c * e c = 1 := by rw [← map_mul, hcc, map_one]
  obtain ⟨ρ', hρ'⟩ := perm_five_odd_invol_conj' (e c) τσ hcc' hsc hτ2 hτs
  set rY := ψ.symm ρ'
  have hrτ : (rY : G) * τ₀Y * (rY : G)⁻¹ = τY := by
    have := lift (rY * τ₀Y * rY⁻¹) τY (by
      rw [map_mul, map_mul, map_inv, ψ.apply_symm_apply, hψτ₀, hρ', hψτ])
    simpa using this
  have hc₀τ : (τ₀Y : G)⁻¹ * c₀ ∈ Subgroup.zpowers x := by
    rw [← cenMk_eq_iff τ₀Y.2.1 hc₀, hτ₀c, hc₀c]
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hc₀τ
  have hc₀' : c₀ = τ₀Y * x ^ m := by rw [hm]; group
  have hτ₀x : Commute (τ₀Y : G) x := Subgroup.mem_centralizer_singleton_iff.mp τ₀Y.2.1
  have hτ₀t : (τ₀Y : G) * t = t * τ₀Y := Subgroup.mem_centralizer_singleton_iff.mp τ₀Y.2.2
  have hinvk : ∀ k : ℤ, t * x ^ k * t⁻¹ = (x ^ k)⁻¹ := fun k => by
    rw [← conj_zpow, htx, inv_zpow]
  have hx3m : x ^ (3 * m) = 1 := by
    rw [zpow_mul, zpow_ofNat, ← hx3, pow_orderOf_eq_one, one_zpow]
  have hit : i = c₀ * t := by rw [ht]; group
  have key : ∀ j : ℤ, x ^ j * ((τ₀Y : G) * x ^ m * t) * (x ^ j)⁻¹ =
      (τ₀Y : G) * x ^ (2 * j + m) * t := by
    intro j
    have h1 : x ^ j * (τ₀Y : G) = (τ₀Y : G) * x ^ j := (hτ₀x.zpow_right j).eq.symm
    have h2 : t * (x ^ j)⁻¹ = x ^ j * t := by
      calc t * (x ^ j)⁻¹ = t * (x ^ j)⁻¹ * t⁻¹ * t := by group
        _ = x ^ j * t := by rw [← zpow_neg, hinvk, zpow_neg, inv_inv]
    calc x ^ j * ((τ₀Y : G) * x ^ m * t) * (x ^ j)⁻¹ =
        (x ^ j * (τ₀Y : G)) * x ^ m * (t * (x ^ j)⁻¹) := by simp only [mul_assoc]
      _ = ((τ₀Y : G) * x ^ j) * x ^ m * (x ^ j * t) := by rw [h1, h2]
      _ = (τ₀Y : G) * (x ^ j * x ^ m * x ^ j) * t := by simp only [mul_assoc]
      _ = (τ₀Y : G) * x ^ (2 * j + m) * t := by
          rw [← zpow_add, ← zpow_add, show j + m + j = 2 * j + m by ring]
  have hconj : x ^ (-2 * m) * i * (x ^ (-2 * m))⁻¹ = (τ₀Y : G) * t := by
    rw [hit, hc₀', key, show 2 * (-2 * m) + m = -(3 * m) by ring, zpow_neg, hx3m, inv_one,
      mul_one]
  refine ⟨t, htK, htQ, htt, htz, A, hAt, hAiso, hzA, hAcl,
    ⟨_, hsA, hsY2, hsY1, hsYz, hsYzc, hsK⟩, τY, yY, hτY2, hτYz, hτt, hyt, hyτ, hy3,
    rY * (x ^ (-2 * m) * gi), ?_⟩
  have hrt : (rY : G) * t = t * rY := Subgroup.mem_centralizer_singleton_iff.mp rY.2.2
  calc (rY : G) * (x ^ (-2 * m) * gi) * z * ((rY : G) * (x ^ (-2 * m) * gi))⁻¹
      = (rY : G) * (x ^ (-2 * m) * (gi * z * gi⁻¹) * (x ^ (-2 * m))⁻¹) * (rY : G)⁻¹ := by
        group
    _ = (rY : G) * ((τ₀Y : G) * t) * (rY : G)⁻¹ := by rw [hgi, hconj]
    _ = t * ((rY : G) * τ₀Y * (rY : G)⁻¹) := by
        rw [hτ₀t]
        calc (rY : G) * (t * τ₀Y) * (rY : G)⁻¹ = (rY * t) * τ₀Y * (rY : G)⁻¹ := by group
          _ = (t * rY) * τ₀Y * (rY : G)⁻¹ := by rw [hrt]
          _ = t * ((rY : G) * τ₀Y * (rY : G)⁻¹) := by group
    _ = t * τY := by rw [hrτ]

end HSSetting

end CFSG.Quasithin.HSType
