module

public import CFSG.Walter.W67.Section5.P56AbInterface
public import CFSG.Walter.W67.Section5.P56AbAut
public import CFSG.Walter.W67.Section5.Lemma54

public section

namespace CFSG.Walter.W67

open P56Ab

namespace P56AbData

variable {G : Type} [Group G] [Finite G] (d : P56AbData G)

abbrev V : Subgroup G := d.P₁ ⊔ d.P₂

abbrev NV : Subgroup G := Subgroup.normalizer (d.V : Set G)

abbrev CV : Subgroup G := Subgroup.centralizer (d.V : Set G)

abbrev H : Subgroup G := Subgroup.zpowers d.J ⊔ d.B ⊔ d.E

theorem P₁_comm {a b : G} (ha : a ∈ d.P₁) (hb : b ∈ d.P₁) : a * b = b * a := by
  have := d.P₁_elementary
  exact setLike_mul_comm ha hb

theorem P₂_comm {a b : G} (ha : a ∈ d.P₂) (hb : b ∈ d.P₂) : a * b = b * a := by
  have := d.P₂_elementary
  exact setLike_mul_comm ha hb

theorem P₁_pow {a : G} (ha : a ∈ d.P₁) : a ^ 3 = 1 :=
  @elemPow_eq_one_of_isElementaryAbelian 3 G _ d.P₁ d.P₁_elementary a ha

theorem P₂_pow {a : G} (ha : a ∈ d.P₂) : a ^ 3 = 1 :=
  @elemPow_eq_one_of_isElementaryAbelian 3 G _ d.P₂ d.P₂_elementary a ha

theorem P₂_le_normalizer_P₁ : d.P₂ ≤ Subgroup.normalizer (d.P₁ : Set G) := by
  intro b hb
  apply Sec53.mem_normalizer_of_conj_le
  intro a ha
  rw [← d.P₁_comm_P₂ a ha b hb, mul_inv_cancel_right]
  exact ha

theorem mem_V {x : G} : x ∈ d.V ↔ ∃ a ∈ d.P₁, ∃ b ∈ d.P₂, a * b = x :=
  mem_sup_iff_of_le_normalizer d.P₂_le_normalizer_P₁

theorem V_comm {x y : G} (hx : x ∈ d.V) (hy : y ∈ d.V) : x * y = y * x := by
  obtain ⟨a, ha, b, hb, rfl⟩ := d.mem_V.mp hx
  obtain ⟨a', ha', b', hb', rfl⟩ := d.mem_V.mp hy
  calc a * b * (a' * b') = (a * a') * (b * b') := by
        rw [mul_assoc, ← mul_assoc b, ← d.P₁_comm_P₂ a' ha' b hb]; group
    _ = (a' * a) * (b' * b) := by rw [d.P₁_comm ha ha', d.P₂_comm hb hb']
    _ = a' * b' * (a * b) := by
        rw [mul_assoc, ← mul_assoc a, d.P₁_comm_P₂ a ha b' hb']; group

theorem V_pow {x : G} (hx : x ∈ d.V) : x ^ 3 = 1 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := d.mem_V.mp hx
  rw [(Commute.mul_pow (d.P₁_comm_P₂ a ha b hb) 3), d.P₁_pow ha, d.P₂_pow hb, one_mul]

theorem card_V : Nat.card d.V = 3 ^ (2 * d.n) := by
  rw [Sec54.card_sup_eq_mul d.P₂_le_normalizer_P₁ d.P₁_inf_P₂, d.card_P₁, d.card_P₂, two_mul,
    pow_add]

theorem V_isPGroup : IsPGroup 3 d.V :=
  fun x => ⟨1, Subtype.ext (by simpa using d.V_pow x.2)⟩

theorem V_ne_bot : d.V ≠ ⊥ := by
  intro h
  have := d.card_V
  rw [h, Subgroup.card_bot] at this
  have h1 : 1 < 3 ^ (2 * d.n) := Nat.one_lt_pow (by have := d.three_le_n; omega) (by norm_num)
  omega

theorem J_mul_J : d.J * d.J = 1 := by
  rw [← sq, ← d.orderOf_J, pow_orderOf_eq_one]

theorem J_inv_eq : d.J⁻¹ = d.J := by
  rw [inv_eq_iff_mul_eq_one, d.J_mul_J]

theorem J_comm_P₁ {a : G} (ha : a ∈ d.P₁) : d.J * a = a * d.J :=
  (Subgroup.mem_centralizer_singleton_iff.mp (d.P₁_le ha)).symm

theorem J_conj_V {a b : G} (ha : a ∈ d.P₁) (hb : b ∈ d.P₂) :
    d.J * (a * b) * d.J⁻¹ = a * b⁻¹ := by
  have h2 := d.J_inv b hb
  calc d.J * (a * b) * d.J⁻¹ = (d.J * a * d.J⁻¹) * (d.J * b * d.J⁻¹) := by group
    _ = a * b⁻¹ := by rw [d.J_comm_P₁ ha, mul_inv_cancel_right, h2]

theorem mem_P₁_iff {x : G} : x ∈ d.P₁ ↔ x ∈ d.V ∧ d.J * x = x * d.J := by
  constructor
  · intro hx
    exact ⟨Subgroup.mem_sup_left hx, d.J_comm_P₁ hx⟩
  · rintro ⟨hx, hJx⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := d.mem_V.mp hx
    have h1 : d.J * (a * b) * d.J⁻¹ = a * b := by rw [hJx, mul_inv_cancel_right]
    rw [d.J_conj_V ha hb, mul_right_inj] at h1
    have hb1 : b = 1 := by
      have hb3 := d.P₂_pow hb
      have : b * b = 1 := by
        nth_rw 2 [← h1]
        exact mul_inv_cancel b
      have h2 : b ^ 2 = 1 := by rw [sq, this]
      have : b = b ^ 3 * (b ^ 2)⁻¹ := by group
      rw [this, hb3, h2, inv_one, mul_one]
    rw [hb1, mul_one]
    exact ha

theorem mem_P₂_iff {x : G} : x ∈ d.P₂ ↔ x ∈ d.V ∧ d.J * x * d.J⁻¹ = x⁻¹ := by
  constructor
  · intro hx
    exact ⟨Subgroup.mem_sup_right hx, d.J_inv x hx⟩
  · rintro ⟨hx, hJx⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := d.mem_V.mp hx
    rw [d.J_conj_V ha hb, mul_inv_rev, ← d.P₁_comm_P₂ a⁻¹ (d.P₁.inv_mem ha) b⁻¹
      (d.P₂.inv_mem hb), mul_left_inj] at hJx
    have ha1 : a = 1 := by
      have ha3 := d.P₁_pow ha
      have h2 : a ^ 2 = 1 := by rw [sq]; nth_rw 2 [hJx]; exact mul_inv_cancel a
      have : a = a ^ 3 * (a ^ 2)⁻¹ := by group
      rw [this, ha3, h2, inv_one, mul_one]
    rw [ha1, one_mul]
    exact hb

theorem J_mem_NV : d.J ∈ d.NV := by
  apply Sec53.mem_normalizer_of_conj_le
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := d.mem_V.mp hx
  rw [d.J_conj_V ha hb]
  exact d.V.mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right (d.P₂.inv_mem hb))

theorem le_NV_of_le {X : Subgroup G} (h₁ : X ≤ Subgroup.normalizer (d.P₁ : Set G))
    (h₂ : X ≤ Subgroup.normalizer (d.P₂ : Set G)) : X ≤ d.NV := by
  intro x hx
  apply Sec53.mem_normalizer_of_conj_le
  intro y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := d.mem_V.mp hy
  rw [show x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) by group]
  exact d.V.mul_mem (Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (h₁ hx) a).mp ha))
    (Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (h₂ hx) b).mp hb))

theorem B_le_NV : d.B ≤ d.NV := d.le_NV_of_le d.B_le_normalizer₁ d.B_le_normalizer₂

theorem E_le_NV : d.E ≤ d.NV := d.le_NV_of_le d.E_le_normalizer₁ d.E_le_normalizer₂

theorem P₀_le_NV : d.P₀ ≤ d.NV := d.P₀_le.trans d.E_le_NV

theorem H_le_NV : d.H ≤ d.NV :=
  sup_le (sup_le (Subgroup.zpowers_le.mpr d.J_mem_NV) d.B_le_NV) d.E_le_NV

theorem V_le_NV : d.V ≤ d.NV := Subgroup.le_normalizer

theorem CV_le_NV : d.CV ≤ d.NV := Subgroup.centralizer_le_normalizer _

theorem H_le_centralizer : d.H ≤ Subgroup.centralizer ({d.J} : Set G) :=
  sup_le (sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
    d.B_le) d.E_le

theorem V_le_CV : d.V ≤ d.CV := fun _ hx =>
  Subgroup.mem_centralizer_iff.mpr fun _ hy => (d.V_comm hx hy).symm

theorem CV_normal_NV : (d.CV.subgroupOf d.NV).Normal :=
  ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.mp (Sec54.mem_normalizer_centralizer g.2) x).mp hx⟩

theorem mem_normalizer_CV {g : G} (hg : g ∈ d.NV) :
    g ∈ Subgroup.normalizer (d.CV : Set G) :=
  Sec54.mem_normalizer_centralizer hg

theorem mem_normalizer_P₁ {g : G} (hg : g ∈ d.NV) (hgJ : g * d.J = d.J * g) :
    g ∈ Subgroup.normalizer (d.P₁ : Set G) := by
  apply Sec53.mem_normalizer_of_conj_le
  intro a ha
  rw [d.mem_P₁_iff] at ha ⊢
  refine ⟨(Subgroup.mem_normalizer_iff.mp hg a).mp ha.1, ?_⟩
  have hJg : d.J = g * d.J * g⁻¹ := by rw [hgJ, mul_inv_cancel_right]
  calc d.J * (g * a * g⁻¹) = (g * d.J * g⁻¹) * (g * a * g⁻¹) := by rw [← hJg]
    _ = g * (d.J * a) * g⁻¹ := by group
    _ = g * (a * d.J) * g⁻¹ := by rw [ha.2]
    _ = (g * a * g⁻¹) * (g * d.J * g⁻¹) := by group
    _ = g * a * g⁻¹ * d.J := by rw [← hJg]

theorem mem_normalizer_P₂ {g : G} (hg : g ∈ d.NV) (hgJ : g * d.J = d.J * g) :
    g ∈ Subgroup.normalizer (d.P₂ : Set G) := by
  apply Sec53.mem_normalizer_of_conj_le
  intro b hb
  rw [d.mem_P₂_iff] at hb ⊢
  refine ⟨(Subgroup.mem_normalizer_iff.mp hg b).mp hb.1, ?_⟩
  have hJg : d.J = g * d.J * g⁻¹ := by rw [hgJ, mul_inv_cancel_right]
  calc d.J * (g * b * g⁻¹) * d.J⁻¹ =
        (g * d.J * g⁻¹) * (g * b * g⁻¹) * (g * d.J * g⁻¹)⁻¹ := by rw [← hJg]
    _ = g * (d.J * b * d.J⁻¹) * g⁻¹ := by group
    _ = (g * b * g⁻¹)⁻¹ := by rw [hb.2]; group

theorem orderOf_ne_two_of_mem_CV {u : G} (hu : u ∈ d.CV) : orderOf u ≠ 2 := by
  intro hu2
  have h := d.centralizer_involution u hu2
  have hle : d.V ≤ Subgroup.centralizer ({u} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hu x hx)
  have hdvd : 3 ^ (2 * d.n) ∣ Nat.card (Subgroup.centralizer ({u} : Set G)) :=
    d.card_V ▸ Subgroup.card_dvd_of_le hle
  have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').mp hdvd
  omega

theorem odd_card_CV : Odd (Nat.card d.CV) := by
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 h2
  exact d.orderOf_ne_two_of_mem_CV u.2 (by rw [← Subgroup.orderOf_coe] at hu; exact hu)

theorem J_not_mem_CV : d.J ∉ d.CV := fun h => d.orderOf_ne_two_of_mem_CV h d.orderOf_J

omit [Finite G] in
theorem exists_inverted {P : Subgroup G} {t : G} (ht : t * t = 1)
    (htP : t ∈ Subgroup.normalizer (P : Set G)) {x : G} (hx : x ∈ P)
    (htx : t * x * t⁻¹ ≠ x) : ∃ y ∈ P, y ≠ 1 ∧ t * y * t⁻¹ = y⁻¹ := by
  have htinv : t⁻¹ = t := by rw [inv_eq_iff_mul_eq_one, ht]
  have hx' : t * x * t⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp htP x).mp hx
  refine ⟨x⁻¹ * (t * x * t⁻¹), P.mul_mem (P.inv_mem hx) hx', ?_, ?_⟩
  · intro h
    apply htx
    rw [inv_mul_eq_one] at h
    exact h.symm
  · rw [htinv]
    calc t * (x⁻¹ * (t * x * t)) * t = t * x⁻¹ * t * x * (t * t) := by group
      _ = t * x⁻¹ * t * x := by rw [ht, mul_one]
      _ = (x⁻¹ * (t * x * t))⁻¹ := by
          rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, inv_inv, htinv]
          group

theorem le_zpowers_J {W : Subgroup G} (hWN : W ≤ d.NV) (hJW : d.J ∈ W) (hW : IsPGroup 2 W) :
    W ≤ Subgroup.zpowers d.J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hWS⟩ := hW.exists_le_sylow
  have hSab := d.abelian_sylow S
  have hSel := d.elementary_sylow S
  intro w hw
  have hwS := hWS hw
  have hJS := hWS hJW
  have hwJ : w * d.J = d.J * w := setLike_mul_comm hwS hJS
  have hww : w * w = 1 := by
    rw [← sq]
    exact @elemPow_eq_one_of_isElementaryAbelian 2 G _ (S : Subgroup G) hSel w hwS
  by_cases hw1 : w = 1
  · rw [hw1]; exact Subgroup.one_mem _
  by_cases hwJ' : w = d.J
  · rw [hwJ']; exact Subgroup.mem_zpowers _
  exfalso
  have hwN := hWN hw
  have h1 : ∀ a ∈ d.P₁, w * a * w⁻¹ = a := by
    by_contra hcon
    push Not at hcon
    obtain ⟨a, ha, hwa⟩ := hcon
    obtain ⟨y, hy, hy1, hyinv⟩ := exists_inverted hww (d.mem_normalizer_P₁ hwN hwJ) ha hwa
    exact d.no_real_three d.J y w d.orderOf_J (d.P₁_le hy)
      (Subgroup.mem_centralizer_singleton_iff.mpr hwJ) hy1 (d.P₁_pow hy) hww hyinv
  have h2 : ∀ b ∈ d.P₂, w * b * w⁻¹ = b := by
    by_contra hcon
    push Not at hcon
    obtain ⟨b, hb, hwb⟩ := hcon
    obtain ⟨y, hy, hy1, hyinv⟩ := exists_inverted hww (d.mem_normalizer_P₂ hwN hwJ) hb hwb
    have hJw2 : (d.J * w) ^ 2 = 1 := by
      rw [sq, show d.J * w * (d.J * w) = d.J * (w * d.J) * w by group, hwJ,
        show d.J * (d.J * w) * w = (d.J * d.J) * (w * w) by group, d.J_mul_J, hww, one_mul]
    have hJw1 : d.J * w ≠ 1 := by
      intro h
      apply hwJ'
      rw [eq_inv_of_mul_eq_one_right h, d.J_inv_eq]
    have hu : orderOf (d.J * w) = 2 := orderOf_eq_prime hJw2 hJw1
    have hyc : y ∈ Subgroup.centralizer ({d.J * w} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hJy := d.J_inv y hy
      symm
      calc d.J * w * y = d.J * (w * y * w⁻¹) * w := by group
        _ = d.J * y⁻¹ * w := by rw [hyinv]
        _ = d.J * (d.J * y * d.J⁻¹) * w := by rw [hJy]
        _ = d.J * (d.J⁻¹ * y * d.J) * w := by rw [d.J_inv_eq]
        _ = y * (d.J * w) := by group
    have hwc : w ∈ Subgroup.centralizer ({d.J * w} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← mul_assoc, hwJ]
    exact d.no_real_three (d.J * w) y w hu hyc hwc hy1 (d.P₂_pow hy) hww hyinv
  have hwC : w ∈ d.CV := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := d.mem_V.mp hx
    have ha' := h1 a ha
    have hb' := h2 b hb
    calc a * b * w = (w * a * w⁻¹) * (w * b * w⁻¹) * w := by rw [ha', hb']
      _ = w * (a * b) := by group
  apply d.orderOf_ne_two_of_mem_CV hwC
  apply orderOf_eq_prime
  · rw [sq, hww]
  · exact hw1

theorem card_le_two {W : Subgroup G} (hWN : W ≤ d.NV) (hW : IsPGroup 2 W) : Nat.card W ≤ 2 :=
  Sec54.card_le_two d.J_mem_NV d.orderOf_J
    (fun _ hW'N hJW' hW' => d.le_zpowers_J hW'N hJW' hW') W hWN hW

theorem mem_H_sup_CV {x : G} (hx : x ∈ d.NV) (hxJ : x * d.J * x⁻¹ * d.J⁻¹ ∈ d.CV) :
    x ∈ d.H ⊔ d.CV := by
  set D := d.CV ⊔ Subgroup.zpowers d.J with hD
  have hJN : Subgroup.zpowers d.J ≤ Subgroup.normalizer (d.CV : Set G) :=
    Subgroup.zpowers_le.mpr (d.mem_normalizer_CV d.J_mem_NV)
  have hDN : D ≤ d.NV := sup_le d.CV_le_NV (Subgroup.zpowers_le.mpr d.J_mem_NV)
  have hxJD : x * d.J * x⁻¹ ∈ D := by
    have : x * d.J * x⁻¹ = (x * d.J * x⁻¹ * d.J⁻¹) * d.J := by group
    rw [this]
    exact D.mul_mem (Subgroup.mem_sup_left hxJ) (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  obtain ⟨g, hgD, hg⟩ := Sec54.exists_conj (Subgroup.mem_sup_right (Subgroup.mem_zpowers d.J))
    d.orderOf_J (fun W hWD hW => d.card_le_two (hWD.trans hDN) hW) hxJD
  obtain ⟨c, hc, j, hj, rfl⟩ := (mem_sup_iff_of_le_normalizer hJN).mp hgD
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hj
  have hjJ : d.J ^ k * d.J * (d.J ^ k)⁻¹ = d.J := by
    rw [(Commute.zpow_left (Commute.refl d.J) k).eq, mul_inv_cancel_right]
  have hcx : c⁻¹ * x ∈ d.NV ⊓ Subgroup.centralizer ({d.J} : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨d.NV.mul_mem (d.NV.inv_mem (d.CV_le_NV hc)) hx, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    symm
    have h1 : c * d.J * c⁻¹ = x * d.J * x⁻¹ := by
      rw [← hg]
      calc c * d.J * c⁻¹ = c * (d.J ^ k * d.J * (d.J ^ k)⁻¹) * c⁻¹ := by rw [hjJ]
        _ = c * d.J ^ k * d.J * (c * d.J ^ k)⁻¹ := by group
    calc d.J * (c⁻¹ * x) = c⁻¹ * (c * d.J * c⁻¹) * x := by group
      _ = c⁻¹ * (x * d.J * x⁻¹) * x := by rw [h1]
      _ = c⁻¹ * x * d.J := by group
  have hmem := d.normalizer_inf_centralizer_J hcx
  have : x = c * (c⁻¹ * x) := by group
  rw [this]
  have hHC : d.H ⊔ d.CV = d.CV ⊔ d.H := sup_comm _ _
  exact (d.H ⊔ d.CV).mul_mem (Subgroup.mem_sup_right hc) hmem

end P56AbData

end CFSG.Walter.W67
