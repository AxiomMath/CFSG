module

public import CFSG.Monster.GMS.F1Basic
public import CFSG.Monster.GMS.Transport
public import CFSG.Monster.B.Recog.GenericStrongEmbedding
public import CFSG.Monster.GMS.NotConj

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

variable {G : Type*} [Group G]

theorem card_centralizer_eq_of_isConj {x y : G} (h : IsConj x y) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) =
      Nat.card (Subgroup.centralizer ({y} : Set G)) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  have hmap : (Subgroup.centralizer ({x} : Set G)).map (MulAut.conj c).toMonoidHom =
      Subgroup.centralizer ({y} : Set G) := by
    rw [← hc]
    ext w
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · rintro ⟨v, hv, rfl⟩
      calc c * v * c⁻¹ * (c * x * c⁻¹) = c * (v * x) * c⁻¹ := by group
        _ = c * (x * v) * c⁻¹ := by rw [hv]
        _ = c * x * c⁻¹ * (c * v * c⁻¹) := by group
    · intro hw
      refine ⟨c⁻¹ * w * c, ?_, by group⟩
      calc c⁻¹ * w * c * x = c⁻¹ * (w * (c * x * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * x * c⁻¹) * w) * c := by rw [hw]
        _ = x * (c⁻¹ * w * c) := by group
  exact Nat.card_congr
    (((MulAut.conj c).subgroupMap _).trans (MulEquiv.subgroupCongr hmap)).toEquiv

theorem centralizer_conj_le {H : Subgroup G} {x : G}
    (hx : Subgroup.centralizer ({x} : Set G) ≤ H) {h : G} (hh : h ∈ H) :
    Subgroup.centralizer ({h * x * h⁻¹} : Set G) ≤ H := by
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff] at hg
  have hg' : h⁻¹ * g * h ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc h⁻¹ * g * h * x = h⁻¹ * (g * (h * x * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * x * h⁻¹) * g) * h := by rw [hg]
      _ = x * (h⁻¹ * g * h) := by group
  have := H.mul_mem (H.mul_mem hh (hx hg')) (H.inv_mem hh)
  simpa [mul_assoc] using this

private theorem eq_one_or_eq_of_mem_zpowers {K : Type*} [Group K] {w x : K} (hw : orderOf w = 2)
    (hx : x ∈ Subgroup.zpowers w) : x = 1 ∨ x = w := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← zpow_mod_orderOf, hw]
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left
    rw [show ((2 : ℕ) : ℤ) = 2 from rfl, hk, zpow_zero]
  · right
    rw [show ((2 : ℕ) : ℤ) = 2 from rfl, hk, zpow_one]

private theorem orderOf_conj' (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]

variable [Finite G]

omit [Finite G] in
private theorem centralizer_le_of_isStronglyEmbeddedOrder {M : Subgroup G}
    (hM : CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M) {x : G} (hxM : x ∈ M) (hx : orderOf x = 2) :
    Subgroup.centralizer ({x} : Set G) ≤ M := by
  intro c hc
  by_contra hcM
  have hodd := hM.2.2 c hcM
  have hxc : x ∈ M ⊓ M.map (MulAut.conj c).toMonoidHom := by
    refine ⟨hxM, Subgroup.mem_map.mpr ⟨x, hxM, ?_⟩⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hc]
    group
  have hdvd : orderOf (⟨x, hxc⟩ : (M ⊓ M.map (MulAut.conj c).toMonoidHom : Subgroup G)) ∣
      Nat.card (M ⊓ M.map (MulAut.conj c).toMonoidHom : Subgroup G) := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hx] at hdvd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

private theorem exists_conj_mem_sylow_two (S : Sylow 2 G) {t : G} (ht : orderOf t = 2) :
    ∃ g : G, g * t * g⁻¹ ∈ (S : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  obtain ⟨R, hR⟩ := h2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R S
  refine ⟨g, ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul]
  have := Subgroup.smul_mem_pointwise_smul t (MulAut.conj g) (R : Subgroup G)
    (hR (Subgroup.mem_zpowers t))
  simpa [MulAut.smul_def, MulAut.conj_apply] using this

omit [Finite G] in
private theorem isConj_of_odd_orderOf_mul {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hodd : Odd (orderOf (x * y))) : IsConj x y := by
  obtain ⟨k, hk⟩ := hodd
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hrx : (x * y) * x = x * (x * y)⁻¹ := by
    rw [mul_inv_rev, hx', hy', mul_assoc]
  have hpow : ∀ n : ℕ, (x * y) ^ n * x = x * ((x * y) ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc (x * y) ^ (n + 1) * x = (x * y) ^ n * ((x * y) * x) := by rw [pow_succ, mul_assoc]
        _ = (x * y) ^ n * x * (x * y)⁻¹ := by rw [hrx, mul_assoc]
        _ = x * ((x * y) ^ n)⁻¹ * (x * y)⁻¹ := by rw [ih]
        _ = x * ((x * y) ^ (n + 1))⁻¹ := by simp only [pow_succ', mul_inv_rev, mul_assoc]
  have h1 : (x * y) ^ (2 * k + 1) = 1 := hk ▸ pow_orderOf_eq_one (x * y)
  refine isConj_iff.mpr ⟨(x * y) ^ k, ?_⟩
  calc (x * y) ^ k * x * ((x * y) ^ k)⁻¹ = x * ((x * y) ^ k)⁻¹ * ((x * y) ^ k)⁻¹ := by
        rw [hpow]
    _ = x * ((x * y) ^ (2 * k))⁻¹ := by rw [mul_assoc, ← mul_inv_rev, ← pow_add, two_mul]
    _ = x * (x * y) := by
        congr 1
        rw [inv_eq_iff_mul_eq_one, ← pow_succ, h1]
    _ = y := by rw [← mul_assoc, hx, one_mul]

private theorem odd_orderOf_mul_of_isStronglyEmbeddedOrder {M : Subgroup G}
    (hM : CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M) {g : G} (hg : g ∉ M) {u v : G}
    (huM : u ∈ M) (hu2 : orderOf u = 2) (hvM : g⁻¹ * v * g ∈ M) (hv2 : orderOf v = 2) :
    Odd (orderOf (u * v)) := by
  have huu : u * u = 1 := by rw [← sq, ← hu2, pow_orderOf_eq_one]
  have hvv : v * v = 1 := by rw [← sq, ← hv2, pow_orderOf_eq_one]
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
  have hCv : ∀ c, c * v = v * c → g⁻¹ * c * g ∈ M := by
    intro c hc
    have hv2' : orderOf (g⁻¹ * v * g) = 2 := by
      have := orderOf_conj' g⁻¹ v
      rw [inv_inv] at this
      rw [this, hv2]
    apply centralizer_le_of_isStronglyEmbeddedOrder hM hvM hv2'
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * c * g * (g⁻¹ * v * g) = g⁻¹ * (c * v) * g := by group
      _ = g⁻¹ * (v * c) * g := by rw [hc]
      _ = g⁻¹ * v * g * (g⁻¹ * c * g) := by group
  by_contra heven
  rw [Nat.not_odd_iff_even] at heven
  obtain ⟨k, hk⟩ := heven
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp only [add_zero] at hk
    exact (orderOf_pos (u * v)).ne' hk
  have hw1 : (u * v) ^ k ≠ 1 := by
    intro h
    have := orderOf_le_of_pow_eq_one (Nat.pos_of_ne_zero hk0) h
    omega
  have hw2 : (u * v) ^ k * (u * v) ^ k = 1 := by rw [← pow_add, ← hk, pow_orderOf_eq_one]
  have hwinv : ((u * v) ^ k)⁻¹ = (u * v) ^ k := inv_eq_of_mul_eq_one_right hw2
  have hcomm : ∀ x : G, x⁻¹ = x → x * (u * v) * x = (u * v)⁻¹ →
      x * (u * v) ^ k = (u * v) ^ k * x := by
    intro x hx hxuv
    have hconj : x * (u * v) ^ k * x⁻¹ = (u * v) ^ k := by
      rw [← conj_pow, hx, hxuv, inv_pow, hwinv]
    calc x * (u * v) ^ k = x * (u * v) ^ k * x⁻¹ * x := by group
      _ = (u * v) ^ k * x := by rw [hconj]
  have huw : u * (u * v) ^ k = (u * v) ^ k * u := hcomm u huinv (by
    rw [mul_inv_rev, huinv, hvinv, ← mul_assoc, huu, one_mul])
  have hvw : v * (u * v) ^ k = (u * v) ^ k * v := hcomm v hvinv (by
    rw [mul_inv_rev, huinv, hvinv, mul_assoc, mul_assoc, hvv, mul_one])
  have hwM : (u * v) ^ k ∈ M := centralizer_le_of_isStronglyEmbeddedOrder hM huM hu2
    (Subgroup.mem_centralizer_singleton_iff.mpr huw.symm)
  have hwMg : g⁻¹ * (u * v) ^ k * g ∈ M := hCv _ hvw.symm
  have hodd := hM.2.2 g hg
  have hmem : (u * v) ^ k ∈ M ⊓ M.map (MulAut.conj g).toMonoidHom :=
    ⟨hwM, Subgroup.mem_map.mpr ⟨g⁻¹ * (u * v) ^ k * g, hwMg, by simp [mul_assoc]⟩⟩
  have hord : orderOf ((u * v) ^ k) = 2 := orderOf_eq_prime (by rw [sq]; exact hw2) hw1
  have hdvd : orderOf (⟨_, hmem⟩ : (M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G)) ∣
      Nat.card (M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G) := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hord] at hdvd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

theorem isConj_of_isStronglyEmbeddedOrder {M : Subgroup G}
    (hM : CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M) (S : Sylow 2 G)
    (hSM : (S : Subgroup G) ≤ M) {s t : G} (hs : orderOf s = 2) (ht : orderOf t = 2) :
    IsConj s t := by
  obtain ⟨a, ha⟩ := exists_conj_mem_sylow_two S hs
  obtain ⟨b, hb⟩ := exists_conj_mem_sylow_two S ht
  obtain ⟨g, hg⟩ : ∃ g, g ∉ M := by
    by_contra hall
    push Not at hall
    exact hM.1 (eq_top_iff.mpr fun x _ => hall x)
  have hu2 : orderOf (a * s * a⁻¹) = 2 := by rw [orderOf_conj', hs]
  have hv2 : orderOf (g * (b * t * b⁻¹) * g⁻¹) = 2 := by rw [orderOf_conj', orderOf_conj', ht]
  have hvM : g⁻¹ * (g * (b * t * b⁻¹) * g⁻¹) * g ∈ M := by
    have : g⁻¹ * (g * (b * t * b⁻¹) * g⁻¹) * g = b * t * b⁻¹ := by group
    rw [this]
    exact hSM hb
  have hodd := odd_orderOf_mul_of_isStronglyEmbeddedOrder hM hg (hSM ha) hu2 hvM hv2
  have huu : (a * s * a⁻¹) * (a * s * a⁻¹) = 1 := by rw [← sq, ← hu2, pow_orderOf_eq_one]
  have hvv : (g * (b * t * b⁻¹) * g⁻¹) * (g * (b * t * b⁻¹) * g⁻¹) = 1 := by
    rw [← sq, ← hv2, pow_orderOf_eq_one]
  have huv := isConj_of_odd_orderOf_mul huu hvv hodd
  exact (isConj_iff.mpr ⟨a, rfl⟩).trans (huv.trans (isConj_iff.mpr ⟨(g * b)⁻¹, by group⟩))

theorem eq_top_of_centralizer_le
    {d₀ : B} {a z : G} (hG : GMSF1Type d₀ a z) (H : Subgroup G)
    (haH : Subgroup.centralizer ({a} : Set G) ≤ H) {z' : H} (hz' : GMSLeechCentralizer z')
    (hcl : ∀ t : H, orderOf t = 2 →
      (∃ h : H, (h : G) * a * (h : G)⁻¹ = t) ∨ IsConj z' t) :
    H = ⊤ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzG := hG.2
  have hz'2 : orderOf (z' : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hz'.1
  obtain ⟨P', hP'⟩ := hz'.exists_sylow_center
  set S₀ : Subgroup G := (P' : Subgroup H).map H.subtype with hS₀
  have hS₀card : Nat.card S₀ = 2 ^ 46 := by
    rw [hS₀, Subgroup.card_map_of_injective H.subtype_injective]
    exact hz'.card_sylow_two P'
  obtain P : Sylow 2 G := default
  have hfac : 2 ^ (Nat.card G).factorization 2 = 2 ^ 46 := by
    rw [← P.card_eq_multiplicity]
    exact hzG.card_sylow_two P
  let S : Sylow 2 G := Sylow.ofCard S₀ (by rw [hS₀card, hfac])
  have hS : (S : Subgroup G) = S₀ := rfl
  have hSH : (S : Subgroup G) ≤ H := by
    rw [hS, hS₀]
    exact Subgroup.map_subtype_le _
  have hz'P' : z' ∈ (P' : Subgroup H) := by
    have : z' ∈ (Subgroup.center (P' : Subgroup H)).map (P' : Subgroup H).subtype := by
      rw [hP']
      exact Subgroup.mem_zpowers z'
    obtain ⟨w, -, rfl⟩ := Subgroup.mem_map.mp this
    exact w.2
  have hz'S : (z' : G) ∈ (S : Subgroup G) := Subgroup.mem_map.mpr ⟨z', hz'P', rfl⟩
  have hcentral : ∀ x ∈ (S : Subgroup G), (∀ s ∈ (S : Subgroup G), x * s = s * x) →
      ∃ y : H, (y : G) = x ∧ y ∈ Subgroup.zpowers z' := by
    intro x hx hxc
    obtain ⟨y, hyP, rfl⟩ := Subgroup.mem_map.mp hx
    refine ⟨y, rfl, ?_⟩
    rw [← hP']
    refine Subgroup.mem_map.mpr ⟨⟨y, hyP⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro s
    apply Subtype.ext
    apply Subtype.ext
    have := hxc (s : H) (Subgroup.mem_map.mpr ⟨s, s.2, rfl⟩)
    simpa using this.symm
  have hz'c : ∀ s ∈ (S : Subgroup G), (z' : G) * s = s * z' := by
    intro s hs
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hs
    have hz'Z : z' ∈ (Subgroup.center (P' : Subgroup H)).map (P' : Subgroup H).subtype := by
      rw [hP']
      exact Subgroup.mem_zpowers z'
    obtain ⟨c, hc, hcz⟩ := Subgroup.mem_map.mp hz'Z
    have := Subgroup.mem_center_iff.mp hc ⟨w, hw⟩
    have h' : (c : H) * w = w * c := by
      have := congrArg Subtype.val this
      simpa using this.symm
    rw [← hcz]
    simpa using congrArg Subtype.val h'
  have hzz' : IsConj z (z' : G) := by
    refine isConj_of_mem_center_sylow hzG.1 hzG.2.1 hzG.2.2.2.2 S hz'2 ?_
    refine Subgroup.mem_map.mpr ⟨⟨z', hz'S⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro s
    apply Subtype.ext
    exact (hz'c s s.2).symm
  have hCz' : Subgroup.centralizer ({(z' : G)} : Set G) ≤ H := by
    set C' : Subgroup G := (Subgroup.centralizer ({z'} : Set H)).map H.subtype with hC'
    have hle : C' ≤ Subgroup.centralizer ({(z' : G)} : Set G) := by
      rintro x ⟨y, hy, rfl⟩
      have hy' := Subgroup.mem_centralizer_singleton_iff.mp hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      simpa using congrArg Subtype.val hy'
    have hcard : Nat.card (Subgroup.centralizer ({(z' : G)} : Set G)) ≤ Nat.card C' := by
      rw [hC', Subgroup.card_map_of_injective H.subtype_injective, hz'.card_centralizer,
        ← card_centralizer_eq_of_isConj hzz', hzG.card_centralizer]
    have heq := Subgroup.eq_of_le_of_card_ge hle hcard
    rw [← heq, hC']
    exact Subgroup.map_subtype_le _
  have hC : ∀ t ∈ H, orderOf t = 2 → Subgroup.centralizer ({t} : Set G) ≤ H := by
    intro t htH ht2
    rcases hcl ⟨t, htH⟩ (by rw [← Subgroup.orderOf_mk t htH] at ht2; exact ht2) with
      ⟨h, hh⟩ | hconj
    · have := centralizer_conj_le haH h.2
      rwa [hh] at this
    · obtain ⟨h, hh⟩ := isConj_iff.mp hconj
      have := centralizer_conj_le hCz' h.2
      have hh' : (h : G) * z' * (h : G)⁻¹ = t := by
        simpa using congrArg Subtype.val hh
      rwa [hh'] at this
  by_contra hne
  have hSE := CFSG.Monster.B.Recog.isStronglyEmbeddedOrder_of_centralizer_le_of_unique hne hC S
    hSH hz'S hz'2 hz'c (fun x hx hx2 hxc => by
      obtain ⟨y, rfl, hy⟩ := hcentral x hx hxc
      rcases eq_one_or_eq_of_mem_zpowers hz'.1 hy with rfl | rfl
      · simp at hx2
      · rfl)
  exact hG.not_isConj (isConj_of_isStronglyEmbeddedOrder hSE S hSH hG.1.1 hzG.1)

theorem nonempty_mulEquiv_of_centralizer_le
    {d₀ : B} {a z : G} (hG : GMSF1Type d₀ a z)
    {X : Type*} [Group X] {a₀ z₀ : X} (hz₀ : GMSLeechCentralizer z₀)
    (hX : ∀ t : X, orderOf t = 2 → IsConj a₀ t ∨ IsConj z₀ t)
    (H : Subgroup G) (haH : Subgroup.centralizer ({a} : Set G) ≤ H) (e : H ≃* X)
    (hea : e ⟨a, haH (Subgroup.mem_centralizer_singleton_iff.mpr rfl)⟩ = a₀) :
    Nonempty (G ≃* X) := by
  have hz' : GMSLeechCentralizer (e.symm z₀) := GMSLeechCentralizer.of_mulEquiv e.symm hz₀
  have htop : H = ⊤ := by
    refine eq_top_of_centralizer_le hG H haH hz' fun t ht => ?_
    have ht' : orderOf (e t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht
    rcases hX (e t) ht' with h | h
    · left
      obtain ⟨c, hc⟩ := isConj_iff.mp h
      refine ⟨e.symm c, ?_⟩
      have : e.symm c * ⟨a, haH (Subgroup.mem_centralizer_singleton_iff.mpr rfl)⟩ *
          (e.symm c)⁻¹ = t := by
        apply e.injective
        rw [map_mul, map_mul, map_inv, e.apply_symm_apply, hea, hc]
      simpa using congrArg Subtype.val this
    · right
      have := (isConj_iff.mp h)
      obtain ⟨c, hc⟩ := this
      refine isConj_iff.mpr ⟨e.symm c, ?_⟩
      apply e.injective
      rw [map_mul, map_mul, map_inv, e.apply_symm_apply, e.apply_symm_apply, hc]
  exact ⟨Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr htop).symm.trans e)⟩

end CFSG.Monster.GMS
