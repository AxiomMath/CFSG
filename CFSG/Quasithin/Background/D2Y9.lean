module

public import CFSG.Quasithin.Background.D2Y7

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

variable {V : Type*} [CommGroup V] [Finite V]

@[expose] def normR (X : Subgroup (MulAut V)) (x : MulAut V) : Subgroup (MulAut V) :=
  pCoreOf 3 X ⊓ Subgroup.normalizer (centR X x : Set (MulAut V))

section Basic

variable {X : Subgroup (MulAut V)} {t x z : MulAut V}

omit [Finite V] in
theorem normR_le_pCoreOf : normR X x ≤ pCoreOf 3 X := inf_le_left

omit [Finite V] in
theorem centR_le_normR : centR X x ≤ normR X x := fun _ hp =>
  ⟨(mem_centR.mp hp).1, Subgroup.le_normalizer hp⟩

omit [Finite V] in
theorem normR_conj {q p : MulAut V} (hq : q ∈ normR X x) (hp : p ∈ centR X x) :
    q * p * q⁻¹ ∈ centR X x :=
  (Subgroup.mem_normalizer_iff.mp hq.2 p).mp hp

omit [Finite V] in
theorem mem_normR_of {q : MulAut V} (hqR : q ∈ pCoreOf 3 X)
    (h1 : ∀ p ∈ centR X x, q * p * q⁻¹ ∈ centR X x)
    (h2 : ∀ p ∈ centR X x, q⁻¹ * p * q ∈ centR X x) : q ∈ normR X x := by
  refine ⟨hqR, Subgroup.mem_normalizer_iff.mpr fun p => ⟨h1 p, fun hp => ?_⟩⟩
  have := h2 _ hp
  simpa [mul_assoc] using this

theorem Good.E9 (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) (hX1 : ∀ Y ∈ Xk X 1, False)
    (h : InvPair X t x) (hg : Good X t x z) :
    orderOf x = 3 ∧ orderOf z = 3 ∧ x * z = z * x ∧
      Subgroup.zpowers x ≠ Subgroup.zpowers z ∧
      Subgroup.zpowers x ⊔ Subgroup.zpowers z = centR X x := by
  have hxo := (inverted_data hV c hX1 h.ht h.hx h.hx1 h.hinv).1
  have hxrk := (inverted_data hV c hX1 h.ht h.hx h.hx1 h.hinv).2.1
  have hzo : orderOf z = 3 := orderOf_eq_prime (hg.cube z hg.hz) hg.hz1
  have hxP : x ∈ centR X x := mem_centR.mpr ⟨h.hx, rfl⟩
  have hxz : x * z = z * x := hg.comm x hxP z hg.hz
  have hne : Subgroup.zpowers x ≠ Subgroup.zpowers z := fun e => by
    rw [e] at hxrk
    have := hg.rk6
    omega
  obtain ⟨hEcard, -, -⟩ := E9_data hxo hzo hxz hne
  have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers z ≤ centR X x :=
    sup_le (Subgroup.zpowers_le.mpr hxP) (Subgroup.zpowers_le.mpr hg.hz)
  exact ⟨hxo, hzo, hxz, hne, Subgroup.eq_of_le_of_card_ge hle (by rw [hEcard, hg.card])⟩

theorem zpowers_conj_z (hg : Good X t x z) {q : MulAut V}
    (hq : ∀ p ∈ centR X x, q * p * q⁻¹ ∈ centR X x) :
    Subgroup.zpowers (q * z * q⁻¹) = Subgroup.zpowers z := by
  by_contra hne
  have hconj := hq z hg.hz
  have hne1 : q * z * q⁻¹ ≠ 1 := by
    intro e
    apply hg.hz1
    have : z = q⁻¹ * (q * z * q⁻¹) * q := by group
    rw [this, e]
    group
  have h4 := hg.rk4 _ hconj hne1 hne
  rw [rk_commV_zpowers_conj] at h4
  have := hg.rk6
  omega

theorem normR_comm_z (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) (hX1 : ∀ Y ∈ Xk X 1, False)
    (h : InvPair X t x) (hg : Good X t x z) {q : MulAut V} (hq : q ∈ normR X x) :
    q * z = z * q := by
  obtain ⟨-, hzo, -⟩ := Good.E9 hV c hX1 h hg
  have hodd : Odd (orderOf q) := odd_orderOf_of_mem_pCoreOf hq.1
  have hz3 : Nat.card (Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, hzo]
  have hconj : conjBy q (Subgroup.zpowers z) = Subgroup.zpowers z := by
    rw [← zpowers_conj]
    exact zpowers_conj_z hg (fun p hp => normR_conj hq hp)
  exact commute_of_conjBy_eq hz3 hodd hconj z (Subgroup.mem_zpowers z)

theorem normR_x_mod_z (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) (hX1 : ∀ Y ∈ Xk X 1, False)
    (h : InvPair X t x) (hg : Good X t x z) {q : MulAut V} (hq : q ∈ normR X x) :
    q * x * q⁻¹ * x⁻¹ ∈ Subgroup.zpowers z := by
  obtain ⟨hxo, hzo, hxz, hne, hsup⟩ := Good.E9 hV c hX1 h hg
  have hxrk := (inverted_data hV c hX1 h.ht h.hx h.hx1 h.hinv).2.1
  have hx3 : x ^ 3 = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
  have hz3 : z ^ 3 = 1 := hg.cube z hg.hz
  have hqz := normR_comm_z hV c hX1 h hg hq
  have hqzc : q * z * q⁻¹ = z := by rw [hqz]; group
  have hxP : x ∈ centR X x := mem_centR.mpr ⟨h.hx, rfl⟩
  have haP : q * x * q⁻¹ ∈ centR X x := normR_conj hq hxP
  have haE : q * x * q⁻¹ ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers z := by rw [hsup]; exact haP
  obtain ⟨-, -, hform⟩ := E9_data hxo hzo hxz hne
  obtain ⟨i, j, hij⟩ := hform _ haE
  have hx3z : x ^ (3 : ℤ) = 1 := by exact_mod_cast hx3
  have hz3z : z ^ (3 : ℤ) = 1 := by exact_mod_cast hz3
  have hred : x ^ i = x ^ (i % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv i 3]
    rw [zpow_add, zpow_mul, hx3z, one_zpow, mul_one]
  rw [hred] at hij
  have hqx1 : q * x * q⁻¹ ≠ 1 := by
    intro e
    apply h.hx1
    have : x = q⁻¹ * (q * x * q⁻¹) * q := by group
    rw [this, e]
    group
  have hcz : Commute x z := hxz
  have hi : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  rcases hi with hi | hi | hi
  · exfalso
    rw [hi, zpow_zero, one_mul] at hij
    have hz' : q * x * q⁻¹ ∈ Subgroup.zpowers z := by
      rw [hij]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) j
    have hzc : Nat.card (Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, hzo]
    have heq : Subgroup.zpowers (q * x * q⁻¹) = Subgroup.zpowers z :=
      zpowers_eq_of_prime_card hzc hz' hqx1
    have h1 : rk (commV (Subgroup.zpowers (q * x * q⁻¹))) = 4 := by
      rw [rk_commV_zpowers_conj]; exact hxrk
    rw [heq] at h1
    have := hg.rk6
    omega
  · rw [hi, zpow_one] at hij
    rw [hij]
    have : x * z ^ j * x⁻¹ = z ^ j := by
      rw [(hcz.zpow_right j).eq]
      group
    rw [this]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) j
  · rw [hi] at hij
    have h4 : x ^ (4 : ℤ) = x := by
      calc x ^ (4 : ℤ) = x ^ (1 + 3 : ℤ) := by norm_num
        _ = x ^ (1 : ℤ) * x ^ (3 : ℤ) := zpow_add _ _ _
        _ = x := by rw [hx3z, mul_one, zpow_one]
    have e1 : q * q * x * (q * q)⁻¹ = x := by
      calc q * q * x * (q * q)⁻¹ = q * (q * x * q⁻¹) * q⁻¹ := by group
        _ = q * (x ^ (2 : ℤ) * z ^ j) * q⁻¹ := by rw [hij]
        _ = (q * x ^ (2 : ℤ) * q⁻¹) * (q * z ^ j * q⁻¹) := by group
        _ = (q * x * q⁻¹) ^ (2 : ℤ) * (q * z * q⁻¹) ^ j := by rw [← conj_zpow, ← conj_zpow]
        _ = (x ^ (2 : ℤ) * z ^ j) ^ (2 : ℤ) * z ^ j := by rw [hij, hqzc]
        _ = x ^ (4 : ℤ) * z ^ (3 * j) := by
          rw [(hcz.zpow_zpow 2 j).mul_zpow]
          group
        _ = x := by
          have h3j : z ^ (3 * j) = 1 := by rw [zpow_mul, hz3z, one_zpow]
          rw [h4, h3j, mul_one]
    have hqq : q * q ∈ centR X x :=
      mem_centR.mpr ⟨(pCoreOf 3 X).mul_mem hq.1 hq.1, mul_inv_eq_iff_eq_mul.mp e1⟩
    have hqP : q ∈ centR X x := mem_of_sq_mem (odd_orderOf_of_mem_pCoreOf hq.1) hqq
    have hqx : q * x = x * q := (mem_centR.mp hqP).2
    have : q * x * q⁻¹ * x⁻¹ = 1 := by rw [hqx]; group
    rw [this]
    exact Subgroup.one_mem _

theorem normR_conj_zpow (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) (hX1 : ∀ Y ∈ Xk X 1, False)
    (h : InvPair X t x) (hg : Good X t x z) {q : MulAut V} (hq : q ∈ normR X x) (a b : ℤ) :
    q * (x ^ a * z ^ b) * q⁻¹ * (x ^ a * z ^ b)⁻¹ = (q * x * q⁻¹ * x⁻¹) ^ a := by
  obtain ⟨-, -, hxz, -⟩ := Good.E9 hV c hX1 h hg
  have hqz := normR_comm_z hV c hX1 h hg hq
  have hqzc : q * z * q⁻¹ = z := by rw [hqz]; group
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (normR_x_mod_z hV c hX1 h hg hq)
  have hζx : Commute (q * x * q⁻¹ * x⁻¹) x := by
    rw [← hm]
    exact ((show Commute z x from hxz.symm).zpow_left m)
  have e : q * x * q⁻¹ = (q * x * q⁻¹ * x⁻¹) * x := by group
  calc q * (x ^ a * z ^ b) * q⁻¹ * (x ^ a * z ^ b)⁻¹
      = (q * x ^ a * q⁻¹) * (q * z ^ b * q⁻¹) * (x ^ a * z ^ b)⁻¹ := by group
    _ = (q * x * q⁻¹) ^ a * (q * z * q⁻¹) ^ b * (x ^ a * z ^ b)⁻¹ := by
        rw [← conj_zpow, ← conj_zpow]
    _ = ((q * x * q⁻¹ * x⁻¹) * x) ^ a * z ^ b * (x ^ a * z ^ b)⁻¹ := by rw [← e, hqzc]
    _ = (q * x * q⁻¹ * x⁻¹) ^ a * x ^ a * z ^ b * (x ^ a * z ^ b)⁻¹ := by
        rw [hζx.mul_zpow]
    _ = (q * x * q⁻¹ * x⁻¹) ^ a := by group

omit [Finite V] in
theorem theta_mul {x z a b : MulAut V} (haz : a * z = z * a)
    (hb : b * x * b⁻¹ * x⁻¹ ∈ Subgroup.zpowers z) (ha : a * x * a⁻¹ * x⁻¹ ∈ Subgroup.zpowers z) :
    a * b * x * (a * b)⁻¹ * x⁻¹ = (a * x * a⁻¹ * x⁻¹) * (b * x * b⁻¹ * x⁻¹) := by
  obtain ⟨ma, hma⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨mb, hmb⟩ := Subgroup.mem_zpowers_iff.mp hb
  have e1 : a * (b * x * b⁻¹ * x⁻¹) * a⁻¹ = b * x * b⁻¹ * x⁻¹ := by
    rw [← hmb]
    have := ((show Commute a z from haz).zpow_right mb).eq
    rw [this]
    group
  have e2 : (b * x * b⁻¹ * x⁻¹) * (a * x * a⁻¹ * x⁻¹) =
      (a * x * a⁻¹ * x⁻¹) * (b * x * b⁻¹ * x⁻¹) := by
    rw [← hma, ← hmb]
    exact ((Commute.refl z).zpow_zpow mb ma).eq
  calc a * b * x * (a * b)⁻¹ * x⁻¹
      = (a * (b * x * b⁻¹ * x⁻¹) * a⁻¹) * (a * x * a⁻¹ * x⁻¹) := by group
    _ = (b * x * b⁻¹ * x⁻¹) * (a * x * a⁻¹ * x⁻¹) := by rw [e1]
    _ = _ := e2

theorem card_normR (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) (hX1 : ∀ Y ∈ Xk X 1, False)
    (h : InvPair X t x) (hg : Good X t x z) (hne : ∃ q ∈ normR X x, q ∉ centR X x) :
    Nat.card (normR X x) = 27 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨hxo, hzo, hxz, hne', hsup⟩ := Good.E9 hV c hX1 h hg
  have hzc : Nat.card (Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, hzo]
  have hθ : ∀ q ∈ normR X x, q * x * q⁻¹ * x⁻¹ ∈ Subgroup.zpowers z := fun q hq =>
    normR_x_mod_z hV c hX1 h hg hq
  let θ : ↥(normR X x) →* ↥(Subgroup.zpowers z) :=
    MonoidHom.mk' (fun q => ⟨(q : MulAut V) * x * (q : MulAut V)⁻¹ * x⁻¹, hθ q q.2⟩) (by
      intro a b
      apply Subtype.ext
      exact theta_mul (normR_comm_z hV c hX1 h hg a.2) (hθ b b.2) (hθ a a.2))
  have hker : θ.ker = (centR X x).subgroupOf (normR X x) := by
    ext q
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hq
      have h1 : (q : MulAut V) * x * (q : MulAut V)⁻¹ * x⁻¹ = 1 := congrArg Subtype.val hq
      have h2 : (q : MulAut V) * x * (q : MulAut V)⁻¹ = x := mul_inv_eq_one.mp h1
      exact mem_centR.mpr ⟨q.2.1, mul_inv_eq_iff_eq_mul.mp h2⟩
    · intro hq
      apply Subtype.ext
      show (q : MulAut V) * x * (q : MulAut V)⁻¹ * x⁻¹ = 1
      have := (mem_centR.mp hq).2
      rw [this]
      group
  have hPQ : centR X x ≤ normR X x := centR_le_normR
  have hidx : θ.ker.index = Nat.card θ.range := Subgroup.index_ker θ
  have hrange : Nat.card θ.range ∣ 3 := by
    rw [← hzc]
    exact Subgroup.card_subgroup_dvd_card θ.range
  have hkcard : Nat.card θ.ker = 9 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPQ).toEquiv, hg.card]
  have hmul := Subgroup.card_mul_index θ.ker
  rw [hkcard] at hmul
  have hidx3 : θ.ker.index ∣ 3 := by rw [hidx]; exact hrange
  have hidx1 : θ.ker.index ≠ 1 := by
    intro h1
    obtain ⟨q, hq, hqP⟩ := hne
    have htop : θ.ker = ⊤ := Subgroup.index_eq_one.mp h1
    have : (⟨q, hq⟩ : ↥(normR X x)) ∈ θ.ker := by rw [htop]; exact Subgroup.mem_top _
    rw [hker, Subgroup.mem_subgroupOf] at this
    exact hqP this
  have hidx3' : θ.ker.index = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hidx3 with h1 | h1
    · exact absurd h1 hidx1
    · exact h1
  rw [hidx3'] at hmul
  omega

theorem central_cube_mem_Z (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X)
    (hX1 : ∀ Y ∈ Xk X 1, False) (h : InvPair X t x) (hg : Good X t x z)
    (hne : ∃ q ∈ normR X x, q ∉ centR X x) {ζ : MulAut V} (hζR : ζ ∈ pCoreOf 3 X)
    (hζc : ∀ r ∈ pCoreOf 3 X, ζ * r = r * ζ) : ζ ∈ Subgroup.zpowers z := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨hxo, hzo, hxz, hne', hsup⟩ := Good.E9 hV c hX1 h hg
  have hx3 : x ^ 3 = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
  have hx3z : x ^ (3 : ℤ) = 1 := by exact_mod_cast hx3
  have hζP : ζ ∈ centR X x := mem_centR.mpr ⟨hζR, (hζc x h.hx)⟩
  have hζE : ζ ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers z := by rw [hsup]; exact hζP
  obtain ⟨-, -, hform⟩ := E9_data hxo hzo hxz hne'
  obtain ⟨a, b, hab⟩ := hform ζ hζE
  obtain ⟨q, hq, hqP⟩ := hne
  have hconj := normR_conj_zpow hV c hX1 h hg hq a b
  rw [← hab] at hconj
  have hcomm : q * ζ * q⁻¹ * ζ⁻¹ = 1 := by
    rw [← hζc q hq.1]
    group
  rw [hcomm] at hconj
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (normR_x_mod_z hV c hX1 h hg hq)
  have hζq1 : q * x * q⁻¹ * x⁻¹ ≠ 1 := by
    intro e
    apply hqP
    have h2 : q * x * q⁻¹ = x := mul_inv_eq_one.mp e
    exact mem_centR.mpr ⟨hq.1, mul_inv_eq_iff_eq_mul.mp h2⟩
  have hζq3 : (q * x * q⁻¹ * x⁻¹) ^ 3 = 1 := by
    rw [← hm]
    exact zpow_cube_eq_one (hg.cube z hg.hz) m
  have hζqo : orderOf (q * x * q⁻¹ * x⁻¹) = 3 := orderOf_eq_prime hζq3 hζq1
  have hdvd : ((3 : ℕ) : ℤ) ∣ a := by
    rw [← hζqo]
    exact orderOf_dvd_iff_zpow_eq_one.mpr hconj.symm
  obtain ⟨k, hk⟩ := hdvd
  have hxa : x ^ a = 1 := by
    rw [hk]
    push_cast
    rw [zpow_mul, hx3z, one_zpow]
  rw [hab, hxa, one_mul]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) b

theorem exists_central_cube (h : InvPair X t x) :
    ∃ ζ ∈ pCoreOf 3 X, ζ ≠ 1 ∧ ζ ^ 3 = 1 ∧ ∀ r ∈ pCoreOf 3 X, ζ * r = r * ζ := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : Nontrivial ↥(pCoreOf 3 X) :=
    ⟨⟨⟨x, h.hx⟩, 1, fun e => h.hx1 (congrArg Subtype.val e)⟩⟩
  have := IsPGroup.center_nontrivial (pCoreOf_isPGroup 3 X)
  obtain ⟨c₀, hc₀⟩ := exists_ne (1 : ↥(Subgroup.center ↥(pCoreOf 3 X)))
  set g₀ : ↥(pCoreOf 3 X) := (c₀ : ↥(pCoreOf 3 X)) with hg₀
  have hg₁ : g₀ ≠ 1 := fun e => hc₀ (Subtype.ext e)
  obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf).mp (pCoreOf_isPGroup 3 X) g₀
  have ha1 : 1 ≤ a := by
    by_contra h0
    have : a = 0 := by omega
    rw [this, pow_zero, orderOf_eq_one_iff] at ha
    exact hg₁ ha
  have h3 : 3 ∣ orderOf g₀ := by rw [ha]; exact dvd_pow_self 3 (by omega)
  have hco : orderOf g₀ ≠ 0 := (orderOf_pos g₀).ne'
  obtain ⟨ζ', hζ'⟩ : ∃ ζ', ζ' = g₀ ^ (orderOf g₀ / 3) := ⟨_, rfl⟩
  have hζo : orderOf ζ' = 3 := by rw [hζ']; exact orderOf_pow_orderOf_div hco h3
  have hζ3 : ζ' ^ 3 = 1 := by
    have := pow_orderOf_eq_one ζ'
    rwa [hζo] at this
  have hζ1 : ζ' ≠ 1 := fun e => by rw [e, orderOf_one] at hζo; omega
  have hζc : ζ' ∈ Subgroup.center ↥(pCoreOf 3 X) := by
    rw [hζ']
    exact Subgroup.pow_mem _ c₀.2 _
  refine ⟨(ζ' : MulAut V), ζ'.2, fun e => hζ1 (Subtype.ext e), ?_, fun r hr => ?_⟩
  · exact congrArg Subtype.val hζ3
  · have := Subgroup.mem_center_iff.mp hζc ⟨r, hr⟩
    exact congrArg Subtype.val this.symm

theorem z_central (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) (hX1 : ∀ Y ∈ Xk X 1, False)
    (h : InvPair X t x) (hg : Good X t x z) (hne : ∃ q ∈ normR X x, q ∉ centR X x) :
    ∀ r ∈ pCoreOf 3 X, z * r = r * z := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨ζ, hζR, hζ1, hζ3, hζc⟩ := exists_central_cube h
  have hmem := central_cube_mem_Z hV c hX1 h hg hne hζR hζc
  obtain ⟨-, hzo, -⟩ := Good.E9 hV c hX1 h hg
  have hzc : Nat.card (Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, hzo]
  have heq : Subgroup.zpowers ζ = Subgroup.zpowers z := zpowers_eq_of_prime_card hzc hmem hζ1
  have hz_in : z ∈ Subgroup.zpowers ζ := by rw [heq]; exact Subgroup.mem_zpowers z
  intro r hr
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz_in
  rw [← hk]
  exact ((show Commute ζ r from hζc r hr).zpow_left k).eq

end Basic

end CFSG.Quasithin
