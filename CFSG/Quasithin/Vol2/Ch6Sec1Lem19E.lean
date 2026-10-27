module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem19T

public section

namespace CFSG.Quasithin.H13.L619

open CFSG.Open CFSG.LieType.BorelTits CFSG.Quasithin
open scoped commutatorElement

theorem central_eq_one_of_abelian_sylow {E : Type*} [Group E] [Finite E] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hgen : Subgroup.closure {x : E | ∃ k : ℕ, x ^ 2 ^ k = 1} = ⊤)
    (P : Sylow p E) (hP : IsMulCommutative (P : Subgroup E)) {a : E}
    (ha : a ∈ Subgroup.center E) {j : ℕ} (haj : a ^ p ^ j = 1) : a = 1 := by
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp (orderOf_dvd_of_pow_eq_one haj)
  have hzp : IsPGroup p (Subgroup.zpowers a) :=
    IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  have : (Subgroup.zpowers a).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : n ∈ Subgroup.center E := (Subgroup.zpowers_le.mpr ha) hn
    rw [Subgroup.mem_center_iff] at hn'
    rw [hn' g, mul_inv_cancel_right]
    exact hn
  have haP : a ∈ (P : Subgroup E) := hzp.le_sylow_of_normal P (Subgroup.mem_zpowers a)
  have hder := central_mem_sylow_derived_of_closure hp2 hgen P ⟨a, haP⟩ ha
  rw [commutator_eq_bot] at hder
  simpa using congrArg Subtype.val (Subgroup.mem_bot.mp hder)

theorem isMulCommutative_sylow_of_cyclic {E D : Type*} [Group E] [Finite E] [Group D] [Finite D]
    (η : E →* D) (hsurj : Function.Surjective η) (hcentral : η.ker ≤ Subgroup.center E)
    {p : ℕ} [Fact p.Prime] (hcyc : ∀ R : Sylow p D, IsCyclic R) (P : Sylow p E) :
    IsMulCommutative (P : Subgroup E) := by
  let R : Sylow p D := Sylow.mapSurjective hsurj P
  have : IsCyclic R := hcyc R
  let φ : (P : Subgroup E) →* R :=
    (η.comp (P : Subgroup E).subtype).codRestrict (R : Subgroup D) (by
      intro b
      change η (b : E) ∈ (R : Subgroup D)
      rw [Sylow.coe_mapSurjective]
      exact Subgroup.mem_map_of_mem η b.property)
  have hφcentral : φ.ker ≤ Subgroup.center (P : Subgroup E) := by
    intro b hb
    have hbker : (b : E) ∈ η.ker := congrArg Subtype.val hb
    apply Subgroup.mem_center_iff.mpr
    intro c
    exact Subtype.ext ((Subgroup.mem_center_iff.mp (hcentral hbker)) (c : E))
  exact φ.isMulCommutative_of_isCyclic_of_ker_le_center hφcentral

theorem central_ker_eq_bot_of_abelian {E D : Type*} [Group E] [Finite E] [Group D]
    (η : E →* D) (hcentral : η.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card η.ker))
    (hgen : Subgroup.closure {x : E | ∃ k : ℕ, x ^ 2 ^ k = 1} = ⊤)
    (habel : ∀ p [Fact p.Prime], p ≠ 2 → ∃ P : Sylow p E, IsMulCommutative (P : Subgroup E)) :
    η.ker = ⊥ := by
  classical
  rw [eq_bot_iff]
  intro x hx
  by_contra hxone
  have hcard : Nat.card η.ker ≠ 1 := by
    intro hcard
    have hbot : η.ker = ⊥ := Subgroup.card_eq_one.mp hcard
    exact hxone (by rw [hbot] at hx; exact hx)
  obtain ⟨p, hp, hpdiv⟩ := Nat.exists_prime_and_dvd hcard
  have : Fact p.Prime := ⟨hp⟩
  have hpodd : p ≠ 2 := by
    intro heq
    exact hodd.not_two_dvd_nat (heq ▸ hpdiv)
  obtain ⟨a, haorder⟩ := exists_prime_orderOf_dvd_card' (G := η.ker) p hpdiv
  have haEorder : orderOf (a : E) = p := (Subgroup.orderOf_coe a).trans haorder
  obtain ⟨P, hP⟩ := habel p hpodd
  have ha1 := central_eq_one_of_abelian_sylow hpodd hgen P hP (hcentral a.2) (j := 1)
    (by rw [pow_one, ← haEorder, pow_orderOf_eq_one])
  rw [ha1, orderOf_one] at haEorder
  exact hp.ne_one haEorder.symm

theorem commute_lift_of_commutator {E D : Type*} [Group E] [Group D] (η : E →* D)
    (hsurj : Function.Surjective η) (hcentral : η.ker ≤ Subgroup.center E) {X Y : Subgroup D}
    (hXY : ∀ a ∈ X, ∀ b ∈ Y, a * b = b * a) {x y : D} (hx : x ∈ ⁅X, X⁆) (hy : y ∈ Y)
    {x' y' : E} (hx' : η x' = x) (hy' : η y' = y) : x' * y' = y' * x' := by
  set c : E → E := fun u => u * y' * u⁻¹ * y'⁻¹ with hc
  have hcen : ∀ u : E, η u ∈ X → c u ∈ Subgroup.center E := by
    intro u hu
    refine hcentral ?_
    rw [MonoidHom.mem_ker, hc]
    simp only [map_mul, map_inv, hy', hXY _ hu _ hy, mul_inv_cancel_right, mul_inv_cancel]
  have hmul : ∀ u v : E, η v ∈ X → c (u * v) = c v * c u := by
    intro u v hv
    have hcv := Subgroup.mem_center_iff.mp (hcen v hv)
    calc c (u * v) = u * c v * y' * u⁻¹ * y'⁻¹ := by simp only [hc]; group
      _ = c v * u * y' * u⁻¹ * y'⁻¹ := by rw [hcv u]
      _ = c v * c u := by simp only [hc]; group
  have hone : c 1 = 1 := by simp [hc]
  have hinv : ∀ u : E, η u ∈ X → c u⁻¹ = (c u)⁻¹ := by
    intro u hu
    have h := hmul u⁻¹ u hu
    rw [inv_mul_cancel, hone] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  have hcomm : ∀ a b : E, c a ∈ Subgroup.center E → c b * c a = c a * c b := fun a b ha =>
    (Subgroup.mem_center_iff.mp ha (c b))
  set X' := X.comap η with hX'
  have hkey : ∀ w ∈ ⁅X', X'⁆, η w ∈ X ∧ c w = 1 := by
    intro w hw
    rw [Subgroup.commutator_def] at hw
    induction hw using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hw
      have ha' : η a ∈ X := ha
      have hb' : η b ∈ X := hb
      have hai : η a⁻¹ ∈ X := by rw [map_inv]; exact X.inv_mem ha'
      have hbi : η b⁻¹ ∈ X := by rw [map_inv]; exact X.inv_mem hb'
      have hX : η ⁅a, b⁆ ∈ X := by
        rw [commutatorElement_def, map_mul, map_mul, map_mul]
        exact X.mul_mem (X.mul_mem (X.mul_mem ha' hb') hai) hbi
      refine ⟨hX, ?_⟩
      rw [commutatorElement_def, hmul _ _ hbi, hmul _ _ hai, hmul _ _ hb', hinv _ ha',
        hinv _ hb']
      have h1 := hcen a ha'
      have h2 := hcen b hb'
      calc (c b)⁻¹ * ((c a)⁻¹ * (c b * c a))
          = (c b)⁻¹ * ((c a)⁻¹ * (c a * c b)) := by rw [hcomm a b h1]
        _ = 1 := by group
    | one => exact ⟨by rw [map_one]; exact X.one_mem, hone⟩
    | mul u v _ _ hu hv =>
      refine ⟨by rw [map_mul]; exact X.mul_mem hu.1 hv.1, ?_⟩
      rw [hmul u v hv.1, hu.2, hv.2, mul_one]
    | inv u _ hu =>
      refine ⟨by rw [map_inv]; exact X.inv_mem hu.1, ?_⟩
      rw [hinv u hu.1, hu.2, inv_one]
  have hmap : (⁅X', X'⁆).map η = ⁅X, X⁆ := by
    rw [Subgroup.map_commutator, hX', Subgroup.map_comap_eq_self_of_surjective hsurj]
  rw [← hmap] at hx
  obtain ⟨w, hw, hwx⟩ := hx
  obtain ⟨hwX, hcw⟩ := hkey w hw
  have hκ : w⁻¹ * x' ∈ η.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hwx, hx', inv_mul_cancel]
  have hκc := hcentral hκ
  have hcκ : c (w⁻¹ * x') = 1 := by
    simp only [hc]
    rw [(Subgroup.mem_center_iff.mp hκc y').symm]
    group
  have hx'X : η (w⁻¹ * x') ∈ X := by
    rw [MonoidHom.mem_ker.mp hκ]
    exact X.one_mem
  have hfin : c x' = 1 := by
    have e : x' = w * (w⁻¹ * x') := by group
    rw [e, hmul _ _ hx'X, hcκ, hcw, one_mul]
  have : x' * y' * x'⁻¹ * y'⁻¹ = 1 := hfin
  calc x' * y' = x' * y' * x'⁻¹ * y'⁻¹ * (y' * x') := by group
    _ = y' * x' := by rw [this, one_mul]


theorem isMulCommutative_closure_pair {E : Type*} [Group E] {a b : E} (hab : a * b = b * a) :
    IsMulCommutative ↥(Subgroup.closure ({a, b} : Set E)) := by
  have h1 : Subgroup.closure ({a, b} : Set E) ≤ Subgroup.centralizer ({a, b} : Set E) := by
    rw [Subgroup.closure_le]
    rintro u (rfl | rfl) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] <;>
      rintro v (rfl | rfl) <;> simp [hab]
  have h2 : Subgroup.closure ({a, b} : Set E) ≤
      Subgroup.centralizer (Subgroup.closure ({a, b} : Set E) : Set E) := by
    rw [Subgroup.le_centralizer_iff]
    rw [Subgroup.closure_le]
    intro u hu
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro v hv
    exact ((Subgroup.mem_centralizer_iff.mp (h1 hv)) u hu).symm
  exact ⟨⟨fun u v => Subtype.ext (Subgroup.mem_centralizer_iff.mp (h2 u.2) v v.2).symm⟩⟩

theorem exists_abelian_sylow_of_commute {E D : Type*} [Group E] [Finite E] [Group D] (η : E →* D)
    (hsurj : Function.Surjective η) (hcentral : η.ker ≤ Subgroup.center E) {X Y : Subgroup D}
    (hXY : ∀ a ∈ X, ∀ b ∈ Y, a * b = b * a) {p : ℕ} [hp : Fact p.Prime] {x y : D}
    (hx : x ∈ ⁅X, X⁆) (hy : y ∈ Y) {i j : ℕ} (hx3 : x ^ p ^ i = 1) (hy3 : y ^ p ^ j = 1)
    (hS : ∀ R : Subgroup D, IsPGroup p R → Subgroup.closure ({x, y} : Set D) ≤ R →
      R ≤ Subgroup.closure ({x, y} : Set D)) :
    ∃ P : Sylow p E, IsMulCommutative (P : Subgroup E) := by
  obtain ⟨x', hxx', a, ha⟩ := exists_pow_prime_pow_lift η hsurj hp.out hx3
  obtain ⟨y', hyy', b, hb⟩ := exists_pow_prime_pow_lift η hsurj hp.out hy3
  have hxy' : x' * y' = y' * x' :=
    commute_lift_of_commutator η hsurj hcentral hXY hx hy hxx' hyy'
  set B := Subgroup.closure ({x', y'} : Set E) with hB
  have hBab := isMulCommutative_closure_pair hxy'
  have hB3 : IsPGroup p B := by
    have hzx : IsPGroup p (Subgroup.zpowers x') := by
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp.out).mp (orderOf_dvd_of_pow_eq_one ha)
      exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
    have hzy : IsPGroup p (Subgroup.zpowers y') := by
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp.out).mp (orderOf_dvd_of_pow_eq_one hb)
      exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
    have hnorm : Subgroup.zpowers x' ≤ Subgroup.normalizer (Subgroup.zpowers y' : Set E) := by
      rw [Subgroup.zpowers_le]
      refine Subgroup.mem_normalizer_iff.mpr fun g => ?_
      have hc : Commute x' y' := hxy'
      constructor
      · intro hg
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
        rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
        exact Subgroup.zpow_mem_zpowers _ _
      · intro hg
        have e : g = x'⁻¹ * (x' * g * x'⁻¹) * x' := by group
        rw [e]
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
        rw [← hk, ((hc.inv_left).zpow_right k).eq, inv_mul_cancel_right]
        exact Subgroup.zpow_mem_zpowers _ _
    have heq : B = Subgroup.zpowers x' ⊔ Subgroup.zpowers y' := by
      rw [hB, show ({x', y'} : Set E) = {x'} ∪ {y'} from rfl, Subgroup.closure_union,
        Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure]
    rw [heq]
    exact hzx.to_sup_of_normal_right' hzy hnorm
  obtain ⟨P, hP⟩ := hB3.exists_le_sylow
  refine ⟨P, ⟨⟨fun u v => Subtype.ext ?_⟩⟩⟩
  have hmapB : B.map η = Subgroup.closure ({x, y} : Set D) := by
    rw [hB, MonoidHom.map_closure, Set.image_pair, hxx', hyy']
  have hPle : (P : Subgroup E).map η ≤ Subgroup.closure ({x, y} : Set D) :=
    hS _ (P.isPGroup'.map η) (hmapB ▸ Subgroup.map_mono hP)
  have hdecomp : ∀ w : E, w ∈ (P : Subgroup E) → ∃ β ∈ B, β⁻¹ * w ∈ Subgroup.center E := by
    intro w hw
    have hw' : η w ∈ B.map η := hmapB ▸ hPle ⟨w, hw, rfl⟩
    obtain ⟨β, hβ, hβw⟩ := hw'
    refine ⟨β, hβ, hcentral ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hβw, inv_mul_cancel]
  obtain ⟨β₁, hβ₁, hκ₁⟩ := hdecomp u u.2
  obtain ⟨β₂, hβ₂, hκ₂⟩ := hdecomp v v.2
  have hβ : β₁ * β₂ = β₂ * β₁ := congrArg Subtype.val
    (hBab.is_comm.comm ⟨β₁, hβ₁⟩ ⟨β₂, hβ₂⟩)
  set κ₁ := β₁⁻¹ * (u : E) with hk₁
  set κ₂ := β₂⁻¹ * (v : E) with hk₂
  have e₁ : (u : E) = β₁ * κ₁ := by rw [hk₁]; group
  have e₂ : (v : E) = β₂ * κ₂ := by rw [hk₂]; group
  have c₁ := Subgroup.mem_center_iff.mp hκ₁
  have c₂ := Subgroup.mem_center_iff.mp hκ₂
  show (u : E) * v = v * u
  rw [e₁, e₂]
  calc β₁ * κ₁ * (β₂ * κ₂) = β₁ * (κ₁ * β₂) * κ₂ := by group
    _ = β₁ * (β₂ * κ₁) * κ₂ := by rw [← c₁ β₂]
    _ = β₁ * β₂ * (κ₁ * κ₂) := by group
    _ = β₂ * β₁ * (κ₂ * κ₁) := by rw [hβ, c₂ κ₁]
    _ = β₂ * (β₁ * κ₂) * κ₁ := by group
    _ = β₂ * (κ₂ * β₁) * κ₁ := by rw [c₂ β₁]
    _ = β₂ * κ₂ * (β₁ * κ₁) := by group

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_eq_of_mem_zpowers {x r : G} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) {m : ℕ}
    (hr : r ^ 3 ^ m = 1) (hmem : r * x * r⁻¹ ∈ Subgroup.zpowers x) : r * x * r⁻¹ = x := by
  have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hk' : r * x * r⁻¹ = x ^ (k % 3) := by
    rw [← hk, ← zpow_mod_orderOf, hord]; norm_cast
  have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hmod with h0 | h1 | h2
  · exfalso
    rw [h0, zpow_zero] at hk'
    have : x = 1 := by
      have e : x = r⁻¹ * (r * x * r⁻¹) * r := by group
      rw [e, hk']; group
    exact hx1 this
  · rw [h1, zpow_one] at hk'; exact hk'
  · exfalso
    rw [h2] at hk'
    have h2' : x ^ ((2 : ℤ)) = x⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← zpow_add_one, show (2 : ℤ) + 1 = (3 : ℕ) by norm_num,
        zpow_natCast, hx3]
    have hinv : r * x * r⁻¹ = x⁻¹ := hk'.trans h2'
    have hpow : ∀ j : ℕ, r ^ (2 * j + 1) * x * (r ^ (2 * j + 1))⁻¹ = x⁻¹ := by
      intro j
      induction j with
      | zero => simpa using hinv
      | succ j ih =>
        have e : r ^ (2 * (j + 1) + 1) = r * r * r ^ (2 * j + 1) := by
          rw [show 2 * (j + 1) + 1 = 2 + (2 * j + 1) by ring, pow_add, pow_two]
        calc r ^ (2 * (j + 1) + 1) * x * (r ^ (2 * (j + 1) + 1))⁻¹
            = r * (r * (r ^ (2 * j + 1) * x * (r ^ (2 * j + 1))⁻¹) * r⁻¹) * r⁻¹ := by
              rw [e]; group
          _ = r * (r * x⁻¹ * r⁻¹) * r⁻¹ := by rw [ih]
          _ = r * (r * x * r⁻¹)⁻¹ * r⁻¹ := by group
          _ = x⁻¹ := by rw [hinv, inv_inv, hinv]
    obtain ⟨j, hj⟩ : ∃ j, 3 ^ m = 2 * j + 1 := (Odd.pow (by decide : Odd 3)).exists_bit1
    have := hpow j
    rw [← hj, hr, one_mul, inv_one, mul_one] at this
    have hx2 : x ^ 2 = 1 := by
      rw [pow_two]
      calc x * x = x * x⁻¹ := by rw [← this]
        _ = 1 := mul_inv_cancel x
    have : x = 1 := by
      calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
        _ = 1 := by rw [hx3, hx2]; group
    exact hx1 this

theorem three_le_pRank_of_two_comps {J I D A₁ A₂ : Subgroup G} (hA₁ : ThreeComp J A₁)
    (hA₂ : ThreeComp J A₂) (hinf : A₁ ⊓ A₂ ≤ pCoreOf 2 A₁)
    (hAI : A₁ ⊔ A₂ ≤ I) (hDI : D ≤ Subgroup.normalizer (I : Set G)) (hDinf : D ⊓ I = ⊥)
    (hD3 : Nat.card D = 3) (hD₁ : D ≤ Subgroup.normalizer (A₁ : Set G))
    (hD₂ : D ≤ Subgroup.normalizer (A₂ : Set G)) :
    3 ≤ CFSG.Open.pRank 3 (A₁ ⊔ A₂ ⊔ D) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X := A₁ ⊔ A₂ ⊔ D with hX
  have hA₁X : A₁ ≤ X := le_sup_left.trans le_sup_left
  have hA₂X : A₂ ≤ X := le_sup_right.trans le_sup_left
  have hDX : D ≤ X := le_sup_right
  have hXA₁ : X ≤ Subgroup.normalizer (A₁ : Set G) :=
    sup_le (sup_le Subgroup.le_normalizer (hA₂.le.trans hA₁.normal)) hD₁
  have hXA₂ : X ≤ Subgroup.normalizer (A₂ : Set G) :=
    sup_le (sup_le (hA₁.le.trans hA₂.normal) Subgroup.le_normalizer) hD₂
  have hXI : X ≤ Subgroup.normalizer (I : Set G) :=
    sup_le (hAI.trans Subgroup.le_normalizer) hDI
  obtain ⟨R⟩ := (inferInstance : Nonempty (Sylow 3 ↥X))
  set R' := (R : Subgroup ↥X).map X.subtype with hR'
  have hR3 : IsPGroup 3 R' := R.2.map _
  obtain ⟨x₀, hx₀A, hx₀R, hx₀3⟩ := exists_mem_sylow_of_orderOf hA₁X hXA₁ R
    hA₁.exists_three.choose_spec.1 hA₁.exists_three.choose_spec.2
  obtain ⟨x₁, hx₁A, hx₁R, hx₁3⟩ := exists_mem_sylow_of_orderOf hA₂X hXA₂ R
    hA₂.exists_three.choose_spec.1 hA₂.exists_three.choose_spec.2
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := ↥D) 3 (by rw [hD3])
  have hR'X : R' ≤ X := Subgroup.map_subtype_le _
  set d' : ↥X := ⟨(d : G), hDX d.2⟩ with hd'
  have hp : IsPGroup 3 (Subgroup.zpowers d') := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, pow_one, hd', Subgroup.orderOf_mk, Subgroup.orderOf_coe, hd]
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥X Q R
  set x₂ : G := (g : G) * d * (g : G)⁻¹ with hx₂
  have hx₂R : x₂ ∈ R' := by
    refine ⟨g * d' * g⁻¹, ?_, rfl⟩
    have hmem : g * d' * g⁻¹ ∈ ((g • Q : Sylow 3 ↥X) : Subgroup ↥X) :=
      Subgroup.smul_mem_pointwise_smul d' (MulAut.conj g) (Q : Subgroup ↥X)
        (hQ (Subgroup.mem_zpowers d'))
    rwa [hg] at hmem
  have hx₂3 : orderOf x₂ = 3 := by
    rw [← hd, ← Subgroup.orderOf_coe d]
    exact orderOf_injective (MulAut.conj (g : G)).toMonoidHom (MulAut.conj (g : G)).injective _
  have hx₂I : x₂ ∉ I := by
    intro hx
    have hdI : (d : G) ∈ I := (Subgroup.mem_normalizer_iff.mp (hXI g.2) (d : G)).mpr hx
    have hdD : (d : G) ∈ D ⊓ I := ⟨d.2, hdI⟩
    rw [hDinf, Subgroup.mem_bot] at hdD
    rw [show d = 1 from Subtype.ext hdD, orderOf_one] at hd
    omega
  have hcent : ∀ {A : Subgroup G}, ThreeComp J A → X ≤ Subgroup.normalizer (A : Set G) →
      ∀ {x : G}, x ∈ A → x ∈ R' → orderOf x = 3 → ∀ r ∈ R', r * x * r⁻¹ = x := by
    intro A hA hXA x hxA hxR hx3 r hr
    have hRA3 : IsPGroup 3 ↥(R' ⊓ A) := hR3.to_le inf_le_left
    have hcardRA : Nat.card ↥(R' ⊓ A) ≤ 3 := hA.card_le _ inf_le_right hRA3
    have hzle : Subgroup.zpowers x ≤ R' ⊓ A := Subgroup.zpowers_le.mpr ⟨hxR, hxA⟩
    have heq : Subgroup.zpowers x = R' ⊓ A :=
      Subgroup.eq_of_le_of_card_ge hzle (by rw [Nat.card_zpowers, hx3]; exact hcardRA)
    have hrx : r * x * r⁻¹ ∈ R' ⊓ A :=
      ⟨R'.mul_mem (R'.mul_mem hr hxR) (R'.inv_mem hr),
        (Subgroup.mem_normalizer_iff.mp (hXA (hR'X hr)) x).mp hxA⟩
    rw [← heq] at hrx
    obtain ⟨m, hm⟩ := hR3 ⟨r, hr⟩
    have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hx3; omega
    exact conj_eq_of_mem_zpowers (hx3 ▸ pow_orderOf_eq_one x) hx1
      (by simpa using congrArg Subtype.val hm) hrx
  have hc₀ := hcent hA₁ hXA₁ hx₀A hx₀R hx₀3
  have hc₁ := hcent hA₂ hXA₂ hx₁A hx₁R hx₁3
  have hcomm : ∀ {u v : G}, v * u * v⁻¹ = u → u * v = v * u := fun {u v} h => by
    calc u * v = v * u * v⁻¹ * v := by rw [h]
      _ = v * u := by group
  have hpow : ∀ {u : G}, orderOf u = 3 → u ^ 3 = 1 := fun h => h ▸ pow_orderOf_eq_one _
  have hord1 : ∀ {u : G} {O : Subgroup G}, IsPGroup 2 O → u ∈ O → orderOf u = 3 → False := by
    intro u O hO hu h3
    obtain ⟨b, hb⟩ := hO ⟨u, hu⟩
    have hb' : u ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
    have := orderOf_dvd_of_pow_eq_one hb'
    rw [h3] at this
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three this)
    omega
  have hx₀1 : x₀ ≠ 1 := fun h => by rw [h, orderOf_one] at hx₀3; omega
  have hx₁ : x₁ ∉ Subgroup.zpowers x₀ := by
    intro h
    have hx₁A' : x₁ ∈ A₁ := Subgroup.zpowers_le.mpr hx₀A h
    exact hord1 (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 A₁)
      (hinf ⟨hx₁A', hx₁A⟩) hx₁3
  have hx₂' : x₂ ∉ Subgroup.zpowers x₀ ⊔ Subgroup.zpowers x₁ := by
    intro h
    apply hx₂I
    have hle : Subgroup.zpowers x₀ ⊔ Subgroup.zpowers x₁ ≤ I :=
      sup_le ((Subgroup.zpowers_le.mpr hx₀A).trans (le_sup_left.trans hAI))
        ((Subgroup.zpowers_le.mpr hx₁A).trans (le_sup_right.trans hAI))
    exact hle h
  exact three_le_pRank_of_commute (hA₁X hx₀A) (hA₂X hx₁A) (hR'X hx₂R)
    (hcomm (hc₀ x₁ hx₁R)) (hcomm (hc₀ x₂ hx₂R)) (hcomm (hc₁ x₂ hx₂R))
    (hpow hx₀3) (hpow hx₁3) (hpow hx₂3) hx₀1 hx₁ hx₂'

end CFSG.Quasithin.H13.L619
