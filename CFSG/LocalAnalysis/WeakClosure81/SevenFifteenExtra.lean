module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Extraspecial
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open scoped commutatorElement

variable {G : Type*} [Group G]

private lemma exists_mul_of_mem_sup_of_le_normalizer {H K : Subgroup G}
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, h * k = x := by
  haveI : (K.subgroupOf (H ⊔ K)).Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hHK
  have htop : H.subgroupOf (H ⊔ K) ⊔ K.subgroupOf (H ⊔ K) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  have hx' : (⟨x, hx⟩ : ↥(H ⊔ K)) ∈ H.subgroupOf (H ⊔ K) ⊔ K.subgroupOf (H ⊔ K) := by
    rw [htop]; trivial
  obtain ⟨h, hh, k, hk, hhk⟩ := (Subgroup.mem_sup_of_normal_right).mp hx'
  exact ⟨(h : G), (Subgroup.mem_subgroupOf.mp hh), (k : G),
    (Subgroup.mem_subgroupOf.mp hk), congrArg Subtype.val hhk⟩

theorem exists_mulEquiv_quotient_of_complement {I Q P : Subgroup G} [(I.subgroupOf Q).Normal]
    (hPQ : P ≤ Q) (hPI : P ⊓ I = ⊥) (hPIQ : P ⊔ I = Q) :
    Nonempty (↥P ≃* (↥Q ⧸ I.subgroupOf Q)) := by
  let φ : ↥P →* (↥Q ⧸ I.subgroupOf Q) :=
    (QuotientGroup.mk' (I.subgroupOf Q)).comp (Subgroup.inclusion hPQ)
  have hmk : ∀ a : ↥P, φ a = (Subgroup.inclusion hPQ a : ↥Q ⧸ I.subgroupOf Q) := fun _ => rfl
  refine ⟨MulEquiv.ofBijective φ ⟨?_, ?_⟩⟩
  · intro a b hab
    have h1 : φ (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : Subgroup.inclusion hPQ (a * b⁻¹) ∈ I.subgroupOf Q :=
      (QuotientGroup.eq_one_iff (Subgroup.inclusion hPQ (a * b⁻¹))).mp (by
        rw [← hmk]; exact h1)
    have h3 : ((a * b⁻¹ : ↥P) : G) ∈ I := by
      have := (Subgroup.mem_subgroupOf).mp h2
      simpa using this
    have h4 : ((a * b⁻¹ : ↥P) : G) ∈ P ⊓ I := ⟨(a * b⁻¹).2, h3⟩
    rw [hPI] at h4
    have h4' : (a * b⁻¹ : ↥P) = 1 := Subtype.ext (Subgroup.mem_bot.mp h4)
    exact mul_inv_eq_one.mp h4'
  · intro q
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (I.subgroupOf Q) q
    have hIQ : I ≤ Q := le_sup_right.trans (le_of_eq hPIQ)
    have hPN : P ≤ Subgroup.normalizer (I : Set G) :=
      hPQ.trans (Subgroup.le_normalizer_of_normal_subgroupOf hIQ)
    have hx' : (x : G) ∈ P ⊔ I := by rw [hPIQ]; exact x.2
    obtain ⟨p, hpP, i, hiI, hpi⟩ := exists_mul_of_mem_sup_of_le_normalizer hPN hx'
    have hiQ : i ∈ Q := hIQ hiI
    refine ⟨⟨p, hpP⟩, ?_⟩
    change QuotientGroup.mk' (I.subgroupOf Q) (Subgroup.inclusion hPQ ⟨p, hpP⟩) = q
    rw [← hx, QuotientGroup.mk'_eq_mk']
    refine ⟨⟨i, hiQ⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]; exact hiI
    · apply Subtype.ext
      simpa [Subgroup.coe_mul, Subgroup.coe_inclusion] using hpi

theorem isExtraspecial_of_mulEquiv {p : ℕ} {M N : Type*} [Group M] [Group N] (e : M ≃* N)
    [CFSG.IsExtraspecial p N] : CFSG.IsExtraspecial p M where
  center_order_p := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact CFSG.IsExtraspecial.center_order_p p N
  quotient_elementary_abelian :=
    CFSG.IsElementaryAbelian.of_mulEquiv
      (QuotientGroup.congr (Subgroup.center M) (Subgroup.center N) e
        (Subgroup.map_center_eq e)).symm
      (CFSG.IsExtraspecial.quotient_elementary_abelian p N)
  quotient_nontrivial := by
    haveI := CFSG.IsExtraspecial.quotient_nontrivial p N
    exact (QuotientGroup.congr (Subgroup.center M) (Subgroup.center N) e
      (Subgroup.map_center_eq e)).toEquiv.nontrivial

theorem isExtraspecial_of_complement {p : ℕ} {I Q P : Subgroup G} [(I.subgroupOf Q).Normal]
    (hPQ : P ≤ Q) (hPI : P ⊓ I = ⊥) (hPIQ : P ⊔ I = Q)
    [CFSG.IsExtraspecial p (↥Q ⧸ I.subgroupOf Q)] : CFSG.IsExtraspecial p ↥P := by
  obtain ⟨e⟩ := exists_mulEquiv_quotient_of_complement hPQ hPI hPIQ
  exact isExtraspecial_of_mulEquiv e

theorem nat_card_eq_of_complement {I Q P : Subgroup G} [(I.subgroupOf Q).Normal]
    (hPQ : P ≤ Q) (hPI : P ⊓ I = ⊥) (hPIQ : P ⊔ I = Q) :
    Nat.card ↥P = Nat.card (↥Q ⧸ I.subgroupOf Q) := by
  obtain ⟨e⟩ := exists_mulEquiv_quotient_of_complement hPQ hPI hPIQ
  exact Nat.card_congr e

theorem exponent_eq_of_complement {I Q P : Subgroup G} [(I.subgroupOf Q).Normal]
    (hPQ : P ≤ Q) (hPI : P ⊓ I = ⊥) (hPIQ : P ⊔ I = Q) :
    Monoid.exponent ↥P = Monoid.exponent (↥Q ⧸ I.subgroupOf Q) := by
  obtain ⟨e⟩ := exists_mulEquiv_quotient_of_complement hPQ hPI hPIQ
  rw [Monoid.exponent_eq_of_mulEquiv e]

theorem commutator_zpowers_eq_of_complement {I Q V P : Subgroup G} {v : G}
    (hQI : Q ≤ Subgroup.normalizer (I : Set G)) (hvI : v ∈ Subgroup.normalizer (I : Set G))
    (hPI : P ⊓ I = ⊥) (hPIQ : P ⊔ I = Q) (hvP : v ∈ Subgroup.normalizer (P : Set G))
    (hVv : V ≤ Subgroup.zpowers v ⊔ I) (hgen : Q ≤ I ⊔ ⁅Q, V⁆) :
    ⁅P, Subgroup.zpowers v⁆ = P := by
  have hPQ : P ≤ Q := le_sup_left.trans (le_of_eq hPIQ)
  have hvPN : Subgroup.zpowers v ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.zpowers_le.mpr hvP
  have hvIN : Subgroup.zpowers v ≤ Subgroup.normalizer (I : Set G) :=
    Subgroup.zpowers_le.mpr hvI
  have hPN : P ≤ Subgroup.normalizer (I : Set G) := hPQ.trans hQI
  have hcommP : ⁅P, Subgroup.zpowers v⁆ ≤ P := by
    rw [Subgroup.commutator_le]
    intro p hp w hw
    have hwp : w * p * w⁻¹ ∈ P :=
      ((Subgroup.mem_normalizer_iff.mp (hvPN hw)) p).mp hp
    have heq : ⁅p, w⁆ = p * (w * p * w⁻¹)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [heq]
    exact P.mul_mem hp (P.inv_mem hwp)
  have hcommQ : ⁅Q, V⁆ ≤ I ⊔ ⁅P, Subgroup.zpowers v⁆ := by
    rw [Subgroup.commutator_le]
    intro q hq w hw
    obtain ⟨a, ha, i, hi, hai⟩ := exists_mul_of_mem_sup_of_le_normalizer hvIN (hVv hw)
    have haN : a ∈ Subgroup.normalizer (I : Set G) := hvIN ha
    have haiI : a * ⁅q, i⁆ * a⁻¹ ∈ I := by
      have hqi : ⁅q, i⁆ ∈ I := by
        have hqI : q * i * q⁻¹ ∈ I := ((Subgroup.mem_normalizer_iff.mp (hQI hq)) i).mp hi
        have he : ⁅q, i⁆ = (q * i * q⁻¹) * i⁻¹ := by
          rw [commutatorElement_def]
        rw [he]
        exact I.mul_mem hqI (I.inv_mem hi)
      exact ((Subgroup.mem_normalizer_iff.mp haN) ⁅q, i⁆).mp hqi
    have hqa : ⁅q, a⁆ ∈ I ⊔ ⁅P, Subgroup.zpowers v⁆ := by
      have hq' : q ∈ P ⊔ I := (le_of_eq hPIQ.symm) hq
      obtain ⟨p, hp, j, hj, hpj⟩ := exists_mul_of_mem_sup_of_le_normalizer hPN hq'
      have hja : ⁅j, a⁆ ∈ I := by
        have haj : a * j⁻¹ * a⁻¹ ∈ I :=
          ((Subgroup.mem_normalizer_iff.mp haN) j⁻¹).mp (I.inv_mem hj)
        have he : ⁅j, a⁆ = j * (a * j⁻¹ * a⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [he]
        exact I.mul_mem hj haj
      have hpjI : p * ⁅j, a⁆ * p⁻¹ ∈ I :=
        ((Subgroup.mem_normalizer_iff.mp (hQI (hPQ hp))) ⁅j, a⁆).mp hja
      have he : ⁅q, a⁆ = (p * ⁅j, a⁆ * p⁻¹) * ⁅p, a⁆ := by
        rw [← hpj]
        simp only [commutatorElement_def]; group
      rw [he]
      exact Subgroup.mul_mem_sup hpjI (Subgroup.commutator_mem_commutator hp ha)
    have he : ⁅q, w⁆ = ⁅q, a⁆ * (a * ⁅q, i⁆ * a⁻¹) := by
      rw [← hai, commutatorElement_mul_right_eq_mul_conj]
      group
    rw [he]
    exact (I ⊔ ⁅P, Subgroup.zpowers v⁆).mul_mem hqa (Subgroup.mem_sup_left haiI)
  have hQT : Q ≤ I ⊔ ⁅P, Subgroup.zpowers v⁆ :=
    hgen.trans (sup_le le_sup_left hcommQ)
  have hPT : P ≤ ⁅P, Subgroup.zpowers v⁆ := by
    intro p hp
    obtain ⟨c, hc, i, hi, hci⟩ :=
      exists_mul_of_mem_sup_of_le_normalizer (hcommP.trans hPN)
        (le_of_eq (sup_comm I ⁅P, Subgroup.zpowers v⁆) (hQT (hPQ hp)))
    have hcP : c ∈ P := hcommP hc
    have hiP : i ∈ P := by
      have he : i = c⁻¹ * p := by rw [← hci]; group
      rw [he]
      exact P.mul_mem (P.inv_mem hcP) hp
    have hib : i ∈ P ⊓ I := ⟨hiP, hi⟩
    rw [hPI] at hib
    have hi1 : i = 1 := Subgroup.mem_bot.mp hib
    rw [← hci, hi1, mul_one]
    exact hc
  exact le_antisymm hcommP hPT

structure HeisConfig (p : ℕ) (P : Subgroup G) (v x z g : G) : Prop where
  x_mem : x ∈ P
  z_mem : z ∈ P
  g_mem : g ∈ P
  x_pow : x ^ p = 1
  g_pow : g ^ p = 1
  z_pow : z ^ p = 1
  z_ne_one : z ≠ 1
  z_central : ∀ y ∈ P, y * z = z * y
  g_conj_x : g * x * g⁻¹ = x * z
  v_conj_x : v * x * v⁻¹ = x⁻¹
  v_comm_z : v * z = z * v
  le_closure : P ≤ Subgroup.closure ({x, g, z} : Set G)
  centralizer_le : ∀ y ∈ P, v * y = y * v → y ∈ Subgroup.zpowers z
  v_conj_mem : ∀ y ∈ P, ∃ c ∈ Subgroup.zpowers z, v * y * v⁻¹ = y⁻¹ * c

private lemma zpow_eq_one_or_self {G : Type*} [Group G] {v : G} (hv : v * v = 1) (n : ℤ) :
    v ^ n = 1 ∨ v ^ n = v := by
  have hv2 : v ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two, hv]
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' n
  · left
    rw [hk, zpow_mul, hv2, one_zpow]
  · right
    rw [hk, zpow_add, zpow_mul, hv2, one_zpow, one_mul, zpow_one]

private theorem commutator_eq_center_of_isExtraspecial {p : ℕ} [Fact p.Prime] {H : Type*} [Group H]
    [CFSG.IsExtraspecial p H] : commutator H = Subgroup.center H := by
  have hZtop : Subgroup.center H ≠ ⊤ := by
    intro h
    haveI : Nontrivial (H ⧸ Subgroup.center H) := CFSG.IsExtraspecial.quotient_nontrivial p H
    exact (not_subsingleton_iff_nontrivial.mpr ‹Nontrivial (H ⧸ Subgroup.center H)›)
      (QuotientGroup.subsingleton_iff.mpr h)
  have hle : commutator H ≤ Subgroup.center H := by
    haveI : IsElementaryAbelian p (H ⧸ Subgroup.center H) :=
      CFSG.IsExtraspecial.quotient_elementary_abelian p H
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [← QuotientGroup.eq_one_iff (⁅a, b⁆)]
    change (QuotientGroup.mk' (Subgroup.center H)) ⁅a, b⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm' _ _)
  have hbot : commutator H ≠ ⊥ := by
    intro h
    have hc : IsMulCommutative H := (commutator_eq_bot_iff H).mp h
    haveI : IsMulCommutative H := hc
    exact hZtop Subgroup.center_eq_top
  have hdiv : Nat.card (commutator H) ∣ p := by
    rw [← CFSG.IsExtraspecial.center_order_p p H]
    exact Subgroup.card_dvd_of_le hle
  have hne1 : Nat.card (commutator H) ≠ 1 := fun h =>
    hbot (Subgroup.eq_bot_of_card_eq (commutator H) h)
  have hpc : Nat.card (commutator H) = p := by
    rcases (Fact.out : Nat.Prime p).eq_one_or_self_of_dvd _ hdiv with h1 | hp
    · exact absurd h1 hne1
    · exact hp
  haveI : Finite (Subgroup.center H) :=
    Nat.finite_of_card_ne_zero (by
      rw [CFSG.IsExtraspecial.center_order_p p H]; exact (Fact.out : Nat.Prime p).ne_zero)
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [CFSG.IsExtraspecial.center_order_p p H, hpc])

private lemma commutatorElement_mul_mem_center {H : Type*} [Group H] (x y : H) {c d : H}
    (hc : c ∈ Subgroup.center H) (hd : d ∈ Subgroup.center H) : ⁅x * c, y * d⁆ = ⁅x, y⁆ := by
  have hc' : ∀ g : H, c * g * c⁻¹ = g := fun g => by
    rw [← Subgroup.mem_center_iff.1 hc g, mul_inv_cancel_right]
  have hd' : ∀ g : H, d * g * d⁻¹ = g := fun g => by
    rw [← Subgroup.mem_center_iff.1 hd g, mul_inv_cancel_right]
  calc ⁅x * c, y * d⁆ = x * (c * (y * d) * c⁻¹) * x⁻¹ * d⁻¹ * y⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = x * y * (d * x⁻¹ * d⁻¹) * y⁻¹ := by rw [hc']; group
    _ = ⁅x, y⁆ := by rw [hd', commutatorElement_def]

private lemma conj_eq_self_of_mem_center {H : Type*} [Group H] {z : H}
    (hz : z ∈ Subgroup.center H) (g : H) : g * z * g⁻¹ = z := by
  rw [Subgroup.mem_center_iff.1 hz g, mul_inv_cancel_right]

private lemma commutatorElement_inv_inv_of_mem_center {H : Type*} [Group H] {a b : H}
    (hab : ⁅a, b⁆ ∈ Subgroup.center H) : ⁅a⁻¹, b⁻¹⁆ = ⁅a, b⁆ := by
  have h1 : ⁅a⁻¹, b⁆ = ⁅a, b⁆⁻¹ := by
    rw [commutatorElement_inv_left, ← commutatorElement_inv]
    simpa using conj_eq_self_of_mem_center ((Subgroup.center H).inv_mem hab) a⁻¹
  calc ⁅a⁻¹, b⁻¹⁆ = b⁻¹ * ⁅b, a⁻¹⁆ * b := commutatorElement_inv_right a⁻¹ b
    _ = b⁻¹ * ⁅a, b⁆ * b := by rw [← commutatorElement_inv, h1, inv_inv]
    _ = ⁅a, b⁆ := by simpa using conj_eq_self_of_mem_center hab b⁻¹

private lemma conj_commutator_mul_self {H : Type*} [Group H] {p v : H} (hv : v * v = 1) :
    v * ⁅p, v⁆ * v⁻¹ * ⁅p, v⁆ = 1 := by
  have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  rw [commutatorElement_def, hv']
  calc v * (p * v * p⁻¹ * v) * v * (p * v * p⁻¹ * v)
      = v * p * v * p⁻¹ * (v * v) * p * v * p⁻¹ * v := by group
    _ = v * p * v * p⁻¹ * p * v * p⁻¹ * v := by rw [hv, mul_one]
    _ = v * p * (v * v) * p⁻¹ * v := by group
    _ = v * p * p⁻¹ * v := by rw [hv, mul_one]
    _ = v * v := by group
    _ = 1 := hv

private theorem exists_conj_data_of_isExtraspecial {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {P : Subgroup G} {v : G} [CFSG.IsExtraspecial p ↥P] (hcard : Nat.card ↥P = p ^ 3)
    (hv : v * v = 1) (hvP : v ∈ Subgroup.normalizer (P : Set G))
    (hPv : ⁅P, Subgroup.zpowers v⁆ = P) :
    ∃ σ : ↥P → ↥P,
      (∀ y : ↥P, (σ y : G) = v * (y : G) * v⁻¹) ∧
      (∀ y : ↥P, σ y * y ∈ Subgroup.center ↥P) ∧
      (∀ z ∈ Subgroup.center ↥P, σ z = z) := by

  haveI : Finite ↥P :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 3 (Fact.out : Nat.Prime p).ne_zero)
  haveI : IsElementaryAbelian p (↥P ⧸ Subgroup.center ↥P) :=
    CFSG.IsExtraspecial.quotient_elementary_abelian p ↥P
  let Z : Subgroup ↥P := Subgroup.center ↥P
  have hcommZ : commutator ↥P = Z := commutator_eq_center_of_isExtraspecial (p := p)
  have hHH : commutator ↥P ≤ Z := le_of_eq hcommZ
  let σ : ↥P → ↥P := fun y =>
    ⟨v * (y : G) * v⁻¹, ((Subgroup.mem_normalizer_iff.mp hvP) (y : G)).mp y.2⟩
  have hσ : ∀ y : ↥P, (σ y : G) = v * (y : G) * v⁻¹ := fun _ => rfl
  have hσ_mul : ∀ a b : ↥P, σ (a * b) = σ a * σ b := by
    intro a b; apply Subtype.ext
    simp only [Subgroup.coe_mul, hσ]; group
  have hσ_inv : ∀ a : ↥P, σ a⁻¹ = (σ a)⁻¹ := by
    intro a; apply Subtype.ext
    simp only [Subgroup.coe_inv, hσ]; group
  have hσ_one : σ 1 = 1 := by
    apply Subtype.ext; simp only [Subgroup.coe_one, hσ]; group
  let ψ : ↥P →* (↥P ⧸ Z) :=
    MonoidHom.mk' (fun y => (σ y * y : ↥P ⧸ Z)) (by
      intro a b
      change (QuotientGroup.mk' Z) (σ (a * b) * (a * b)) =
        (QuotientGroup.mk' Z) (σ a * a) * (QuotientGroup.mk' Z) (σ b * b)
      rw [hσ_mul]
      letI : CommMonoid (↥P ⧸ Z) :=
        { (inferInstance : Group (↥P ⧸ Z)) with mul_comm := fun x y => mul_comm' x y }
      simp only [map_mul]
      ac_rfl)
  have hψ : ∀ y : ↥P, ψ y = (σ y * y : ↥P ⧸ Z) := fun _ => rfl
  have hS : ∀ y : ↥P, y ∈ ψ.ker ↔ σ y * y ∈ Z := by
    intro y
    rw [MonoidHom.mem_ker, hψ]
    exact QuotientGroup.eq_one_iff (σ y * y)
  have hgen : ⁅P, Subgroup.zpowers v⁆ ≤ ψ.ker.map P.subtype := by
    rw [Subgroup.commutator_le]
    intro p hp w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    rcases zpow_eq_one_or_self hv k with hk | hk
    · rw [hk, commutatorElement_one_right]
      exact (ψ.ker.map P.subtype).one_mem
    · rw [hk]
      have hmemP : ⁅p, v⁆ ∈ P := by
        rw [← hPv]
        exact Subgroup.commutator_mem_commutator hp (Subgroup.mem_zpowers v)
      refine Subgroup.mem_map.mpr ⟨⟨⁅p, v⁆, hmemP⟩, ?_, rfl⟩
      rw [hS]
      have h1 : σ ⟨⁅p, v⁆, hmemP⟩ * ⟨⁅p, v⁆, hmemP⟩ = 1 := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_one, hσ]
        exact conj_commutator_mul_self hv
      rw [h1]
      exact Z.one_mem
  have hker_map : ψ.ker.map P.subtype = P := by
    apply le_antisymm
    · intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨s, -, rfl⟩
      exact s.2
    · exact (le_of_eq hPv.symm).trans hgen
  have hσy_mem : ∀ y : ↥P, σ y * y ∈ Z := by
    intro y
    have hy : (y : G) ∈ ψ.ker.map P.subtype := by rw [hker_map]; exact y.2
    rcases Subgroup.mem_map.mp hy with ⟨s, hs, hsy⟩
    have hsy' : s = y := Subtype.ext hsy
    rw [← hsy']
    exact (hS s).mp hs
  let Fix : Subgroup ↥P :=
    { carrier := {z | σ z = z}
      one_mem' := hσ_one
      mul_mem' := fun {a b} ha hb => by
        show σ (a * b) = a * b
        rw [hσ_mul, ha, hb]
      inv_mem' := fun {a} ha => by
        show σ a⁻¹ = a⁻¹
        rw [hσ_inv, ha] }
  have hfix : commutator ↥P ≤ Fix := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    show σ ⁅a, b⁆ = ⁅a, b⁆
    have hσc : σ ⁅a, b⁆ = ⁅σ a, σ b⁆ := by
      apply Subtype.ext
      simp only [hσ, Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]; group
    rw [hσc]
    have hca : σ a = a⁻¹ * (σ a * a) := by
      conv_lhs => rw [show σ a = (σ a * a) * a⁻¹ by group]
      rw [← Subgroup.mem_center_iff.1 (hσy_mem a) a⁻¹]
    have hcb : σ b = b⁻¹ * (σ b * b) := by
      conv_lhs => rw [show σ b = (σ b * b) * b⁻¹ by group]
      rw [← Subgroup.mem_center_iff.1 (hσy_mem b) b⁻¹]
    have hab : ⁅a, b⁆ ∈ Subgroup.center ↥P := by
      change ⁅a, b⁆ ∈ Z
      rw [← hcommZ]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [hca, hcb, commutatorElement_mul_mem_center a⁻¹ b⁻¹ (hσy_mem a) (hσy_mem b)]
    exact commutatorElement_inv_inv_of_mem_center hab
  have hσz : ∀ z ∈ Z, σ z = z := fun z hz => hfix (hcommZ.symm ▸ hz)
  exact ⟨σ, hσ, hσy_mem, hσz⟩

theorem inf_centralizer_eq_center {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {P : Subgroup G} {v : G}
    [CFSG.IsExtraspecial p ↥P] (hcard : Nat.card ↥P = p ^ 3) (hexp : Monoid.exponent ↥P = p)
    (hv : v * v = 1) (hvP : v ∈ Subgroup.normalizer (P : Set G))
    (hPv : ⁅P, Subgroup.zpowers v⁆ = P) :
    P ⊓ Subgroup.centralizer ({v} : Set G) = (Subgroup.center ↥P).map P.subtype := by
  haveI : Finite ↥P :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 3 (Fact.out : Nat.Prime p).ne_zero)
  let Z : Subgroup ↥P := Subgroup.center ↥P
  obtain ⟨σ, hσ, hσy_mem, hσz⟩ := exists_conj_data_of_isExtraspecial hp hcard hv hvP hPv
  have hcenter_le : (Subgroup.center ↥P).map P.subtype ≤
      P ⊓ Subgroup.centralizer ({v} : Set G) := by
    intro g hg
    rcases Subgroup.mem_map.mp hg with ⟨z, hz, rfl⟩
    refine ⟨z.2, ?_⟩
    change (z : G) ∈ Subgroup.centralizer ({v} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    have hcoe : v * (z : G) * v⁻¹ = (z : G) := by
      simpa only [hσ] using congrArg Subtype.val (hσz z hz)
    calc v * (z : G) = (v * (z : G) * v⁻¹) * v := by group
      _ = (z : G) * v := by rw [hcoe]
  have hcent_le : P ⊓ Subgroup.centralizer ({v} : Set G) ≤
      (Subgroup.center ↥P).map P.subtype := by
    intro g hg
    rcases hg with ⟨hgP, hgC⟩
    have hvg : v * g = g * v := (Subgroup.mem_centralizer_iff.mp hgC) v (Set.mem_singleton v)
    have hgy : σ ⟨g, hgP⟩ = ⟨g, hgP⟩ := by
      apply Subtype.ext
      simp only [hσ]
      rw [hvg]; group
    have hy2 : (⟨g, hgP⟩ : ↥P) * ⟨g, hgP⟩ ∈ Z := by
      have := hσy_mem ⟨g, hgP⟩
      rwa [hgy] at this
    have hyp : (⟨g, hgP⟩ : ↥P) ^ p = 1 := by
      have := Monoid.pow_exponent_eq_one (⟨g, hgP⟩ : ↥P)
      rwa [hexp] at this
    have h2 : (((⟨g, hgP⟩ : ↥P) : ↥P ⧸ Z)) ^ 2 = 1 := by
      change (QuotientGroup.mk' Z) ((⟨g, hgP⟩ : ↥P) ^ 2) = 1
      exact (QuotientGroup.eq_one_iff _).mpr (by rwa [pow_two])
    have hp' : (((⟨g, hgP⟩ : ↥P) : ↥P ⧸ Z)) ^ p = 1 := by
      change (QuotientGroup.mk' Z) ((⟨g, hgP⟩ : ↥P) ^ p) = 1
      exact (QuotientGroup.eq_one_iff _).mpr (by rw [hyp]; exact Z.one_mem)
    have hcop : Nat.gcd 2 p = 1 := by
      rcases (Fact.out : Nat.Prime p).eq_two_or_odd' with h2p | hodd
      · exact absurd h2p hp
      · exact Nat.coprime_comm.mp hodd.coprime_two_right
    have horder : orderOf (((⟨g, hgP⟩ : ↥P) : ↥P ⧸ Z)) = 1 := by
      have hdvd : orderOf (((⟨g, hgP⟩ : ↥P) : ↥P ⧸ Z)) ∣ 1 := by
        rw [← hcop]
        exact Nat.dvd_gcd (orderOf_dvd_iff_pow_eq_one.mpr h2)
          (orderOf_dvd_iff_pow_eq_one.mpr hp')
      exact Nat.dvd_one.mp hdvd
    exact Subgroup.mem_map.mpr ⟨⟨g, hgP⟩,
      (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp horder), rfl⟩
  exact le_antisymm hcent_le hcenter_le

theorem exists_heisConfig {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {P : Subgroup G} {v : G}
    [CFSG.IsExtraspecial p ↥P] (hcard : Nat.card ↥P = p ^ 3) (hexp : Monoid.exponent ↥P = p)
    (hv : v * v = 1) (hvP : v ∈ Subgroup.normalizer (P : Set G))
    (hPv : ⁅P, Subgroup.zpowers v⁆ = P) :
    ∃ x z g : G, HeisConfig p P v x z g := by
  haveI : Finite ↥P :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 3 (Fact.out : Nat.Prime p).ne_zero)
  let Z : Subgroup ↥P := Subgroup.center ↥P
  have hcommZ : commutator ↥P = Z := commutator_eq_center_of_isExtraspecial (p := p)
  have hZcard : Nat.card Z = p := CFSG.IsExtraspecial.center_order_p p ↥P
  obtain ⟨σ, hσ, hσy_mem, hσz⟩ := exists_conj_data_of_isExtraspecial hp hcard hv hvP hPv
  have hσ_mul : ∀ a b : ↥P, σ (a * b) = σ a * σ b := by
    intro a b; apply Subtype.ext
    simp only [hσ, Subgroup.coe_mul]; group
  have hσ_inv : ∀ a : ↥P, σ a⁻¹ = (σ a)⁻¹ := by
    intro a; apply Subtype.ext
    simp only [hσ, Subgroup.coe_inv]; group
  have hcop : Nat.gcd 2 p = 1 := by
    rcases (Fact.out : Nat.Prime p).eq_two_or_odd' with h2p | hodd
    · exact absurd h2p hp
    · exact Nat.coprime_comm.mp hodd.coprime_two_right
  have hZtop : Z ≠ ⊤ := by
    intro h
    haveI : Nontrivial (↥P ⧸ Z) := CFSG.IsExtraspecial.quotient_nontrivial p ↥P
    exact (not_subsingleton_iff_nontrivial.mpr ‹Nontrivial (↥P ⧸ Z)›)
      (QuotientGroup.subsingleton_iff.mpr h)
  obtain ⟨x₀, hx₀Z⟩ : ∃ y : ↥P, y ∉ Z := by
    by_contra h
    push Not at h
    exact hZtop (eq_top_iff.mpr (fun y _ => h y))
  let c₀ : ↥P := σ x₀ * x₀
  have hc₀Z : c₀ ∈ Z := hσy_mem x₀
  have hc₀p : c₀ ^ p = 1 := by
    have := Monoid.pow_exponent_eq_one c₀
    rwa [hexp] at this
  let m : ℕ := (p - 1) / 2
  let t : ↥P := c₀ ^ m
  have htZ : t ∈ Z := Z.pow_mem hc₀Z m
  have h2m : 2 * m = p - 1 := by
    rcases (Fact.out : Nat.Prime p).eq_two_or_odd' with h2 | hodd
    · exact absurd h2 hp
    · obtain ⟨k, hk⟩ := hodd
      dsimp only [m]
      rw [hk]
      have hk1 : 2 * k + 1 - 1 = 2 * k := by omega
      rw [hk1, Nat.mul_div_right k (by norm_num)]
  have ht_sq : t * t = c₀⁻¹ := by
    change c₀ ^ m * c₀ ^ m = c₀⁻¹
    calc c₀ ^ m * c₀ ^ m = c₀ ^ (m + m) := by rw [← pow_add]
      _ = c₀ ^ (2 * m) := by rw [two_mul]
      _ = c₀ ^ (p - 1) := by rw [h2m]
      _ = c₀⁻¹ := by
          have hp1 : 1 ≤ p := (Fact.out : Nat.Prime p).one_le
          calc c₀ ^ (p - 1) = c₀ ^ (p - 1) * c₀ * c₀⁻¹ := by group
            _ = c₀ ^ p * c₀⁻¹ := by rw [← pow_succ, Nat.sub_add_cancel hp1]
            _ = c₀⁻¹ := by rw [hc₀p, one_mul]
  have hct : c₀ * t = t⁻¹ := by
    have h1 : c₀ * (t * t) = 1 := by rw [ht_sq, mul_inv_cancel]
    calc c₀ * t = c₀ * (t * t) * t⁻¹ := by group
      _ = 1 * t⁻¹ := by rw [h1]
      _ = t⁻¹ := one_mul _
  let xH : ↥P := x₀ * t
  have hσt : σ t = t := hσz t htZ
  have hσx₀ : σ x₀ = c₀ * x₀⁻¹ := by
    change σ x₀ = (σ x₀ * x₀) * x₀⁻¹
    group
  have hσxH : σ xH = xH⁻¹ := by
    change σ (x₀ * t) = (x₀ * t)⁻¹
    rw [hσ_mul, hσt, hσx₀, mul_inv_rev]
    rw [show c₀ * x₀⁻¹ * t = c₀ * t * x₀⁻¹ by
      calc c₀ * x₀⁻¹ * t = c₀ * (x₀⁻¹ * t) := by group
        _ = c₀ * (t * x₀⁻¹) := by rw [Subgroup.mem_center_iff.1 htZ x₀⁻¹]
        _ = c₀ * t * x₀⁻¹ := by group]
    rw [hct]
  have hxHp : xH ^ p = 1 := by
    have := Monoid.pow_exponent_eq_one xH
    rwa [hexp] at this
  have hxHZ : xH ∉ Z := by
    intro hxZ
    have h1 : xH⁻¹ = xH := by rw [← hσxH, hσz xH hxZ]
    have h2 : xH ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 2 [← h1]
      rw [mul_inv_cancel]
    have hxH1 : xH = 1 := by
      have hdvd : orderOf xH ∣ 1 := by
        rw [← hcop]
        exact Nat.dvd_gcd (orderOf_dvd_iff_pow_eq_one.mpr h2)
          (orderOf_dvd_iff_pow_eq_one.mpr hxHp)
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)
    apply hx₀Z
    have hx₀ : x₀ = t⁻¹ := eq_inv_of_mul_eq_one_left hxH1
    rw [hx₀]
    exact Z.inv_mem htZ
  obtain ⟨gH, hgH⟩ : ∃ g : ↥P, g * xH ≠ xH * g := by
    by_contra h
    push Not at h
    exact hxHZ (Subgroup.mem_center_iff.mpr (fun g => h g))
  let zH : ↥P := ⁅gH, xH⁆
  have hzHne : zH ≠ 1 := fun h => hgH (commutatorElement_eq_one_iff_mul_comm.mp h)
  have hzHZ : zH ∈ Z := by
    change zH ∈ Z
    rw [← hcommZ]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top gH) (Subgroup.mem_top xH)
  have hzHp : zH ^ p = 1 := by
    have := Monoid.pow_exponent_eq_one zH
    rwa [hexp] at this
  haveI : Finite Z :=
    Nat.finite_of_card_ne_zero (by rw [hZcard]; exact (Fact.out : Nat.Prime p).ne_zero)
  have hzpZ : Subgroup.zpowers zH = Z := by
    have hle : Subgroup.zpowers zH ≤ Z := Subgroup.zpowers_le.mpr hzHZ
    have hdiv : orderOf zH ∣ p := by
      rw [← hZcard, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le hle
    have hone : orderOf zH = p := by
      rcases (Fact.out : Nat.Prime p).eq_one_or_self_of_dvd _ hdiv with h1 | hp'
      · exact absurd h1 (fun h => hzHne (orderOf_eq_one_iff.mp h))
      · exact hp'
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hZcard, Nat.card_zpowers, hone])
  refine ⟨(xH : G), (zH : G), (gH : G), ?_⟩
  refine
    { x_mem := xH.2
      z_mem := zH.2
      g_mem := gH.2
      x_pow := by simpa using congrArg Subtype.val hxHp
      g_pow := by
        have := Monoid.pow_exponent_eq_one gH
        rw [hexp] at this
        simpa using congrArg Subtype.val this
      z_pow := by simpa using congrArg Subtype.val hzHp
      z_ne_one := fun h => hzHne (Subtype.ext h)
      z_central := fun y hy => by
        simpa using congrArg Subtype.val ((Subgroup.mem_center_iff.mp hzHZ) ⟨y, hy⟩)
      g_conj_x := by
        have h1 : gH * xH * gH⁻¹ = zH * xH := by
          change gH * xH * gH⁻¹ = ⁅gH, xH⁆ * xH
          rw [commutatorElement_def]
          group
        have h2 : zH * xH = xH * zH := ((Subgroup.mem_center_iff.mp hzHZ) xH).symm
        simpa using congrArg Subtype.val (h1.trans h2)
      v_conj_x := by
        rw [← hσ xH]
        exact congrArg Subtype.val hσxH
      v_comm_z := by
        have hcoe : v * (zH : G) * v⁻¹ = (zH : G) := by
          simpa only [hσ] using congrArg Subtype.val (hσz zH hzHZ)
        calc v * (zH : G) = v * (zH : G) * v⁻¹ * v := by group
          _ = (zH : G) * v := by rw [hcoe]
      le_closure := by
        let T : Subgroup G := Subgroup.closure ({(xH : G), (gH : G), (zH : G)} : Set G)
        have hxT : (xH : G) ∈ T := Subgroup.subset_closure (by simp)
        have hgT : (gH : G) ∈ T := Subgroup.subset_closure (by simp)
        have hzT : (zH : G) ∈ T := Subgroup.subset_closure (by simp)
        have hTP : T ≤ P := (Subgroup.closure_le P).mpr (fun u hu => by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
          rcases hu with rfl | rfl | rfl
          · exact xH.2
          · exact gH.2
          · exact zH.2)
        have hZT : Z.map P.subtype ≤ T := by
          have heq : Z.map P.subtype = Subgroup.zpowers (zH : G) := by
            rw [← hzpZ]
            exact MonoidHom.map_zpowers P.subtype zH
          rw [heq, Subgroup.zpowers_le]
          exact hzT
        let TH : Subgroup ↥P := T.subgroupOf P
        have hZTH : Z ≤ TH := fun c hc => hZT (Subgroup.mem_map.mpr ⟨c, hc, rfl⟩)
        have hxTH : xH ∈ TH := hxT
        have hgTH : gH ∈ TH := hgT
        haveI : Finite (↥P ⧸ Z) := inferInstance
        let A : Subgroup (↥P ⧸ Z) := Subgroup.zpowers (QuotientGroup.mk' Z xH)
        let B : Subgroup (↥P ⧸ Z) := Subgroup.zpowers (QuotientGroup.mk' Z gH)
        have hA : Nat.card A = p := by
          have hπxp : (QuotientGroup.mk' Z xH) ^ p = 1 := by
            rw [← map_pow, hxHp, map_one]
          have hπxne : QuotientGroup.mk' Z xH ≠ 1 := fun h =>
            hxHZ ((QuotientGroup.eq_one_iff xH).mp h)
          have hdvd : orderOf (QuotientGroup.mk' Z xH) ∣ p :=
            orderOf_dvd_iff_pow_eq_one.mpr hπxp
          have hone : orderOf (QuotientGroup.mk' Z xH) = p := by
            rcases (Fact.out : Nat.Prime p).eq_one_or_self_of_dvd _ hdvd with h1 | hp'
            · exact absurd h1 (fun h => hπxne (orderOf_eq_one_iff.mp h))
            · exact hp'
          rw [show A = Subgroup.zpowers (QuotientGroup.mk' Z xH) from rfl, Nat.card_zpowers, hone]
        have hπgnot : QuotientGroup.mk' Z gH ∉ A := by
          intro hmem
          rw [show A = Subgroup.zpowers (QuotientGroup.mk' Z xH) from rfl,
            Subgroup.mem_zpowers_iff] at hmem
          obtain ⟨k, hk⟩ := hmem
          have h1 : QuotientGroup.mk' Z (gH * (xH ^ k)⁻¹) = 1 := by
            rw [map_mul, map_inv, map_zpow, hk, mul_inv_cancel]
          have h2 : gH * (xH ^ k)⁻¹ ∈ Z := (QuotientGroup.eq_one_iff _).mp h1
          apply hgH
          have hg : gH = (gH * (xH ^ k)⁻¹) * xH ^ k := by group
          have hpow : xH ^ k * xH = xH * xH ^ k := by
            simpa only [zpow_one] using zpow_mul_comm xH k 1
          calc gH * xH = ((gH * (xH ^ k)⁻¹) * xH ^ k) * xH := by conv_lhs => rw [hg]
            _ = (gH * (xH ^ k)⁻¹) * (xH ^ k * xH) := by group
            _ = (gH * (xH ^ k)⁻¹) * (xH * xH ^ k) := by rw [hpow]
            _ = (xH * (gH * (xH ^ k)⁻¹)) * xH ^ k := by
                rw [Subgroup.mem_center_iff.1 h2 xH]; group
            _ = xH * gH := by
                rw [mul_assoc]
                exact congrArg (fun t => xH * t) hg.symm
        have hW : A ⊔ B = ⊤ := by
          have hQcard : Nat.card (↥P ⧸ Z) = p ^ 2 := by
            have h1 : Nat.card Z * Z.index = Nat.card ↥P := Subgroup.card_mul_index (H := Z)
            rw [hZcard, Subgroup.index_eq_card, hcard] at h1
            have h2 : p ^ 3 = p * p ^ 2 := by ring
            rw [h2] at h1
            exact Nat.mul_left_cancel (Fact.out : Nat.Prime p).pos h1
          have hpdvd : p ∣ Nat.card ↥(A ⊔ B) := by
            rw [← hA]
            exact Subgroup.card_dvd_of_le le_sup_left
          have hWQ : Nat.card ↥(A ⊔ B) ∣ p ^ 2 := by
            rw [← hQcard]
            simpa only [Subgroup.card_top] using
              Subgroup.card_dvd_of_le (le_top : A ⊔ B ≤ ⊤)
          have hWne : Nat.card ↥(A ⊔ B) ≠ p := by
            intro hcardW
            have hAeq : A ⊔ B = A :=
              (Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hcardW, hA])).symm
            exact hπgnot (hAeq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
          have hWeq : Nat.card ↥(A ⊔ B) = p ^ 2 := by
            obtain ⟨k, hk_le, hk⟩ := (Nat.dvd_prime_pow (Fact.out : Nat.Prime p)).mp hWQ
            have hkpos : 0 < k := by
              rcases Nat.eq_zero_or_pos k with h0 | hpos
              · rw [h0, pow_zero] at hk
                have : p ∣ 1 := hk ▸ hpdvd
                exact absurd (Nat.dvd_one.mp this) (Fact.out : Nat.Prime p).ne_one
              · exact hpos
            have hk12 : k = 1 ∨ k = 2 := by omega
            rcases hk12 with rfl | rfl
            · exact absurd (by simpa using hk) hWne
            · exact hk
          exact Subgroup.eq_top_of_card_eq (H := A ⊔ B) (by rw [hWeq, hQcard])
        have hπ : TH.map (QuotientGroup.mk' Z) = ⊤ := by
          apply top_le_iff.mp
          rw [← hW]
          apply sup_le
          · rw [show A = Subgroup.zpowers (QuotientGroup.mk' Z xH) from rfl, Subgroup.zpowers_le]
            exact Subgroup.mem_map.mpr ⟨xH, hxTH, rfl⟩
          · rw [show B = Subgroup.zpowers (QuotientGroup.mk' Z gH) from rfl, Subgroup.zpowers_le]
            exact Subgroup.mem_map.mpr ⟨gH, hgTH, rfl⟩
        have hTHtop : TH = ⊤ := by
          apply top_le_iff.mp
          intro y _
          have hmem : (QuotientGroup.mk' Z y) ∈ TH.map (QuotientGroup.mk' Z) := by
            rw [hπ]; trivial
          rcases Subgroup.mem_map.mp hmem with ⟨c, hc, hcy⟩
          have h1 : c⁻¹ * y ∈ Z := by
            rw [← QuotientGroup.eq_one_iff]
            change (QuotientGroup.mk' Z) (c⁻¹ * y) = 1
            rw [map_mul, map_inv, hcy, inv_mul_cancel]
          have h2 : c⁻¹ * y ∈ TH := hZTH h1
          have hy : y = c * (c⁻¹ * y) := by group
          rw [hy]
          exact TH.mul_mem hc h2
        have htop : T = P := by
          have hsub : (⊤ : Subgroup ↥P).map P.subtype = P := by
            rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
          have hTH' : T.subgroupOf P = (⊤ : Subgroup ↥P) := hTHtop
          rw [← Subgroup.map_subgroupOf_eq_of_le hTP, hTH', hsub]
        show P ≤ T
        rw [← htop]
      centralizer_le := fun y hy hyv => by
        have hmem : y ∈ P ⊓ Subgroup.centralizer ({v} : Set G) :=
          ⟨hy, Subgroup.mem_centralizer_iff.mpr (fun h hh => by
            rw [Set.mem_singleton_iff] at hh
            rw [hh]
            exact hyv)⟩
        rw [inf_centralizer_eq_center hp hcard hexp hv hvP hPv] at hmem
        rcases Subgroup.mem_map.mp hmem with ⟨c, hc, rfl⟩
        have hc' : c ∈ Subgroup.zpowers zH := by rw [hzpZ]; exact hc
        have hmap : (c : G) ∈ (Subgroup.zpowers zH).map P.subtype :=
          Subgroup.mem_map.mpr ⟨c, hc', rfl⟩
        rwa [MonoidHom.map_zpowers] at hmap
      v_conj_mem := fun y hy => by
        let yH : ↥P := ⟨y, hy⟩
        have hcZ : σ yH * yH ∈ Z := hσy_mem yH
        have hczp : σ yH * yH ∈ Subgroup.zpowers zH := by rw [hzpZ]; exact hcZ
        refine ⟨((σ yH * yH : ↥P) : G), ?_, ?_⟩
        · have hmap : ((σ yH * yH : ↥P) : G) ∈ (Subgroup.zpowers zH).map P.subtype :=
            Subgroup.mem_map.mpr ⟨σ yH * yH, hczp, rfl⟩
          rwa [MonoidHom.map_zpowers] at hmap
        · have h1 : σ yH = yH⁻¹ * (σ yH * yH) := by
            conv_lhs => rw [show σ yH = (σ yH * yH) * yH⁻¹ by group]
            rw [← Subgroup.mem_center_iff.1 hcZ yH⁻¹]
          calc v * y * v⁻¹ = (σ yH : G) := by
                show v * (yH : G) * v⁻¹ = (σ yH : G)
                rw [hσ yH]
            _ = ((yH⁻¹ * (σ yH * yH) : ↥P) : G) := by conv_lhs => rw [h1]
            _ = (yH : G)⁻¹ * ((σ yH * yH : ↥P) : G) := by
                simp only [Subgroup.coe_mul, Subgroup.coe_inv] }

end CFSG.LocalAnalysis.WeakClosure81
