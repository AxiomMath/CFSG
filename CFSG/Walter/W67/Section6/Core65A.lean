module

public import CFSG.Walter.W67.Section6.Core64A
public import CFSG.Walter.Bender1970.S2.Subnormal
public import CFSG.Walter.W67.Section6.Core62F

public section

namespace CFSG.Walter.W67.Sec65

open Sec6

variable {G : Type} [Group G] [Finite G]

structure Hyp65 (G : Type) [Group G] [Finite G] (e u ρ : G) : Prop where
  perfect : commutator G = ⊤
  orderOf_e : orderOf e = 7
  orderOf_u : orderOf u = 7
  orderOf_ρ : orderOf ρ = 3
  comm_eu : e * u = u * e
  comm_eρ : e * ρ = ρ * e
  ρ_mem : ρ ∈ Subgroup.normalizer ((Subgroup.zpowers u : Subgroup G) : Set G)
  ρ_not_comm : ρ * u ≠ u * ρ
  mem_P : ∀ g : G, g * e = e * g → g * u = u * g →
    g ∈ Subgroup.zpowers e ⊔ Subgroup.zpowers u
  normalizer_E : Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G) ≤
    Subgroup.centralizer ((Subgroup.zpowers e : Subgroup G) : Set G)
  card_seven : ∀ Q : Subgroup G, IsPGroup 7 Q → Q ≤ Subgroup.centralizer ({e} : Set G) →
    Nat.card Q ≤ 7 ^ 2
  card_three : ∀ Q : Subgroup G, IsPGroup 3 Q → Q ≤ Subgroup.centralizer ({e} : Set G) →
    Nat.card Q ≤ 3
  no_real : ∀ x y : G, orderOf x = 7 → y * x * y⁻¹ ≠ x⁻¹
  three_comm : ∀ T : Subgroup G, IsPGroup 3 T → ∀ a ∈ T, ∀ b ∈ T, a * b = b * a
  centralizer_three : ∀ R : G, orderOf R = 3 → ∃ h : G,
    cj h (Subgroup.zpowers e) ≤ Subgroup.centralizer ({R} : Set G) ∧
    (Nat.card (Subgroup.centralizer ({R} : Set G))).factorization 7 = 1

abbrev PP (e u : G) : Subgroup G := Subgroup.zpowers e ⊔ Subgroup.zpowers u

namespace Hyp65

variable {e u ρ : G} (h : Hyp65 G e u ρ)
include h

theorem ρ_pow_three : ρ ^ 3 = 1 := by rw [← h.orderOf_ρ, pow_orderOf_eq_one]

theorem e_pow_seven : e ^ 7 = 1 := by rw [← h.orderOf_e, pow_orderOf_eq_one]

theorem u_pow_seven : u ^ 7 = 1 := by rw [← h.orderOf_u, pow_orderOf_eq_one]

theorem card_E : Nat.card (Subgroup.zpowers e) = 7 := by rw [Nat.card_zpowers, h.orderOf_e]

theorem card_U : Nat.card (Subgroup.zpowers u) = 7 := by rw [Nat.card_zpowers, h.orderOf_u]

theorem isPGroup_E : IsPGroup 7 (Subgroup.zpowers e) :=
  IsPGroup.of_card (n := 1) (by rw [h.card_E, pow_one])

theorem isPGroup_U : IsPGroup 7 (Subgroup.zpowers u) :=
  IsPGroup.of_card (n := 1) (by rw [h.card_U, pow_one])

omit [Finite G] h in
theorem comm_of_mem_zpowers {g x y : G} (hx : x * g = g * x) (hy : y ∈ Subgroup.zpowers g) :
    x * y = y * x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact (Commute.zpow_right (show Commute x g from hx) k).eq

theorem E_le_centralizer_ρ : Subgroup.zpowers e ≤ Subgroup.centralizer ({ρ} : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (comm_of_mem_zpowers h.comm_eρ.symm hx).symm

theorem ρ_mem_normalizer_E : ρ ∈ Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G) :=
  Subgroup.centralizer_le_normalizer _ (by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (comm_of_mem_zpowers h.comm_eρ.symm hx).symm)

theorem U_inf_centralizer_ρ : Subgroup.zpowers u ⊓ Subgroup.centralizer ({ρ} : Set G) = ⊥ := by
  have hdvd : Nat.card ↥(Subgroup.zpowers u ⊓ Subgroup.centralizer ({ρ} : Set G)) ∣ 7 :=
    h.card_U ▸ Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h1 | h7
  · exact Subgroup.card_eq_one.mp h1
  · exfalso
    have heq : Subgroup.zpowers u ⊓ Subgroup.centralizer ({ρ} : Set G) = Subgroup.zpowers u :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h7, h.card_U])
    have hu : u ∈ Subgroup.zpowers u ⊓ Subgroup.centralizer ({ρ} : Set G) := by
      rw [heq]; exact Subgroup.mem_zpowers u
    exact h.ρ_not_comm (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hu).2).symm

theorem E_inf_U : Subgroup.zpowers e ⊓ Subgroup.zpowers u = ⊥ := by
  rw [eq_bot_iff, ← h.U_inf_centralizer_ρ]
  exact le_inf inf_le_right (inf_le_left.trans h.E_le_centralizer_ρ)

theorem U_le_centralizer_E : Subgroup.zpowers u ≤
    Subgroup.centralizer ((Subgroup.zpowers e : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hxe : x * e = e * x := (comm_of_mem_zpowers h.comm_eu hx).symm
  exact (comm_of_mem_zpowers hxe hy).symm

theorem P_comm : ∀ a ∈ PP e u, ∀ b ∈ PP e u, a * b = b * a := by
  have hP : ∀ g : G, g * e = e * g → g * u = u * g → PP e u ≤ Subgroup.centralizer ({g} : Set G) :=
    fun g hge hgu => sup_le
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hge.symm))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hgu.symm))
  have he : PP e u ≤ Subgroup.centralizer ({e} : Set G) := hP e rfl h.comm_eu
  have hu : PP e u ≤ Subgroup.centralizer ({u} : Set G) := hP u h.comm_eu.symm rfl
  intro a ha b hb
  have hb' := hP b (Subgroup.mem_centralizer_singleton_iff.mp (he hb))
    (Subgroup.mem_centralizer_singleton_iff.mp (hu hb))
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hb' ha))

theorem card_P : Nat.card (PP e u) = 7 ^ 2 := by
  rw [card_sup_of_inf_eq_bot (h.U_le_centralizer_E.trans (Subgroup.centralizer_le_normalizer _))
    h.E_inf_U, h.card_E, h.card_U]
  norm_num

theorem isPGroup_P : IsPGroup 7 (PP e u) := IsPGroup.of_card h.card_P

omit [Finite G] h in
theorem E_le_P : Subgroup.zpowers e ≤ PP e u := le_sup_left

omit [Finite G] h in
theorem U_le_P : Subgroup.zpowers u ≤ PP e u := le_sup_right

omit [Finite G] h in
theorem e_mem_P : e ∈ PP e u := E_le_P (Subgroup.mem_zpowers e)

omit [Finite G] h in
theorem u_mem_P : u ∈ PP e u := U_le_P (Subgroup.mem_zpowers u)

theorem exists_mul_of_mem_P {x : G} (hx : x ∈ PP e u) :
    ∃ a ∈ Subgroup.zpowers e, ∃ b ∈ Subgroup.zpowers u, a * b = x :=
  (mem_sup_iff_of_le_normalizer
    (h.U_le_centralizer_E.trans (Subgroup.centralizer_le_normalizer _))).mp hx

theorem ρ_mem_normalizer_P : ρ ∈ Subgroup.normalizer ((PP e u : Subgroup G) : Set G) :=
  mem_normalizer_sup h.ρ_mem_normalizer_E h.ρ_mem

theorem commutator_ρ_mem_U {x : G} (hx : x ∈ PP e u) :
    ρ * x * ρ⁻¹ * x⁻¹ ∈ Subgroup.zpowers u := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul_of_mem_P hx
  have hρa : ρ * a = a * ρ :=
    (Subgroup.mem_centralizer_singleton_iff.mp (h.E_le_centralizer_ρ ha)).symm
  have hb' : ρ * b * ρ⁻¹ ∈ Subgroup.zpowers u :=
    (Subgroup.mem_normalizer_iff.mp h.ρ_mem b).mp hb
  have hab : a * (ρ * b * ρ⁻¹) = (ρ * b * ρ⁻¹) * a :=
    h.P_comm a (E_le_P ha) _ (U_le_P hb')
  have e1 : ρ * (a * b) * ρ⁻¹ * (a * b)⁻¹ = (ρ * b * ρ⁻¹) * b⁻¹ := by
    calc ρ * (a * b) * ρ⁻¹ * (a * b)⁻¹ = (ρ * a) * b * ρ⁻¹ * b⁻¹ * a⁻¹ := by group
      _ = a * (ρ * b * ρ⁻¹) * b⁻¹ * a⁻¹ := by rw [hρa]; group
      _ = (ρ * b * ρ⁻¹) * a * b⁻¹ * a⁻¹ := by rw [hab]
      _ = (ρ * b * ρ⁻¹) * b⁻¹ := by
        have hba : a * b⁻¹ = b⁻¹ * a :=
          h.P_comm a (E_le_P ha) _ (U_le_P ((Subgroup.zpowers u).inv_mem hb))
        rw [mul_assoc (ρ * b * ρ⁻¹) a, hba]
        group
  rw [e1]
  exact (Subgroup.zpowers u).mul_mem hb' ((Subgroup.zpowers u).inv_mem hb)

theorem P_inf_centralizer_ρ : PP e u ⊓ Subgroup.centralizer ({ρ} : Set G) = Subgroup.zpowers e := by
  refine le_antisymm ?_ (le_inf E_le_P h.E_le_centralizer_ρ)
  intro x hx
  obtain ⟨hxP, hxρ⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul_of_mem_P hxP
  have hρa : ρ * a = a * ρ :=
    (Subgroup.mem_centralizer_singleton_iff.mp (h.E_le_centralizer_ρ ha)).symm
  have hρab : a * b * ρ = ρ * (a * b) := Subgroup.mem_centralizer_singleton_iff.mp hxρ
  have hbρ : b * ρ = ρ * b := by
    have : a * (b * ρ) = a * (ρ * b) := by
      calc a * (b * ρ) = a * b * ρ := by group
        _ = ρ * (a * b) := hρab
        _ = a * (ρ * b) := by rw [← mul_assoc, hρa, mul_assoc]
    exact mul_left_cancel this
  have hb1 : b ∈ Subgroup.zpowers u ⊓ Subgroup.centralizer ({ρ} : Set G) :=
    Subgroup.mem_inf.mpr ⟨hb, Subgroup.mem_centralizer_singleton_iff.mpr hbρ⟩
  rw [h.U_inf_centralizer_ρ, Subgroup.mem_bot] at hb1
  rw [hb1, mul_one]
  exact ha

theorem centralizer_P_le : Subgroup.centralizer ((PP e u : Subgroup G) : Set G) ≤ PP e u := by
  intro g hg
  have hge := Subgroup.mem_centralizer_iff.mp hg e e_mem_P
  have hgu := Subgroup.mem_centralizer_iff.mp hg u u_mem_P
  exact h.mem_P g hge.symm hgu.symm

theorem eq_E_or_U {Z : Subgroup G} (hZP : Z ≤ PP e u) (hZ : Nat.card Z = 7)
    (hρZ : ρ ∈ Subgroup.normalizer (Z : Set G)) :
    Z = Subgroup.zpowers e ∨ Z = Subgroup.zpowers u := by
  have hdvd : Nat.card ↥(Z ⊓ Subgroup.zpowers u) ∣ 7 := hZ ▸ Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h1 | h7
  · left
    have hbot : Z ⊓ Subgroup.zpowers u = ⊥ := Subgroup.card_eq_one.mp h1
    have hle : Z ≤ Subgroup.zpowers e := by
      rw [← h.P_inf_centralizer_ρ]
      intro z hz
      refine Subgroup.mem_inf.mpr ⟨hZP hz, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have hc : ρ * z * ρ⁻¹ * z⁻¹ ∈ Z ⊓ Subgroup.zpowers u :=
        Subgroup.mem_inf.mpr ⟨Z.mul_mem ((Subgroup.mem_normalizer_iff.mp hρZ z).mp hz)
          (Z.inv_mem hz), h.commutator_ρ_mem_U (hZP hz)⟩
      rw [hbot, Subgroup.mem_bot] at hc
      calc z * ρ = (ρ * z * ρ⁻¹ * z⁻¹)⁻¹ * (ρ * z) := by group
        _ = ρ * z := by rw [hc, inv_one, one_mul]
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [h.card_E, hZ])
  · right
    have h1 : Z ⊓ Subgroup.zpowers u = Z :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h7, hZ])
    have h2 : Z ⊓ Subgroup.zpowers u = Subgroup.zpowers u :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h7, h.card_U])
    rw [← h1, h2]

theorem card_le_seven_of_le_centralizer_ρ {Q : Subgroup G} (hQ : IsPGroup 7 Q)
    (hQρ : Q ≤ Subgroup.centralizer ({ρ} : Set G)) : Nat.card Q ≤ 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨-, -, hfac⟩ := h.centralizer_three ρ h.orderOf_ρ
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have hdvd : 7 ^ k ∣ Nat.card (Subgroup.centralizer ({ρ} : Set G)) :=
    hk ▸ Subgroup.card_dvd_of_le hQρ
  have hk1 : k ≤ 1 := by
    have := (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) Nat.card_pos.ne').mp hdvd
    rwa [hfac] at this
  rw [hk]
  calc 7 ^ k ≤ 7 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
    _ = 7 := pow_one 7

theorem card_le_three {X : Subgroup G} (hXρ : X ⊓ Subgroup.centralizer ({ρ} : Set G) =
    Subgroup.zpowers e) {T : Subgroup G} (hT3 : IsPGroup 3 T)
    (hTX : T ≤ Subgroup.normalizer (X : Set G)) (hρT : ρ ∈ T) : Nat.card T ≤ 3 := by
  refine h.card_three T hT3 fun t ht => ?_
  have htρ : t * ρ = ρ * t := h.three_comm T hT3 t ht ρ hρT
  have htC : t ∈ Subgroup.centralizer ({ρ} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr htρ
  have htN : t ∈ Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G) := by
    rw [← hXρ]
    exact mem_normalizer_inf (hTX ht) (Subgroup.le_normalizer htC)
  have := Subgroup.mem_centralizer_iff.mp (h.normalizer_E htN) e (Subgroup.mem_zpowers e)
  exact Subgroup.mem_centralizer_singleton_iff.mpr this.symm

theorem eq_one_of_mem_normalizer {X : Subgroup G} (hX : IsPGroup 7 X) (hPX : PP e u ≤ X) {t : G}
    (ht : t ∈ Subgroup.normalizer (X : Set G)) (ht2 : t * t = 1) : t = 1 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  by_cases hc : ∀ x ∈ X, t * x * t⁻¹ = x
  · have htC : t ∈ Subgroup.centralizer ((PP e u : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have := hc x (hPX hx)
      calc x * t = t * x * t⁻¹ * t := by rw [this]
        _ = t * x := by group
    have htP := h.centralizer_P_le htC
    have h49 : t ^ 49 = 1 := by
      have := Subgroup.orderOf_dvd_natCard _ htP
      rw [h.card_P] at this
      exact orderOf_dvd_iff_pow_eq_one.mp this
    have h2 : t ^ 2 = 1 := by rw [pow_two, ht2]
    have := pow_gcd_eq_one.mpr ⟨h49, h2⟩
    norm_num at this
    exact this
  · exfalso
    push Not at hc
    obtain ⟨x, hx, htx⟩ := hc
    obtain ⟨hyX, hy1, hyinv⟩ := Sec64.inv_of_not_comm ht2 ht hx htx
    set y := (t * x * t⁻¹)⁻¹ * x with hy
    have hyr : IsPGroup 7 (Subgroup.zpowers y) := hX.to_le (Subgroup.zpowers_le.mpr hyX)
    obtain ⟨z, hz, hzo⟩ := exists_orderOf_eq_of_ne_bot hyr (by
      intro hbot
      apply hy1
      have : y ∈ (⊥ : Subgroup G) := hbot ▸ Subgroup.mem_zpowers y
      exact Subgroup.mem_bot.mp this)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    apply h.no_real _ t hzo
    rw [← conj_zpow, hyinv, inv_zpow]

theorem factorization_three_le {X : Subgroup G} (hρX : ρ ∈ Subgroup.normalizer (X : Set G))
    (hXρ : X ⊓ Subgroup.centralizer ({ρ} : Set G) = Subgroup.zpowers e) :
    (Nat.card (Subgroup.normalizer (X : Set G))).factorization 3 ≤ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := Subgroup.normalizer (X : Set G) with hN
  have hR3 : IsPGroup 3 (Subgroup.zpowers ρ) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.orderOf_ρ, pow_one])
  obtain ⟨S, hS⟩ := (hR3.comap_subtype (K := N)).exists_le_sylow
  set T := (S : Subgroup N).map N.subtype with hT
  have hTN : T ≤ N := Subgroup.map_subtype_le _
  have hρT : ρ ∈ T := ⟨⟨ρ, hρX⟩, hS (Subgroup.mem_comap.mpr (Subgroup.mem_zpowers ρ)), rfl⟩
  have hT3 := h.card_le_three hXρ (S.isPGroup'.map N.subtype) hTN hρT
  rw [Subgroup.card_map_of_injective N.subtype_injective, Sylow.card_eq_multiplicity] at hT3
  by_contra hlt
  push Not at hlt
  have : 3 ^ 2 ≤ 3 ^ (Nat.card N).factorization 3 := Nat.pow_le_pow_right (by norm_num) hlt
  omega

omit h in
theorem eq_three_pow_mul_seven_pow {n : ℕ} (hn : n ≠ 0)
    (hp : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → ℓ = 3 ∨ ℓ = 7) :
    n = 3 ^ n.factorization 3 * 7 ^ n.factorization 7 := by
  have hsupp : n.factorization.support ⊆ {3, 7} := by
    intro ℓ hℓ
    rw [Nat.support_factorization] at hℓ
    rcases hp ℓ (Nat.prime_of_mem_primeFactors hℓ) (Nat.dvd_of_mem_primeFactors hℓ) with h3 | h7
    · rw [h3]; simp
    · rw [h7]; simp
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod_of_support_subset _ hsupp _ (fun _ _ => pow_zero _)]
  rw [Finset.prod_pair (by norm_num)]

theorem normalizer_eq_sup {X : Subgroup G} (hX : IsPGroup 7 X)
    (hρX : ρ ∈ Subgroup.normalizer (X : Set G))
    (hXρ : X ⊓ Subgroup.centralizer ({ρ} : Set G) = Subgroup.zpowers e)
    (hXc : Nat.card X = 7 ^ (Nat.card (Subgroup.normalizer (X : Set G))).factorization 7)
    (hp : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card (Subgroup.normalizer (X : Set G)) → ℓ = 3 ∨ ℓ = 7) :
    Subgroup.normalizer (X : Set G) = X ⊔ Subgroup.zpowers ρ := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set N := Subgroup.normalizer (X : Set G) with hN
  have hR : Subgroup.zpowers ρ ≤ N := Subgroup.zpowers_le.mpr hρX
  have hinf : X ⊓ Subgroup.zpowers ρ = ⊥ := by
    apply inf_eq_bot_of_coprime
    obtain ⟨k, hk⟩ := hX.exists_card_eq
    rw [hk, Nat.card_zpowers, h.orderOf_ρ]
    exact Nat.Coprime.pow_left _ (by norm_num)
  have hcard : Nat.card ↥(X ⊔ Subgroup.zpowers ρ) = Nat.card X * 3 := by
    rw [card_sup_of_inf_eq_bot hR hinf, Nat.card_zpowers, h.orderOf_ρ]
  have hle : X ⊔ Subgroup.zpowers ρ ≤ N := sup_le Subgroup.le_normalizer hR
  have hNc := eq_three_pow_mul_seven_pow Nat.card_pos.ne' hp
  have h3 := h.factorization_three_le hρX hXρ
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hcard, hNc, ← hXc, mul_comm]
  apply Nat.mul_le_mul_left
  calc 3 ^ (Nat.card N).factorization 3 ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) h3
    _ = 3 := pow_one 3

end Hyp65

end CFSG.Walter.W67.Sec65
