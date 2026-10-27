module

public import CFSG.Quasithin.Recognition.RuTypeJ36c
public import CFSG.Quasithin.Recognition.RuTypeJ31c

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem comm_of_prime_normalizes [Finite G] {P : Subgroup G} (hP : Nat.card P = 125) {ℓ : ℕ}
    [hℓ : Fact ℓ.Prime] (h1 : 125 % ℓ ≠ 1 % ℓ) (h5 : 125 % ℓ ≠ 5 % ℓ) (h25 : 125 % ℓ ≠ 25 % ℓ)
    {y : G} (hy : y ^ ℓ = 1) (hyN : y ∈ Subgroup.normalizer (P : Set G)) :
    ∀ x ∈ P, y * x = x * y := by
  classical
  set α := autNHom P ⟨y, hyN⟩ with hα
  have hαℓ : α ^ ℓ = 1 := by
    rw [hα, ← map_pow]
    have : (⟨y, hyN⟩ : Subgroup.normalizer (P : Set G)) ^ ℓ = 1 := Subtype.ext (by simpa using hy)
    rw [this, map_one]
  set K : Subgroup (MulAut P) := Subgroup.zpowers α
  have hK : IsPGroup ℓ K := by
    rw [IsPGroup.iff_card, Nat.card_zpowers]
    rcases (Nat.dvd_prime hℓ.out).mp (orderOf_dvd_of_pow_eq_one hαℓ) with h | h
    · exact ⟨0, by rw [h, pow_zero]⟩
    · exact ⟨1, by rw [h, pow_one]⟩
  let F : Subgroup P :=
    { carrier := {x | α x = x}
      mul_mem' := fun {a b} ha hb => by
        show α (a * b) = a * b
        rw [map_mul, ha, hb]
      one_mem' := by show α 1 = 1; rw [map_one]
      inv_mem' := fun {a} ha => by
        show α a⁻¹ = a⁻¹
        rw [map_inv, ha] }
  have hfix : MulAction.fixedPoints K P = (F : Set P) := by
    ext x
    constructor
    · intro hx
      exact hx ⟨α, Subgroup.mem_zpowers α⟩
    · intro hx k
      have hst : α ∈ MulAction.stabilizer (MulAut P) x := hx
      have hk : (k : MulAut P) ∈ MulAction.stabilizer (MulAut P) x :=
        (Subgroup.zpowers_le.mpr hst) k.2
      exact hk
  have hmod0 := hK.card_modEq_card_fixedPoints P
  rw [hfix] at hmod0
  have hmod : Nat.card P ≡ Nat.card F [MOD ℓ] := hmod0
  have hFc : Nat.card F ∣ 125 := hP ▸ Subgroup.card_subgroup_dvd_card F
  rw [hP] at hmod
  obtain ⟨j, hj, hjF⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).mp
    (show Nat.card F ∣ 5 ^ 3 from hFc)
  have hF : Nat.card F = 125 := by
    interval_cases j
    · rw [hjF] at hmod; exact absurd hmod h1
    · rw [hjF] at hmod; exact absurd hmod h5
    · rw [hjF] at hmod; exact absurd hmod h25
    · rw [hjF]; norm_num
  have htop : F = ⊤ := Subgroup.eq_top_of_card_eq F (by rw [hF, hP])
  intro x hx
  have hxF : (⟨x, hx⟩ : P) ∈ F := by rw [htop]; exact Subgroup.mem_top _
  have h := congrArg Subtype.val (show α ⟨x, hx⟩ = ⟨x, hx⟩ from hxF)
  rw [hα, autNHom_apply] at h
  calc y * x = (y * x * y⁻¹) * y := by group
    _ = x * y := by rw [h]

noncomputable abbrev MP5 (b : G) : Subgroup G := Subgroup.normalizer (P5 b : Set G)

noncomputable abbrev NB5 (b : G) : Subgroup G :=
  Subgroup.normalizer (Subgroup.zpowers b : Set G)

noncomputable abbrev rP5 (b : G) : ℕ := ((NB5 b).subgroupOf (MP5 b)).index

namespace RuDataM

variable (M : RuDataM G) [Finite G]

section Five

variable {M} {b : G} (hbH : b ∈ ruH M.T) (hb5 : orderOf b = 5)
include hbH hb5

theorem exists_sylow_P5
    : ∃ S : Sylow 5 G, (S : Subgroup G) = P5 b := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hf : (Nat.card G).factorization 5 = 3 := by
    rw [M.card_eq, show 2 ^ 14 * 3 ^ 3 * 5 ^ 3 * 7 * 13 * 29 = 5 ^ 3 * 43237376 * 27 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.Prime.factorization_pow (by norm_num)]
    simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 5 ∣ 43237376 by norm_num),
      Nat.factorization_eq_zero_of_not_dvd (show ¬ 5 ∣ 27 by norm_num)]
  exact ⟨Sylow.ofCard (P5 b) (by rw [card_P5_eq_125 hbH hb5, hf]; norm_num), rfl⟩

theorem pow_four_T5 {t : G} (ht : t ∈ M.T5 b) : t ^ 4 = 1 := by
  obtain ⟨e⟩ := T5_quaternion hbH hb5
  have hq : ∀ q : QuaternionGroup 2, q ^ 4 = 1 := by decide
  have h := hq (e ⟨t, ht⟩)
  rw [← map_pow] at h
  have := e.injective (h.trans (map_one e).symm)
  simpa using congrArg Subtype.val this

theorem z_mem_zpowers_T5
    {t : G} (ht : t ∈ M.T5 b) (ht1 : t ≠ 1) : M.z ∈ Subgroup.zpowers t := by
  by_cases h2 : t ^ 2 = 1
  · rw [eq_z_of_T5 hbH hb5 ht h2 ht1]
    exact Subgroup.mem_zpowers _
  · have h22 : (t ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact pow_four_T5 hbH hb5 ht
    rw [← eq_z_of_T5 hbH hb5 (pow_mem ht 2) h22 h2]
    exact Subgroup.npow_mem_zpowers _ _

theorem exists_P5_not_comm_z
    : ∃ x ∈ P5 b, x * M.z ≠ M.z * x := by
  by_contra h
  push Not at h
  have hle : P5 b ≤ Subgroup.zpowers b := fun x hx => mem_zpowers_of_P5_comm_z hbH hb5 hx (h x hx)
  have := Subgroup.card_le_of_le hle
  rw [card_P5_eq_125 hbH hb5, Nat.card_zpowers, hb5] at this
  norm_num at this

theorem mem_P5_of_centralizes
    (hab : ∀ x ∈ P5 b, ∀ y ∈ P5 b, x * y = y * x) {g : G}
    (hg : ∀ y ∈ P5 b, g * y = y * g) : g ∈ P5 b := by
  obtain ⟨xz, hxz, hxzc⟩ := exists_P5_not_comm_z hbH hb5
  have hgG : g ∈ G5 b := mem_G5.mpr (hg b (b_mem_P5 hb5))
  obtain ⟨p, hp, t, ht, rfl⟩ := G5_eq_mul hbH hb5 hgG
  by_cases ht1 : t = 1
  · rw [ht1, mul_one]; exact hp
  · exfalso
    have htc : ∀ y ∈ P5 b, t * y = y * t := by
      intro y hy
      have h1 := hg y hy
      have h2 : p * y = y * p := hab p hp y hy
      calc t * y = p⁻¹ * (p * t * y) := by group
        _ = p⁻¹ * (y * (p * t)) := by rw [h1]
        _ = p⁻¹ * (y * p) * t := by group
        _ = p⁻¹ * (p * y) * t := by rw [h2]
        _ = y * t := by group
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (z_mem_zpowers_T5 hbH hb5 ht ht1)
    apply hxzc
    rw [← hk]
    exact ((Commute.zpow_left (show Commute t xz from htc xz hxz) k)).eq.symm

theorem card_normalizer_P5_eq
    : Nat.card (MP5 b) = 4000 * rP5 b := by
  have h := ((NB5 b).subgroupOf (MP5 b)).card_mul_index
  rw [card_subgroupOf_of_le normalizer_B5_le_normalizer_P5, card_normalizer_B5 hbH hb5] at h
  exact h.symm

theorem not_two_dvd_index_normalizer
    : ¬ 2 ∣ rP5 b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRX : RB5 hbH hb5 ≤ MP5 b :=
    (RB5_le_normalizer hbH hb5).trans normalizer_B5_le_normalizer_P5
  let S2 : Sylow 2 (MP5 b) :=
    { toSubgroup := (RB5 hbH hb5).subgroupOf (MP5 b)
      isPGroup' := (RB5_isPGroup hbH hb5).comap_of_injective (MP5 b).subtype
        Subtype.val_injective
      is_maximal' := fun {Q} hQ hle => by
        have hQ' : IsPGroup 2 (Q.map (MP5 b).subtype) := hQ.map _
        have hRQ : RB5 hbH hb5 ≤ Q.map (MP5 b).subtype := fun x hx =>
          ⟨⟨x, hRX hx⟩, hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
        have heq := eq_RB5_of_le_normalizer_P5 hbH hb5 hQ' hRQ (Subgroup.map_subtype_le Q)
        ext x
        rw [Subgroup.mem_subgroupOf, ← heq]
        exact ⟨fun h => ⟨x, h, rfl⟩, fun ⟨y, hy, hyx⟩ => by
          rw [← Subtype.ext hyx]; exact hy⟩ }
  have hS2 : ¬ 2 ∣ (S2 : Subgroup (MP5 b)).index := S2.not_dvd_index
  have hS2c : Nat.card (S2 : Subgroup (MP5 b)) = 32 := by
    rw [show (S2 : Subgroup (MP5 b)) = (RB5 hbH hb5).subgroupOf (MP5 b) from rfl,
      card_subgroupOf_of_le hRX, card_RB5 hbH hb5]
  have h := (S2 : Subgroup (MP5 b)).card_mul_index
  rw [hS2c, card_normalizer_P5_eq hbH hb5] at h
  have hS2i : (S2 : Subgroup (MP5 b)).index = 125 * rP5 b := by omega
  exact fun h2 => hS2 (hS2i ▸ Dvd.dvd.mul_left h2 125)

theorem not_dvd_card_normalizer_P5
    (hab : ∀ x ∈ P5 b, ∀ y ∈ P5 b, x * y = y * x) {ℓ : ℕ}
    (hℓ : ℓ = 7 ∨ ℓ = 13 ∨ ℓ = 29) : ¬ ℓ ∣ Nat.card (MP5 b) := by
  intro hdvd
  have hℓp : ℓ.Prime := by rcases hℓ with rfl | rfl | rfl <;> norm_num
  have : Fact ℓ.Prime := ⟨hℓp⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := MP5 b) ℓ hdvd
  have hyℓ : (y : G) ^ ℓ = 1 := by
    rw [← Subgroup.orderOf_coe] at hy
    rw [← hy, pow_orderOf_eq_one]
  have hcomm := comm_of_prime_normalizes (card_P5_eq_125 hbH hb5)
    (by rcases hℓ with rfl | rfl | rfl <;> norm_num)
    (by rcases hℓ with rfl | rfl | rfl <;> norm_num)
    (by rcases hℓ with rfl | rfl | rfl <;> norm_num) hyℓ y.2
  have hyP := mem_P5_of_centralizes hbH hb5 hab hcomm
  have h125 : orderOf (y : G) ∣ 125 := card_P5_eq_125 hbH hb5 ▸
    Subgroup.orderOf_dvd_natCard _ hyP
  rw [Subgroup.orderOf_coe, hy] at h125
  rcases hℓ with rfl | rfl | rfl <;> norm_num at h125

omit [Finite G] hbH hb5 in
theorem arith_J36 {r m : ℕ} (hr : r ∣ 27) (hG : 4000 * r * m = 145926144000)
    (hm : m % 5 = 1) : r = 1 := by
  obtain ⟨k, hk, rfl⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp
    (show r ∣ 3 ^ 3 from hr)
  interval_cases k
  · rfl
  · exfalso; norm_num at hG; omega
  · exfalso; norm_num at hG; omega
  · exfalso; norm_num at hG; omega

theorem normalizer_P5_le_of_comm
    (hab : ∀ x ∈ P5 b, ∀ y ∈ P5 b, x * y = y * x) :
    MP5 b ≤ NB5 b := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hXcard : Nat.card (MP5 b) = 4000 * rP5 b := card_normalizer_P5_eq hbH hb5
  have hr2 : ¬ 2 ∣ rP5 b := not_two_dvd_index_normalizer hbH hb5
  have h7 := not_dvd_card_normalizer_P5 hbH hb5 hab (Or.inl rfl)
  have h13 := not_dvd_card_normalizer_P5 hbH hb5 hab (Or.inr (Or.inl rfl))
  have h29 := not_dvd_card_normalizer_P5 hbH hb5 hab (Or.inr (Or.inr rfl))
  rw [hXcard] at h7 h13 h29
  have hXG : Nat.card (MP5 b) ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _
  rw [hXcard, M.card_eq] at hXG
  have hr0 : rP5 b ∣ 36481536 := by
    have : 4000 * rP5 b ∣ 4000 * 36481536 := by
      rw [show 4000 * 36481536 = 2 ^ 14 * 3 ^ 3 * 5 ^ 3 * 7 * 13 * 29 by norm_num]
      exact hXG
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  have hr27 : rP5 b ∣ 27 := by
    have hcop : Nat.Coprime (rP5 b) 1351168 := by
      rw [show (1351168 : ℕ) = 2 ^ 9 * 7 * 13 * 29 by norm_num]
      refine Nat.Coprime.mul_right (Nat.Coprime.mul_right (Nat.Coprime.mul_right ?_ ?_) ?_) ?_
      · exact Nat.Coprime.pow_right _ ((Nat.coprime_comm.mp
          ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hr2)))
      · exact Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr
          (fun h => h7 (Dvd.dvd.mul_left h _)))
      · exact Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr
          (fun h => h13 (Dvd.dvd.mul_left h _)))
      · exact Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr
          (fun h => h29 (Dvd.dvd.mul_left h _)))
    exact hcop.dvd_of_dvd_mul_right (by rw [show 27 * 1351168 = 36481536 by norm_num]; exact hr0)
  obtain ⟨S5, hS5⟩ := exists_sylow_P5 hbH hb5
  have hmod := card_sylow_modEq_one 5 G
  rw [Sylow.card_eq_index_normalizer S5] at hmod
  have hS5X : Subgroup.normalizer (S5 : Set G) = MP5 b := by
    rw [show (S5 : Set G) = (P5 b : Set G) by rw [← hS5]; rfl]
  rw [hS5X, Nat.ModEq] at hmod
  have hGX := (MP5 b).card_mul_index
  rw [hXcard, M.card_eq] at hGX
  have hr1 : rP5 b = 1 := arith_J36 hr27 (by rw [hGX]; norm_num) (by rw [hmod])
  have h := ((NB5 b).subgroupOf (MP5 b)).index_eq_one.mp hr1
  intro x hx
  have : (⟨x, hx⟩ : MP5 b) ∈ (NB5 b).subgroupOf (MP5 b) := by rw [h]; exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp this

theorem not_comm_P5
    : ¬ ∀ x ∈ P5 b, ∀ y ∈ P5 b, x * y = y * x := by
  intro hab
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hXNB := normalizer_P5_le_of_comm hbH hb5 hab
  obtain ⟨hiH, hi2, hiz, hib, t, ht, hti⟩ := iel_spec hbH hb5
  set i := iel hbH hb5
  have hCi : Nat.card (P5 b ⊓ Subgroup.centralizer ({i} : Set G) : Subgroup G) = 5 := by
    have h := card_P5_eq hbH hb5 hiH hi2 hib ht hti
    rw [card_P5_eq_125 hbH hb5] at h
    have h' : Nat.card (P5 b ⊓ Subgroup.centralizer ({i} : Set G) : Subgroup G) ^ 2 = 5 ^ 2 := by
      omega
    exact Nat.pow_left_injective (by norm_num) h'
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card'
    (G := (P5 b ⊓ Subgroup.centralizer ({i} : Set G) : Subgroup G)) 5 (by rw [hCi])
  have hcP : (c : G) ∈ P5 b := (Subgroup.mem_inf.mp c.2).1
  have hci : (c : G) * i = i * c :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp c.2).2
  have hco : orderOf (c : G) = 5 := by rw [Subgroup.orderOf_coe]; exact hc
  obtain ⟨g, hg⟩ := isConj_iff.mp hiz
  have hcH : g⁻¹ * c * g ∈ ruH M.T := by
    rw [M.mem_H_iff_comm]
    have hgz : M.z = g⁻¹ * i * g := by rw [← hg]; group
    rw [hgz]
    calc g⁻¹ * i * g * (g⁻¹ * c * g) = g⁻¹ * (i * c) * g := by group
      _ = g⁻¹ * (c * i) * g := by rw [hci]
      _ = g⁻¹ * c * g * (g⁻¹ * i * g) := by group
  have hco' : orderOf (g⁻¹ * c * g) = 5 := by
    rw [show g⁻¹ * c * g = g⁻¹ * c * g⁻¹⁻¹ by rw [inv_inv], orderOf_conj_eq, hco]
  obtain ⟨h, hh, hmem⟩ := M.exists_conj_five hcH hbH hco' hb5
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
  set u := h * g⁻¹
  have hu : (c : G) = u⁻¹ * b ^ j * u := by
    rw [hj]
    simp only [u]
    group
  obtain ⟨S5, hS5⟩ := exists_sylow_P5 hbH hb5
  have hS5X : Subgroup.normalizer (S5 : Set G) = Subgroup.normalizer (P5 b : Set G) := by
    rw [show (S5 : Set G) = (P5 b : Set G) by rw [← hS5]; rfl]
  have : IsMulCommutative (S5 : Subgroup G) :=
    ⟨⟨fun x y => Subtype.ext (by
      have hx : (x : G) ∈ P5 b := hS5 ▸ x.2
      have hy : (y : G) ∈ P5 b := hS5 ▸ y.2
      exact hab _ hx _ hy)⟩⟩
  have hbS : b ^ j ∈ (S5 : Subgroup G) := hS5 ▸ zpowers_le_P5 hb5 (Subgroup.zpow_mem_zpowers b j)
  have hcS : u⁻¹ * b ^ j * u ∈ (S5 : Subgroup G) := hS5 ▸ (hu ▸ hcP)
  obtain ⟨n, hn, hne⟩ := S5.conj_eq_normalizer_conj_of_mem (b ^ j) u hbS hcS
  have hnX : n ∈ MP5 b := by
    show n ∈ Subgroup.normalizer (P5 b : Set G)
    rw [← hS5X]
    exact hn
  have hnNB : n ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G) := hXNB hnX
  have hcB : (c : G) ∈ Subgroup.zpowers b := by
    rw [hu, hne]
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hnNB) (b ^ j)).mp
      (Subgroup.zpow_mem_zpowers b j)
    simpa using this
  have := eq_one_of_zpowers_comm_inv hb5 hib hcB hci.symm
  rw [this, orderOf_one] at hco
  norm_num at hco

end Five

end RuDataM

end CFSG.Quasithin.RuType
