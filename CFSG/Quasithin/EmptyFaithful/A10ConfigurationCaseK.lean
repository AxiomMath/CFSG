module

public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationFusion
public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationCaseModel
public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationCounting

public section

namespace CFSG.Quasithin.A10

open CFSG.Open CFSG.Quasithin S4

variable {G : Type*} [Group G]

namespace Emb

variable {T M : Subgroup G} (E : Emb G T M)

@[expose] def K : Subgroup G := Subgroup.normalizer (E.B : Set G)

@[expose] def zK : Set G := {y | ∃ k ∈ E.K, k⁻¹ * E.z * k = y}

theorem B_le_K : E.B ≤ E.K := Subgroup.le_normalizer

theorem T_le_K : T ≤ E.K := E.T_le_normalizer_B

theorem card_B : Nat.card E.B = 16 := by
  unfold B
  rw [card_map_of_inj E.injective, card_A2]

theorem z_mem_K : E.z ∈ E.K := E.B_le_K E.z_mem_B

theorem conj_mem_B_of_mem_K {k y : G} (hk : k ∈ E.K) (hy : y ∈ E.B) : k⁻¹ * y * k ∈ E.B := by
  have := (Subgroup.mem_normalizer_iff.mp (E.K.inv_mem hk) y).mp hy
  simpa using this

theorem zK_sub_B : ∀ y ∈ E.zK, y ∈ E.B := by
  rintro y ⟨k, hk, rfl⟩
  exact E.conj_mem_B_of_mem_K hk E.z_mem_B

theorem z_mem_zK : E.z ∈ E.zK := ⟨1, E.K.one_mem, by simp⟩

theorem zK_inv {y k : G} (hy : y ∈ E.zK) (hk : k ∈ E.K) : k⁻¹ * y * k ∈ E.zK := by
  obtain ⟨k₀, hk₀, rfl⟩ := hy
  exact ⟨k₀ * k, E.K.mul_mem hk₀ hk, by group⟩

theorem zK_inv_iff {y k : G} (hk : k ∈ E.K) : y ∈ E.zK ↔ k⁻¹ * y * k ∈ E.zK := by
  refine ⟨fun h => E.zK_inv h hk, fun h => ?_⟩
  have := E.zK_inv h (E.K.inv_mem hk)
  simpa [mul_assoc] using this

theorem zK_model (hT : quasithinIsSylowTwo T) (hGz : Subgroup.centralizer ({E.z} : Set G) = T)
    {y : G} (hy : y ∈ E.zK) :
    ∃ w ∈ A2, E.ι w = y ∧ (D1 w = true ∨ D4 w = true ∨ D5 w = true) := by
  have hyB := E.zK_sub_B y hy
  obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.mp hyB
  obtain ⟨k, hk, hky⟩ := hy
  refine ⟨w, hw, hwy, ?_⟩
  have hw1 : w ≠ 1 := by
    rintro rfl
    rw [map_one] at hwy
    apply E.z_ne_one
    calc E.z = k * (k⁻¹ * E.z * k) * k⁻¹ := by group
      _ = 1 := by rw [hky, ← hwy]; group
  rcases B_cases w hw with h | h | h | h | h | h
  · exact absurd h hw1
  · exact Or.inl h
  · exact absurd ⟨k, by rw [hky, hwy]⟩ (E.not_mem_zG_of_D236 hGz hT (Or.inl h))
  · exact absurd ⟨k, by rw [hky, hwy]⟩ (E.not_mem_zG_of_D236 hGz hT (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem ι_mem_K {w : Wc} (hw : w ∈ Th) : E.ι w ∈ E.K := by
  apply E.T_le_K
  have := Subgroup.mem_map_of_mem E.ι hw
  rwa [E.map_Th] at this

theorem zK_of_T_conj {w₀ w : Wc} (h₀ : E.ι w₀ ∈ E.zK) (hx : ∃ x ∈ Th, x⁻¹ * w₀ * x = w) :
    E.ι w ∈ E.zK := by
  obtain ⟨x, hx, rfl⟩ := hx
  have := E.zK_inv h₀ (E.ι_mem_K hx)
  simpa using this

theorem exists_zK_eq [Finite G] (hT : quasithinIsSylowTwo T)
    (hM : quasithinIsMaxTwoLocal M) (hGz : Subgroup.centralizer ({E.z} : Set G) = T)
    (hnwc : ¬ ∀ g : G, g⁻¹ * E.z * g ∈ E.B → g⁻¹ * E.z * g = E.z) :
    ∃ a b : Bool, (a = true ∨ b = true) ∧
      ∀ y : G, y ∈ E.zK ↔ ∃ w ∈ Zset a b, E.ι w = y := by
  classical
  have h4 : ∀ w ∈ A2, D4 w = true → E.ι w ∈ E.zK →
      (decide (∃ w ∈ A2, D4 w = true ∧ E.ι w ∈ E.zK)) = true := fun w hw h hz =>
    decide_eq_true ⟨w, hw, h, hz⟩
  have h5 : ∀ w ∈ A2, D5 w = true → E.ι w ∈ E.zK →
      (decide (∃ w ∈ A2, D5 w = true ∧ E.ι w ∈ E.zK)) = true := fun w hw h hz =>
    decide_eq_true ⟨w, hw, h, hz⟩
  refine ⟨decide (∃ w ∈ A2, D4 w = true ∧ E.ι w ∈ E.zK),
    decide (∃ w ∈ A2, D5 w = true ∧ E.ι w ∈ E.zK), ?_, fun y => ⟨?_, ?_⟩⟩
  · push Not at hnwc
    obtain ⟨g, hgB, hgz⟩ := hnwc
    obtain ⟨k, hk, hkg⟩ := E.fusion_B hT hM E.z_mem_B hgB
    have hy : g⁻¹ * E.z * g ∈ E.zK := ⟨k, hk, hkg⟩
    obtain ⟨w, hw, hwy, hcls⟩ := E.zK_model hT hGz hy
    rcases hcls with h | h | h
    · exfalso
      have := B_D1 w hw h
      rw [this] at hwy
      exact hgz hwy.symm
    · left
      exact h4 w hw h (hwy ▸ hy)
    · right
      exact h5 w hw h (hwy ▸ hy)
  · intro hy
    obtain ⟨w, hw, hwy, hcls⟩ := E.zK_model hT hGz hy
    refine ⟨w, mem_Zset.2 ?_, hwy⟩
    rcases hcls with h | h | h
    · exact Or.inl (B_D1 w hw h)
    · exact Or.inr (Or.inl ⟨h4 w hw h (hwy ▸ hy), hw, h⟩)
    · exact Or.inr (Or.inr ⟨h5 w hw h (hwy ▸ hy), hw, h⟩)
  · rintro ⟨w, hw, rfl⟩
    rcases mem_Zset.1 hw with rfl | ⟨ha, hwA, hw4⟩ | ⟨hb, hwA, hw5⟩
    · exact E.z_mem_zK
    · obtain ⟨w₀, hw₀, h₀4, h₀z⟩ := of_decide_eq_true ha
      exact E.zK_of_T_conj h₀z (B_orbit_D4 w₀ hw₀ h₀4 w hwA hw4)
    · obtain ⟨w₀, hw₀, h₀5, h₀z⟩ := of_decide_eq_true hb
      exact E.zK_of_T_conj h₀z (B_orbit_D5 w₀ hw₀ h₀5 w hwA hw5)

theorem ncard_zK {a b : Bool} (h : ∀ y : G, y ∈ E.zK ↔ ∃ w ∈ Zset a b, E.ι w = y) :
    E.zK.ncard = (Zset a b).card := by
  have : E.zK = E.ι '' ↑(Zset a b) := by
    ext y
    rw [h y]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, rfl⟩
  rw [this, Set.ncard_image_of_injective _ E.injective, Set.ncard_coe_finset]

theorem card_K_eq [Finite G] (hGz : Subgroup.centralizer ({E.z} : Set G) = T) :
    Nat.card E.K = 128 * E.zK.ncard := by
  have h := ncard_conjClass_mul_card E.K E.z
  rw [hGz, inf_eq_right.mpr E.T_le_K, E.card_T] at h
  rw [← h, mul_comm]
  rfl

theorem card_K_ne_640 [Finite G] (hT : quasithinIsSylowTwo T)
    (hGz : Subgroup.centralizer ({E.z} : Set G) = T) : Nat.card E.K ≠ 640 := by
  intro hK
  have hBK : E.B ≤ E.K := E.B_le_K
  have : (E.B.subgroupOf E.K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBK).2 le_rfl
  have hcommT : ∀ g : E.K, (g : G) * E.z = E.z * g → (g : G) ∈ T := by
    intro g hg
    have hmem : (g : G) ∈ Subgroup.centralizer ({E.z} : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun h hh => by
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact hg.symm
    rwa [hGz] at hmem
  refine false_of_card_640 (K := E.K) hK (B := E.B.subgroupOf E.K) ?_
    (z := ⟨E.z, E.z_mem_K⟩) (Subgroup.mem_subgroupOf.2 E.z_mem_B) ?_ ?_
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBK).toEquiv]
    exact E.card_B
  · intro g hg
    have h1 : (g : G) * E.z = E.z * g := congrArg Subtype.val hg
    obtain ⟨n, hn⟩ := hT.1 ⟨g, hcommT g h1⟩
    exact ⟨n, Subtype.ext (by simpa using congrArg Subtype.val hn)⟩
  · intro g hg
    have hz : (g : G) * E.z = E.z * g :=
      congrArg Subtype.val (hg ⟨E.z, E.z_mem_K⟩ (Subgroup.mem_subgroupOf.2 E.z_mem_B))
    have hgT := hcommT g hz
    obtain ⟨x, hx, hxg⟩ := (E.mem_T_iff).1 hgT
    have hxA : x ∈ A2 := by
      refine centralizer_B_Th x hx fun y hy => ?_
      have hyB : E.ι y ∈ E.B := Subgroup.mem_map_of_mem _ hy
      have := congrArg Subtype.val
        (hg ⟨E.ι y, E.B_le_K hyB⟩ (Subgroup.mem_subgroupOf.2 hyB))
      apply E.injective
      rw [map_mul, map_mul, hxg]
      exact this
    rw [Subgroup.mem_subgroupOf]
    rw [← hxg]
    exact Subgroup.mem_map_of_mem _ hxA

theorem zK_eq_full [Finite G] (hT : quasithinIsSylowTwo T) (hM : quasithinIsMaxTwoLocal M)
    (hGz : Subgroup.centralizer ({E.z} : Set G) = T)
    (hnwc : ¬ ∀ g : G, g⁻¹ * E.z * g ∈ E.B → g⁻¹ * E.z * g = E.z) :
    ∀ y : G, y ∈ E.zK ↔ ∃ w ∈ Zset true true, E.ι w = y := by
  obtain ⟨a, b, hab, h⟩ := E.exists_zK_eq hT hM hGz hnwc
  have hcard := E.card_K_eq hGz
  rw [E.ncard_zK h, card_Zset] at hcard
  have hne := E.card_K_ne_640 hT hGz
  cases a <;> cases b <;> simp at hab <;> simp at hcard <;> first | exact h | exact absurd hcard hne

theorem card_K [Finite G] (hT : quasithinIsSylowTwo T) (hM : quasithinIsMaxTwoLocal M)
    (hGz : Subgroup.centralizer ({E.z} : Set G) = T)
    (hnwc : ¬ ∀ g : G, g⁻¹ * E.z * g ∈ E.B → g⁻¹ * E.z * g = E.z) : Nat.card E.K = 1152 := by
  have hcard := E.card_K_eq hGz
  rw [E.ncard_zK (E.zK_eq_full hT hM hGz hnwc), card_Zset] at hcard
  simpa using hcard

@[expose] def Y : Subgroup G := Subgroup.centralizer ({E.t} : Set G)

@[expose] def X : Subgroup G := oTwoUpper E.Y

theorem t_sq : E.t * E.t = 1 := by
  rw [t, ← map_mul, t0_sq, map_one]

theorem t_ne_one : E.t ≠ 1 := by
  intro h
  exact t0_ne_one (E.injective (by rw [map_one]; exact h))

theorem mem_Y {y : G} : y ∈ E.Y ↔ y * E.t = E.t * y := by
  unfold Y
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact (h E.t rfl).symm
  · intro h g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact h.symm

theorem X_le_Y : E.X ≤ E.Y := oTwoUpper_le E.Y

theorem mem_X_of_odd {x : G} (hx : x ∈ E.Y) (ho : Odd (orderOf x)) : x ∈ E.X :=
  mem_oTwoUpper_of_odd hx ho

theorem conj_mem_X {g y : G} (hg : g ∈ E.Y) (hy : y ∈ E.X) : g * y * g⁻¹ ∈ E.X :=
  conj_mem_oTwoUpper (Subgroup.le_normalizer hg) hy

theorem t_not_mem_zK (hzK : ∀ y : G, y ∈ E.zK ↔ ∃ w ∈ Zset true true, E.ι w = y) :
    E.t ∉ E.zK := by
  intro h
  obtain ⟨w, hw, hwt⟩ := (hzK _).1 h
  have : w = t0 := E.injective hwt
  rw [this] at hw
  exact D23_not_mem_Zset t0 (Or.inl t0_mem_D2) hw

theorem B_compl (hzK : ∀ y : G, y ∈ E.zK ↔ ∃ w ∈ Zset true true, E.ι w = y) {y : G}
    (hy : y ∈ E.B) (hy1 : y ≠ 1) (hyz : y ∉ E.zK) :
    ∃ w ∈ A2, E.ι w = y ∧ (D2 w = true ∨ D3 w = true) := by
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hy
  refine ⟨w, hw, rfl, B_compl_Zset w hw ?_ ?_⟩
  · intro h
    apply hy1
    rw [h, map_one]
  · intro h
    exact hyz ((hzK _).2 ⟨w, h, rfl⟩)

theorem ncard_tK_le (hzK : ∀ y : G, y ∈ E.zK ↔ ∃ w ∈ Zset true true, E.ι w = y) :
    {y | ∃ k ∈ E.K, k⁻¹ * E.t * k = y}.ncard ≤ 6 := by
  classical
  have hsub : {y | ∃ k ∈ E.K, k⁻¹ * E.t * k = y} ⊆ E.ι '' ↑(Finset.univ.filter fun w : Wc =>
      w ∈ A2 ∧ w ≠ 1 ∧ w ∉ Zset true true) := by
    rintro _ ⟨k, hk, rfl⟩
    have hB : k⁻¹ * E.t * k ∈ E.B := E.conj_mem_B_of_mem_K hk E.t_mem_B
    obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.mp hB
    refine ⟨w, ?_, hwy⟩
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, hw, ?_, ?_⟩
    · rintro rfl
      rw [map_one] at hwy
      apply E.t_ne_one
      calc E.t = k * (k⁻¹ * E.t * k) * k⁻¹ := by group
        _ = 1 := by rw [← hwy]; group
    · intro hz
      apply E.t_not_mem_zK hzK
      have : E.ι w ∈ E.zK := (hzK _).2 ⟨w, hz, rfl⟩
      rw [hwy] at this
      have := E.zK_inv this (E.K.inv_mem hk)
      simpa [mul_assoc] using this
  calc _ ≤ (E.ι '' ↑(Finset.univ.filter fun w : Wc => w ∈ A2 ∧ w ≠ 1 ∧ w ∉ Zset true true)).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = 6 := by
      rw [Set.ncard_image_of_injective _ E.injective, Set.ncard_coe_finset, card_NK]

theorem mk_one_mul (a b : S4) :
    (⟨1, a, false⟩ : Wc) * ⟨1, b, false⟩ = ⟨1, a * b, false⟩ := by
  rw [Wc.mul_false]
  show (⟨1 * 1, a * b, false⟩ : Wc) = _
  rw [mul_one]

theorem mk_one_pow_three {a : S4} (h : a * a * a = 1) :
    (⟨1, a, false⟩ : Wc) ^ 3 = 1 := by
  rw [pow_succ, pow_two, mk_one_mul, mk_one_mul, h]
  rfl

theorem mk_one_sq {a : S4} (h : a * a = 1) : (⟨1, a, false⟩ : Wc) * ⟨1, a, false⟩ = 1 := by
  rw [mk_one_mul, h]
  rfl

theorem exists_c [Finite G] (hzK : ∀ y : G, y ∈ E.zK ↔ ∃ w ∈ Zset true true, E.ι w = y)
    (hK : Nat.card E.K = 1152) : ∃ c : G, c ∈ E.K ∧ c ∈ E.Y ∧ orderOf c = 3 := by
  have h := ncard_conjClass_mul_card E.K E.t
  rw [hK] at h
  have hle := E.ncard_tK_le hzK
  have h3 : 3 ∣ Nat.card ↥(E.K ⊓ Subgroup.centralizer ({E.t} : Set G)) := by
    generalize {y | ∃ k ∈ E.K, k⁻¹ * E.t * k = y}.ncard = a at h hle
    generalize Nat.card ↥(E.K ⊓ Subgroup.centralizer ({E.t} : Set G)) = c at h ⊢
    interval_cases a <;> omega
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(E.K ⊓ Subgroup.centralizer ({E.t} : Set G))) 3 h3
  exact ⟨c, c.2.1, c.2.2, by rw [← Subgroup.orderOf_coe] at hc; exact hc⟩

theorem c_pow_three {c : G} (hc3 : orderOf c = 3) : c ^ 3 = 1 := hc3 ▸ pow_orderOf_eq_one c

theorem c_ne_one {c : G} (hc3 : orderOf c = 3) : c ≠ 1 := by
  rintro rfl
  rw [orderOf_one] at hc3
  omega

theorem c_odd {c : G} (hc3 : orderOf c = 3) : Odd (orderOf c) := by
  rw [hc3]; decide

theorem c_not_comm_zK (hT : quasithinIsSylowTwo T) (hGz : Subgroup.centralizer ({E.z} : Set G) = T)
    {c y : G} (hc3 : orderOf c = 3) (hy : y ∈ E.zK) : c * y ≠ y * c := by
  intro hcy
  obtain ⟨k, hk, rfl⟩ := hy
  have hcomm : (k * c * k⁻¹) * E.z = E.z * (k * c * k⁻¹) := by
    have : c * (k⁻¹ * E.z * k) = (k⁻¹ * E.z * k) * c := hcy
    calc k * c * k⁻¹ * E.z = k * (c * (k⁻¹ * E.z * k)) * k⁻¹ := by group
      _ = k * ((k⁻¹ * E.z * k) * c) * k⁻¹ := by rw [this]
      _ = E.z * (k * c * k⁻¹) := by group
  have hmem' : k * c * k⁻¹ ∈ Subgroup.centralizer ({E.z} : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hcomm.symm
  rw [hGz] at hmem'
  have h3 : (k * c * k⁻¹) ^ 3 = 1 := by rw [conj_pow, c_pow_three hc3]; group
  have h1 : k * c * k⁻¹ ≠ 1 := by
    intro h
    apply c_ne_one hc3
    have : c = k⁻¹ * (k * c * k⁻¹) * k := by group
    rw [this, h]
    group
  exact not_mem_isPGroup_of_order_three hT.1 h3 h1 hmem'

theorem card_R [Finite G] (hT : quasithinIsSylowTwo T)
    (hGz : Subgroup.centralizer ({E.z} : Set G) = T) {c : G} (hcK : c ∈ E.K) (hcY : c ∈ E.Y)
    (hc3 : orderOf c = 3) :
    Nat.card ↥(E.B ⊓ Subgroup.centralizer ({c} : Set G)) = 4 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcard : Nat.card (Subgroup.zpowers c) = 3 := card_zpowers_of_orderOf hc3
  have hp : IsPGroup 3 (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [hcard]; norm_num)
  have hmod := card_modEq_card_inf_centralizer (p := 3) (B := E.B) hcK hp
  rw [E.card_B] at hmod
  have hdvd : Nat.card ↥(E.B ⊓ Subgroup.centralizer ({c} : Set G)) ∣ 2 ^ 4 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : E.B ⊓ Subgroup.centralizer ({c} : Set G) ≤ E.B)
    rw [E.card_B] at this
    simpa using this
  obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [hi'] at hmod ⊢
  unfold Nat.ModEq at hmod
  have hi024 : i = 0 ∨ i = 2 ∨ i = 4 := by interval_cases i <;> omega
  have htR : E.t ∈ E.B ⊓ Subgroup.centralizer ({c} : Set G) :=
    ⟨E.t_mem_B, Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (E.mem_Y.1 hcY)⟩
  rcases hi024 with rfl | rfl | rfl
  · exfalso
    have : E.B ⊓ Subgroup.centralizer ({c} : Set G) = ⊥ :=
      Subgroup.eq_bot_of_card_eq _ (by rw [hi']; norm_num)
    rw [this, Subgroup.mem_bot] at htR
    exact E.t_ne_one htR
  · norm_num
  · exfalso
    have hle : E.B ⊓ Subgroup.centralizer ({c} : Set G) = E.B := by
      refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
      rw [hi', E.card_B]
      norm_num
    have hzR : E.z ∈ E.B ⊓ Subgroup.centralizer ({c} : Set G) := by
      rw [hle]; exact E.z_mem_B
    exact E.c_not_comm_zK hT hGz hc3 E.z_mem_zK (Subgroup.mem_centralizer_iff.mp hzR.2 c rfl)

theorem R_sub [Finite G] (hT : quasithinIsSylowTwo T)
    (hGz : Subgroup.centralizer ({E.z} : Set G) = T)
    (hzK : ∀ y : G, y ∈ E.zK ↔ ∃ w ∈ Zset true true, E.ι w = y) {c : G} (hcY : c ∈ E.Y)
    (hc3 : orderOf c = 3) {y : G} (hy : y ∈ E.B) (hcy : c * y = y * c) :
    ∃ w ∈ A2, E.ι w = y ∧ w.b = 1 := by
  have hct : c * E.t = E.t * c := E.mem_Y.1 hcY
  obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.mp hy
  refine ⟨w, hw, hwy, ?_⟩
  by_cases hy1 : y = 1
  · have : w = 1 := E.injective (by rw [hwy, hy1, map_one])
    rw [this]
    rfl
  have hyz : y ∉ E.zK := fun h => E.c_not_comm_zK hT hGz hc3 h hcy
  obtain ⟨w', hw', hw'y, hD⟩ := E.B_compl hzK hy hy1 hyz
  have hw'w : w' = w := E.injective (by rw [hw'y, hwy])
  subst hw'w
  by_cases hwt : w' = t0
  · rw [hwt]
    exact t0_b
  have hty : E.t * y ∈ E.B := E.B.mul_mem E.t_mem_B hy
  have hty1 : E.t * y ≠ 1 := by
    intro h
    apply hwt
    apply E.injective
    have h2 : y = E.t⁻¹ := eq_inv_of_mul_eq_one_right h
    have h3 : E.t⁻¹ = E.t := inv_eq_of_mul_eq_one_right E.t_sq
    rw [hwy, h2, h3]
    rfl
  have htyz : E.t * y ∉ E.zK := by
    intro h
    exact E.c_not_comm_zK hT hGz hc3 h (by
      calc c * (E.t * y) = E.t * y * c := by
            rw [← mul_assoc, hct, mul_assoc, hcy, mul_assoc])
  obtain ⟨w'', hw'', hw''y, hD''⟩ := E.B_compl hzK hty hty1 htyz
  have hw''eq : w'' = t0 * w' := E.injective (by
    rw [hw''y, map_mul, hwy]
    rfl)
  rw [hw''eq] at hD''
  exact R_fact w' hw hD hwt hD''

theorem c_comm_V'_one [Finite G] (hT : quasithinIsSylowTwo T)
    (hGz : Subgroup.centralizer ({E.z} : Set G) = T)
    (hzK : ∀ y : G, y ∈ E.zK ↔ ∃ w ∈ Zset true true, E.ι w = y) {c : G} (hcK : c ∈ E.K)
    (hcY : c ∈ E.Y) (hc3 : orderOf c = 3) {w : Wc} (hw : w ∈ A2) (hwb : w.b = 1) :
    c * E.ι w = E.ι w * c := by
  classical
  set R : Subgroup G := E.B ⊓ Subgroup.centralizer ({c} : Set G) with hR
  have hRsub : (R : Set G) ⊆ E.ι '' ↑(Finset.univ.filter fun w : Wc => w ∈ A2 ∧ w.b = 1) := by
    intro y hy
    obtain ⟨w', hw', hw'y, hb⟩ := E.R_sub hT hGz hzK hcY hc3 hy.1
      (Subgroup.mem_centralizer_iff.mp hy.2 c rfl)
    refine ⟨w', ?_, hw'y⟩
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hw', hb⟩
  have hcard : (E.ι '' ↑(Finset.univ.filter fun w : Wc => w ∈ A2 ∧ w.b = 1)).ncard = 4 := by
    rw [Set.ncard_image_of_injective _ E.injective, Set.ncard_coe_finset, card_Rm]
  have hRcard : (R : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact E.card_R hT hGz hcK hcY hc3
  have heq := Set.eq_of_subset_of_ncard_le hRsub (by rw [hcard, hRcard]) (Set.toFinite _)
  have hmem : E.ι w ∈ (R : Set G) := by
    rw [heq]
    refine ⟨w, ?_, rfl⟩
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hw, hwb⟩
  exact (Subgroup.mem_centralizer_iff.mp hmem.2 c rfl)

theorem comm_of_conj_eq {c y : G} (h : c⁻¹ * y * c = y) : c * y = y * c := by
  calc c * y = c * (c⁻¹ * y * c) := by rw [h]
    _ = y * c := by group

theorem c_conj_one_V' [Finite G] (hT : quasithinIsSylowTwo T)
    (hGz : Subgroup.centralizer ({E.z} : Set G) = T)
    (hzK : ∀ y : G, y ∈ E.zK ↔ ∃ w ∈ Zset true true, E.ι w = y) {c : G} (hcK : c ∈ E.K)
    (hcY : c ∈ E.Y) (hc3 : orderOf c = 3) {b : S4} (hb : b ∈ v'List) (hb1 : b ≠ 1) :
    ∃ b' ∈ v'List, b' ≠ 1 ∧ b' ≠ b ∧
      c⁻¹ * E.ι ⟨1, b, false⟩ * c = E.ι ⟨1, b', false⟩ := by
  set w₀ : Wc := ⟨1, b, false⟩ with hw₀
  have hw₀A : w₀ ∈ A2 := V'_one_mem b hb
  obtain ⟨hw₀A', hD₀⟩ := one_V'_mem_Zset_false b hb hb1
  set y : G := E.ι w₀ with hy
  have hyB : y ∈ E.B := Subgroup.mem_map_of_mem _ hw₀A
  have hyz : y ∉ E.zK := by
    intro h
    obtain ⟨w', hw', hw'y⟩ := (hzK _).1 h
    have : w' = w₀ := E.injective hw'y
    rw [this] at hw'
    exact D23_not_mem_Zset w₀ hD₀ hw'
  have hy1 : y ≠ 1 := by
    intro h
    have : w₀ = 1 := E.injective (by rw [hy] at h; rw [h, map_one])
    have hb' : w₀.b = b := rfl
    rw [this] at hb'
    exact hb1 hb'.symm
  have hy₂B : c⁻¹ * y * c ∈ E.B := E.conj_mem_B_of_mem_K hcK hyB
  have hy₂1 : c⁻¹ * y * c ≠ 1 := by
    intro h
    apply hy1
    have : y = c * (c⁻¹ * y * c) * c⁻¹ := by group
    rw [this, h]
    group
  have hy₂z : c⁻¹ * y * c ∉ E.zK := fun h => hyz ((E.zK_inv_iff hcK).2 h)
  obtain ⟨w₂, hw₂A, hw₂y, hD₂⟩ := E.B_compl hzK hy₂B hy₂1 hy₂z
  have hnc : ¬ c * y = y * c := by
    intro hcy
    obtain ⟨w', hw', hw'y, hb'⟩ := E.R_sub hT hGz hzK hcY hc3 hyB hcy
    have : w' = w₀ := E.injective (by rw [hw'y])
    rw [this] at hb'
    exact hb1 hb'
  have hw₂b : w₂.b ≠ 1 := by
    intro hb2
    apply hnc
    have h1 := E.c_comm_V'_one hT hGz hzK hcK hcY hc3 hw₂A hb2
    rw [hw₂y] at h1
    have h2 : y * c = (c⁻¹ * y * c) * c := by rw [← h1]; group
    have h3 : y = c⁻¹ * y * c := mul_right_cancel h2
    exact comm_of_conj_eq h3.symm
  obtain ⟨ha, hb', he⟩ := P_fact w₂ hw₂A hD₂ hw₂b
  have hw₂eq : w₂ = ⟨1, w₂.b, false⟩ := Wc.ext ha rfl he
  refine ⟨w₂.b, hb', hw₂b, ?_, hw₂y.symm.trans (congrArg E.ι hw₂eq)⟩
  intro hbb
  have : w₂ = w₀ := by rw [hw₂eq, hbb]
  apply hnc
  apply comm_of_conj_eq
  rw [← hw₂y, this]

theorem ι_one_mem_Y (a : S4) : E.ι ⟨1, a, false⟩ ∈ E.Y := by
  rw [E.mem_Y, t, ← map_mul, ← map_mul, one_a_commute_t0 a]

theorem mul_conj_mem_X {x c : G} (hx : x ∈ E.Y) (hx2 : x * x = 1) (hc : c ∈ E.X) :
    x * (c⁻¹ * x * c) ∈ E.X := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have h1 := E.conj_mem_X hx (E.X.inv_mem hc)
  rw [hxi] at h1
  have := E.X.mul_mem h1 hc
  simpa [mul_assoc] using this

theorem V'_le_X [Finite G] (hT : quasithinIsSylowTwo T)
    (hGz : Subgroup.centralizer ({E.z} : Set G) = T)
    (hzK : ∀ y : G, y ∈ E.zK ↔ ∃ w ∈ Zset true true, E.ι w = y) {c : G} (hcK : c ∈ E.K)
    (hcY : c ∈ E.Y) (hc3 : orderOf c = 3) : ∀ v ∈ v'List, E.ι ⟨1, v, false⟩ ∈ E.X := by
  have hcX : c ∈ E.X := E.mem_X_of_odd hcY (c_odd hc3)
  have hf1 : f1 ∈ v'List := f1_mem
  have hf1' : f1 ≠ 1 := f1_ne_one
  obtain ⟨b₂, hb₂, hb₂1, hb₂f, hb₂eq⟩ := E.c_conj_one_V' hT hGz hzK hcK hcY hc3 hf1 hf1'
  set a : S4 := f1 * b₂ with ha
  obtain ⟨hamem, ha1, haf, hab⟩ := V'_third f1 hf1 b₂ hb₂ hf1' hb₂1 (Ne.symm hb₂f)
  have hwX : E.ι ⟨1, a, false⟩ ∈ E.X := by
    have h := E.mul_conj_mem_X (E.ι_one_mem_Y f1) (by rw [← map_mul, mk_one_sq f1_sq, map_one]) hcX
    rw [hb₂eq, ← map_mul, mk_one_mul] at h
    exact h
  obtain ⟨b₃, hb₃, hb₃1, hb₃a, hb₃eq⟩ := E.c_conj_one_V' hT hGz hzK hcK hcY hc3 hamem ha1
  have hw₃X : E.ι ⟨1, b₃, false⟩ ∈ E.X := by
    rw [← hb₃eq]
    have := E.conj_mem_X (E.Y.inv_mem hcY) hwX
    simpa [mul_assoc] using this
  intro v hv
  rcases V'_generated a hamem b₃ hb₃ ha1 hb₃1 (Ne.symm hb₃a) v hv with rfl | rfl | rfl | rfl
  · rw [show (⟨1, 1, false⟩ : Wc) = 1 from rfl, map_one]
    exact E.X.one_mem
  · exact hwX
  · exact hw₃X
  · rw [← mk_one_mul, map_mul]
    exact E.X.mul_mem hwX hw₃X

theorem V_le_X (v : S4) (hv : v ∈ vList) : E.ι ⟨1, v, false⟩ ∈ E.X := by
  obtain ⟨a, b, ha, hb, hab⟩ := V_odd_products v hv
  have hodd : ∀ a : S4, a * a * a = 1 → E.ι ⟨1, a, false⟩ ∈ E.X := fun a ha => by
    refine E.mem_X_of_odd (E.ι_one_mem_Y a) ?_
    have h3 : (E.ι ⟨1, a, false⟩) ^ 3 = 1 := by rw [← map_pow, mk_one_pow_three ha, map_one]
    exact Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one h3)
  rw [← hab, ← mk_one_mul, map_mul]
  exact E.X.mul_mem (hodd a ha) (hodd b hb)

theorem T₂_le_X [Finite G] (hT : quasithinIsSylowTwo T)
    (hGz : Subgroup.centralizer ({E.z} : Set G) = T)
    (hzK : ∀ y : G, y ∈ E.zK ↔ ∃ w ∈ Zset true true, E.ι w = y) {c : G} (hcK : c ∈ E.K)
    (hcY : c ∈ E.Y) (hc3 : orderOf c = 3) : E.T₂ ≤ E.X := by
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨d, hd, hw'⟩ := T2h_eq w hw
  obtain ⟨v, hv, v', hv', hdv⟩ := D_eq_V_mul_V' d hd
  have : w = ⟨1, v, false⟩ * ⟨1, v', false⟩ := by rw [hw', mk_one_mul, ← hdv]
  rw [this, map_mul]
  exact E.X.mul_mem (E.V_le_X v hv) (E.V'_le_X hT hGz hzK hcK hcY hc3 v' hv')

end Emb

end CFSG.Quasithin.A10
