module

public import CFSG.Walter.J1Recog.Coord
public import CFSG.Walter.J1Recog.Tools
public import CFSG.Walter.J1.CardEq

public section

namespace CFSG.Walter.J1Recog

open CFSG.Walter.J1

structure Setup (G : Type) [Group G] [Finite G] where
  h : JankoHyp G
  S : Sylow 2 G
  n : G
  m : G
  t_mem : h.t ∈ S
  n_mem : n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G)
  m_mem : m ∈ Subgroup.normalizer ((S : Subgroup G) : Set G)
  orderOf_n : orderOf n = 7
  orderOf_m : orderOf m = 3
  m_n : m⁻¹ * n * m = n ^ 2
  m_t : m * h.t = h.t * m
  rel : ee h.t n 0 * ee h.t n 2 = ee h.t n 3

theorem exists_sq_conj {G : Type*} [Group G] {x y : G} (hy : orderOf y = 7) (hx : orderOf x = 3)
    (hxy : x * y * x⁻¹ ∈ Subgroup.zpowers y) (hc : x * y ≠ y * x) :
    ∃ m, (m = x ∨ m = x⁻¹) ∧ m⁻¹ * y * m = y ^ 2 := by
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hy7 : y ^ 7 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  rcases conj_eq_pow_of_seven_three hy hx3 hxy with h1 | h2 | h4
  · exact absurd (by rw [← mul_inv_eq_iff_eq_mul, h1]) hc
  · refine ⟨x⁻¹, Or.inr rfl, ?_⟩
    rw [inv_inv, h2]
  · refine ⟨x, Or.inl rfl, ?_⟩
    set z := x⁻¹ * y * x with hz
    have hz4 : z ^ 4 = y := by
      have : z ^ 4 = x⁻¹ * y ^ 4 * x := by
        rw [hz, show x⁻¹ * y * x = x⁻¹ * y * x⁻¹⁻¹ by rw [inv_inv], conj_pow, inv_inv]
      rw [this, ← h4]
      group
    have hz7 : z ^ 7 = 1 := by
      rw [hz, show x⁻¹ * y * x = x⁻¹ * y * x⁻¹⁻¹ by rw [inv_inv], conj_pow, hy7]
      group
    calc z = z ^ 8 := by rw [show (8 : ℕ) = 7 + 1 from rfl, pow_succ, hz7, one_mul]
      _ = (z ^ 4) ^ 2 := by rw [← pow_mul]
      _ = y ^ 2 := by rw [hz4]

theorem exists_setup {G : Type} [Group G] [Finite G] (h : JankoHyp G) : Nonempty (Setup G) := by
  obtain ⟨S⟩ : Nonempty (Sylow 2 G) := inferInstance
  set H := Subgroup.normalizer ((S : Subgroup G) : Set G)
  obtain ⟨y, hyH, hy⟩ : ∃ y ∈ H, orderOf y = 7 := by
    have h48 := h.ncard_orderOf_seven S
    obtain ⟨y, hy⟩ := Set.nonempty_of_ncard_ne_zero (by rw [h48]; norm_num)
    exact ⟨y, hy.1, hy.2⟩
  obtain ⟨x, hxH, hxy, hx⟩ : ∃ x ∈ H, x * y * x⁻¹ ∈ Subgroup.zpowers y ∧ orderOf x = 3 := by
    have h14 := h.ncard_normalizer_three S hyH hy
    obtain ⟨x, hx⟩ := Set.nonempty_of_ncard_ne_zero (by rw [h14]; norm_num)
    exact ⟨x, hx.1, hx.2.1, hx.2.2⟩
  have hc : x * y ≠ y * x := by
    intro hc
    apply h.not_seven_mul_dvd_orderOf (q := 3) (Or.inr rfl) (x * y)
    rw [(Commute.orderOf_mul_eq_mul_orderOf_of_coprime hc (by rw [hx, hy]; norm_num)), hx, hy]
  obtain ⟨m, hmx, hm⟩ := exists_sq_conj hy hx hxy hc
  have hmH : m ∈ H := by rcases hmx with rfl | rfl; exacts [hxH, H.inv_mem hxH]
  have hmo : orderOf m = 3 := by rcases hmx with rfl | rfl; exacts [hx, by rw [orderOf_inv, hx]]
  obtain ⟨t₀, ht₀, ht₀1⟩ := exists_ne_one_of_card (h.card_inf_centralizer_three S hmH hmo)
    (by norm_num)
  have ht₀S : t₀ ∈ S := ht₀.1
  have ht₀m : t₀ * m = m * t₀ := Subgroup.mem_centralizer_singleton_iff.mp ht₀.2
  have ht₀2 : orderOf t₀ = 2 := orderOf_eq_two_iff.mpr ⟨h.mul_self_of_mem_sylow' S ht₀S, ht₀1⟩
  have hfree : ∀ v ∈ (S : Subgroup G), v ≠ 1 → y * v ≠ v * y := by
    intro v hv hv1 hcv
    have hv2 : orderOf v = 2 := orderOf_eq_two_iff.mpr ⟨h.mul_self_of_mem_sylow' S hv, hv1⟩
    apply h.not_seven_mul_dvd_orderOf (q := 2) (Or.inl rfl) (y * v)
    rw [(Commute.orderOf_mul_eq_mul_orderOf_of_coprime hcv (by rw [hy, hv2]; norm_num)), hy, hv2]
  have hc : IsCoord (S : Subgroup G) t₀ y := ⟨h.card_sylow' S,
    fun a ha b hb => congrArg Subtype.val ((h.abelian_sylow S).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩),
    fun a ha => h.mul_self_of_mem_sylow' S ha, ht₀S, ht₀1, hyH, hy, hfree⟩
  obtain ⟨n, hn, hrel⟩ := hc.exists_normal_form
  have hnH : n ∈ H := by rcases hn with rfl | rfl; exacts [hyH, H.inv_mem hyH]
  have hno : orderOf n = 7 := by rcases hn with rfl | rfl; exacts [hy, by rw [orderOf_inv, hy]]
  have hmn : m⁻¹ * n * m = n ^ 2 := by
    rcases hn with rfl | rfl
    · exact hm
    · rw [inv_pow, ← hm]
      group
  obtain ⟨g, hg⟩ := h.exists_conj_t_eq ht₀2
  have ht₀S' : (h.conj g).t ∈ S := by rw [hg]; exact ht₀S
  have hmt : m * (h.conj g).t = (h.conj g).t * m := by rw [hg]; exact ht₀m.symm
  have hrel' : ee (h.conj g).t n 0 * ee (h.conj g).t n 2 = ee (h.conj g).t n 3 := by
    rw [hg]; exact hrel
  exact ⟨⟨h.conj g, S, n, m, ht₀S', hnH, hmH, hno, hmo, hmn, hmt, hrel'⟩⟩

namespace Setup

variable {G : Type} [Group G] [Finite G] (X : Setup G)

abbrev t : G := X.h.t

abbrev F : Subgroup G := X.h.F

abbrev e (i : ℕ) : G := ee X.t X.n i

include X in
theorem card_G : Nat.card G = 175560 := JankoHyp.card_eq X.h

theorem t_mul_t : X.t * X.t = 1 := X.h.t_mul_t

theorem n_pow_seven : X.n ^ 7 = 1 := by rw [← X.orderOf_n]; exact pow_orderOf_eq_one _

theorem m_pow_three : X.m ^ 3 = 1 := by rw [← X.orderOf_m]; exact pow_orderOf_eq_one _

theorem n_ne_one : X.n ≠ 1 := by
  intro h1; have := X.orderOf_n; rw [h1, orderOf_one] at this; omega

theorem m_ne_one : X.m ≠ 1 := by
  intro h1; have := X.orderOf_m; rw [h1, orderOf_one] at this; omega

theorem e_mem (i : ℕ) : X.e i ∈ (X.S : Subgroup G) := by
  have hni : X.n ^ i ∈ Subgroup.normalizer ((X.S : Subgroup G) : Set G) :=
    Subgroup.pow_mem _ X.n_mem i
  have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hni) X.t).mp X.t_mem
  rw [inv_inv] at this
  exact this

theorem mem_comm {a b : G} (ha : a ∈ X.S) (hb : b ∈ X.S) : a * b = b * a :=
  congrArg Subtype.val ((X.h.abelian_sylow X.S).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem mem_mul_self {a : G} (ha : a ∈ X.S) : a * a = 1 := X.h.mul_self_of_mem_sylow' X.S ha

theorem e_comm (i j : ℕ) : X.e i * X.e j = X.e j * X.e i := X.mem_comm (X.e_mem i) (X.e_mem j)

theorem e_mul_self (i : ℕ) : X.e i * X.e i = 1 := X.mem_mul_self (X.e_mem i)

theorem e_zero : X.e 0 = X.t := ee_zero _ _

theorem e_mod (i : ℕ) : X.e (i % 7) = X.e i := ee_mod X.n_pow_seven i

theorem rel_shift (j : ℕ) : X.e j * X.e (j + 2) = X.e (j + 3) := by
  have := ee_mul_shift X.rel j
  simpa [e, Nat.add_comm] using this

theorem rel05 : X.e 0 * X.e 1 = X.e 5 := by
  have h5 := X.rel_shift 5
  rw [show 5 + 2 = 7 from rfl, show 5 + 3 = 8 from rfl, ← X.e_mod 7, ← X.e_mod 8,
    show 7 % 7 = 0 from rfl, show 8 % 7 = 1 from rfl] at h5
  rw [← h5, ← mul_assoc, X.e_comm 0 5, mul_assoc, X.e_mul_self, mul_one]

theorem rel03 : X.e 0 * X.e 2 = X.e 3 := X.rel_shift 0

theorem rel06 : X.e 1 * X.e 2 = X.e 6 := by
  have h6 := X.rel_shift 6
  rw [show 6 + 2 = 8 from rfl, show 6 + 3 = 9 from rfl, ← X.e_mod 8, ← X.e_mod 9,
    show 8 % 7 = 1 from rfl, show 9 % 7 = 2 from rfl] at h6
  rw [← h6, ← mul_assoc, X.e_comm 1 6, mul_assoc, X.e_mul_self, mul_one]

theorem rel04 : X.e 0 * X.e 6 = X.e 4 := by
  have h4 := X.rel_shift 4
  rw [show 4 + 2 = 6 from rfl, show 4 + 3 = 7 from rfl, ← X.e_mod 7,
    show 7 % 7 = 0 from rfl] at h4
  rw [← h4, mul_assoc, X.e_mul_self, mul_one]

theorem m_e (i : ℕ) : X.m⁻¹ * X.e i * X.m = X.e (2 * i) := by
  have hmn : ∀ k : ℕ, X.m⁻¹ * X.n ^ k * X.m = X.n ^ (2 * k) := by
    intro k
    rw [show X.m⁻¹ * X.n ^ k * X.m = (X.m⁻¹ * X.n * X.m) ^ k by
      rw [show X.m⁻¹ * X.n * X.m = X.m⁻¹ * X.n * X.m⁻¹⁻¹ by rw [inv_inv], conj_pow, inv_inv],
      X.m_n, ← pow_mul]
  have hmt : X.m⁻¹ * X.t * X.m = X.t := by
    rw [mul_assoc, ← X.m_t, ← mul_assoc, inv_mul_cancel, one_mul]
  calc X.m⁻¹ * X.e i * X.m
      = (X.m⁻¹ * X.n ^ i * X.m)⁻¹ * (X.m⁻¹ * X.t * X.m) * (X.m⁻¹ * X.n ^ i * X.m) := by
        simp only [e, ee]; group
    _ = X.e (2 * i) := by rw [hmn, hmt]; rfl

theorem m_mem_centralizer : X.m ∈ Subgroup.centralizer ({X.t} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr X.m_t

theorem m_mem_F : X.m ∈ X.F :=
  X.h.mem_F_of_odd X.m_mem_centralizer (by rw [X.orderOf_m]; decide)

theorem e_mem_centralizer (i : ℕ) : X.e i ∈ Subgroup.centralizer ({X.t} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr (X.mem_comm (X.e_mem i) X.t_mem)

theorem t_ne_one : X.t ≠ 1 := X.h.t_ne_one

theorem free_of_seven {y : G} (hy : orderOf y = 7) {v : G} (hv : v ∈ (X.S : Subgroup G))
    (hv1 : v ≠ 1) : y * v ≠ v * y := by
  intro hcv
  have hv2 : orderOf v = 2 := orderOf_eq_two_iff.mpr ⟨X.mem_mul_self hv, hv1⟩
  apply X.h.not_seven_mul_dvd_orderOf (q := 2) (Or.inl rfl) (y * v)
  rw [(Commute.orderOf_mul_eq_mul_orderOf_of_coprime hcv (by rw [hy, hv2]; norm_num)), hy, hv2]

theorem isCoord : IsCoord (X.S : Subgroup G) X.t X.n :=
  ⟨X.h.card_sylow' X.S, fun _ ha _ hb => X.mem_comm ha hb, fun _ ha => X.mem_mul_self ha,
    X.t_mem, X.t_ne_one, X.n_mem, X.orderOf_n, fun _ hv hv1 => X.free_of_seven X.orderOf_n hv hv1⟩

theorem e_ne {i j : ℕ} (hij : i < j) (hj : j < 7) : X.e i ≠ X.e j := X.isCoord.ee_ne hij hj

theorem e_ne_one (i : ℕ) : X.e i ≠ 1 := X.isCoord.ee_ne_one i

theorem e_mem_F_two {i : ℕ} (hi : X.e i ∈ X.F) : X.e (2 * i) ∈ X.F := by
  rw [← X.m_e]
  exact X.F.mul_mem (X.F.mul_mem (X.F.inv_mem X.m_mem_F) hi) X.m_mem_F

theorem card_inf_F : Nat.card ((X.S : Subgroup G) ⊓ X.F : Subgroup G) = 4 :=
  X.h.card_inf_F X.S X.t_mem

theorem ncard_inf_F : ((((X.S : Subgroup G) ⊓ X.F : Subgroup G)) : Set G).ncard = 4 := by
  rw [← X.card_inf_F]
  exact (Nat.card_coe_set_eq _).symm

theorem e1_not_mem_F : X.e 1 ∉ X.F := by
  intro h1
  have h2 : X.e 2 ∈ X.F := X.e_mem_F_two h1
  have h4 : X.e 4 ∈ X.F := X.e_mem_F_two h2
  have h6 : X.e 6 ∈ X.F := by rw [← X.rel06]; exact X.F.mul_mem h1 h2
  have hsub : ({1, X.e 1, X.e 2, X.e 4, X.e 6} : Set G) ⊆
      (((X.S : Subgroup G) ⊓ X.F : Subgroup G) : Set G) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact ⟨X.e_mem 1, h1⟩
    · exact ⟨X.e_mem 2, h2⟩
    · exact ⟨X.e_mem 4, h4⟩
    · exact ⟨X.e_mem 6, h6⟩
  have hcard := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [X.ncard_inf_F] at hcard
  have hne : ∀ i, (1 : G) ≠ X.e i := fun i h => X.e_ne_one i h.symm
  rw [Set.ncard_insert_of_notMem (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hne 1, hne 2, hne 4, hne 6⟩),
    Set.ncard_insert_of_notMem (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨X.e_ne (by norm_num) (by norm_num), X.e_ne (by norm_num) (by norm_num),
        X.e_ne (by norm_num) (by norm_num)⟩),
    Set.ncard_insert_of_notMem (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨X.e_ne (by norm_num) (by norm_num), X.e_ne (by norm_num) (by norm_num)⟩),
    Set.ncard_pair (X.e_ne (by norm_num) (by norm_num))] at hcard
  omega

theorem e2_not_mem_F : X.e 2 ∉ X.F := by
  intro h2
  apply X.e1_not_mem_F
  have h4 : X.e 4 ∈ X.F := X.e_mem_F_two h2
  have h8 := X.e_mem_F_two h4
  rwa [← X.e_mod, show 2 * 4 % 7 = 1 from rfl] at h8

theorem e4_not_mem_F : X.e 4 ∉ X.F := by
  intro h4
  apply X.e1_not_mem_F
  have h8 := X.e_mem_F_two h4
  rwa [← X.e_mod, show 2 * 4 % 7 = 1 from rfl] at h8

theorem t_not_mem_F : X.t ∉ X.F := X.h.t_not_mem

theorem inf_F_eq : (((X.S : Subgroup G) ⊓ X.F : Subgroup G) : Set G) =
    {1, X.e 3, X.e 5, X.e 6} := by
  have hsub : (((X.S : Subgroup G) ⊓ X.F : Subgroup G) : Set G) ⊆ {1, X.e 3, X.e 5, X.e 6} := by
    rintro x ⟨hxS, hxF⟩
    rcases X.isCoord.cover hxS with rfl | ⟨i, hi, rfl⟩
    · exact Set.mem_insert _ _
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      interval_cases i
      · exact absurd (X.e_zero ▸ hxF) X.t_not_mem_F
      · exact absurd hxF X.e1_not_mem_F
      · exact absurd hxF X.e2_not_mem_F
      · exact Or.inr (Or.inl rfl)
      · exact absurd hxF X.e4_not_mem_F
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
  rw [X.ncard_inf_F]
  have hne : ∀ i, (1 : G) ≠ X.e i := fun i h => X.e_ne_one i h.symm
  rw [Set.ncard_insert_of_notMem (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hne 3, hne 5, hne 6⟩),
    Set.ncard_insert_of_notMem (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨X.e_ne (by norm_num) (by norm_num), X.e_ne (by norm_num) (by norm_num)⟩),
    Set.ncard_pair (X.e_ne (by norm_num) (by norm_num))]

theorem e3_mem_F : X.e 3 ∈ X.F := by
  have : X.e 3 ∈ (((X.S : Subgroup G) ⊓ X.F : Subgroup G) : Set G) := by
    rw [X.inf_F_eq]; simp
  exact this.2

theorem e5_mem_F : X.e 5 ∈ X.F := by
  have : X.e 5 ∈ (((X.S : Subgroup G) ⊓ X.F : Subgroup G) : Set G) := by
    rw [X.inf_F_eq]; simp
  exact this.2

theorem e6_mem_F : X.e 6 ∈ X.F := by
  have : X.e 6 ∈ (((X.S : Subgroup G) ⊓ X.F : Subgroup G) : Set G) := by
    rw [X.inf_F_eq]; simp
  exact this.2

end Setup

end CFSG.Walter.J1Recog
