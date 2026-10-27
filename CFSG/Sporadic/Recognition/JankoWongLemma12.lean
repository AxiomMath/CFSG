module

public import CFSG.Sporadic.Recognition.JankoWongLemma9
public import CFSG.Sporadic.Recognition.JankoWongKleinOrder
public import CFSG.Sporadic.Recognition.JankoWongKleinSylow

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup CFSG.GH74 CFSG.GH74.GLS

theorem permT_comm_decomp : ∀ i j : Fin 3,
    permT * (permA3 ^ (i : ℕ) * permB3 ^ (j : ℕ)) = (permA3 ^ (i : ℕ) * permB3 ^ (j : ℕ)) * permT →
      i = j := by
  unfold permT permA3 permB3; decide

theorem permT_conj_permA3 : permT * permA3 * permT⁻¹ = permB3 := by
  unfold permT permA3 permB3; decide

theorem permT_conj_permB3 : permT * permB3 * permT⁻¹ = permA3 := by
  unfold permT permA3 permB3; decide

namespace Setup

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {S : Setup G} (c : Ctx S)

theorem d_conj_t : (c.d : G) * (c.t : G) * (c.d : G)⁻¹ = S.z * (c.t : G) := by
  have h : ((c.d : G) * c.t) * ((c.d : G) * c.t) = S.z := by
    have := congrArg Subtype.val c.hdt
    simp only [pow_two, Subgroup.coe_mul] at this
    exact this
  have hdinv : (c.d : G)⁻¹ = c.d := inv_eq_of_mul_eq_one_right c.dG_sq
  have htinv : (c.t : G)⁻¹ = c.t := inv_eq_of_mul_eq_one_right c.tG_sq
  calc (c.d : G) * c.t * (c.d : G)⁻¹ = ((c.d : G) * c.t) * c.d := by rw [hdinv]
    _ = (((c.d : G) * c.t) * ((c.d : G) * c.t)) * (c.t : G)⁻¹ := by group
    _ = S.z * (c.t : G)⁻¹ := by rw [h]
    _ = S.z * c.t := by rw [htinv]

@[expose] def CO (v : G) : Subgroup G := c.OG ⊓ centralizer ({v} : Set G)

theorem card_CO_dvd_nine {v : G} (hv : v ^ 2 = 1) (hv1 : v ≠ 1) (hvs : v * c.s = c.s * v) :
    3 ∣ Nat.card (c.CO v) ∧ Nat.card (c.CO v) ∣ 9 := by
  have h36 := S.card_inf_centralizer_involution c.x_cube c.x_type hv hv1 hvs
  have hle : c.CO v ≤ centralizer ({(c.x : G)} : Set G) ⊓ centralizer ({v} : Set G) :=
    inf_le_inf c.OG_le_Cg le_rfl
  have hdvd36 : Nat.card (c.CO v) ∣ 36 := h36 ▸ Subgroup.card_dvd_of_le hle
  have hp : IsPGroup 3 (c.CO v) := c.isPGroup_three_OG.to_le inf_le_left
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  refine ⟨?_, ?_⟩
  · have hz : zpowers c.s ≤ c.CO v := by
      rw [Subgroup.zpowers_le]
      exact ⟨c.zpowers_le_OG (Subgroup.mem_zpowers c.s),
        Subgroup.mem_centralizer_singleton_iff.mpr hvs.symm⟩
    have := Subgroup.card_dvd_of_le hz
    rwa [Nat.card_zpowers, c.orderOf_s] at this
  · rw [hk] at hdvd36 ⊢
    have h4 : (3 ^ k).Coprime 4 := Nat.Coprime.pow_left k (by norm_num)
    exact h4.dvd_of_dvd_mul_left (by simpa using hdvd36)

theorem card_CO_conj {g : G} (hg : g ∈ c.Ng) (v : G) :
    Nat.card (c.CO (g * v * g⁻¹)) = Nat.card (c.CO v) := by
  refine Nat.card_congr
    { toFun := fun y => ⟨g⁻¹ * y.1 * g, ?_⟩
      invFun := fun y => ⟨g * y.1 * g⁻¹, ?_⟩
      left_inv := fun y => by apply Subtype.ext; show g * (g⁻¹ * y.1 * g) * g⁻¹ = y.1; group
      right_inv := fun y => by apply Subtype.ext; show g⁻¹ * (g * y.1 * g⁻¹) * g = y.1; group }
  · obtain ⟨y, hyO, hyv⟩ := y
    have hyv' := Subgroup.mem_centralizer_singleton_iff.mp hyv
    refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    · have := c.OG_normalized g⁻¹ ((c.Ng).inv_mem hg) y hyO
      simpa using this
    · calc g⁻¹ * y * g * v = g⁻¹ * (y * (g * v * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * v * g⁻¹) * y) * g := by rw [hyv']
        _ = v * (g⁻¹ * y * g) := by group
  · obtain ⟨y, hyO, hyv⟩ := y
    have hyv' := Subgroup.mem_centralizer_singleton_iff.mp hyv
    refine ⟨c.OG_normalized g hg y hyO, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc g * y * g⁻¹ * (g * v * g⁻¹) = g * (y * v) * g⁻¹ := by group
      _ = g * (v * y) * g⁻¹ := by rw [hyv']
      _ = (g * v * g⁻¹) * (g * y * g⁻¹) := by group

theorem t_conj_a : c.t * c.a * c.t⁻¹ = c.b := by
  have h3 : (c.t * c.a * c.t⁻¹) ^ 3 = 1 := by
    have : (c.t * c.a * c.t⁻¹) ^ 3 = c.t * c.a ^ 3 * c.t⁻¹ := by simp [pow_succ, mul_assoc]
    rw [this, c.ha3]; simp
  refine S.cover.eq_of_cube_one h3 c.hb3 ?_
  rw [map_mul, map_mul, map_inv, c.ht, c.ha, c.hb]
  exact permT_conj_permA3

theorem t_conj_b : c.t * c.b * c.t⁻¹ = c.a := by
  have h3 : (c.t * c.b * c.t⁻¹) ^ 3 = 1 := by
    have : (c.t * c.b * c.t⁻¹) ^ 3 = c.t * c.b ^ 3 * c.t⁻¹ := by simp [pow_succ, mul_assoc]
    rw [this, c.hb3]; simp
  refine S.cover.eq_of_cube_one h3 c.ha3 ?_
  rw [map_mul, map_mul, map_inv, c.ht, c.ha, c.hb]
  exact permT_conj_permB3

theorem t_normalizes_P : ∀ p ∈ c.P, c.t * p * c.t⁻¹ ∈ c.P := by
  intro p hp
  obtain ⟨i, j, -, -, rfl⟩ := Ctx.P_decomp c p hp
  have : c.t * (c.a ^ i * c.b ^ j) * c.t⁻¹ = c.b ^ i * c.a ^ j := by
    calc c.t * (c.a ^ i * c.b ^ j) * c.t⁻¹
        = (c.t * c.a * c.t⁻¹) ^ i * (c.t * c.b * c.t⁻¹) ^ j := by
          rw [conj_pow, conj_pow]; group
      _ = c.b ^ i * c.a ^ j := by rw [c.t_conj_a, c.t_conj_b]
  rw [this]
  exact c.P.mul_mem (c.P.pow_mem c.hbP i) (c.P.pow_mem c.haP j)

theorem P_comm_x {p : S.H} (hp : p ∈ c.P) : p * c.x = c.x * p := by
  have hcomm := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := c.P) (by
    rw [c.hP9]; norm_num)
  have hxP : c.x ∈ c.P := c.P.mul_mem c.haP c.hbP
  have := hcomm.is_comm.comm ⟨p, hp⟩ ⟨c.x, hxP⟩
  exact congrArg (fun w : c.P => (w : S.H)) this

theorem mem_P_of_three_power {y : S.H} (hy : y * c.x = c.x * y) {n : ℕ} (hn : y ^ (3 ^ n) = 1) :
    y ∈ c.P := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C₀ : Subgroup S.H := centralizer ({c.x} : Set S.H) with hC₀
  have hcard : Nat.card C₀ = 36 := S.cover.card_centralizer_type33 c.x_cube c.x_type
  have hPC : c.P ≤ C₀ := fun p hp => Subgroup.mem_centralizer_singleton_iff.mpr (c.P_comm_x hp)
  set P' : Subgroup ↥C₀ := c.P.subgroupOf C₀ with hP'
  have hP'card : Nat.card P' = 9 := by
    rw [hP', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPC).toEquiv, c.hP9]
  have hP'p : IsPGroup 3 P' := c.hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPC).symm
  obtain ⟨Q, hQ⟩ := hP'p.exists_le_sylow
  have hQcard : Nat.card Q = 9 := by
    rw [Q.card_eq_multiplicity, hcard]
    have : (36 : ℕ) = 3 ^ 2 * 4 := by norm_num
    rw [this, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three]
    have h4 : (4 : ℕ).factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
    simp [h4]
  have hPQ : P' = (Q : Subgroup ↥C₀) :=
    Subgroup.eq_of_le_of_card_ge hQ (by rw [hQcard, hP'card])
  let t' : ↥C₀ := ⟨c.t, Subgroup.mem_centralizer_singleton_iff.mpr c.htx⟩
  have ht'N : t' ∈ Subgroup.normalizer (P' : Set ↥C₀) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact Subgroup.mem_subgroupOf.mpr (by
        have := c.t_normalizes_P h.1 (Subgroup.mem_subgroupOf.mp hh)
        exact this)
    · intro hh
      have h1 := Subgroup.mem_subgroupOf.mp hh
      have h2 := c.t_normalizes_P (c.t * h.1 * c.t⁻¹) h1
      have h3 : c.t * (c.t * h.1 * c.t⁻¹) * c.t⁻¹ = h.1 := by
        have : c.t * c.t = 1 := by rw [← pow_two]; exact c.ht2
        calc c.t * (c.t * h.1 * c.t⁻¹) * c.t⁻¹ = (c.t * c.t) * h.1 * (c.t * c.t)⁻¹ := by group
          _ = h.1 := by rw [this]; group
      rw [h3] at h2
      exact Subgroup.mem_subgroupOf.mpr h2
  have ht'2 : orderOf t' = 2 := by
    have h2 : t' ^ 2 = 1 := Subtype.ext (by simpa using c.ht2)
    have h1 : t' ≠ 1 := fun e => c.t_ne_one (congrArg Subtype.val e)
    exact orderOf_eq_prime h2 h1
  have h2N : 2 ∣ Nat.card (Subgroup.normalizer (P' : Set ↥C₀)) := by
    have := orderOf_dvd_natCard (⟨t', ht'N⟩ : Subgroup.normalizer (P' : Set ↥C₀))
    rwa [Subgroup.orderOf_mk, ht'2] at this
  have h9N : 9 ∣ Nat.card (Subgroup.normalizer (P' : Set ↥C₀)) := by
    rw [← hP'card]; exact Subgroup.card_dvd_of_le Subgroup.le_normalizer
  have hNdvd : Nat.card (Subgroup.normalizer (P' : Set ↥C₀)) ∣ 36 := by
    rw [← Nat.card_congr (Equiv.refl _)]
    have := Subgroup.card_subgroup_dvd_card (Subgroup.normalizer (P' : Set ↥C₀))
    rwa [Nat.card_congr (Equiv.refl _), hcard] at this
  have hindex : (Subgroup.normalizer (P' : Set ↥C₀)).index = 1 ∨
      (Subgroup.normalizer (P' : Set ↥C₀)).index = 2 := by
    have h1 := Subgroup.index_mul_card (Subgroup.normalizer (P' : Set ↥C₀))
    rw [hcard] at h1
    have h18 : 18 ∣ Nat.card (Subgroup.normalizer (P' : Set ↥C₀)) := by
      obtain ⟨a₂, ha₂⟩ := h2N
      obtain ⟨a₉, ha₉⟩ := h9N
      omega
    have hpos : 0 < Nat.card (Subgroup.normalizer (P' : Set ↥C₀)) := Nat.card_pos
    have hle : 18 ≤ Nat.card (Subgroup.normalizer (P' : Set ↥C₀)) := Nat.le_of_dvd hpos h18
    have hidxpos : 0 < (Subgroup.normalizer (P' : Set ↥C₀)).index := by
      rcases Nat.eq_zero_or_pos (Subgroup.normalizer (P' : Set ↥C₀)).index with h | h
      · rw [h] at h1; omega
      · exact h
    have : (Subgroup.normalizer (P' : Set ↥C₀)).index ≤ 2 := by
      by_contra hlt
      push Not at hlt
      nlinarith
    omega
  have hidx : Nat.card (Sylow 3 ↥C₀) = (Subgroup.normalizer (P' : Set ↥C₀)).index := by
    rw [Sylow.card_eq_index_normalizer Q]
    exact congrArg (fun H : Subgroup ↥C₀ => (Subgroup.normalizer (H : Set ↥C₀)).index) hPQ.symm
  have hn1 : Nat.card (Sylow 3 ↥C₀) = 1 := by
    have hmod := card_sylow_modEq_one 3 ↥C₀
    unfold Nat.ModEq at hmod
    rw [hidx] at hmod ⊢
    omega
  have hsub : Subsingleton (Sylow 3 ↥C₀) := (Nat.card_eq_one_iff_unique.mp hn1).1
  let y' : ↥C₀ := ⟨y, Subgroup.mem_centralizer_singleton_iff.mpr hy⟩
  have hy'p : IsPGroup 3 (zpowers y') := by
    have h1 : y' ^ (3 ^ n) = 1 := Subtype.ext (by simpa using hn)
    have hd := orderOf_dvd_of_pow_eq_one h1
    obtain ⟨m, -, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers]; exact hm')
  obtain ⟨Q', hQ'⟩ := hy'p.exists_le_sylow
  have hy'Q : y' ∈ (Q' : Subgroup ↥C₀) := hQ' (Subgroup.mem_zpowers y')
  rw [Subsingleton.elim Q' Q, ← hPQ] at hy'Q
  exact Subgroup.mem_subgroupOf.mp hy'Q

theorem mem_zpowers_s_of_commute {y : G} (hy : y ∈ c.OG) (hz : y * S.z = S.z * y)
    (ht : y * (c.t : G) = (c.t : G) * y) : y ∈ zpowers c.s := by
  have hyC : y ∈ c.Cg := c.OG_le_Cg hy
  have hys : y * c.s = c.s * y := Subgroup.mem_centralizer_singleton_iff.mp hyC
  have hyH : y ∈ S.H := Subgroup.mem_centralizer_singleton_iff.mpr hz
  have hyHx : (⟨y, hyH⟩ : S.H) * c.x = c.x * (⟨y, hyH⟩ : S.H) := Subtype.ext hys
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (⟨y, hyH⟩ : S.H) ^ (3 ^ n) = 1 := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp c.isPGroup_three_OG ⟨y, hy⟩
    refine ⟨n, ?_⟩
    have h1 : (⟨y, hy⟩ : c.OG) ^ (3 ^ n) = 1 := by rw [← hn]; exact pow_orderOf_eq_one _
    apply Subtype.ext
    have := congrArg (fun w : c.OG => (w : G)) h1
    simpa using this
  have hP := c.mem_P_of_three_power hyHx hn
  obtain ⟨i, j, hi, hj, hyij⟩ := Ctx.P_decomp c _ hP
  have htH : c.t * (⟨y, hyH⟩ : S.H) = (⟨y, hyH⟩ : S.H) * c.t := Subtype.ext ht.symm
  have hρ : S.ρ c.t * S.ρ (⟨y, hyH⟩ : S.H) = S.ρ (⟨y, hyH⟩ : S.H) * S.ρ c.t := by
    rw [← map_mul, ← map_mul, htH]
  rw [hyij, map_mul, map_pow, map_pow, c.ha, c.hb, c.ht] at hρ
  have hij : (⟨i, hi⟩ : Fin 3) = ⟨j, hj⟩ := permT_comm_decomp ⟨i, hi⟩ ⟨j, hj⟩ hρ
  have hij' : i = j := congrArg Fin.val hij
  subst hij'
  have hyx : (⟨y, hyH⟩ : S.H) = c.x ^ i := by
    rw [hyij]; unfold Ctx.x; rw [Commute.mul_pow c.hab]
  refine Subgroup.mem_zpowers_iff.mpr ⟨(i : ℤ), ?_⟩
  have := congrArg Subtype.val hyx
  simpa [Ctx.s] using this.symm

theorem card_OG_mul_nine :
    9 * Nat.card c.OG = Nat.card (c.CO S.z) * Nat.card (c.CO (c.t : G)) *
      Nat.card (c.CO (S.z * (c.t : G))) := by
  have hz2 : S.z ^ 2 = 1 := by rw [← S.order_z]; exact pow_orderOf_eq_one S.z
  have ht2 : (c.t : G) ^ 2 = 1 := by
    have := congrArg Subtype.val c.ht2
    simpa using this
  have htC : (c.t : G) ∈ c.Cg := c.mem_cg_iff.mpr (by
    have := c.t_comm_s
    calc (c.t : G) * c.s * (c.t : G)⁻¹ = c.s * (c.t : G) * (c.t : G)⁻¹ := by rw [this]
      _ = c.s := by group)
  have hscomm : ∀ y ∈ c.OG, c.s * y = y * c.s := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.mp (c.OG_le_Cg hy)).symm
  have h := card_mul_sq_eq_prod_centralizers_of_klein (C := G) (A := c.OG) (Z := zpowers c.s)
    c.isPGroup_three_OG hz2 ht2 c.t_comm_z.symm
    (fun y hy => c.OG_normalized S.z (c.cg_le_ng c.z_mem_cg) y hy)
    (fun y hy => c.OG_normalized (c.t : G) (c.cg_le_ng htC) y hy)
    c.zpowers_le_OG
    (fun z' hz' y hy => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz'
      exact (Commute.zpow_left (show Commute c.s y from hscomm y hy) k).eq)
    (fun z' hz' => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz'
      exact ⟨(Commute.zpow_right (show Commute S.z c.s from c.z_comm_s) k).eq,
        (Commute.zpow_right (show Commute (c.t : G) c.s from c.t_comm_s) k).eq⟩)
    (fun y hy h1 h2 => c.mem_zpowers_s_of_commute hy h1.symm h2.symm)
  rw [Nat.card_zpowers, c.orderOf_s] at h
  unfold CO
  omega

theorem conj_mem_Cg {g y : G} (hg : g ∈ c.Ng) (hy : y ∈ c.Cg) : g * y * g⁻¹ ∈ c.Cg := by
  have hn : (c.Cg.subgroupOf c.Ng).Normal := Subgroup.normal_of_index_eq_two c.index_two
  have := hn.conj_mem ⟨y, c.cg_le_ng hy⟩ (Subgroup.mem_subgroupOf.mpr hy) ⟨g, hg⟩
  exact Subgroup.mem_subgroupOf.mp this

theorem card_Cg_factorization_two : (Nat.card c.Cg).factorization 2 = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T'⟩ : Nonempty (Sylow 2 ↥c.Cg) := inferInstance
  have h4 : Nat.card T' = 4 := S.card_sylow_centralizer_type33 c.x_cube c.x_type T'
  rw [T'.card_eq_multiplicity] at h4
  have : (2 : ℕ) ^ ((Nat.card c.Cg).factorization 2) = 2 ^ 2 := by rw [h4]; norm_num
  exact Nat.pow_right_injective (le_refl 2) this

theorem z_sq : S.z ^ 2 = 1 := by rw [← S.order_z]; exact pow_orderOf_eq_one S.z

theorem z_ne_one' : S.z ≠ 1 := fun e => S.cover.ne_one (Subtype.ext e)

theorem tG_sq' : (c.t : G) ^ 2 = 1 := by
  have := congrArg Subtype.val c.ht2
  simpa using this

theorem tG_ne_one : (c.t : G) ≠ 1 := fun e => c.t_ne_one (Subtype.ext e)

theorem tC_mem : (c.t : G) ∈ c.Cg := c.mem_cg_iff.mpr (by
  have := c.t_comm_s
  calc (c.t : G) * c.s * (c.t : G)⁻¹ = c.s * (c.t : G) * (c.t : G)⁻¹ := by rw [this]
    _ = c.s := by group)

theorem card_CO_z : 3 ∣ Nat.card (c.CO S.z) ∧ Nat.card (c.CO S.z) ∣ 9 :=
  c.card_CO_dvd_nine (z_sq (S := S)) (z_ne_one' (S := S)) c.z_comm_s

theorem card_CO_t : 3 ∣ Nat.card (c.CO (c.t : G)) ∧ Nat.card (c.CO (c.t : G)) ∣ 9 :=
  c.card_CO_dvd_nine c.tG_sq' c.tG_ne_one c.t_comm_s

theorem card_CO_zt : Nat.card (c.CO (S.z * (c.t : G))) = Nat.card (c.CO (c.t : G)) := by
  rw [← c.d_conj_t]
  exact c.card_CO_conj c.d_mem_ng (c.t : G)

theorem card_OG_mul_nine' :
    9 * Nat.card c.OG = Nat.card (c.CO S.z) * Nat.card (c.CO (c.t : G)) ^ 2 := by
  rw [c.card_OG_mul_nine, c.card_CO_zt]; ring

theorem eq_three_or_nine {m : ℕ} (h3 : 3 ∣ m) (h9 : m ∣ 9) : m = 3 ∨ m = 9 := by
  have : m ≤ 9 := Nat.le_of_dvd (by norm_num) h9
  interval_cases m <;> simp_all

theorem le_OG_of_odd_normal {W : Subgroup G} (hWN : W ≤ c.Ng)
    (hn : ∀ g ∈ c.Ng, ∀ y ∈ W, g * y * g⁻¹ ∈ W) (hodd : Odd (Nat.card W)) : W ≤ c.OG := by
  have hnormN : (W.subgroupOf c.Ng).Normal := by
    refine ⟨fun n hn' g => ?_⟩
    exact Subgroup.mem_subgroupOf.mpr (hn g g.2 n (Subgroup.mem_subgroupOf.mp hn'))
  have hoddN : Odd (Nat.card (W.subgroupOf c.Ng)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWN).toEquiv]; exact hodd
  have hle : W.subgroupOf c.Ng ≤ CFSG.oddCore ↥c.Ng := by
    unfold CFSG.oddCore
    exact le_sSup ⟨hnormN, hoddN⟩
  intro y hy
  have : (⟨y, hWN hy⟩ : ↥c.Ng) ∈ CFSG.oddCore ↥c.Ng := hle (Subgroup.mem_subgroupOf.mpr hy)
  exact ⟨_, this, rfl⟩

theorem exists_odd_complement (hN : CFSG.HasNormalPComplement 2 ↥c.Cg) :
    ∃ XG : Subgroup G, XG ≤ c.OG ∧ Odd (Nat.card XG) ∧ Nat.card c.Cg = 4 * Nat.card XG ∧
      ∀ w ∈ c.Cg, Odd (orderOf w) → w ∈ XG := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨X, hXn, hXcop, hXq⟩ := hN
  have hXodd : Odd (Nat.card X) := Nat.coprime_two_left.mp hXcop
  set XG : Subgroup G := X.map c.Cg.subtype with hXG
  have hXGcard : Nat.card XG = Nat.card X := Subgroup.card_map_of_injective c.Cg.subtype_injective
  have hodd_mem : ∀ w ∈ c.Cg, Odd (orderOf w) → w ∈ XG := by
    intro w hw hw_odd
    let w' : ↥c.Cg := ⟨w, hw⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hXq (QuotientGroup.mk w')
    have hdvd : orderOf (QuotientGroup.mk w' : ↥c.Cg ⧸ X) ∣ orderOf w' :=
      orderOf_map_dvd (QuotientGroup.mk' X) w'
    have hw'ord : orderOf w' = orderOf w := (Subgroup.orderOf_coe w').symm
    rw [hk, hw'ord] at hdvd
    have hk0 : k = 0 := by
      by_contra hk0
      have h2 : 2 ∣ orderOf w := (dvd_pow_self 2 hk0).trans hdvd
      exact (Nat.not_even_iff_odd.mpr hw_odd) (even_iff_two_dvd.mpr h2)
    rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
    have : w' ∈ X := (QuotientGroup.eq_one_iff w').mp hk
    exact ⟨w', this, rfl⟩
  have hXGodd : ∀ y ∈ XG, Odd (orderOf y) := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 : orderOf (⟨y, hy⟩ : X) ∣ Nat.card X := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    show Odd (orderOf (y : G))
    rw [Subgroup.orderOf_coe]
    exact Odd.of_dvd_nat hXodd h1
  have hXGnorm : ∀ g ∈ c.Ng, ∀ y ∈ XG, g * y * g⁻¹ ∈ XG := by
    intro g hg y hy
    have hyC : y ∈ c.Cg := by obtain ⟨y', -, rfl⟩ := hy; exact y'.2
    refine hodd_mem _ (c.conj_mem_Cg hg hyC) ?_
    have := hXGodd y hy
    have hc : orderOf (g * y * g⁻¹) = orderOf y := by
      have h := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y
      exact h
    rw [hc]; exact this
  have hXGle : XG ≤ c.Ng := fun y hy => c.cg_le_ng (by obtain ⟨y', -, rfl⟩ := hy; exact y'.2)
  have hXGO : XG ≤ c.OG := c.le_OG_of_odd_normal hXGle hXGnorm (by rw [hXGcard]; exact hXodd)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hXq
  have hCcard : Nat.card c.Cg = 2 ^ k * Nat.card X := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup X, hk]
  have hk2 : k = 2 := by
    have hf := c.card_Cg_factorization_two
    rw [hCcard, Nat.factorization_mul (by positivity) Nat.card_pos.ne', Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two] at hf
    have h0 : (Nat.card X).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (fun h =>
        (Nat.not_even_iff_odd.mpr hXodd) (even_iff_two_dvd.mpr h))
    simp [h0] at hf
    exact hf
  refine ⟨XG, hXGO, by rw [hXGcard]; exact hXodd, ?_, hodd_mem⟩
  rw [hXGcard, hCcard, hk2]
  norm_num

theorem card_OG_eq_81_of_hasNormalPComplement (h27 : 27 ∣ Nat.card c.Cg)
    (hN : CFSG.HasNormalPComplement 2 ↥c.Cg) : Nat.card c.OG = 81 := by
  obtain ⟨XG, hXGO, -, hCcard, hodd_mem⟩ := c.exists_odd_complement hN
  have h27X : 27 ∣ Nat.card XG := by
    rw [hCcard] at h27
    have hc : Nat.Coprime 27 4 := by norm_num
    exact hc.dvd_of_dvd_mul_left h27
  have h27O : 27 ∣ Nat.card c.OG := h27X.trans (Subgroup.card_dvd_of_le hXGO)
  set PG : Subgroup G := c.P.map S.H.subtype with hPG
  have hPGp : IsPGroup 3 PG := c.hP.map _
  have hPGO : PG ≤ c.OG := by
    intro y hy
    apply hXGO
    have hyC : y ∈ c.Cg := by
      obtain ⟨p, hp, rfl⟩ := hy
      exact c.mem_cg_iff.mpr (by
        have := congrArg (fun w : S.H => (w : G)) (c.P_comm_x hp)
        have h1 : (p : G) * c.s = c.s * (p : G) := this
        calc (p : G) * c.s * (p : G)⁻¹ = c.s * (p : G) * (p : G)⁻¹ := by rw [h1]
          _ = c.s := by group)
    refine hodd_mem y hyC ?_
    obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.mp hPGp ⟨y, hy⟩
    have : orderOf y = 3 ^ m := by rw [← hm, ← Subgroup.orderOf_coe]
    rw [this]
    exact Odd.pow (by decide)
  have hPG9 : Nat.card PG = 9 := by
    rw [hPG, Subgroup.card_map_of_injective S.H.subtype_injective, c.hP9]
  have hPGz : PG ≤ c.CO S.z := by
    refine le_inf hPGO ?_
    rintro _ ⟨p, hp, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp
      p.2)
  have ha₁ : Nat.card (c.CO S.z) = 9 := by
    have h9 : 9 ∣ Nat.card (c.CO S.z) := by
      rw [← hPG9]; exact Subgroup.card_dvd_of_le hPGz
    exact Nat.dvd_antisymm c.card_CO_z.2 h9
  have hb := eq_three_or_nine c.card_CO_t.1 c.card_CO_t.2
  have hmul := c.card_OG_mul_nine'
  rw [ha₁] at hmul
  rcases hb with hb | hb
  · exfalso
    rw [hb] at hmul
    have : Nat.card c.OG = 9 := by omega
    rw [this] at h27O
    omega
  · rw [hb] at hmul
    omega

theorem exists_conj_z_of_not_hasNormalPComplement (hN : ¬ CFSG.HasNormalPComplement 2 ↥c.Cg) :
    ∃ x : ↥c.Cg, (x : G) * S.z * (x : G)⁻¹ = (c.t : G) ∨
      (x : G) * S.z * (x : G)⁻¹ = S.z * (c.t : G) := by
  let zC : ↥c.Cg := ⟨S.z, c.z_mem_cg⟩
  let tC : ↥c.Cg := ⟨(c.t : G), c.tC_mem⟩
  have hz2 : zC ^ 2 = 1 := Subtype.ext (by simpa [zC] using z_sq (S := S))
  have ht2 : tC ^ 2 = 1 := Subtype.ext (by simpa [tC] using c.tG_sq')
  have hzt : zC * tC = tC * zC := Subtype.ext c.t_comm_z.symm
  have hz1 : zC ≠ 1 := fun e => z_ne_one' (S := S) (congrArg Subtype.val e)
  have ht1 : tC ≠ 1 := fun e => c.tG_ne_one (congrArg Subtype.val e)
  have hne : zC ≠ tC := fun e => c.t_ne_z (Subtype.ext (congrArg Subtype.val e).symm)
  have h4 : 2 ^ 2 ∣ Nat.card c.Cg ∧ ¬ 2 ^ 3 ∣ Nat.card c.Cg := by
    have hf := c.card_Cg_factorization_two
    have hne0 : Nat.card c.Cg ≠ 0 := Nat.card_pos.ne'
    constructor
    · exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne0).mpr (by omega)
    · intro h
      have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne0).mp h
      omega
  obtain ⟨x, hx⟩ := exists_conj_of_not_hasNormalPComplement hz2 ht2 hzt hz1 ht1 hne h4 hN
  refine ⟨x, ?_⟩
  rcases hx with hx | hx
  · exact Or.inl (congrArg Subtype.val hx)
  · exact Or.inr (congrArg Subtype.val hx)

theorem card_OG_eq_81_of_not_hasNormalPComplement
    (hN : ¬ CFSG.HasNormalPComplement 2 ↥c.Cg) : Nat.card c.OG = 81 := by
  obtain ⟨x, hx⟩ := c.exists_conj_z_of_not_hasNormalPComplement hN
  have hxg : (x : G) ∈ c.Ng := c.cg_le_ng x.2
  have hconj := c.card_CO_conj hxg S.z
  have hCO : Nat.card (c.CO S.z) = Nat.card (c.CO (c.t : G)) := by
    rcases hx with hx | hx
    · rw [hx] at hconj
      exact hconj.symm
    · rw [hx, c.card_CO_zt] at hconj
      exact hconj.symm
  have hmul := c.card_OG_mul_nine'
  rw [← hCO] at hmul
  rcases eq_three_or_nine c.card_CO_z.1 c.card_CO_z.2 with h3 | h9
  · exfalso
    rw [h3] at hmul
    exact c.false_of_card_OG_eq_three (by omega) hN
  · rw [h9] at hmul
    omega

theorem card_OG_eq_81 :
    Nat.card c.OG = 81 := by
  have h27 := S.twentySeven_dvd_card
  by_cases hN : CFSG.HasNormalPComplement 2 ↥c.Cg
  · exact c.card_OG_eq_81_of_hasNormalPComplement (c.twentySeven_dvd_card_Cg h27) hN
  · exact c.card_OG_eq_81_of_not_hasNormalPComplement hN

end Ctx



end Setup

end CFSG.Sporadic.Recognition.JankoWong
