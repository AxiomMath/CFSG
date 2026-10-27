module

public import CFSG.Monster.B.Pinned.Primes.Extraspecial
public import CFSG.RankThree.CentralExtension.ScalarNormalizerKernel

public section

namespace CFSG.RankThree.PartOne.KS.ScalFive

open Subgroup CFSG.Monster.B.Pinned CFSG.RankThree.CentralExtension
open scoped Matrix

theorem fact5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

variable {G : Type*} [Group G] {n : ℕ}

abbrev QG (q : Fin n → G) : Subgroup G := closure (Set.range q)

@[expose] def HG (q : Fin n → G) (s t : G) : Subgroup G :=
  closure ((QG q : Set G) ∪ {s} ∪ {t})

theorem q_mem {q : Fin n → G} (i : Fin n) : q i ∈ QG q := subset_closure ⟨i, rfl⟩

theorem Q_le_H {q : Fin n → G} {s t : G} : QG q ≤ HG q s t := fun _ hg =>
  subset_closure (Or.inl (Or.inl hg))

theorem s_mem_H {q : Fin n → G} {s t : G} : s ∈ HG q s t :=
  subset_closure (Or.inl (Or.inr rfl))

theorem t_mem_H {q : Fin n → G} {s t : G} : t ∈ HG q s t := subset_closure (Or.inr rfl)

theorem prod_mem_of_mem_z {q : Fin n → G} {z : G} (hz : z ∈ QG q) (a : Fin n → ℕ) (c : ℕ) :
    (List.ofFn fun j => q j ^ a j).prod * z ^ c ∈ QG q := by
  refine mul_mem (list_prod_mem fun g hg => ?_) (pow_mem hz _)
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hg
  exact pow_mem (q_mem j) _

structure ScalRel (q : Fin n → G) (z s t : G) (M Sm : Matrix (Fin n) (Fin n) (ZMod 5))
    (i₀ j₀ : Fin n) (cs : Fin n → ℕ) (r : ZMod 5) (ct : Fin n → ℕ) : Prop where
  commData : CommData 5 q z M
  z_eq : bcomm (q i₀) (q j₀) = z
  conj_s : ∀ i, s⁻¹ * q i * s =
    (List.ofFn fun j => q j ^ (Sm i j).val).prod * z ^ cs i
  conj_t : ∀ i, t⁻¹ * q i * t = q i ^ r.val * z ^ ct i
  s_pow : s ^ 5 ∈ QG q
  t_pow : t ^ 4 = 1
  ts_mem : t⁻¹ * s⁻¹ * t * s ∈ QG q

theorem bcomm_map {G' : Type*} [Group G'] (ι : G →* G') (a b : G) :
    ι (bcomm a b) = bcomm (ι a) (ι b) := by
  simp only [bcomm, map_mul, map_inv]

theorem mem_QG_of_injective {G' : Type*} [Group G'] (ι : G →* G') (hι : Function.Injective ι)
    {q : Fin n → G} {x : G} (hx : ι x ∈ QG (fun j => ι (q j))) : x ∈ QG q := by
  have h : QG (fun j => ι (q j)) = (QG q).map ι := by
    simp only [QG, MonoidHom.map_closure, ← Set.range_comp]
    rfl
  rw [h] at hx
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
  exact hι hyx ▸ hy

theorem ScalRel.of_injective {G' : Type*} [Group G'] (ι : G →* G') (hι : Function.Injective ι)
    {q : Fin n → G} {z s t : G} {M Sm : Matrix (Fin n) (Fin n) (ZMod 5)} {i₀ j₀ : Fin n}
    {cs : Fin n → ℕ} {r : ZMod 5} {ct : Fin n → ℕ}
    (h : ScalRel (fun j => ι (q j)) (ι z) (ι s) (ι t) M Sm i₀ j₀ cs r ct) :
    ScalRel q z s t M Sm i₀ j₀ cs r ct := by
  have hz_eq : bcomm (q i₀) (q j₀) = z := hι (by rw [bcomm_map]; exact h.z_eq)
  refine ⟨⟨fun i => hι (by rw [map_pow, map_one]; exact h.commData.pow_q i),
    (orderOf_injective ι hι z).symm.trans h.commData.orderOf_z,
    fun i => hι (by rw [map_mul, map_mul]; exact h.commData.comm_z i),
    fun i j => hι (by rw [map_pow, bcomm_map]; exact h.commData.bcomm_q i j),
    h.commData.isUnit_det, ?_⟩, hz_eq,
    fun i => hι (by
      have := h.conj_s i
      simp only [map_mul, map_inv, map_pow, map_list_prod, List.map_ofFn, Function.comp_def]
      exact this),
    fun i => hι (by
      have := h.conj_t i
      simp only [map_mul, map_inv, map_pow]
      exact this),
    mem_QG_of_injective ι hι (by rw [map_pow]; exact h.s_pow),
    hι (by rw [map_pow, map_one]; exact h.t_pow),
    mem_QG_of_injective ι hι (by simp only [map_mul, map_inv]; exact h.ts_mem)⟩
  rw [← hz_eq]
  unfold bcomm
  exact mul_mem (mul_mem (mul_mem (inv_mem (subset_closure ⟨i₀, rfl⟩))
    (inv_mem (subset_closure ⟨j₀, rfl⟩))) (subset_closure ⟨i₀, rfl⟩)) (subset_closure ⟨j₀, rfl⟩)

theorem mul_pow_class_two {a b c : G}
    (hc : b * a = a * b * c) (hca : Commute c a) (hcb : Commute c b) (m : ℕ) :
    (a * b) ^ m = a ^ m * b ^ m * c ^ m.choose 2 := by
  have hbk : ∀ k : ℕ, b ^ k * a = a * b ^ k * c ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc b ^ (k + 1) * a = b * (b ^ k * a) := by rw [pow_succ', mul_assoc]
        _ = b * (a * b ^ k * c ^ k) := by rw [ih]
        _ = (b * a) * b ^ k * c ^ k := by group
        _ = a * b * c * b ^ k * c ^ k := by rw [hc]
        _ = a * b * (c * b ^ k) * c ^ k := by group
        _ = a * b * (b ^ k * c) * c ^ k := by rw [(hcb.pow_right k).eq]
        _ = a * b ^ (k + 1) * c ^ (k + 1) := by rw [pow_succ' b k, pow_succ' c k]; group
  induction m with
  | zero => simp
  | succ m ih =>
    have hT : (m + 1).choose 2 = m + m.choose 2 := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
    have e1 : c ^ m.choose 2 * a = a * c ^ m.choose 2 := (hca.pow_left _).eq
    have e2 : c ^ m.choose 2 * b = b * c ^ m.choose 2 := (hcb.pow_left _).eq
    have e3 : c ^ m * b = b * c ^ m := (hcb.pow_left _).eq
    rw [pow_succ, ih, hT, pow_add c m (m.choose 2)]
    calc a ^ m * b ^ m * c ^ m.choose 2 * (a * b)
        = a ^ m * b ^ m * (c ^ m.choose 2 * a) * b := by group
      _ = a ^ m * (b ^ m * a) * (c ^ m.choose 2 * b) := by rw [e1]; group
      _ = a ^ m * (a * b ^ m * c ^ m) * (b * c ^ m.choose 2) := by rw [hbk, e2]
      _ = a ^ m * a * b ^ m * (c ^ m * b) * c ^ m.choose 2 := by group
      _ = a ^ m * a * b ^ m * (b * c ^ m) * c ^ m.choose 2 := by rw [e3]
      _ = a ^ (m + 1) * b ^ (m + 1) * (c ^ m * c ^ m.choose 2) := by
        rw [pow_succ a m, pow_succ b m]; group

theorem mk_eq_one_iff {q : Fin n → G} {s t : G}
    [((QG q).subgroupOf (HG q s t)).Normal] (h : HG q s t) :
    (h : HG q s t ⧸ (QG q).subgroupOf (HG q s t)) = 1 ↔ (h : G) ∈ QG q := by
  rw [QuotientGroup.eq_one_iff]
  exact mem_subgroupOf

namespace ScalRel

variable {q : Fin n → G} {z s t : G} {M Sm : Matrix (Fin n) (Fin n) (ZMod 5)} {i₀ j₀ : Fin n}
  {cs : Fin n → ℕ} {r : ZMod 5} {ct : Fin n → ℕ}
  (hR : ScalRel q z s t M Sm i₀ j₀ cs r ct)
include hR

theorem z_mem : z ∈ QG q := hR.commData.mem_z

theorem orderOf_z : orderOf z = 5 := hR.commData.orderOf_z

theorem z_pow_five : z ^ 5 = 1 := by rw [← hR.orderOf_z]; exact pow_orderOf_eq_one z

theorem prod_mem (a : Fin n → ℕ) (c : ℕ) :
    (List.ofFn fun j => q j ^ a j).prod * z ^ c ∈ QG q :=
  prod_mem_of_mem_z hR.z_mem a c

theorem conj_s_mem (i : Fin n) : s⁻¹ * q i * s ∈ QG q := by
  rw [hR.conj_s i]
  exact hR.prod_mem _ _

theorem conj_t_mem (i : Fin n) : t⁻¹ * q i * t ∈ QG q := by
  rw [hR.conj_t i]
  exact mul_mem (pow_mem (q_mem i) _) (pow_mem hR.z_mem _)

theorem s_conj_Q : ∀ g ∈ QG q, s⁻¹ * g * s ∈ QG q := fun _ hg =>
  CommData.conj_mem hR.conj_s_mem hg

theorem t_conj_Q : ∀ g ∈ QG q, t⁻¹ * g * t ∈ QG q := fun _ hg =>
  CommData.conj_mem hR.conj_t_mem hg

theorem Q_commute_z {g : G} (hg : g ∈ QG q) : g * z = z * g :=
  hR.commData.commute_of_mem hg (mem_zpowers z)

theorem bcomm_mem_zpowers {u v : G} (hu : u ∈ QG q) (hv : v ∈ QG q) : bcomm u v ∈ zpowers z :=
  hR.commData.bcomm_mem hu hv

theorem pow_five_of_mem {g : G} (hg : g ∈ QG q) : g ^ 5 = 1 := by
  induction hg using closure_induction with
  | mem g hg =>
    obtain ⟨i, rfl⟩ := hg
    exact hR.commData.pow_q i
  | one => exact one_pow 5
  | mul a b ha hb iha ihb =>
    set c := bcomm b a with hcdef
    have hcz : c ∈ zpowers z := hR.bcomm_mem_zpowers hb ha
    have hc : b * a = a * b * c := by rw [hcdef, bcomm]; group
    have hca : Commute c a := (hR.commData.commute_of_mem ha hcz).symm
    have hcb : Commute c b := (hR.commData.commute_of_mem hb hcz).symm
    have hc5 : c ^ 5 = 1 := by
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hcz
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hR.z_pow_five,
        one_zpow]
    rw [mul_pow_class_two hc hca hcb, iha, ihb, show (5 : ℕ).choose 2 = 5 * 2 by decide,
      pow_mul, hc5, one_pow, one_mul, one_mul]
  | inv a ha iha => rw [inv_pow, iha, inv_one]

theorem coord_pow {g : G} (hg : g ∈ QG q) (k : ℕ) :
    coord 5 q z M (g ^ k) = k • coord 5 q z M g := by
  induction k with
  | zero => rw [pow_zero, hR.commData.coord_one, zero_smul]
  | succ k ih =>
    rw [pow_succ, hR.commData.coord_mul (pow_mem hg k) hg, ih, succ_nsmul]

theorem coord_q_pow_mul (i : Fin n) (k c : ℕ) :
    coord 5 q z M (q i ^ k * z ^ c) = Pi.single i (k : ZMod 5) := by
  rw [hR.commData.coord_mul (pow_mem (q_mem i) k) (pow_mem hR.z_mem c),
    hR.commData.coord_of_mem_zpowers (pow_mem (mem_zpowers z) c), add_zero,
    hR.coord_pow (q_mem i), hR.commData.coord_q]
  ext j
  by_cases h : j = i
  · subst h
    simp
  · simp [h]

theorem actMat_t : CommData.actMat 5 q z M t = r • (1 : Matrix (Fin n) (Fin n) (ZMod 5)) := by
  ext i j
  simp only [CommData.actMat, Matrix.of_apply, hR.conj_t i, hR.coord_q_pow_mul,
    ZMod.natCast_zmod_val, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases h : j = i
  · subst h
    simp
  · simp [h, Ne.symm h]

theorem actMat_s : CommData.actMat 5 q z M s = Sm :=
  hR.commData.actMat_eq Sm cs hR.conj_s

theorem s_not_mem_Q (hS1 : Sm ≠ 1) : s ∉ QG q := fun hs => by
  have h1 := hR.commData.actMat_of_mem hs
  rw [hR.actMat_s] at h1
  exact hS1 h1

section Finite

variable [Finite G]

theorem H_conj {h : G} (hh : h ∈ HG q s t) : ∀ g ∈ QG q, h⁻¹ * g * h ∈ QG q := by
  refine conj_mem_of_mem_closure ?_ hh
  intro b hb g hg
  rcases hb with (hb | hb) | hb
  · exact mul_mem (mul_mem (inv_mem hb) hg) hb
  · rw [Set.mem_singleton_iff.1 hb]
    exact hR.s_conj_Q g hg
  · rw [Set.mem_singleton_iff.1 hb]
    exact hR.t_conj_Q g hg

theorem H_conj' {h : G} (hh : h ∈ HG q s t) : ∀ g ∈ QG q, h * g * h⁻¹ ∈ QG q := by
  intro g hg
  have := hR.H_conj (inv_mem hh) g hg
  rwa [inv_inv] at this

theorem Q_normal_H : ((QG q).subgroupOf (HG q s t)).Normal := by
  rw [normal_subgroupOf_iff Q_le_H]
  intro u g hu hg
  exact hR.H_conj' hg u hu

theorem card_Q : Nat.card (QG q) = 5 ^ (n + 1) := by
  have := fact5
  exact hR.commData.card_eq

theorem card_center_Q : Nat.card (center (QG q)) = 5 := by
  have := fact5
  rw [hR.commData.center_eq]
  exact hR.commData.card_zQ

theorem center_Q_eq_commutator : center (QG q) = commutator (QG q) := by
  have := fact5
  rw [hR.commData.center_eq, hR.commData.commutator_eq hR.z_eq]

theorem mem_center_of_coord_eq_zero {u : G} (hu : u ∈ QG q) (h : coord 5 q z M u = 0) :
    (⟨u, hu⟩ : QG q) ∈ center (QG q) := by
  have := fact5
  rw [hR.commData.center_eq, ← hR.commData.ker_coordHom, MonoidHom.mem_ker,
    hR.commData.coordHom_apply]
  show Multiplicative.ofAdd (coord 5 q z M u) = 1
  rw [h, ofAdd_zero]

section Quot

variable [((QG q).subgroupOf (HG q s t)).Normal]

omit [Finite G] in
theorem sb_pow : ((⟨s, s_mem_H⟩ : HG q s t) : HG q s t ⧸ (QG q).subgroupOf (HG q s t)) ^ 5 = 1 := by
  rw [← QuotientGroup.mk_pow, mk_eq_one_iff]
  exact hR.s_pow

omit [Finite G] in
theorem tb_pow : ((⟨t, t_mem_H⟩ : HG q s t) : HG q s t ⧸ (QG q).subgroupOf (HG q s t)) ^ 4 = 1 := by
  rw [← QuotientGroup.mk_pow, mk_eq_one_iff]
  show t ^ 4 ∈ QG q
  rw [hR.t_pow]
  exact one_mem _

omit [Finite G] in
theorem sb_commute : Commute
    ((⟨s, s_mem_H⟩ : HG q s t) : HG q s t ⧸ (QG q).subgroupOf (HG q s t))
    ((⟨t, t_mem_H⟩ : HG q s t) : HG q s t ⧸ (QG q).subgroupOf (HG q s t)) := by
  show _ * _ = _ * _
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
  show (s * t)⁻¹ * (t * s) ∈ QG q
  have e : (s * t)⁻¹ * (t * s) = t⁻¹ * s⁻¹ * t * s := by group
  rw [e]
  exact hR.ts_mem

omit [Finite G] in
theorem Hq_cyclic : IsCyclic (HG q s t ⧸ (QG q).subgroupOf (HG q s t)) := by
  set sb : HG q s t ⧸ (QG q).subgroupOf (HG q s t) :=
    ((⟨s, s_mem_H⟩ : HG q s t) : HG q s t ⧸ (QG q).subgroupOf (HG q s t)) with hsb
  set tb : HG q s t ⧸ (QG q).subgroupOf (HG q s t) :=
    ((⟨t, t_mem_H⟩ : HG q s t) : HG q s t ⧸ (QG q).subgroupOf (HG q s t)) with htb
  have hs5 : sb ^ 5 = 1 := hR.sb_pow
  have ht4 : tb ^ 4 = 1 := hR.tb_pow
  have hcomm : Commute sb tb := hR.sb_commute
  have hcs : (sb * tb) ^ 16 = sb := by
    have h1 : sb ^ 16 = sb := by
      rw [show (16 : ℕ) = 5 * 3 + 1 by norm_num, pow_add, pow_mul, hs5, one_pow, one_mul,
        pow_one]
    have h2 : tb ^ 16 = 1 := by
      rw [show (16 : ℕ) = 4 * 4 by norm_num, pow_mul, ht4, one_pow]
    rw [Commute.mul_pow hcomm, h1, h2, mul_one]
  have hct : (sb * tb) ^ 25 = tb := by
    have h1 : sb ^ 25 = 1 := by
      rw [show (25 : ℕ) = 5 * 5 by norm_num, pow_mul, hs5, one_pow]
    have h2 : tb ^ 25 = tb := by
      rw [show (25 : ℕ) = 4 * 6 + 1 by norm_num, pow_add, pow_mul, ht4, one_pow, one_mul,
        pow_one]
    rw [Commute.mul_pow hcomm, h1, h2, one_mul]
  have hsm : sb ∈ zpowers (sb * tb) := mem_zpowers_iff.2 ⟨16, by
    rw [show (16 : ℤ) = ((16 : ℕ) : ℤ) by norm_num, zpow_natCast]
    exact hcs⟩
  have htm : tb ∈ zpowers (sb * tb) := mem_zpowers_iff.2 ⟨25, by
    rw [show (25 : ℤ) = ((25 : ℕ) : ℤ) by norm_num, zpow_natCast]
    exact hct⟩
  rw [isCyclic_iff_exists_zpowers_eq_top]
  refine ⟨sb * tb, ?_⟩
  rw [eq_top_iff]
  intro g _
  induction g using QuotientGroup.induction_on with
  | H h =>
    obtain ⟨g, hg⟩ := h
    refine closure_induction (p := fun g hg =>
      ((⟨g, hg⟩ : HG q s t) : HG q s t ⧸ (QG q).subgroupOf (HG q s t)) ∈ zpowers (sb * tb))
      ?_ ?_ ?_ ?_ hg
    · intro g hg'
      simp only [Set.mem_union, Set.mem_singleton_iff, SetLike.mem_coe] at hg'
      rcases hg' with (hg' | rfl) | rfl
      · have h1 : ((⟨g, subset_closure (Or.inl (Or.inl hg'))⟩ : HG q s t) :
            HG q s t ⧸ (QG q).subgroupOf (HG q s t)) = 1 := (mk_eq_one_iff _).2 hg'
        rw [h1]
        exact one_mem _
      · exact hsm
      · exact htm
    · show ((1 : HG q s t) : HG q s t ⧸ (QG q).subgroupOf (HG q s t)) ∈ _
      rw [QuotientGroup.mk_one]
      exact one_mem _
    · intro a b ha hb iha ihb
      show ((⟨a, ha⟩ * ⟨b, hb⟩ : HG q s t) : HG q s t ⧸ (QG q).subgroupOf (HG q s t)) ∈ _
      rw [QuotientGroup.mk_mul]
      exact mul_mem iha ihb
    · intro a ha iha
      show (((⟨a, ha⟩ : HG q s t)⁻¹ : HG q s t) : HG q s t ⧸ (QG q).subgroupOf (HG q s t)) ∈ _
      rw [QuotientGroup.mk_inv]
      exact inv_mem iha

omit [Finite G] in
theorem sb_ne_one (hS1 : Sm ≠ 1) :
    ((⟨s, s_mem_H⟩ : HG q s t) : HG q s t ⧸ (QG q).subgroupOf (HG q s t)) ≠ 1 := fun h =>
  hR.s_not_mem_Q hS1 ((mk_eq_one_iff _).1 h)

omit [Finite G] in
theorem five_dvd_card_Hq (hS1 : Sm ≠ 1) :
    5 ∣ Nat.card (HG q s t ⧸ (QG q).subgroupOf (HG q s t)) := by
  have := fact5
  have h1 : orderOf ((⟨s, s_mem_H⟩ : HG q s t) :
      HG q s t ⧸ (QG q).subgroupOf (HG q s t)) = 5 :=
    orderOf_eq_prime hR.sb_pow (hR.sb_ne_one hS1)
  exact h1 ▸ orderOf_dvd_natCard _

omit [((QG q).subgroupOf (HG q s t)).Normal] in
theorem card_H_eq : Nat.card (HG q s t) =
    Nat.card (HG q s t ⧸ (QG q).subgroupOf (HG q s t)) * 5 ^ (n + 1) := by
  rw [card_eq_card_quotient_mul_card_subgroup ((QG q).subgroupOf (HG q s t)),
    Nat.card_congr (subgroupOfEquivOfLe Q_le_H).toEquiv, hR.card_Q]

theorem pow_dvd_card_H (hS1 : Sm ≠ 1) : 5 ^ (n + 2) ∣ Nat.card (HG q s t) := by
  rw [hR.card_H_eq, show n + 2 = (n + 1) + 1 from rfl, pow_succ', mul_comm]
  exact Nat.mul_dvd_mul dvd_rfl (hR.five_dvd_card_Hq hS1) |>.trans (by rw [mul_comm])

theorem index_coprime (hS1 : Sm ≠ 1) (h5 : (Nat.card G).factorization 5 ≤ n + 2) :
    (HG q s t).index.Coprime 5 := by
  have := fact5
  rw [Nat.coprime_comm, Nat.prime_five.coprime_iff_not_dvd]
  intro hd
  have hcard : Nat.card (HG q s t) * (HG q s t).index = Nat.card G := Subgroup.card_mul_index _
  have h1 : 5 ^ (n + 2) * 5 ∣ Nat.card G := hcard ▸ mul_dvd_mul (hR.pow_dvd_card_H hS1) hd
  have h2 : 5 ^ (n + 2 + 1) ∣ Nat.card G := by rwa [pow_succ]
  have h3 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_five Nat.card_pos.ne').1 h2
  omega

end Quot

theorem kernelTrivial (hS1 : Sm ≠ 1) (hr2 : r ^ 2 ≠ 1) (hr3 : r ^ 3 ≠ 1)
    (h5 : (Nat.card G).factorization 5 ≤ n + 2)
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E] (π : E →* G)
    (hπ : Function.Surjective π) (hC : π.ker ≤ center E) (hCp : IsPGroup 5 π.ker) :
    π.ker = ⊥ := by
  have := fact5
  have hN : ((QG q).subgroupOf (HG q s t)).Normal := hR.Q_normal_H
  have hcyc : IsCyclic (HG q s t ⧸ (QG q).subgroupOf (HG q s t)) := hR.Hq_cyclic
  set σ : HG q s t ⧸ (QG q).subgroupOf (HG q s t) :=
    ((⟨t⁻¹, inv_mem t_mem_H⟩ : HG q s t) : HG q s t ⧸ (QG q).subgroupOf (HG q s t)) with hσ
  have hσZ : σ ∈ center (HG q s t ⧸ (QG q).subgroupOf (HG q s t)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact mul_comm' g σ
  have hσ4 : σ ^ 4 = 1 := by
    rw [hσ, ← QuotientGroup.mk_pow, mk_eq_one_iff]
    show (t⁻¹) ^ 4 ∈ QG q
    rw [inv_pow, hR.t_pow, inv_one]
    exact one_mem _
  have hσo : (orderOf σ).Coprime 5 :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hσ4) (by norm_num)
  have hσV : ∀ h : HG q s t, (h : HG q s t ⧸ (QG q).subgroupOf (HG q s t)) = σ →
      ∀ g ∈ QG q, ((h : G) * g * (h : G)⁻¹)⁻¹ * g ^ r.val ∈
        (center (QG q)).map (QG q).subtype := by
    intro h hh g hg
    have hw : t * (h : G) ∈ QG q := by
      have h2 := mem_subgroupOf.1 (QuotientGroup.eq.1 hh.symm)
      simpa using h2
    have hhw : (h : G) = t⁻¹ * (t * (h : G)) := by group
    have hconj : (h : G) * g * (h : G)⁻¹ = t⁻¹ * ((t * (h : G)) * g * (t * (h : G))⁻¹) * t := by
      group
    have hg' : (t * (h : G)) * g * (t * (h : G))⁻¹ ∈ QG q := mul_mem (mul_mem hw hg) (inv_mem hw)
    have hcoord' : coord 5 q z M ((t * (h : G)) * g * (t * (h : G))⁻¹) = coord 5 q z M g := by
      have := hR.commData.coord_conj_of_mem (inv_mem hw) hg
      simpa using this
    have hu : t⁻¹ * ((t * (h : G)) * g * (t * (h : G))⁻¹) * t ∈ QG q := hR.t_conj_Q _ hg'
    have hcoordu : coord 5 q z M (t⁻¹ * ((t * (h : G)) * g * (t * (h : G))⁻¹) * t) =
        r • coord 5 q z M g := by
      rw [hR.commData.coord_conj hR.conj_t_mem hg', hR.actMat_t, Matrix.vecMul_smul,
        Matrix.vecMul_one, hcoord']
    have hwq : ((h : G) * g * (h : G)⁻¹)⁻¹ * g ^ r.val ∈ QG q := by
      rw [hconj]
      exact mul_mem (inv_mem hu) (pow_mem hg _)
    refine Subgroup.mem_map.2 ⟨⟨_, hwq⟩, hR.mem_center_of_coord_eq_zero hwq ?_, rfl⟩
    rw [hR.commData.coord_mul (hconj ▸ inv_mem hu) (pow_mem hg _),
      hR.commData.coord_inv (hconj ▸ hu), hconj, hcoordu, hR.coord_pow hg,
      ← Nat.cast_smul_eq_nsmul (ZMod 5), ZMod.natCast_zmod_val, neg_add_cancel]
  exact scalar_normalizer_pKernel_eq_bot (hR.index_coprime hS1 h5) Q_le_H
    (fun g hg => hR.pow_five_of_mem hg) hR.center_Q_eq_commutator hR.card_center_Q
    (fun P => inferInstance) σ hσZ hσo r hr2 hr3 hσV π hπ hC hCp

end Finite

end ScalRel

end CFSG.RankThree.PartOne.KS.ScalFive
