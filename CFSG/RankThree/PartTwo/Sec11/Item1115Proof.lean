module

public import CFSG.RankThree.PartTwo.Sec11.FixedPoints
public import CFSG.RankThree.PartTwo.Sec11.Item1116Proof
public import CFSG.RankThree.PartTwo.Sec11.RFactsK
public import CFSG.RankThree.PartTwo.KFacts.KS44Transport
public import CFSG.RankThree.PartTwo.Sec11.Item1115
public import CFSG.RankThree.PartTwo.Sec11.Transitivity

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

namespace Item1115Proof

section Cyclic

variable {G : Type} [Group G] [Finite G]

theorem mem_zpowers_of_orderOf_dvd {r u w : G} (hu : u ∈ Subgroup.zpowers r)
    (hw : w ∈ Subgroup.zpowers r) (hdvd : orderOf u ∣ orderOf w) :
    u ∈ Subgroup.zpowers w := by
  set S := Subgroup.zpowers r
  have hle : Subgroup.zpowers (⟨u, hu⟩ : S) ≤ Subgroup.zpowers (⟨w, hw⟩ : S) := by
    rw [IsCyclic.subgroup_le_iff_card_dvd, Nat.card_zpowers, Nat.card_zpowers,
      Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    exact hdvd
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hle (Subgroup.mem_zpowers _))
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  have := congrArg Subtype.val hk
  simpa using this

omit [Finite G] in
theorem exists_pow_three_pow_of_mem_zpowers {r w : G} (hr : ∃ k : ℕ, r ^ 3 ^ k = 1)
    (hw : w ∈ Subgroup.zpowers r) : ∃ k : ℕ, w ^ 3 ^ k = 1 := by
  obtain ⟨k, hk⟩ := hr
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  refine ⟨k, ?_⟩
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]

omit [Finite G] in
theorem exists_orderOf_eq_three_pow {w : G} (hw : ∃ k : ℕ, w ^ 3 ^ k = 1) :
    ∃ j : ℕ, orderOf w = 3 ^ j := by
  obtain ⟨k, hk⟩ := hw
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk)
  exact ⟨j, hj⟩

theorem mem_zpowers_or_mem_zpowers {r u w : G} (hr : ∃ k : ℕ, r ^ 3 ^ k = 1)
    (hu : u ∈ Subgroup.zpowers r) (hw : w ∈ Subgroup.zpowers r) :
    u ∈ Subgroup.zpowers w ∨ w ∈ Subgroup.zpowers u := by
  obtain ⟨i, hi⟩ := exists_orderOf_eq_three_pow (exists_pow_three_pow_of_mem_zpowers hr hu)
  obtain ⟨j, hj⟩ := exists_orderOf_eq_three_pow (exists_pow_three_pow_of_mem_zpowers hr hw)
  rcases le_total i j with hij | hji
  · left
    exact mem_zpowers_of_orderOf_dvd hu hw (by rw [hi, hj]; exact Nat.pow_dvd_pow 3 hij)
  · right
    exact mem_zpowers_of_orderOf_dvd hw hu (by rw [hi, hj]; exact Nat.pow_dvd_pow 3 hji)

theorem commute_pow_three_of_commute_pow_three {w s : G} (hw : ∃ k : ℕ, w ^ 3 ^ k = 1)
    (hws : w ∈ Subgroup.normalizer (Subgroup.zpowers s : Set G))
    (h3 : w * s ^ 3 = s ^ 3 * w) : w ^ 3 * s = s * w ^ 3 := by
  set z := w * s * w⁻¹ * s⁻¹ with hz
  have hconj : ∀ y ∈ Subgroup.zpowers s, w * y * w⁻¹ ∈ Subgroup.zpowers s := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp hws y).mp hy
  have hs : s ∈ Subgroup.zpowers s := Subgroup.mem_zpowers s
  have hzS : z ∈ Subgroup.zpowers s := Subgroup.mul_mem _ (hconj s hs) (Subgroup.inv_mem _ hs)
  have hcomm : ∀ y ∈ Subgroup.zpowers s, ∀ y' ∈ Subgroup.zpowers s, y * y' = y' * y := by
    intro y hy y' hy'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy'
    rw [← zpow_add, ← zpow_add, add_comm]
  have hws' : w * s * w⁻¹ = z * s := by rw [hz]; group
  have hz3 : z ^ 3 = 1 := by
    have h1 : (w * s * w⁻¹) ^ 3 = s ^ 3 := by
      rw [conj_pow, h3, mul_inv_cancel_right]
    have h2 : (z * s) ^ 3 = z ^ 3 * s ^ 3 := (Commute.mul_pow (hcomm z hzS s hs) 3)
    rw [hws', h2] at h1
    calc z ^ 3 = z ^ 3 * s ^ 3 * (s ^ 3)⁻¹ := by group
      _ = 1 := by rw [h1, mul_inv_cancel]
  have hwz : w * z * w⁻¹ = z := by
    by_cases hz1 : z = 1
    · rw [hz1, mul_one, mul_inv_cancel]
    · refine conj_eq_self_of_threeElement hz3 hw (mem_zpowers_of_orderOf_dvd (hconj z hzS) hzS ?_)
      apply orderOf_dvd_of_pow_eq_one
      rw [conj_pow, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
  have hn : ∀ n : ℕ, w ^ n * s * (w ^ n)⁻¹ = z ^ n * s := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc w ^ (n + 1) * s * (w ^ (n + 1))⁻¹ = w * (w ^ n * s * (w ^ n)⁻¹) * w⁻¹ := by
            rw [pow_succ', mul_inv_rev]; group
        _ = w * (z ^ n * s) * w⁻¹ := by rw [ih]
        _ = (w * z * w⁻¹) ^ n * (w * s * w⁻¹) := by rw [conj_pow]; group
        _ = z ^ (n + 1) * s := by rw [hwz, hws', ← mul_assoc, ← pow_succ]
  have h33 := hn 3
  rw [hz3, one_mul] at h33
  calc w ^ 3 * s = w ^ 3 * s * (w ^ 3)⁻¹ * w ^ 3 := by group
    _ = s * w ^ 3 := by rw [h33]

theorem commute_pow_three_pow {w : G} (hw : ∃ k : ℕ, w ^ 3 ^ k = 1) :
    ∀ (v : ℕ) (s : G), w ∈ Subgroup.normalizer (Subgroup.zpowers s : Set G) →
      w * s ^ 3 ^ v = s ^ 3 ^ v * w → w ^ 3 ^ v * s = s * w ^ 3 ^ v := by
  intro v
  induction v with
  | zero => intro s _ h; simpa using h
  | succ v ih =>
    intro s hws h
    have hws3 : w ∈ Subgroup.normalizer (Subgroup.zpowers (s ^ 3) : Set G) := by
      apply Sec10.mem_normalizer_zpowers_of_conj_mem
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp
        ((Subgroup.mem_normalizer_iff.mp hws s).mp (Subgroup.mem_zpowers s))
      refine Subgroup.mem_zpowers_iff.mpr ⟨i, ?_⟩
      rw [← conj_pow, ← hi]
      group
    have h' : w * (s ^ 3) ^ 3 ^ v = (s ^ 3) ^ 3 ^ v * w := by
      rw [← pow_mul, ← pow_succ']
      exact h
    have h1 := ih (s ^ 3) hws3 h'
    have hw' : ∃ k : ℕ, (w ^ 3 ^ v) ^ 3 ^ k = 1 := by
      obtain ⟨k, hk⟩ := hw
      exact ⟨k, by rw [← pow_mul, mul_comm, pow_mul, hk, one_pow]⟩
    have hws' : w ^ 3 ^ v ∈ Subgroup.normalizer (Subgroup.zpowers s : Set G) :=
      Subgroup.pow_mem _ hws _
    have h2 := commute_pow_three_of_commute_pow_three hw' hws' h1
    rw [← pow_mul, ← pow_succ] at h2
    exact h2

theorem mem_zpowers_pow_orderOf {w s : G} (hw : ∃ k : ℕ, w ^ 3 ^ k = 1)
    (hs : ∃ k : ℕ, s ^ 3 ^ k = 1) (hws : w ∈ Subgroup.normalizer (Subgroup.zpowers s : Set G))
    (hfaith : ∀ n : ℕ, w ^ n * s = s * w ^ n → w ^ n = 1) {y : G}
    (hy : y ∈ Subgroup.zpowers s) (hwy : w * y = y * w) :
    y ∈ Subgroup.zpowers (s ^ orderOf w) := by
  obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hy)
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [pow_zero]
    exact Subgroup.one_mem _
  obtain ⟨v, k', hk', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk0.ne' 3 (by norm_num)
  have hsv : s ^ 3 ^ v ∈ Subgroup.zpowers (s ^ (3 ^ v * k')) := by
    have h3v : ∃ m : ℕ, (s ^ 3 ^ v) ^ 3 ^ m = 1 := by
      obtain ⟨m, hm⟩ := hs
      exact ⟨m, by rw [← pow_mul, mul_comm, pow_mul, hm, one_pow]⟩
    have := Item1116Proof.mem_zpowers_zpow_of_not_dvd h3v (i := (k' : ℤ)) (by exact_mod_cast hk')
    rwa [zpow_natCast, ← pow_mul] at this
  have hwv : w * s ^ 3 ^ v = s ^ 3 ^ v * w := by
    have hC : Subgroup.zpowers (s ^ (3 ^ v * k')) ≤ Subgroup.centralizer {w} :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hwy.symm)
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hC hsv)).symm
  have h1 := commute_pow_three_pow hw v s hws hwv
  have h2 := hfaith _ h1
  obtain ⟨t, ht⟩ := orderOf_dvd_of_pow_eq_one h2
  refine Subgroup.mem_zpowers_iff.mpr ⟨((t * k' : ℕ) : ℤ), ?_⟩
  rw [zpow_natCast, ← pow_mul, ht, mul_assoc]

theorem orderOf_dvd_orderOf_of_faithful {w s : G} (hw : ∃ k : ℕ, w ^ 3 ^ k = 1)
    (hs : ∃ k : ℕ, s ^ 3 ^ k = 1) (hws : w ∈ Subgroup.normalizer (Subgroup.zpowers s : Set G))
    (hfaith : ∀ n : ℕ, w ^ n * s = s * w ^ n → w ^ n = 1) : orderOf w ∣ orderOf s := by
  obtain ⟨m, hm⟩ := exists_orderOf_eq_three_pow hs
  have h1 : w * s ^ 3 ^ m = s ^ 3 ^ m * w := by rw [← hm, pow_orderOf_eq_one, mul_one, one_mul]
  have h2 := hfaith _ (commute_pow_three_pow hw m s hws h1)
  rw [hm]
  exact orderOf_dvd_of_pow_eq_one h2

omit [Finite G] in
theorem commute_of_mem_closure_pair {y z u v : G} (hyz : y * z = z * y)
    (hu : u ∈ Subgroup.closure ({y, z} : Set G)) (hv : v ∈ Subgroup.closure ({y, z} : Set G)) :
    u * v = v * u := by
  obtain ⟨i, j, rfl⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair hyz hu
  obtain ⟨k, l, rfl⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair hyz hv
  have hc : Commute y z := hyz
  exact ((Commute.zpow_zpow_self y i k).mul_right (hc.zpow_zpow i l)).mul_left
    ((hc.symm.zpow_zpow j k).mul_right (Commute.zpow_zpow_self z j l))

theorem card_closure_pair_le_mul {y z : G} (hyz : y * z = z * y) :
    Nat.card (Subgroup.closure ({y, z} : Set G)) ≤ orderOf y * orderOf z := by
  have hyK : y ∈ Subgroup.closure ({y, z} : Set G) := Subgroup.subset_closure (by simp)
  have hzK : z ∈ Subgroup.closure ({y, z} : Set G) := Subgroup.subset_closure (by simp)
  let f : Subgroup.zpowers y × Subgroup.zpowers z → Subgroup.closure ({y, z} : Set G) :=
    fun p => ⟨p.1 * p.2, Subgroup.mul_mem _ (Subgroup.zpowers_le.mpr hyK p.1.2)
      (Subgroup.zpowers_le.mpr hzK p.2.2)⟩
  have hf : Function.Surjective f := by
    rintro ⟨w, hw⟩
    obtain ⟨m, n, rfl⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair hyz hw
    exact ⟨(⟨y ^ m, Subgroup.zpow_mem_zpowers y m⟩, ⟨z ^ n, Subgroup.zpow_mem_zpowers z n⟩), rfl⟩
  calc Nat.card (Subgroup.closure ({y, z} : Set G)) ≤
        Nat.card (Subgroup.zpowers y × Subgroup.zpowers z) := Nat.card_le_card_of_surjective f hf
    _ = orderOf y * orderOf z := by rw [Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers]

omit [Finite G] in
theorem inv_pow_mul_pow_mem {V : Subgroup G} {w v : G}
    (hw : w ∈ Subgroup.normalizer (V : Set G)) (hv : v ∈ V) (n : ℕ) :
    (w ^ n)⁻¹ * (w * v) ^ n ∈ V := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (w ^ (n + 1))⁻¹ * (w * v) ^ (n + 1) =
        w⁻¹ * ((w ^ n)⁻¹ * (w * v) ^ n) * w * v := by
      rw [pow_succ, pow_succ]
      group
    rw [e]
    refine V.mul_mem ?_ hv
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hw) _).mp ih
    rwa [inv_inv] at this

theorem card_closure_le_mul_card_inf {V : Subgroup G} {y₁ y₂ : G} (hy : y₁ * y₂ = y₂ * y₁)
    {N : ℕ} (hN0 : 0 < N) (hN : y₂ ^ N ∈ V) {m : ℕ} (hm : (y₂ ^ m)⁻¹ * y₁ ∈ V) :
    Nat.card (Subgroup.closure ({y₁, y₂} : Set G)) ≤
      N * Nat.card (V ⊓ Subgroup.closure ({y₁, y₂} : Set G) : Subgroup G) := by
  set V' := Subgroup.closure ({y₁, y₂} : Set G) with hV'
  have hy₁ : y₁ ∈ V' := Subgroup.subset_closure (by simp)
  have hy₂ : y₂ ∈ V' := Subgroup.subset_closure (by simp)
  set u := (y₂ ^ m)⁻¹ * y₁ with hu
  have huV' : u ∈ V' := Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ hy₂ m)) hy₁
  have hc : Commute y₂ u := by
    have h1 : Commute y₂ y₁ := hy.symm
    exact ((Commute.refl y₂).pow_right m).inv_right.mul_right h1
  have hy₁eq : y₁ = y₂ ^ m * u := by rw [hu]; group
  let f : Fin N × (V ⊓ V' : Subgroup G) → V' := fun p =>
    ⟨y₂ ^ (p.1 : ℕ) * p.2, Subgroup.mul_mem _ (Subgroup.pow_mem _ hy₂ _) p.2.2.2⟩
  have hf : Function.Surjective f := by
    rintro ⟨z, hz⟩
    obtain ⟨i, j, rfl⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair hy hz
    set t : ℤ := (m : ℤ) * i + j with ht
    have hNz : (0 : ℤ) < N := by exact_mod_cast hN0
    have ht0 : 0 ≤ t % N := Int.emod_nonneg _ hNz.ne'
    have htN : t % N < N := Int.emod_lt_of_pos _ hNz
    have e1 : y₁ ^ i * y₂ ^ j = y₂ ^ t * u ^ i := by
      have hcu : Commute (y₂ ^ m) u := hc.pow_left m
      have hju : u ^ i * y₂ ^ j = y₂ ^ j * u ^ i := ((hc.zpow_left j).zpow_right i).eq.symm
      calc y₁ ^ i * y₂ ^ j = (y₂ ^ m * u) ^ i * y₂ ^ j := by rw [← hy₁eq]
        _ = (y₂ ^ m) ^ i * (u ^ i * y₂ ^ j) := by rw [hcu.mul_zpow, mul_assoc]
        _ = y₂ ^ ((m : ℤ) * i) * y₂ ^ j * u ^ i := by
          rw [hju, ← zpow_natCast y₂ m, ← zpow_mul, mul_assoc]
        _ = y₂ ^ t * u ^ i := by rw [← zpow_add]
    have e2 : y₂ ^ t = y₂ ^ ((t % N).toNat) * (y₂ ^ N) ^ (t / N) := by
      rw [← zpow_natCast y₂ (t % N).toNat, Int.toNat_of_nonneg ht0, ← zpow_natCast y₂ N,
        ← zpow_mul, ← zpow_add, Int.emod_add_mul_ediv]
    refine ⟨(⟨(t % N).toNat, by omega⟩, ⟨(y₂ ^ N) ^ (t / N) * u ^ i, ?_, ?_⟩), ?_⟩
    · exact V.mul_mem (V.zpow_mem hN _) (V.zpow_mem hm i)
    · exact V'.mul_mem (V'.zpow_mem (V'.pow_mem hy₂ N) _) (V'.zpow_mem huV' i)
    · apply Subtype.ext
      change y₂ ^ (t % N).toNat * ((y₂ ^ N) ^ (t / N) * u ^ i) = y₁ ^ i * y₂ ^ j
      rw [e1, e2, mul_assoc]
  calc Nat.card V' ≤ Nat.card (Fin N × (V ⊓ V' : Subgroup G)) :=
        Nat.card_le_card_of_surjective f hf
    _ = N * Nat.card (V ⊓ V' : Subgroup G) := by
      rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin]

omit [Finite G] in
theorem le_normalizer_map_conj {P K : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (P : Set G)) (hPK : P ≤ Subgroup.normalizer (K : Set G)) :
    P ≤ Subgroup.normalizer ((K.map (MulAut.conj n).toMonoidHom : Subgroup G) : Set G) := by
  intro q hq
  have hq' : n⁻¹ * q * n ∈ P := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) q).mp hq
    rwa [inv_inv] at this
  have hK : K.map (MulAut.conj (n⁻¹ * q * n)).toMonoidHom = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPK hq')
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  change (K.map (MulAut.conj n).toMonoidHom).map (MulAut.conj q).toMonoidHom = _
  rw [map_conj_map_conj]
  have e : q * n = n * (n⁻¹ * q * n) := by group
  rw [e, ← map_conj_map_conj, hK]

theorem sec11K_map_conj' {L : Subgroup G} {n : G} (hn : n ∈ Subgroup.normalizer (L : Set G))
    (a : G) :
    sec11K L (MulAut.conj n a) = (sec11K L a).map (MulAut.conj n).toMonoidHom := by
  unfold sec11K
  rw [GroupTheory.SteinbergBY.map_inSubgroup_perfectResidual_of_injective _
    (MulAut.conj n).injective]
  congr 1
  have hL : L.map (MulAut.conj n).toMonoidHom = L := Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
  rw [Subgroup.map_inf _ _ _ (MulAut.conj n).injective, map_centralizer_singleton, hL]

end Cyclic

section Mho

variable {G : Type} [Group G] [Finite G]

structure MhoHyp (r s x a : G) : Prop where
  commute_s_x : s * x = x * s
  inf_eq_bot : Subgroup.zpowers s ⊓ Subgroup.zpowers x = ⊥
  r_mem_normalizer_s : r ∈ Subgroup.normalizer (Subgroup.zpowers s : Set G)
  r_mem_normalizer_x : r ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G)
  pow_r : ∃ k : ℕ, r ^ 3 ^ k = 1
  pow_s : ∃ k : ℕ, s ^ 3 ^ k = 1
  pow_x : ∃ k : ℕ, x ^ 3 ^ k = 1
  a_mem : a ∈ Subgroup.zpowers r
  a_ne_one : a ≠ 1
  a_cube : a ^ 3 = 1
  not_commute_s : a * s ≠ s * a
  not_commute_x : a * x ≠ x * a

namespace MhoHyp

variable {r s x a : G}

theorem mem_zpowers_of_ne_one (h : MhoHyp r s x a) {w : G} (hw : w ∈ Subgroup.zpowers r)
    (hw1 : w ≠ 1) : a ∈ Subgroup.zpowers w := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine mem_zpowers_of_orderOf_dvd h.a_mem hw ?_
  rw [orderOf_eq_prime h.a_cube h.a_ne_one]
  obtain ⟨j, hj⟩ := exists_orderOf_eq_three_pow (exists_pow_three_pow_of_mem_zpowers h.pow_r hw)
  rw [hj]
  rcases j with _ | j
  · exact absurd (orderOf_eq_one_iff.mp (by simpa using hj)) hw1
  · exact dvd_pow_self 3 (Nat.succ_ne_zero j)

theorem faithful_s (h : MhoHyp r s x a) {w : G} (hw : w ∈ Subgroup.zpowers r) (n : ℕ)
    (hn : w ^ n * s = s * w ^ n) : w ^ n = 1 := by
  by_contra hne
  have ha := h.mem_zpowers_of_ne_one (Subgroup.pow_mem _ hw n) hne
  have hC : Subgroup.zpowers (w ^ n) ≤ Subgroup.centralizer ({s} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hn)
  exact h.not_commute_s (Subgroup.mem_centralizer_singleton_iff.mp (hC ha))

theorem faithful_x (h : MhoHyp r s x a) {w : G} (hw : w ∈ Subgroup.zpowers r) (n : ℕ)
    (hn : w ^ n * x = x * w ^ n) : w ^ n = 1 := by
  by_contra hne
  have ha := h.mem_zpowers_of_ne_one (Subgroup.pow_mem _ hw n) hne
  have hC : Subgroup.zpowers (w ^ n) ≤ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hn)
  exact h.not_commute_x (Subgroup.mem_centralizer_singleton_iff.mp (hC ha))

theorem r_mem_normalizer_V (h : MhoHyp r s x a) :
    r ∈ Subgroup.normalizer ((Subgroup.closure {s, x} : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  have hle : Subgroup.closure ({s, x} : Set G) ≤
      (Subgroup.closure ({s, x} : Set G)).comap (MulAut.conj r).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    change r * y * r⁻¹ ∈ _
    rcases hy with rfl | rfl
    · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
        ((Subgroup.mem_normalizer_iff.mp h.r_mem_normalizer_s y).mp (Subgroup.mem_zpowers y))
    · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
        ((Subgroup.mem_normalizer_iff.mp h.r_mem_normalizer_x y).mp (Subgroup.mem_zpowers y))
  exact hle hz

theorem exists_mul_of_mem (h : MhoHyp r s x a) {y : G}
    (hy : y ∈ Subgroup.closure ({r, x, s} : Set G)) :
    ∃ w ∈ Subgroup.zpowers r, ∃ v ∈ Subgroup.closure ({s, x} : Set G), y = w * v := by
  have hcl : Subgroup.closure ({r, x, s} : Set G) =
      Subgroup.zpowers r ⊔ Subgroup.closure ({s, x} : Set G) := by
    rw [Set.insert_eq, Subgroup.closure_union, Subgroup.zpowers_eq_closure, Set.pair_comm]
  have hle : Subgroup.zpowers r ≤
      Subgroup.normalizer ((Subgroup.closure {s, x} : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr h.r_mem_normalizer_V
  have hy' : y ∈ ((Subgroup.zpowers r ⊔ Subgroup.closure ({s, x} : Set G) : Subgroup G) :
      Set G) := by
    rw [← hcl]
    exact hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle] at hy'
  obtain ⟨w, hw, v, hv, rfl⟩ := Set.mem_mul.mp hy'
  exact ⟨w, hw, v, hv, rfl⟩

theorem mem_closure_pow_of_commute (h : MhoHyp r s x a) {w : G} (hw : w ∈ Subgroup.zpowers r)
    {v : G} (hv : v ∈ Subgroup.closure ({s, x} : Set G)) (hwv : w * v = v * w) :
    v ∈ Subgroup.closure ({s ^ orderOf w, x ^ orderOf w} : Set G) := by
  obtain ⟨i, j, rfl⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair h.commute_s_x hv
  have hw3 := exists_pow_three_pow_of_mem_zpowers h.pow_r hw
  have hws : w ∈ Subgroup.normalizer (Subgroup.zpowers s : Set G) :=
    Subgroup.zpowers_le.mpr h.r_mem_normalizer_s hw
  have hwx : w ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) :=
    Subgroup.zpowers_le.mpr h.r_mem_normalizer_x hw
  have hs' : w * s ^ i * w⁻¹ ∈ Subgroup.zpowers s :=
    (Subgroup.mem_normalizer_iff.mp hws _).mp (Subgroup.zpow_mem_zpowers s i)
  have hx' : w * x ^ j * w⁻¹ ∈ Subgroup.zpowers x :=
    (Subgroup.mem_normalizer_iff.mp hwx _).mp (Subgroup.zpow_mem_zpowers x j)
  have e : (w * s ^ i * w⁻¹)⁻¹ * s ^ i = (w * x ^ j * w⁻¹) * (x ^ j)⁻¹ := by
    have h1 : w * (s ^ i * x ^ j) * w⁻¹ = s ^ i * x ^ j := by rw [hwv, mul_inv_cancel_right]
    have h2 : w * (s ^ i * x ^ j) * w⁻¹ = (w * s ^ i * w⁻¹) * (w * x ^ j * w⁻¹) := by group
    calc (w * s ^ i * w⁻¹)⁻¹ * s ^ i
        = (w * s ^ i * w⁻¹)⁻¹ * (s ^ i * x ^ j) * (x ^ j)⁻¹ := by group
      _ = (w * s ^ i * w⁻¹)⁻¹ * ((w * s ^ i * w⁻¹) * (w * x ^ j * w⁻¹)) * (x ^ j)⁻¹ := by
          rw [← h2, h1]
      _ = (w * x ^ j * w⁻¹) * (x ^ j)⁻¹ := by group
  have hmem : (w * s ^ i * w⁻¹)⁻¹ * s ^ i ∈ Subgroup.zpowers s ⊓ Subgroup.zpowers x := by
    refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hs') (Subgroup.zpow_mem_zpowers s i), ?_⟩
    rw [e]
    exact Subgroup.mul_mem _ hx' (Subgroup.inv_mem _ (Subgroup.zpow_mem_zpowers x j))
  rw [h.inf_eq_bot, Subgroup.mem_bot] at hmem
  have hsi : w * s ^ i = s ^ i * w := by
    have h3 : w * s ^ i * w⁻¹ = s ^ i := inv_mul_eq_one.mp hmem
    calc w * s ^ i = w * s ^ i * w⁻¹ * w := by group
      _ = s ^ i * w := by rw [h3]
  have hxj : w * x ^ j = x ^ j * w := by
    have h3 : (w * x ^ j * w⁻¹) * (x ^ j)⁻¹ = 1 := by rw [← e, hmem]
    have h4 : w * x ^ j * w⁻¹ = x ^ j := mul_inv_eq_one.mp h3
    calc w * x ^ j = w * x ^ j * w⁻¹ * w := by group
      _ = x ^ j * w := by rw [h4]
  have h1 := mem_zpowers_pow_orderOf hw3 h.pow_s hws (h.faithful_s hw)
    (Subgroup.zpow_mem_zpowers s i) hsi
  have h2 := mem_zpowers_pow_orderOf hw3 h.pow_x hwx (h.faithful_x hw)
    (Subgroup.zpow_mem_zpowers x j) hxj
  exact Subgroup.mul_mem _ (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) h1)
    (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) h2)

theorem mul_orderOf_le_card (h : MhoHyp r s x a) :
    orderOf s * orderOf x ≤ Nat.card (Subgroup.closure ({s, x} : Set G)) := by
  have hsK : s ∈ Subgroup.closure ({s, x} : Set G) := Subgroup.subset_closure (by simp)
  have hxK : x ∈ Subgroup.closure ({s, x} : Set G) := Subgroup.subset_closure (by simp)
  let f : Subgroup.zpowers s × Subgroup.zpowers x → Subgroup.closure ({s, x} : Set G) :=
    fun p => ⟨p.1 * p.2, Subgroup.mul_mem _ (Subgroup.zpowers_le.mpr hsK p.1.2)
      (Subgroup.zpowers_le.mpr hxK p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨u, v⟩ ⟨u', v'⟩ huv
    have e : (u : G) * v = u' * v' := congrArg Subtype.val huv
    have h1 : (u' : G)⁻¹ * u = v' * (v : G)⁻¹ := by
      calc (u' : G)⁻¹ * u = (u' : G)⁻¹ * (u * v) * (v : G)⁻¹ := by group
        _ = (u' : G)⁻¹ * (u' * v') * (v : G)⁻¹ := by rw [e]
        _ = v' * (v : G)⁻¹ := by group
    have h2 : (u' : G)⁻¹ * u ∈ Subgroup.zpowers s ⊓ Subgroup.zpowers x := by
      refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ u'.2) u.2, ?_⟩
      rw [h1]
      exact Subgroup.mul_mem _ v'.2 (Subgroup.inv_mem _ v.2)
    rw [h.inf_eq_bot, Subgroup.mem_bot] at h2
    have hu : (u : G) = u' := (inv_mul_eq_one.mp h2).symm
    have hv : (v : G) = v' := by
      rw [hu] at e
      exact mul_left_cancel e
    exact Prod.ext (Subtype.ext hu) (Subtype.ext hv)
  calc orderOf s * orderOf x = Nat.card (Subgroup.zpowers s × Subgroup.zpowers x) := by
        rw [Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers]
    _ ≤ Nat.card (Subgroup.closure ({s, x} : Set G)) := Nat.card_le_card_of_injective f hf

theorem eq_one_of_card_le (h : MhoHyp r s x a) {w₁ w₂ v₁ v₂ : G} (hw₂ : w₂ ∈ Subgroup.zpowers r)
    (hv₁ : v₁ ∈ Subgroup.closure ({s, x} : Set G)) (hv₂ : v₂ ∈ Subgroup.closure ({s, x} : Set G))
    (hy : w₁ * v₁ * (w₂ * v₂) = w₂ * v₂ * (w₁ * v₁)) (hw : w₁ ∈ Subgroup.zpowers w₂)
    (hcard : Nat.card (Subgroup.closure ({s, x} : Set G)) ≤
      Nat.card (Subgroup.closure ({w₁ * v₁, w₂ * v₂} : Set G))) : w₂ = 1 := by
  by_contra hne
  set V := Subgroup.closure ({s, x} : Set G) with hV
  set V' := Subgroup.closure ({w₁ * v₁, w₂ * v₂} : Set G) with hV'
  set N := orderOf w₂ with hNdef
  have hw₂3 := exists_pow_three_pow_of_mem_zpowers h.pow_r hw₂
  have hN0 : 0 < N := orderOf_pos_iff.mpr (isOfFinOrder_of_finite w₂)
  have hN1 : N ≠ 1 := fun h1 => hne (orderOf_eq_one_iff.mp h1)
  have hw₂N : w₂ ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.zpowers_le.mpr h.r_mem_normalizer_V hw₂
  have hy₂N : (w₂ * v₂) ^ N ∈ V := by
    have := inv_pow_mul_pow_mem hw₂N hv₂ N
    rwa [pow_orderOf_eq_one, inv_one, one_mul] at this
  obtain ⟨m, hm⟩ : ∃ m : ℕ, w₂ ^ m = w₁ :=
    (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hw)
  have hm' : ((w₂ * v₂) ^ m)⁻¹ * (w₁ * v₁) ∈ V := by
    have h1 := inv_pow_mul_pow_mem hw₂N hv₂ m
    have e : ((w₂ * v₂) ^ m)⁻¹ * (w₁ * v₁) = ((w₂ ^ m)⁻¹ * (w₂ * v₂) ^ m)⁻¹ * v₁ := by
      rw [← hm]
      group
    rw [e]
    exact V.mul_mem (V.inv_mem h1) hv₁
  have hbound := card_closure_le_mul_card_inf hy hN0 hy₂N hm'
  have hinf : V ⊓ V' ≤ Subgroup.closure ({s ^ N, x ^ N} : Set G) := by
    rintro u ⟨huV, huV'⟩
    apply h.mem_closure_pow_of_commute hw₂ huV
    have hu2 : u * (w₂ * v₂) = (w₂ * v₂) * u :=
      commute_of_mem_closure_pair hy huV' (Subgroup.subset_closure (by simp))
    have huv : u * v₂ = v₂ * u := commute_of_mem_closure_pair h.commute_s_x huV hv₂
    have hw2 : w₂ = (w₂ * v₂) * v₂⁻¹ := by group
    calc w₂ * u = (w₂ * v₂) * v₂⁻¹ * u := by rw [← hw2]
      _ = (w₂ * v₂) * (v₂⁻¹ * u) := by rw [mul_assoc]
      _ = (w₂ * v₂) * (u * v₂⁻¹) := by
          rw [show v₂⁻¹ * u = u * v₂⁻¹ by
            calc v₂⁻¹ * u = v₂⁻¹ * (u * v₂) * v₂⁻¹ := by group
              _ = v₂⁻¹ * (v₂ * u) * v₂⁻¹ := by rw [huv]
              _ = u * v₂⁻¹ := by group]
      _ = u * (w₂ * v₂) * v₂⁻¹ := by rw [← mul_assoc, ← hu2]
      _ = u * w₂ := by rw [mul_assoc, mul_assoc, mul_inv_cancel, mul_one]
  have hsN : N * orderOf (s ^ N) = orderOf s := by
    have hd := orderOf_dvd_orderOf_of_faithful hw₂3 h.pow_s
      (Subgroup.zpowers_le.mpr h.r_mem_normalizer_s hw₂) (h.faithful_s hw₂)
    rw [orderOf_pow_of_dvd hN0.ne' hd, Nat.mul_div_cancel' hd]
  have hxN : N * orderOf (x ^ N) = orderOf x := by
    have hd := orderOf_dvd_orderOf_of_faithful hw₂3 h.pow_x
      (Subgroup.zpowers_le.mpr h.r_mem_normalizer_x hw₂) (h.faithful_x hw₂)
    rw [orderOf_pow_of_dvd hN0.ne' hd, Nat.mul_div_cancel' hd]
  have hcomm : s ^ N * x ^ N = x ^ N * s ^ N := ((Commute.pow_pow h.commute_s_x) N N).eq
  have h1 : Nat.card V' ≤ N * (orderOf (s ^ N) * orderOf (x ^ N)) :=
    hbound.trans (Nat.mul_le_mul_left N
      ((Subgroup.card_le_of_le hinf).trans (card_closure_pair_le_mul hcomm)))
  have h2 : N * Nat.card V' ≤ 1 * Nat.card V' := by
    calc N * Nat.card V' ≤ N * (N * (orderOf (s ^ N) * orderOf (x ^ N))) :=
          Nat.mul_le_mul_left N h1
      _ = (N * orderOf (s ^ N)) * (N * orderOf (x ^ N)) := by ring
      _ = orderOf s * orderOf x := by rw [hsN, hxN]
      _ ≤ Nat.card V := h.mul_orderOf_le_card
      _ ≤ Nat.card V' := hcard
      _ = 1 * Nat.card V' := (one_mul _).symm
  have h3 := Nat.le_of_mul_le_mul_right h2 Nat.card_pos
  omega

theorem normalizer_le (h : MhoHyp r s x a) :
    Subgroup.normalizer ((Subgroup.closure {r, x, s} : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure {s, x} : Subgroup G) : Set G) := by
  intro g hg
  set V := Subgroup.closure ({s, x} : Set G) with hV
  have hsV : s ∈ V := Subgroup.subset_closure (by simp)
  have hxV : x ∈ V := Subgroup.subset_closure (by simp)
  have hVR : V ≤ Subgroup.closure ({r, x, s} : Set G) := by
    rw [hV, Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl <;> exact Subgroup.subset_closure (by simp)
  have hys := (Subgroup.mem_normalizer_iff.mp hg _).mp (hVR hsV)
  have hyx := (Subgroup.mem_normalizer_iff.mp hg _).mp (hVR hxV)
  obtain ⟨w₁, hw₁, v₁, hv₁, he₁⟩ := h.exists_mul_of_mem hys
  obtain ⟨w₂, hw₂, v₂, hv₂, he₂⟩ := h.exists_mul_of_mem hyx
  have hmap : V.map (MulAut.conj g).toMonoidHom =
      Subgroup.closure ({w₁ * v₁, w₂ * v₂} : Set G) := by
    rw [hV, MonoidHom.map_closure, Set.image_pair, ← he₁, ← he₂]
    rfl
  have hcard : Nat.card (V.map (MulAut.conj g).toMonoidHom) = Nat.card V :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hcomm : w₁ * v₁ * (w₂ * v₂) = w₂ * v₂ * (w₁ * v₁) := by
    rw [← he₁, ← he₂]
    calc g * s * g⁻¹ * (g * x * g⁻¹) = g * (s * x) * g⁻¹ := by group
      _ = g * (x * s) * g⁻¹ := by rw [h.commute_s_x]
      _ = g * x * g⁻¹ * (g * s * g⁻¹) := by group
  have hw : w₁ = 1 ∧ w₂ = 1 := by
    rcases mem_zpowers_or_mem_zpowers h.pow_r hw₁ hw₂ with h12 | h21
    · have h2 := h.eq_one_of_card_le hw₂ hv₁ hv₂ hcomm h12 (by rw [← hmap, hcard])
      refine ⟨?_, h2⟩
      rw [h2, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at h12
      exact h12
    · have h1 := h.eq_one_of_card_le hw₁ hv₂ hv₁ hcomm.symm h21
        (by rw [Set.pair_comm (w₂ * v₂) (w₁ * v₁), ← hmap, hcard])
      refine ⟨h1, ?_⟩
      rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at h21
      exact h21
  obtain ⟨rfl, rfl⟩ := hw
  have hle : V.map (MulAut.conj g).toMonoidHom ≤ V := by
    rw [hmap, Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · simpa using hv₁
    · simpa using hv₂
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge hle hcard.ge)

end MhoHyp

end Mho

section Data

variable {G : Type} [Group G] [Finite G]
variable {A : Subgroup G} {c : G} {L : Subgroup G} {a : G} {R Y : Subgroup G} {d x s r g : G}

omit [Finite G] in
theorem A_le_R [Finite G] (h : Sec9.Hyp91 G A c L a R) : A ≤ R := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
    Subgroup.normalizer (A : Set G) with hK
  have hAe := h.mem_partTwoF.1
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hAK : A ≤ K := by
    refine le_inf (fun y hy => Subgroup.centralizer_le_normalizer _ ?_) Subgroup.le_normalizer
    rw [← GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers]
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm y hy c h.mem_A)
  have hA3 : IsPGroup 3 A := fun y => ⟨1, Subtype.ext (by simpa using hAe.2 y y.2)⟩
  have hN : (Subgroup.comap K.subtype A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAK).mpr inf_le_right
  obtain ⟨Q, hQ⟩ := h.isSylowOf_inf
  have hle := @IsPGroup.le_sylow_of_normal 3 K _ _ hN (hA3.comap_subtype (K := K)) Q
  intro y hy
  have h1 : (⟨y, hAK hy⟩ : K) ∈ (Q : Subgroup K) := hle (Subgroup.mem_subgroupOf.mpr hy)
  have h2 : y ∈ (Q : Subgroup K).map K.subtype := ⟨_, h1, rfl⟩
  rw [hQ] at h2
  exact h2.1

theorem d_mem (h : Sec11Data G A c L a R Y d x s r g) : d ∈ A ∧ d ∈ L ∧ d ^ 3 = 1 := by
  have hd : d ∈ A ⊓ L := by
    rw [h.inf_eq]
    exact Subgroup.mem_zpowers d
  exact ⟨hd.1, hd.2, h.mem_partTwoF.1.2 d hd.1⟩

theorem d_mem_zpowers_x (h : Sec11Data G A c L a R Y d x s r g) : d ∈ Subgroup.zpowers x := by
  obtain ⟨hdA, hdL, -⟩ := d_mem h
  rw [← h.inf_L_eq]
  exact ⟨A_le_R h.toHyp91 hdA, hdL⟩

theorem orderOf_c_d (h : Sec11Data G A c L a R Y d x s r g) : orderOf c = 3 ∧ orderOf d = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, hd1⟩ := h.toSec11Std.not_mem_facts h.inf_eq h.closure_eq
  exact ⟨orderOf_eq_prime (h.mem_partTwoF.1.2 c h.mem_A) h.ne_one,
    orderOf_eq_prime (d_mem h).2.2 hd1⟩

theorem inf_zpowers_eq_bot (h : Sec11Data G A c L a R Y d x s r g) :
    Subgroup.zpowers s ⊓ Subgroup.zpowers x = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hzs, hzx⟩
  rw [Subgroup.mem_bot]
  have hzRC : z ∈ R ⊓ Sec4.thetaQuotCentralizer L := by
    rw [h.inf_centralizer_eq]
    exact hzs
  have hzRL : z ∈ R ⊓ L := by
    rw [h.inf_L_eq]
    exact hzx
  have hθ := mem_theta_of_mem_thetaQuotCentralizer (center_eq_bot_of_isList1016 h.isList1016)
    hzRL.2 hzRC.2
  exact eq_one_of_mem_R_of_mem_theta h.isSylowOf.isPGroup hzRL.1 ⟨⟨z, hzRL.2⟩, hθ, rfl⟩

theorem mem_normalizer_zpowers_s (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g)
    {y : G} (hy : y ∈ R) : y ∈ Subgroup.normalizer (Subgroup.zpowers s : Set G) := by
  have hRL := (Item1116Proof.le_centralizer_and_normalizer h45 h).2
  rw [← h.inf_centralizer_eq]
  exact Item1116Proof.mem_normalizer_inf (Subgroup.le_normalizer hy)
    (Sec6.normalizer_le_normalizer_thetaQuotCentralizer L (hRL hy))

theorem mem_normalizer_zpowers_x (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g)
    {y : G} (hy : y ∈ R) : y ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
  have hRL := (Item1116Proof.le_centralizer_and_normalizer h45 h).2
  rw [← h.inf_L_eq]
  exact Item1116Proof.mem_normalizer_inf (Subgroup.le_normalizer hy) (hRL hy)

theorem not_commute_a_x (h : Sec11Data G A c L a R Y d x s r g) : a * x ≠ x * a := by
  intro hax
  apply Item1116Proof.not_le_centralizer_of_isSylowOf h.toSec11Std h.toSec11Std.isSylowOf_inf_L
  rw [h.inf_L_eq, Subgroup.zpowers_le]
  exact Subgroup.mem_centralizer_singleton_iff.mpr hax.symm

theorem mhoHyp (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g)
    (ha : a ∈ Subgroup.zpowers r) (hsa : s * a ≠ a * s) : MhoHyp r s x a where
  commute_s_x := h.commute_s_x
  inf_eq_bot := inf_zpowers_eq_bot h
  r_mem_normalizer_s := mem_normalizer_zpowers_s h45 h (Item1116Proof.mem_R h).1
  r_mem_normalizer_x := mem_normalizer_zpowers_x h45 h (Item1116Proof.mem_R h).1
  pow_r := Item1116Proof.exists_pow_eq_one_of_mem h (Item1116Proof.mem_R h).1
  pow_s := Item1116Proof.exists_pow_eq_one_of_mem h (Item1116Proof.mem_R h).2.2
  pow_x := Item1116Proof.exists_pow_eq_one_of_mem h (Item1116Proof.mem_R h).2.1
  a_mem := ha
  a_ne_one := h.a_ne_one
  a_cube := h.mem_partTwoF.1.2 a h.a_mem
  not_commute_s := fun e => hsa e.symm
  not_commute_x := not_commute_a_x h

theorem g_mem_normalizer_V (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g)
    (ha : a ∈ Subgroup.zpowers r) (hsa : s * a ≠ a * s) :
    g ∈ Subgroup.normalizer ((Subgroup.closure {s, x} : Subgroup G) : Set G) := by
  refine (mhoHyp h45 h ha hsa).normalizer_le ?_
  rw [← h.R_eq]
  exact h.g_mem_normalizer

theorem commutator_le_V (h : Sec11Data G A c L a R Y d x s r g) (hrg : r * g = g * r)
    (hRV : R ≤ Subgroup.normalizer ((Subgroup.closure {s, x} : Subgroup G) : Set G))
    (hgV : g ∈ Subgroup.normalizer ((Subgroup.closure {s, x} : Subgroup G) : Set G)) :
    ⁅sec11P R g, sec11P R g⁆ ≤ Subgroup.closure {s, x} := by
  set V := Subgroup.closure ({s, x} : Set G) with hVdef
  obtain ⟨hrR, -, -⟩ := Item1116Proof.mem_R h
  have hsV : s ∈ V := Subgroup.subset_closure (by simp)
  have hxV : x ∈ V := Subgroup.subset_closure (by simp)
  have hPT : sec11P R g ≤ Subgroup.closure {r, g, s, x} := by
    refine sup_le ?_ ?_
    · rw [h.R_eq, Subgroup.closure_le]
      rintro y (rfl | rfl | rfl) <;> exact Subgroup.subset_closure (by simp)
    · rw [Subgroup.zpowers_le]
      exact Subgroup.subset_closure (by simp)
  have hTN : ∀ y ∈ ({r, g, s, x} : Set G), y ∈ Subgroup.normalizer (V : Set G) := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy | hy | hy <;> rw [hy]
    exacts [hRV hrR, hgV, Subgroup.le_normalizer hsV, Subgroup.le_normalizer hxV]
  refine (Subgroup.commutator_mono hPT hPT).trans (commutator_closure_le ?_ ?_)
  · rw [Subgroup.closure_le]
    exact hTN
  · have hrg' : ⁅r, g⁆ = 1 := by rw [commutatorElement_eq_one_iff_mul_comm, hrg]
    have hgr' : ⁅g, r⁆ = 1 := by rw [commutatorElement_eq_one_iff_mul_comm, hrg]
    intro y hy z hz
    have hyN := hTN y hy
    have hzN := hTN z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy hz
    rcases hy with hy | hy | hy | hy
    · rcases hz with hz | hz | hz | hz
      · rw [hy, hz, commutatorElement_self]
        exact V.one_mem
      · rw [hy, hz, hrg']
        exact V.one_mem
      · exact commutator_mem_of_mem_right hyN (by rw [hz]; exact hsV)
      · exact commutator_mem_of_mem_right hyN (by rw [hz]; exact hxV)
    · rcases hz with hz | hz | hz | hz
      · rw [hy, hz, hgr']
        exact V.one_mem
      · rw [hy, hz, commutatorElement_self]
        exact V.one_mem
      · exact commutator_mem_of_mem_right hyN (by rw [hz]; exact hsV)
      · exact commutator_mem_of_mem_right hyN (by rw [hz]; exact hxV)
    · exact commutator_mem_of_mem_left (by rw [hy]; exact hsV) hzN
    · exact commutator_mem_of_mem_left (by rw [hy]; exact hxV) hzN

theorem comm_s_a_mem (h113 : Item113) (h : Sec11Data G A c L a R Y d x s r g) :
    s * a * s⁻¹ * a⁻¹ ∈ Subgroup.zpowers c := by
  have hsA := h.R_le_normalizer_A h113 (Item1116Proof.mem_R h).2.2
  have h1 : s * a * s⁻¹ * a⁻¹ ∈ A :=
    A.mul_mem ((Subgroup.mem_normalizer_iff.mp hsA a).mp h.a_mem) (A.inv_mem h.a_mem)
  have hsC : s ∈ Sec4.thetaQuotCentralizer L := by
    have h2 : s ∈ R ⊓ Sec4.thetaQuotCentralizer L := by
      rw [h.inf_centralizer_eq]
      exact Subgroup.mem_zpowers s
    exact h2.2
  have h2 : a * s⁻¹ * a⁻¹ ∈ Sec4.thetaQuotCentralizer L :=
    (Subgroup.mem_normalizer_iff.mp (Sec6.normalizer_le_normalizer_thetaQuotCentralizer L
      h.toHyp81.a_mem_normalizer) _).mp (Subgroup.inv_mem _ hsC)
  have h3 : s * a * s⁻¹ * a⁻¹ ∈ Sec4.thetaQuotCentralizer L := by
    have e : s * a * s⁻¹ * a⁻¹ = s * (a * s⁻¹ * a⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hsC h2
  have h4 := mem_sectionCentralizer_of_mem_thetaQuotCentralizer h1 h3
  rw [h.sectionCentralizer_eq] at h4
  exact h4

theorem c_mem_commutator (h113 : Item113) (h : Sec11Data G A c L a R Y d x s r g)
    (hsa : s * a ≠ a * s) : c ∈ ⁅sec11P R g, sec11P R g⁆ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz := comm_s_a_mem h113 h
  have hz1 : s * a * s⁻¹ * a⁻¹ ≠ 1 := by
    intro h1
    apply hsa
    calc s * a = (s * a * s⁻¹ * a⁻¹) * (a * s) := by group
      _ = a * s := by rw [h1, one_mul]
  have hc3 := (orderOf_c_d h).1
  have hz3 : (s * a * s⁻¹ * a⁻¹) ^ 3 = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hc3,
      pow_orderOf_eq_one, one_zpow]
  have hcz : c ∈ Subgroup.zpowers (s * a * s⁻¹ * a⁻¹) :=
    mem_zpowers_of_orderOf_dvd (Subgroup.mem_zpowers c) hz
      (by rw [hc3, orderOf_eq_prime hz3 hz1])
  have hsP : s ∈ sec11P R g := le_sup_left (a := R) (Item1116Proof.mem_R h).2.2
  have haP : a ∈ sec11P R g := le_sup_left (a := R) (A_le_R h.toHyp91 h.a_mem)
  have hzP : s * a * s⁻¹ * a⁻¹ ∈ ⁅sec11P R g, sec11P R g⁆ :=
    Subgroup.commutator_mem_commutator hsP haP
  exact Subgroup.zpowers_le.mpr hzP hcz

theorem d_mem_commutator (h : Sec11Data G A c L a R Y d x s r g)
    (hc : c ∈ ⁅sec11P R g, sec11P R g⁆) : d ∈ ⁅sec11P R g, sec11P R g⁆ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hdA, -, hd3⟩ := d_mem h
  have hcA := h.mem_A
  have hc3 : c ^ 3 = 1 := h.mem_partTwoF.1.2 c hcA
  have hcd : c * d = d * c :=
    congrArg Subtype.val (h.mem_partTwoF.1.1.is_comm.comm ⟨c, hcA⟩ ⟨d, hdA⟩)
  obtain ⟨i, j, -, hj, hij⟩ := KFacts.exists_pow_mul_pow_of_mem_closure_pair hcd hc3 hd3 h.conj_mem
  have hj0 : j ≠ 0 := by
    rintro rfl
    apply h.g_not_mem
    apply Sec10.mem_normalizer_zpowers_of_conj_mem
    rw [hij, pow_zero, mul_one]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers c) i
  have hcP : c ∈ sec11P R g := le_sup_left (a := R) (c_mem_of_hyp91 h.toHyp91)
  have hgP : g ∈ sec11P R g :=
    (le_sup_right : Subgroup.zpowers g ≤ sec11P R g) (Subgroup.mem_zpowers g)
  have hgc : g * c * g⁻¹ * c⁻¹ ∈ ⁅sec11P R g, sec11P R g⁆ :=
    Subgroup.commutator_mem_commutator hgP hcP
  have hdj : d ^ j ∈ ⁅sec11P R g, sec11P R g⁆ := by
    have e : d ^ j = (c ^ i)⁻¹ * (g * c * g⁻¹ * c⁻¹) * c := by
      calc d ^ j = (c ^ i)⁻¹ * (c ^ i * d ^ j) := by group
        _ = (c ^ i)⁻¹ * (g * c * g⁻¹) := by rw [hij]
        _ = (c ^ i)⁻¹ * (g * c * g⁻¹ * c⁻¹) * c := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ hc i)) hgc)
      hc
  have hdj3 : (d ^ j) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hd3, one_pow]
  have hdj1 : d ^ j ≠ 1 := by
    intro h1
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [(orderOf_c_d h).2] at h2
    omega
  have hd : d ∈ Subgroup.zpowers (d ^ j) :=
    mem_zpowers_of_orderOf_dvd (Subgroup.mem_zpowers d)
      (Subgroup.pow_mem _ (Subgroup.mem_zpowers d) j)
      (by rw [(orderOf_c_d h).2, orderOf_eq_prime hdj3 hdj1])
  exact Subgroup.zpowers_le.mpr hdj hd

theorem mem_closure_c_d (h : Sec11Data G A c L a R Y d x s r g) {y : G}
    (hy : y ∈ Subgroup.closure ({s, x} : Set G)) (hy3 : y ^ 3 = 1) :
    y ∈ Subgroup.closure ({c, d} : Set G) := by
  obtain ⟨i, j, rfl⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair h.commute_s_x hy
  have hc : Commute (s ^ i) (x ^ j) := Commute.zpow_zpow h.commute_s_x i j
  have h1 : (s ^ i) ^ 3 * (x ^ j) ^ 3 = 1 := by
    rw [← hc.mul_pow]
    exact hy3
  have h2 : (s ^ i) ^ 3 ∈ Subgroup.zpowers s ⊓ Subgroup.zpowers x := by
    refine ⟨Subgroup.pow_mem _ (Subgroup.zpow_mem_zpowers s i) 3, ?_⟩
    rw [eq_inv_of_mul_eq_one_left h1]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.zpow_mem_zpowers x j) 3)
  rw [inf_zpowers_eq_bot h, Subgroup.mem_bot] at h2
  have h3 : (x ^ j) ^ 3 = 1 := by
    rw [h2, one_mul] at h1
    exact h1
  obtain ⟨hc3, hd3⟩ := orderOf_c_d h
  have hsi : s ^ i ∈ Subgroup.zpowers c :=
    mem_zpowers_of_orderOf_dvd (Subgroup.zpow_mem_zpowers s i) h.c_mem_zpowers_s
      (by rw [hc3]; exact orderOf_dvd_of_pow_eq_one h2)
  have hxj : x ^ j ∈ Subgroup.zpowers d :=
    mem_zpowers_of_orderOf_dvd (Subgroup.zpow_mem_zpowers x j) (d_mem_zpowers_x h)
      (by rw [hd3]; exact orderOf_dvd_of_pow_eq_one h3)
  exact Subgroup.mul_mem _ (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hsi)
    (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hxj)

theorem normalizer_P_le_cd (h113 : Item113) (h : Sec11Data G A c L a R Y d x s r g)
    (hPP : ⁅sec11P R g, sec11P R g⁆ ≤ Subgroup.closure {s, x}) (hsa : s * a ≠ a * s) :
    Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G) := by
  intro n hn
  have hc := c_mem_commutator h113 h hsa
  have hd := d_mem_commutator h hc
  have hcdQ : Subgroup.closure ({c, d} : Set G) ≤ ⁅sec11P R g, sec11P R g⁆ := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy <;> rw [hy]
    exacts [hc, hd]
  have hnQ : n ∈ Subgroup.normalizer ((⁅sec11P R g, sec11P R g⁆ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hn ⊢
    rw [Subgroup.map_commutator, hn]
  have hcdA : Subgroup.closure ({c, d} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy <;> rw [hy]
    exacts [h.mem_A, (d_mem h).1]
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  apply mem_closure_c_d h (hPP ((Subgroup.mem_normalizer_iff.mp hnQ z).mp (hcdQ hz)))
  rw [conj_pow, h.mem_partTwoF.1.2 z (hcdA hz), mul_one, mul_inv_cancel]

theorem W_le_normalizer_d (h117 : Item117) (h : Sec11Data G A c L a R Y d x s r g) :
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) :=
  (h117 G A c L a R Y h.toSec11Std d h.inf_eq (Subgroup.zpowers d)
    (Subgroup.zpowers_le.mpr (d_mem h).1) (by rw [Nat.card_zpowers, (orderOf_c_d h).2])).mpr rfl

theorem normalizer_P_le_d (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g)
    (hcdN : Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G))
    (htrans : ∀ F : Subgroup G, F ≤ Subgroup.closure {c, d} →
      Nat.card F = Nat.card (Subgroup.zpowers c) → F ≠ Subgroup.zpowers d →
        ∃ p ∈ sec11P R g, F = (Subgroup.zpowers c).map (MulAut.conj p).toMonoidHom) :
    Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers d : Set G) := by
  intro n hn
  have hPd : sec11P R g ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) := by
    refine sup_le ((h.R_le_normalizer_A h113).trans (W_le_normalizer_d h117 h)) ?_
    rw [Subgroup.zpowers_le]
    exact W_le_normalizer_d h117 h h.g_mem.2
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  by_contra hne
  have hD'cd : (Subgroup.zpowers d).map (MulAut.conj n).toMonoidHom ≤
      Subgroup.closure {c, d} := by
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
    exact (Subgroup.mem_normalizer_iff.mp (hcdN hn) d).mp (Subgroup.subset_closure (by simp))
  have hD'card : Nat.card ((Subgroup.zpowers d).map (MulAut.conj n).toMonoidHom) =
      Nat.card (Subgroup.zpowers c) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj n).injective, Nat.card_zpowers,
      Nat.card_zpowers, (orderOf_c_d h).1, (orderOf_c_d h).2]
  obtain ⟨p, hp, hpD⟩ := htrans _ hD'cd hD'card hne
  have hpN : p⁻¹ * n ∈ Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer hp)) hn
  have hc : (Subgroup.zpowers d).map (MulAut.conj (p⁻¹ * n)).toMonoidHom =
      Subgroup.zpowers c := by
    rw [← map_conj_map_conj, hpD, map_conj_map_conj, inv_mul_cancel, map_one]
    ext y
    simp
  have hPc := le_normalizer_map_conj hpN hPd
  rw [hc] at hPc
  exact h.g_not_mem
    (hPc ((le_sup_right : Subgroup.zpowers g ≤ sec11P R g) (Subgroup.mem_zpowers g)))

theorem false_of_mem_zpowers (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) (ha : a ∈ Subgroup.zpowers r)
    (hrg : r * g = g * r) (hsa : s * a ≠ a * s) : False := by
  have hgV := g_mem_normalizer_V h45 h ha hsa
  have hRV := h.R_le_normalizer_V h45
  have hPP := commutator_le_V h hrg hRV hgV
  have hcdN := normalizer_P_le_cd h113 h hPP hsa
  have htrans := h.htrans_of_mem_normalizer (W_le_normalizer_d h117 h h.g_mem.2)
  have hNd := normalizer_P_le_d h113 h117 h hcdN htrans
  exact rank3II_11_15_of h hrg h.commute_s_x hRV hgV (h.normalizer_P_le_normalizer_V h45 h113)
    (h.commutator_mem_V h45 h113 outAbelian1016 (Item1116Proof.mem_R h).1) h.r_not_mem_V hcdN
    hNd htrans

theorem not_yNotField (h45 : Sec4.Item4_5) (h113 : Item113)
    (h : Sec11Data G A c L a R Y d x s r g) (hf : KFacts.InducesStdKind Y c .field)
    (hsa : s * a ≠ a * s) {e : G} (he : e ∈ Subgroup.closure ({a, c} : Set G))
    (hec : e ∉ Subgroup.zpowers c) : ¬ YNotField c L e := by
  rintro ⟨Ye, hYe, hKe, hnf⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe := h.mem_partTwoF.1
  have ha3 : a ^ 3 = 1 := hAe.2 a h.a_mem
  have hc3 : c ^ 3 = 1 := hAe.2 c h.mem_A
  have hac : a * c = c * a := congrArg Subtype.val (hAe.1.is_comm.comm ⟨a, h.a_mem⟩ ⟨c, h.mem_A⟩)
  have hRc := le_centralizer_of_le_normalizer_zpowers (orderOf_c_d h).1 h.isSylowOf.isPGroup
    h.isSylowOf.le
  have hsR := (Item1116Proof.mem_R h).2.2
  have hsc : s * c = c * s := Subgroup.mem_centralizer_singleton_iff.mp (hRc hsR)
  have hsL := (Item1116Proof.le_centralizer_and_normalizer h45 h).2 hsR
  obtain ⟨k, hk⟩ : ∃ k : ℕ, c ^ k = s * a * s⁻¹ * a⁻¹ :=
    (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr (comm_s_a_mem h113 h))
  have hacC : Commute a c := hac
  have hsk : s * a * s⁻¹ = a * c ^ ((k : ℕ) : ℤ) := by
    rw [zpow_natCast, (hacC.pow_right k).eq, hk]
    group
  have hk3 : k % 3 ≠ 0 := by
    intro hk0
    apply hsa
    have hck : c ^ k = 1 := by
      rw [← Nat.mod_add_div k 3, hk0, zero_add, pow_mul, hc3, one_pow]
    have h1 : s * a * s⁻¹ * a⁻¹ = 1 := by rw [← hk, hck]
    calc s * a = s * a * s⁻¹ * a⁻¹ * (a * s) := by group
      _ = a * s := by rw [h1, one_mul]
  obtain ⟨i, j, hi, -, hij⟩ := KFacts.exists_pow_mul_pow_of_mem_closure_pair hac ha3 hc3 he
  have hi0 : i ≠ 0 := by
    rintro rfl
    apply hec
    rw [hij, pow_zero, one_mul]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers c) j
  have hconj := conj_zpow_eq_of_conj_eq hac hsc hsk (i * j * k)
  have hpow : e ^ i = s ^ (i * j * k) * a * (s ^ (i * j * k))⁻¹ := by
    have ha' : a ^ (i * i) = a := by
      have h1 : (i * i) % 3 = 1 := by
        rcases (by omega : i = 1 ∨ i = 2) with rfl | rfl <;> rfl
      rw [← Nat.mod_add_div (i * i) 3, h1, pow_add, pow_mul, ha3, one_pow, mul_one, pow_one]
    have hc' : c ^ (j * i) = c ^ (((i * j * k : ℕ) : ℤ) * ((k : ℕ) : ℤ)) := by
      rw [← Int.natCast_mul, zpow_natCast]
      have hkk : (k * k) % 3 = 1 := by
        rcases (by omega : k % 3 = 1 ∨ k % 3 = 2) with h1 | h1 <;> rw [Nat.mul_mod, h1]
      have hmod : (i * j * k * k) % 3 = (j * i) % 3 := by
        calc (i * j * k * k) % 3 = (i * j * (k * k)) % 3 := by rw [mul_assoc (i * j)]
          _ = ((i * j) % 3 * ((k * k) % 3)) % 3 := Nat.mul_mod _ _ _
          _ = (j * i) % 3 := by rw [hkk, mul_one, Nat.mod_mod, mul_comm]
      rw [← Nat.mod_add_div (j * i) 3, ← Nat.mod_add_div (i * j * k * k) 3, hmod, pow_add,
        pow_add, pow_mul, pow_mul, hc3, one_pow, one_pow]
    rw [hconj, hij, (hacC.pow_pow i j).mul_pow, ← pow_mul, ← pow_mul, ha', hc']
  set u := s ^ (i * j * k) with hu
  have huc : u * c = c * u := (Commute.pow_left (show Commute s c from hsc) _).eq
  have huL : u ∈ Subgroup.normalizer (L : Set G) := Subgroup.pow_mem _ hsL _
  have he3 : e ^ 3 = 1 := by
    rw [hij]
    exact hAe.2 _ (A.mul_mem (A.pow_mem h.a_mem i) (A.pow_mem h.mem_A j))
  have he1 : e ≠ 1 := fun h1 => hec (h1 ▸ Subgroup.one_mem _)
  have hau3 : (u * a * u⁻¹) ^ 3 = 1 := by rw [conj_pow, ha3, mul_one, mul_inv_cancel]
  have hau1 : u * a * u⁻¹ ≠ 1 := by
    intro h1
    apply h.a_ne_one
    calc a = u⁻¹ * (u * a * u⁻¹) * u := by group
      _ = 1 := by rw [h1]; group
  have hau_mem : u * a * u⁻¹ ∈ Subgroup.zpowers e := by
    rw [← hpow]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers e) i
  have he_mem : e ∈ Subgroup.zpowers (u * a * u⁻¹) :=
    mem_zpowers_of_orderOf_dvd (Subgroup.mem_zpowers e) hau_mem
      (by rw [orderOf_eq_prime he3 he1, orderOf_eq_prime hau3 hau1])
  have hzp : Subgroup.zpowers (u * a * u⁻¹) = Subgroup.zpowers e :=
    le_antisymm (Subgroup.zpowers_le.mpr hau_mem) (Subgroup.zpowers_le.mpr he_mem)
  have hcent : Subgroup.centralizer ({e} : Set G) =
      Subgroup.centralizer ({u * a * u⁻¹} : Set G) := by
    rw [GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers, ← hzp,
      ← GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers]
  have hYu : Y.map (MulAut.conj u).toMonoidHom ∈ thetaComponentsAt 3 e := by
    have h1 := map_mem_thetaComponentsAt (MulAut.conj u) h.mem_thetaComponentsAt_Y
    rw [thetaComponentsAt_eq_thetaComponentsIn, MulAut.conj_apply] at h1
    rw [thetaComponentsAt_eq_thetaComponentsIn, hcent]
    exact h1
  have hKeq : sec11K L e = (sec11K L a).map (MulAut.conj u).toMonoidHom := by
    rw [← sec11K_map_conj' huL a]
    unfold sec11K
    rw [hcent, MulAut.conj_apply]
  have hKY : sec11K L e ≤ Y.map (MulAut.conj u).toMonoidHom := by
    rw [hKeq]
    exact Subgroup.map_mono h.sec11K_le
  have hK1 : sec11K L e ≠ ⊥ := by
    rw [hKeq]
    intro hbot
    have hdK := h.toSec11Std.d_mem_sec11K h.inf_eq
    obtain ⟨-, -, hd1⟩ := h.toSec11Std.not_mem_facts h.inf_eq h.closure_eq
    have h1 : (MulAut.conj u).toMonoidHom d ∈ (sec11K L a).map (MulAut.conj u).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hdK
    rw [hbot, Subgroup.mem_bot] at h1
    apply hd1
    have h2 : u * d * u⁻¹ = 1 := h1
    calc d = u⁻¹ * (u * d * u⁻¹) * u := by group
      _ = 1 := by rw [h2]; group
  have hYeq :=
    PartOne.EmbeddingFixedResidual.eq_of_perfect_le_of_mem_thetaComponentsAt Nat.prime_three
      hYe hYu hK1 (Sec6.isPerfect_inSubgroup_perfectResidual _) hKe hKY
  have hfu := KFacts.InducesStdKind.map (MulAut.conj u).toMonoidHom Y
    (KFacts.thetaQuotMap_iff_of_injective _ (MulAut.conj u).injective Y) hf
  have hcu : (MulAut.conj u).toMonoidHom c = c := by
    change u * c * u⁻¹ = c
    rw [huc, mul_inv_cancel_right]
  rw [hcu, ← hYeq] at hfu
  exact hnf hfu

end Data

end Item1115Proof

section Main

@[expose] def Item11133Field : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G)
    (a : G) (R Y : Subgroup G) (d x s r g : G), Sec11Data G A c L a R Y d x s r g →
      KFacts.InducesStdKind Y c .field → r * a = a * r →
      Subgroup.closure ({r, s} : Set G) ≠ Subgroup.closure {a, s} →
      ∀ e ∈ Subgroup.zpowers r ⊓ Subgroup.closure {a, c}, e ∉ Subgroup.zpowers c →
        YNotField c L e

end Main

end CFSG.RankThree.PartTwo.Sec11
