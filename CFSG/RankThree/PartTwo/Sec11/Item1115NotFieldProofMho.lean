module

public import CFSG.RankThree.PartTwo.Sec11.Item1115Proof

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Item1115NotFieldProof

section Mho

variable {G : Type} [Group G] [Finite G]

theorem exists_orderMod (V : Subgroup G) (w : G) :
    ∃ N : ℕ, 0 < N ∧ w ^ N ∈ V ∧ ∀ n : ℕ, w ^ n ∈ V → N ∣ n := by
  classical
  have hex : ∃ n : ℕ, 0 < n ∧ w ^ n ∈ V :=
    ⟨orderOf w, orderOf_pos_iff.mpr (isOfFinOrder_of_finite w), by
      rw [pow_orderOf_eq_one]
      exact V.one_mem⟩
  obtain ⟨hN0, hNV⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, hN0, hNV, fun n hn => ?_⟩
  apply Nat.dvd_of_mod_eq_zero
  by_contra hne
  apply Nat.find_min hex (Nat.mod_lt n hN0)
  refine ⟨Nat.pos_of_ne_zero hne, ?_⟩
  have e : w ^ (n % Nat.find hex) = ((w ^ Nat.find hex) ^ (n / Nat.find hex))⁻¹ * w ^ n := by
    rw [← pow_mul, eq_inv_mul_iff_mul_eq, ← pow_add, Nat.div_add_mod]
  rw [e]
  exact V.mul_mem (V.inv_mem (V.pow_mem hNV _)) hn

theorem mem_zpowers_pow_of_dvd {w t : G} (hw3 : ∃ k : ℕ, w ^ 3 ^ k = 1)
    (ht : ∃ k : ℕ, t ^ 3 ^ k = 1) (hwt : w ∈ Subgroup.normalizer (Subgroup.zpowers t : Set G))
    {N : ℕ} (hN : ∀ n : ℕ, w ^ n * t = t * w ^ n → N ∣ n) {y : G}
    (hy : y ∈ Subgroup.zpowers t) (hwy : w * y = y * w) : y ∈ Subgroup.zpowers (t ^ N) := by
  obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hy)
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [pow_zero]
    exact Subgroup.one_mem _
  obtain ⟨v, k', hk', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk0.ne' 3 (by norm_num)
  have htv : t ^ 3 ^ v ∈ Subgroup.zpowers (t ^ (3 ^ v * k')) := by
    have h3v : ∃ m : ℕ, (t ^ 3 ^ v) ^ 3 ^ m = 1 := by
      obtain ⟨m, hm⟩ := ht
      exact ⟨m, by rw [← pow_mul, mul_comm, pow_mul, hm, one_pow]⟩
    have := Item1116Proof.mem_zpowers_zpow_of_not_dvd h3v (i := (k' : ℤ)) (by exact_mod_cast hk')
    rwa [zpow_natCast, ← pow_mul] at this
  have hwv : w * t ^ 3 ^ v = t ^ 3 ^ v * w := by
    have hC : Subgroup.zpowers (t ^ (3 ^ v * k')) ≤ Subgroup.centralizer {w} :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hwy.symm)
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hC htv)).symm
  obtain ⟨u, hu⟩ := hN _ (Item1115Proof.commute_pow_three_pow hw3 v t hwt hwv)
  refine Subgroup.mem_zpowers_iff.mpr ⟨((u * k' : ℕ) : ℤ), ?_⟩
  rw [zpow_natCast, ← pow_mul, hu, mul_assoc]

theorem dvd_orderOf_of_dvd {w t : G} (hw3 : ∃ k : ℕ, w ^ 3 ^ k = 1)
    (ht : ∃ k : ℕ, t ^ 3 ^ k = 1) (hwt : w ∈ Subgroup.normalizer (Subgroup.zpowers t : Set G))
    {N : ℕ} (hN : ∀ n : ℕ, w ^ n * t = t * w ^ n → N ∣ n) : N ∣ orderOf t := by
  obtain ⟨m, hm⟩ := Item1115Proof.exists_orderOf_eq_three_pow ht
  have h1 : w * t ^ 3 ^ m = t ^ 3 ^ m * w := by rw [← hm, pow_orderOf_eq_one, mul_one, one_mul]
  rw [hm]
  exact hN _ (Item1115Proof.commute_pow_three_pow hw3 m t hwt h1)

omit [Finite G] in
theorem eq_and_eq_of_mul_eq {s x p q p' q' : G}
    (hinf : Subgroup.zpowers s ⊓ Subgroup.zpowers x = ⊥) (hp : p ∈ Subgroup.zpowers s)
    (hp' : p' ∈ Subgroup.zpowers s) (hq : q ∈ Subgroup.zpowers x)
    (hq' : q' ∈ Subgroup.zpowers x) (h : p * q = p' * q') : p = p' ∧ q = q' := by
  have e : p'⁻¹ * p = q' * q⁻¹ := by
    calc p'⁻¹ * p = p'⁻¹ * (p * q) * q⁻¹ := by group
      _ = p'⁻¹ * (p' * q') * q⁻¹ := by rw [h]
      _ = q' * q⁻¹ := by group
  have hmem : p'⁻¹ * p ∈ Subgroup.zpowers s ⊓ Subgroup.zpowers x := by
    refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hp') hp, ?_⟩
    rw [e]
    exact Subgroup.mul_mem _ hq' (Subgroup.inv_mem _ hq)
  rw [hinf, Subgroup.mem_bot] at hmem
  have hpp : p = p' := (inv_mul_eq_one.mp hmem).symm
  refine ⟨hpp, ?_⟩
  rw [hpp] at h
  exact mul_left_cancel h

theorem false_of_swap {s x g : G} (hsx : s * x = x * s)
    (hinf : Subgroup.zpowers s ⊓ Subgroup.zpowers x = ⊥) (hs : ∃ k : ℕ, s ^ 3 ^ k = 1)
    (hs1 : s ≠ 1) (hg : ∃ k : ℕ, g ^ 3 ^ k = 1)
    (hgs : g * s * g⁻¹ ∈ Subgroup.closure ({s ^ 3, x} : Set G))
    (hgx : g * x * g⁻¹ ∈ Subgroup.closure ({s, x ^ 3} : Set G)) : False := by
  set Vx := Subgroup.closure ({s, x ^ 3} : Set G) with hVx
  set Vs := Subgroup.closure ({s ^ 3, x} : Set G) with hVs
  have hc : Commute s x := hsx
  have hc1 : s * x ^ 3 = x ^ 3 * s := (hc.pow_right 3).eq
  have hc2 : s ^ 3 * x = x * s ^ 3 := (hc.pow_left 3).eq
  have hs3Vs : s ^ 3 ∈ Vs := Subgroup.subset_closure (by simp)
  have hxVs : x ∈ Vs := Subgroup.subset_closure (by simp)
  have hsVx : s ∈ Vx := Subgroup.subset_closure (by simp)
  have hx3Vx : x ^ 3 ∈ Vx := Subgroup.subset_closure (by simp)
  have hcubeVx : ∀ y ∈ Vx, y ^ 3 ∈ Vs := by
    intro y hy
    obtain ⟨i, j, rfl⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair hc1 hy
    have hij : Commute (s ^ i) ((x ^ 3) ^ j) := (show Commute s (x ^ 3) from hc1).zpow_zpow i j
    rw [hij.mul_pow]
    refine Vs.mul_mem ?_ (Subgroup.pow_mem _ (Subgroup.zpow_mem _ (Subgroup.pow_mem _ hxVs 3) j) 3)
    rw [← zpow_natCast, ← zpow_mul, mul_comm i, zpow_mul, zpow_natCast]
    exact Subgroup.zpow_mem _ hs3Vs i
  have hcubeVs : ∀ y ∈ Vs, y ^ 3 ∈ Vx := by
    intro y hy
    obtain ⟨i, j, rfl⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair hc2 hy
    have hij : Commute ((s ^ 3) ^ i) (x ^ j) := (show Commute (s ^ 3) x from hc2).zpow_zpow i j
    rw [hij.mul_pow]
    refine Vx.mul_mem (Subgroup.pow_mem _ (Subgroup.zpow_mem _ (Subgroup.pow_mem _ hsVx 3) i) 3) ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm j, zpow_mul, zpow_natCast]
    exact Subgroup.zpow_mem _ hx3Vx j
  have hgVx : Vx ≤ Vs.comap (MulAut.conj g).toMonoidHom := by
    rw [hVx, Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    change g * y * g⁻¹ ∈ Vs
    rcases hy with rfl | rfl
    · exact hgs
    · rw [← conj_pow]
      exact hcubeVx _ hgx
  have hgVs : Vs ≤ Vx.comap (MulAut.conj g).toMonoidHom := by
    rw [hVs, Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    change g * y * g⁻¹ ∈ Vx
    rcases hy with rfl | rfl
    · rw [← conj_pow]
      exact hcubeVs _ hgs
    · exact hgx
  have hg2 : g ^ 2 ∈ Subgroup.normalizer (Vx : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    have e : g ^ 2 * y * (g ^ 2)⁻¹ = g * (g * y * g⁻¹) * g⁻¹ := by
      rw [sq, mul_inv_rev]
      group
    rw [e]
    exact hgVs (hgVx hy)
  have hgN : g ∈ Subgroup.normalizer (Vx : Set G) := by
    have h1 : g ∈ Subgroup.zpowers (g ^ (2 : ℤ)) :=
      Item1116Proof.mem_zpowers_zpow_of_not_dvd hg (by decide)
    rw [zpow_ofNat] at h1
    exact Subgroup.zpowers_le.mpr hg2 h1
  have hsVs : s ∈ Vs := by
    have h1 : g⁻¹ * s * g ∈ Vx := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) s).mp hsVx
      rwa [inv_inv] at this
    have h2 : g * (g⁻¹ * s * g) * g⁻¹ ∈ Vs := hgVx h1
    rwa [show g * (g⁻¹ * s * g) * g⁻¹ = s by group] at h2
  obtain ⟨i, j, hij⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair hc2 hsVs
  have hp : (s ^ 3) ^ i ∈ Subgroup.zpowers s :=
    Subgroup.zpow_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers s) 3) i
  have hj := (eq_and_eq_of_mul_eq hinf hp (Subgroup.mem_zpowers s)
    (Subgroup.zpow_mem_zpowers x j) (Subgroup.one_mem _) (by rw [mul_one]; exact hij.symm)).1
  have h3 : s ^ ((3 : ℤ) * i) = s := by
    rw [zpow_mul, zpow_ofNat]
    exact hj
  have h1 : s ^ ((3 : ℤ) * i - 1) = 1 := by
    rw [zpow_sub, h3, zpow_one, mul_inv_cancel]
  have hdvd := orderOf_dvd_iff_zpow_eq_one.mpr h1
  obtain ⟨k, hk⟩ := Item1115Proof.exists_orderOf_eq_three_pow hs
  rcases k with _ | k
  · exact hs1 (orderOf_eq_one_iff.mp (by simpa using hk))
  · rw [hk] at hdvd
    have h3k : (3 : ℤ) ∣ ((3 ^ (k + 1) : ℕ) : ℤ) := by
      push_cast
      exact dvd_pow_self 3 (Nat.succ_ne_zero k)
    have := h3k.trans hdvd
    omega

structure MhoHypV (r s x e : G) : Prop where
  commute_s_x : s * x = x * s
  inf_eq_bot : Subgroup.zpowers s ⊓ Subgroup.zpowers x = ⊥
  r_mem_normalizer_s : r ∈ Subgroup.normalizer (Subgroup.zpowers s : Set G)
  r_mem_normalizer_x : r ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G)
  pow_r : ∃ k : ℕ, r ^ 3 ^ k = 1
  pow_s : ∃ k : ℕ, s ^ 3 ^ k = 1
  pow_x : ∃ k : ℕ, x ^ 3 ^ k = 1
  e_mem : e ∈ Subgroup.zpowers r
  e_cube_mem : e ^ 3 ∈ Subgroup.closure ({s, x} : Set G)
  not_commute_s : e * s ≠ s * e
  not_commute_x : e * x ≠ x * e

namespace MhoHypV

variable {r s x e : G}

omit [Finite G] in
theorem pow_e (h : MhoHypV r s x e) : ∃ k : ℕ, e ^ 3 ^ k = 1 :=
  Item1115Proof.exists_pow_three_pow_of_mem_zpowers h.pow_r h.e_mem

theorem mem_zpowers_of_not_mem (h : MhoHypV r s x e) {w : G} (hw : w ∈ Subgroup.zpowers r)
    (hwV : w ∉ Subgroup.closure ({s, x} : Set G)) : e ∈ Subgroup.zpowers w := by
  rcases Item1115Proof.mem_zpowers_or_mem_zpowers h.pow_r h.e_mem hw with hew | hwe
  · exact hew
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hwe
    refine Item1116Proof.mem_zpowers_zpow_of_not_dvd h.pow_e fun h3 => hwV ?_
    obtain ⟨t, rfl⟩ := h3
    have e3 : e ^ (3 : ℤ) = e ^ 3 := zpow_ofNat e 3
    rw [zpow_mul, e3]
    exact Subgroup.zpow_mem _ h.e_cube_mem t

theorem mem_V_of_commute_s (h : MhoHypV r s x e) {w : G} (hw : w ∈ Subgroup.zpowers r)
    (hws : w * s = s * w) : w ∈ Subgroup.closure ({s, x} : Set G) := by
  by_contra hwV
  have hC : Subgroup.zpowers w ≤ Subgroup.centralizer ({s} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hws)
  exact h.not_commute_s
    (Subgroup.mem_centralizer_singleton_iff.mp (hC (h.mem_zpowers_of_not_mem hw hwV)))

theorem mem_V_of_commute_x (h : MhoHypV r s x e) {w : G} (hw : w ∈ Subgroup.zpowers r)
    (hwx : w * x = x * w) : w ∈ Subgroup.closure ({s, x} : Set G) := by
  by_contra hwV
  have hC : Subgroup.zpowers w ≤ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hwx)
  exact h.not_commute_x
    (Subgroup.mem_centralizer_singleton_iff.mp (hC (h.mem_zpowers_of_not_mem hw hwV)))

theorem mem_closure_pow_of_commute (h : MhoHypV r s x e) {w : G} (hw : w ∈ Subgroup.zpowers r)
    {N : ℕ} (hN : ∀ n : ℕ, w ^ n ∈ Subgroup.closure ({s, x} : Set G) → N ∣ n) {v : G}
    (hv : v ∈ Subgroup.closure ({s, x} : Set G)) (hwv : w * v = v * w) :
    v ∈ Subgroup.closure ({s ^ N, x ^ N} : Set G) := by
  obtain ⟨i, j, rfl⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair h.commute_s_x hv
  have hw3 := Item1115Proof.exists_pow_three_pow_of_mem_zpowers h.pow_r hw
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
  have h1 := mem_zpowers_pow_of_dvd hw3 h.pow_s hws
    (fun n hn => hN n (h.mem_V_of_commute_s (Subgroup.pow_mem _ hw n) hn))
    (Subgroup.zpow_mem_zpowers s i) hsi
  have h2 := mem_zpowers_pow_of_dvd hw3 h.pow_x hwx
    (fun n hn => hN n (h.mem_V_of_commute_x (Subgroup.pow_mem _ hw n) hn))
    (Subgroup.zpow_mem_zpowers x j) hxj
  exact Subgroup.mul_mem _ (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) h1)
    (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) h2)

theorem r_mem_normalizer_V (h : MhoHypV r s x e) :
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

theorem exists_mul_of_mem (h : MhoHypV r s x e) {y : G}
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

theorem mul_orderOf_le_card (h : MhoHypV r s x e) :
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

theorem mem_V_of_card_le (h : MhoHypV r s x e) {w₁ w₂ v₁ v₂ : G}
    (hw₂ : w₂ ∈ Subgroup.zpowers r) (hv₁ : v₁ ∈ Subgroup.closure ({s, x} : Set G))
    (hv₂ : v₂ ∈ Subgroup.closure ({s, x} : Set G))
    (hy : w₁ * v₁ * (w₂ * v₂) = w₂ * v₂ * (w₁ * v₁)) (hw : w₁ ∈ Subgroup.zpowers w₂)
    (hcard : Nat.card (Subgroup.closure ({s, x} : Set G)) ≤
      Nat.card (Subgroup.closure ({w₁ * v₁, w₂ * v₂} : Set G))) :
    w₂ ∈ Subgroup.closure ({s, x} : Set G) := by
  by_contra hne
  set V := Subgroup.closure ({s, x} : Set G) with hV
  set V' := Subgroup.closure ({w₁ * v₁, w₂ * v₂} : Set G) with hV'
  obtain ⟨N, hN0, hNV, hNdvd⟩ := exists_orderMod V w₂
  have hN1 : N ≠ 1 := by
    rintro rfl
    rw [pow_one] at hNV
    exact hne hNV
  have hw₂N : w₂ ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.zpowers_le.mpr h.r_mem_normalizer_V hw₂
  have hy₂N : (w₂ * v₂) ^ N ∈ V := by
    have h1 := Item1115Proof.inv_pow_mul_pow_mem hw₂N hv₂ N
    have e : (w₂ * v₂) ^ N = w₂ ^ N * ((w₂ ^ N)⁻¹ * (w₂ * v₂) ^ N) := by group
    rw [e]
    exact V.mul_mem hNV h1
  obtain ⟨m, hm⟩ : ∃ m : ℕ, w₂ ^ m = w₁ :=
    (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hw)
  have hm' : ((w₂ * v₂) ^ m)⁻¹ * (w₁ * v₁) ∈ V := by
    have h1 := Item1115Proof.inv_pow_mul_pow_mem hw₂N hv₂ m
    have e : ((w₂ * v₂) ^ m)⁻¹ * (w₁ * v₁) = ((w₂ ^ m)⁻¹ * (w₂ * v₂) ^ m)⁻¹ * v₁ := by
      rw [← hm]
      group
    rw [e]
    exact V.mul_mem (V.inv_mem h1) hv₁
  have hbound := Item1115Proof.card_closure_le_mul_card_inf hy hN0 hy₂N hm'
  have hinf : V ⊓ V' ≤ Subgroup.closure ({s ^ N, x ^ N} : Set G) := by
    rintro u ⟨huV, huV'⟩
    apply h.mem_closure_pow_of_commute hw₂ hNdvd huV
    have hu2 : u * (w₂ * v₂) = (w₂ * v₂) * u :=
      Item1115Proof.commute_of_mem_closure_pair hy huV' (Subgroup.subset_closure (by simp))
    have huv : u * v₂ = v₂ * u :=
      Item1115Proof.commute_of_mem_closure_pair h.commute_s_x huV hv₂
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
  have hw₂3 := Item1115Proof.exists_pow_three_pow_of_mem_zpowers h.pow_r hw₂
  have hws : w₂ ∈ Subgroup.normalizer (Subgroup.zpowers s : Set G) :=
    Subgroup.zpowers_le.mpr h.r_mem_normalizer_s hw₂
  have hwx : w₂ ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) :=
    Subgroup.zpowers_le.mpr h.r_mem_normalizer_x hw₂
  have hsN : N * orderOf (s ^ N) = orderOf s := by
    have hd := dvd_orderOf_of_dvd hw₂3 h.pow_s hws
      (fun n hn => hNdvd n (h.mem_V_of_commute_s (Subgroup.pow_mem _ hw₂ n) hn))
    rw [orderOf_pow_of_dvd hN0.ne' hd, Nat.mul_div_cancel' hd]
  have hxN : N * orderOf (x ^ N) = orderOf x := by
    have hd := dvd_orderOf_of_dvd hw₂3 h.pow_x hwx
      (fun n hn => hNdvd n (h.mem_V_of_commute_x (Subgroup.pow_mem _ hw₂ n) hn))
    rw [orderOf_pow_of_dvd hN0.ne' hd, Nat.mul_div_cancel' hd]
  have hcomm : s ^ N * x ^ N = x ^ N * s ^ N := ((Commute.pow_pow h.commute_s_x) N N).eq
  have h1 : Nat.card V' ≤ N * (orderOf (s ^ N) * orderOf (x ^ N)) :=
    hbound.trans (Nat.mul_le_mul_left N
      ((Subgroup.card_le_of_le hinf).trans (Item1115Proof.card_closure_pair_le_mul hcomm)))
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

theorem normalizer_le (h : MhoHypV r s x e) :
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
  have hw : w₁ ∈ V ∧ w₂ ∈ V := by
    rcases Item1115Proof.mem_zpowers_or_mem_zpowers h.pow_r hw₁ hw₂ with h12 | h21
    · have h2 := h.mem_V_of_card_le hw₂ hv₁ hv₂ hcomm h12 (by rw [← hmap, hcard])
      exact ⟨Subgroup.zpowers_le.mpr h2 h12, h2⟩
    · have h1 := h.mem_V_of_card_le hw₁ hv₂ hv₁ hcomm.symm h21
        (by rw [Set.pair_comm (w₂ * v₂) (w₁ * v₁), ← hmap, hcard])
      exact ⟨h1, Subgroup.zpowers_le.mpr h1 h21⟩
  have hle : V.map (MulAut.conj g).toMonoidHom ≤ V := by
    rw [hmap, Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact V.mul_mem hw.1 hv₁
    · exact V.mul_mem hw.2 hv₂
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge hle hcard.ge)

theorem commutator_mem_V (h : MhoHypV r s x e) {g : G} (hg : ∃ k : ℕ, g ^ 3 ^ k = 1)
    (hgR : g ∈ Subgroup.normalizer ((Subgroup.closure {r, x, s} : Subgroup G) : Set G))
    (hgV : g ∈ Subgroup.normalizer ((Subgroup.closure {s, x} : Subgroup G) : Set G)) :
    r * g * r⁻¹ * g⁻¹ ∈ Subgroup.closure ({s, x} : Set G) := by
  set V := Subgroup.closure ({s, x} : Set G) with hV
  have hsV : s ∈ V := Subgroup.subset_closure (by simp)
  have hxV : x ∈ V := Subgroup.subset_closure (by simp)
  have hc : Commute s x := h.commute_s_x
  have hrV := h.r_mem_normalizer_V
  have hs1 : s ≠ 1 := fun h1 => h.not_commute_s (by rw [h1, mul_one, one_mul])
  obtain ⟨w, hw, v₀, hv₀, hwv⟩ := h.exists_mul_of_mem
    ((Subgroup.mem_normalizer_iff.mp hgR r).mp (Subgroup.subset_closure (by simp)))
  have hws : w ∈ Subgroup.normalizer (Subgroup.zpowers s : Set G) :=
    Subgroup.zpowers_le.mpr h.r_mem_normalizer_s hw
  have hwx : w ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) :=
    Subgroup.zpowers_le.mpr h.r_mem_normalizer_x hw
  have hconjV : ∀ y ∈ V, g * r * g⁻¹ * y * (g * r * g⁻¹)⁻¹ = w * y * w⁻¹ := by
    intro y hy
    have hvy : v₀ * y = y * v₀ := Item1115Proof.commute_of_mem_closure_pair h.commute_s_x hv₀ hy
    rw [hwv]
    calc w * v₀ * y * (w * v₀)⁻¹ = w * (v₀ * y) * v₀⁻¹ * w⁻¹ := by group
      _ = w * (y * v₀) * v₀⁻¹ * w⁻¹ := by rw [hvy]
      _ = w * y * w⁻¹ := by group
  have hsplit : ∀ (y : G) (p q τ : ℤ), y ∈ V → g * y * g⁻¹ = s ^ p * x ^ q →
      r * y * r⁻¹ = y ^ τ → w * s ^ p * w⁻¹ = (s ^ p) ^ τ ∧ w * x ^ q * w⁻¹ = (x ^ q) ^ τ := by
    intro y p q τ hy hgy hry
    have hgyV : g * y * g⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hgV y).mp hy
    have e1 : (w * s ^ p * w⁻¹) * (w * x ^ q * w⁻¹) = (s ^ p) ^ τ * (x ^ q) ^ τ := by
      calc (w * s ^ p * w⁻¹) * (w * x ^ q * w⁻¹) = w * (g * y * g⁻¹) * w⁻¹ := by
            rw [hgy]
            group
        _ = g * r * g⁻¹ * (g * y * g⁻¹) * (g * r * g⁻¹)⁻¹ := (hconjV _ hgyV).symm
        _ = g * (r * y * r⁻¹) * g⁻¹ := by group
        _ = (g * y * g⁻¹) ^ τ := by rw [hry, conj_zpow]
        _ = (s ^ p) ^ τ * (x ^ q) ^ τ := by rw [hgy, (hc.zpow_zpow p q).mul_zpow]
    exact eq_and_eq_of_mul_eq h.inf_eq_bot
      ((Subgroup.mem_normalizer_iff.mp hws _).mp (Subgroup.zpow_mem_zpowers s p))
      (Subgroup.zpow_mem _ (Subgroup.zpow_mem_zpowers s p) τ)
      ((Subgroup.mem_normalizer_iff.mp hwx _).mp (Subgroup.zpow_mem_zpowers x q))
      (Subgroup.zpow_mem _ (Subgroup.zpow_mem_zpowers x q) τ) e1
  obtain ⟨σ, hσ⟩ := Subgroup.mem_zpowers_iff.mp
    ((Subgroup.mem_normalizer_iff.mp h.r_mem_normalizer_s s).mp (Subgroup.mem_zpowers s))
  obtain ⟨ρ, hρ⟩ := Subgroup.mem_zpowers_iff.mp
    ((Subgroup.mem_normalizer_iff.mp h.r_mem_normalizer_x x).mp (Subgroup.mem_zpowers x))
  obtain ⟨γ, δ, hγδ⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair h.commute_s_x
    ((Subgroup.mem_normalizer_iff.mp hgV s).mp hsV)
  obtain ⟨α, β, hαβ⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair h.commute_s_x
    ((Subgroup.mem_normalizer_iff.mp hgV x).mp hxV)
  have hsγ := (hsplit s γ δ σ hsV hγδ hσ.symm).1
  have hxβ := (hsplit x α β ρ hxV hαβ hρ.symm).2
  have hw' : r⁻¹ * w ∈ Subgroup.zpowers r :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers r)) hw
  have hcs : r⁻¹ * w * s ^ γ = s ^ γ * (r⁻¹ * w) := by
    have e : w * s ^ γ * w⁻¹ = r * s ^ γ * r⁻¹ := by
      rw [hsγ, ← zpow_mul, mul_comm γ σ, zpow_mul, hσ, conj_zpow]
    calc r⁻¹ * w * s ^ γ = r⁻¹ * (w * s ^ γ * w⁻¹) * w := by group
      _ = r⁻¹ * (r * s ^ γ * r⁻¹) * w := by rw [e]
      _ = s ^ γ * (r⁻¹ * w) := by group
  have hcx : r⁻¹ * w * x ^ β = x ^ β * (r⁻¹ * w) := by
    have e : w * x ^ β * w⁻¹ = r * x ^ β * r⁻¹ := by
      rw [hxβ, ← zpow_mul, mul_comm β ρ, zpow_mul, hρ, conj_zpow]
    calc r⁻¹ * w * x ^ β = r⁻¹ * (w * x ^ β * w⁻¹) * w := by group
      _ = r⁻¹ * (r * x ^ β * r⁻¹) * w := by rw [e]
      _ = x ^ β * (r⁻¹ * w) := by group
  have hw'V : r⁻¹ * w ∈ V := by
    by_cases hγ3 : (3 : ℤ) ∣ γ
    · by_cases hβ3 : (3 : ℤ) ∣ β
      · exfalso
        obtain ⟨γ', rfl⟩ := hγ3
        obtain ⟨β', rfl⟩ := hβ3
        refine false_of_swap h.commute_s_x h.inf_eq_bot h.pow_s hs1 hg ?_ ?_
        · rw [hγδ, zpow_mul s 3 γ', zpow_ofNat]
          exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _)
            (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _)
        · rw [hαβ, zpow_mul x 3 β', zpow_ofNat]
          exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _)
            (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _)
      · have hxx : x ∈ Subgroup.zpowers (x ^ β) :=
          Item1116Proof.mem_zpowers_zpow_of_not_dvd h.pow_x hβ3
        have hC : Subgroup.zpowers (x ^ β) ≤ Subgroup.centralizer ({r⁻¹ * w} : Set G) :=
          Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hcx.symm)
        exact h.mem_V_of_commute_x hw' (Subgroup.mem_centralizer_singleton_iff.mp (hC hxx)).symm
    · have hss : s ∈ Subgroup.zpowers (s ^ γ) :=
        Item1116Proof.mem_zpowers_zpow_of_not_dvd h.pow_s hγ3
      have hC : Subgroup.zpowers (s ^ γ) ≤ Subgroup.centralizer ({r⁻¹ * w} : Set G) :=
        Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hcs.symm)
      exact h.mem_V_of_commute_s hw' (Subgroup.mem_centralizer_singleton_iff.mp (hC hss)).symm
  have hz : r⁻¹ * w * v₀ ∈ V := V.mul_mem hw'V hv₀
  have e : r * g * r⁻¹ * g⁻¹ = r * (r⁻¹ * w * v₀)⁻¹ * r⁻¹ := by
    have e1 : g * r⁻¹ * g⁻¹ = (w * v₀)⁻¹ := by
      rw [← hwv]
      group
    calc r * g * r⁻¹ * g⁻¹ = r * (g * r⁻¹ * g⁻¹) := by group
      _ = r * (w * v₀)⁻¹ := by rw [e1]
      _ = r * (r⁻¹ * w * v₀)⁻¹ * r⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp hrV _).mp (V.inv_mem hz)

end MhoHypV

end Mho

section Data

variable {G : Type} [Group G] [Finite G]
variable {A : Subgroup G} {c : G} {L : Subgroup G} {a : G} {R Y : Subgroup G} {d x s r g : G}

theorem exists_mhoHypV (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g)
    (hsa : s * a ≠ a * s) : ∃ i : ℤ, MhoHypV r s x (r ^ i) := by
  obtain ⟨hrR, hxR, hsR⟩ := Item1116Proof.mem_R h
  obtain ⟨i, j, hij⟩ := Item1116Proof.exists_zpow_mul_zpow_of_mem_closure
    (Item1115Proof.mem_normalizer_zpowers_s h45 h hrR) h.a_mem_closure
  refine ⟨i, ?_⟩
  set V := Subgroup.closure ({s, x} : Set G) with hV
  have he : r ^ i = a * (s ^ j)⁻¹ := by rw [hij]; group
  have hsjV : s ^ j ∈ V := Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) j
  have haV : a ∈ Subgroup.normalizer (V : Set G) :=
    h.R_le_normalizer_V h45 (Item1115Proof.A_le_R h.toHyp91 h.a_mem)
  have hsjs : (s ^ j)⁻¹ * s = s * (s ^ j)⁻¹ :=
    (((Commute.refl s).zpow_left j).inv_left).eq
  have hsjx : (s ^ j)⁻¹ * x = x * (s ^ j)⁻¹ :=
    (((show Commute s x from h.commute_s_x).zpow_left j).inv_left).eq
  exact
    { commute_s_x := h.commute_s_x
      inf_eq_bot := Item1115Proof.inf_zpowers_eq_bot h
      r_mem_normalizer_s := Item1115Proof.mem_normalizer_zpowers_s h45 h hrR
      r_mem_normalizer_x := Item1115Proof.mem_normalizer_zpowers_x h45 h hrR
      pow_r := Item1116Proof.exists_pow_eq_one_of_mem h hrR
      pow_s := Item1116Proof.exists_pow_eq_one_of_mem h hsR
      pow_x := Item1116Proof.exists_pow_eq_one_of_mem h hxR
      e_mem := Subgroup.zpow_mem_zpowers r i
      e_cube_mem := by
        rw [he]
        have h1 := Item1115Proof.inv_pow_mul_pow_mem haV (V.inv_mem hsjV) 3
        rwa [h.mem_partTwoF.1.2 a h.a_mem, inv_one, one_mul] at h1
      not_commute_s := fun e => by
        apply hsa
        have e' : a * s * (s ^ j)⁻¹ = s * a * (s ^ j)⁻¹ := by
          calc a * s * (s ^ j)⁻¹ = a * ((s ^ j)⁻¹ * s) := by rw [mul_assoc, hsjs]
            _ = r ^ i * s := by rw [he, mul_assoc]
            _ = s * r ^ i := e
            _ = s * a * (s ^ j)⁻¹ := by rw [he, mul_assoc]
        exact (mul_right_cancel e').symm
      not_commute_x := fun e => by
        apply Item1115Proof.not_commute_a_x h
        have e' : a * x * (s ^ j)⁻¹ = x * a * (s ^ j)⁻¹ := by
          calc a * x * (s ^ j)⁻¹ = a * ((s ^ j)⁻¹ * x) := by rw [mul_assoc, hsjx]
            _ = r ^ i * x := by rw [he, mul_assoc]
            _ = x * r ^ i := e
            _ = x * a * (s ^ j)⁻¹ := by rw [he, mul_assoc]
        exact mul_right_cancel e' }

theorem normalizer_R_le_V (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g)
    (hsa : s * a ≠ a * s) :
    Subgroup.normalizer (R : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure {s, x} : Subgroup G) : Set G) := by
  obtain ⟨i, hV⟩ := exists_mhoHypV h45 h hsa
  rw [h.R_eq]
  exact hV.normalizer_le

theorem commutator_r_g_mem_V (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g)
    (hsa : s * a ≠ a * s) : r * g * r⁻¹ * g⁻¹ ∈ Subgroup.closure ({s, x} : Set G) := by
  obtain ⟨i, hV⟩ := exists_mhoHypV h45 h hsa
  have hgR : g ∈ Subgroup.normalizer ((Subgroup.closure {r, x, s} : Subgroup G) : Set G) := by
    rw [← h.R_eq]
    exact h.g_mem_normalizer
  exact hV.commutator_mem_V h.pow_eq_one hgR (normalizer_R_le_V h45 h hsa h.g_mem_normalizer)

end Data

end Item1115NotFieldProof

end CFSG.RankThree.PartTwo.Sec11
