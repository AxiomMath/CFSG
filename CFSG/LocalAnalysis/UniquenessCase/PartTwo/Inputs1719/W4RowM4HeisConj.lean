module

public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.Heisenberg

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

section Helpers

variable {G : Type*} [Group G]

private def m4Q (n : ℕ) (x y : Fin n → G) (z : G) : Subgroup G :=
  Subgroup.closure (Set.range x ∪ Set.range y ∪ {z})

private theorem m4_mem_sup_of_le_normalizer {X Y : Subgroup G}
    (h : Y ≤ Subgroup.normalizer (X : Set G)) {s : G} (hs : s ∈ X ⊔ Y) :
    ∃ y ∈ Y, ∃ x ∈ X, s = y * x := by
  let P : Subgroup G :=
    { carrier := {s | ∃ y ∈ Y, ∃ x ∈ X, s = y * x}
      mul_mem' := by
        rintro s1 s2 ⟨y1, hy1, x1, hx1, rfl⟩ ⟨y2, hy2, x2, hx2, rfl⟩
        obtain ⟨x1', hx1', hx1''⟩ : ∃ x1' ∈ X, x1 * y2 = y2 * x1' := by
          refine ⟨y2⁻¹ * x1 * y2, ?_, by group⟩
          exact (Subgroup.mem_set_normalizer_iff''.mp (h hy2) x1).mp hx1
        refine ⟨y1 * y2, Y.mul_mem hy1 hy2, x1' * x2, X.mul_mem hx1' hx2, ?_⟩
        rw [show y1 * x1 * (y2 * x2) = y1 * (x1 * y2) * x2 by group, hx1'']
        group
      one_mem' := ⟨1, Y.one_mem, 1, X.one_mem, by simp⟩
      inv_mem' := by
        rintro s ⟨y, hy, x, hx, rfl⟩
        obtain ⟨x', hx', hx''⟩ : ∃ x' ∈ X, x⁻¹ * y⁻¹ = y⁻¹ * x' := by
          refine ⟨y * x⁻¹ * y⁻¹, ?_, by group⟩
          exact (Subgroup.mem_set_normalizer_iff.mp (h hy) x⁻¹).mp (X.inv_mem hx)
        refine ⟨y⁻¹, Y.inv_mem hy, x', hx', ?_⟩
        rw [mul_inv_rev, hx''] }
  have hP : X ⊔ Y ≤ P := by
    rw [sup_le_iff]
    exact ⟨fun x hx => ⟨1, Y.one_mem, x, hx, by simp⟩,
      fun y hy => ⟨y, hy, 1, X.one_mem, by simp⟩⟩
  exact hP hs

private lemma m4_conj_pow_eq {u g c z : G} (hguc : g⁻¹ * u * g = u * c)
    (hcg : g * c = c * g) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (hcz : c ∈ Subgroup.zpowers z) (hc1 : c ≠ 1) :
    ∃ k : ℕ, (g ^ k)⁻¹ * u * g ^ k = u * z := by
  have hfin : IsOfFinOrder z := isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hz3⟩
  obtain ⟨m, hm⟩ : ∃ m : ℕ, z ^ m = c :=
    (Submonoid.mem_powers_iff c z).mp (hfin.mem_powers_iff_mem_zpowers.mpr hcz)
  have hm3 : ¬ 3 ∣ m := by
    rintro ⟨t, rfl⟩
    exact hc1 (by rw [← hm, pow_mul, hz3, one_pow])
  have hcop : Nat.Coprime m 3 :=
    Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 3)).2 hm3)
  obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by norm_num : 1 < 3)
  refine ⟨k, ?_⟩
  have hiter : ∀ j : ℕ, (g ^ j)⁻¹ * u * g ^ j = u * c ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hcj : g⁻¹ * c ^ j * g = c ^ j := by
        rw [mul_assoc, ← (Commute.pow_right (show Commute g c from hcg) j).eq, ← mul_assoc,
          inv_mul_cancel, one_mul]
      calc (g ^ (j + 1))⁻¹ * u * g ^ (j + 1)
          = g⁻¹ * ((g ^ j)⁻¹ * u * g ^ j) * g := by rw [pow_succ]; group
        _ = g⁻¹ * (u * c ^ j) * g := by rw [ih]
        _ = (g⁻¹ * u * g) * (g⁻¹ * c ^ j * g) := by group
        _ = (u * c) * c ^ j := by rw [hguc, hcj]
        _ = u * c ^ (j + 1) := by rw [pow_succ']; group
  rw [hiter k, ← hm]
  have hzk : (z ^ m) ^ k = z := by
    rw [← pow_mul, ← Nat.div_add_mod (m * k) 3, hk, pow_add, pow_mul, hz3, one_pow, one_mul,
      pow_one]
  rw [hzk]

private lemma m4_conj_inv_zpow (a b : G) (i : ℤ) : a⁻¹ * b ^ i * a = (a⁻¹ * b * a) ^ i := by
  simpa using (conj_zpow (a := a⁻¹) (b := b) (i := i)).symm

private theorem m4_conj_pair {x y z : G}
    (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hz3 : z ^ 3 = 1)
    (hzx : x * z = z * x) (hzy : y * z = z * y)
    (hyx : y⁻¹ * x * y = x * z) (hz1 : z ≠ 1) :
    ∀ u ∈ Subgroup.closure ({x, y, z} : Set G), u ∉ Subgroup.zpowers z →
      ∃ q ∈ Subgroup.closure ({x, y, z} : Set G), q⁻¹ * u * q = u * z := by
  have hxy_conj : y * x * y⁻¹ = x * z⁻¹ := by
    have h1 : (y * x * y⁻¹) * z = x := by
      have hzy' : y⁻¹ * z = z * y⁻¹ :=
        (Commute.inv_left (show Commute y z from hzy)).eq
      calc (y * x * y⁻¹) * z = y * x * (y⁻¹ * z) := by group
        _ = y * x * (z * y⁻¹) := by rw [hzy']
        _ = y * (x * z) * y⁻¹ := by group
        _ = y * (y⁻¹ * x * y) * y⁻¹ := by rw [hyx]
        _ = x := by group
    calc y * x * y⁻¹ = (y * x * y⁻¹) * z * z⁻¹ := by group
      _ = x * z⁻¹ := by rw [h1]
  have hx_conj : x * y * x⁻¹ = y * z := by
    have h1 : x * y = y * x * z := by
      calc x * y = y * (y⁻¹ * x * y) := by group
        _ = y * (x * z) := by rw [hyx]
        _ = y * x * z := by group
    have hzxinv : z * x⁻¹ = x⁻¹ * z :=
      (((show Commute x z from hzx).symm).inv_right).eq
    calc x * y * x⁻¹ = y * x * z * x⁻¹ := by rw [h1]
      _ = y * x * (z * x⁻¹) := by group
      _ = y * x * (x⁻¹ * z) := by rw [hzxinv]
      _ = y * z := by group
  have hx_conj_inv : x⁻¹ * y * x = y * z⁻¹ := by
    have h1 : y * x = x * z⁻¹ * y := by
      calc y * x = y * x * y⁻¹ * y := by group
        _ = x * z⁻¹ * y := by rw [hxy_conj]
    calc x⁻¹ * y * x = x⁻¹ * (y * x) := by group
      _ = x⁻¹ * (x * z⁻¹ * y) := by rw [h1]
      _ = z⁻¹ * y := by group
      _ = y * z⁻¹ := ((show Commute y z from hzy).inv_right).eq.symm
  let H : Subgroup G :=
    { carrier := {g | ∃ e c : ℤ, g = x ^ e * z ^ c}
      mul_mem' := by
        rintro g1 g2 ⟨e1, c1, rfl⟩ ⟨e2, c2, rfl⟩
        refine ⟨e1 + e2, c1 + c2, ?_⟩
        have hzc : z ^ c1 * x ^ e2 = x ^ e2 * z ^ c1 :=
          ((((show Commute x z from hzx).symm).zpow_left c1).zpow_right e2).eq
        calc x ^ e1 * z ^ c1 * (x ^ e2 * z ^ c2)
            = x ^ e1 * (z ^ c1 * x ^ e2) * z ^ c2 := by group
          _ = x ^ e1 * (x ^ e2 * z ^ c1) * z ^ c2 := by rw [hzc]
          _ = (x ^ e1 * x ^ e2) * (z ^ c1 * z ^ c2) := by group
          _ = x ^ (e1 + e2) * z ^ (c1 + c2) := by rw [← zpow_add, ← zpow_add]
      one_mem' := ⟨0, 0, by simp⟩
      inv_mem' := by
        rintro g ⟨e, c, rfl⟩
        refine ⟨-e, -c, ?_⟩
        have hzc : z ^ (-c) * x ^ (-e) = x ^ (-e) * z ^ (-c) :=
          ((((show Commute x z from hzx).symm).zpow_left (-c)).zpow_right (-e)).eq
        rw [mul_inv_rev, show (z ^ c)⁻¹ = z ^ (-c) from (zpow_neg z c).symm,
          show (x ^ e)⁻¹ = x ^ (-e) from (zpow_neg x e).symm]
        exact hzc }
  have hxH : x ∈ H := ⟨1, 0, by simp⟩
  have hzH : z ∈ H := ⟨0, 1, by simp⟩
  have hyb : ∀ e : ℤ, y⁻¹ * x ^ e * y = x ^ e * z ^ e := by
    intro e
    have h1 : y⁻¹ * x ^ e * y = (y⁻¹ * x * y) ^ e := m4_conj_inv_zpow y x e
    rw [h1, hyx, (show Commute x z from hzx).mul_zpow e]
  have hya : ∀ e : ℤ, y * x ^ e * y⁻¹ = x ^ e * z ^ (-e) := by
    intro e
    rw [← conj_zpow, hxy_conj, ((show Commute x z from hzx).inv_right).mul_zpow e, inv_zpow']
  have hyz_c : ∀ c : ℤ, y⁻¹ * z ^ c * y = z ^ c := by
    intro c
    rw [m4_conj_inv_zpow y z c]
    have h : y⁻¹ * z * y = z := by
      calc y⁻¹ * z * y = y⁻¹ * (z * y) := by group
        _ = y⁻¹ * (y * z) := by rw [← hzy]
        _ = z := by group
    rw [h]
  have hyz_c' : ∀ c : ℤ, y * z ^ c * y⁻¹ = z ^ c := by
    intro c
    rw [← conj_zpow]
    have h : y * z * y⁻¹ = z := by rw [hzy]; group
    rw [h]
  have hxy_pow : ∀ k : ℤ, x * y ^ k * x⁻¹ = y ^ k * z ^ k := by
    intro k
    rw [← conj_zpow, hx_conj, (show Commute y z from hzy).mul_zpow k]
  have hxy_pow_inv : ∀ k : ℤ, x⁻¹ * y ^ k * x = y ^ k * z ^ (-k) := by
    intro k
    rw [m4_conj_inv_zpow x y k, hx_conj_inv,
      ((show Commute y z from hzy).inv_right).mul_zpow k, inv_zpow']
  have hxz_c : ∀ c : ℤ, x⁻¹ * z ^ c * x = z ^ c := by
    intro c
    rw [m4_conj_inv_zpow x z c]
    have h : x⁻¹ * z * x = z := by
      calc x⁻¹ * z * x = x⁻¹ * (z * x) := by group
        _ = x⁻¹ * (x * z) := by rw [← hzx]
        _ = z := by group
    rw [h]
  have hy_norm : y ∈ Subgroup.normalizer H := by
    rw [Subgroup.mem_set_normalizer_iff]
    intro h
    constructor
    · rintro ⟨e, c, rfl⟩
      refine ⟨e, c - e, ?_⟩
      calc y * (x ^ e * z ^ c) * y⁻¹
          = (y * x ^ e * y⁻¹) * z ^ c := by
              rw [show y * (x ^ e * z ^ c) * y⁻¹ = y * x ^ e * (z ^ c * y⁻¹) by group]
              rw [show z ^ c * y⁻¹ = y⁻¹ * z ^ c from
                ((show Commute z y from hzy.symm).zpow_left c).inv_right.eq]
              group
        _ = (x ^ e * z ^ (-e)) * z ^ c := by rw [hya]
        _ = x ^ e * z ^ (c - e) := by
              rw [mul_assoc, ← zpow_add, show -e + c = c - e by ring]
    · rintro ⟨e, c, hh⟩
      refine ⟨e, e + c, ?_⟩
      have h1 : h = y⁻¹ * (x ^ e * z ^ c) * y := by rw [← hh]; group
      rw [h1]
      calc y⁻¹ * (x ^ e * z ^ c) * y
          = (y⁻¹ * x ^ e * y) * z ^ c := by
              rw [show y⁻¹ * (x ^ e * z ^ c) * y = y⁻¹ * x ^ e * (z ^ c * y) by group]
              rw [show z ^ c * y = y * z ^ c from
                ((show Commute z y from hzy.symm).zpow_left c).eq]
              group
        _ = (x ^ e * z ^ e) * z ^ c := by rw [hyb]
        _ = x ^ e * z ^ (e + c) := by rw [mul_assoc, ← zpow_add]
  have hYnorm : Subgroup.zpowers y ≤ Subgroup.normalizer (H : Set G) :=
    Subgroup.zpowers_le.mpr hy_norm
  have hclosure : Subgroup.closure ({x, y, z} : Set G) = H ⊔ Subgroup.zpowers y := by
    apply le_antisymm
    · refine (Subgroup.closure_le _).mpr ?_
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      · exact Subgroup.mem_sup_left hxH
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩)
      · exact Subgroup.mem_sup_left hzH
    · apply sup_le
      · intro g hg
        obtain ⟨e, c, rfl⟩ := hg
        have hx' : x ∈ Subgroup.closure ({x, y, z} : Set G) := Subgroup.subset_closure (by simp)
        have hz' : z ∈ Subgroup.closure ({x, y, z} : Set G) := Subgroup.subset_closure (by simp)
        exact (Subgroup.closure ({x, y, z} : Set G)).mul_mem
          ((Subgroup.closure ({x, y, z} : Set G)).zpow_mem hx' e)
          ((Subgroup.closure ({x, y, z} : Set G)).zpow_mem hz' c)
      · intro g hg
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
        have hy' : y ∈ Subgroup.closure ({x, y, z} : Set G) := Subgroup.subset_closure (by simp)
        exact (Subgroup.closure ({x, y, z} : Set G)).zpow_mem hy' j
  intro u hu huz
  have hu_sup : u ∈ H ⊔ Subgroup.zpowers y := hclosure ▸ hu
  obtain ⟨y0, hy0, h0, hh0, hu_eq⟩ := m4_mem_sup_of_le_normalizer hYnorm hu_sup
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy0
  obtain ⟨e, c, rfl⟩ := hh0
  have hyk_norm : y ^ k ∈ Subgroup.normalizer (H : Set G) :=
    hYnorm (Subgroup.zpow_mem_zpowers y k)
  have hh0H : y ^ k * (x ^ e * z ^ c) * y ^ (-k) ∈ H := by
    have h := (Subgroup.mem_set_normalizer_iff.mp hyk_norm (x ^ e * z ^ c)).mp ⟨e, c, rfl⟩
    rw [zpow_neg]
    exact h
  obtain ⟨e', c', he'⟩ := hh0H
  have hu_nf : u = x ^ e' * z ^ c' * y ^ k := by
    rw [hu_eq]
    calc y ^ k * (x ^ e * z ^ c)
        = (y ^ k * (x ^ e * z ^ c) * y ^ (-k)) * y ^ k := by group
      _ = (x ^ e' * z ^ c') * y ^ k := by rw [he']
      _ = x ^ e' * z ^ c' * y ^ k := by group
  have horder : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  by_cases he : e' % 3 = 0
  · have h3e : (3 : ℤ) ∣ e' := Int.dvd_of_emod_eq_zero he
    obtain ⟨t, rfl⟩ := h3e
    have hx1 : x ^ (3 * t) = 1 := by rw [zpow_mul, zpow_ofNat, hx3, one_zpow]
    rw [hx1, one_mul] at hu_nf
    have hk : k % 3 ≠ 0 := by
      intro hk0
      apply huz
      have h3k : (3 : ℤ) ∣ k := Int.dvd_of_emod_eq_zero hk0
      obtain ⟨s, rfl⟩ := h3k
      rw [hu_nf]
      have hy1 : y ^ (3 * s) = 1 := by rw [zpow_mul, zpow_ofNat, hy3, one_zpow]
      rw [hy1, mul_one]
      exact Subgroup.mem_zpowers_iff.mpr ⟨c', rfl⟩
    have hc1 : z ^ (-k) ≠ 1 := by
      intro hc
      apply hk
      have h3 : (3 : ℤ) ∣ -k := by
        have h := (orderOf_dvd_iff_zpow_eq_one (x := z)).mpr hc
        rwa [horder] at h
      have h3' : (3 : ℤ) ∣ k := by simpa using dvd_neg.mp h3
      exact Int.emod_eq_zero_of_dvd h3'
    have hguc : x⁻¹ * u * x = u * z ^ (-k) := by
      rw [hu_nf]
      calc x⁻¹ * (z ^ c' * y ^ k) * x
          = (x⁻¹ * z ^ c' * x) * (x⁻¹ * y ^ k * x) := by group
        _ = z ^ c' * (y ^ k * z ^ (-k)) := by rw [hxz_c, hxy_pow_inv]
        _ = z ^ c' * y ^ k * z ^ (-k) := by group
    obtain ⟨j, hj⟩ := m4_conj_pow_eq hguc
      ((show Commute x z from hzx).zpow_right (-k)).eq hz3 hz1
      (Subgroup.mem_zpowers_iff.mpr ⟨-k, rfl⟩) hc1
    have hxcl : x ∈ Subgroup.closure ({x, y, z} : Set G) := Subgroup.subset_closure (by simp)
    exact ⟨x ^ j, (Subgroup.closure ({x, y, z} : Set G)).pow_mem hxcl j, hj⟩
  · have hc1 : z ^ e' ≠ 1 := by
      intro hc
      apply he
      have h3 : (3 : ℤ) ∣ e' := by
        have h := (orderOf_dvd_iff_zpow_eq_one (x := z)).mpr hc
        rwa [horder] at h
      exact Int.emod_eq_zero_of_dvd h3
    have hguc : y⁻¹ * u * y = u * z ^ e' := by
      rw [hu_nf]
      have h1 : z ^ e' * (z ^ c' * y ^ k) = (z ^ c' * y ^ k) * z ^ e' :=
        ((((Commute.refl z).zpow_left e').zpow_right c').mul_right
          (((show Commute z y from hzy.symm).zpow_left e').zpow_right k)).eq
      calc y⁻¹ * (x ^ e' * z ^ c' * y ^ k) * y
          = (y⁻¹ * x ^ e' * y) * (y⁻¹ * z ^ c' * y) * y ^ k := by group
        _ = (x ^ e' * z ^ e') * z ^ c' * y ^ k := by rw [hyb, hyz_c]
        _ = x ^ e' * (z ^ e' * (z ^ c' * y ^ k)) := by group
        _ = x ^ e' * ((z ^ c' * y ^ k) * z ^ e') := by rw [h1]
        _ = x ^ e' * z ^ c' * y ^ k * z ^ e' := by group
    obtain ⟨j, hj⟩ := m4_conj_pow_eq hguc
      ((show Commute y z from hzy).zpow_right e').eq hz3 hz1
      (Subgroup.mem_zpowers_iff.mpr ⟨e', rfl⟩) hc1
    have hycl : y ∈ Subgroup.closure ({x, y, z} : Set G) := Subgroup.subset_closure (by simp)
    exact ⟨y ^ j, (Subgroup.closure ({x, y, z} : Set G)).pow_mem hycl j, hj⟩

private theorem m4_conj_aux : ∀ (n : ℕ) {x y : Fin n → G} {z : G}, HeisCfg 3 n x y z →
    (∀ i, y i ^ 3 = 1) → ∀ u, u ∈ m4Q n x y z → u ∉ Subgroup.zpowers z →
      ∃ q ∈ m4Q n x y z, q⁻¹ * u * q = u * z := by
  intro n
  induction n with
  | zero =>
    intro x y z h hy u hu huz
    have hx : Set.range x = (∅ : Set G) := Set.range_eq_empty_iff.mpr ⟨fun i => Fin.elim0 i⟩
    have hy' : Set.range y = (∅ : Set G) := Set.range_eq_empty_iff.mpr ⟨fun i => Fin.elim0 i⟩
    have hle : m4Q 0 x y z ≤ Subgroup.zpowers z := by
      rw [m4Q, hx, hy', Set.empty_union, Set.empty_union]
      exact le_of_eq (Subgroup.zpowers_eq_closure z).symm
    exact absurd (hle hu) huz
  | succ n ih =>
    intro x y z h hy u hu huz
    set A : Subgroup G := Subgroup.closure ({x 0, y 0, z} : Set G) with hA
    set B : Subgroup G := m4Q n (fun i => x i.succ) (fun i => y i.succ) z with hB
    have hle : m4Q (n + 1) x y z ≤ A ⊔ B := by
      rw [m4Q]
      refine (Subgroup.closure_le _).mpr ?_
      rintro w ((hw | hw) | hw)
      · obtain ⟨i, rfl⟩ := hw
        by_cases hi : i = 0
        · subst hi
          exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
        · obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi
          exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
      · obtain ⟨i, rfl⟩ := hw
        by_cases hi : i = 0
        · subst hi
          exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
        · obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi
          exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
      · rw [Set.mem_singleton_iff] at hw
        subst hw
        exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
    have hge : A ⊔ B ≤ m4Q (n + 1) x y z := by
      rw [sup_le_iff]
      constructor
      · rw [hA]
        refine (Subgroup.closure_le _).mpr ?_
        intro g hg
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
        rcases hg with rfl | rfl | rfl
        · exact Subgroup.subset_closure (by simp)
        · exact Subgroup.subset_closure (by simp)
        · exact Subgroup.subset_closure (by simp)
      · rw [hB, m4Q]
        refine (Subgroup.closure_le _).mpr ?_
        intro g hg
        rcases hg with (hg | hg) | hg
        · obtain ⟨i, rfl⟩ := hg
          exact Subgroup.subset_closure (by simp)
        · obtain ⟨i, rfl⟩ := hg
          exact Subgroup.subset_closure (by simp)
        · rw [Set.mem_singleton_iff] at hg
          subst hg
          exact Subgroup.subset_closure (by simp)
    have hABcomm : A ≤ Subgroup.centralizer (B : Set G) := by
      rw [hA]
      refine (Subgroup.closure_le _).mpr ?_
      intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl | rfl
      · rw [hB, m4Q, Subgroup.centralizer_closure]
        refine Subgroup.mem_centralizer_iff.mpr ?_
        rintro b ((⟨i, rfl⟩ | ⟨i, rfl⟩) | rfl)
        · exact h.xx i.succ 0
        · exact (h.xy 0 i.succ (Fin.succ_ne_zero i).symm).symm
        · exact (h.zx 0).symm
      · rw [hB, m4Q, Subgroup.centralizer_closure]
        refine Subgroup.mem_centralizer_iff.mpr ?_
        rintro b ((⟨i, rfl⟩ | ⟨i, rfl⟩) | rfl)
        · exact h.xy i.succ 0 (by simp)
        · exact (h.yy 0 i.succ (Fin.succ_ne_zero i).symm).symm
        · exact (h.zy 0).symm
      · rw [hB, m4Q, Subgroup.centralizer_closure]
        refine Subgroup.mem_centralizer_iff.mpr ?_
        rintro b ((⟨i, rfl⟩ | ⟨i, rfl⟩) | rfl)
        · exact h.zx i.succ
        · exact h.zy i.succ
        · rfl
    have hAB : A ≤ Subgroup.normalizer (B : Set G) := by
      rw [Subgroup.le_set_normalizer_iff]
      intro a ha b hb
      have hba : a * b = b * a := (Subgroup.mem_centralizer_iff.mp (hABcomm ha) b hb).symm
      rw [show a * b * a⁻¹ = b by rw [hba]; group]
      exact hb
    have hQeq : m4Q (n + 1) x y z = A ⊔ B := le_antisymm hle hge
    have hu_sup : u ∈ A ⊔ B := hQeq ▸ hu
    have hu_sup' : u ∈ B ⊔ A := by rw [sup_comm]; exact hu_sup
    obtain ⟨a, ha, b, hb, hu_ab⟩ := m4_mem_sup_of_le_normalizer hAB hu_sup'
    by_cases haz : a ∈ Subgroup.zpowers z
    · have hbz : b ∉ Subgroup.zpowers z := by
        intro hb'
        have hab : a * b ∈ Subgroup.zpowers z := (Subgroup.zpowers z).mul_mem haz hb'
        exact huz (hu_ab ▸ hab)
      obtain ⟨q, hqB, hq⟩ := ih h.tail (fun i => hy i.succ) b hb hbz
      refine ⟨q, hge (Subgroup.mem_sup_right hqB), ?_⟩
      rw [hu_ab]
      have hqb' : q⁻¹ * a * q = a := by
        have hqa : q * a = a * q := Subgroup.mem_centralizer_iff.mp (hABcomm ha) q hqB
        calc q⁻¹ * a * q = q⁻¹ * (a * q) := by group
          _ = q⁻¹ * (q * a) := by rw [← hqa]
          _ = a := by group
      calc q⁻¹ * (a * b) * q = (q⁻¹ * a * q) * (q⁻¹ * b * q) := by group
        _ = a * (b * z) := by rw [hqb', hq]
        _ = (a * b) * z := by group
    · obtain ⟨q, hqA, hq⟩ := m4_conj_pair (h.xp 0) (hy 0) h.zp (h.zx 0) (h.zy 0) (h.yx 0)
        h.z1 a ha haz
      refine ⟨q, hge (Subgroup.mem_sup_left hqA), ?_⟩
      rw [hu_ab]
      have hqb' : q⁻¹ * b * q = b := by
        have hqb : q * b = b * q := (Subgroup.mem_centralizer_iff.mp (hABcomm hqA) b hb).symm
        calc q⁻¹ * b * q = q⁻¹ * (b * q) := by group
          _ = q⁻¹ * (q * b) := by rw [← hqb]
          _ = b := by group
      have hzA : z ∈ A := Subgroup.subset_closure (by simp)
      have hzb : z * b = b * z :=
        (Subgroup.mem_centralizer_iff.mp (hABcomm hzA) b hb).symm
      calc q⁻¹ * (a * b) * q = (q⁻¹ * a * q) * (q⁻¹ * b * q) := by group
        _ = (a * z) * b := by rw [hq, hqb']
        _ = (a * b) * z := by
              rw [show (a * z) * b = a * (z * b) by group, hzb]
              group

end Helpers

theorem exists_conj_eq_mul_of_mem_heis {G : Type*} [Group G] {n : ℕ} {x y : Fin n → G} {z : G}
    (h : HeisCfg 3 n x y z) (hy : ∀ i, y i ^ 3 = 1) {u : G}
    (hu : u ∈ Subgroup.closure (Set.range x ∪ Set.range y ∪ {z}))
    (hz : u ∉ Subgroup.zpowers z) :
    ∃ q ∈ Subgroup.closure (Set.range x ∪ Set.range y ∪ {z}), q⁻¹ * u * q = u * z :=
  m4_conj_aux n h hy u hu hz

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
