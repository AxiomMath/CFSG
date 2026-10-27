module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5Torus

public section

namespace CFSG.StandardType.Line63.H5

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover CFSG.RankThree.Classical2 CFSG.RankThree.Classical
  CFSG.StandardType.TableBU CFSG.Assembly

variable {K : Type} [Field K] {n : ℕ}

theorem exists_cube_of_pow_three_eq_one [Finite K] (h9 : 9 ∣ Nat.card Kˣ) {z : Kˣ}
    (hz : z ^ 3 = 1) : ∃ ζ : Kˣ, ζ ^ 3 = z := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg z)
  have hN : orderOf g = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  have h1 : g ^ (k * 3) = 1 := by
    rw [_root_.zpow_mul]
    exact_mod_cast hz
  have h2 : (orderOf g : ℤ) ∣ k * 3 := orderOf_dvd_iff_zpow_eq_one.mpr h1
  rw [hN] at h2
  have h3 : (9 : ℤ) ∣ (Nat.card Kˣ : ℤ) := by exact_mod_cast h9
  have h4 : (9 : ℤ) ∣ k * 3 := h3.trans h2
  obtain ⟨k', hk'⟩ : (3 : ℤ) ∣ k := by omega
  refine ⟨g ^ k', ?_⟩
  rw [hk', mul_comm 3 k', _root_.zpow_mul]
  norm_cast

theorem nine_dvd_card_units [Finite K] (hKd : UnitaryFieldData 2 n K) (h9 : 9 ∣ 2 ^ n + 1) :
    9 ∣ Nat.card Kˣ := by
  rw [Nat.card_units, hKd.card, pow_mul', sq]
  have e := Nat.mul_self_sub_mul_self_eq (2 ^ n) 1
  rw [mul_one] at e
  rw [e]
  exact Dvd.dvd.mul_right h9 _

@[expose] def uVec (ζ z : Kˣ) : Fin 6 → Kˣ := ![ζ, ζ, ζ * z, ζ, ζ, ζ]

theorem uVec_zero_eq_one (ζ z : Kˣ) : uVec ζ z 0 = uVec ζ z 1 := rfl

theorem uVec_pow_three {ζ z : Kˣ} (hζ : ζ ^ 3 = z) (hz : z ^ 3 = 1) (i : Fin 6) :
    uVec ζ z i ^ 3 = z := by
  fin_cases i <;> simp [uVec, mul_pow, hζ, hz]

theorem uVec_prod {ζ z : Kˣ} (hζ : ζ ^ 3 = z) (hz : z ^ 3 = 1) :
    ∏ i, (uVec ζ z i : K) = 1 := by
  have h6 : (ζ : K) ^ 6 = (z : K) ^ 2 := by
    rw [← hζ, Units.val_pow_eq_pow_val]
    ring
  have h3 : (z : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hz]
    simp
  calc ∏ i, (uVec ζ z i : K) = (ζ : K) ^ 6 * z := by
        simp [uVec, Fin.prod_univ_succ]
        ring
    _ = (z : K) ^ 3 := by rw [h6]; ring
    _ = 1 := h3

theorem uVec_norm {ζ z : Kˣ} (hζ : ζ ^ (2 ^ n + 1) = 1) (hz : z ^ (2 ^ n + 1) = 1) (i : Fin 6) :
    (uVec ζ z i : K) ^ (2 ^ n + 1) = 1 := by
  rw [← Units.val_pow_eq_pow_val]
  have : uVec ζ z i ^ (2 ^ n + 1) = 1 := by
    fin_cases i <;> simp [uVec, mul_pow, hζ, hz]
  rw [this]
  simp

theorem pow_norm_eq_one_of_pow_three {z : Kˣ} (hz : z ^ 3 = 1) (hpq : 3 ∣ 2 ^ n + 1) :
    z ^ (2 ^ n + 1) = 1 := by
  obtain ⟨k, hk⟩ := hpq
  rw [hk, pow_mul, hz, one_pow]

@[expose] noncomputable def scalarSU (h : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1) {z : Kˣ}
    (hz : z ^ 3 = 1) : ↥(unitarySU 2 n K 6) :=
  ⟨diagHom 6 (fun _ => z), diagHom_mem_unitarySU h
    (fun _ => by
      rw [← Units.val_pow_eq_pow_val, pow_norm_eq_one_of_pow_three hz hpq]
      simp)
    (by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Units.val_pow_eq_pow_val,
        show z ^ 6 = (z ^ 3) ^ 2 by group, hz]
      simp)⟩

@[expose] noncomputable def uSU (h : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1) {ζ z : Kˣ}
    (hζ : ζ ^ 3 = z) (hz : z ^ 3 = 1) (hζq : ζ ^ (2 ^ n + 1) = 1) : ↥(unitarySU 2 n K 6) :=
  ⟨diagHom 6 (uVec ζ z), diagHom_mem_unitarySU h
    (uVec_norm hζq (pow_norm_eq_one_of_pow_three hz hpq)) (uVec_prod hζ hz)⟩

theorem uSU_pow_three (h : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1) {ζ z : Kˣ}
    (hζ : ζ ^ 3 = z) (hz : z ^ 3 = 1) (hζq : ζ ^ (2 ^ n + 1) = 1) :
    uSU h hpq hζ hz hζq ^ 3 = scalarSU h hpq hz := by
  apply Subtype.ext
  show (diagHom 6 (uVec ζ z) : GL (Fin 6) K) ^ 3 = diagHom 6 (fun _ => z)
  rw [← map_pow]
  congr 1
  funext i
  exact uVec_pow_three hζ hz i

theorem eq_of_commute_swap {τ : Fin 6 → Kˣ} {i j : Fin 6}
    (h : Commute (permGL (Equiv.swap i j) : GL (Fin 6) K) (diagHom 6 τ)) : τ i = τ j := by
  have h1 := permGL_mul_diagHom_mul_inv (K := K) (Equiv.swap i j) τ
  have h2 : (permGL (Equiv.swap i j) : GL (Fin 6) K) * diagHom 6 τ *
      (permGL (Equiv.swap i j))⁻¹ = diagHom 6 τ := by
    rw [h.eq]
    group
  rw [h1] at h2
  have h3 := congrFun (diagHom_injective 6 h2) i
  rw [Function.comp_apply, Equiv.symm_swap, Equiv.swap_apply_left] at h3
  exact h3.symm

theorem exists_twoLocal_five_of_nine [Finite K] {G : Type} [Group G] [Finite G]
    (hKd : UnitaryFieldData 2 n K) (h9 : 9 ∣ 2 ^ n + 1)
    (φ : ↥(unitarySU 2 n K 6) →* G) (hφ : Function.Injective φ) {z : Kˣ} (hz3 : z ^ 3 = 1)
    (hz1 : z ≠ 1) (c : G) (hc : ∀ s, c * φ s = φ s * c)
    (hc3 : c ^ 3 = φ (scalarSU hKd (dvd_trans (by norm_num) h9) hz3)) :
    ∃ U E : Subgroup G, U ≠ ⊥ ∧ IsPGroup 2 U ∧ E ≤ Subgroup.normalizer (U : Set G) ∧
      CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 5 := by
  classical
  have hpq : 3 ∣ 2 ^ n + 1 := dvd_trans (by norm_num) h9
  obtain ⟨E₀, hE₀ab, hE₀card, hE₀diag⟩ := exists_torusFour hKd hpq
  obtain ⟨ζ, hζ⟩ := exists_cube_of_pow_three_eq_one (nine_dvd_card_units hKd h9) hz3
  have hζq : ζ ^ (2 ^ n + 1) = 1 := by
    have h9' : ζ ^ 9 = 1 := by rw [show ζ ^ 9 = (ζ ^ 3) ^ 3 by group, hζ, hz3]
    obtain ⟨k, hk⟩ := h9
    rw [hk, pow_mul, h9', one_pow]
  set ū := uSU hKd hpq hζ hz3 hζq with hū
  set w := swapSU hKd with hw
  set E₁ : Subgroup G := E₀.map φ with hE₁
  set y : G := c * (φ ū)⁻¹ with hy
  have hcu : Commute c (φ ū) := hc ū
  have hy3 : y ^ 3 = 1 := by
    have h1 : (φ ū) ^ 3 = c ^ 3 := by
      rw [← map_pow, hū, uSU_pow_three hKd hpq hζ hz3 hζq, hc3]
    rw [hy, (hcu.inv_right).mul_pow, inv_pow, h1]
    group
  have hE₀comm : ∀ s ∈ E₀, Commute s ū := by
    intro s hs
    obtain ⟨t, hst, -, -⟩ := hE₀diag s hs
    apply Subtype.ext
    show (s : GL (Fin 6) K) * diagHom 6 (uVec ζ z) = diagHom 6 (uVec ζ z) * (s : GL (Fin 6) K)
    rw [hst]
    exact (diagHom_commute t _).eq
  have hE₁y : ∀ e ∈ E₁, e * y = y * e := by
    rintro _ ⟨s, hs, rfl⟩
    have h1 : Commute (φ s) c := (hc s).symm
    have h2 : Commute (φ s) (φ ū) := (hE₀comm s hs).map φ
    exact (h1.mul_right (h2.inv_right)).eq
  have hw1 : φ w ≠ 1 := fun h1 => swapSU_ne_one hKd hz1 (hφ (h1.trans (map_one φ).symm))
  have hww : (φ w) ^ 2 = 1 := by rw [← map_pow, hw, swapSU_sq, map_one]
  set U : Subgroup G := Subgroup.zpowers (φ w) with hU
  have hUne : U ≠ ⊥ := by
    rw [hU, Ne, Subgroup.zpowers_eq_bot]
    exact hw1
  have hU2 : IsPGroup 2 U := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [hU, Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one (by simpa using hww)
  have hnorm : ∀ g : G, g * φ w = φ w * g → g ∈ Subgroup.normalizer (U : Set G) := by
    intro g hg
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun h hh => ?_)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (Commute.zpow_left (show Commute (φ w) g from hg.symm) k).eq
  have hE₁w : ∀ e ∈ E₁, e * φ w = φ w * e := by
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨t, hst, ht01, -⟩ := hE₀diag s hs
    have : Commute s w := by
      apply Subtype.ext
      show (s : GL (Fin 6) K) * permGL (Equiv.swap (0 : Fin 6) 1) =
        permGL (Equiv.swap (0 : Fin 6) 1) * (s : GL (Fin 6) K)
      rw [hst]
      exact (swap_commute_diagHom ht01).eq.symm
    exact (this.map φ).eq
  have hyw : y * φ w = φ w * y := by
    have h1 : Commute (φ ū) (φ w) := by
      refine Commute.map ?_ φ
      apply Subtype.ext
      show diagHom 6 (uVec ζ z) * permGL (Equiv.swap (0 : Fin 6) 1) =
        permGL (Equiv.swap (0 : Fin 6) 1) * diagHom 6 (uVec ζ z)
      exact (swap_commute_diagHom (uVec_zero_eq_one ζ z)).eq.symm
    have h2 : Commute c (φ w) := hc w
    exact (h2.mul_left (h1.inv_left)).eq
  have hyE₁ : y ∉ E₁ := by
    rintro ⟨s, hs, hsy⟩
    obtain ⟨t, hst, ht01, ht3⟩ := hE₀diag s hs
    set σ : ↥(unitarySU 2 n K 6) := s * ū with hσ
    have hcσ : φ σ = c := by
      rw [hσ, map_mul, hsy, hy]
      group
    have hcentral : ∀ s' : ↥(unitarySU 2 n K 6), σ * s' = s' * σ := by
      intro s'
      apply hφ
      calc φ (σ * s') = φ σ * φ s' := map_mul φ σ s'
        _ = c * φ s' := by rw [hcσ]
        _ = φ s' * c := hc s'
        _ = φ s' * φ σ := by rw [hcσ]
        _ = φ (s' * σ) := (map_mul φ s' σ).symm
    have hτ : (σ : GL (Fin 6) K) = diagHom 6 (t * uVec ζ z) := by
      show (s : GL (Fin 6) K) * diagHom 6 (uVec ζ z) = _
      rw [hst, map_mul]
    have hsw : ∀ j : Fin 6, j ≠ 0 → (t * uVec ζ z) 0 = (t * uVec ζ z) j := by
      intro j hj
      refine eq_of_commute_swap ?_
      have hjm := permGL_swap_mem_unitarySU hKd (i := 0) (j := j) (Ne.symm hj)
      have h1 := congrArg Subtype.val (hcentral ⟨_, hjm⟩)
      have h2 : (σ : GL (Fin 6) K) * permGL (Equiv.swap (0 : Fin 6) j) =
          permGL (Equiv.swap (0 : Fin 6) j) * (σ : GL (Fin 6) K) := h1
      rw [hτ] at h2
      exact h2.symm
    have e2 : t 0 * ζ = t 2 * (ζ * z) := hsw 2 (by decide)
    have e3 : t 0 * ζ = t 3 * ζ := hsw 3 (by decide)
    have e4 : t 0 * ζ = t 4 * ζ := hsw 4 (by decide)
    have e5 : t 0 * ζ = t 5 * ζ := hsw 5 (by decide)
    have hdet : ∏ i, (t i : K) = 1 := by
      have h1 := ((mem_unitarySU_iff hKd).mp s.2).1
      rw [hst, det_diagHom] at h1
      exact h1
    rw [Fin.prod_univ_six] at hdet
    have ζ0 : (ζ : K) ≠ 0 := ζ.ne_zero
    have ccast : ∀ a b : Kˣ, a = b → (a : K) = b := fun a b h => h ▸ rfl
    have k2 := ccast _ _ e2
    have k3 := ccast _ _ e3
    have k4 := ccast _ _ e4
    have k5 := ccast _ _ e5
    have k01 := ccast _ _ ht01
    have kcube := ccast _ _ (ht3 0)
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one] at k2 k3 k4 k5 kcube
    have h3 : (t 3 : K) = t 0 := mul_right_cancel₀ ζ0 (by linear_combination -k3)
    have h4 : (t 4 : K) = t 0 := mul_right_cancel₀ ζ0 (by linear_combination -k4)
    have h5 : (t 5 : K) = t 0 := mul_right_cancel₀ ζ0 (by linear_combination -k5)
    have h2 : (t 0 : K) = t 2 * z := mul_right_cancel₀ ζ0 (by linear_combination k2)
    rw [← k01, h3, h4, h5] at hdet
    apply hz1
    apply Units.ext
    rw [Units.val_one]
    calc (z : K) = z * 1 := (mul_one _).symm
      _ = z * ((t 0 : K) * t 0 * t 2 * t 0 * t 0 * t 0) := by rw [hdet]
      _ = (t 0 : K) ^ 5 * (t 2 * z) := by ring
      _ = (t 0 : K) ^ 5 * t 0 := by rw [← h2]
      _ = ((t 0 : K) ^ 3) ^ 2 := by ring
      _ = 1 := by rw [kcube]; norm_num
  have hy1 : y ≠ 1 := fun h1 => hyE₁ (h1 ▸ E₁.one_mem)
  have hyord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hX : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers y) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
      show (a : G) * b = b * a
      rw [← hi, ← hj, ← _root_.zpow_add, ← _root_.zpow_add, add_comm]
    · intro g hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hy3,
        _root_.one_zpow]
  have hE₁ab : CFSG.Open.IsElemAbelian 3 E₁ :=
    CFSG.StandardType.TableB.isElemAbelian_map hE₀ab φ
  have hcomm : ∀ a ∈ E₁, ∀ b ∈ Subgroup.zpowers y, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (show Commute a y from hE₁y a ha) k).eq
  have hXN : Subgroup.zpowers y ≤ Subgroup.normalizer (E₁ : Set G) := by
    intro b hb
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun g hg => ?_)
    exact hcomm g hg b hb
  have hdisj : Disjoint E₁ (Subgroup.zpowers y) := by
    rw [Subgroup.disjoint_def]
    intro x hx hxy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxy
    have hmod : y ^ (k % 3) = y ^ k := by
      have := zpow_mod_orderOf y k
      rwa [hyord, Nat.cast_ofNat] at this
    rw [← hmod] at hx ⊢
    have hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hk with hk | hk | hk
    · rw [hk]
      simp
    · rw [hk] at hx
      exact absurd (by simpa using hx) hyE₁
    · rw [hk] at hx
      have hx' : y ^ 2 ∈ E₁ := by simpa using hx
      have h4 : y ^ 4 = y := by rw [show 4 = 3 + 1 by rfl, pow_succ, hy3, one_mul]
      have h2 : (y ^ 2) ^ 2 = y := by rw [← pow_mul]; exact h4
      exact absurd (h2 ▸ E₁.pow_mem hx' 2) hyE₁
  refine ⟨U, E₁ ⊔ Subgroup.zpowers y, hUne, hU2, ?_,
    CFSG.StandardType.TableB.isElemAbelian_sup hE₁ab hX hcomm, ?_⟩
  · refine sup_le (fun e he => hnorm e (hE₁w e he)) fun e he => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    exact hnorm _ (Commute.zpow_left (show Commute y (φ w) from hyw) k).eq
  · rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hXN hdisj,
      ← Nat.card_congr (E₀.equivMapOfInjective φ hφ).toEquiv, hE₀card, Nat.card_zpowers, hyord]
    norm_num

theorem five_le_twoLocalRank_of_nine [Finite K] {G : Type} [Group G] [Finite G]
    (hKd : UnitaryFieldData 2 n K) (h9 : 9 ∣ 2 ^ n + 1)
    (φ : ↥(unitarySU 2 n K 6) →* G) (hφ : Function.Injective φ) {z : Kˣ} (hz3 : z ^ 3 = 1)
    (hz1 : z ≠ 1) (c : G) (hc : ∀ s, c * φ s = φ s * c)
    (hc3 : c ^ 3 = φ (scalarSU hKd (dvd_trans (by norm_num) h9) hz3)) :
    5 ≤ LargeEvenTwoLocalRank 3 G := by
  obtain ⟨U, E, hU, hU2, hEU, hE, hcard⟩ :=
    exists_twoLocal_five_of_nine hKd h9 φ hφ hz3 hz1 c hc hc3
  have h := CFSG.StandardType.TableB.card_le_of_twoLocal Nat.prime_three
    (H := Subgroup.normalizer (U : Set G)) ⟨U, hU, hU2, rfl⟩ hEU hE
  rw [hcard] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h

end CFSG.StandardType.Line63.H5

end
