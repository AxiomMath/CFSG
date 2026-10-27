module

public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Torus
public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Rot
public import CFSG.LocalAnalysis.SectionRank.Alternating
public import CFSG.Quasithin.Background.A3FactsRank
public import CFSG.Quasithin.Background.A3FactsNumber

public section

namespace CFSG.Quasithin

namespace A3Facts

open CFSG.Open CFSG.SectionRank CFSG.SectionRank.ClassicalEven CFSG.Assembly.LowTwoRank Matrix

theorem two_le_pRank_statedProj {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] {H : Subgroup (GL ι K)} {p : ℕ} [hp : Fact p.Prime] {x y : GL ι K}
    (hxH : x ∈ H) (hyH : y ∈ H) (hx : x ^ p ∈ StatedScalars ι K) (hy : y ^ p ∈ StatedScalars ι K)
    (hxy : (x * y)⁻¹ * (y * x) ∈ StatedScalars ι K)
    (hx1 : x ∉ StatedScalars ι K)
    (hy1 : ∀ n : ℕ, ∀ c ∈ StatedScalars ι K, x ^ n * c ≠ y) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (StatedProj H)) := by
  let N := (StatedScalars ι K).subgroupOf H
  let π : H →* StatedProj H := QuotientGroup.mk' N
  have hmem : ∀ u v : H, π u = π v → ((u : GL ι K)⁻¹ * v) ∈ StatedScalars ι K := fun u v h => by
    change QuotientGroup.mk' N u = QuotientGroup.mk' N v at h
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at h
    simpa using h
  have hone : ∀ u : H, π u = 1 ↔ (u : GL ι K) ∈ StatedScalars ι K := fun u => by
    change (u : H ⧸ N) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  refine two_le_pRank_of_gens (x := π ⟨x, hxH⟩) (y := π ⟨y, hyH⟩) ?_ ?_ ?_ ?_ ?_
  · rw [← map_pow, hone]
    exact hx
  · rw [← map_pow, hone]
    exact hy
  · show π ⟨x, hxH⟩ * π ⟨y, hyH⟩ = π ⟨y, hyH⟩ * π ⟨x, hxH⟩
    rw [← map_mul, ← map_mul]
    change ((⟨x, hxH⟩ * ⟨y, hyH⟩ : H) : H ⧸ N) = ((⟨y, hyH⟩ * ⟨x, hxH⟩ : H) : H ⧸ N)
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact hxy
  · intro h
    exact hx1 ((hone _).1 h)
  · intro n h
    rw [← map_pow] at h
    have := hmem _ _ h
    simp only [SubgroupClass.coe_pow] at this
    exact hy1 n _ this (mul_inv_cancel_left _ _)

section Torus

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem torusDiag_hent {d d' : ι → Kˣ} (h : torusDiag (K := K) d = torusDiag d') (i : ι) :
    d i = d' i :=
  congrFun (torusDiag_injective h) i

omit [Finite K] in
theorem torusVec_pow_order {r : ℕ} {ζ : Kˣ} (hζ : orderOf ζ = r) (j k : ι) :
    torusDiag (K := K) (torusVec ζ j k) ^ r = 1 := by
  rw [← map_pow, torusVec_pow, ← hζ, pow_orderOf_eq_one, torusVec_one, map_one]

theorem two_le_pRank_diag {H : Subgroup (GL ι K)} {p : ℕ} [Fact p.Prime] {a b : ι → Kˣ}
    (haH : torusDiag (K := K) a ∈ H) (hbH : torusDiag (K := K) b ∈ H)
    (ha : ∃ c : Kˣ, a ^ p = fun _ => c) (hb : ∃ c : Kˣ, b ^ p = fun _ => c)
    (ha1 : ∃ i j, a i ≠ a j) (hb1 : ∀ (n : ℕ) (c : Kˣ), ∃ i, a i ^ n * c ≠ b i) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (StatedProj H)) := by
  have hcomm (u v : ι → Kˣ) : Commute (torusDiag (K := K) u) (torusDiag v) :=
    (Commute.all u v).map torusDiag
  refine two_le_pRank_statedProj haH hbH ?_ ?_ ?_ ?_ ?_
  · obtain ⟨c, hc⟩ := ha
    rw [← map_pow, hc, ← scalar_eq_torusDiag]
    exact ⟨c, rfl⟩
  · obtain ⟨c, hc⟩ := hb
    rw [← map_pow, hc, ← scalar_eq_torusDiag]
    exact ⟨c, rfl⟩
  · rw [(hcomm _ _).eq]
    simp
  · rintro ⟨c, hc⟩
    rw [scalar_eq_torusDiag] at hc
    obtain ⟨i, j, hij⟩ := ha1
    exact hij ((torusDiag_hent hc i).symm.trans (torusDiag_hent hc j))
  · rintro n _ ⟨c, rfl⟩ h
    rw [← map_pow, scalar_eq_torusDiag, ← map_mul] at h
    obtain ⟨i, hi⟩ := hb1 n c
    exact hi (by simpa using torusDiag_hent h i)

theorem two_le_pRank_torus_shared {H : Subgroup (GL ι K)} {r : ℕ} [hr : Fact r.Prime]
    (hr3 : r ≠ 3) {ζ : Kˣ} (hζ : orderOf ζ = r) {i₀ i₁ i₂ : ι} (h01 : i₀ ≠ i₁)
    (h02 : i₀ ≠ i₂) (h12 : i₁ ≠ i₂)
    (hx : torusDiag (K := K) (torusVec ζ i₀ i₂) ∈ H)
    (hy : torusDiag (K := K) (torusVec ζ i₁ i₂) ∈ H) :
    2 ≤ CFSG.Open.pRank r (⊤ : Subgroup (StatedProj H)) := by
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hζ
    exact hr.out.one_lt.ne hζ
  have hcomm (a b : ι → Kˣ) : Commute (torusDiag (K := K) a) (torusDiag b) :=
    (Commute.all a b).map torusDiag
  refine two_le_pRank_statedProj hx hy (by rw [torusVec_pow_order hζ]; exact one_mem _)
    (by rw [torusVec_pow_order hζ]; exact one_mem _) ?_ ?_ ?_
  · rw [(hcomm _ _).eq]
    simp
  · rintro ⟨c, hc⟩
    rw [scalar_eq_torusDiag] at hc
    have e0 := torusDiag_hent hc i₀
    have e1 := torusDiag_hent hc i₁
    rw [torusVec_apply_left ζ h02] at e0
    rw [torusVec_apply_of_ne ζ h01.symm h12] at e1
    exact hζ1 (e0.symm.trans e1)
  · rintro n _ ⟨c, rfl⟩ h
    rw [← map_pow, torusVec_pow, scalar_eq_torusDiag, ← map_mul] at h
    have e0 := torusDiag_hent h i₀
    have e1 := torusDiag_hent h i₁
    have e2 := torusDiag_hent h i₂
    simp only [Pi.mul_apply, torusVec_apply_left _ h02, torusVec_apply_of_ne _ h01 h02,
      torusVec_apply_of_ne _ h01.symm h12, torusVec_apply_left _ h12,
      torusVec_apply_right _ h02, torusVec_apply_right _ h12, one_mul] at e0 e1 e2
    rw [e1] at e0 e2
    have hA : ζ ^ n = ζ⁻¹ := eq_inv_of_mul_eq_one_left e0
    rw [hA, inv_inv] at e2
    have h3 : ζ ^ 3 = 1 := by
      calc ζ ^ 3 = (ζ * ζ) * ζ := by rw [pow_succ, pow_two]
        _ = 1 := by rw [e2]; exact inv_mul_cancel ζ
    exact hr3 ((Nat.prime_dvd_prime_iff_eq hr.out Nat.prime_three).1
      (hζ ▸ orderOf_dvd_of_pow_eq_one h3))

theorem two_le_pRank_torus_disjoint {H : Subgroup (GL ι K)} {r : ℕ} [hr : Fact r.Prime]
    (hr2 : r ≠ 2) {ζ : Kˣ} (hζ : orderOf ζ = r) {i₀ i₁ k₀ k₁ : ι} (h0 : i₀ ≠ k₀)
    (h1 : i₁ ≠ k₁) (hik : i₀ ≠ i₁) (hik' : i₀ ≠ k₁) (hki : k₀ ≠ i₁) (hkk : k₀ ≠ k₁)
    (hx : torusDiag (K := K) (torusVec ζ i₀ k₀) ∈ H)
    (hy : torusDiag (K := K) (torusVec ζ i₁ k₁) ∈ H) :
    2 ≤ CFSG.Open.pRank r (⊤ : Subgroup (StatedProj H)) := by
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hζ
    exact hr.out.one_lt.ne hζ
  have hcomm (a b : ι → Kˣ) : Commute (torusDiag (K := K) a) (torusDiag b) :=
    (Commute.all a b).map torusDiag
  refine two_le_pRank_statedProj hx hy (by rw [torusVec_pow_order hζ]; exact one_mem _)
    (by rw [torusVec_pow_order hζ]; exact one_mem _) ?_ ?_ ?_
  · rw [(hcomm _ _).eq]
    simp
  · rintro ⟨c, hc⟩
    rw [scalar_eq_torusDiag] at hc
    have e0 := torusDiag_hent hc i₀
    have e1 := torusDiag_hent hc i₁
    rw [torusVec_apply_left ζ h0] at e0
    rw [torusVec_apply_of_ne ζ hik.symm (Ne.symm hki)] at e1
    exact hζ1 (e0.symm.trans e1)
  · rintro n _ ⟨c, rfl⟩ h
    rw [← map_pow, torusVec_pow, scalar_eq_torusDiag, ← map_mul] at h
    have e0 := torusDiag_hent h i₁
    have e1 := torusDiag_hent h k₁
    have a1 : torusVec (ζ ^ n) i₀ k₀ i₁ = 1 := torusVec_apply_of_ne _ hik.symm hki.symm
    have a2 : torusVec (ζ ^ n) i₀ k₀ k₁ = 1 := torusVec_apply_of_ne _ hik'.symm hkk.symm
    have b1 : torusVec ζ i₁ k₁ i₁ = ζ := torusVec_apply_left ζ h1
    have b2 : torusVec ζ i₁ k₁ k₁ = ζ⁻¹ := torusVec_apply_right ζ h1
    simp only [Pi.mul_apply, a1, a2, b1, b2, one_mul] at e0 e1
    have h2 : ζ * ζ = 1 := mul_eq_one_iff_eq_inv.2 (e0.symm.trans e1)
    have h2' : ζ ^ 2 = 1 := by rw [pow_two]; exact h2
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr.out Nat.prime_two).1
      (hζ ▸ orderOf_dvd_of_pow_eq_one h2'))

end Torus

section Families

variable {K : Type} [Field K]

theorem torusDiag_mem_Sp {n : ℕ} {d : Fin n ⊕ Fin n → Kˣ}
    (hd : ∀ k, (d (Sum.inl k) : K) * (d (Sum.inr k) : K) = 1) : torusDiag d ∈ StatedSp n K := by
  refine Subgroup.subset_closure ?_
  show (torusDiag d : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ * fromBlocks 0 1 (-1) 0 *
      (torusDiag d : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = fromBlocks 0 1 (-1) 0
  rw [coe_torusDiag, diagonal_transpose]
  ext (a | a) (b | b)
  · simp [Matrix.diagonal_mul, Matrix.mul_diagonal]
  · by_cases hab : a = b
    · subst hab
      simpa [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.fromBlocks_apply₁₂,
        Matrix.one_apply] using hd a
    · simp [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.fromBlocks_apply₁₂, hab]
  · by_cases hab : a = b
    · subst hab
      simp [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.fromBlocks_apply₂₁]
      rw [mul_comm]
      exact hd a
    · simp [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.fromBlocks_apply₂₁, hab]
  · simp [Matrix.diagonal_mul, Matrix.mul_diagonal]

theorem two_le_pRank_three_of_rotGL {ι : Type} [Fintype ι] [DecidableEq ι] {H : Subgroup (GL ι K)}
    [Finite K] {e : Fin 2 ⊕ Fin 2 → ι} (he : Function.Injective e)
    (hH : ∀ k, rotGL (e (.inl k)) (e (.inr k)) ∈ H) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj H)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hne : ∀ a b : Fin 2 ⊕ Fin 2, a ≠ b → e a ≠ e b := fun _ _ h => he.ne h
  refine two_le_pRank_statedProj (hH 0) (hH 1) (by rw [rotGL_pow_three]; exact one_mem _)
    (by rw [rotGL_pow_three]; exact one_mem _) ?_ ?_ ?_
  · rw [(rotGL_commute (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide))
      (hne _ _ (by decide))).eq]
    simp
  · exact fun hx => mul_scalar_ne (g := 1) (hne _ _ (by decide)) (one_mulVec _)
      (rotMatrix_mulVec_left _ _) hx (one_mul _)
  · exact fun n c hc => mul_scalar_ne (hne _ _ (by decide))
      (rotGL_pow_mulVec_of_ne (hne _ _ (by decide)) (hne _ _ (by decide)) n)
      (rotMatrix_mulVec_left _ _) hc

theorem psl_two_le_pRank_three {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 4 ≤ n) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSL n K))) :=
  two_le_pRank_three_of_rotGL ((Fin.castLE_injective hn).comp finSumFinEquiv.injective)
    fun _ => Subgroup.subset_closure (det_rotMatrix _ _)

theorem psl_three_two_le_pRank {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 3 ≤ f) [Finite K] :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧
      2 ≤ CFSG.Open.pRank r (⊤ : Subgroup (StatedProj (StatedSL 3 K))) := by
  obtain ⟨r, hr, hrd, hr3⟩ := exists_prime_dvd_two_pow_sub_one hf
  have h8 : 8 ≤ 2 ^ f := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h2f : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  have hr2 : r ≠ 2 := by
    rintro rfl
    omega
  have := Fact.mk hr
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) r
    (by rw [Nat.card_units, hK]; exact hrd)
  exact ⟨r, hr, hr2, two_le_pRank_torus_shared hr3 hζ (i₀ := 0) (i₁ := 1) (i₂ := 2) (by decide)
    (by decide) (by decide) (torusDiag_mem_SL (prod_torusVec ζ _ _))
    (torusDiag_mem_SL (prod_torusVec ζ _ _))⟩

theorem psu_three_two_le_pRank {f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 2 ≤ f)
    (hf3 : f ≠ 3) [Finite K] :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧
      2 ≤ CFSG.Open.pRank r (⊤ : Subgroup (StatedProj (StatedSU 3 (2 ^ f) K))) := by
  obtain ⟨r, hr, hrd, hr3⟩ := exists_prime_dvd_two_pow_add_one hf hf3
  have h2f : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  have hr2 : r ≠ 2 := by
    rintro rfl
    omega
  have := Fact.mk hr
  have hq : 2 ^ f ≠ 0 := by positivity
  have hcard : Nat.card Kˣ = (2 ^ f + 1) * (2 ^ f - 1) := by
    rw [Nat.card_units, hK, ← Nat.sq_sub_sq, one_pow]
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) r
    (by rw [hcard]; exact hrd.mul_right _)
  have hζq : ζ ^ (2 ^ f + 1) = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (by rw [hζ]; exact hrd)
  exact ⟨r, hr, hr2, two_le_pRank_torus_shared hr3 hζ (i₀ := 0) (i₁ := 1) (i₂ := 2) (by decide)
    (by decide) (by decide)
    (torusDiag_mem_SU hq (prod_torusVec ζ _ _) (by rw [torusVec_pow, hζq, torusVec_one]))
    (torusDiag_mem_SU hq (prod_torusVec ζ _ _) (by rw [torusVec_pow, hζq, torusVec_one]))⟩

theorem psp_two_two_le_pRank {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) [Finite K] :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧
      2 ≤ CFSG.Open.pRank r (⊤ : Subgroup (StatedProj (StatedSp 2 K))) := by
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h2f : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  have hr : (2 ^ f - 1).minFac.Prime := Nat.minFac_prime (by omega)
  have hr2 : (2 ^ f - 1).minFac ≠ 2 := fun h => by
    have h' := Nat.minFac_dvd (2 ^ f - 1)
    rw [h] at h'
    omega
  have := Fact.mk hr
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) (2 ^ f - 1).minFac
    (by rw [Nat.card_units, hK]; exact Nat.minFac_dvd _)
  have hmem : ∀ a : Fin 2, torusDiag (K := K) (torusVec ζ (Sum.inl a) (Sum.inr a)) ∈
      StatedSp 2 K := fun a => by
    refine torusDiag_mem_Sp fun b => ?_
    by_cases hb : b = a
    · subst hb
      rw [torusVec_apply_left ζ Sum.inl_ne_inr, torusVec_apply_right ζ Sum.inl_ne_inr]
      simp
    · rw [torusVec_apply_of_ne ζ (by simpa using hb) Sum.inl_ne_inr,
        torusVec_apply_of_ne ζ Sum.inr_ne_inl (by simpa using hb)]
      simp
  exact ⟨_, hr, hr2, two_le_pRank_torus_disjoint hr2 hζ (i₀ := Sum.inl 0) (i₁ := Sum.inl 1)
    (k₀ := Sum.inr 0) (k₁ := Sum.inr 1) Sum.inl_ne_inr Sum.inl_ne_inr (by simp) Sum.inl_ne_inr
    Sum.inr_ne_inl (by simp) (hmem 0) (hmem 1)⟩

theorem psu_three_eight_two_le_pRank [Finite K] (hK : Nat.card K = (2 ^ 3) ^ 2) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSU 3 (2 ^ 3) K))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card Kˣ = 63 := by
    rw [Nat.card_units, hK]
    norm_num
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  rw [hcard] at hg
  set ζ : Kˣ := g ^ 7 with hζdef
  have hζ : orderOf ζ = 9 := by
    rw [hζdef, orderOf_pow_of_dvd (by norm_num) (by rw [hg]; norm_num), hg]
  have hζ9 : ζ ^ 9 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hζ3 : ζ ^ 3 ≠ 1 := fun h => by
    have := orderOf_dvd_of_pow_eq_one h
    rw [hζ] at this
    omega
  set ω : Kˣ := ζ ^ 3 with hωdef
  have hω3 : ω ^ 3 = 1 := by rw [hωdef, ← pow_mul]; exact hζ9
  have hω1 : ω ≠ 1 := hζ3
  have hq : (2 ^ 3 : ℕ) ≠ 0 := by norm_num
  have hprodA : ∏ i, (![ω, ω ^ 2, 1] : Fin 3 → Kˣ) i = 1 := by
    rw [Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, mul_one]
    rw [← pow_succ', hω3]
  have hprodB : ∏ i, (![ζ, ζ, ζ⁻¹ ^ 2] : Fin 3 → Kˣ) i = 1 := by
    rw [Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    rw [← pow_two, ← mul_pow, mul_inv_cancel, one_pow]
  have hω9 : ω ^ 9 = 1 := by rw [show 9 = 3 * 3 from rfl, pow_mul, hω3, one_pow]
  have hA9 : (![ω, ω ^ 2, 1] : Fin 3 → Kˣ) ^ (2 ^ 3 + 1) = 1 := by
    funext i
    fin_cases i <;> simp [Pi.pow_apply]
    · exact hω9
    · rw [← pow_mul, show 2 * 9 = 3 * 6 from rfl, pow_mul, hω3, one_pow]
  have hB9 : (![ζ, ζ, ζ⁻¹ ^ 2] : Fin 3 → Kˣ) ^ (2 ^ 3 + 1) = 1 := by
    funext i
    fin_cases i <;> simp [Pi.pow_apply]
    · exact hζ9
    · exact hζ9
    · rw [← pow_mul, show 2 * 9 = 9 * 2 from rfl, pow_mul, hζ9, one_pow]
  have hA3 : (![ω, ω ^ 2, 1] : Fin 3 → Kˣ) ^ 3 = fun _ => 1 := by
    funext i
    fin_cases i <;> simp [Pi.pow_apply]
    · exact hω3
    · rw [← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hω3, one_pow]
  have hB3 : (![ζ, ζ, ζ⁻¹ ^ 2] : Fin 3 → Kˣ) ^ 3 = fun _ => ω := by
    funext i
    fin_cases i <;> simp [Pi.pow_apply]
    · exact hωdef.symm
    · exact hωdef.symm
    · rw [← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, ← hωdef]
      exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ]; exact hω3)
  refine two_le_pRank_diag (a := ![ω, ω ^ 2, 1]) (b := ![ζ, ζ, ζ⁻¹ ^ 2])
    (torusDiag_mem_SU hq hprodA hA9) (torusDiag_mem_SU hq hprodB hB9) ⟨1, hA3⟩ ⟨ω, hB3⟩
    ⟨0, 2, by simpa using hω1⟩ ?_
  intro n c
  by_contra hcon
  push Not at hcon
  have h0 := hcon 0
  have h1 := hcon 1
  have h2 := hcon 2
  simp at h0 h1 h2
  rw [h2] at h0 h1
  have e0 : ω ^ n = ω := by
    have := mul_inv_eq_iff_eq_mul.1 h0
    rw [this, ← pow_succ']
  have e1 : (ω ^ 2) ^ n = ω := by
    have := mul_inv_eq_iff_eq_mul.1 h1
    rw [this, ← pow_succ']
  rw [← pow_mul, mul_comm, pow_mul, e0] at e1
  exact hω1 (mul_left_cancel (a := ω) (by rw [mul_one, ← pow_two]; exact e1))

@[expose] def cycleMatrix : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

@[expose] def cycleMatrixInv : Matrix (Fin 3) (Fin 3) K := !![0, 1, 0; 0, 0, 1; 1, 0, 0]

theorem cycleMatrix_mul_inv : (cycleMatrix : Matrix (Fin 3) (Fin 3) K) * cycleMatrixInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cycleMatrix, cycleMatrixInv, Matrix.mul_apply,
    Fin.sum_univ_three]

theorem cycleMatrix_inv_mul : (cycleMatrixInv : Matrix (Fin 3) (Fin 3) K) * cycleMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cycleMatrix, cycleMatrixInv, Matrix.mul_apply,
    Fin.sum_univ_three]

@[expose] def cycleGL : GL (Fin 3) K :=
  ⟨cycleMatrix, cycleMatrixInv, cycleMatrix_mul_inv, cycleMatrix_inv_mul⟩

theorem cycleMatrix_pow_three : (cycleMatrix : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
  rw [pow_succ, pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cycleMatrix, Matrix.mul_apply, Fin.sum_univ_three]

theorem cycle_mul_diag (ω : K) (hω : ω ^ 3 = 1) :
    (cycleMatrix : Matrix (Fin 3) (Fin 3) K) * diagonal ![ω, ω ^ 2, 1] =
      (diagonal ![ω, ω ^ 2, 1] * cycleMatrix) * Matrix.scalar (Fin 3) (ω ^ 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycleMatrix, Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
  all_goals first | linear_combination (-1 : K) * hω | linear_combination (-ω) * hω

theorem psl_three_four_two_le_pRank [Finite K] (hK : Nat.card K = 2 ^ 2) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSL 3 K))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card Kˣ = 3 := by
    rw [Nat.card_units, hK]
    norm_num
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rw [hcard])
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hω1 : ω ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hω
    omega
  have hω2 : ω ^ 2 ≠ ω := fun h =>
    hω1 (mul_left_cancel (a := ω) (by rw [mul_one, ← pow_two]; exact h))
  have hprod : ∏ i, (![ω, ω ^ 2, 1] : Fin 3 → Kˣ) i = 1 := by
    rw [Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, mul_one]
    rw [← pow_succ', hω3]
  have hcube : (![ω, ω ^ 2, 1] : Fin 3 → Kˣ) ^ 3 = 1 := by
    funext i
    fin_cases i <;> simp [Pi.pow_apply]
    · exact hω3
    · rw [← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hω3, one_pow]
  have hdet : (cycleMatrix : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    simp [cycleMatrix, Matrix.det_fin_three]
  refine two_le_pRank_statedProj (x := torusDiag (K := K) ![ω, ω ^ 2, 1]) (y := cycleGL)
    (torusDiag_mem_SL hprod) (Subgroup.subset_closure hdet) ?_ ?_ ?_ ?_ ?_
  · rw [← map_pow, hcube, map_one]
    exact one_mem _
  · rw [show (cycleGL : GL (Fin 3) K) ^ 3 = 1 from
      Units.ext (by rw [Units.val_pow_eq_pow_val]; exact cycleMatrix_pow_three)]
    exact one_mem _
  · show _ ∈ (GeneralLinearGroup.scalar (Fin 3) (R := K)).range
    rw [MonoidHom.mem_range]
    refine ⟨ω ^ 2, ?_⟩
    rw [eq_comm, inv_mul_eq_iff_eq_mul]
    apply Units.ext
    have hω3' : (ω : K) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]
    have hd : (fun i => ((![ω, ω ^ 2, 1] : Fin 3 → Kˣ) i : K)) =
        ![(ω : K), (ω : K) ^ 2, 1] := by
      funext i
      fin_cases i <;> simp
    simp only [Units.val_mul, coe_torusDiag, hd, GeneralLinearGroup.coe_scalar,
      Units.val_pow_eq_pow_val]
    exact cycle_mul_diag (ω : K) hω3'
  · rintro ⟨c, hc⟩
    rw [scalar_eq_torusDiag] at hc
    have e0 := torusDiag_hent hc 0
    have e1 := torusDiag_hent hc 1
    simp at e0 e1
    exact hω2 (e1.symm.trans e0)
  · rintro n _ ⟨c, rfl⟩ h
    have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 2) h
    simp [cycleGL, cycleMatrix, Matrix.mul_apply, Fin.sum_univ_three, coe_torusDiag] at this
    rw [Matrix.diagonal_pow, Matrix.diagonal_apply_ne _ (by decide : (0 : Fin 3) ≠ 2),
      zero_mul] at this
    exact zero_ne_one this

end Families

section Alternating

open Equiv

theorem two_le_pRank_alternating {n : ℕ} (hn : 6 ≤ n) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (alternatingGroup (Fin n))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let p0 : Fin n := ⟨0, by omega⟩
  let p1 : Fin n := ⟨1, by omega⟩
  let p2 : Fin n := ⟨2, by omega⟩
  let p3 : Fin n := ⟨3, by omega⟩
  let p4 : Fin n := ⟨4, by omega⟩
  let p5 : Fin n := ⟨5, by omega⟩
  have h01 : p0 ≠ p1 := fun h => by simp [p0, p1, Fin.ext_iff] at h
  have h02 : p0 ≠ p2 := fun h => by simp [p0, p2, Fin.ext_iff] at h
  have h12 : p1 ≠ p2 := fun h => by simp [p1, p2, Fin.ext_iff] at h
  have h34 : p3 ≠ p4 := fun h => by simp [p3, p4, Fin.ext_iff] at h
  have h35 : p3 ≠ p5 := fun h => by simp [p3, p5, Fin.ext_iff] at h
  have h45 : p4 ≠ p5 := fun h => by simp [p4, p5, Fin.ext_iff] at h
  have hx3 : (swap p0 p1 * swap p0 p2).IsThreeCycle :=
    Perm.isThreeCycle_swap_mul_swap_same h01 h02 h12
  have hy3 : (swap p3 p4 * swap p3 p5).IsThreeCycle :=
    Perm.isThreeCycle_swap_mul_swap_same h34 h35 h45
  let x : alternatingGroup (Fin n) := ⟨_, Perm.mem_alternatingGroup.2 hx3.sign⟩
  let y : alternatingGroup (Fin n) := ⟨_, Perm.mem_alternatingGroup.2 hy3.sign⟩
  have hxfix : ∀ z : Fin n, z ≠ p0 → z ≠ p1 → z ≠ p2 → (swap p0 p1 * swap p0 p2) z = z :=
    fun z a b c => threeCycle_apply_of_ne a b c
  have hyfix : ∀ z : Fin n, z ≠ p3 → z ≠ p4 → z ≠ p5 → (swap p3 p4 * swap p3 p5) z = z :=
    fun z a b c => threeCycle_apply_of_ne a b c
  have hp30 : p3 ≠ p0 := fun h => by simp [p0, p3, Fin.ext_iff] at h
  have hp31 : p3 ≠ p1 := fun h => by simp [p1, p3, Fin.ext_iff] at h
  have hp32 : p3 ≠ p2 := fun h => by simp [p2, p3, Fin.ext_iff] at h
  refine two_le_pRank_of_gens (x := x) (y := y) ?_ ?_ ?_ ?_ ?_
  · apply Subtype.ext
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    change (swap p0 p1 * swap p0 p2) ^ 3 = 1
    rw [← hx3.orderOf]
    exact pow_orderOf_eq_one _
  · apply Subtype.ext
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    change (swap p3 p4 * swap p3 p5) ^ 3 = 1
    rw [← hy3.orderOf]
    exact pow_orderOf_eq_one _
  · have hd : Perm.Disjoint (swap p0 p1 * swap p0 p2) (swap p3 p4 * swap p3 p5) := by
      intro z
      by_cases hz : z.val < 3
      · right
        exact hyfix z (fun h => by simp [p3, Fin.ext_iff] at h; omega)
          (fun h => by simp [p4, Fin.ext_iff] at h; omega)
          (fun h => by simp [p5, Fin.ext_iff] at h; omega)
      · left
        exact hxfix z (fun h => by simp [p0, Fin.ext_iff] at h; omega)
          (fun h => by simp [p1, Fin.ext_iff] at h; omega)
          (fun h => by simp [p2, Fin.ext_iff] at h; omega)
    exact Subtype.ext hd.commute.eq
  · intro h
    have h1 : (swap p0 p1 * swap p0 p2) p0 = p0 := by
      have := congrArg (fun g : alternatingGroup (Fin n) => (g : Perm (Fin n)) p0) h
      change (swap p0 p1 * swap p0 p2) p0 = ((1 : alternatingGroup (Fin n)) : Perm (Fin n)) p0
        at this
      simpa using this
    rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne h02.symm h12.symm] at h1
    exact h02 h1.symm
  · intro m h
    have h1 : ((x ^ m : alternatingGroup (Fin n)) : Perm (Fin n)) p3 = p3 := by
      rw [SubgroupClass.coe_pow]
      exact Perm.pow_apply_eq_self_of_apply_eq_self (hxfix p3 hp30 hp31 hp32) m
    rw [h] at h1
    change (swap p3 p4 * swap p3 p5) p3 = p3 at h1
    rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne h35.symm h45.symm] at h1
    exact h35 h1.symm

end Alternating

end A3Facts

end CFSG.Quasithin
