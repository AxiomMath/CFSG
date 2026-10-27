module

public import CFSG.RankThree.GF2n.Tim79Pair

public section

namespace CFSG.RankThree.GF2n.Stroth80.FieldModel

open Polynomial

section Arith

theorem pow_two_modEq_inj {n i j : ℕ} (hi : i < n) (hj : j < n)
    (h : 2 ^ i ≡ 2 ^ j [MOD 2 ^ n - 1]) : i = j := by
  by_contra hne
  wlog hlt : i < j generalizing i j
  · exact this hj hi h.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne))
  have hle : 2 ^ i ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hlt.le
  have hd : 2 ^ n - 1 ∣ 2 ^ j - 2 ^ i := (Nat.modEq_iff_dvd' hle).mp h
  have hodd : Nat.Coprime (2 ^ n - 1) (2 ^ i) := by
    have : Nat.Coprime (2 ^ n - 1) 2 := by
      have h2 : 2 ≤ 2 ^ n := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hodd : Odd (2 ^ n - 1) :=
        Nat.Even.sub_odd (by omega) (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
      exact Nat.coprime_comm.mp (Nat.coprime_two_left.mpr hodd)
    exact Nat.Coprime.pow_right _ this
  have e : 2 ^ j - 2 ^ i = 2 ^ i * (2 ^ (j - i) - 1) := by
    rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_of_le hlt.le]
  rw [e] at hd
  have hd2 : 2 ^ n - 1 ∣ 2 ^ (j - i) - 1 := hodd.dvd_of_dvd_mul_left hd
  have hpos : 0 < 2 ^ (j - i) - 1 := by
    have : 2 ≤ 2 ^ (j - i) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (j - i) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hlt2 : 2 ^ (j - i) < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have := Nat.le_of_dvd hpos hd2
  omega

end Arith

section Field

variable {K : Type*} [Field K] [Finite K]

theorem pow_two_pow_card {n : ℕ} (hK : Nat.card K = 2 ^ n) (x : K) : x ^ 2 ^ n = x := by
  classical
  haveI := Fintype.ofFinite K
  have := FiniteField.pow_card x
  rwa [← Nat.card_eq_fintype_card, hK] at this

theorem lt_two_pow_of_three_le {n : ℕ} (hn : 3 ≤ n) : n + 2 < 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ]; omega

theorem orderOf_pow_two_pow {n i : ℕ} {a : K} (hn : 1 ≤ n) (ha : orderOf a = 2 ^ n - 1) :
    orderOf (a ^ 2 ^ i) = 2 ^ n - 1 := by
  have hodd : Odd (2 ^ n - 1) :=
    Nat.Even.sub_odd (Nat.one_le_two_pow) (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  have hcop : Nat.Coprime (orderOf a) (2 ^ i) := by
    rw [ha]
    exact Nat.Coprime.pow_right _ (Nat.coprime_comm.mp (Nat.coprime_two_left.mpr hodd))
  rw [Nat.Coprime.orderOf_pow hcop, ha]



theorem pow_eq_pow_iff_modEq_field {a : K} (ha0 : a ≠ 0) {m m' : ℕ} :
    a ^ m = a ^ m' ↔ m ≡ m' [MOD orderOf a] := by
  have hu : orderOf (Units.mk0 a ha0) = orderOf a :=
    (orderOf_units (y := Units.mk0 a ha0)).symm
  rw [← hu, ← pow_eq_pow_iff_modEq]
  constructor
  · intro h
    exact Units.ext (by simpa using h)
  · intro h
    simpa using congrArg Units.val h

theorem orderOf_inv_field (a : K) : orderOf a⁻¹ = orderOf a :=
  orderOf_eq_orderOf_iff.mpr fun m => by rw [inv_pow, inv_eq_one]

theorem nat_core (A B P : ℕ) (h1 : A ≤ P) (h2 : 2 ≤ A) (h3 : 1 ≤ B) (h4 : 2 * B ≤ P) (h5 : 3 < P)
    (h6 : ((P - 1 : ℕ) : ℤ) ∣ ((1 + B : ℕ) : ℤ) - (A : ℤ)) : 1 + B = A := by
  have h0 := Int.eq_zero_of_abs_lt_dvd h6 (by rw [abs_lt]; constructor <;> push_cast <;> omega)
  omega

theorem no_coset_of_closed {n : ℕ} (hn : 3 ≤ n) (hK : Nat.card K = 2 ^ n) {a : K}
    (ha : orderOf a = 2 ^ n - 1) (S : Set K) (hsq : ∀ x ∈ S, x ^ 2 ∈ S)
    (hS : ∀ x ∈ S, x = 1 ∨ ∃ i < n, x = a ^ 2 ^ i) {d : ℕ} (hd3 : 3 ≤ d)
    (hdN : d ∣ 2 ^ n - 1) {μ : K} (hμ0 : μ ≠ 0) (hμ : ∀ ζ : K, ζ ^ d = 1 → μ * ζ ∈ S) :
    False := by
  classical
  haveI := Fintype.ofFinite K
  have hlt := lt_two_pow_of_three_le hn
  have hNpos : 0 < 2 ^ n - 1 := by omega
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [orderOf_zero] at ha
    omega
  have hsqk : ∀ k, ∀ x ∈ S, x ^ 2 ^ k ∈ S := by
    intro k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih =>
      intro x hx
      have := hsq _ (ih x hx)
      rwa [← pow_mul, ← pow_succ] at this
  set O : Finset K := (Finset.range n).image (fun i => a ^ 2 ^ i) with hO
  have hOcard : O.card ≤ n := Finset.card_image_le.trans (by simp)
  have hSsub : ∀ x ∈ S, x ∈ insert (1 : K) O := by
    intro x hx
    rcases hS x hx with h | ⟨i, hi, h⟩
    · simp [h]
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, h.symm⟩)
  have hdne : d ≠ 2 ^ n - 1 := by
    intro hdeq
    have hmem : ∀ x ∈ (Finset.univ.erase (0 : K)), μ * x ∈ insert (1 : K) O := by
      intro x hx
      have hx0 : x ≠ 0 := Finset.ne_of_mem_erase hx
      refine hSsub _ (hμ x ?_)
      rw [hdeq, ← hK]
      have := FiniteField.pow_card_sub_one_eq_one x hx0
      rwa [← Nat.card_eq_fintype_card] at this
    have hcard := Finset.card_le_card_of_injOn (fun x => μ * x) hmem
      (fun x _ y _ h => mul_left_cancel₀ hμ0 h)
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card, hK] at hcard
    have h2 : (insert (1 : K) O).card ≤ n + 1 :=
      (Finset.card_insert_le _ _).trans (by omega)
    omega
  have hdlt : d < 2 ^ n - 1 := lt_of_le_of_ne (Nat.le_of_dvd hNpos hdN) hdne
  obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hcardu : Nat.card Kˣ = 2 ^ n - 1 := by rw [Nat.card_units, hK]
  rw [hcardu] at hg₀
  have hg₀' : orderOf (g₀ : K) = 2 ^ n - 1 := by rw [orderOf_units]; exact hg₀
  have hdpos : 0 < d := by omega
  obtain ⟨e, he⟩ := hdN
  have hepos : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · rw [h, mul_zero] at he; omega
    · exact h
  have hed : (2 ^ n - 1) / d = e := by
    rw [he]; exact Nat.mul_div_cancel_left e hdpos
  set ζ₁ : K := (g₀ : K) ^ e with hζ₁def
  have hζ₁ : orderOf ζ₁ = d := by
    rw [hζ₁def, orderOf_pow_of_dvd (by omega) (by rw [hg₀', he]; exact Dvd.intro_left _ rfl),
      hg₀', he, Nat.mul_div_cancel _ hepos]
  have hζd : ζ₁ ^ d = 1 := by rw [← hζ₁]; exact pow_orderOf_eq_one ζ₁
  have hζ2d : (ζ₁ ^ 2) ^ d = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζd, one_pow]
  have hζne : ζ₁ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hζ₁
    omega
  have hμS : μ ∈ S := by simpa using hμ 1 (one_pow d)
  have hdvd : d ∣ 2 ^ n - 1 := ⟨e, he⟩
  rcases hS μ hμS with hμ1 | ⟨i, hi, hμi⟩
  ·
    have h1 : ζ₁ ∈ S := by simpa [hμ1] using hμ ζ₁ hζd
    rcases hS ζ₁ h1 with h | ⟨j, hj, hj'⟩
    · exact hζne h
    · have : orderOf ζ₁ = 2 ^ n - 1 := by rw [hj']; exact orderOf_pow_two_pow (by omega) ha
      omega
  ·
    have hA : ∀ ζ₀ : K, ζ₀ ^ d = 1 → a * ζ₀ ∈ S := by
      intro ζ₀ hζ₀
      have h1 : μ * ζ₀ ^ 2 ^ i ∈ S := hμ _ (by rw [← pow_mul, mul_comm, pow_mul, hζ₀, one_pow])
      have h2 := hsqk (n - i) _ h1
      have e2 : (μ * ζ₀ ^ 2 ^ i) ^ 2 ^ (n - i) = a * ζ₀ := by
        rw [hμi, ← mul_pow, ← pow_mul, ← pow_add, Nat.add_sub_of_le hi.le, pow_two_pow_card hK]
      rwa [e2] at h2
    have hA1 := hA ζ₁ hζd
    have hA2 := hA (ζ₁ ^ 2) hζ2d
    rcases hS _ hA1 with h1 | ⟨j, hj, hj'⟩
    · have hζinv : ζ₁ = a⁻¹ := eq_inv_of_mul_eq_one_right h1
      have : orderOf ζ₁ = 2 ^ n - 1 := by rw [hζinv, orderOf_inv_field, ha]
      omega
    rcases hS _ hA2 with h2 | ⟨k, hk, hk'⟩
    · have h3 : ζ₁ ^ 2 = a⁻¹ := eq_inv_of_mul_eq_one_right h2
      have h4 : orderOf (ζ₁ ^ 2) = 2 ^ n - 1 := by rw [h3, orderOf_inv_field, ha]
      have h5 : orderOf (ζ₁ ^ 2) ∣ d := orderOf_dvd_of_pow_eq_one hζ2d
      rw [h4] at h5
      have := Nat.le_of_dvd hdpos h5
      omega
    ·
      have hj0 : j ≠ 0 := by
        rintro rfl
        apply hζne
        have : a * ζ₁ = a * 1 := by rw [hj']; simp
        exact mul_left_cancel₀ ha0 this
      have e1 : a ^ 2 ^ (j + 1) = a ^ (1 + 2 ^ k) := by
        calc a ^ 2 ^ (j + 1) = (a ^ 2 ^ j) ^ 2 := by rw [pow_succ, pow_mul]
          _ = (a * ζ₁) ^ 2 := by rw [hj']
          _ = a * (a * ζ₁ ^ 2) := by ring
          _ = a * a ^ 2 ^ k := by rw [hk']
          _ = a ^ (1 + 2 ^ k) := by rw [pow_add, pow_one]
      have hmod : 2 ^ (j + 1) ≡ 1 + 2 ^ k [MOD 2 ^ n - 1] := by
        have := (pow_eq_pow_iff_modEq_field ha0).mp e1
        rwa [ha] at this
      have hdvdz := (Nat.modEq_iff_dvd.mp hmod)
      have hA' : 2 ^ (j + 1) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hA2' : 2 ≤ 2 ^ (j + 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hB1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      have hB2 : 2 * 2 ^ k ≤ 2 ^ n := by
        rw [← pow_succ']
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have heq : 1 + 2 ^ k = 2 ^ (j + 1) :=
        nat_core _ _ _ hA' hA2' hB1 hB2 (by omega) hdvdz
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · rw [hk0] at heq
        have : 2 ^ (j + 1) = 2 ^ 1 := by omega
        have := Nat.pow_right_injective (le_refl 2) this
        omega
      · have h2k : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
        have h2j : 2 ∣ 2 ^ (j + 1) := dvd_pow_self 2 (by omega)
        omega


variable [CharP K 2]

theorem eval₂_sq (g : ℕ[X]) (x : K) :
    g.eval₂ (Nat.castRingHom K) (x ^ 2) = (g.eval₂ (Nat.castRingHom K) x) ^ 2 := by
  haveI : ExpChar K 2 := ExpChar.prime Nat.prime_two
  have h := Polynomial.hom_eval₂ g (Nat.castRingHom K) (frobenius K 2) x
  have hc : (frobenius K 2).comp (Nat.castRingHom K) = Nat.castRingHom K :=
    Subsingleton.elim _ _
  rw [hc] at h
  simpa [frobenius_def] using h.symm

theorem root_eq_pow_of_eval {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) {a : K}
    (ha : orderOf a = 2 ^ n - 1) (g : ℕ[X]) (hmon : g.Monic) (hdeg : g.natDegree ≤ n)
    (hga : g.eval₂ (Nat.castRingHom K) a = 0) {x : K} (hx : g.eval₂ (Nat.castRingHom K) x = 0) :
    ∃ i < n, x = a ^ 2 ^ i := by
  classical
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [orderOf_zero] at ha
    have : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  set gK : K[X] := g.map (Nat.castRingHom K) with hgK
  have hgKmon : gK.Monic := hmon.map _
  have hgK0 : gK ≠ 0 := hgKmon.ne_zero
  have hgKdeg : gK.natDegree ≤ n := (natDegree_map_le).trans hdeg
  set O : Finset K := (Finset.range n).image (fun i => a ^ 2 ^ i) with hO
  have hOinj : Set.InjOn (fun i : ℕ => a ^ 2 ^ i) (Finset.range n : Set ℕ) := by
    intro i hi j hj hij
    have h := (pow_eq_pow_iff_modEq_field ha0).mp hij
    rw [ha] at h
    exact pow_two_modEq_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) h
  have hOcard : O.card = n := by
    rw [hO, Finset.card_image_of_injOn hOinj, Finset.card_range]
  have hOroots : ∀ i : ℕ, g.eval₂ (Nat.castRingHom K) (a ^ 2 ^ i) = 0 := by
    intro i
    induction i with
    | zero => simpa using hga
    | succ i ih =>
      have := eval₂_sq g (a ^ 2 ^ i)
      rw [ih, ← pow_mul, ← pow_succ] at this
      simpa using this
  set R : Finset K := gK.roots.toFinset with hR
  have hRmem : ∀ y : K, y ∈ R ↔ g.eval₂ (Nat.castRingHom K) y = 0 := by
    intro y
    rw [hR, Multiset.mem_toFinset, mem_roots hgK0, IsRoot.def, hgK, eval_map]
  have hOR : O ⊆ R := by
    intro y hy
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
    exact (hRmem _).mpr (hOroots i)
  have hRcard : R.card ≤ n := by
    calc R.card ≤ Multiset.card gK.roots := Multiset.toFinset_card_le _
      _ ≤ gK.natDegree := card_roots' _
      _ ≤ n := hgKdeg
  have hRO : R = O := (Finset.eq_of_subset_of_card_le hOR (by omega)).symm
  have hxR : x ∈ R := (hRmem x).mpr hx
  rw [hRO] at hxR
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hxR
  exact ⟨i, Finset.mem_range.mp hi, rfl⟩


theorem no_coset_of_poly {n : ℕ} (hn : 3 ≤ n) (hK : Nat.card K = 2 ^ n) {a : K}
    (ha : orderOf a = 2 ^ n - 1) (g : ℕ[X]) (hmon : g.Monic) (hdeg : g.natDegree ≤ n)
    (hga : g.eval₂ (Nat.castRingHom K) a = 0) {d : ℕ} (hd3 : 3 ≤ d) (hdN : d ∣ 2 ^ n - 1)
    {μ : K} (hμ0 : μ ≠ 0)
    (hμ : ∀ ζ : K, ζ ^ d = 1 → (μ * ζ - 1) * g.eval₂ (Nat.castRingHom K) (μ * ζ) = 0) :
    False := by
  refine no_coset_of_closed hn hK ha {x | x = 1 ∨ g.eval₂ (Nat.castRingHom K) x = 0} ?_ ?_ hd3
    hdN hμ0 ?_
  · rintro x (h | h)
    · left; rw [h]; simp
    · right; rw [eval₂_sq, h]; simp
  · rintro x (h | h)
    · exact Or.inl h
    · exact Or.inr (root_eq_pow_of_eval (by omega) hK ha g hmon hdeg hga h)
  · intro ζ hζ
    have := hμ ζ hζ
    rcases mul_eq_zero.mp this with h | h
    · left; exact sub_eq_zero.mp h
    · right; exact h


end Field

section Eigen

variable {K : Type*} [Field K] [Finite K]

theorem exists_unit_generator : ∃ g₀ : Kˣ, ∀ x : Kˣ, x ∈ Subgroup.zpowers g₀ :=
  IsCyclic.exists_generator

theorem exists_eigenvector_of_pow_eq_one {W : Type*} [AddCommGroup W] [Module K W] [Nontrivial W]
    (S : W →ₗ[K] W) {e : ℕ} (he : 0 < e) (hdvd : e ∣ Nat.card K - 1) (hS : S ^ e = 1) :
    ∃ (ℓ : K) (v : W), v ≠ 0 ∧ S v = ℓ • v ∧ ℓ ^ e = 1 := by
  classical
  obtain ⟨g₀, hg₀⟩ := exists_unit_generator (K := K)
  have hcard : orderOf g₀ = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hg₀
  have hcardu : Nat.card Kˣ = Nat.card K - 1 := Nat.card_units K
  obtain ⟨c, hc⟩ := hdvd
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · have hpos : 0 < Nat.card K - 1 := by
        rw [← hcardu]; exact Nat.card_pos
      rw [h, mul_zero] at hc; omega
    · exact h
  set ζ : K := (g₀ : K) ^ c with hζdef
  have hζ : IsPrimitiveRoot ζ e := by
    rw [IsPrimitiveRoot.iff_orderOf, hζdef]
    have h1 : orderOf (g₀ : K) = Nat.card K - 1 := by rw [orderOf_units, hcard, hcardu]
    rw [orderOf_pow_of_dvd (by omega) (by rw [h1, hc]; exact Dvd.intro_left _ rfl), h1, hc,
      Nat.mul_div_cancel _ hcpos]
  have hprod := Polynomial.X_pow_sub_one_eq_prod (R := K) he hζ
  by_contra hcon
  push Not at hcon
  have hinj : ∀ r ∈ Polynomial.nthRootsFinset e (1 : K),
      Function.Injective (Polynomial.aeval S (X - C r)) := by
    intro r hr
    rw [Polynomial.mem_nthRootsFinset he] at hr
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    by_contra hv0
    have : S v = r • v := by
      have h1 : (Polynomial.aeval S (X - C r)) v = 0 := hv
      simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.sub_apply,
        Module.algebraMap_end_apply] at h1
      exact sub_eq_zero.mp h1
    exact hcon r v hv0 this hr
  have hprodinj0 : ∀ t : Finset K, (∀ r ∈ t, Function.Injective (Polynomial.aeval S (X - C r))) →
      Function.Injective (Polynomial.aeval S (∏ r ∈ t, (X - C r))) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _
      rw [Finset.prod_empty, map_one]
      exact fun a b hab => hab
    | insert r t hr ih =>
      intro h
      rw [Finset.prod_insert hr, map_mul]
      intro a b hab
      rw [Module.End.mul_apply, Module.End.mul_apply] at hab
      exact ih (fun x hx => h x (Finset.mem_insert_of_mem hx))
        ((h r (Finset.mem_insert_self _ _)) hab)
  have hprodinj : Function.Injective
      (Polynomial.aeval S (∏ r ∈ Polynomial.nthRootsFinset e (1 : K), (X - C r))) :=
    hprodinj0 _ hinj
  rw [← hprod] at hprodinj
  have hz : Polynomial.aeval S (X ^ e - 1 : K[X]) = 0 := by
    simp [hS]
  rw [hz] at hprodinj
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  exact hw (hprodinj (by simp))


theorem exists_pow_eq_of_pow_eq_one {d e : ℕ} (he : 0 < e) (hde : d * e = Nat.card K - 1)
    {ℓ : K} (hℓ : ℓ ^ e = 1) : ∃ μ : K, μ ^ d = ℓ := by
  classical
  have hℓ0 : ℓ ≠ 0 := by
    rintro rfl
    rw [zero_pow he.ne'] at hℓ
    exact zero_ne_one hℓ
  obtain ⟨g₀, hg₀⟩ := exists_unit_generator (K := K)
  have hcard : orderOf g₀ = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hg₀
  have hcardu : Nat.card Kˣ = Nat.card K - 1 := Nat.card_units K
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg₀ (Units.mk0 ℓ hℓ0))
  have h1 : g₀ ^ (m * e) = 1 := by
    rw [zpow_mul, hm]
    apply Units.ext
    simpa using hℓ
  have h2 : ((orderOf g₀ : ℕ) : ℤ) ∣ m * e := orderOf_dvd_iff_zpow_eq_one.mpr h1
  rw [hcard, hcardu, ← hde] at h2
  have h3 : (d : ℤ) ∣ m := by
    have : ((d * e : ℕ) : ℤ) ∣ m * e := h2
    push_cast at this
    exact Int.dvd_of_mul_dvd_mul_right (by exact_mod_cast he.ne') this
  obtain ⟨m', hm'⟩ := h3
  refine ⟨((g₀ ^ m' : Kˣ) : K), ?_⟩
  have : ((g₀ ^ m' : Kˣ) : K) ^ d = ((g₀ ^ m' : Kˣ) ^ d : Kˣ) := by simp
  rw [this, ← zpow_natCast, ← zpow_mul, mul_comm m' d, ← hm', hm]
  simp

theorem eigen_coset {F : Type*} [AddCommGroup F] [Module K F] (T : F →ₗ[K] F) {d e : ℕ}
    (hd : 0 < d) (he : 0 < e) (hde : d * e = Nat.card K - 1) (hT : T ^ (d * e) = 1)
    (W U : Submodule K F) (hW : W ≠ ⊥) (hTW : ∀ w ∈ W, (T ^ d) w ∈ W)
    (hTU : ∀ i, 1 ≤ i → i < d → ∀ w ∈ W, (T ^ i) w ∈ U) (hWU : Disjoint W U) (f : K[X])
    (hf : ∀ w ∈ W, Polynomial.aeval T f w = 0) :
    ∃ μ : K, μ ≠ 0 ∧ ∀ ζ : K, ζ ^ d = 1 → f.eval (μ * ζ) = 0 := by
  classical
  haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  let S : W →ₗ[K] W := (T ^ d).restrict hTW
  have hSpow : ∀ k : ℕ, ∀ w : W, ((S ^ k) w : F) = (T ^ (d * k)) w := by
    intro k
    induction k with
    | zero => intro w; simp
    | succ k ih =>
      intro w
      rw [pow_succ, Module.End.mul_apply, ih, mul_add, mul_one, pow_add, Module.End.mul_apply]
      rfl
  have hS : S ^ e = 1 := by
    ext w
    show ((S ^ e) w : F) = (w : F)
    rw [hSpow, hT]
    rfl
  obtain ⟨ℓ, v, hv0, hSv, hℓ⟩ :=
    exists_eigenvector_of_pow_eq_one S he ⟨d, by rw [← hde, mul_comm]⟩ hS
  have hv'0 : (v : F) ≠ 0 := fun h => hv0 (Subtype.ext h)
  have hTv : (T ^ d) (v : F) = ℓ • (v : F) := by
    have := congrArg (fun x : W => (x : F)) hSv
    simpa [S] using this
  obtain ⟨μ, hμ⟩ := exists_pow_eq_of_pow_eq_one he hde hℓ
  have hℓ0 : ℓ ≠ 0 := by
    rintro rfl
    rw [zero_pow he.ne'] at hℓ
    exact zero_ne_one hℓ
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow hd.ne'] at hμ
    exact hℓ0 hμ.symm
  refine ⟨μ, hμ0, fun ζ hζ => ?_⟩
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hd.ne'] at hζ
    exact zero_ne_one hζ
  set κ : K := μ * ζ with hκ
  have hκ0 : κ ≠ 0 := mul_ne_zero hμ0 hζ0
  have hκd : κ ^ d = ℓ := by rw [hκ, mul_pow, hζ, mul_one, hμ]
  set v' : F := (v : F) with hv'
  set Fn : ℕ → F := fun j => (κ⁻¹ ^ j) • (T ^ j) v' with hFn
  set E : F := ∑ i ∈ Finset.range d, Fn i with hE
  have hFd : Fn d = v' := by
    rw [hFn]
    simp only
    rw [hTv, smul_smul, inv_pow, hκd, inv_mul_cancel₀ hℓ0, one_smul]
  have hF0 : Fn 0 = v' := by simp [hFn]
  have hTFn : ∀ i, T (Fn i) = κ • Fn (i + 1) := by
    intro i
    rw [hFn]
    simp only
    rw [map_smul, ← Module.End.mul_apply, ← pow_succ', smul_smul]
    congr 1
    rw [pow_succ]
    field_simp
  have hTE : T E = κ • E := by
    rw [hE, map_sum]
    simp_rw [hTFn]
    rw [← Finset.smul_sum]
    congr 1
    have h1 := Finset.sum_range_succ' Fn d
    have h2 := Finset.sum_range_succ Fn d
    rw [hFd, hF0] at *
    have : ∑ i ∈ Finset.range d, Fn (i + 1) = ∑ i ∈ Finset.range d, Fn i := by
      have h3 : ∑ i ∈ Finset.range d, Fn (i + 1) + v' = ∑ i ∈ Finset.range d, Fn i + v' := by
        rw [← h1, h2]
      exact add_right_cancel h3
    exact this
  have hE0 : E ≠ 0 := by
    intro hE0
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    have h1 := Finset.sum_range_succ' Fn d'
    rw [hE, h1, hF0] at hE0
    have hvU : v' ∈ U := by
      have : v' = -∑ i ∈ Finset.range d', Fn (i + 1) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]
        exact hE0
      rw [this]
      refine U.neg_mem (U.sum_mem fun i hi => ?_)
      have hi' : i + 1 < d' + 1 := by
        have := Finset.mem_range.mp hi
        omega
      rw [hFn]
      exact U.smul_mem _ (hTU (i + 1) (by omega) hi' v' v.2)
    have : v' ∈ W ⊓ U := ⟨v.2, hvU⟩
    rw [hWU.eq_bot, Submodule.mem_bot] at this
    exact hv'0 this
  have hcomm : Commute (Polynomial.aeval T f) T := by
    have : Polynomial.aeval T (f * X) = Polynomial.aeval T (X * f) := by rw [mul_comm]
    simp only [map_mul, Polynomial.aeval_X] at this
    exact this
  have hfE : Polynomial.aeval T f E = 0 := by
    rw [hE, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hFn]
    simp only
    rw [map_smul]
    have : Polynomial.aeval T f ((T ^ i) v') = (T ^ i) (Polynomial.aeval T f v') := by
      rw [← Module.End.mul_apply, (hcomm.pow_right i).eq, Module.End.mul_apply]
    rw [this, hf v' v.2, map_zero, smul_zero]
  have hev : Module.End.HasEigenvector T κ E :=
    ⟨Module.End.mem_eigenspace_iff.mpr hTE, hE0⟩
  have := Module.End.aeval_apply_of_hasEigenvector (p := f) hev
  rw [hfE] at this
  exact (smul_eq_zero.mp this.symm).resolve_right hE0


end Eigen

section Gamma

variable {K : Type*} [Field K] [Finite K]

theorem pow_gt_aux {q m : ℕ} (hq : 2 ≤ q) (hm : 2 ≤ m) : m * (q - 1) + 1 < q ^ m := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 2 := ⟨q - 2, by omega⟩
  have h1 : r + 2 - 1 = r + 1 := by omega
  rw [h1]
  induction m, hm using Nat.le_induction with
  | base => nlinarith
  | succ m hm ih =>
    rw [pow_succ]
    have h2 : (m * (r + 1) + 2) * (r + 2) ≤ (r + 2) ^ m * (r + 2) :=
      Nat.mul_le_mul_right _ ih
    nlinarith [Nat.zero_le (m * r * r), Nat.zero_le (m * r), Nat.zero_le m]

theorem exists_pow_eq_of_orderOf {a : K} (ha : orderOf a = Nat.card K - 1) (ha0 : a ≠ 0)
    {x : K} (hx : x ≠ 0) : ∃ k : ℕ, a ^ k = x := by
  have hu : orderOf (Units.mk0 a ha0) = Nat.card Kˣ := by
    rw [Nat.card_units K, ← ha, ← orderOf_units]
    rfl
  have htop : Subgroup.zpowers (Units.mk0 a ha0) = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hu]
  have hmem : Units.mk0 x hx ∈ Subgroup.zpowers (Units.mk0 a ha0) := by rw [htop]; trivial
  rw [← mem_powers_iff_mem_zpowers] at hmem
  obtain ⟨k, hk⟩ := hmem
  exact ⟨k, by simpa using congrArg Units.val hk⟩

end Gamma

section Eigen2

variable {K : Type*} [Field K] [Finite K]



theorem eq_one_of_conj {a : K} (hK3 : 3 ≤ Nat.card K) (ha : orderOf a = Nat.card K - 1)
    (θ : K →+ K) (hθ : Function.Bijective θ) (c : K) (σ : RingAut K)
    (h : ∀ x, θ (a * x) = c * σ (θ x)) : σ = 1 := by
  classical
  by_contra hσ
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Finite (RingAut K) :=
    Finite.of_injective (fun f : RingAut K => (f : K → K)) DFunLike.coe_injective
  haveI : Fintype (RingAut K) := Fintype.ofFinite _
  have hm0 : 0 < orderOf σ := orderOf_pos σ
  have hm2 : 2 ≤ orderOf σ := by
    have : orderOf σ ≠ 1 := fun h1 => hσ (orderOf_eq_one_iff.mp h1)
    omega
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [orderOf_zero] at ha
    omega
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h0 : ∀ x, θ x = 0 := by
      intro x
      have := h (a⁻¹ * x)
      rw [mul_inv_cancel_left₀ ha0] at this
      simpa using this
    obtain ⟨x, hx⟩ := hθ.2 1
    rw [h0 x] at hx
    exact zero_ne_one hx
  set m := orderOf σ with hm
  have hσm : σ ^ m = 1 := pow_orderOf_eq_one σ
  let cc : ℕ → K := fun k => ∏ i ∈ Finset.range k, (σ ^ i) c
  have hpw : ∀ i (x : K), (σ ^ (i + 1)) x = σ ((σ ^ i) x) := by
    intro i x
    rw [pow_succ', RingAut.mul_apply]
  have hcc : ∀ k, cc (k + 1) = σ (cc k) * c := by
    intro k
    simp only [cc]
    rw [Finset.prod_range_succ', map_prod]
    simp [hpw]
  have hA : ∀ k (x : K), θ (a ^ k * x) = cc k * (σ ^ k) (θ x) := by
    intro k
    induction k with
    | zero => intro x; simp [cc]
    | succ k ih =>
      intro x
      rw [pow_succ', mul_assoc, h, ih, map_mul, hcc, hpw]
      ring
  set ν : K := cc m with hν
  have hAm : ∀ x, θ (a ^ m * x) = ν * θ x := by
    intro x
    rw [hA, hσm]
    rfl
  have hν0 : ν ≠ 0 := by
    simp only [hν, cc]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => by
      intro h0
      exact hc0 ((map_eq_zero_iff _ (σ ^ i).injective).mp h0)
  have hσν : σ ν = ν := by
    obtain ⟨x', hx'⟩ := hθ.2 1
    have e1 : θ (a ^ m * (a * x')) = ν * c := by
      rw [hAm, h, hx', map_one, mul_one]
    have e2 : θ (a ^ m * (a * x')) = c * σ ν := by
      rw [show a ^ m * (a * x') = a * (a ^ m * x') by ring, h, hAm, map_mul, hx', map_one, mul_one]
    have : c * σ ν = c * ν := by rw [← e2, e1, mul_comm]
    exact mul_left_cancel₀ hc0 this
  have hνE : ν ∈ FixedPoints.subfield (Subgroup.zpowers σ) K := by
    have hstab : σ ∈ MulAction.stabilizer (RingAut K) ν := by
      rw [MulAction.mem_stabilizer_iff]
      exact hσν
    have hle : Subgroup.zpowers σ ≤ MulAction.stabilizer (RingAut K) ν :=
      Subgroup.zpowers_le.mpr hstab
    intro g
    exact MulAction.mem_stabilizer_iff.mp (hle g.2)
  haveI : Fintype (FixedPoints.subfield (Subgroup.zpowers σ) K) := Fintype.ofFinite _
  haveI : Fintype (Subgroup.zpowers σ) := Fintype.ofFinite _
  have hfr : Module.finrank (FixedPoints.subfield (Subgroup.zpowers σ) K) K = m := by
    have := FixedPoints.finrank_eq_card (Subgroup.zpowers σ) K
    have h2 : Fintype.card (Subgroup.zpowers σ) = m := by
      rw [← Nat.card_eq_fintype_card]
      exact Nat.card_zpowers σ
    rw [h2] at this
    exact this
  have hcardK :
      Fintype.card K = Fintype.card (FixedPoints.subfield (Subgroup.zpowers σ) K) ^ m := by
    rw [← hfr]
    exact Module.card_eq_pow_finrank (K := FixedPoints.subfield (Subgroup.zpowers σ) K) (V := K)
  have hq2 : 2 ≤ Fintype.card (FixedPoints.subfield (Subgroup.zpowers σ) K) := Fintype.one_lt_card
  have hAmj : ∀ j (x : K), θ (a ^ (m * j) * x) = ν ^ j * θ x := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
      intro x
      rw [show m * (j + 1) = m + m * j by ring, pow_add, mul_assoc, hAm, ih, pow_succ]
      ring
  have hνq : ν ^ (Fintype.card (FixedPoints.subfield (Subgroup.zpowers σ) K) - 1) = 1 := by
    have h1 : (⟨ν, hνE⟩ : FixedPoints.subfield (Subgroup.zpowers σ) K) ≠ 0 :=
      fun h0 => hν0 (congrArg Subtype.val h0)
    have := FiniteField.pow_card_sub_one_eq_one
      (⟨ν, hνE⟩ : FixedPoints.subfield (Subgroup.zpowers σ) K) h1
    exact congrArg Subtype.val this
  have hord : a ^ (m * (Fintype.card (FixedPoints.subfield (Subgroup.zpowers σ) K) - 1)) = 1 := by
    have h1 := hAmj (Fintype.card (FixedPoints.subfield (Subgroup.zpowers σ) K) - 1) 1
    rw [hνq, one_mul, mul_one] at h1
    have := hθ.1 (h1.trans (by simp : θ 1 = θ 1))
    simpa using hθ.1 h1
  have hdvd : Nat.card K - 1 ∣
      m * (Fintype.card (FixedPoints.subfield (Subgroup.zpowers σ) K) - 1) := by
    rw [← ha]
    exact orderOf_dvd_of_pow_eq_one hord
  have hpos : 0 < m * (Fintype.card (FixedPoints.subfield (Subgroup.zpowers σ) K) - 1) :=
    Nat.mul_pos hm0 (by omega)
  have hle := Nat.le_of_dvd hpos hdvd
  have hgt := pow_gt_aux hq2 hm2
  rw [Nat.card_eq_fintype_card, hcardK] at hle
  omega


theorem semilinear_of_conj {a : K} (hK3 : 3 ≤ Nat.card K) (ha : orderOf a = Nat.card K - 1)
    (θ : K →+ K) (hθ : Function.Bijective θ) (c : K) (σ : RingAut K)
    (h : ∀ x, θ (a * x) = c * σ (θ x)) : ∃ σ' : K ≃+* K, ∀ x, θ x = θ 1 * σ' x := by
  have hσ : σ = 1 := eq_one_of_conj hK3 ha θ hθ c σ h
  subst hσ
  have h' : ∀ x, θ (a * x) = c * θ x := by intro x; simpa using h x
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [orderOf_zero] at ha
    omega
  have hpow : ∀ (k : ℕ) (x : K), θ (a ^ k * x) = c ^ k * θ x := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ, mul_comm (a ^ k) a, mul_assoc, h', ih, pow_succ]
      ring
  have hθ1 : θ 1 ≠ 0 := fun h0 => one_ne_zero (hθ.1 (by rw [h0, map_zero]))
  let f : K →+ K := (AddMonoidHom.mulRight (θ 1)⁻¹).comp θ
  have hmul : ∀ x y, θ (x * y) = f x * θ y := by
    intro x y
    by_cases hx : x = 0
    · simp [hx, f]
    · obtain ⟨k, rfl⟩ := exists_pow_eq_of_orderOf ha ha0 hx
      have e1 := hpow k y
      have e2 := hpow k 1
      rw [mul_one] at e2
      show θ (a ^ k * y) = (θ (a ^ k) * (θ 1)⁻¹) * θ y
      rw [e1, e2]
      field_simp
  exact Tim79.exists_ringEquiv_of_mul_eq θ f θ hθ hmul


theorem semilinear_of_card_four [CharP K 2] [PerfectRing K 2] (hK : Nat.card K = 4) (θ : K →+ K)
    (hθ : Function.Bijective θ) : ∃ σ' : K ≃+* K, ∀ x, θ x = θ 1 * σ' x := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : ExpChar K 2 := ExpChar.prime Nat.prime_two
  have hK' : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have hθ1 : θ 1 ≠ 0 := fun h0 => one_ne_zero (hθ.1 (by rw [h0, map_zero]))
  have hadd : ∀ x : K, x + x = 0 := fun x => CharTwo.add_self_eq_zero x
  obtain ⟨ω, hω0, hω1⟩ : ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := by
      intro x _
      by_cases hx : x = 0
      · simp [hx]
      · simp [hcon x hx]
    have := (Finset.card_le_card hsub).trans (Finset.card_le_two)
    rw [Finset.card_univ] at this
    omega
  have hne01 : (0 : K) ≠ 1 := zero_ne_one
  have hne1ω : (1 : K) ≠ ω := fun h => hω1 h.symm
  have hne0ω1 : (0 : K) ≠ ω + 1 := by
    intro h
    apply hω1
    have h1 : ω + 1 = 0 := h.symm
    have h2 : ω = -1 := eq_neg_of_add_eq_zero_left h1
    rw [h2, CharTwo.neg_eq]
  have hne1ω1 : (1 : K) ≠ ω + 1 := by
    intro h
    apply hω0
    have : ω + 1 = 0 + 1 := by rw [← h, zero_add]
    exact (add_right_cancel this)
  have hneωω1 : ω ≠ ω + 1 := by
    intro h
    have : ω + 0 = ω + 1 := by rw [add_zero]; exact h
    exact one_ne_zero (add_left_cancel this).symm
  have hcover : ∀ x : K, x = 0 ∨ x = 1 ∨ x = ω ∨ x = ω + 1 := by
    have hsub : ({0, 1, ω, ω + 1} : Finset K) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [hK', Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp only [Finset.mem_singleton]; exact hneωω1
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hne1ω, hne1ω1⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hne01, hω0.symm, hne0ω1⟩
    intro x
    have : x ∈ ({0, 1, ω, ω + 1} : Finset K) := by rw [hsub]; exact Finset.mem_univ x
    simpa using this
  set c := θ 1 with hc
  let ρ : K →+ K := (AddMonoidHom.mulRight c⁻¹).comp θ
  have hρ1 : ρ 1 = 1 := mul_inv_cancel₀ hθ1
  have hρinj : Function.Injective ρ := by
    intro x y hxy
    apply hθ.1
    have := mul_right_cancel₀ (inv_ne_zero hθ1) hxy
    exact this
  have hρω0 : ρ ω ≠ 0 := by
    intro h0
    have : ρ ω = ρ 0 := by rw [h0, map_zero]
    exact hω0 (hρinj this)
  have hρω1 : ρ ω ≠ 1 := by
    intro h1
    have : ρ ω = ρ 1 := by rw [h1, hρ1]
    exact hω1 (hρinj this)
  have hθρ : ∀ x, θ x = c * ρ x := by
    intro x
    simp only [ρ, AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulRight]
    field_simp
  have hρω : ρ ω = ω ∨ ρ ω = ω + 1 := by
    rcases hcover (ρ ω) with h | h | h | h
    · exact absurd h hρω0
    · exact absurd h hρω1
    · exact Or.inl h
    · exact Or.inr h
  rcases hρω with h | h
  ·
    refine ⟨RingEquiv.refl K, fun x => ?_⟩
    rw [hθρ]
    congr 1
    rcases hcover x with rfl | rfl | rfl | rfl
    · simp
    · exact hρ1
    · exact h
    · rw [map_add, h, hρ1]; rfl
  ·
    have hω4 : ω ^ 4 = ω := by
      have := FiniteField.pow_card ω
      rwa [hK'] at this
    have hω3 : ω ^ 3 = 1 := by
      have h1 : ω * (ω ^ 3 - 1) = 0 := by ring_nf; rw [hω4]; ring
      rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 hω0
      · exact sub_eq_zero.mp h2
    have hωsq : ω ^ 2 = ω + 1 := by
      have h1 : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by ring_nf; rw [hω3]; ring
      rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd (sub_eq_zero.mp h2) hω1
      · have h3 : ω ^ 2 = -(ω + 1) := by linear_combination h2
        rw [h3, CharTwo.neg_eq]
    refine ⟨frobeniusEquiv K 2, fun x => ?_⟩
    rw [hθρ, frobeniusEquiv_def]
    congr 1
    rcases hcover x with rfl | rfl | rfl | rfl
    · simp
    · rw [hρ1]; simp
    · rw [h, hωsq]
    · have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      rw [map_add, h, hρ1]
      linear_combination (-1 : K) * hωsq - ω * h2

end Eigen2

end CFSG.RankThree.GF2n.Stroth80.FieldModel
