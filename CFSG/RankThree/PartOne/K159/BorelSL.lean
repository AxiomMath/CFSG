module

public import CFSG.RankThree.PartOne.K159.BorelConj
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public section

namespace CFSG.RankThree.PartOne.K159

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Torus

@[expose] def prodUnits (m : ℕ) (K : Type) [Field K] : (Fin m → Kˣ) →* Kˣ where
  toFun d := ∏ i, d i
  map_one' := by simp
  map_mul' a b := by simp [Finset.prod_mul_distrib]

theorem prodUnits_surjective {m : ℕ} (hm : 1 ≤ m) (K : Type) [Field K] :
    Function.Surjective (prodUnits m K) := by
  classical
  intro u
  refine ⟨Pi.mulSingle ⟨0, hm⟩ u, ?_⟩
  show ∏ i, (Pi.mulSingle (⟨0, hm⟩ : Fin m) u : Fin m → Kˣ) i = u
  rw [Finset.prod_eq_single (⟨0, hm⟩ : Fin m)]
  · simp
  · intro j _ hj
    simp [Pi.mulSingle_eq_of_ne hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

@[expose] noncomputable def diagElem {m : ℕ} {K : Type} [Field K] (d : Fin m → Kˣ) (hd : ∏ i, d i = 1) :
    SpecialLinearGroup (Fin m) K :=
  ⟨Matrix.diagonal (fun i => ((d i : Kˣ) : K)), by
    rw [Matrix.det_diagonal]
    have := congrArg (fun u : Kˣ => (u : K)) hd
    simpa [Units.coe_prod] using this⟩

theorem diagElem_coe {m : ℕ} {K : Type} [Field K] (d : Fin m → Kˣ) (hd : ∏ i, d i = 1) :
    ((diagElem d hd : SpecialLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K) =
      Matrix.diagonal (fun i => ((d i : Kˣ) : K)) := rfl

theorem diagElem_mul {m : ℕ} {K : Type} [Field K] (d e : Fin m → Kˣ) (hd : ∏ i, d i = 1)
    (he : ∏ i, e i = 1) (hde : ∏ i, (d * e) i = 1) :
    diagElem d hd * diagElem e he = diagElem (d * e) hde := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul, diagElem_coe, diagElem_coe, diagElem_coe,
    Matrix.diagonal_mul_diagonal]
  simp

@[expose] noncomputable def diagSL (m : ℕ) (K : Type) [Field K] :
    (prodUnits m K).ker →* SpecialLinearGroup (Fin m) K where
  toFun d := diagElem d.1 d.2
  map_one' := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp [diagElem_coe]
  map_mul' a b := (diagElem_mul a.1 b.1 a.2 b.2 (a * b).2).symm

theorem diagSL_coe {m : ℕ} {K : Type} [Field K] (d : (prodUnits m K).ker) :
    ((diagSL m K d : SpecialLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K) =
      Matrix.diagonal (fun i => ((d.1 i : Kˣ) : K)) := rfl

theorem diagSL_injective (m : ℕ) (K : Type) [Field K] : Function.Injective (diagSL m K) := by
  intro a b h
  have h1 := congrArg (fun g : SpecialLinearGroup (Fin m) K =>
    (g : Matrix (Fin m) (Fin m) K)) h
  apply Subtype.ext
  funext i
  apply Units.ext
  have := congrFun (congrFun h1 i) i
  simpa [diagSL_coe] using this

variable {K : Type} [Field K] [Finite K]

theorem card_diagSL {m : ℕ} (hm : 1 ≤ m) :
    Nat.card (diagSL m K).range = (Nat.card K - 1) ^ (m - 1) := by
  have h1 : Nat.card (diagSL m K).range = Nat.card (prodUnits m K).ker :=
    (Nat.card_congr (MonoidHom.ofInjective (diagSL_injective m K)).toEquiv).symm
  have h2 := Subgroup.card_ker_mul_card_of_surjective (prodUnits_surjective hm K)
  have h3 : Nat.card (Fin m → Kˣ) = (Nat.card K - 1) ^ m := by
    rw [Nat.card_pi]
    simp [Nat.card_units]
  have hq : 0 < Nat.card K - 1 := by
    have := Finite.one_lt_card (α := K)
    omega
  rw [h1]
  rw [h3, Nat.card_units] at h2
  apply Nat.eq_of_mul_eq_mul_right hq
  rw [h2, ← pow_succ]
  congr 1
  omega

end Torus

section Normalizer

variable {K : Type} [Field K] [Finite K] {m : ℕ}

omit [Finite K] in
theorem diagSL_conj_mem_unitriangular (d : (prodUnits m K).ker) {u : SpecialLinearGroup (Fin m) K}
    (hu : u ∈ unitriangular m K) : diagSL m K d * u * (diagSL m K d)⁻¹ ∈ unitriangular m K := by
  rw [mem_unitriangular] at hu ⊢
  obtain ⟨hlow, hdiag⟩ := hu
  have hinv : (diagSL m K d)⁻¹ = diagSL m K d⁻¹ := (map_inv _ d).symm
  have hu' : ((diagSL m K d * u * (diagSL m K d)⁻¹ : SpecialLinearGroup (Fin m) K) :
      Matrix (Fin m) (Fin m) K) =
      Matrix.diagonal (fun i => ((d.1 i : Kˣ) : K)) * (u : Matrix (Fin m) (Fin m) K) *
        Matrix.diagonal (fun i => (((d⁻¹).1 i : Kˣ) : K)) := by
    rw [hinv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, diagSL_coe,
      diagSL_coe]
  have hentry : ∀ i j, ((diagSL m K d * u * (diagSL m K d)⁻¹ : SpecialLinearGroup (Fin m) K) :
      Matrix (Fin m) (Fin m) K) i j =
      ((d.1 i : Kˣ) : K) * (u : Matrix (Fin m) (Fin m) K) i j * ((d.1 j : Kˣ) : K)⁻¹ := by
    intro i j
    rw [hu']
    generalize (u : Matrix (Fin m) (Fin m) K) = U
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [hentry, hlow i j hij]
    simp
  · rw [hentry, hdiag i, mul_one]
    exact mul_inv_cancel₀ (Units.ne_zero _)

omit [Finite K] in
theorem diagSL_range_le_normalizer :
    (diagSL m K).range ≤
      Subgroup.normalizer (unitriangular m K : Set (SpecialLinearGroup (Fin m) K)) :=
  le_normalizer_of_forall_conj_mem fun g hg u hu => by
    obtain ⟨d, rfl⟩ := hg
    exact diagSL_conj_mem_unitriangular d hu

end Normalizer

section Arith

theorem card_SL_eq_mul {K : Type} [Field K] [Finite K] {m : ℕ} (hm : 1 ≤ m) :
    Nat.card (SpecialLinearGroup (Fin m) K) =
      Nat.card K ^ (m * (m - 1) / 2) * (Nat.card K - 1) ^ (m - 1) *
        ∏ j ∈ Finset.Icc 2 m, ∑ i ∈ Finset.range j, Nat.card K ^ i := by
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  rw [card_SL_eq hm, mul_assoc]
  congr 1
  have h : ∀ j ∈ Finset.Icc 2 m, Nat.card K ^ j - 1 =
      (∑ i ∈ Finset.range j, Nat.card K ^ i) * (Nat.card K - 1) := fun j _ =>
    (geom_sum_mul_of_one_le hq j).symm
  rw [Finset.prod_congr rfl h, Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc, mul_comm]
  congr 2

theorem not_dvd_prod_geom {p q m : ℕ} (hp : p.Prime) (hq : 1 ≤ q) (hpq : p ∣ q - 1) (hmp : m < p) :
    ¬ p ∣ ∏ j ∈ Finset.Icc 2 m, ∑ i ∈ Finset.range j, q ^ i := by
  have : Fact p.Prime := ⟨hp⟩
  have hq1 : (q : ZMod p) = 1 := by
    have h1 : ((q - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hpq
    rw [Nat.cast_sub hq] at h1
    simpa [sub_eq_zero] using h1
  intro hdvd
  have h0 : ((∏ j ∈ Finset.Icc 2 m, ∑ i ∈ Finset.range j, q ^ i : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 hdvd
  push_cast at h0
  rw [Finset.prod_eq_zero_iff] at h0
  obtain ⟨j, hj, hj0⟩ := h0
  rw [Finset.mem_Icc] at hj
  simp only [hq1, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hj0
  have h2 := (ZMod.natCast_eq_zero_iff _ _).1 hj0
  have h3 := Nat.le_of_dvd (by omega) h2
  omega

end Arith

section Centralizer

variable {K : Type} [Field K] {m : ℕ}

@[expose] def transvSL {i j : Fin m} (hij : i < j) (c : K) : SpecialLinearGroup (Fin m) K :=
  ⟨Matrix.transvection i j c, Matrix.det_transvection_of_ne i j hij.ne c⟩

theorem transvSL_coe {i j : Fin m} (hij : i < j) (c : K) :
    ((transvSL hij c : SpecialLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K) =
      Matrix.transvection i j c := rfl

theorem transvSL_mem_unitriangular {i j : Fin m} (hij : i < j) (c : K) :
    transvSL hij c ∈ unitriangular m K := by
  rw [mem_unitriangular]
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · rw [transvSL_coe]
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    have h1 : a ≠ b := hab.ne'
    have h2 : ¬ (i = a ∧ j = b) := fun h => by
      obtain ⟨rfl, rfl⟩ := h
      exact absurd hij (not_lt.2 hab.le)
    simp [h1, h2]
  · rw [transvSL_coe]
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    have h2 : ¬ (i = a ∧ j = a) := fun h => hij.ne (h.1.trans h.2.symm)
    simp [h2]

theorem exists_noncomm_unitriangular [CharP K 2] {p : ℕ} (hp : p.Prime) (hm : 2 ≤ m) (hmp : m < p)
    (hT2 : IsPGroup 2 ↥(unitriangular m K)) (x : SpecialLinearGroup (Fin m) K) (hx : orderOf x = p) :
    ∃ t ∈ unitriangular m K, x * t ≠ t * x := by
  classical
  by_contra hcon
  push Not at hcon
  have hp2 : p ≠ 2 := by omega
  set X : Matrix (Fin m) (Fin m) K := (x : Matrix (Fin m) (Fin m) K) with hXdef
  let first : Fin m := ⟨0, by omega⟩
  let last : Fin m := ⟨m - 1, by omega⟩
  have hfl : first < last := by
    simp only [Fin.lt_def, first, last]
    omega
  have hE : ∀ i j : Fin m, i < j →
      X * Matrix.single i j (1 : K) = Matrix.single i j (1 : K) * X := by
    intro i j hij
    have h1 := congrArg (fun g : SpecialLinearGroup (Fin m) K => (g : Matrix (Fin m) (Fin m) K))
      (hcon _ (transvSL_mem_unitriangular hij 1))
    simp only [Matrix.SpecialLinearGroup.coe_mul, transvSL_coe] at h1
    simp only [Matrix.transvection, mul_add, add_mul, mul_one, one_mul] at h1
    exact add_left_cancel h1
  have hcol : ∀ i j : Fin m, i < j → ∀ k, k ≠ i → X k i = 0 := by
    intro i j hij k hki
    have h := congrFun (congrFun (hE i j hij) k) j
    rw [Matrix.mul_single_apply_same, Matrix.single_mul_apply_of_ne _ _ _ _ _ hki] at h
    simpa using h
  have hrow : ∀ i j : Fin m, i < j → ∀ l, l ≠ j → X j l = 0 := by
    intro i j hij l hlj
    have h := congrFun (congrFun (hE i j hij) i) l
    rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hlj, Matrix.single_mul_apply_same] at h
    simpa using h.symm
  have hdiag : ∀ i j : Fin m, i < j → X i i = X j j := by
    intro i j hij
    have h := congrFun (congrFun (hE i j hij) i) j
    rw [Matrix.mul_single_apply_same, Matrix.single_mul_apply_same] at h
    simpa using h
  have hshape : ∀ k l : Fin m, k ≠ l → ¬ (k = first ∧ l = last) → X k l = 0 := by
    intro k l hkl hno
    by_cases hl : l = last
    · have hk : k ≠ first := fun h => hno ⟨h, hl⟩
      have hfk : first < k := by
        simp only [Fin.lt_def, first]
        have : k.val ≠ 0 := fun h => hk (Fin.ext h)
        omega
      exact hrow first k hfk l (fun h => hkl h.symm)
    · have hlt : l < last := by
        simp only [Fin.lt_def, last]
        have : l.val ≠ m - 1 := fun h => hl (Fin.ext h)
        have := l.2
        omega
      exact hcol l last hlt k hkl
  have hlam : ∀ i : Fin m, X i i = X first first := by
    intro i
    by_cases hi : i = first
    · rw [hi]
    · have : first < i := by
        simp only [Fin.lt_def, first]
        have : i.val ≠ 0 := fun h => hi (Fin.ext h)
        omega
      exact (hdiag first i this).symm
  set lam : K := X first first with hlamdef
  have hup : X.IsUpperTriangular := fun i j hji => by
    refine hshape i j hji.ne' ?_
    rintro ⟨rfl, rfl⟩
    exact absurd hji (not_lt.2 hfl.le)
  have hdet : lam ^ m = 1 := by
    have h1 : X.det = 1 := x.2
    rw [Matrix.det_of_isUpperTriangular hup] at h1
    simpa [hlam, Finset.prod_const, Finset.card_univ] using h1
  have hlam0 : lam ≠ 0 := by
    intro h
    rw [h, zero_pow (by omega)] at hdet
    exact zero_ne_one hdet
  set μ : K := X first last / lam with hμ
  have hXu : X = lam • ((transvSL hfl μ : SpecialLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K) := by
    ext k l
    rw [transvSL_coe, Matrix.smul_apply]
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
      smul_eq_mul]
    by_cases hkl : k = l
    · subst hkl
      have h2 : ¬ (first = k ∧ last = k) := fun h => hfl.ne (h.1.trans h.2.symm)
      simp [h2, hlam k]
    · by_cases h3 : k = first ∧ l = last
      · obtain ⟨rfl, rfl⟩ := h3
        have h4 : (first = first ∧ last = last) := ⟨rfl, rfl⟩
        have h5 : first ≠ last := hfl.ne
        simp [h5, hμ]
        field_simp
      · have h4 : ¬ (first = k ∧ last = l) := fun h => h3 ⟨h.1.symm, h.2.symm⟩
        simp [hkl, h4, hshape k l hkl h3]
  have huT := transvSL_mem_unitriangular hfl μ
  set uSL : SpecialLinearGroup (Fin m) K := transvSL hfl μ with huSL
  have hxp : x ^ p = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have hXp : X ^ p = 1 := by
    have := congrArg (fun g : SpecialLinearGroup (Fin m) K => (g : Matrix (Fin m) (Fin m) K)) hxp
    simpa [Matrix.SpecialLinearGroup.coe_pow] using this
  rw [hXu, smul_pow] at hXp
  have hUp : ((uSL ^ p : SpecialLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K) =
      (uSL : Matrix (Fin m) (Fin m) K) ^ p := Matrix.SpecialLinearGroup.coe_pow uSL p
  have hdiag1 : ((uSL ^ p : SpecialLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K) first first = 1 :=
    (mem_unitriangular.1 (pow_mem huT p)).2 first
  have hlamp : lam ^ p = 1 := by
    have := congrFun (congrFun hXp first) first
    rw [Matrix.smul_apply, ← hUp, hdiag1, Matrix.one_apply_eq, smul_eq_mul, mul_one] at this
    exact this
  have hUp1 : uSL ^ p = 1 := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [hUp]
    rw [hlamp, one_smul] at hXp
    rw [hXp, Matrix.SpecialLinearGroup.coe_one]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hT2) ⟨uSL, huT⟩
  have hord : orderOf (⟨uSL, huT⟩ : ↥(unitriangular m K)) ∣ p :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext hUp1)
  rw [hk] at hord
  have hk0 : k = 0 := by
    by_contra hk0
    have h2 : 2 ∣ p := (dvd_pow_self 2 hk0).trans hord
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2).symm
  have hu1 : uSL = 1 := by
    have h1 : orderOf (⟨uSL, huT⟩ : ↥(unitriangular m K)) = 1 := by rw [hk, hk0, pow_zero]
    exact congrArg Subtype.val (orderOf_eq_one_iff.1 h1)
  have hX1 : X = lam • (1 : Matrix (Fin m) (Fin m) K) := by
    rw [hXu, hu1, Matrix.SpecialLinearGroup.coe_one]
  have hlam1 : lam = 1 := by
    have h1 : lam ^ Nat.gcd m p = 1 := pow_gcd_eq_one.2 ⟨hdet, hlamp⟩
    have hcop : Nat.gcd m p = 1 := by
      refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => ?_)
      have := Nat.le_of_dvd (by omega) h
      omega
    rwa [hcop, pow_one] at h1
  have hx1 : x = 1 := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [Matrix.SpecialLinearGroup.coe_one]
    show X i j = (1 : Matrix (Fin m) (Fin m) K) i j
    rw [hX1, hlam1, one_smul]
  rw [hx1, orderOf_one] at hx
  exact hp.ne_one hx.symm

end Centralizer

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem odd_card_sub_one : Odd (Nat.card K - 1) := by
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  rw [← Nat.card_eq_fintype_card] at hn
  rw [hn]
  have h1 : 1 ≤ 2 ^ (n : ℕ) := Nat.one_le_two_pow
  obtain ⟨k, hk⟩ : Even (2 ^ (n : ℕ)) := Nat.even_pow.2 ⟨even_two, n.pos.ne'⟩
  exact ⟨k - 1, by omega⟩

theorem borelFactsGrp_specialLinear {p m : ℕ} (hp : p.Prime) (hpq : p ∣ Nat.card K - 1)
    (hm : 2 ≤ m) (hmp : m < p) : BorelFactsGrp p (SpecialLinearGroup (Fin m) K) := by
  classical
  have hm1 : 1 ≤ m := by omega
  obtain ⟨T, hT⟩ := exists_sylow_unitriangular (K := K) 2 hm1
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have hpSL : p ∣ Nat.card (SpecialLinearGroup (Fin m) K) := by
    rw [card_SL_eq hm1]
    refine Dvd.dvd.mul_left ?_ _
    refine Dvd.dvd.trans ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_Icc.2 ⟨le_rfl, hm⟩))
    simpa using hpq.trans (Nat.sub_dvd_pow_sub_pow (Nat.card K) 1 2)
  have hTcard : Nat.card ↥(T : Subgroup (SpecialLinearGroup (Fin m) K)) =
      Nat.card K ^ (m * (m - 1) / 2) := by
    rw [hT]
    exact card_unitriangular m
  refine BorelFactsGrp.of_torus hpSL T (D := (diagSL m K).range) ?_ ?_ ?_
    (not_dvd_prod_geom hp hq hpq hmp) ?_
  · rw [hT]
    exact diagSL_range_le_normalizer
  · rw [card_diagSL hm1]
    exact odd_card_sub_one.pow
  · rw [card_SL_eq_mul hm1, card_diagSL hm1, hTcard]
  · intro x hx
    have hT2 : IsPGroup 2 ↥(unitriangular m K) := by
      rw [← hT]
      exact T.isPGroup'
    obtain ⟨t, ht, hne⟩ := exists_noncomm_unitriangular hp hm hmp hT2 x hx
    exact ⟨t, hT ▸ ht, hne⟩

end Main

end CFSG.RankThree.PartOne.K159
