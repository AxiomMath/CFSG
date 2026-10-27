module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdCodimTwoOuter

public section

namespace CFSG.StandardType

namespace TableBU63

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.SectionRank.OddCover
  CFSG.RankThree.PartOne.KCUnitaryModel TableBUD TableBUE TableBUR TableBUDT

section Comb

theorem exists_perm_ne_zero {m : Type*} [Fintype m] [DecidableEq m] {R : Type*} [CommRing R]
    {M : Matrix m m R} (h : M.det ≠ 0) : ∃ σ : Equiv.Perm m, ∀ i, M (σ i) i ≠ 0 := by
  rw [Matrix.det_apply] at h
  obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨σ, fun i hi => hσ ?_⟩
  have h0 : ∏ j, M (σ j) j = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
  rw [h0, smul_zero]

theorem eq_of_pow_eq {K : Type*} [Field K] {ζ : K} (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1) {a b : ℕ}
    (ha : a < 3) (hb : b < 3) (hab : ζ ^ a = ζ ^ b) : a = b := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    norm_num at hζ3
  have hζ2 : ζ ^ 2 ≠ 1 := fun h2 => hζ1 (by rw [pow_succ, h2, one_mul] at hζ3; exact hζ3)
  have hζ21 : ζ ^ 2 ≠ ζ := fun h2 => hζ1 (by
    have h3 : ζ * (ζ - 1) = 0 := by rw [mul_sub, mul_one, ← sq, h2, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left hζ0))
  interval_cases a <;> interval_cases b <;>
    simp only [pow_zero, pow_one] at hab ⊢ <;> first
    | rfl
    | exact absurd hab.symm hζ1
    | exact absurd hab hζ1
    | exact absurd hab.symm hζ2
    | exact absurd hab hζ2
    | exact absurd hab.symm hζ21
    | exact absurd hab hζ21

theorem eq_of_heis {K : Type*} [Field K] {η ε : Fin 6 → K} {ζ : K}
    {g : Matrix (Fin 6) (Fin 6) K} (hdet : g.det ≠ 0)
    (hrel : ∀ i j, g i j ≠ 0 → η i = ζ * η j ∧ ε i = ε j) (hη : ∀ i, η i ≠ 0) (hζ3 : ζ ^ 3 = 1)
    (hζ1 : ζ ≠ 1) {s t : Fin 6} (hst : s ≠ t) (hηst : η s = η t) (hεst : ε s = ε t) :
    ∀ i, ε i = ε s := by
  obtain ⟨σ, hσ⟩ := exists_perm_ne_zero hdet
  have hση : ∀ (m : ℕ) i, η ((σ ^ m) i) = ζ ^ m * η i := by
    intro m
    induction m with
    | zero => intro i; simp
    | succ m ih =>
      intro i
      rw [pow_succ', Equiv.Perm.mul_apply, (hrel _ _ (hσ _)).1, ih, pow_succ']
      ring
  have hσε : ∀ (m : ℕ) i, ε ((σ ^ m) i) = ε i := by
    intro m
    induction m with
    | zero => intro i; simp
    | succ m ih =>
      intro i
      rw [pow_succ', Equiv.Perm.mul_apply, (hrel _ _ (hσ _)).2, ih]
  set f : Fin 6 → Fin 6 := fun k => (σ ^ ((k : ℕ) / 2)) (if (k : ℕ) % 2 = 0 then s else t)
    with hf
  have hfη : ∀ k : Fin 6, η (f k) = ζ ^ ((k : ℕ) / 2) * η s := by
    intro k
    rw [hf]
    dsimp only
    rw [hση]
    split_ifs
    · rfl
    · rw [hηst]
  have hfinj : Function.Injective f := by
    intro k l hkl
    have h1 : ζ ^ ((k : ℕ) / 2) = ζ ^ ((l : ℕ) / 2) := by
      have e := congrArg η hkl
      rw [hfη, hfη] at e
      exact mul_right_cancel₀ (hη s) e
    have h2 := eq_of_pow_eq hζ3 hζ1 (by omega) (by omega) h1
    have h3 : (if (k : ℕ) % 2 = 0 then s else t) = (if (l : ℕ) % 2 = 0 then s else t) := by
      have e : (σ ^ ((k : ℕ) / 2)) (if (k : ℕ) % 2 = 0 then s else t) =
          (σ ^ ((k : ℕ) / 2)) (if (l : ℕ) % 2 = 0 then s else t) := by
        have e' := hkl
        simp only [hf, h2] at e' ⊢
        exact e'
      exact (σ ^ ((k : ℕ) / 2)).injective e
    have h4 : (k : ℕ) % 2 = (l : ℕ) % 2 := by
      by_cases hk : (k : ℕ) % 2 = 0 <;> by_cases hl : (l : ℕ) % 2 = 0
      · omega
      · rw [ite_eq_left hk, ite_eq_right hl] at h3
        exact absurd h3 hst
      · rw [ite_eq_right hk, ite_eq_left hl] at h3
        exact absurd h3.symm hst
      · omega
    apply Fin.ext
    omega
  have hfsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hfinj
  intro i
  obtain ⟨k, rfl⟩ := hfsurj i
  rw [hf]
  dsimp only
  rw [hσε]
  split_ifs
  · rfl
  · exact hεst.symm

end Comb

section Frob

variable {K : Type} [Field K] {d : ℕ}

theorem frob_eq_of_conj [NeZero d] (φ : K →+* K) {B h g : GL (Fin d) K} {c₁ c₂ ζ : K}
    (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0)
    (h1 : (B : Matrix (Fin d) (Fin d) K) * (h : Matrix (Fin d) (Fin d) K).map φ =
      c₁ • ((h : Matrix (Fin d) (Fin d) K) * (B : Matrix (Fin d) (Fin d) K)))
    (h2 : (B : Matrix (Fin d) (Fin d) K) * (g : Matrix (Fin d) (Fin d) K).map φ =
      c₂ • ((g : Matrix (Fin d) (Fin d) K) * (B : Matrix (Fin d) (Fin d) K)))
    (h3 : (h : Matrix (Fin d) (Fin d) K) * (g : Matrix (Fin d) (Fin d) K) =
      ζ • ((g : Matrix (Fin d) (Fin d) K) * (h : Matrix (Fin d) (Fin d) K))) :
    φ ζ = ζ := by
  set H := (h : Matrix (Fin d) (Fin d) K)
  set G := (g : Matrix (Fin d) (Fin d) K)
  set Bm := (B : Matrix (Fin d) (Fin d) K)
  have hmap : (H * G).map φ = φ ζ • (G.map φ * H.map φ) := by
    rw [h3]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, map_mul,
      map_sum]
  have e1 : Bm * (H * G).map φ = (c₁ * c₂) • (H * G * Bm) := by
    rw [Matrix.map_mul, ← Matrix.mul_assoc, h1, Matrix.smul_mul, Matrix.mul_assoc, h2,
      Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  have e2 : Bm * (H * G).map φ = (φ ζ * c₂ * c₁) • (G * H * Bm) := by
    rw [hmap, Matrix.mul_smul, ← Matrix.mul_assoc, h2, Matrix.smul_mul, Matrix.mul_assoc, h1,
      Matrix.mul_smul, smul_smul, smul_smul, Matrix.mul_assoc]
  have e3 : ((c₁ * c₂ * ζ) • (G * H * Bm)) = (φ ζ * c₂ * c₁) • (G * H * Bm) := by
    rw [← e2, e1, h3, Matrix.smul_mul, smul_smul]
  have hinv : IsUnit (G * H * Bm) := ((Units.isUnit g).mul (Units.isUnit h)).mul (Units.isUnit B)
  obtain ⟨Y, hY⟩ := hinv.exists_right_inv
  have e4 := congrArg (fun M => M * Y) e3
  simp only [Matrix.smul_mul, hY] at e4
  have e5 := congrFun (congrFun e4 0) 0
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at e5
  have hc : c₁ * c₂ ≠ 0 := mul_ne_zero hc₁ hc₂
  have e6 : (c₁ * c₂) * ζ = (c₁ * c₂) * φ ζ := by rw [e5]; ring
  exact (mul_left_cancel₀ hc e6).symm

theorem pow_ne_self_of_cube {ζ : K} (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1) {q : ℕ} (hq : 3 ∣ q + 1) :
    ζ ^ q ≠ ζ := by
  intro hζq
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    norm_num at hζ3
  obtain ⟨k, hk⟩ := hq
  have h1 : ζ ^ (q + 1) = 1 := by rw [hk, pow_mul, hζ3, one_pow]
  rw [pow_succ, hζq, ← sq] at h1
  apply hζ1
  rw [pow_succ, h1, one_mul] at hζ3
  exact hζ3

end Frob

section Outer

variable {K : Type} [Field K] [Finite K] {n d : ℕ} (h : UnitaryFieldData 2 n K)

include h in
theorem exists_bar_conj_of_outer (hK : Nat.card K = (2 ^ n) ^ 2) (hd : 3 ≤ d)
    (hq : ¬(d = 3 ∧ 2 ^ n = 2))
    {U : Subgroup (MulAut (LargeEvenProj (unitarySU 2 n K d)))} (hU1 : U ≠ ⊥)
    (hU2 : IsPGroup 2 U)
    (hUI : U ⊓ (MulAut.conj : LargeEvenProj (unitarySU 2 n K d) →* MulAut _).range = ⊥)
    {S : Set (GL (Fin d) K)}
    (hSU : ∀ D ∈ S, D ∈ primeFormUnitary h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K))
    (hSN : ∀ D ∈ S, D ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    (hSA : ∀ D (hD : D ∈ S), TableB.projConj (unitarySU 2 n K d) ⟨D, hSN D hD⟩ ∈
      Subgroup.normalizer (U : Set (MulAut (LargeEvenProj (unitarySU 2 n K d))))) :
    ∃ B : GL (Fin d) K, ∀ D ∈ S, ∃ c : Kˣ,
      (B : Matrix (Fin d) (Fin d) K) * (D : Matrix (Fin d) (Fin d) K).map h.bar =
        (c : K) • ((D : Matrix (Fin d) (Fin d) K) * (B : Matrix (Fin d) (Fin d) K)) := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hC := isPrimeFormGram_one (K := K) (n := d)
  set e := projE h hd1 with he
  set E := MulAut.congr e with hE
  obtain ⟨-, -, hPsi1, -, hreal, hFF, -, -, hD, -, hcardD⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hd hq
  have hEa : ∀ D (hDS : D ∈ S), E (TableB.projConj (unitarySU 2 n K d) ⟨D, hSN D hDS⟩) =
      primeFormConjHom h _ ⟨D, hSU D hDS⟩ := fun D hDS => by
    rw [hE]
    exact congr_projConj_eq h hd1 (hSN D hDS) (hSU D hDS)
  have htriv : ∀ c ∈ U, E c ∈ primeFormD h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) →
      c = 1 := by
    intro c hcU hcD
    obtain ⟨k, hk⟩ := hU2 ⟨c, hcU⟩
    have hk' : c ^ 2 ^ k = 1 := congrArg Subtype.val hk
    set Dd := primeFormD h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) with hDd
    set N := (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (primeFormP h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K))).subgroupOf Dd with hN
    set y : Dd := ⟨E c, hcD⟩ with hy
    have hy2 : y ^ 2 ^ k = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, hy]
      change (E c) ^ 2 ^ k = 1
      rw [← map_pow, hk', map_one]
    have hord : orderOf (y : Dd ⧸ N) = 1 := by
      have h1 : orderOf (y : Dd ⧸ N) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by
        rw [← QuotientGroup.mk_pow, hy2, QuotientGroup.mk_one])
      have h2 : orderOf (y : Dd ⧸ N) ∣ 2 ^ n + 1 := (orderOf_dvd_natCard _).trans hcardD
      have hodd : Nat.Coprime (2 ^ k) (2 ^ n + 1) := by
        apply Nat.Coprime.pow_left
        rw [Nat.coprime_two_left]
        exact Even.add_one (Nat.even_pow.mpr ⟨even_two, by have := h.one_le; omega⟩)
      exact Nat.eq_one_of_dvd_coprimes hodd h1 h2
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hord
    obtain ⟨y', hy'⟩ := hord
    have hc : c = MulAut.conj (e.symm y') := by
      apply E.injective
      rw [hE, congr_conj, MulEquiv.apply_symm_apply]
      exact hy'.symm
    have hmem : c ∈ U ⊓ (MulAut.conj : LargeEvenProj (unitarySU 2 n K d) →* MulAut _).range :=
      ⟨hcU, ⟨e.symm y', hc.symm⟩⟩
    rw [hUI, Subgroup.mem_bot] at hmem
    exact hmem
  have hcomm : ∀ D (hDS : D ∈ S), ∀ u ∈ U,
      TableB.projConj (unitarySU 2 n K d) ⟨D, hSN D hDS⟩ * u =
        u * TableB.projConj (unitarySU 2 n K d) ⟨D, hSN D hDS⟩ := by
    intro D hDS u hu
    set a := TableB.projConj (unitarySU 2 n K d) ⟨D, hSN D hDS⟩ with ha
    have hcU : a * u * a⁻¹ * u⁻¹ ∈ U :=
      U.mul_mem ((Subgroup.mem_normalizer_iff.mp (hSA D hDS) u).mp hu) (U.inv_mem hu)
    have h1 : E a ∈ primeFormD h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
      ⟨_, (hEa D hDS).symm⟩
    have hcD : E (a * u * a⁻¹ * u⁻¹) ∈
        primeFormD h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv,
        show E a * E u * (E a)⁻¹ * (E u)⁻¹ = E a * (E u * (E a)⁻¹ * (E u)⁻¹) by group]
      exact Subgroup.mul_mem _ h1 (hD.conj_mem _ (Subgroup.inv_mem _ h1) (E u))
    have h2 := htriv _ hcU hcD
    calc a * u = a * u * a⁻¹ * u⁻¹ * (u * a) := by group
      _ = u * a := by rw [h2, one_mul]
  have h2U : 2 ∣ Nat.card U := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hU2
    rw [hk]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exfalso
      rw [pow_zero, Subgroup.card_eq_one] at hk
      exact hU1 hk
    · exact dvd_pow_self 2 hk0.ne'
  have := Fact.mk Nat.prime_two
  obtain ⟨⟨u, huU⟩, hu2⟩ := exists_prime_orderOf_dvd_card' 2 h2U
  rw [Subgroup.orderOf_mk] at hu2
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu2
    norm_num at hu2
  obtain ⟨φ, ⟨B, hB⟩, -⟩ := hreal (E u)
  have hφ1 : φ ≠ 1 := by
    rintro rfl
    have hmem : E u ∈ primeFormD h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
      ⟨B, by rw [hB, map_one, mul_one]⟩
    exact hu1 (htriv u huU hmem)
  have hφ2 : φ ^ 2 = 1 := by
    have h1 : primeFormFieldFactor h hC hd hq (E u) = φ := by
      rw [hB]
      exact hFF B φ
    have hu2' : u ^ 2 = 1 := by
      have h3 := pow_orderOf_eq_one u
      rwa [hu2] at h3
    rw [← h1, ← map_pow, ← map_pow, hu2', map_one, map_one]
  have hφbar : ∀ x : K, φ x = h.bar x := by
    have hn1 := h.one_le
    obtain ⟨s, hs, hφs, hφm⟩ := exists_frobenius_pow_eq (n := 2 * n) (by omega)
      (by rw [hK, ← pow_mul, mul_comm]) φ
    have h2 := (hφm 2).mp hφ2
    have h1 : ¬ 2 * n ∣ 1 * s := fun hdvd => hφ1 (by simpa using (hφm 1).mpr hdvd)
    obtain ⟨k, hk⟩ := h2
    have hsn : s = n := by
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · interval_cases k
        · exfalso
          apply h1
          have : s = 0 := by omega
          rw [this]
          exact dvd_zero _
        · omega
      · have : 2 * n * 2 ≤ 2 * n * k := Nat.mul_le_mul_left _ hk2
        omega
    intro x
    rw [hφs x, hsn, UnitaryFieldData.bar_apply]
  refine ⟨B, fun D hDS => ?_⟩
  set Dg : primeFormUnitary h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
    ⟨D, hSU D hDS⟩ with hDg
  have hEc : E u * E (TableB.projConj (unitarySU 2 n K d) ⟨D, hSN D hDS⟩) =
      E (TableB.projConj (unitarySU 2 n K d) ⟨D, hSN D hDS⟩) * E u := by
    rw [← map_mul, ← map_mul, hcomm D hDS u huU]
  rw [hEa D hDS, hB] at hEc
  have key : primeFormConjHom h _ (B * primeFormFieldU h hC φ Dg) =
      primeFormConjHom h _ (Dg * B) := by
    rw [map_mul, map_mul, ← primeFormField_conj_eq h hC φ Dg]
    calc primeFormConjHom h _ B * (primeFormFieldHom h hC φ * primeFormConjHom h _ Dg *
          (primeFormFieldHom h hC φ)⁻¹)
        = primeFormConjHom h _ B * primeFormFieldHom h hC φ * primeFormConjHom h _ Dg *
          (primeFormFieldHom h hC φ)⁻¹ := by group
      _ = primeFormConjHom h _ Dg * (primeFormConjHom h _ B * primeFormFieldHom h hC φ) *
          (primeFormFieldHom h hC φ)⁻¹ := by rw [hEc]
      _ = primeFormConjHom h _ Dg * primeFormConjHom h _ B := by group
  have hM1 : primeFormPsi h hC ⟨(Dg * B)⁻¹ * (B * primeFormFieldU h hC φ Dg),
      RingEquiv.refl K⟩ = 1 := by
    rw [primeFormPsi_apply, map_mul, map_inv, key, inv_mul_cancel, one_mul]
    exact map_one _
  obtain ⟨-, c, -, hcM⟩ := (hPsi1 _).mp hM1
  have h1 : (B : GL (Fin d) K) * glAut φ D =
      Matrix.GeneralLinearGroup.scalar (Fin d) c * (D * (B : GL (Fin d) K)) := by
    have h2 : (((Dg * B)⁻¹ * (B * primeFormFieldU h hC φ Dg) :
        primeFormUnitary h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) : GL (Fin d) K) =
          (D * (B : GL (Fin d) K))⁻¹ * ((B : GL (Fin d) K) * glAut φ D) := rfl
    rw [h2] at hcM
    rw [TypeA.PGLTor.scalar_mul_comm]
    calc (B : GL (Fin d) K) * glAut φ D =
        D * (B : GL (Fin d) K) * ((D * (B : GL (Fin d) K))⁻¹ *
          ((B : GL (Fin d) K) * glAut φ D)) := by group
      _ = _ := by rw [hcM]
  refine ⟨c, ?_⟩
  have h3 := congrArg (fun M : GL (Fin d) K => (M : Matrix (Fin d) (Fin d) K)) h1
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, coe_glAut] at h3
  have hmap : (D : Matrix (Fin d) (Fin d) K).map φ = (D : Matrix (Fin d) (Fin d) K).map h.bar := by
    ext i j
    simp [hφbar]
  rw [← hmap, h3, scalar_mul_eq_smul]

end Outer

section Inner

variable {K : Type} [Field K] [Finite K] {n d : ℕ} (h : UnitaryFieldData 2 n K)

include h in
theorem exists_pair_of_inn (hK : Nat.card K = (2 ^ n) ^ 2) (hd : 3 ≤ d)
    (hdq : (d, 2 ^ n) ≠ (3, 2))
    {U : Subgroup (MulAut (LargeEvenProj (unitarySU 2 n K d)))} (hU2 : IsPGroup 2 U)
    (hUI : U ⊓ (MulAut.conj : LargeEvenProj (unitarySU 2 n K d) →* MulAut _).range ≠ ⊥)
    {P : GL (Fin d) K} (hP : P ∈ primeFormUnitary h (idGram K d))
    {S : Set (GL (Fin d) K)}
    (hSN : ∀ D ∈ S, D ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    (hSA : ∀ D (hD : D ∈ S), TableB.projConj (unitarySU 2 n K d) ⟨D, hSN D hD⟩ ∈
      Subgroup.normalizer (U : Set (MulAut (LargeEvenProj (unitarySU 2 n K d))))) :
    ∃ s t : Fin d, s ≠ t ∧ ∀ D ∈ S, ∀ τ : Fin d → Kˣ, (∀ i, (τ i : K) ^ (2 ^ n + 1) = 1) →
      P⁻¹ * D * P = diagHom d τ → τ s = τ t := by
  classical
  set π := LargeEvenProjMk (unitarySU 2 n K d) with hπ
  have hPi : P⁻¹ ∈ primeFormUnitary h (idGram K d) := (primeFormUnitary h (idGram K d)).inv_mem hP
  set c := conjSU h P⁻¹ hPi with hc
  set φ : ↥(unitarySU 2 n K d) →* MulAut (LargeEvenProj (unitarySU 2 n K d)) :=
    (MulAut.conj : LargeEvenProj (unitarySU 2 n K d) →* MulAut _).comp
      (π.comp c.toMonoidHom) with hφ
  have hZ : Subgroup.center (LargeEvenProj (unitarySU 2 n K d)) = ⊥ :=
    center_proj_eq_bot hK hd hdq
  have hker : φ.ker ≤ Subgroup.center ↥(unitarySU 2 n K d) := by
    intro x hx
    have h1 : π (c x) = 1 := conj_injective_of_center hZ (by rw [map_one]; exact hx)
    have h2 : c x ∈ suScalars n d K := by
      have h3 : c x ∈ π.ker := h1
      rwa [hπ, LargeEvenProjMk, QuotientGroup.ker_mk'] at h3
    rw [← map_conjSU_suScalars h P⁻¹ hPi] at h2
    obtain ⟨y, hy, hyx⟩ := h2
    have hxy : y = x := c.injective hyx
    subst hxy
    apply ker_projMk_le_center
    rw [LargeEvenProjMk, QuotientGroup.ker_mk']
    exact hy
  set V := U ⊓ (MulAut.conj : LargeEvenProj (unitarySU 2 n K d) →* MulAut _).range with hV
  have hV2 : IsPGroup 2 V := hU2.to_le inf_le_left
  have hVφ : V ≤ φ.range := by
    rintro _ ⟨-, ⟨r, rfl⟩⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ r
    refine ⟨c.symm x, ?_⟩
    change MulAut.conj (π (c (c.symm x))) = _
    rw [MulEquiv.apply_symm_apply]
  have hBV : Subgroup.normalizer (U : Set (MulAut (LargeEvenProj (unitarySU 2 n K d)))) ≤
      Subgroup.normalizer (V : Set (MulAut (LargeEvenProj (unitarySU 2 n K d)))) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro v
    have hUa := (Subgroup.mem_normalizer_iff.mp ha) v
    constructor
    · rintro ⟨hvU, ⟨r, rfl⟩⟩
      exact ⟨hUa.mp hvU, ⟨a r, (mul_conj_mul_inv_eq a r).symm⟩⟩
    · rintro ⟨hvU, ⟨r, hr⟩⟩
      refine ⟨hUa.mpr hvU, ⟨a⁻¹ r, ?_⟩⟩
      have e := mul_conj_mul_inv_eq a⁻¹ r
      rw [hr, inv_inv] at e
      rw [← e]
      group
  obtain ⟨s, t, hst, hpair⟩ := SURepair.exists_framePair_of_twoSubgroup h hker hUI hV2 hVφ hBV
  refine ⟨s, t, hst, fun D hD τ hτn hτ => hpair _ (hSA D hD) τ ⟨hτn, fun x x' hxx' => ?_⟩⟩
  change TableB.projConj (unitarySU 2 n K d) ⟨D, hSN D hD⟩ * MulAut.conj (π (c x)) *
    (TableB.projConj (unitarySU 2 n K d) ⟨D, hSN D hD⟩)⁻¹ = MulAut.conj (π (c x'))
  rw [mul_conj_mul_inv_eq, projConj_mk_coe]
  congr 2
  apply Subtype.ext
  change D * ((c x : ↥(unitarySU 2 n K d)) : GL (Fin d) K) * D⁻¹ =
    ((c x' : ↥(unitarySU 2 n K d)) : GL (Fin d) K)
  rw [hc, coe_conjSU, coe_conjSU, hxx', ← hτ]
  group

end Inner

section Heis

variable {K : Type} [Field K] [Finite K] {n : ℕ} (h : UnitaryFieldData 2 n K)

omit [Finite K] in
theorem commute_of_mem_closure {G : Type*} [Group G] {k : Set G}
    (hk : ∀ a ∈ k, ∀ b ∈ k, a * b = b * a) {a b : G} (ha : a ∈ Subgroup.closure k)
    (hb : b ∈ Subgroup.closure k) : a * b = b * a := by
  have h1 : Subgroup.closure k ≤ Subgroup.centralizer k :=
    (Subgroup.closure_le _).mpr fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy =>
      hk y hy x hx
  have h2 : Subgroup.closure k ≤ Subgroup.centralizer (Subgroup.closure k : Set G) :=
    (Subgroup.closure_le _).mpr fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy =>
      ((Subgroup.mem_centralizer_iff.mp (h1 hy)) x hx).symm
  exact Subgroup.mem_centralizer_iff.mp (h2 hb) a ha

omit [Finite K] in
theorem norm_eq_one_of_diag {d : ℕ} (hpq : 3 ∣ 2 ^ n + 1) {τ : Fin d → Kˣ} {D : GL (Fin d) K}
    (hD : D ^ 3 = 1) (hτ : D = diagHom d τ) (i : Fin d) :
    (τ i : K) ^ 3 = 1 ∧ (τ i : K) ^ (2 ^ n + 1) = 1 := by
  have h1 : diagHom d (τ ^ 3) = 1 := by rw [map_pow, ← hτ, hD]
  have h2 : τ ^ 3 = 1 := by
    have := congrArg (fun M : GL (Fin d) K => (M : Matrix (Fin d) (Fin d) K)) h1
    funext j
    have e := congrFun (congrFun this j) j
    simp only [coe_diagHom, Units.val_one, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at e
    exact Units.ext e
  have h3 : (τ i : K) ^ 3 = 1 := by
    have := congrFun h2 i
    rw [Pi.pow_apply, Pi.one_apply] at this
    rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
  obtain ⟨k, hk⟩ := hpq
  exact ⟨h3, by rw [hk, pow_mul, h3, one_pow]⟩

include h in
theorem not_normalizes_twoSubgroup (hK : Nat.card K = (2 ^ n) ^ 2) (hpq : 3 ∣ 2 ^ n + 1)
    {U : Subgroup (MulAut (LargeEvenProj (unitarySU 2 n K 6)))} (hU1 : U ≠ ⊥)
    (hU2 : IsPGroup 2 U) {x y z : GL (Fin 6) K}
    (hxu : x ∈ primeFormUnitary h (idGram K 6)) (hyu : y ∈ primeFormUnitary h (idGram K 6))
    (hzu : z ∈ primeFormUnitary h (idGram K 6))
    (hxN : x ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (hyN : y ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (hzN : z ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (hxU : TableB.projConj (unitarySU 2 n K 6) ⟨x, hxN⟩ ∈
      Subgroup.normalizer (U : Set (MulAut (LargeEvenProj (unitarySU 2 n K 6)))))
    (hyU : TableB.projConj (unitarySU 2 n K 6) ⟨y, hyN⟩ ∈
      Subgroup.normalizer (U : Set (MulAut (LargeEvenProj (unitarySU 2 n K 6)))))
    (hzU : TableB.projConj (unitarySU 2 n K 6) ⟨z, hzN⟩ ∈
      Subgroup.normalizer (U : Set (MulAut (LargeEvenProj (unitarySU 2 n K 6)))))
    (hx3 : x ^ 3 = 1) (hz3 : z ^ 3 = 1) {ζ : Kˣ} (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1)
    (hxy : x * y = Matrix.GeneralLinearGroup.scalar (Fin 6) ζ * (y * x))
    (hxz : x * z = z * x) (hyz : y * z = z * y)
    (hzs : z ∉ LargeEvenScalars (Fin 6) K) : False := by
  classical
  have hdq : ((6 : ℕ), 2 ^ n) ≠ (3, 2) := fun he => by
    have := congrArg Prod.fst he
    simp only at this
    omega
  have hζ3' : (ζ : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hζ3, Units.val_one]
  have hζ1' : (ζ : K) ≠ 1 := fun e => hζ1 (Units.ext e)
  have hxyM : (x : Matrix (Fin 6) (Fin 6) K) * (y : Matrix (Fin 6) (Fin 6) K) =
      (ζ : K) • ((y : Matrix (Fin 6) (Fin 6) K) * (x : Matrix (Fin 6) (Fin 6) K)) := by
    have := congrArg (fun M : GL (Fin 6) K => (M : Matrix (Fin 6) (Fin 6) K)) hxy
    simpa only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, scalar_mul_eq_smul,
      Matrix.smul_mul] using this
  by_cases hUI : U ⊓ (MulAut.conj : LargeEvenProj (unitarySU 2 n K 6) →* MulAut _).range = ⊥
  ·
    set S : Set (GL (Fin 6) K) := {x, y} with hS
    have hSU : ∀ D ∈ S, D ∈ primeFormUnitary h ((1 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
      rintro D (rfl | rfl)
      · exact hxu
      · exact hyu
    have hSN : ∀ D ∈ S, D ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) := by
      rintro D (rfl | rfl)
      · exact hxN
      · exact hyN
    obtain ⟨B, hB⟩ := exists_bar_conj_of_outer h hK (by norm_num) (by omega) hU1 hU2 hUI hSU hSN
      (by
        rintro D (rfl | rfl)
        · exact hxU
        · exact hyU)
    obtain ⟨c₁, hc₁⟩ := hB x (Or.inl rfl)
    obtain ⟨c₂, hc₂⟩ := hB y (Or.inr rfl)
    have hfix := frob_eq_of_conj h.bar c₁.ne_zero c₂.ne_zero hc₁ hc₂ hxyM
    rw [UnitaryFieldData.bar_apply] at hfix
    exact pow_ne_self_of_cube hζ3' hζ1' hpq hfix
  ·
    set X : primeFormUnitary h (idGram K 6) := ⟨x, hxu⟩ with hX
    set Z : primeFormUnitary h (idGram K 6) := ⟨z, hzu⟩ with hZ
    have hk : ∀ a ∈ ({X, Z} : Set (primeFormUnitary h (idGram K 6))),
        ∀ b ∈ ({X, Z} : Set (primeFormUnitary h (idGram K 6))), a * b = b * a := by
      have hXZ : X * Z = Z * X := Subtype.ext hxz
      rintro a (rfl | rfl) b (rfl | rfl)
      · rfl
      · exact hXZ
      · exact hXZ.symm
      · rfl
    set H₁ := Subgroup.closure ({X, Z} : Set (primeFormUnitary h (idGram K 6))) with hH₁
    have hpow : ∀ a ∈ H₁, a ^ 3 = 1 := by
      intro a ha
      induction ha using Subgroup.closure_induction with
      | mem a ha =>
        rcases ha with rfl | rfl
        · exact Subtype.ext hx3
        · exact Subtype.ext hz3
      | one => exact one_pow _
      | mul a b ha hb iha ihb =>
        rw [Commute.mul_pow (commute_of_mem_closure hk ha hb) 3, iha, ihb, one_mul]
      | inv a ha iha => rw [inv_pow, iha, inv_one]
    obtain ⟨P, hP⟩ := CFSG.RankThree.PartOne.KFU.exists_unitary_conj_diag h Nat.prime_three hpq
      H₁ (fun a ha b hb => commute_of_mem_closure hk ha hb) hpow
    have hdiag : ∀ D ∈ ({x, z} : Set (GL (Fin 6) K)), ∃ τ : Fin 6 → Kˣ,
        (P : GL (Fin 6) K)⁻¹ * D * P = diagHom 6 τ := by
      rintro D hD
      have hDH : ∃ D' ∈ H₁, (D' : GL (Fin 6) K) = D := by
        rcases hD with rfl | rfl
        · exact ⟨X, Subgroup.subset_closure (Or.inl rfl), rfl⟩
        · exact ⟨Z, Subgroup.subset_closure (Or.inr rfl), rfl⟩
      obtain ⟨D', hD'H, rfl⟩ := hDH
      have := hP D' hD'H
      exact exists_diagHom_of_isDiag (by simpa using this)
    obtain ⟨η, hη⟩ := hdiag x (Or.inl rfl)
    obtain ⟨ε, hε⟩ := hdiag z (Or.inr rfl)
    have hPx3 : ((P : GL (Fin 6) K)⁻¹ * x * P) ^ 3 = 1 := by
      have e := conj_pow (a := (P : GL (Fin 6) K)⁻¹) (b := x) (i := 3)
      rw [inv_inv] at e
      rw [e, hx3, mul_one, inv_mul_cancel]
    have hPz3 : ((P : GL (Fin 6) K)⁻¹ * z * P) ^ 3 = 1 := by
      have e := conj_pow (a := (P : GL (Fin 6) K)⁻¹) (b := z) (i := 3)
      rw [inv_inv] at e
      rw [e, hz3, mul_one, inv_mul_cancel]
    have hSN : ∀ D ∈ ({x, z} : Set (GL (Fin 6) K)),
        D ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) := by
      rintro D (rfl | rfl)
      · exact hxN
      · exact hzN
    obtain ⟨s, t, hst, hpair⟩ := exists_pair_of_inn h hK (by norm_num) hdq hU2 hUI P.2 hSN
      (by
        rintro D (rfl | rfl)
        · exact hxU
        · exact hzU)
    have hηst := hpair x (Or.inl rfl) η (fun i => (norm_eq_one_of_diag hpq hPx3 hη i).2) hη
    have hεst := hpair z (Or.inr rfl) ε (fun i => (norm_eq_one_of_diag hpq hPz3 hε i).2) hε
    set Y : Matrix (Fin 6) (Fin 6) K :=
      (((P : GL (Fin 6) K)⁻¹ * y * P : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) with hY
    have hYdet : Y.det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).mp
        (Units.isUnit ((P : GL (Fin 6) K)⁻¹ * y * (P : GL (Fin 6) K)))).ne_zero
    have hconj : ∀ A B : GL (Fin 6) K, (P : GL (Fin 6) K)⁻¹ * (A * B) * P =
        ((P : GL (Fin 6) K)⁻¹ * A * P) * ((P : GL (Fin 6) K)⁻¹ * B * P) := fun A B => by group
    have hxy' : diagHom 6 η * ((P : GL (Fin 6) K)⁻¹ * y * P) =
        Matrix.GeneralLinearGroup.scalar (Fin 6) ζ * (((P : GL (Fin 6) K)⁻¹ * y * P) *
          diagHom 6 η) := by
      rw [← hη, ← hconj, hxy, ← hconj]
      calc (P : GL (Fin 6) K)⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 6) ζ * (y * x)) * P =
          ((P : GL (Fin 6) K)⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 6) ζ) * (y * x) * P := by
            group
        _ = (Matrix.GeneralLinearGroup.scalar (Fin 6) ζ * (P : GL (Fin 6) K)⁻¹) * (y * x) * P := by
            rw [← TypeA.PGLTor.scalar_mul_comm]
        _ = _ := by group
    have hzy' : diagHom 6 ε * ((P : GL (Fin 6) K)⁻¹ * y * P) =
        ((P : GL (Fin 6) K)⁻¹ * y * P) * diagHom 6 ε := by
      rw [← hε, ← hconj, ← hconj, hyz]
    have hrel : ∀ i j, Y i j ≠ 0 → (η i : K) = (ζ : K) * η j ∧ (ε i : K) = ε j := by
      intro i j hij
      have e1 := congrFun (congrFun (congrArg (fun M : GL (Fin 6) K =>
        (M : Matrix (Fin 6) (Fin 6) K)) hxy') i) j
      have e2 := congrFun (congrFun (congrArg (fun M : GL (Fin 6) K =>
        (M : Matrix (Fin 6) (Fin 6) K)) hzy') i) j
      simp only [Units.val_mul, coe_diagHom, Matrix.diagonal_mul, Matrix.mul_diagonal,
        Matrix.GeneralLinearGroup.coe_scalar, scalar_mul_eq_smul, Matrix.smul_apply,
        smul_eq_mul, ← hY] at e1 e2
      constructor
      · exact mul_right_cancel₀ hij (by rw [e1]; ring)
      · exact mul_right_cancel₀ hij (by rw [e2, mul_comm])
    have hconst := eq_of_heis (η := fun i => (η i : K)) (ε := fun i => (ε i : K)) hYdet hrel
      (fun i => (η i).ne_zero) hζ3' hζ1' hst (congrArg Units.val hηst)
      (congrArg Units.val hεst)
    apply hzs
    refine ⟨ε s, ?_⟩
    have hεc : diagHom 6 ε = Matrix.GeneralLinearGroup.scalar (Fin 6) (ε s) := by
      apply Units.ext
      rw [coe_diagHom, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
      congr 1
      funext i
      exact hconst i
    calc Matrix.GeneralLinearGroup.scalar (Fin 6) (ε s) =
        (P : GL (Fin 6) K) * diagHom 6 ε * (P : GL (Fin 6) K)⁻¹ := by
          rw [hεc, ← TypeA.PGLTor.scalar_mul_comm, mul_inv_cancel_right]
      _ = z := by rw [← hε]; group

end Heis

end TableBU63

end CFSG.StandardType
