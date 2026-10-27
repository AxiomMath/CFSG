module

public import CFSG.LocalAnalysis.StandardType.GGL45TALinRank

public section

namespace CFSG.StandardType.GGL45TA

open CFSG CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA Matrix

variable {k : Type} [Field k]

@[expose] noncomputable def diagGL (n : ℕ) : (Fin n → kˣ) →* GL (Fin n) k :=
  (Units.map (Matrix.diagonalRingHom (Fin n) k).toMonoidHom).comp
    (MulEquiv.piUnits (M := fun _ : Fin n => k)).symm.toMonoidHom

theorem coe_diagGL (n : ℕ) (t : Fin n → kˣ) :
    ((diagGL n t : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = diagonal fun i => (t i : k) := rfl

theorem diagGL_mem_sl {n : ℕ} {t : Fin n → kˣ} (ht : ∏ i, t i = 1) :
    diagGL n t ∈ LargeEvenSLGroup (Fin n) k := by
  rw [TypeA.mem_largeEvenSLGroup_iff, coe_diagGL, det_diagonal, ← Units.coe_prod, ht, Units.val_one]

@[expose] noncomputable def rootSL {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    Multiplicative k →* LargeEvenSLGroup (Fin n) k where
  toFun c := (TypeA.slKerEquiv n k).symm
    (Matrix.SpecialLinearGroup.transvection hij (Multiplicative.toAdd c))
  map_one' := by
    change (TypeA.slKerEquiv n k).symm
      (Matrix.SpecialLinearGroup.transvection hij (Multiplicative.toAdd 1)) = 1
    rw [toAdd_one, Matrix.SpecialLinearGroup.transvection_coeff_zero, map_one]
  map_mul' a b := by
    change (TypeA.slKerEquiv n k).symm
        (Matrix.SpecialLinearGroup.transvection hij (Multiplicative.toAdd (a * b))) =
      (TypeA.slKerEquiv n k).symm
          (Matrix.SpecialLinearGroup.transvection hij (Multiplicative.toAdd a)) *
        (TypeA.slKerEquiv n k).symm
          (Matrix.SpecialLinearGroup.transvection hij (Multiplicative.toAdd b))
    rw [← map_mul, toAdd_mul]
    congr 1
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul]
    show Matrix.transvection i j _ = Matrix.transvection i j _ * Matrix.transvection i j _
    exact (Matrix.transvection_mul_transvection_same i j hij _ _).symm

theorem coe_rootSL {n : ℕ} {i j : Fin n} (hij : i ≠ j) (c : Multiplicative k) :
    (((rootSL hij c : LargeEvenSLGroup (Fin n) k) : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      1 + single i j (Multiplicative.toAdd c) := by
  rw [← TypeA.coe_slKerEquiv, rootSL, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.apply_symm_apply]
  rfl

theorem map_diagGL (σ : k ≃+* k) (n : ℕ) (t : Fin n → kˣ) :
    Matrix.GeneralLinearGroup.map σ.toRingHom (diagGL n t) =
      diagGL n fun i => Units.map σ.toRingHom.toMonoidHom (t i) := by
  apply Units.ext
  rw [YS09Field.coe_glMap, coe_diagGL, coe_diagGL, diagonal_map (map_zero _)]
  rfl

theorem map_rootSL (σ : k ≃+* k) {n : ℕ} {i j : Fin n} (hij : i ≠ j) (c : Multiplicative k) :
    Matrix.GeneralLinearGroup.map σ.toRingHom (rootSL hij c : GL (Fin n) k) =
      (rootSL hij (Multiplicative.ofAdd (σ (Multiplicative.toAdd c))) : GL (Fin n) k) := by
  apply Units.ext
  rw [YS09Field.coe_glMap, coe_rootSL, coe_rootSL, Matrix.map_add, Matrix.map_one, map_single]
  · rfl
  · exact map_zero _
  · exact map_one _
  · exact map_add _

theorem diagGL_conj_rootSL {n : ℕ} {i j : Fin n} (hij : i ≠ j) (t : Fin n → kˣ)
    (c : Multiplicative k) :
    diagGL n t * (rootSL hij c : GL (Fin n) k) * (diagGL n t)⁻¹ =
      (rootSL hij (Multiplicative.ofAdd ((t i : k) * Multiplicative.toAdd c * (t j : k)⁻¹)) :
        GL (Fin n) k) := by
  have hinv : (diagGL n t)⁻¹ = diagGL n t⁻¹ := (map_inv _ _).symm
  rw [hinv]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_diagGL, coe_diagGL, coe_rootSL, coe_rootSL]
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Pi.inv_apply, toAdd_ofAdd]
  have ht : ∀ x : Fin n, (t x : k) * ((t x)⁻¹ : kˣ) = 1 := fun x => Units.mul_inv _
  by_cases hab : a = b
  · subst hab
    have : ¬ (i = a ∧ j = a) := fun h => hij (h.1.trans h.2.symm)
    simp only [if_true, this, if_false, add_zero, mul_one]
    exact ht a
  · simp only [hab, if_false, zero_add, mul_zero]
    by_cases hia : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := hia
      simp only [and_self, if_true, Units.val_inv_eq_inv_val]
    · simp only [hia, if_false, mul_zero, zero_mul]

namespace LinSetting

variable {d : ℕ} [Finite k] {K : Type} [Group K] {p q₀ : ℕ} {ψ : MulAut K}
  {E : Subgroup (MulAut K)}

theorem rk_bound (S : LinSetting p q₀ d k K ψ E) : p ^ (d - 2) * p ≤ Nat.card E * p ^ 2 := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 2 := ⟨d - 2, by have := S.three_le; omega⟩
  rw [show m + 2 - 2 = m by omega]
  haveI : CharP k 2 := S.char_two
  haveI : Finite K := Finite.of_surjective S.π S.surj
  haveI : NeZero p := ⟨S.hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := S.exists_primitive
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  let i₀ : Fin (m + 2) := Fin.castSucc (Fin.last m)
  let i₁ : Fin (m + 2) := Fin.last (m + 1)
  have hi : i₁ ≠ i₀ := (Fin.castSucc_lt_last (Fin.last m)).ne'
  let T : Subgroup (Fin (m + 2) → kˣ) :=
    { carrier := {t | (∀ i, t i ^ p = 1) ∧ t i₀ = 1 ∧ ∏ i, t i = 1}
      mul_mem' := fun {a b} ha hb => ⟨fun i => by
          rw [Pi.mul_apply, mul_pow, ha.1 i, hb.1 i, one_mul],
        by rw [Pi.mul_apply, ha.2.1, hb.2.1, one_mul],
        by rw [show (∏ i, (a * b) i) = ∏ i, a i * b i from rfl, Finset.prod_mul_distrib, ha.2.2,
          hb.2.2, one_mul]⟩
      one_mem' := ⟨fun i => one_pow p, rfl, Finset.prod_const_one⟩
      inv_mem' := fun {a} ha => ⟨fun i => by rw [Pi.inv_apply, inv_pow, ha.1 i, inv_one],
        by rw [Pi.inv_apply, ha.2.1, inv_one],
        by rw [show (∏ i, a⁻¹ i) = ∏ i, (a i)⁻¹ from rfl, Finset.prod_inv_distrib, ha.2.2,
          inv_one]⟩ }
  let δ : T →* LargeEvenSLGroup (Fin (m + 2)) k :=
    ((diagGL (m + 2)).comp T.subtype).codRestrict _ fun t => diagGL_mem_sl t.2.2.2
  have hδ : ∀ t : T, ((δ t : LargeEvenSLGroup (Fin (m + 2)) k) : GL (Fin (m + 2)) k) =
      diagGL (m + 2) t.1 := fun t => rfl
  let ρ : T →* K := S.π.comp δ
  let ν : Multiplicative k →* K := S.π.comp (rootSL hi)
  set R₀ := ρ.range with hR₀
  set Q := ν.range with hQ
  have hψ : ∀ h h' : LargeEvenSLGroup (Fin (m + 2)) k,
      (h' : GL (Fin (m + 2)) k) = Matrix.GeneralLinearGroup.map S.τ.toRingHom h →
        ψ (S.π h) = S.π h' := fun h h' hh' =>
    S.ψ_impl h h' (by rw [hh', one_mul, inv_one, mul_one])
  have hτt : ∀ t : T, (fun i => Units.map S.τ.toRingHom.toMonoidHom (t.1 i)) = t.1 := fun t =>
    funext fun i => S.units_map_eq (m := 1) (by rw [pow_one]; exact S.tau_pow) (t.2.1 i)
  have hTcomm : ∀ a b : T, a * b = b * a := fun a b => Subtype.ext (mul_comm _ _)
  have hR₀elem : IsElemAbelian p R₀ := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a, ha⟩ := x.2
      obtain ⟨b, hb⟩ := y.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha, ← hb, ← map_mul, ← map_mul, hTcomm]
    · obtain ⟨a, rfl⟩ := hx
      rw [← map_pow]
      have : a ^ p = 1 := Subtype.ext (funext fun i => by
        rw [Subgroup.coe_pow, Pi.pow_apply]; exact a.2.1 i)
      rw [this, map_one]
  have hR₀ψ : ∀ r ∈ R₀, ψ r = r := by
    rintro _ ⟨a, rfl⟩
    exact hψ (δ a) (δ a) (by rw [hδ, map_diagGL, hτt])
  have hQ2 : IsPGroup 2 Q := by
    rintro ⟨_, c, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← map_pow, sq, ← ofAdd_toAdd c, ← ofAdd_add,
      CharTwo.add_self_eq_zero, ofAdd_zero, map_one]
  have hQne : Q ≠ ⊥ := by
    intro hbot
    have hmem : ν (Multiplicative.ofAdd 1) ∈ Q := ⟨_, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have hker : rootSL hi (Multiplicative.ofAdd (1 : k)) ∈ S.π.ker := hmem
    obtain ⟨c, hc⟩ := S.ker_le _ hker
    have h1 := congrArg (fun g : GL (Fin (m + 2)) k => (g : Matrix _ _ k) i₁ i₀) hc
    simp only [Matrix.GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_ne _ hi,
      coe_rootSL, toAdd_ofAdd, Matrix.add_apply, one_apply_ne hi, single_apply_same,
      zero_add] at h1
    exact one_ne_zero h1.symm
  have hQψ : ∀ g ∈ Q, ψ g ∈ Q := by
    rintro _ ⟨c, rfl⟩
    exact ⟨Multiplicative.ofAdd (S.τ (Multiplicative.toAdd c)),
      (hψ (rootSL hi c) _ (by rw [map_rootSL])).symm⟩
  have hconj : ∀ (a : T) (c : Multiplicative k), ∃ c', ρ a * ν c * (ρ a)⁻¹ = ν c' := by
    intro a c
    refine ⟨Multiplicative.ofAdd ((a.1 i₁ : k) * Multiplicative.toAdd c * (a.1 i₀ : k)⁻¹), ?_⟩
    change S.π (δ a) * S.π (rootSL hi c) * (S.π (δ a))⁻¹ = S.π (rootSL hi _)
    rw [← map_mul, ← map_inv, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hδ]
    exact diagGL_conj_rootSL hi a.1 c
  have hnorm : R₀ ≤ Subgroup.normalizer (Q : Set K) := by
    rintro _ ⟨a, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨c, rfl⟩
      obtain ⟨c', hc'⟩ := hconj a c
      exact ⟨c', hc'.symm⟩
    · rintro ⟨c, hc⟩
      obtain ⟨c', hc'⟩ := hconj a⁻¹ c
      refine ⟨c', ?_⟩
      rw [← hc', hc, map_inv]
      group
  have hrk := S.rk R₀ Q hR₀elem hR₀ψ hQ2 hQne hQψ hnorm
  let tvec : (Fin m → Fin p) → Fin (m + 2) → kˣ := fun s =>
    Fin.snoc (Fin.snoc (fun j => ζ ^ (s j : ℕ)) 1) (∏ j, ζ ^ (s j : ℕ))⁻¹
  have hz : ∀ n : ℕ, (ζ ^ n) ^ p = 1 := fun n => by
    rw [← pow_mul, mul_comm, pow_mul, hζp, one_pow]
  have htvecT : ∀ s, tvec s ∈ T := by
    intro s
    refine ⟨fun i => ?_, ?_, ?_⟩
    · refine Fin.lastCases ?_ (fun i => ?_) i
      · simp only [tvec, Fin.snoc_last, inv_pow, ← Finset.prod_pow, hz, Finset.prod_const_one,
          inv_one]
      · refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [tvec, Fin.snoc_castSucc, Fin.snoc_last]
        · simp only [tvec, Fin.snoc_castSucc, hz]
    · simp [tvec, i₀, Fin.snoc_castSucc, Fin.snoc_last]
    · rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
      simp [tvec, Fin.snoc_castSucc, Fin.snoc_last]
  let F : (Fin m → Fin p) → R₀ := fun s => ⟨ρ ⟨tvec s, htvecT s⟩, ⟨_, rfl⟩⟩
  have hF : Function.Injective F := by
    intro s s' hss'
    have h1 : ρ ⟨tvec s, htvecT s⟩ = ρ ⟨tvec s', htvecT s'⟩ := congrArg Subtype.val hss'
    have h2 : δ ⟨tvec s, htvecT s⟩ * (δ ⟨tvec s', htvecT s'⟩)⁻¹ ∈ S.π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      exact mul_inv_eq_one.mpr h1
    obtain ⟨c, hc⟩ := S.ker_le _ h2
    have hentry : ∀ i, (tvec s i : k) * (tvec s' i : k)⁻¹ = c := by
      intro i
      have h3 := congrArg (fun g : GL (Fin (m + 2)) k => (g : Matrix _ _ k) i i) hc
      simp only [Matrix.GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq,
        Subgroup.coe_mul, Subgroup.coe_inv, hδ, Units.val_mul, coe_diagGL] at h3
      rw [← map_inv, coe_diagGL, diagonal_mul_diagonal, diagonal_apply_eq] at h3
      simpa using h3.symm
    have hc1 : (c : k) = 1 := by
      have := hentry i₀
      simp only [tvec, i₀, Fin.snoc_castSucc, Fin.snoc_last, Units.val_one, inv_one,
        mul_one] at this
      exact this.symm
    funext j
    have h4 := hentry (Fin.castSucc (Fin.castSucc j))
    rw [hc1] at h4
    simp only [tvec, Fin.snoc_castSucc] at h4
    have h5 : ζ ^ (s j : ℕ) = ζ ^ (s' j : ℕ) := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
      have hne : ((ζ ^ (s' j : ℕ) : kˣ) : k) ≠ 0 := Units.ne_zero _
      field_simp at h4
      simpa using h4
    exact Fin.ext (hζ.pow_inj (s j).2 (s' j).2 h5)
  have hcard : p ^ m ≤ Nat.card R₀ := by
    have := Nat.card_le_card_of_injective F hF
    rwa [Nat.card_fun, Nat.card_fin, Nat.card_fin] at this
  calc p ^ m * p ≤ Nat.card R₀ * p := Nat.mul_le_mul_right p hcard
    _ ≤ Nat.card E * p ^ 2 := hrk

end LinSetting

end CFSG.StandardType.GGL45TA
