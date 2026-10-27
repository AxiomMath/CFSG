module

public import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint (LieModel suzukiS suzukiN suzukiD suzukiGroup)
open CFSG.Open (StatedProj StatedSL)

private theorem charP_two_of_natCard_eq_two_pow_torus {K : Type*} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) : CharP K 2 := by
  have := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (p := 2) (f := n) (by rwa [← Nat.card_eq_fintype_card])

private theorem eq_bot_or_eq_range_of_conj {K X : Type} [Field K] [Group X]
    (φ : Multiplicative K →* X) (c : X) (μ : Kˣ) (hμ : ∀ x : Kˣ, ∃ k : ℕ, μ ^ k = x)
    (hc : ∀ a : K, c * φ (Multiplicative.ofAdd a) * c⁻¹ =
      φ (Multiplicative.ofAdd ((μ : K) * a)))
    (U : Subgroup X) (hUV : U ≤ φ.range) (hU : ∀ u ∈ U, c * u * c⁻¹ ∈ U) :
    U = ⊥ ∨ U = φ.range := by
  by_cases h : ∀ a : K, φ (Multiplicative.ofAdd a) ∈ U → a = 0
  · left
    refine eq_bot_iff.2 fun u hu => ?_
    obtain ⟨x, rfl⟩ := hUV hu
    have hx : x.toAdd = 0 := h x.toAdd hu
    have : x = 1 := Multiplicative.toAdd.injective (by simpa using hx)
    simp [this]
  · right
    push Not at h
    obtain ⟨a₀, ha₀, ha₀0⟩ := h
    have key : ∀ k : ℕ, φ (Multiplicative.ofAdd ((μ : K) ^ k * a₀)) ∈ U := by
      intro k
      induction k with
      | zero => simpa using ha₀
      | succ k ih =>
        have e : (μ : K) ^ (k + 1) * a₀ = (μ : K) * ((μ : K) ^ k * a₀) := by ring
        rw [e, ← hc]
        exact hU _ ih
    refine le_antisymm hUV ?_
    rintro _ ⟨x, rfl⟩
    by_cases hx : x.toAdd = 0
    · have : x = 1 := Multiplicative.toAdd.injective (by simpa using hx)
      simp [this]
    · obtain ⟨k, hk⟩ := hμ (Units.mk0 (x.toAdd / a₀) (div_ne_zero hx ha₀0))
      have hk' : (μ : K) ^ k = x.toAdd / a₀ := by simpa using congrArg Units.val hk
      have hxk : x = Multiplicative.ofAdd ((μ : K) ^ k * a₀) := by
        rw [hk', div_mul_cancel₀ _ ha₀0]
        rfl
      rw [hxk]
      exact key k

private theorem exists_of_injective_root_torus {K X H : Type} [Field K] [Finite K] [Group X]
    [Finite X] [Group H] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 3 ≤ n) (e : X ≃* H)
    (R : Multiplicative K →* H) (hR : Function.Injective R)
    (ht : Nat.card K = 8 → ∀ l : Kˣ, ∃ d : H, ∀ a : K,
      d * R (Multiplicative.ofAdd a) * d⁻¹ = R (Multiplicative.ofAdd ((l : K) ^ 2 * a))) :
    ∃ V : Subgroup X, IsMulCommutative V ∧ (∀ v ∈ V, v ^ 2 = 1) ∧ 8 ≤ Nat.card V ∧
      (Nat.card V = 8 → ∃ c ∈ Subgroup.normalizer (V : Set X), ∀ U : Subgroup X, U ≤ V →
        (∀ u ∈ U, c * u * c⁻¹ ∈ U) → U = ⊥ ∨ U = V) := by
  have hchar : CharP K 2 := charP_two_of_natCard_eq_two_pow_torus hK
  let φ : Multiplicative K →* X := e.symm.toMonoidHom.comp R
  have hφ : Function.Injective φ := e.symm.injective.comp hR
  have hcard : Nat.card φ.range = 2 ^ n := by
    rw [Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv.symm, Nat.card_congr Multiplicative.toAdd,
      hK]
  refine ⟨φ.range, Subgroup.range_isMulCommutative φ, ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have : x ^ 2 = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one, two_nsmul, CharTwo.add_self_eq_zero]
    rw [this, map_one]
  · rw [hcard]
    exact (Nat.pow_le_pow_right (by norm_num) hn : 2 ^ 3 ≤ 2 ^ n)
  · intro h8
    have hK8 : Nat.card K = 8 := by rw [hK, ← hcard]; exact h8
    obtain ⟨μ, hμ⟩ := IsCyclic.exists_generator (α := Kˣ)
    have hμpow : ∀ x : Kˣ, ∃ k : ℕ, μ ^ k = x := fun x =>
      (Submonoid.mem_powers_iff x μ).1 (mem_powers_iff_mem_zpowers.2 (hμ x))
    have hμ7 : μ ^ 7 = 1 := by
      have h := pow_card_eq_one' (G := Kˣ) (x := μ)
      rwa [Nat.card_units, hK8] at h
    have hl : (μ ^ 4) ^ 2 = μ := by
      calc (μ ^ 4) ^ 2 = μ ^ 7 * μ := by rw [← pow_mul, ← pow_succ]
        _ = μ := by rw [hμ7, one_mul]
    obtain ⟨d, hd⟩ := ht hK8 (μ ^ 4)
    have hc : ∀ a : K, e.symm d * φ (Multiplicative.ofAdd a) * (e.symm d)⁻¹ =
        φ (Multiplicative.ofAdd ((μ : K) * a)) := by
      intro a
      have h1 : (((μ ^ 4 : Kˣ) : K)) ^ 2 = (μ : K) := by simpa using congrArg Units.val hl
      have := congrArg e.symm (hd a)
      rw [h1] at this
      simpa [φ] using this
    refine ⟨e.symm d, ?_, fun U hUV hU => eq_bot_or_eq_range_of_conj φ _ μ hμpow hc U hUV hU⟩
    apply Subgroup.mem_normalizer_fintype
    rintro _ ⟨x, rfl⟩
    exact ⟨Multiplicative.ofAdd ((μ : K) * x.toAdd), (hc x.toAdd).symm⟩

private theorem diagonal_mul_transvection_eq_mul_diagonal {m : ℕ} {K : Type} [Field K] {i j : Fin m}
    (hij : i ≠ j) (v : Fin m → K) (a b : K) (hab : v i * a = b * v j) :
    Matrix.diagonal v * Matrix.transvection i j a =
      Matrix.transvection i j b * Matrix.diagonal v := by
  ext k l
  simp only [Matrix.transvection, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply]
  by_cases h1 : i = k
  · by_cases h2 : j = l
    · subst h1 h2
      simp [hij, hab]
    · by_cases h3 : k = l
      · subst h3
        simp [h2]
      · simp [h2, h3]
  · by_cases h3 : k = l
    · subst h3
      simp [h1]
    · simp [h1, h3]

private theorem exists_root_torus_statedProj {m : ℕ} (hm : 2 ≤ m) (K : Type) [Field K] :
    ∃ R : Multiplicative K →* StatedProj (StatedSL m K), Function.Injective R ∧
      ∀ l : Kˣ, ∃ d : StatedProj (StatedSL m K), ∀ a : K,
        d * R (Multiplicative.ofAdd a) * d⁻¹ = R (Multiplicative.ofAdd ((l : K) ^ 2 * a)) := by
  let i : Fin m := ⟨0, by omega⟩
  let j : Fin m := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j, Fin.ext_iff]
  let T : Multiplicative K →* Matrix (Fin m) (Fin m) K :=
    { toFun := fun a => Matrix.transvection i j a.toAdd
      map_one' := Matrix.transvection_zero i j
      map_mul' := fun a b => (Matrix.transvection_mul_transvection_same i j hij _ _).symm }
  let T' : Multiplicative K →* StatedSL m K :=
    T.toHomUnits.codRestrict (StatedSL m K) fun a =>
      Subgroup.subset_closure (Matrix.det_transvection_of_ne i j hij a.toAdd)
  refine ⟨(QuotientGroup.mk' _).comp T', ?_, fun l => ?_⟩
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at ha
    obtain ⟨c, hc⟩ := ha
    have hij' := congrArg (fun g : GL (Fin m) K => (g : Matrix (Fin m) (Fin m) K) i j) hc
    simp [T', T, Matrix.transvection, hij] at hij'
    exact Subgroup.mem_bot.mpr (Multiplicative.toAdd.injective (by simpa using hij'.symm))
  · let v : Fin m → K := fun k =>
      (if k = i then (l : K) else 1) * (if k = j then (l : K)⁻¹ else 1)
    have hvi : v i = l := by simp [v, hij]
    have hvj : v j = (l : K)⁻¹ := by simp [v, hij.symm]
    have hdet : (Matrix.diagonal v).det = 1 := by
      rw [Matrix.det_diagonal]
      simp only [v, Finset.prod_mul_distrib]
      rw [Fintype.prod_ite_eq' i (fun _ => (l : K)), Fintype.prod_ite_eq' j (fun _ => (l : K)⁻¹)]
      exact mul_inv_cancel₀ l.ne_zero
    let D : GL (Fin m) K :=
      Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal v) (by rw [hdet]; exact one_ne_zero)
    let dS : StatedSL m K := ⟨D, Subgroup.subset_closure hdet⟩
    refine ⟨QuotientGroup.mk' _ dS, fun a => ?_⟩
    simp only [MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    rw [mul_inv_eq_iff_eq_mul]
    refine Subtype.ext (Units.ext ?_)
    exact diagonal_mul_transvection_eq_mul_diagonal hij v _ _
      (by rw [hvi, hvj, toAdd_ofAdd, toAdd_ofAdd]; field_simp)

private theorem suzukiD_mul_suzukiS_eight {K : Type} [Field K] (l x : K) (hl : l ^ 7 = 1) :
    Matrix.diagonal ![l ^ 3, l ^ 2, l ^ 5, l ^ 4] * suzukiS 1 0 x =
      suzukiS 1 0 (l ^ 2 * x) * Matrix.diagonal ![l ^ 3, l ^ 2, l ^ 5, l ^ 4] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suzukiS, suzukiN, Matrix.diagonal_mul, Matrix.mul_diagonal]
  all_goals first | ring1 | linear_combination (-(l ^ 4 * x ^ 4)) * hl

private theorem exists_root_torus_suzuki (a : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] :
    ∃ R : Multiplicative K →* suzukiGroup a K, Function.Injective R ∧
      (a = 1 → Nat.card K = 8 → ∀ l : Kˣ, ∃ d : suzukiGroup a K, ∀ x : K,
        d * R (Multiplicative.ofAdd x) * d⁻¹ = R (Multiplicative.ofAdd ((l : K) ^ 2 * x))) := by
  have hadd : ∀ x y : K, (x + y) ^ 2 ^ (a + 1) = x ^ 2 ^ (a + 1) + y ^ 2 ^ (a + 1) :=
    fun x y => add_pow_char_pow x y 2 (a + 1)
  let S : Multiplicative K →* Matrix (Fin 4) (Fin 4) K :=
    { toFun := fun v => suzukiS a 0 v.toAdd
      map_one' := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [suzukiS, suzukiN]
      map_mul' := fun v w => by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [suzukiS, suzukiN, Matrix.mul_apply, Fin.sum_univ_four, hadd] }
  let S' : Multiplicative K →* suzukiGroup a K :=
    S.toHomUnits.codRestrict (suzukiGroup a K) fun v =>
      Subgroup.subset_closure (Or.inl ⟨0, v.toAdd, rfl⟩)
  refine ⟨S', fun v w hvw => ?_, ?_⟩
  · have h20 := congrArg
      (fun g : suzukiGroup a K => ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 2 0) hvw
    simpa [S', S, suzukiS] using h20
  · rintro rfl h8 l
    have := Fintype.ofFinite K
    have hl7 : (l : K) ^ 7 = 1 := by
      have h := FiniteField.pow_card_sub_one_eq_one (l : K) l.ne_zero
      rwa [← Nat.card_eq_fintype_card, h8] at h
    have h5 : ((l : K) ^ 2)⁻¹ = (l : K) ^ 5 :=
      inv_eq_of_mul_eq_one_right (by rw [← pow_add]; exact hl7)
    have h4 : ((l : K) ^ 3)⁻¹ = (l : K) ^ 4 :=
      inv_eq_of_mul_eq_one_right (by rw [← pow_add]; exact hl7)
    have hD : suzukiD 1 l =
        Matrix.diagonal ![(l : K) ^ 3, (l : K) ^ 2, (l : K) ^ 5, (l : K) ^ 4] := by
      unfold suzukiD
      congr 1
      ext i
      fin_cases i
      · simp
      · simp
      · simp [zpow_neg, h5]
      · simp [zpow_neg, h4]
    have hdet : (suzukiD 1 l).det ≠ 0 := by
      rw [hD, Matrix.det_diagonal, Fin.prod_univ_four]
      simp [l.ne_zero]
    let D : GL (Fin 4) K := Matrix.GeneralLinearGroup.mkOfDetNeZero (suzukiD 1 l) hdet
    have hDmem : D ∈ suzukiGroup 1 K := Subgroup.subset_closure (Or.inr (Or.inl ⟨l, rfl⟩))
    refine ⟨⟨D, hDmem⟩, fun x => ?_⟩
    rw [mul_inv_eq_iff_eq_mul]
    refine Subtype.ext (Units.ext ?_)
    have hS' : ∀ y : K, (((S' (Multiplicative.ofAdd y) : suzukiGroup 1 K) : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) = suzukiS 1 0 y := fun y => rfl
    have hDv : (((⟨D, hDmem⟩ : suzukiGroup 1 K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        suzukiD 1 l := rfl
    rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_mul, Units.val_mul, hS', hS', hDv, hD]
    exact suzukiD_mul_suzukiS_eight (l : K) x hl7

theorem exists_elemAbelian_irred_of_isCalL1 {X : Type} [Group X] [Finite X] (h : IsCalL1 X) :
    ∃ V : Subgroup X, IsMulCommutative V ∧ (∀ v ∈ V, v ^ 2 = 1) ∧ 8 ≤ Nat.card V ∧
      (Nat.card V = 8 → ∃ c ∈ Subgroup.normalizer (V : Set X), ∀ U : Subgroup X, U ≤ V →
        (∀ u ∈ U, c * u * c⁻¹ ∈ U) → U = ⊥ ∨ U = V) := by
  obtain ⟨n, hodd, hn1, hX⟩ := h
  have hn3 : 3 ≤ n := by
    obtain ⟨k, hk⟩ := hodd
    omega
  rcases hX with hL2 | hSz | hL3
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ :=
      (show LieModel X .PSL 2 2 n from hL2).statedClassicalModel (by decide)
    obtain ⟨R, hR, hRt⟩ := exists_root_torus_statedProj le_rfl K
    exact exists_of_injective_root_torus hK hn3 e R hR fun _ => hRt
  · obtain ⟨-, -, a, -, K, _, _, hfa, hK, ⟨e⟩⟩ :=
      (show LieModel X .twistedB2 0 2 n from hSz).suzukiModel
    have : CharP K 2 := charP_two_of_natCard_eq_two_pow_torus hK
    obtain ⟨R, hR, hRt⟩ := exists_root_torus_suzuki a K
    refine exists_of_injective_root_torus hK hn3 e R hR fun h8 => hRt ?_ h8
    have h2 : 2 ^ n = 2 ^ 3 := by rw [← hK, h8]; norm_num
    have := Nat.pow_right_injective (le_refl 2) h2
    omega
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ :=
      (show LieModel X .PSL 3 2 n from hL3).statedClassicalModel (by decide)
    obtain ⟨R, hR, hRt⟩ := exists_root_torus_statedProj (m := 3) (by norm_num) K
    exact exists_of_injective_root_torus hK hn3 e R hR fun _ => hRt

end CFSG.LocalAnalysis.WeakClosure81

end
