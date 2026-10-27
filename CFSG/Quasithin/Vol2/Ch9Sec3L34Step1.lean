module

public import CFSG.Quasithin.Vol2.Ch9Sec3L34Out
public import CFSG.Quasithin.Vol2.Ch9Sec3L34KG1
public import CFSG.LocalAnalysis.EvenBN.TwoF4.CoprimeProduct
public import CFSG.Quasithin.Vol2.Ch9Sec3Cart
public import CFSG.Quasithin.Vol2.Ch9Sec3Conj
public import CFSG.Quasithin.Vol2.Ch9Sec3L34Max

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

section Model

open CFSG.Quasithin.H Matrix

namespace Om4Pt

variable {K : Type} [Field K]

theorem exists_ne_of_commute_swap [CharP K 2] [Fintype K] (hK4 : Fintype.card K = 4)
    {A B : GL (Fin 2) K} {τ : K ≃+* K} (hA : Om4.IsUT A) (hB : Om4.IsUT B) {a : Kˣ}
    (ha : a ≠ 1)
    (hcomm : (Om4.lr A B * Om4.frM τ * Om4.trM) * Om4.rho (diagOf a, diagOf a⁻¹) =
      Om4.rho (diagOf a, diagOf a⁻¹) * (Om4.lr A B * Om4.frM τ * Om4.trM)) :
    ∃ X : Matrix (Fin 2) (Fin 2) K, (Multiplicative.toAdd
      ((Om4.lr A B * Om4.frM τ * Om4.trM : MulAut (Om4.VM K)) (Multiplicative.ofAdd X)) :
        Matrix (Fin 2) (Fin 2) K) 1 1 ≠ X 1 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have ha' : (a : K) ≠ 1 := fun h => ha (Units.ext h)
  have ha0 : (a : K) ≠ 0 := a.ne_zero
  have haa : (a : K) * ((a⁻¹ : Kˣ) : K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hainv : (a : K) ≠ ((a⁻¹ : Kˣ) : K) := by
    intro h
    have h1 : (a : K) * a = 1 := by rw [h] at haa ⊢; rw [← h]; exact h ▸ haa
    have h3 : ((a : K) - 1) ^ 2 = 0 := by linear_combination h1 + (1 - (a : K)) * h2
    exact ha' (sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h3))
  have hconj : (Om4.lr A B * Om4.frM τ * Om4.trM) * Om4.rho (diagOf a, diagOf a⁻¹) *
      (Om4.lr A B * Om4.frM τ * Om4.trM)⁻¹ = Om4.rho (diagOf a, diagOf a⁻¹) := by
    rw [hcomm, mul_inv_cancel_right]
  rw [Om4.rho_apply, Om4.conj_swap] at hconj
  obtain ⟨c, hc0, hcA, -⟩ := Om4.exists_smul_of_lr_eq hconj
  have eA := Om4.conj_map_apply hA (isUT_diagOf a⁻¹) τ
  have hA00 := congrFun (congrFun hcA 0) 0
  have hA11 := congrFun (congrFun hcA 1) 1
  rw [Matrix.smul_apply, smul_eq_mul, eA.1] at hA00
  rw [Matrix.smul_apply, smul_eq_mul, eA.2] at hA11
  simp only [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_diagOf, inv_inv,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at hA00 hA11
  have hc1 : c = 1 := by
    have h5 : τ ((a⁻¹ : Kˣ) : K) * τ (a : K) = 1 := by
      rw [← map_mul, mul_comm, haa, map_one]
    have h3 : c * c = 1 := by
      linear_combination (-(c * c)) * h5 - (c * τ ((a⁻¹ : Kˣ) : K)) * hA11 -
        ((a⁻¹ : Kˣ) : K) * hA00 + haa
    have h6 : (c - 1) ^ 2 = 0 := by linear_combination h3 + (1 - c) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h6)
  rw [hc1, one_mul] at hA11
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    exact hainv hA11.symm
  have hfrob := frob_of_ne_one hK4 hτ1
  have key : ∀ μ : K, (Multiplicative.toAdd ((Om4.lr A B * Om4.frM τ * Om4.trM : MulAut (Om4.VM K))
      (Multiplicative.ofAdd (!![0, 0; 0, μ] : Matrix (Fin 2) (Fin 2) K))) :
        Matrix (Fin 2) (Fin 2) K) 1 1 =
      (A : Matrix (Fin 2) (Fin 2) K) 1 1 * μ ^ 2 * (B : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    intro μ
    simp only [MulAut.mul_apply, Om4.toAdd_lr, Om4.toAdd_frM, Om4.toAdd_trM, toAdd_ofAdd]
    have hA10 : (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := hA
    have hB10 : (B : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := hB
    simp [Matrix.mul_apply, Fin.sum_univ_two, hA10, hB10, hfrob, Matrix.transpose_apply]
  by_cases hc' : (A : Matrix (Fin 2) (Fin 2) K) 1 1 * (B : Matrix (Fin 2) (Fin 2) K) 1 1 = 1
  · refine ⟨!![0, 0; 0, (a : K)], ?_⟩
    rw [key]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    intro h
    have h1 : (a : K) ^ 2 = a := by
      calc (a : K) ^ 2 = ((A : Matrix (Fin 2) (Fin 2) K) 1 1 *
            (B : Matrix (Fin 2) (Fin 2) K) 1 1) * (a : K) ^ 2 := by rw [hc', one_mul]
        _ = (A : Matrix (Fin 2) (Fin 2) K) 1 1 * (a : K) ^ 2 *
            (B : Matrix (Fin 2) (Fin 2) K) 1 1 := by ring
        _ = a := h
    have h4 : (a : K) * ((a : K) - 1) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h4 with h | h
    · exact ha0 h
    · exact ha' (sub_eq_zero.mp h)
  · refine ⟨!![0, 0; 0, 1], ?_⟩
    rw [key]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, one_pow, mul_one]
    exact hc'

theorem mem_of_span [CharP K 2] {W : Set (Matrix (Fin 2) (Fin 2) K)}
    (hadd : ∀ X ∈ W, ∀ Y ∈ W, X + Y ∈ W)
    (hρ : ∀ p q : K, ∀ X ∈ W, !![1, p; 0, 1] * X * (!![1, q; 0, 1])ᵀ ∈ W)
    {Y : Matrix (Fin 2) (Fin 2) K} (hY : Y ∈ W) (hδ : Y 1 1 ≠ 0) :
    ∀ Z : Matrix (Fin 2) (Fin 2) K, Z 1 1 = 0 → Z ∈ W := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set δ := Y 1 1 with hδdef
  have hD : ∀ p q : K, !![p * Y 1 0 + q * Y 0 1 + p * q * δ, p * δ; q * δ, 0] ∈ W := by
    intro p q
    have h := hadd _ (hρ p q Y hY) Y hY
    convert h using 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, hδdef]
    · linear_combination (-Y 0 0) * h2
    · linear_combination (-Y 0 1) * h2
    · linear_combination (-Y 1 0) * h2
    · linear_combination (-Y 1 1) * h2
  have hδ' : δ * δ⁻¹ = 1 := mul_inv_cancel₀ hδ
  have hE00 : ∀ μ : K, !![μ, 0; 0, 0] ∈ W := by
    intro μ
    have h := hadd _ (hadd _ (hD (μ * δ⁻¹) 1) _ (hD (μ * δ⁻¹) 0)) _ (hD 0 1)
    convert h using 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    · linear_combination (-(μ * δ⁻¹ * Y 1 0) - Y 0 1) * h2 - μ * hδ'
    · linear_combination (-(μ * δ⁻¹ * δ)) * h2
    · linear_combination (-δ) * h2
  have hE01 : ∀ ν : K, !![0, ν; 0, 0] ∈ W := by
    intro ν
    have h := hadd _ (hD (ν * δ⁻¹) 0) _ (hE00 (ν * δ⁻¹ * Y 1 0))
    convert h using 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    · linear_combination (-(ν * δ⁻¹ * Y 1 0)) * h2
    · linear_combination -ν * hδ'
  have hE10 : ∀ ν : K, !![0, 0; ν, 0] ∈ W := by
    intro ν
    have h := hadd _ (hD 0 (ν * δ⁻¹)) _ (hE00 (ν * δ⁻¹ * Y 0 1))
    convert h using 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    · linear_combination (-(ν * δ⁻¹ * Y 0 1)) * h2
    · linear_combination -ν * hδ'
  intro Z hZ
  have h := hadd _ (hadd _ (hE00 (Z 0 0)) _ (hE01 (Z 0 1))) _ (hE10 (Z 1 0))
  convert h using 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hZ]

end Om4Pt

end Model

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace L34

theorem commutator_mem_of_relIndex_le_two {V W : Subgroup G}
    (hidx : W.relIndex V ≤ 2) {g : G} (hgV : g ∈ Subgroup.normalizer (V : Set G))
    (hgW : g ∈ Subgroup.normalizer (W : Set G)) {v : G} (hv : v ∈ V) :
    g * v * g⁻¹ * v⁻¹ ∈ W := by
  have hgv : g * v * g⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hgV v).mp hv
  have hpos : 0 < W.relIndex V := Nat.pos_of_ne_zero (by
    rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite)
  rcases Nat.lt_or_ge (W.relIndex V) 2 with h1 | h2
  · have h1' : W.relIndex V = 1 := by omega
    have hVW : V ≤ W := Subgroup.relIndex_eq_one.mp h1'
    exact hVW (V.mul_mem hgv (V.inv_mem hv))
  · have h2' : (W.subgroupOf V).index = 2 := le_antisymm hidx h2
    have key := Subgroup.mul_mem_iff_of_index_two h2' (a := ⟨g * v * g⁻¹, hgv⟩)
      (b := ⟨v⁻¹, V.inv_mem hv⟩)
    have e1 : (⟨g * v * g⁻¹, hgv⟩ : ↥V) ∈ W.subgroupOf V ↔
        (⟨v⁻¹, V.inv_mem hv⟩ : ↥V) ∈ W.subgroupOf V := by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      constructor
      · intro h
        have := (Subgroup.mem_normalizer_iff.mp hgW v).mpr h
        exact W.inv_mem this
      · intro h
        exact (Subgroup.mem_normalizer_iff.mp hgW v).mp (by simpa using W.inv_mem h)
    have := key.mpr e1
    rw [Subgroup.mem_subgroupOf] at this
    simpa using this

omit [Finite G] in
theorem mem_pCoreOf_of_commute {H M K : Subgroup G} (hKH : K ≤ H)
    (hJ : IsPGroup 2 (kerIn (H ⊓ M) H)) (hKL : IsPSL 3 2 2 ↥(E2.star (H ⊓ M) H K))
    {b s : G} (hbK : b ∈ K) (hb : orderOf b = 3) (hsK : s ∈ K) {m : ℕ} (hs : s ^ 2 ^ m = 1)
    (hc : b * s = s * b) : s ∈ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := (kerIn (H ⊓ M) H).subgroupOf H with hN
  set π := QuotientGroup.mk' N with hπ
  have hmem : ∀ x : G, ∀ hx : x ∈ K, π ⟨x, hKH hx⟩ ∈ E2.star (H ⊓ M) H K := fun x hx =>
    ⟨⟨x, hKH hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  set b' : ↥(E2.star (H ⊓ M) H K) := ⟨π ⟨b, hKH hbK⟩, hmem b hbK⟩ with hb'
  set s' : ↥(E2.star (H ⊓ M) H K) := ⟨π ⟨s, hKH hsK⟩, hmem s hsK⟩ with hs'
  have hc' : b' * s' = s' * b' := by
    apply Subtype.ext
    show π ⟨b, hKH hbK⟩ * π ⟨s, hKH hsK⟩ = π ⟨s, hKH hsK⟩ * π ⟨b, hKH hbK⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hc
  have hs2 : s' ^ 2 ^ m = 1 := by
    apply Subtype.ext
    show π ⟨s, hKH hsK⟩ ^ 2 ^ m = 1
    rw [← map_pow]
    have : (⟨s, hKH hsK⟩ : ↥H) ^ 2 ^ m = 1 := Subtype.ext (by simpa using hs)
    rw [this, map_one]
  have hb3 : orderOf b' = 3 := by
    have hpow : b' ^ 3 = 1 := by
      apply Subtype.ext
      show π ⟨b, hKH hbK⟩ ^ 3 = 1
      rw [← map_pow]
      have : (⟨b, hKH hbK⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by
        simpa using (orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq hb)))
      rw [this, map_one]
    refine orderOf_eq_prime hpow fun h1 => ?_
    have h2 : π ⟨b, hKH hbK⟩ = 1 := congrArg Subtype.val h1
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
    obtain ⟨k, hk⟩ := hJ ⟨b, h2⟩
    have hk' : b ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hdvd : orderOf b ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    rw [hb] at hdvd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd)
    omega
  have hs1 := eq_one_of_commute_of_two hKL hb3 hs2 hc'
  have h1 : π ⟨s, hKH hsK⟩ = 1 := congrArg Subtype.val hs1
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  have hle : kerIn (H ⊓ M) H ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 (kerIn_le.trans inf_le_left) (le_normalizer_kerIn _ _) hJ
  exact hle h1

theorem mem_pCoreOf_sup_of_centralizes {H K T : Subgroup G} (hH : H = K ⊔ T)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hT2 : IsPGroup 2 T)
    (hKL : IsPSL 3 2 2 (O2Q K)) {v : G} (hvH : v ∈ H)
    (hv : ∀ k ∈ K, v * k * v⁻¹ * k⁻¹ ∈ pCoreOf 2 K) : v ∈ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := hH ▸ le_sup_left
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := by
    rw [hH]
    exact sup_le Subgroup.le_normalizer hTK
  have hHP : H ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    hHK.trans (normalizer_le_normalizer_pCoreOf 2 K)
  set C := centralizerMod (pCoreOf 2 K) H K with hC
  have hvC : v ∈ C := ⟨hvH, hHP hvH, hv⟩
  have hCH : C ≤ H := fun x hx => hx.1
  have hconj : ∀ h ∈ H, ∀ c ∈ C, h * c * h⁻¹ ∈ C := by
    intro h hh c hc
    refine ⟨H.mul_mem (H.mul_mem hh hc.1) (H.inv_mem hh),
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (hHP hh) hc.2.1) (Subgroup.inv_mem _ (hHP hh)),
      fun k hk => ?_⟩
    have hk' : h⁻¹ * k * h ∈ K := (Subgroup.mem_normalizer_iff''.mp (hHK hh) k).mp hk
    have h1 := (Subgroup.mem_normalizer_iff.mp (hHP hh) _).mp (hc.2.2 _ hk')
    have e : h * c * h⁻¹ * k * (h * c * h⁻¹)⁻¹ * k⁻¹ =
        h * (c * (h⁻¹ * k * h) * c⁻¹ * (h⁻¹ * k * h)⁻¹) * h⁻¹ := by group
    rw [e]
    exact h1
  have hHC : H ≤ Subgroup.normalizer (C : Set G) := fun h hh =>
    B6.mem_normalizer_of_forall_mem (fun c hc => hconj h hh c hc)
      (fun c hc => by simpa using hconj h⁻¹ (H.inv_mem hh) c hc)
  have hCK : ∀ c ∈ C, c ∈ K → c ∈ pCoreOf 2 K := fun c hc hcK =>
    mem_pCoreOf_of_centralizes hKL hcK hc.2.2
  have hC2 : IsPGroup 2 ↥C := by
    rintro ⟨c, hc⟩
    have hcH := hc.1
    have hmul := Subgroup.coe_mul_of_right_le_normalizer_left K T hTK
    have hc' : c ∈ ((K ⊔ T : Subgroup G) : Set G) := hH ▸ hcH
    rw [hmul] at hc'
    obtain ⟨k, hk, t, ht, rfl⟩ := hc'
    obtain ⟨m, hm⟩ := hT2 ⟨t, ht⟩
    have htm : t ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hKn : (K.subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hHK
    set ρ := QuotientGroup.mk' (K.subgroupOf H) with hρ
    have hkK : ρ ⟨k, hKH hk⟩ = 1 := by
      rw [hρ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hk
    have htH : t ∈ H := hH ▸ Subgroup.mem_sup_right ht
    have hpow : ρ (⟨k * t, hcH⟩ ^ 2 ^ m) = 1 := by
      have e : (⟨k * t, hcH⟩ : ↥H) = ⟨k, hKH hk⟩ * ⟨t, htH⟩ := rfl
      rw [map_pow, e, map_mul, hkK, one_mul, ← map_pow]
      have : (⟨t, htH⟩ : ↥H) ^ 2 ^ m = 1 := Subtype.ext (by simpa using htm)
      rw [this, map_one]
    rw [hρ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hpow
    have hpK : (k * t) ^ 2 ^ m ∈ K := by simpa using hpow
    have hpC : (k * t) ^ 2 ^ m ∈ C := C.pow_mem hc _
    obtain ⟨j, hj⟩ := (pCoreOf_isPGroup 2 K) ⟨_, hCK _ hpC hpK⟩
    refine ⟨m + j, Subtype.ext ?_⟩
    have hj' : ((k * t) ^ 2 ^ m) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    show (k * t) ^ 2 ^ (m + j) = 1
    rw [pow_add, pow_mul]
    exact hj'
  exact le_pCoreOf_of_le_normalizer 2 hCH hHC hC2 hvC


omit [Finite G] in
theorem relIndex_le_two_of_entry {V W : Subgroup G} {K : Type} [Field K] [Fintype K]
    (hK4 : Fintype.card K = 4) (e : ↥V ≃* H.Om4.VM K)
    (hW : ∀ v : ↥V, (Multiplicative.toAdd (e v)) 1 1 = 0 → (v : G) ∈ W) {v₀ : ↥V}
    (hv₀ : (v₀ : G) ∈ W) (hne : (Multiplicative.toAdd (e v₀)) 1 1 ≠ 0) :
    W.relIndex V ≤ 2 := by
  let φ : ↥V →* Multiplicative K :=
    { toFun := fun v => Multiplicative.ofAdd ((Multiplicative.toAdd (e v)) 1 1)
      map_one' := by simp
      map_mul' := fun x y => by simp }
  have hφ : ∀ v, φ v = Multiplicative.ofAdd ((Multiplicative.toAdd (e v)) 1 1) := fun _ => rfl
  have hsurj : Function.Surjective φ := by
    intro c
    refine ⟨e.symm (Multiplicative.ofAdd !![0, 0; 0, Multiplicative.toAdd c]), ?_⟩
    rw [hφ, MulEquiv.apply_symm_apply, toAdd_ofAdd]
    simp
  have hker : φ.ker ≤ W.subgroupOf V := by
    intro v hv
    rw [MonoidHom.mem_ker, hφ] at hv
    exact Subgroup.mem_subgroupOf.mpr (hW v (by simpa using hv))
  have h4 : φ.ker.index = 4 := by
    rw [Subgroup.index,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hsurj).toEquiv,
      Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card, hK4]
  have hmul := Subgroup.relIndex_mul_index hker
  rw [h4] at hmul
  have h1 : φ.ker.relIndex (W.subgroupOf V) ≠ 1 := by
    rw [Ne, Subgroup.relIndex_eq_one]
    intro hle
    have h := hle (Subgroup.mem_subgroupOf.mpr hv₀)
    rw [MonoidHom.mem_ker, hφ] at h
    exact hne (by simpa using h)
  have h0 : φ.ker.relIndex (W.subgroupOf V) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hmul
    norm_num at hmul
  show (W.subgroupOf V).index ≤ 2
  by_contra hlt
  push Not at hlt
  have h6 : 2 * 3 ≤ φ.ker.relIndex (W.subgroupOf V) * (W.subgroupOf V).index :=
    Nat.mul_le_mul (by omega) hlt
  rw [hmul] at h6
  norm_num at h6

theorem commutator_mem_of_fix {K P : Subgroup G} (hKL : IsPSL 3 2 2 (O2Q K))
    (hP : IsSylowTwoOf P K) {v : G} (hvN : v ∈ Subgroup.normalizer (K : Set G))
    (hv2 : v * v = 1) (hvP : ∀ t ∈ P, v * t * v⁻¹ * t⁻¹ ∈ pCoreOf 2 K) {b : G} (hbK : b ∈ K)
    (hb : orderOf b = 3) (hvb : v * b * v⁻¹ * b⁻¹ ∈ pCoreOf 2 K) :
    ∀ k ∈ K, v * k * v⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ : MulAut ↥K := Subgroup.normalizerMonoidHom K ⟨v, hvN⟩ with hφ
  have hφk : ∀ k : ↥K, ((φ k : ↥K) : G) = v * k * v⁻¹ := fun k => rfl
  set α : MulAut (O2Q K) := QuotientGroup.congr (CFSG.pCore 2 ↥K) (CFSG.pCore 2 ↥K) φ
    (Subgroup.characteristic_iff_map_eq.mp inferInstance φ) with hα
  have hαk : ∀ k : ↥K, α (k : O2Q K) = ((φ k : ↥K) : O2Q K) := fun k => rfl
  have hfix : ∀ k : ↥K, α (k : O2Q K) = k ↔ v * k * v⁻¹ * (k : G)⁻¹ ∈ pCoreOf 2 K := by
    intro k
    rw [hαk, QuotientGroup.eq_iff_div_mem, ← mem_pCoreOf_iff_pCore, div_eq_mul_inv,
      Subgroup.coe_mul, Subgroup.coe_inv, hφk]
  have hα2 : α * α = 1 := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H k =>
      rw [MulAut.mul_apply, hαk, hαk, MulAut.one_apply]
      congr 1
      apply Subtype.ext
      rw [hφk, hφk]
      calc v * (v * k * v⁻¹) * v⁻¹ = (v * v) * k * (v * v)⁻¹ := by group
        _ = k := by rw [hv2]; group
  set Pb : Subgroup (O2Q K) := (P.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))
    with hPb
  have hP2 : IsPGroup 2 ↥(P.subgroupOf K) :=
    hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP.1).symm
  have h64 : Nat.card Pb = 64 := by
    refine card_eq_of_isPSL hKL (hP2.map _) fun h2 => hP.2.2 ?_
    exact h2.trans (Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _))
  have hαP : ∀ x ∈ Pb, α x = x := by
    rintro _ ⟨k, hk, rfl⟩
    exact (hfix k).mpr (hvP k (Subgroup.mem_subgroupOf.mp hk))
  have hb3 : orderOf ((⟨b, hbK⟩ : ↥K) : O2Q K) = 3 := by
    have hpow : ((⟨b, hbK⟩ : ↥K) : O2Q K) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow]
      have : (⟨b, hbK⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by
        simpa using (orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq hb)))
      rw [this, QuotientGroup.mk_one]
    refine orderOf_eq_prime hpow fun h1 => ?_
    rw [QuotientGroup.eq_one_iff, ← mem_pCoreOf_iff_pCore] at h1
    obtain ⟨j, hj⟩ := (pCoreOf_isPGroup 2 K) ⟨b, h1⟩
    have hj' : b ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hdvd : orderOf b ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj'
    rw [hb] at hdvd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd)
    omega
  have hα1 := eq_one_of_fix hKL hα2 h64 hαP hb3 ((hfix ⟨b, hbK⟩).mpr hvb)
  intro k hk
  refine (hfix ⟨k, hk⟩).mp ?_
  rw [hα1, MulAut.one_apply]

end L34

namespace Setup

open CFSG.Quasithin.H Matrix

namespace IsCoord

variable {S : Setup T L I n} {K : Type} [Field K] [Fintype K] [CharP K 2]
  {e : ↥(fsuV T I) ≃* Om4.VM K}
  {ψ : ↥(fsuL0 T L) →* Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K}
  (hc : S.IsCoord e ψ)
include hc

theorem mem_of_entry {W : Subgroup G}
    (hW : T ⊓ fsuL0 T L ≤ Subgroup.normalizer (W : Set G)) {v₀ : ↥(fsuV T I)}
    (hv₀ : (v₀ : G) ∈ W) (hne : (Multiplicative.toAdd (e v₀)) 1 1 ≠ 0) (v : ↥(fsuV T I))
    (hv : (Multiplicative.toAdd (e v)) 1 1 = 0) : (v : G) ∈ W := by
  set Ws : Set (Matrix (Fin 2) (Fin 2) K) :=
    {Z | ((e.symm (Multiplicative.ofAdd Z) : ↥(fsuV T I)) : G) ∈ W} with hWs
  have hadd : ∀ X ∈ Ws, ∀ Y ∈ Ws, X + Y ∈ Ws := by
    intro X hX Y hY
    show ((e.symm (Multiplicative.ofAdd (X + Y)) : ↥(fsuV T I)) : G) ∈ W
    rw [ofAdd_add, map_mul, Subgroup.coe_mul]
    exact W.mul_mem hX hY
  have hρ : ∀ p q : K, ∀ X ∈ Ws, !![1, p; 0, 1] * X * (!![1, q; 0, 1])ᵀ ∈ Ws := by
    intro p q X hX
    obtain ⟨x, hxX, hxW⟩ : ∃ x : ↥(fsuV T I), e x = Multiplicative.ofAdd X ∧ (x : G) ∈ W :=
      ⟨_, e.apply_symm_apply _, hX⟩
    obtain ⟨u, hu, hψu⟩ : (uHom K (Multiplicative.ofAdd p), uHom K (Multiplicative.ofAdd q)) ∈
        ((T ⊓ fsuL0 T L).subgroupOf (fsuL0 T L)).map ψ := by
      rw [hc.sylow]
      exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
    have huT : (u : G) ∈ T ⊓ fsuL0 T L := Subgroup.mem_subgroupOf.mp hu
    have h1 := bar_apply e (Subgroup.inclusion S.L0_le_normalizer_V u) x
    rw [hc.bar_L0, hψu, hxX] at h1
    have h2 : Multiplicative.ofAdd (!![1, p; 0, 1] * X * (!![1, q; 0, 1])ᵀ) =
        Om4.rho (uHom K (Multiplicative.ofAdd p), uHom K (Multiplicative.ofAdd q))
          (Multiplicative.ofAdd X) := rfl
    show ((e.symm (Multiplicative.ofAdd (!![1, p; 0, 1] * X * (!![1, q; 0, 1])ᵀ)) :
      ↥(fsuV T I)) : G) ∈ W
    rw [h2, h1, MulEquiv.symm_apply_apply]
    exact (Subgroup.mem_normalizer_iff.mp (hW huT) x).mp hxW
  have hY : Multiplicative.toAdd (e v₀) ∈ Ws := by
    show ((e.symm (Multiplicative.ofAdd (Multiplicative.toAdd (e v₀))) : ↥(fsuV T I)) : G) ∈ W
    rw [ofAdd_toAdd, MulEquiv.symm_apply_apply]
    exact hv₀
  have h := Om4Pt.mem_of_span hadd hρ hY hne (Multiplicative.toAdd (e v)) hv
  have h' : ((e.symm (Multiplicative.ofAdd (Multiplicative.toAdd (e v))) : ↥(fsuV T I)) : G) ∈
      W := h
  rwa [ofAdd_toAdd, MulEquiv.symm_apply_apply] at h'

end IsCoord

variable (S : Setup T L I n)
include S

theorem le_pCoreOf_of_not_stab (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat)
    (h2 : n = 2) {H K B D : Subgroup G} (hH : IsHStar T (fsuM T L) H) (hHK : H = K ⊔ T)
    (hKc : K ∈ cComp H) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hJ : IsPGroup 2 (kerIn (H ⊓ fsuM T L) H))
    (hKL : IsPSL 3 2 2 ↥(E2.star (H ⊓ fsuM T L) H K)) (hBK : B ≤ K) (hB3 : Nat.card B = 3)
    (hBTK : B ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G))
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)))
    (hBD : B = D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G))
    (hns : ¬ T ⊓ K ≤ Subgroup.normalizer (L : Set G)) : fsuV T I ≤ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, _, _, e, ψ, hc, hdiag⟩ := S.exists_isCoord_diag h37c h38c hD
  have hF4 : Fintype.card F = 4 := by rw [hc.card, h2]; norm_num
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hTH : T ≤ H := hH.1.1
  have hT2 : IsPGroup 2 T := S.hyp.fsu.sylow.1
  have hKL' : IsPSL 3 2 2 (O2Q K) := L34.isPSL_of_star hKH hJ hKL
  have hHKn : H ≤ Subgroup.normalizer (K : Set G) := by
    rw [hHK]
    exact sup_le Subgroup.le_normalizer hTK
  have hDL : D ≤ fsuL0 T L := hD.1.trans inf_le_left
  have hBD' : B ≤ D := hBD ▸ inf_le_left
  have hBL : B ≤ fsuL0 T L := hBD'.trans hDL
  obtain ⟨b, hbB, hb1⟩ : ∃ b ∈ B, b ≠ 1 := by
    by_contra hall
    push Not at hall
    have : B = ⊥ := eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (hall x hx)
    rw [this, Subgroup.card_bot] at hB3
    norm_num at hB3
  have hbL0 : b ∈ fsuL0 T L := hDL (hBD' hbB)
  obtain ⟨a, a', hψb⟩ := IsCoord.exists_diag_of_mem hdiag (hBD' hbB) hbL0
  have hbV1 : b ∈ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) := by
    have h := hbB
    rw [hBD] at h
    exact h.2
  have haa' : a * a' = 1 := (hc.mem_centralizer_V1_iff_diag ⟨b, hbL0⟩ a a' hψb).mp hbV1
  have ha' : a' = a⁻¹ := eq_inv_of_mul_eq_one_right haa'
  rw [ha'] at hψb
  have ha1 : a ≠ 1 := by
    rintro rfl
    apply hb1
    have hd1 : diagOf (1 : Fˣ) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    have hψ1 : ψ ⟨b, hbL0⟩ = 1 := by
      rw [hψb, inv_one, hd1, Prod.mk_one_one]
    have hodd : Odd (orderOf b) := hD.2.1.of_dvd_nat (D.orderOf_dvd_natCard (hBD' hbB))
    exact hc.eq_one_of_odd h37c h38c ⟨b, hbL0⟩ hodd hψ1
  have hb3 : orderOf b = 3 := by
    have hdvd : orderOf b ∣ 3 := by
      rw [← hB3]
      exact B.orderOf_dvd_natCard hbB
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hb1
    · exact h
  have hTL0 : T ⊓ fsuL0 T L ≤ Subgroup.normalizer (L : Set G) := by
    rintro x ⟨-, hxL0⟩
    have hform : bar e ⟨x, S.hMN (Setup.L0_le_fsuM hxL0)⟩ =
        Om4.lr (Matrix.SpecialLinearGroup.toGL (ψ ⟨x, hxL0⟩).1)
          (Matrix.SpecialLinearGroup.toGL (ψ ⟨x, hxL0⟩).2) * Om4.frM 1 := by
      rw [Om4.frM_one, mul_one, show (⟨x, S.hMN (Setup.L0_le_fsuM hxL0)⟩ :
        ↥(Subgroup.normalizer (fsuV T I : Set G))) =
        Subgroup.inclusion S.L0_le_normalizer_V ⟨x, hxL0⟩ from rfl, hc.bar_L0, Om4.rho_apply]
    exact hc.mem_normalizer_L_of_isNS h37 h38 h37c h38c (Setup.L0_le_fsuM hxL0) hform
  obtain ⟨s, ⟨hsTK, hsC⟩, hsN⟩ : ∃ s ∈ (T ⊓ K) ⊓ Subgroup.centralizer (B : Set G),
      s ∉ Subgroup.normalizer (L : Set G) := by
    by_contra hall
    push Not at hall
    apply hns
    have hcomm : ⁅T ⊓ K, B⁆ ≤ T ⊓ fsuL0 T L := by
      rw [Subgroup.commutator_le]
      intro y hy c hc'
      refine ⟨?_, ?_⟩
      · have h1 : c * y⁻¹ * c⁻¹ ∈ T ⊓ K :=
          (Subgroup.mem_normalizer_iff.mp (hBTK hc') _).mp ((T ⊓ K).inv_mem hy)
        have h3 : y * c * y⁻¹ * c⁻¹ = y * (c * y⁻¹ * c⁻¹) := by group
        rw [commutatorElement_def, h3]
        exact T.mul_mem hy.1 h1.1
      · have h1 : y * c * y⁻¹ ∈ fsuL0 T L :=
          (Subgroup.mem_normalizer_iff.mp (Setup.T_le_normalizer_L0 hy.1) c).mp (hBL hc')
        rw [commutatorElement_def]
        exact (fsuL0 T L).mul_mem h1 ((fsuL0 T L).inv_mem (hBL hc'))
    have hY2 : IsPGroup 2 ↥(T ⊓ K) := hT2.to_le inf_le_left
    have hcop : Nat.Coprime (Nat.card B) (Nat.card ↥(T ⊓ K)) := by
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hY2
      rw [hB3, hm]
      exact Nat.Coprime.pow_right _ (by norm_num)
    have hdec := CFSG.LocalAnalysis.EvenBN.TwoF4.inf_centralizer_sup_commutator_eq hBTK
      (by have := hY2.isNilpotent; infer_instance) hcop
    rw [← hdec]
    exact sup_le (fun x hx => hall x hx) (hcomm.trans hTL0)
  have hsT : s ∈ T := hsTK.1
  have hsM : s ∈ fsuM T L := Setup.T_le_fsuM hsT
  obtain ⟨m, hm⟩ := hT2 ⟨s, hsT⟩
  have hsm : s ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hbs : b * s = s * b := Subgroup.mem_centralizer_iff.mp hsC b hbB
  have hsO : s ∈ pCoreOf 2 H :=
    L34.mem_pCoreOf_of_commute hKH hJ hKL (hBK hbB) hb3 hsTK.2 hsm hbs
  obtain ⟨A, B', τ, hA, hB', hform⟩ := hc.exists_form_ut hsT
  rcases hform with hform | hform
  · exact absurd (hc.mem_normalizer_L_of_isNS h37 h38 h37c h38c hsM hform) hsN
  have hbar : bar e ⟨s, S.hMN hsM⟩ * bar e (Subgroup.inclusion S.L0_le_normalizer_V
      ⟨b, hbL0⟩) = bar e (Subgroup.inclusion S.L0_le_normalizer_V ⟨b, hbL0⟩) *
      bar e ⟨s, S.hMN hsM⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hbs.symm
  rw [hc.bar_L0, hψb, hform] at hbar
  obtain ⟨X, hX⟩ := Om4Pt.exists_ne_of_commute_swap hF4 hA hB' ha1 hbar
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ↥(fsuV T I), e x₀ = Multiplicative.ofAdd X :=
    ⟨_, e.apply_symm_apply _⟩
  have hyV : s * (x₀ : G) * s⁻¹ ∈ fsuV T I :=
    (Subgroup.mem_normalizer_iff.mp (S.hMN hsM) x₀).mp x₀.2
  have hey : e ⟨s * (x₀ : G) * s⁻¹, hyV⟩ = bar e ⟨s, S.hMN hsM⟩ (e x₀) :=
    (bar_apply e ⟨s, S.hMN hsM⟩ x₀).symm
  rw [hform, hx₀] at hey
  have hv₀V : s * (x₀ : G) * s⁻¹ * (x₀ : G)⁻¹ ∈ fsuV T I :=
    (fsuV T I).mul_mem hyV ((fsuV T I).inv_mem x₀.2)
  have hne : (Multiplicative.toAdd (e ⟨_, hv₀V⟩)) 1 1 ≠ 0 := by
    have e1 : (⟨_, hv₀V⟩ : ↥(fsuV T I)) = ⟨s * (x₀ : G) * s⁻¹, hyV⟩ * x₀⁻¹ := Subtype.ext rfl
    rw [e1, map_mul, map_inv, hey, hx₀, toAdd_mul, toAdd_inv, toAdd_ofAdd, Matrix.add_apply,
      Matrix.neg_apply, ← sub_eq_add_neg, sub_ne_zero]
    exact hX
  have hv₀W : ((⟨_, hv₀V⟩ : ↥(fsuV T I)) : G) ∈ fsuV T I ⊓ pCoreOf 2 H := by
    refine ⟨hv₀V, ?_⟩
    have hx₀H : (x₀ : G) ∈ H := hTH (S.fsuV_le_T x₀.2)
    have h3 : (x₀ : G) * s⁻¹ * (x₀ : G)⁻¹ ∈ pCoreOf 2 H :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hx₀H) s⁻¹).mp
        ((pCoreOf 2 H).inv_mem hsO)
    have e1 : s * (x₀ : G) * s⁻¹ * (x₀ : G)⁻¹ = s * ((x₀ : G) * s⁻¹ * (x₀ : G)⁻¹) := by group
    show s * (x₀ : G) * s⁻¹ * (x₀ : G)⁻¹ ∈ pCoreOf 2 H
    rw [e1]
    exact (pCoreOf 2 H).mul_mem hsO h3
  have hTW : T ≤ Subgroup.normalizer ((fsuV T I ⊓ pCoreOf 2 H : Subgroup G) : Set G) :=
    fun t ht => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨S.T_le_normalizer_V ht, le_normalizer_pCoreOf 2 H (hTH ht)⟩
  have hall : ∀ v : ↥(fsuV T I), (Multiplicative.toAdd (e v)) 1 1 = 0 →
      (v : G) ∈ fsuV T I ⊓ pCoreOf 2 H :=
    fun v hv => hc.mem_of_entry (fun t ht => hTW ht.1) hv₀W hne v hv
  have hidx : (fsuV T I ⊓ pCoreOf 2 H).relIndex (fsuV T I) ≤ 2 :=
    L34.relIndex_le_two_of_entry hF4 e hall hv₀W hne
  have hOK : pCoreOf 2 H ⊓ K ≤ pCoreOf 2 K := F7.pCoreOf_inf_le hKH
  have hcommK : ∀ g ∈ K, g ∈ Subgroup.normalizer (fsuV T I : Set G) →
      ∀ v ∈ fsuV T I, v * g * v⁻¹ * g⁻¹ ∈ pCoreOf 2 K := by
    intro g hgK hgV v hv
    have hgW : g ∈ Subgroup.normalizer ((fsuV T I ⊓ pCoreOf 2 H : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hgV, le_normalizer_pCoreOf 2 H (hKH hgK)⟩
    have h1 := L34.commutator_mem_of_relIndex_le_two hidx hgV hgW hv
    have e1 : v * g * v⁻¹ * g⁻¹ = (g * v * g⁻¹ * v⁻¹)⁻¹ := by group
    have hvK : v ∈ Subgroup.normalizer (K : Set G) := hTK (S.fsuV_le_T hv)
    refine hOK ⟨?_, K.mul_mem ((Subgroup.mem_normalizer_iff.mp hvK g).mp hgK) (K.inv_mem hgK)⟩
    rw [e1]
    exact ((fsuV T I ⊓ pCoreOf 2 H).inv_mem h1).2
  have hTHs : IsSylowTwoOf T H :=
    CFSG.Quasithin.isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow hTH
  have hP : IsSylowTwoOf (T ⊓ K) K := A4.isSylowTwoOf_inf_normal hTHs hKH hHKn
  intro v hv
  have hvK : v ∈ Subgroup.normalizer (K : Set G) := hTK (S.fsuV_le_T hv)
  have hv2 : v * v = 1 := by
    rw [← sq]
    exact S.hV.2 v hv
  refine L34.mem_pCoreOf_sup_of_centralizes hHK hTK hT2 hKL' (hTH (S.fsuV_le_T hv)) ?_
  exact L34.commutator_mem_of_fix hKL' hP hvK hv2
    (fun t ht => hcommK t ht.2 (S.T_le_normalizer_V ht.1) v hv) (hBK hbB) hb3
    (hcommK b (hBK hbB) (S.L0_le_normalizer_V hbL0) v hv)

end Setup

end CFSG.Quasithin.H13.Ch9
