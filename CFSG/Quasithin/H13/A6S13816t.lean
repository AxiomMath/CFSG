module

public import CFSG.Quasithin.H13.A6S13816l
public import CFSG.Quasithin.EmptyFaithful.S1565L16

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

namespace L2Om

open Matrix

variable {K : Type} [Field K]

omit [Field K] in
theorem card_fun_two [Finite K] : Nat.card (Fin 2 → K) = Nat.card K ^ 2 := by
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin]

theorem card_ker_left_le [Finite K] {N : Matrix (Fin 2) (Fin 2) K} (hN : N ≠ 0) :
    Nat.card {M : Matrix (Fin 2) (Fin 2) K // N * M = 0} ≤ Nat.card K ^ 2 := by
  classical
  obtain ⟨i, j, hij⟩ : ∃ i j, N i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hN (Matrix.ext h)
  have hrow : ∀ M M' : {M : Matrix (Fin 2) (Fin 2) K // N * M = 0}, ∀ c,
      N i 0 * (M.1 0 c - M'.1 0 c) + N i 1 * (M.1 1 c - M'.1 1 c) = 0 := by
    intro M M' c
    have h1 := congrFun (congrFun M.2 i) c
    have h2 := congrFun (congrFun M'.2 i) c
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.zero_apply] at h1 h2
    linear_combination h1 - h2
  fin_cases j
  ·
    have hinj : Function.Injective
        (fun M : {M : Matrix (Fin 2) (Fin 2) K // N * M = 0} => M.1 1) := by
      intro M M' h
      have h' : ∀ c, M.1 1 c = M'.1 1 c := fun c => congrFun h c
      apply Subtype.ext
      ext r c
      fin_cases r
      · have := hrow M M' c
        rw [h' c, sub_self, mul_zero, add_zero] at this
        exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hij)
      · exact h' c
    exact (Nat.card_le_card_of_injective _ hinj).trans card_fun_two.le
  ·
    have hinj : Function.Injective
        (fun M : {M : Matrix (Fin 2) (Fin 2) K // N * M = 0} => M.1 0) := by
      intro M M' h
      have h' : ∀ c, M.1 0 c = M'.1 0 c := fun c => congrFun h c
      apply Subtype.ext
      ext r c
      fin_cases r
      · exact h' c
      · have := hrow M M' c
        rw [h' c, sub_self, mul_zero, zero_add] at this
        exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hij)
    exact (Nat.card_le_card_of_injective _ hinj).trans card_fun_two.le

theorem card_fix_left_le [Finite K] {A : Matrix (Fin 2) (Fin 2) K} (hA : A ≠ 1) :
    Nat.card {M : Matrix (Fin 2) (Fin 2) K // A * M = M} ≤ Nat.card K ^ 2 := by
  have e : {M : Matrix (Fin 2) (Fin 2) K // A * M = M} ≃
      {M : Matrix (Fin 2) (Fin 2) K // (A - 1) * M = 0} :=
    Equiv.subtypeEquivRight fun M => by rw [sub_mul, one_mul, sub_eq_zero]
  rw [Nat.card_congr e]
  exact card_ker_left_le (sub_ne_zero.mpr hA)

theorem card_fix_right_le [Finite K] {B : Matrix (Fin 2) (Fin 2) K} (hB : B ≠ 1) :
    Nat.card {M : Matrix (Fin 2) (Fin 2) K // M * B = M} ≤ Nat.card K ^ 2 := by
  have e : {M : Matrix (Fin 2) (Fin 2) K // M * B = M} ≃
      {M : Matrix (Fin 2) (Fin 2) K // Bᵀ * M = M} :=
    { toFun := fun M => ⟨M.1ᵀ, by rw [← Matrix.transpose_mul, M.2]⟩
      invFun := fun M => ⟨M.1ᵀ, by
        rw [show (M.1)ᵀ * B = (Bᵀ * M.1)ᵀ by rw [Matrix.transpose_mul, Matrix.transpose_transpose],
          M.2]⟩
      left_inv := fun M => Subtype.ext (Matrix.transpose_transpose _)
      right_inv := fun M => Subtype.ext (Matrix.transpose_transpose _) }
  rw [Nat.card_congr e]
  refine card_fix_left_le fun h => hB ?_
  rw [← Matrix.transpose_transpose B, h, Matrix.transpose_one]

@[expose] def um (a : K) : Matrix (Fin 2) (Fin 2) K := !![1, a; 0, 1]

theorem um_entry (a b : K) (M : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) :
    (um a * M * (um b)ᵀ) i j =
      (if i = 0 then M 0 j + a * M 1 j else M 1 j) +
        (if j = 0 then b * (if i = 0 then M 0 1 + a * M 1 1 else M 1 1) else 0) := by
  fin_cases i <;> fin_cases j <;>
    simp [um, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.vecMul,
      dotProduct] <;> ring

theorem card_fix_um_le [Finite K] {a b : K} (hab : a ≠ 0 ∨ b ≠ 0) :
    Nat.card {M : Matrix (Fin 2) (Fin 2) K // um a * M * (um b)ᵀ = M} ≤ Nat.card K ^ 2 := by
  classical
  have hent := um_entry a b
  have hform : ∀ M : Matrix (Fin 2) (Fin 2) K, um a * M * (um b)ᵀ = M ↔
      a * M 1 0 + b * M 0 1 + a * b * M 1 1 = 0 ∧ a * M 1 1 = 0 ∧ b * M 1 1 = 0 := by
    intro M
    constructor
    · intro h
      have h00 := congrFun (congrFun h 0) 0
      have h01 := congrFun (congrFun h 0) 1
      have h10 := congrFun (congrFun h 1) 0
      rw [hent] at h00 h01 h10
      simp only [ite_true, ite_false, one_ne_zero, Fin.isValue] at h00 h01 h10
      refine ⟨by linear_combination h00, by linear_combination h01, by linear_combination h10⟩
    · rintro ⟨h1, h2, h3⟩
      ext i j
      rw [hent]
      fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, ite_true, ite_false,
        one_ne_zero, Fin.isValue]
      · linear_combination h1
      · linear_combination h2
      · linear_combination h3
      · ring
  have hK2 : Nat.card (K × K) = Nat.card K ^ 2 := by rw [Nat.card_prod, sq]
  by_cases ha : a = 0
  · have hb : b ≠ 0 := hab.resolve_left (not_not.mpr ha)
    subst ha
    have hinj : Function.Injective
        (fun M : {M : Matrix (Fin 2) (Fin 2) K // um 0 * M * (um b)ᵀ = M} =>
          (M.1 0 0, M.1 1 0)) := by
      intro M M' h
      obtain ⟨h00, h10⟩ := Prod.ext_iff.mp h
      obtain ⟨-, -, h3⟩ := (hform M.1).mp M.2
      obtain ⟨h1, -, -⟩ := (hform M.1).mp M.2
      obtain ⟨h1', -, h3'⟩ := (hform M'.1).mp M'.2
      have m11 : M.1 1 1 = 0 := (mul_eq_zero.mp h3).resolve_left hb
      have m11' : M'.1 1 1 = 0 := (mul_eq_zero.mp h3').resolve_left hb
      rw [m11] at h1
      rw [m11'] at h1'
      have m01 : M.1 0 1 = 0 := (mul_eq_zero.mp (by linear_combination h1)).resolve_left hb
      have m01' : M'.1 0 1 = 0 := (mul_eq_zero.mp (by linear_combination h1')).resolve_left hb
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j
      · exact h00
      · simp only [Fin.zero_eta, Fin.mk_one]; rw [m01, m01']
      · exact h10
      · simp only [Fin.mk_one]; rw [m11, m11']
    exact (Nat.card_le_card_of_injective _ hinj).trans hK2.le
  · have hinj : Function.Injective
        (fun M : {M : Matrix (Fin 2) (Fin 2) K // um a * M * (um b)ᵀ = M} =>
          (M.1 0 0, M.1 0 1)) := by
      intro M M' h
      obtain ⟨h00, h01⟩ := Prod.ext_iff.mp h
      obtain ⟨h1, h2, -⟩ := (hform M.1).mp M.2
      obtain ⟨h1', h2', -⟩ := (hform M'.1).mp M'.2
      have m11 : M.1 1 1 = 0 := (mul_eq_zero.mp h2).resolve_left ha
      have m11' : M'.1 1 1 = 0 := (mul_eq_zero.mp h2').resolve_left ha
      have m10 : a * M.1 1 0 = a * M'.1 1 0 := by
        have h01'' : M.1 0 1 = M'.1 0 1 := h01
        linear_combination h1 - h1' + (-b) * h01'' - a * b * m11 + a * b * m11'
      have m10' : M.1 1 0 = M'.1 1 0 := mul_left_cancel₀ ha m10
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j
      · exact h00
      · exact h01
      · exact m10'
      · simp only [Fin.mk_one]; rw [m11, m11']
    exact (Nat.card_le_card_of_injective _ hinj).trans hK2.le

theorem quad_um {a₁ a₂ b₁ b₂ : K}
    (h : ∀ M : Matrix (Fin 2) (Fin 2) K, um a₁ * (um b₁ * M * (um b₂)ᵀ - M) * (um a₂)ᵀ -
      (um b₁ * M * (um b₂)ᵀ - M) = 0) : a₁ * b₂ + a₂ * b₁ = 0 := by
  set E : Matrix (Fin 2) (Fin 2) K := !![0, 0; 0, 1] with hE
  set Y := um b₁ * E * (um b₂)ᵀ - E with hY
  have hY00 : Y 0 0 = b₁ * b₂ := by
    rw [hY, Matrix.sub_apply, um_entry]; simp [hE]; ring
  have hY01 : Y 0 1 = b₁ := by rw [hY, Matrix.sub_apply, um_entry]; simp [hE]
  have hY10 : Y 1 0 = b₂ := by rw [hY, Matrix.sub_apply, um_entry]; simp [hE]
  have hY11 : Y 1 1 = 0 := by rw [hY, Matrix.sub_apply, um_entry]; simp [hE]
  have h1 := congrFun (congrFun (h E) 0) 0
  rw [← hY, Matrix.sub_apply, um_entry] at h1
  simp only [ite_true, Matrix.zero_apply] at h1
  rw [hY00, hY01, hY10, hY11] at h1
  linear_combination h1

theorem card_le_of_quad [Finite K] (A : Subgroup (Multiplicative (K × K)))
    (hA : ∀ a ∈ A, ∀ b ∈ A, (Multiplicative.toAdd a).1 * (Multiplicative.toAdd b).2 +
      (Multiplicative.toAdd a).2 * (Multiplicative.toAdd b).1 = 0) :
    Nat.card A ≤ Nat.card K := by
  classical
  by_cases hbot : A = ⊥
  · subst hbot
    rw [Subgroup.card_bot]
    exact Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
  · obtain ⟨⟨c, hcA⟩, hc1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.mp hbot)
    have hc0 : Multiplicative.toAdd c ≠ 0 := fun h =>
      hc1 (Subtype.ext (Multiplicative.toAdd.injective h))
    have hsub : ∀ a ∈ A, ∀ a' ∈ A, Multiplicative.toAdd (a / a') =
        Multiplicative.toAdd a - Multiplicative.toAdd a' := fun _ _ _ _ => rfl
    by_cases hc₁ : (Multiplicative.toAdd c).1 = 0
    · have hc₂ : (Multiplicative.toAdd c).2 ≠ 0 := fun h => hc0 (Prod.ext hc₁ h)
      refine Nat.card_le_card_of_injective
        (fun a : A => (Multiplicative.toAdd (a : Multiplicative (K × K))).2) fun a a' haa => ?_
      have hd := hA _ (A.div_mem a.2 a'.2) _ hcA
      rw [hsub _ a.2 _ a'.2] at hd
      simp only [Prod.fst_sub, Prod.snd_sub, hc₁, mul_zero, add_zero] at hd
      have h2 : (Multiplicative.toAdd (a : Multiplicative (K × K))).2 =
          (Multiplicative.toAdd (a' : Multiplicative (K × K))).2 := haa
      have h1 : (Multiplicative.toAdd (a : Multiplicative (K × K))).1 =
          (Multiplicative.toAdd (a' : Multiplicative (K × K))).1 :=
        sub_eq_zero.mp ((mul_eq_zero.mp hd).resolve_right hc₂)
      exact Subtype.ext (Multiplicative.toAdd.injective (Prod.ext h1 h2))
    · refine Nat.card_le_card_of_injective
        (fun a : A => (Multiplicative.toAdd (a : Multiplicative (K × K))).1) fun a a' haa => ?_
      have hd := hA _ (A.div_mem a.2 a'.2) _ hcA
      have h1 : (Multiplicative.toAdd (a : Multiplicative (K × K))).1 =
          (Multiplicative.toAdd (a' : Multiplicative (K × K))).1 := haa
      rw [hsub _ a.2 _ a'.2] at hd
      simp only [Prod.fst_sub, Prod.snd_sub, h1, sub_self, zero_mul, zero_add] at hd
      have h2 : (Multiplicative.toAdd (a : Multiplicative (K × K))).2 =
          (Multiplicative.toAdd (a' : Multiplicative (K × K))).2 :=
        sub_eq_zero.mp ((mul_eq_zero.mp hd).resolve_right hc₁)
      exact Subtype.ext (Multiplicative.toAdd.injective (Prod.ext h1 h2))

theorem tensorAct_mul (γ δ : TensorG2 K) (X : TensorE2 K) :
    tensorAct 2 K (γ * δ) X = tensorAct 2 K γ (tensorAct 2 K δ X) := by
  simp [tensorAct, Matrix.transpose_mul, mul_assoc]

theorem tensorAct_one (X : TensorE2 K) : tensorAct 2 K 1 X = X := by
  simp [tensorAct]

@[expose] noncomputable def xmS (a : K) : ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K) :=
  CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K (SBc5SL2.xm a)

theorem coe_xmS (a : K) :
    ((xmS a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = um a := rfl

theorem xmS_zero : xmS (0 : K) = 1 := by
  have h : SBc5SL2.xm (0 : K) = 1 :=
    Subtype.ext (by ext i j; rw [L2Borel.coe_xm']; fin_cases i <;> fin_cases j <;> simp)
  rw [xmS, h, map_one]

theorem exists_conj_xmS [Finite K] (hK : Nat.card K = 2 ^ 2) {A : Subgroup (TensorG2 K)}
    (hA : IsPGroup 2 A) :
    ∃ g : TensorG2 K, ∀ x ∈ A, ∃ a b : K, g * x * g⁻¹ = (xmS a, xmS b) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set e := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K with he
  have hU := SBc5SL2.isSylowTwoOf_Uplus (F := K) (m := 2) (by norm_num) hK
  have key : ∀ f : TensorG2 K →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K),
      ∃ g : SBc5SL2.SL2 K, ∀ x ∈ A, ∃ a : K, g * e.symm (f x) * g⁻¹ = SBc5SL2.xm a := by
    intro f
    have hP : IsPGroup 2 ((A.map f).map e.symm.toMonoidHom) := (hA.map f).map _
    obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
    obtain ⟨g, -, hg⟩ := B6.isSylowTwoOf_exists_conj (isSylowTwoOf_top_of_sylow Q) hU
    refine ⟨g, fun x hx => ?_⟩
    have hmem : e.symm (f x) ∈ (Q : Subgroup (SBc5SL2.SL2 K)) :=
      hQ ⟨f x, ⟨x, hx, rfl⟩, rfl⟩
    have h1 : g * e.symm (f x) * g⁻¹ ∈ SBc5SL2.Uplus K := by
      rw [hg, B6.mem_conjSub]
      simpa [mul_assoc] using hmem
    obtain ⟨a, ha⟩ := SBc5SL2.mem_Uplus_iff.mp h1
    exact ⟨a, ha⟩
  obtain ⟨g₁, hg₁⟩ := key (MonoidHom.fst _ _)
  obtain ⟨g₂, hg₂⟩ := key (MonoidHom.snd _ _)
  refine ⟨(e g₁, e g₂), fun x hx => ?_⟩
  obtain ⟨a, ha⟩ := hg₁ x hx
  obtain ⟨b, hb⟩ := hg₂ x hx
  refine ⟨a, b, Prod.ext ?_ ?_⟩
  · have := congrArg e ha
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, MonoidHom.coe_fst] at this
    simpa [xmS, he] using this
  · have := congrArg e hb
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, MonoidHom.coe_snd] at this
    simpa [xmS, he] using this

theorem tensorAct_mul_right (γ : TensorG2 K) (X Y : TensorE2 K) :
    tensorAct 2 K γ (X * Y) = tensorAct 2 K γ X * tensorAct 2 K γ Y := by
  simp [tensorAct, Matrix.mul_add, Matrix.add_mul]

theorem tensorAct_inv_right (γ : TensorG2 K) (X : TensorE2 K) :
    tensorAct 2 K γ X⁻¹ = (tensorAct 2 K γ X)⁻¹ := by
  simp [tensorAct]

theorem tensorAct_inv_act (g : TensorG2 K) (X : TensorE2 K) :
    tensorAct 2 K g⁻¹ (tensorAct 2 K g X) = X := by
  rw [← tensorAct_mul, inv_mul_cancel, tensorAct_one]

theorem tensorAct_act_inv (g : TensorG2 K) (X : TensorE2 K) :
    tensorAct 2 K g (tensorAct 2 K g⁻¹ X) = X := by
  rw [← tensorAct_mul, mul_inv_cancel, tensorAct_one]

@[expose] def tensorActEquiv (g : TensorG2 K) : TensorE2 K ≃ TensorE2 K where
  toFun := tensorAct 2 K g
  invFun := tensorAct 2 K g⁻¹
  left_inv := tensorAct_inv_act g
  right_inv := tensorAct_act_inv g

theorem card_fixT_conj (γ g : TensorG2 K) :
    Nat.card {X : TensorE2 K // tensorAct 2 K (g * γ * g⁻¹) X = X} =
      Nat.card {X : TensorE2 K // tensorAct 2 K γ X = X} := by
  refine Nat.card_congr ((tensorActEquiv g⁻¹).subtypeEquiv fun X => ?_)
  show tensorAct 2 K (g * γ * g⁻¹) X = X ↔ tensorAct 2 K γ (tensorAct 2 K g⁻¹ X) =
    tensorAct 2 K g⁻¹ X
  rw [tensorAct_mul, tensorAct_mul]
  constructor
  · intro h
    have := congrArg (tensorAct 2 K g⁻¹) h
    rwa [tensorAct_inv_act] at this
  · intro h
    rw [h, tensorAct_act_inv]

theorem card_fixT_le_of_sq [Finite K] (hK : Nat.card K = 2 ^ 2) {γ : TensorG2 K}
    (hγ2 : γ ^ 2 = 1) (hγ1 : γ ≠ 1) :
    Nat.card {X : TensorE2 K // tensorAct 2 K γ X = X} ≤ Nat.card K ^ 2 := by
  have hA : IsPGroup 2 (Subgroup.zpowers γ) := by
    rintro ⟨y, k, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hγ2,
      _root_.one_zpow]
  obtain ⟨g, hg⟩ := exists_conj_xmS hK hA
  obtain ⟨a, b, hab⟩ := hg γ (Subgroup.mem_zpowers γ)
  have hab0 : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨rfl, rfl⟩ := h
    apply hγ1
    rw [xmS_zero, Prod.mk_one_one] at hab
    have := congrArg (fun z => g⁻¹ * z * g) hab
    simpa [mul_assoc] using this
  rw [← card_fixT_conj γ g, hab]
  have e : {X : TensorE2 K // tensorAct 2 K (xmS a, xmS b) X = X} ≃
      {M : Matrix (Fin 2) (Fin 2) K // um a * M * (um b)ᵀ = M} :=
    Multiplicative.toAdd.subtypeEquiv fun X => by
      show Multiplicative.ofAdd _ = X ↔ _
      rw [← Multiplicative.toAdd.injective.eq_iff]
      rfl
  rw [Nat.card_congr e]
  exact card_fix_um_le hab0

theorem xmS_add (a b : K) : xmS (a + b) = xmS a * xmS b := by
  rw [xmS, ← SBc5SL2.xm_mul, map_mul]
  rfl

@[expose] noncomputable def iota : Multiplicative (K × K) →* TensorG2 K where
  toFun p := (xmS (Multiplicative.toAdd p).1, xmS (Multiplicative.toAdd p).2)
  map_one' := by simp [xmS_zero]
  map_mul' p q := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, xmS_add, Prod.mk_mul_mk]

theorem iota_injective : Function.Injective (iota : Multiplicative (K × K) →* TensorG2 K) := by
  intro p q h
  have h1 := congrArg (fun γ : TensorG2 K =>
    (((γ.1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1,
      ((γ.2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1)) h
  simp only [iota, MonoidHom.coe_mk, OneHom.coe_mk, coe_xmS, um] at h1
  apply Multiplicative.toAdd.injective
  simpa using h1

theorem card_le_of_quadT [Finite K] (hK : Nat.card K = 2 ^ 2) {A : Subgroup (TensorG2 K)}
    (hA2 : ∀ γ ∈ A, γ ^ 2 = 1)
    (hq : ∀ γ ∈ A, ∀ δ ∈ A, ∀ X : TensorE2 K,
      tensorAct 2 K γ (tensorAct 2 K δ X * X⁻¹) = tensorAct 2 K δ X * X⁻¹) :
    Nat.card A ≤ Nat.card K := by
  have hP : IsPGroup 2 A := fun γ => ⟨1, Subtype.ext (by simpa using hA2 γ γ.2)⟩
  obtain ⟨g, hg⟩ := exists_conj_xmS hK hP
  set S : Subgroup (Multiplicative (K × K)) := (A.map (MulAut.conj g).toMonoidHom).comap iota
    with hS
  have hle : A.map (MulAut.conj g).toMonoidHom ≤ iota.range := by
    rintro _ ⟨γ, hγ, rfl⟩
    obtain ⟨a, b, hab⟩ := hg γ hγ
    exact ⟨Multiplicative.ofAdd (a, b), by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hab]; rfl⟩
  have hSA : S.map iota = A.map (MulAut.conj g).toMonoidHom := by
    rw [hS, Subgroup.map_comap_eq, inf_eq_right.mpr hle]
  have hcard : Nat.card A = Nat.card S := by
    rw [← Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective, ← hSA, Subgroup.card_map_of_injective iota_injective]
  rw [hcard]
  refine card_le_of_quad S fun p hp q hq' => ?_
  obtain ⟨γ, hγ, hγp⟩ := hp
  obtain ⟨δ, hδ, hδq⟩ := hq'
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hγp hδq
  have hpq : ∀ X : TensorE2 K, tensorAct 2 K (iota p) (tensorAct 2 K (iota q) X * X⁻¹) =
      tensorAct 2 K (iota q) X * X⁻¹ := by
    intro X
    rw [← hγp, ← hδq]
    have hconj : ∀ (ε : TensorG2 K) (Z : TensorE2 K),
        tensorAct 2 K (g * ε * g⁻¹) (tensorAct 2 K g Z) = tensorAct 2 K g (tensorAct 2 K ε Z) :=
      fun ε Z => by rw [tensorAct_mul, tensorAct_mul, tensorAct_inv_act]
    set Y := tensorAct 2 K g⁻¹ X with hY
    have hX : X = tensorAct 2 K g Y := by rw [hY, tensorAct_act_inv]
    rw [hX]
    calc tensorAct 2 K (g * γ * g⁻¹) (tensorAct 2 K (g * δ * g⁻¹) (tensorAct 2 K g Y) *
          (tensorAct 2 K g Y)⁻¹)
        = tensorAct 2 K (g * γ * g⁻¹) (tensorAct 2 K g (tensorAct 2 K δ Y * Y⁻¹)) := by
          rw [hconj δ Y, ← tensorAct_inv_right g Y, ← tensorAct_mul_right g]
      _ = tensorAct 2 K g (tensorAct 2 K δ Y * Y⁻¹) := by rw [hconj γ, hq γ hγ δ hδ Y]
      _ = tensorAct 2 K (g * δ * g⁻¹) (tensorAct 2 K g Y) * (tensorAct 2 K g Y)⁻¹ := by
          rw [hconj δ Y, tensorAct_mul_right, tensorAct_inv_right]
  apply quad_um
  intro M
  have h1 := hpq (Multiplicative.ofAdd M)
  have h2 := congrArg Multiplicative.toAdd h1
  simp only [iota, MonoidHom.coe_mk, OneHom.coe_mk, tensorAct, coe_xmS, toAdd_mul, toAdd_inv,
    toAdd_ofAdd] at h2
  rw [sub_eq_zero]
  simpa only [sub_eq_add_neg] using h2

theorem coe_ne_one {g : ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K)} (hg : g ≠ 1) :
    ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ≠ 1 := fun h =>
  hg (Subtype.ext (Units.ext h))

theorem card_fixT_left_le [Finite K] {g : ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K)}
    (hg : g ≠ 1) :
    Nat.card {X : TensorE2 K // tensorAct 2 K (g, 1) X = X} ≤ Nat.card K ^ 2 := by
  have e : {X : TensorE2 K // tensorAct 2 K (g, 1) X = X} ≃
      {M : Matrix (Fin 2) (Fin 2) K // ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * M = M} :=
    Multiplicative.toAdd.subtypeEquiv fun X => by
      show Multiplicative.ofAdd _ = X ↔ _
      rw [← Multiplicative.toAdd.injective.eq_iff]
      simp
  rw [Nat.card_congr e]
  exact card_fix_left_le (coe_ne_one hg)

theorem card_fixT_right_le [Finite K] {h : ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K)}
    (hh : h ≠ 1) :
    Nat.card {X : TensorE2 K // tensorAct 2 K (1, h) X = X} ≤ Nat.card K ^ 2 := by
  have e : {X : TensorE2 K // tensorAct 2 K (1, h) X = X} ≃
      {M : Matrix (Fin 2) (Fin 2) K //
        M * ((h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ = M} :=
    Multiplicative.toAdd.subtypeEquiv fun X => by
      show Multiplicative.ofAdd _ = X ↔ _
      rw [← Multiplicative.toAdd.injective.eq_iff]
      simp
  rw [Nat.card_congr e]
  refine card_fix_right_le fun h1 => coe_ne_one hh ?_
  rw [← Matrix.transpose_transpose ((h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), h1,
    Matrix.transpose_one]

theorem card_tensorE2 [Finite K] : Nat.card (TensorE2 K) = Nat.card K ^ 4 := by
  have h1 : Nat.card (TensorE2 K) = Nat.card (Fin 2 → Fin 2 → K) := rfl
  rw [h1, Nat.card_fun, card_fun_two, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin,
    ← pow_mul]

section Module

variable {W : Type} [CommGroup W]

@[expose] def delta (σ : MulAut W) : W →* W where
  toFun w := σ w * w⁻¹
  map_one' := by simp
  map_mul' w w' := by
    rw [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _

theorem delta_apply (σ : MulAut W) (w : W) : delta σ w = σ w * w⁻¹ := rfl

theorem card_range_mul_card_fix [Finite W] (σ : MulAut W) :
    Nat.card (delta σ).range * Nat.card {w : W // σ w = w} = Nat.card W := by
  have hker : Nat.card (delta σ).ker = Nat.card {w : W // σ w = w} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun w => by
      rw [MonoidHom.mem_ker, delta_apply, mul_inv_eq_one])
  rw [← hker, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange (delta σ)).toEquiv]
  exact (Subgroup.card_eq_card_quotient_mul_card_subgroup _).symm

theorem card_range_delta_mul_le [Finite W] (σ τ : MulAut W) :
    Nat.card (delta (σ * τ)).range ≤ Nat.card (delta σ).range * Nat.card (delta τ).range := by
  classical
  have h : ∀ w, delta (σ * τ) w = σ (delta τ w) * delta σ w := fun w => by
    simp only [delta_apply, MulAut.mul_apply, map_mul, map_inv]
    group
  let f : (delta σ).range × (delta τ).range → W := fun p => σ (p.2 : W) * (p.1 : W)
  have hsub : ((delta (σ * τ)).range : Set W) ⊆ Set.range f := by
    rintro _ ⟨w, rfl⟩
    exact ⟨(⟨delta σ w, w, rfl⟩, ⟨delta τ w, w, rfl⟩), (h w).symm⟩
  calc Nat.card (delta (σ * τ)).range = Nat.card ((delta (σ * τ)).range : Set W) := rfl
    _ ≤ Nat.card (Set.range f) := Nat.card_mono (Set.toFinite _) hsub
    _ ≤ Nat.card ((delta σ).range × (delta τ).range) := Finite.card_range_le f
    _ = _ := Nat.card_prod _ _

theorem card_range_delta_inv [Finite W] (σ : MulAut W) :
    Nat.card (delta σ⁻¹).range = Nat.card (delta σ).range := by
  have h : ∀ w, delta σ⁻¹ (σ w) = (delta σ w)⁻¹ := fun w => by
    rw [delta_apply, delta_apply, MulAut.inv_apply_self, _root_.mul_inv_rev, inv_inv]
  have e : (delta σ⁻¹).range = (delta σ).range := by
    ext v
    constructor
    · rintro ⟨w, rfl⟩
      obtain ⟨w', rfl⟩ := σ.surjective w
      rw [h]
      exact Subgroup.inv_mem _ ⟨w', rfl⟩
    · rintro ⟨w, rfl⟩
      have := h w
      rw [← inv_inv (delta σ w), ← this]
      exact Subgroup.inv_mem _ ⟨σ w, rfl⟩
  rw [e]

theorem card_range_delta_conj [Finite W] (σ τ : MulAut W) :
    Nat.card (delta (τ * σ * τ⁻¹)).range = Nat.card (delta σ).range := by
  have h : ∀ w, delta (τ * σ * τ⁻¹) (τ w) = τ (delta σ w) := fun w => by
    simp only [delta_apply, MulAut.mul_apply, MulAut.inv_apply_self, map_mul, map_inv]
  have e : (delta (τ * σ * τ⁻¹)).range = (delta σ).range.map τ.toMonoidHom := by
    ext v
    constructor
    · rintro ⟨w, rfl⟩
      obtain ⟨w', rfl⟩ := τ.surjective w
      exact ⟨delta σ w', ⟨w', rfl⟩, (h w').symm⟩
    · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
      exact ⟨τ w, h w⟩
  rw [e, Subgroup.card_map_of_injective τ.injective]

end Module

section Data

variable {W : Type} [CommGroup W]

theorem exists_tensorData {Mp : Subgroup (MulAut W)} {n : ℕ} (h : Omega4PlusModule Mp n) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      ∃ (π : TensorG2 K →* ↥Mp) (β : W ≃* TensorE2 K),
        Function.Surjective π ∧ IsTensorData2 Mp π β := by
  obtain ⟨K, fK, finK, hK, π, hπ⟩ := h
  refine ⟨K, fK, finK, hK, π, ?_⟩
  obtain ⟨hs, -, -, -, -, -, -, β₀, hβs₀, hβk₀, hβe₀⟩ := hπ
  let β' : ↥(⊤ : Subgroup W) →* (↥(⊤ : Subgroup (TensorE2 K)) ⧸
      (⊥ : Subgroup (TensorE2 K)).subgroupOf ⊤) := β₀
  have hβs : Function.Surjective β' := hβs₀
  have hβk : ∀ u, β' u = 1 ↔ (u : W) ∈ (⊥ : Subgroup W) := hβk₀
  have hinj : Function.Injective β' := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.mp ((hβk u).mp hu))
  let e3 : ↥(⊤ : Subgroup W) ≃* (↥(⊤ : Subgroup (TensorE2 K)) ⧸
      (⊥ : Subgroup (TensorE2 K)).subgroupOf ⊤) := MulEquiv.ofBijective β' ⟨hinj, hβs⟩
  let β : W ≃* TensorE2 K :=
    (Subgroup.topEquiv (G := W)).symm.trans (e3.trans (B5.natQuotEquiv (TensorE2 K)))
  refine ⟨β, hs, fun γ w => ?_⟩
  let u₀ : ↥(⊤ : Subgroup W) := ⟨w, trivial⟩
  let m : ↥(⊤ : Subgroup (TensorE2 K)) := ⟨β w, trivial⟩
  have hm : β' u₀ = QuotientGroup.mk m := by
    apply (B5.natQuotEquiv (TensorE2 K)).injective
    exact (B5.natQuotEquiv_mk (TensorE2 K) (β w)).symm
  have h1 := hβe₀ γ u₀ m trivial trivial hm
  have h3 : β (((π γ : ↥Mp) : MulAut W) w) = B5.natQuotEquiv (TensorE2 K)
      (β' ⟨((π γ : ↥Mp) : MulAut W) w, trivial⟩) := rfl
  refine h3.trans ?_
  have h4 : β' ⟨((π γ : ↥Mp) : MulAut W) w, trivial⟩ = β₀ ⟨((π γ : ↥Mp) : MulAut W) (u₀ : W),
      trivial⟩ := rfl
  rw [h4, h1]
  exact B5.natQuotEquiv_mk (TensorE2 K) _

theorem card_fix_eq {K : Type} [Field K] {Mp : Subgroup (MulAut W)} {π : TensorG2 K →* ↥Mp}
    {β : W ≃* TensorE2 K} (hd : IsTensorData2 Mp π β) (γ : TensorG2 K) :
    Nat.card {w : W // ((π γ : ↥Mp) : MulAut W) w = w} =
      Nat.card {X : TensorE2 K // tensorAct 2 K γ X = X} := by
  refine Nat.card_congr (β.toEquiv.subtypeEquiv fun w => ?_)
  show _ ↔ tensorAct 2 K γ (β w) = β w
  rw [← hd γ w]
  exact β.injective.eq_iff.symm

end Data

section Model

variable {W : Type} [CommGroup W] {K : Type} [Field K]

theorem card_W [Finite K] (β : W ≃* TensorE2 K) : Nat.card W = Nat.card K ^ 4 :=
  (Nat.card_congr β.toEquiv).trans card_tensorE2

theorem le_card_range_of_fix [Finite K] (β : W ≃* TensorE2 K) {σ : MulAut W}
    (hfix : Nat.card {w : W // σ w = w} ≤ Nat.card K ^ 2) :
    Nat.card K ^ 2 ≤ Nat.card (delta σ).range := by
  have : Finite W := Finite.of_equiv _ β.toEquiv.symm
  have h1 := card_range_mul_card_fix σ
  rw [card_W β] at h1
  have hK : 0 < Nat.card K ^ 2 := pow_pos Nat.card_pos 2
  by_contra hlt
  push Not at hlt
  have h2 : Nat.card (delta σ).range * Nat.card {w : W // σ w = w} <
      Nat.card K ^ 2 * Nat.card K ^ 2 :=
    Nat.mul_lt_mul_of_lt_of_le hlt hfix hK
  rw [h1, ← pow_add] at h2
  exact lt_irrefl _ h2

variable [Finite K] [CharP K 2] {Mp : Subgroup (MulAut W)} {π : TensorG2 K →* ↥Mp}
  {β : W ≃* TensorE2 K}

theorem le_card_range_of_sq (hK : Nat.card K = 2 ^ 2) (hd : IsTensorData2 Mp π β)
    (hπs : Function.Surjective π) {σ : MulAut W} (hσ : σ ∈ Mp) (hσ2 : σ ^ 2 = 1)
    (hσ1 : σ ≠ 1) : Nat.card K ^ 2 ≤ Nat.card (delta σ).range := by
  obtain ⟨γ, hγ⟩ := hπs ⟨σ, hσ⟩
  have hσγ : ((π γ : ↥Mp) : MulAut W) = σ := congrArg Subtype.val hγ
  have hγ2 : γ ^ 2 = 1 := hd.injective (by
    rw [map_pow, map_one, hγ]
    exact Subtype.ext (by simpa using hσ2))
  have hγ1 : γ ≠ 1 := fun h => hσ1 (by rw [← hσγ, h, map_one]; rfl)
  refine le_card_range_of_fix β ?_
  rw [← hσγ, card_fix_eq hd γ]
  exact card_fixT_le_of_sq hK hγ2 hγ1

omit [CharP K 2] in
theorem le_card_range_of_factor (hd : IsTensorData2 Mp π β) {σ : MulAut W}
    (hσ : σ ∈ factorL2 Mp π ∨ σ ∈ factorR2 Mp π) (hσ1 : σ ≠ 1) :
    Nat.card K ^ 2 ≤ Nat.card (delta σ).range := by
  refine le_card_range_of_fix β ?_
  rcases hσ with hσ | hσ
  · obtain ⟨g, rfl⟩ := mem_factorL2.mp hσ
    have hg : g ≠ 1 := fun h => hσ1 (by rw [h, Prod.mk_one_one, map_one]; rfl)
    rw [card_fix_eq hd]
    exact card_fixT_left_le hg
  · obtain ⟨h, rfl⟩ := mem_factorR2.mp hσ
    have hh : h ≠ 1 := fun h' => hσ1 (by rw [h', Prod.mk_one_one, map_one]; rfl)
    rw [card_fix_eq hd]
    exact card_fixT_right_le hh

omit [CharP K 2] in
theorem exists_fpf (hK : Nat.card K = 2 ^ 2) (hd : IsTensorData2 Mp π β) :
    ∃ m ∈ Mp, ∀ w : W, m w = w → w = 1 := by
  classical
  have := Fintype.ofFinite K
  obtain ⟨c, hc⟩ : ∃ c : Kˣ, c ≠ 1 := by
    by_contra h
    push Not at h
    have h1 : Nat.card Kˣ = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => (h a).trans (h b).symm⟩, ⟨1⟩⟩
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK] at h1
    norm_num at h1
  set g := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K (SBc5SL2.dm c)
  refine ⟨((π (g, 1) : ↥Mp) : MulAut W), (π (g, 1)).2, fun w hw => ?_⟩
  have h1 : tensorAct 2 K (g, 1) (β w) = β w := by rw [← hd (g, 1) w, hw]
  have h2 := congrArg Multiplicative.toAdd h1
  simp only [tensorAct, toAdd_ofAdd] at h2
  have hg : ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![(c : K), 0; 0, ((c⁻¹ : Kˣ) : K)] :=
    rfl
  have h1' : ((((1 : ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K)) : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K))ᵀ = 1 := by simp
  rw [hg, h1', Matrix.mul_one] at h2
  have hc' : (c : K) ≠ 1 := fun h => hc (Units.ext h)
  have hci : ((c⁻¹ : Kˣ) : K) ≠ 1 := fun h => hc (by
    have := congrArg Inv.inv (Units.ext (u := c⁻¹) (v := 1) (by simpa using h))
    simpa using this)
  have hM : Multiplicative.toAdd (β w) = 0 := by
    set M := Multiplicative.toAdd (β w) with hMdef
    ext i j
    have h3 := congrFun (congrFun h2 i) j
    fin_cases i
    · simp [Matrix.mul_apply, Fin.sum_univ_two] at h3
      exact (mul_eq_zero.mp (by linear_combination h3 : ((c : K) - 1) * M 0 j = 0)).resolve_left
        (sub_ne_zero.mpr hc')
    · simp [Matrix.mul_apply, Fin.sum_univ_two] at h3
      have hci' : (c : K)⁻¹ ≠ 1 := by rwa [← Units.val_inv_eq_inv_val]
      exact (mul_eq_zero.mp (by linear_combination h3 :
        ((c : K)⁻¹ - 1) * M 1 j = 0)).resolve_left (sub_ne_zero.mpr hci')
  have : β w = 1 := Multiplicative.toAdd.injective hM
  exact β.injective (by rw [this, map_one])

theorem card_le_of_quadratic (hK : Nat.card K = 2 ^ 2) (hd : IsTensorData2 Mp π β)
    (hπs : Function.Surjective π) {A : Subgroup (MulAut W)} (hAMp : A ≤ Mp)
    (hA2 : ∀ x ∈ A, x ^ 2 = 1) (hq : ∀ x ∈ A, ∀ y ∈ A, ∀ w : W, x (y w * w⁻¹) = y w * w⁻¹) :
    Nat.card A ≤ Nat.card K := by
  set Ã : Subgroup (TensorG2 K) := A.comap (Mp.subtype.comp π) with hÃ
  have hsurj : Function.Surjective (fun γ : Ã => (⟨((π γ : ↥Mp) : MulAut W), γ.2⟩ : A)) := by
    rintro ⟨x, hx⟩
    obtain ⟨γ, hγ⟩ := hπs ⟨x, hAMp hx⟩
    have hγx : ((π γ : ↥Mp) : MulAut W) = x := congrArg Subtype.val hγ
    exact ⟨⟨γ, show ((π γ : ↥Mp) : MulAut W) ∈ A by rw [hγx]; exact hx⟩, Subtype.ext hγx⟩
  refine (Nat.card_le_card_of_surjective _ hsurj).trans (card_le_of_quadT hK (fun γ hγ => ?_)
    (fun γ hγ δ hδ X => ?_))
  · refine hd.injective ?_
    rw [map_pow, map_one]
    exact Subtype.ext (by simpa using hA2 _ hγ)
  · obtain ⟨w, rfl⟩ := β.surjective X
    have h1 : ((π γ : ↥Mp) : MulAut W) (((π δ : ↥Mp) : MulAut W) w * w⁻¹) =
        ((π δ : ↥Mp) : MulAut W) w * w⁻¹ := hq _ hγ _ hδ w
    have h2 := congrArg β h1
    rw [hd γ, map_mul, map_inv, hd δ] at h2
    exact h2

omit [Field K] [Finite K] [CharP K 2] in
theorem eq_of_card_le_two {α : Type} [Finite α] (h : Nat.card α ≤ 2) {a b c : α} (hab : a ≠ b)
    (hca : c ≠ a) : c = b := by
  by_contra hcb
  have hinj : Function.Injective (![a, b, c] : Fin 3 → α) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have := Nat.card_le_card_of_injective _ hinj
  simp at this
  omega

theorem eq_one_of_card_range_le_two (hK : Nat.card K = 2 ^ 2) (hd : IsTensorData2 Mp π β)
    (hπs : Function.Surjective π) {K₁ K₂ : Subgroup (MulAut W)} (hMp : Mp = K₁ ⊔ K₂)
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) (hinf : K₁ ⊓ K₂ = ⊥)
    (hK₁ : ∀ x ∈ K₁, x ∈ factorL2 Mp π ∨ x ∈ factorR2 Mp π)
    (hK₂ : ∀ x ∈ K₂, x ∈ factorL2 Mp π ∨ x ∈ factorR2 Mp π)
    {u : MulAut W} (hu : u ∈ K₁) (hu1 : u ≠ 1) (hu2 : u ^ 2 = 1) {σ : MulAut W}
    (hσ : ((∀ x ∈ K₁, σ * x * σ⁻¹ ∈ K₁) ∧ ∀ x ∈ K₂, σ * x * σ⁻¹ ∈ K₂) ∨ σ * u * σ⁻¹ ∈ K₂)
    (hδ : Nat.card (delta σ).range ≤ 2) : σ = 1 := by
  have : Finite W := Finite.of_equiv _ β.toEquiv.symm
  have h16 : Nat.card K ^ 2 = 16 := by rw [hK]; norm_num
  have hc4 : ∀ x : MulAut W, Nat.card (delta (σ * x * σ⁻¹ * x⁻¹)).range ≤ 2 * 2 := by
    intro x
    have e : σ * x * σ⁻¹ * x⁻¹ = σ * (x * σ⁻¹ * x⁻¹) := by group
    rw [e]
    refine (card_range_delta_mul_le σ _).trans (Nat.mul_le_mul hδ ?_)
    rw [card_range_delta_conj, card_range_delta_inv]
    exact hδ
  rcases hσ with ⟨hσ₁, hσ₂⟩ | hσu
  ·
    have key : ∀ x, (σ * x * σ⁻¹ * x⁻¹ ∈ factorL2 Mp π ∨ σ * x * σ⁻¹ * x⁻¹ ∈ factorR2 Mp π) →
        σ * x = x * σ := by
      intro x hf
      by_contra hne
      have hc1 : σ * x * σ⁻¹ * x⁻¹ ≠ 1 := by
        intro h
        apply hne
        calc σ * x = (σ * x * σ⁻¹ * x⁻¹) * x * σ := by group
          _ = x * σ := by rw [h, one_mul]
      have h1 := le_card_range_of_factor hd hf hc1
      have h2 := hc4 x
      omega
    have hle : K₁ ⊔ K₂ ≤ Subgroup.centralizer {σ} := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (key x (hK₁ _ (K₁.mul_mem (hσ₁ x hx) (K₁.inv_mem hx)))).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (key x (hK₂ _ (K₂.mul_mem (hσ₂ x hx) (K₂.inv_mem hx)))).symm
    obtain ⟨m, hm, hmfix⟩ := exists_fpf hK hd
    have hmc : σ * m = m * σ :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hle (hMp ▸ hm))).symm
    by_contra hσ1
    obtain ⟨w, hw⟩ : ∃ w, σ w ≠ w := by
      by_contra h
      push Not at h
      exact hσ1 (MulEquiv.ext h)
    have hw₀ : delta σ w ≠ 1 := fun h => hw (mul_inv_eq_one.mp h)
    have hms : m (σ w) = σ (m w) := by
      have := congrArg (fun f : MulAut W => f w) hmc
      simp only [MulAut.mul_apply] at this
      exact this.symm
    have hmw : m (delta σ w) = delta σ (m w) := by
      rw [delta_apply, delta_apply, map_mul, map_inv, hms]
    have hmw1 : m (delta σ w) ≠ 1 := fun h => hw₀ (m.injective (by rw [h, map_one]))
    have heq : (⟨m (delta σ w), m w, hmw.symm⟩ : (delta σ).range) =
        ⟨delta σ w, w, rfl⟩ :=
      eq_of_card_le_two hδ (a := 1) (fun h => hw₀ (congrArg Subtype.val h).symm)
        (fun h => hmw1 (congrArg Subtype.val h))
    exact hw₀ (hmfix _ (congrArg Subtype.val heq))
  ·
    set c := σ * u * σ⁻¹ * u⁻¹ with hc
    have hcu : u⁻¹ * (σ * u * σ⁻¹) = (σ * u * σ⁻¹) * u⁻¹ := hcomm _ (K₁.inv_mem hu) _ hσu
    have hcMp : c ∈ Mp := by
      rw [hMp]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hσu)
        (Subgroup.mem_sup_left (K₁.inv_mem hu))
    have hc2 : c ^ 2 = 1 := by
      have hu2' : u * u = 1 := by rw [← pow_two]; exact hu2
      calc c ^ 2 = (σ * u * σ⁻¹) * (u⁻¹ * (σ * u * σ⁻¹)) * u⁻¹ := by rw [hc, pow_two]; group
        _ = (σ * u * σ⁻¹) * ((σ * u * σ⁻¹) * u⁻¹) * u⁻¹ := by rw [hcu]
        _ = σ * (u * u) * σ⁻¹ * (u * u)⁻¹ := by group
        _ = 1 := by rw [hu2']; group
    have hc1 : c ≠ 1 := by
      intro h
      have h1 : σ * u * σ⁻¹ = u := by
        calc σ * u * σ⁻¹ = c * u := by rw [hc]; group
          _ = u := by rw [h, one_mul]
      have : u ∈ K₁ ⊓ K₂ := ⟨hu, h1 ▸ hσu⟩
      rw [hinf] at this
      exact hu1 this
    have h1 := le_card_range_of_sq hK hd hπs hcMp hc2 hc1
    have h2 : Nat.card (delta c).range ≤ 2 * 2 := hc4 u
    omega

end Model

end L2Om

end CFSG.Quasithin.H13.A6
