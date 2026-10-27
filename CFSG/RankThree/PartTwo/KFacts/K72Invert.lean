module

public import CFSG.RankThree.PartTwo.KFacts.K72Centralizer
public import CFSG.RankThree.PartTwo.KFacts.K72LStar

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.GorensteinWalter

theorem exists_sq_sub_mul_add_sq_eq_neg_one {F : Type*} [Field F] [Finite F] (h3 : (3 : F) ≠ 0) :
    ∃ a b : F, a ^ 2 - a * b + b ^ 2 = -1 := by
  have : Fintype F := Fintype.ofFinite F
  by_cases h2 : ringChar F = 2
  ·
    refine ⟨1, 0, ?_⟩
    have h20 : (2 : F) = 0 := by
      have := (ringChar.spec F 2).mpr (by rw [h2])
      exact_mod_cast this
    have h : (-1 : F) = 1 := by
      rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, h20]
    rw [h]
    ring
  ·
    have hodd : Fintype.card F % 2 = 1 := by
      have h := (FiniteField.even_card_iff_char_two (F := F)).not.mp h2
      omega
    have h20 : (2 : F) ≠ 0 := Ring.two_ne_zero h2
    obtain ⟨u, v, huv⟩ := FiniteField.exists_root_sum_quadratic
      (f := Polynomial.C 1 * Polynomial.X ^ 2 + Polynomial.C 0 * Polynomial.X + Polynomial.C 0)
      (g := Polynomial.C 3 * Polynomial.X ^ 2 + Polynomial.C 0 * Polynomial.X + Polynomial.C 4)
      (Polynomial.degree_quadratic one_ne_zero) (Polynomial.degree_quadratic h3) hodd
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, one_mul, zero_mul, add_zero] at huv
    refine ⟨(u + v) / 2, v, ?_⟩
    field_simp
    linear_combination huv

theorem companion_conj (F : Type*) [Field F] (a b : F) :
    !![b, a - b; a, -b] * !![(0 : F), -1; 1, -1] =
      !![(0 : F), -1; 1, -1] * !![(0 : F), -1; 1, -1] * !![b, a - b; a, -b] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem exists_mul_eq_mul_mul_of_cube {F : Type*} [Field F] [Finite F] (h3 : (3 : F) ≠ 0)
    {D : Matrix (Fin 2) (Fin 2) F} (hdet : D.det = 1) (hD3 : D * D * D = 1) (hD1 : D ≠ 1) :
    ∃ Y : Matrix (Fin 2) (Fin 2) F, Y.det = 1 ∧ Y * D = D * D * Y := by
  obtain ⟨P, Q, hPQ, hQP, hDP⟩ :=
    Sec3.exists_conj_companion h3 hdet (trace_eq_neg_one_of_cube hdet hD3 hD1)
  obtain ⟨a, b, hab⟩ := exists_sq_sub_mul_add_sq_eq_neg_one h3
  set C : Matrix (Fin 2) (Fin 2) F := !![0, -1; 1, -1] with hC
  set Y₀ : Matrix (Fin 2) (Fin 2) F := !![b, a - b; a, -b] with hY₀
  have hY₀det : Y₀.det = 1 := by
    rw [hY₀, Matrix.det_fin_two_of]
    linear_combination -hab
  have hD : D = P * C * Q := by
    calc D = D * (P * Q) := by rw [hPQ, mul_one]
      _ = P * C * Q := by rw [← mul_assoc, hDP]
  refine ⟨P * Y₀ * Q, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_mul, hY₀det, mul_one, ← Matrix.det_mul, hPQ, Matrix.det_one]
  · have hQD : Q * D = C * Q := by
      calc Q * D = Q * (P * C * Q) := by rw [← hD]
        _ = (Q * P) * C * Q := by simp only [Matrix.mul_assoc]
        _ = C * Q := by rw [hQP, Matrix.one_mul]
    have hY₀C : Y₀ * C = C * C * Y₀ := companion_conj F a b
    calc P * Y₀ * Q * D = P * (Y₀ * (Q * D)) := by simp only [Matrix.mul_assoc]
      _ = P * (Y₀ * C) * Q := by rw [hQD]; simp only [Matrix.mul_assoc]
      _ = P * (C * C * Y₀) * Q := by rw [hY₀C]
      _ = (P * C * Q) * (P * C * Q) * (P * Y₀ * Q) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Q P, hQP, Matrix.one_mul, ← Matrix.mul_assoc Q P, hQP,
          Matrix.one_mul]
      _ = D * D * (P * Y₀ * Q) := by rw [← hD]

theorem exists_mul_mul_inv_eq_inv_psl2 {F : Type*} [Field F] [Finite F] (h3 : (3 : F) ≠ 0)
    {d : PSL2 F} (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) : ∃ y : PSL2 F, y * d * y⁻¹ = d⁻¹ := by
  obtain ⟨Y, rfl⟩ := QuotientGroup.mk_surjective d
  have hY3 : Y ^ 3 ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [← QuotientGroup.eq_one_iff]
    exact hd3
  obtain ⟨r, hr2, hrY⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hY3
  rw [Fintype.card_fin] at hr2
  have hY6 : Y ^ 6 = 1 := by
    rw [show (6 : ℕ) = 3 + 3 from rfl, pow_add]
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, ← hrY, Matrix.SpecialLinearGroup.coe_one,
      Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, ← pow_two, hr2, Matrix.diagonal_one]
  set D := Y ^ 4 with hD
  have hD3 : D ^ 3 = 1 := by
    rw [hD, ← pow_mul, show 4 * 3 = 6 * 2 from rfl, pow_mul, hY6, one_pow]
  have hDd : (QuotientGroup.mk D : PSL2 F) = QuotientGroup.mk Y := by
    rw [hD, QuotientGroup.mk_pow, show 4 = 3 + 1 from rfl, pow_succ, hd3, one_mul]
  have hD1 : D ≠ 1 := by
    intro h1
    apply hd1
    rw [← hDd, h1, QuotientGroup.mk_one]
  have hD3m : (D : Matrix (Fin 2) (Fin 2) F) * D * D = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, ← pow_two,
      ← pow_succ, hD3, Matrix.SpecialLinearGroup.coe_one]
  have hD1m : (D : Matrix (Fin 2) (Fin 2) F) ≠ 1 := fun h =>
    hD1 (Matrix.SpecialLinearGroup.ext _ _ fun i j => by
      rw [h, Matrix.SpecialLinearGroup.coe_one])
  obtain ⟨Z, hZdet, hZD⟩ :=
    exists_mul_eq_mul_mul_of_cube h3 (Matrix.SpecialLinearGroup.det_coe D) hD3m hD1m
  set W : Matrix.SpecialLinearGroup (Fin 2) F := ⟨Z, hZdet⟩ with hW
  have hWD : W * D = D * D * W := Matrix.SpecialLinearGroup.ext _ _ fun i j => by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul]
    exact congrFun (congrFun hZD i) j
  rw [← hDd]
  refine ⟨QuotientGroup.mk W, ?_⟩
  have h1 : W * D * W⁻¹ = D⁻¹ := by
    calc W * D * W⁻¹ = D * D * W * W⁻¹ := by rw [hWD]
      _ = D * D := by group
      _ = D⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← pow_two, ← pow_succ, hD3]
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h1,
    QuotientGroup.mk_inv]


variable {G : Type} [Group G] [Finite G]

theorem exists_inverting_of_bar {A L : Subgroup G} {c a d : G}
    (hAe : CFSG.Assembly.IsElemAbelian 3 A) (hcA : c ∈ A) (haA : a ∈ A) (hdA : d ∈ A)
    (hA : A = Subgroup.closure {c, a, d})
    (hLc : ∀ x ∈ L, c * x * c⁻¹ * x⁻¹ ∈ (aschbacherSolvableCore 3 L).map L.subtype)
    (hdL : d ∈ L) (haN : a ∈ Subgroup.normalizer (L : Set G))
    (yb : L ⧸ aschbacherSolvableCore 3 L)
    (hybτ : thetaQuotMulAut L (compAction L ⟨a, haN⟩) yb = yb)
    (hybd : yb * ((⟨d, hdL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) * yb⁻¹ =
      ((⟨d, hdL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L)⁻¹) :
    ∃ l ∈ L ⊓ Subgroup.normalizer (A : Set G), l * d * l⁻¹ = d⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ' := (aschbacherSolvableCore 3 L).map L.subtype with hθ'
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hexp : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have hA3 : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  have hθ3 : ¬ 3 ∣ Nat.card θ' := by
    rw [hθ', Subgroup.card_map_of_injective L.subtype_injective]
    exact (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1
  have hθL : θ' ≤ L := Subgroup.map_subtype_le _
  have hdisj := inf_eq_bot_of_coprime hA3 hθ3
  have hAθ1 : ∀ y ∈ A, y ∈ θ' → y = 1 := fun y hy hyθ => by
    have : y ∈ A ⊓ θ' := ⟨hy, hyθ⟩
    rwa [hdisj, Subgroup.mem_bot] at this
  have hAN : A ≤ Subgroup.normalizer (L : Set G) := by
    rw [hA]
    exact closure_le_normalizer (hexp c hcA) hLc haN hdL
  have hAθ : A ≤ Subgroup.normalizer (θ' : Set G) := hAN.trans (normalizer_le_normalizer_theta L)
  set τ₀ := thetaQuotMulAut L (compAction L ⟨a, haN⟩) with hτ₀
  set dl : L := ⟨d, hdL⟩ with hdl
  set db : L ⧸ aschbacherSolvableCore 3 L := (dl : L ⧸ aschbacherSolvableCore 3 L) with hdb
  obtain ⟨xl, hxl⟩ := QuotientGroup.mk_surjective yb
  set x : G := (xl : G) with hx
  have hxL : x ∈ L := xl.2
  have hR1 : (x * d * x⁻¹)⁻¹ * d⁻¹ ∈ θ' := by
    have h1 : ((xl * dl * xl⁻¹ : L) : L ⧸ aschbacherSolvableCore 3 L) =
        ((dl⁻¹ : L) : L ⧸ aschbacherSolvableCore 3 L) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hxl,
        QuotientGroup.mk_inv, ← hdb, hybd]
    exact ⟨_, QuotientGroup.eq.mp h1, rfl⟩
  have hR2 : (a * x * a⁻¹)⁻¹ * x ∈ θ' := by
    set al := compAction L ⟨a, haN⟩ xl with hal
    have hal' : (al : G) = a * x * a⁻¹ := Sec4.normalizerMonoidHom_apply_coe haN xl
    have h1 : (al : L ⧸ aschbacherSolvableCore 3 L) = (xl : L ⧸ aschbacherSolvableCore 3 L) := by
      have h2 : (al : L ⧸ aschbacherSolvableCore 3 L) = τ₀ yb := by
        rw [hτ₀, ← hxl, thetaQuotMulAut_mk]
      rw [h2, hybτ, hxl]
    refine ⟨_, QuotientGroup.eq.mp h1, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hal']
    rfl
  set w₁ := (x * d * x⁻¹)⁻¹ * d⁻¹ with hw₁
  set v := (a * x * a⁻¹)⁻¹ * x with hv
  have hxd : x * d * x⁻¹ = d⁻¹ * w₁⁻¹ := by rw [hw₁]; group
  have hxa : x * a * x⁻¹ = (x * v * x⁻¹) * a := by rw [hv]; group
  have hxc : x * c * x⁻¹ = (c * x * c⁻¹ * x⁻¹)⁻¹ * c := by group
  have hxv : x * v * x⁻¹ ∈ θ' := conj_mem_theta (Subgroup.le_normalizer hxL) hR2
  have hxA : ∀ y ∈ A, x * y * x⁻¹ ∈ A ⊔ θ' := by
    have hle : Subgroup.closure ({c, a, d} : Set G) ≤
        (A ⊔ θ').comap (MulAut.conj x).toMonoidHom := by
      rw [Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with hy | hy | hy <;> rw [hy]
      · show x * c * x⁻¹ ∈ A ⊔ θ'
        rw [hxc]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.inv_mem _ (hLc x hxL)))
          (Subgroup.mem_sup_left hcA)
      · show x * a * x⁻¹ ∈ A ⊔ θ'
        rw [hxa]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hxv) (Subgroup.mem_sup_left haA)
      · show x * d * x⁻¹ ∈ A ⊔ θ'
        rw [hxd]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (A.inv_mem hdA))
          (Subgroup.mem_sup_right (Subgroup.inv_mem _ hR1))
    intro y hy
    rw [hA] at hy
    exact hle hy
  obtain ⟨t, ht, hlN, hact⟩ := exists_mul_mem_normalizer hA3 hθ3 hAθ hxA
  refine ⟨t * x, ⟨L.mul_mem (hθL ht) hxL, hlN⟩, ?_⟩
  set l := t * x with hl
  have hz : l * d * l⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hlN d).mp hdA
  have h1 := hact d hdA
  rw [hxd] at h1
  have h2 : l * d * l⁻¹ * d ∈ θ' := by
    have e : l * d * l⁻¹ * d = (l * d * l⁻¹ * (d⁻¹ * w₁⁻¹)⁻¹) * (d⁻¹ * w₁⁻¹ * d⁻¹⁻¹) := by group
    rw [e]
    exact θ'.mul_mem h1 (conj_mem_theta (Subgroup.le_normalizer (L.inv_mem hdL))
      (θ'.inv_mem hR1))
  have h3 := hAθ1 _ (A.mul_mem hz hdA) h2
  calc l * d * l⁻¹ = l * d * l⁻¹ * d * d⁻¹ := by group
    _ = d⁻¹ := by rw [h3, one_mul]


theorem exists_inverting_of_inducesKindPSL2 {A L : Subgroup G} {c a d : G}
    {K : Type} [Field K] [Finite K] (h3K : (3 : K) ≠ 0)
    (hAe : CFSG.Assembly.IsElemAbelian 3 A) (hcA : c ∈ A) (haA : a ∈ A) (hdA : d ∈ A)
    (hA : A = Subgroup.closure {c, a, d})
    (hLc : ∀ x ∈ L, c * x * c⁻¹ * x⁻¹ ∈ (aschbacherSolvableCore 3 L).map L.subtype)
    (hdL : d ∈ L) (hd1 : d ≠ 1)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* PSL2 K)
    (ha : InducesKind L (stdPinnedPSL2 K) e a .field) :
    ∃ l ∈ L ⊓ Subgroup.normalizer (A : Set G), l * d * l⁻¹ = d⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hexp : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have hA3 : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  have hθ3 : ¬ 3 ∣ Nat.card ((aschbacherSolvableCore 3 L).map L.subtype) := by
    rw [Subgroup.card_map_of_injective L.subtype_injective]
    exact (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1
  have hdisj := inf_eq_bot_of_coprime hA3 hθ3
  have hAθ1 : ∀ y ∈ A, y ∈ (aschbacherSolvableCore 3 L).map L.subtype → y = 1 := fun y hy hyθ => by
    have : y ∈ A ⊓ (aschbacherSolvableCore 3 L).map L.subtype := ⟨hy, hyθ⟩
    rwa [hdisj, Subgroup.mem_bot] at this
  have haN : a ∈ Subgroup.normalizer (L : Set G) := ha.1
  set τ₀ := thetaQuotMulAut L (compAction L ⟨a, haN⟩) with hτ₀
  set dl : L := ⟨d, hdL⟩ with hdl
  set db : L ⧸ aschbacherSolvableCore 3 L := (dl : L ⧸ aschbacherSolvableCore 3 L) with hdb
  have hτd : τ₀ db = db := by
    rw [hdb, hτ₀, thetaQuotMulAut_mk]
    congr 1
    apply Subtype.ext
    show a * d * a⁻¹ = d
    rw [hcomm a haA d hdA, mul_inv_cancel_right]
  have hdbC : db ∈ Sec8.barCentralizer (Subgroup.zpowers a) L :=
    (mem_barCentralizer_zpowers_iff haN db).mpr hτd
  have hdb3 : db ^ 3 = 1 := by
    rw [hdb, ← QuotientGroup.mk_pow]
    have : dl ^ 3 = 1 := Subtype.ext (by simpa using hexp d hdA)
    rw [this, QuotientGroup.mk_one]
  have hdb1 : db ≠ 1 := by
    intro h1
    rw [hdb, QuotientGroup.eq_one_iff] at h1
    exact hd1 (hAθ1 d hdA ⟨dl, h1, rfl⟩)
  obtain ⟨σ, -, -, ⟨ι⟩⟩ := exists_barCentralizer_mulEquiv_of_field (hexp a haA) e ha
  have h3F : (3 : GH74.GLS.IVK.fixedField σ) ≠ 0 := by
    intro h
    apply h3K
    have h1 : ((3 : GH74.GLS.IVK.fixedField σ) : K) = 3 :=
      map_ofNat (GH74.GLS.IVK.fixedField σ).subtype 3
    rw [← h1, h, ZeroMemClass.coe_zero]
  set d₀ : Sec8.barCentralizer (Subgroup.zpowers a) L := ⟨db, hdbC⟩ with hd₀
  have hd₀3 : ι d₀ ^ 3 = 1 := by
    rw [← map_pow]
    have : d₀ ^ 3 = 1 := Subtype.ext (by simpa using hdb3)
    rw [this, map_one]
  have hd₀1 : ι d₀ ≠ 1 := by
    intro h1
    apply hdb1
    have h2 : d₀ = 1 := ι.injective (h1.trans (map_one ι).symm)
    exact congrArg Subtype.val h2
  obtain ⟨y₀, hy₀⟩ := exists_mul_mul_inv_eq_inv_psl2 h3F hd₀3 hd₀1
  set y₁ := ι.symm y₀ with hy₁
  have hy₁d : y₁ * d₀ * y₁⁻¹ = d₀⁻¹ := by
    apply ι.injective
    rw [map_mul, map_mul, map_inv, map_inv, hy₁, MulEquiv.apply_symm_apply, hy₀]
  set yb : L ⧸ aschbacherSolvableCore 3 L := (y₁ : L ⧸ aschbacherSolvableCore 3 L) with hyb
  have hybd : yb * db * yb⁻¹ = db⁻¹ := congrArg Subtype.val hy₁d
  have hybτ : τ₀ yb = yb := (mem_barCentralizer_zpowers_iff haN yb).mp y₁.2
  exact exists_inverting_of_bar hAe hcA haA hdA hA hLc hdL haN yb hybτ hybd

end CFSG.RankThree.PartTwo.KFacts
