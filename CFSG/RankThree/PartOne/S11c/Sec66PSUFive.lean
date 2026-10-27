module

public import CFSG.RankThree.PartOne.S11c.Sec66PSUFrame
public import CFSG.RankThree.PartOne.S11c.Sec66TLift
public import CFSG.RankThree.PartOne.S11c.SuFiveD

public section

namespace CFSG.RankThree.PartOne.Sec66T

open Matrix CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

section Classify

theorem psu5_aut_classification (θb : MulAut (psu5 h)) (hθb5 : θb ^ 5 = 1) :
    (∃ (P : unit5 h) (c : Kˣ), h.norm (c : K) = 1 ∧
      (P : GL (Fin 5) K) ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin 5) c ∧
      θb = primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) P) ∨
    ∃ (φ : K ≃+* K) (M : unit5 h), φ ^ 5 = 1 ∧ φ ≠ 1 ∧ orderOf θb = 5 ∧
      θb ∉ primeFormD h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) ∧
      (primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) M)⁻¹ * θb *
        primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) M =
          primeFormFieldHom h (isPrimeFormGram_one (n := 5)) φ := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hn : 3 ≤ 5 := by norm_num
  have hq : ¬(5 = 3 ∧ 2 ^ f = 2) := fun hh => absurd hh.1 (by norm_num)
  have hC : IsPrimeFormGram (1 : GL (Fin 5) K) := isPrimeFormGram_one
  have hfin : Finite K := h.finite
  obtain ⟨⟨A, φ⟩, hAφ⟩ := primeFormPsi_surjective h hC hn hq θb
  rw [primeFormPsi_apply] at hAφ
  have hφθ : primeFormFieldFactor h hC hn hq θb = φ := by
    rw [← hAφ]
    exact primeFormFieldFactor_apply h hC hn hq A φ
  have hφ5 : φ ^ 5 = 1 := by
    have := congrArg (primeFormFieldFactor h hC hn hq) hθb5
    rwa [map_pow, hφθ, map_one] at this
  by_cases hφ1 : φ = 1
  · left
    have hθc : θb = primeFormConjHom h _ A := by
      rw [← hAφ, hφ1, map_one, mul_one]
    have hA5 : primeFormConjHom h _ (A ^ 5) = 1 := by
      rw [map_pow, ← hθc]
      exact hθb5
    obtain ⟨-, c, hc1, hcA⟩ := (primeFormPsi_eq_one_iff h hC hn
      (⟨A ^ 5, 1⟩ : unit5 h ⋊[primeFormFieldU h hC] (K ≃+* K))).mp (by
        rw [primeFormPsi_apply, map_one, mul_one]
        exact hA5)
    refine ⟨A, c, hc1, ?_, hθc⟩
    have := hcA
    simpa using this
  · right
    have hφord : orderOf φ = 5 := orderOf_eq_prime hφ5 hφ1
    have hθne : θb ≠ 1 := by
      intro h1
      apply hφ1
      rw [← hφθ, h1, map_one]
    have hθord : orderOf θb = 5 := orderOf_eq_prime hθb5 hθne
    obtain ⟨-, -, -, -, -, M, hM⟩ :=
      CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn hq Nat.prime_five
        (by norm_num) (by norm_num) θb hθord φ hφθ hφord
    refine ⟨φ, M, hφ5, hφ1, hθord, ?_, hM⟩
    intro hD
    apply hφ1
    rw [← ker_primeFormFieldFactor h hC hn hq] at hD
    rw [← hφθ]
    exact MonoidHom.mem_ker.mp hD

end Classify

theorem mem_iff_of_forall_mem_aut {G : Type*} [Group G] [Finite G] {U : Subgroup G}
    (α : MulAut G) (hα : ∀ u ∈ U, α u ∈ U) (x : G) : x ∈ U ↔ α x ∈ U := by
  refine ⟨hα x, fun hx => ?_⟩
  have hle : Subgroup.map α.toMonoidHom U ≤ U := by
    rintro _ ⟨u, hu, rfl⟩
    exact hα u hu
  have heq : Subgroup.map α.toMonoidHom U = U :=
    Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (f := α.toMonoidHom) α.injective).ge
  rw [← heq] at hx
  obtain ⟨u, hu, hux⟩ := hx
  have : u = x := α.injective hux
  rw [← this]
  exact hu

section DCase

theorem psu5_D_case (h5 : 5 ∣ 2 ^ f + 1) {P : unit5 h} {c : Kˣ} (hc : h.norm (c : K) = 1)
    (hP5 : (P : GL (Fin 5) K) ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin 5) c)
    (hinn : primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) P ∉
      innerAut (psu5 h))
    {U : Subgroup (psu5 h)} (hU1 : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hUP : ∀ u ∈ U, primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) P u ∈ U)
    (hra : LocalRankAut 5 (psu5 h)
      (primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) P)) : False := by
  classical
  have hfin : Finite K := h.finite
  set α := primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) P with hα
  have hZc : normOneScalars h (gamma5 h) 5 ≤ Subgroup.center (gamma5 h) :=
    normOneScalars_le_center h _ 5
  obtain ⟨S, hS2, hS1, hSφ⟩ :=
    exists_aut_invariant_two_subgroup (normOneScalars h (gamma5 h) 5) hZc U hU2 hU1
  let φ : gamma5 h ≃* gamma5 h := primeFormConjSU h _ P⁻¹
  have hφ : ∀ x : gamma5 h, QuotientGroup.mk' (normOneScalars h (gamma5 h) 5) x ∈ U ↔
      QuotientGroup.mk' (normOneScalars h (gamma5 h) 5) (φ x) ∈ U := by
    intro x
    have h1 : QuotientGroup.mk' (normOneScalars h (gamma5 h) 5) (φ x) = α⁻¹ (proj5 h x) := by
      have h2 := primeFormConjAut_mk h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) P⁻¹ x
      have h3 : primeFormConjAut h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) P⁻¹ =
          α⁻¹ := by
        have : primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) P⁻¹ = α⁻¹ :=
          map_inv _ P
        exact this
      rw [h3] at h2
      exact h2.symm
    rw [h1]
    have h4 := mem_iff_of_forall_mem_aut α hUP (α⁻¹ (proj5 h x))
    rw [MulAut.apply_inv_self] at h4
    exact h4.symm
  have hSP := hSφ φ hφ
  set S1 : Subgroup (GL (Fin 5) K) := S.map (gamma5 h).subtype with hS1def
  have hS1p : IsPGroup 2 S1 := hS2.map (gamma5 h).subtype
  have hS1ne : S1 ≠ ⊥ := by
    intro hbot
    apply hS1
    have := (Subgroup.map_eq_bot_iff _).mp hbot
    rw [Subgroup.ker_subtype] at this
    exact eq_bot_iff.mpr this
  have hS1P : ∀ s ∈ S1, (P : GL (Fin 5) K)⁻¹ * s * (P : GL (Fin 5) K) ∈ S1 := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨φ g, hSP g hg, rfl⟩
  obtain ⟨P', hP'5, hP'conj⟩ := exists_pow_five_eq_one_conj h h5 hc hP5 hS1p hS1ne hS1P
  have hP'5u : P' ^ 5 = 1 := Subtype.ext hP'5
  have hαP' : primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) P' = α := by
    refine MulEquiv.ext fun x => QuotientGroup.induction_on x fun g => ?_
    rw [primeFormConjHom_mk, hα, primeFormConjHom_mk]
    congr 1
    apply Subtype.ext
    exact hP'conj g
  have hα5 : α ^ 5 = 1 := by
    rw [← hαP', ← map_pow, hP'5u, map_one]
  obtain ⟨P0, hP0⟩ := KFU.exists_unitary_conj_diag h Nat.prime_five h5 (Subgroup.zpowers P')
    (by
      rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
      exact (Commute.zpow_zpow_self P' m n).eq)
    (by
      rintro _ ⟨m, rfl⟩
      show (P' ^ m) ^ 5 = 1
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hP'5u,
        _root_.one_zpow])
  have hDdiag : (((P0⁻¹ * P' * P0 : unit5 h) : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K).IsDiag := hP0 P' (Subgroup.mem_zpowers P')
  set Dg : GL (Fin 5) K := ((P0⁻¹ * P' * P0 : unit5 h) : GL (Fin 5) K) with hDg
  have hP'eq : (P' : GL (Fin 5) K) = (P0 : GL (Fin 5) K) * Dg * (P0 : GL (Fin 5) K)⁻¹ := by
    rw [hDg]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  by_cases hrep : ∃ i j : Fin 5, i ≠ j ∧ ((Dg : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) i i =
      ((Dg : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) j j
  · obtain ⟨i, j, hij, hDij⟩ := hrep
    refine not_localRankAut_of_frame h h5 P0 hij α hα5 hinn ?_ ?_ hra
    · intro a ha
      obtain ⟨t, ht, hat⟩ := exists_of_mem_frameA ha
      rw [← hαP']
      show primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) P'
        ((a : gamma5 h) : psu5 h) = ((a : gamma5 h) : psu5 h)
      rw [primeFormConjHom_mk]
      congr 1
      apply Subtype.ext
      show (P' : GL (Fin 5) K) * (a : GL (Fin 5) K) * (P' : GL (Fin 5) K)⁻¹ = (a : GL (Fin 5) K)
      rw [hat, hP'eq]
      have hc := isDiag_comm hDdiag (isDiag_of_mem_torusEq ht)
      calc (P0 : GL (Fin 5) K) * Dg * (P0 : GL (Fin 5) K)⁻¹ *
            ((P0 : GL (Fin 5) K) * t * (P0 : GL (Fin 5) K)⁻¹) *
            ((P0 : GL (Fin 5) K) * Dg * (P0 : GL (Fin 5) K)⁻¹)⁻¹ =
          (P0 : GL (Fin 5) K) * (Dg * t * Dg⁻¹) * (P0 : GL (Fin 5) K)⁻¹ := by group
        _ = (P0 : GL (Fin 5) K) * t * (P0 : GL (Fin 5) K)⁻¹ := by
          rw [hc]
          group
    · rw [← hαP']
      show primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) P'
        ((frameR h P0 i j : gamma5 h) : psu5 h) = ((frameR h P0 i j : gamma5 h) : psu5 h)
      rw [primeFormConjHom_mk]
      congr 1
      apply Subtype.ext
      show (P' : GL (Fin 5) K) * ((frameR h P0 i j : gamma5 h) : GL (Fin 5) K) *
        (P' : GL (Fin 5) K)⁻¹ = ((frameR h P0 i j : gamma5 h) : GL (Fin 5) K)
      rw [coe_frameR, hP'eq]
      have hc := KFSU5.swapUnit_mul_comm (K := K) (i := i) (j := j) Dg hDdiag hDij
      calc (P0 : GL (Fin 5) K) * Dg * (P0 : GL (Fin 5) K)⁻¹ *
            ((P0 : GL (Fin 5) K) * KFSU5.swapUnit K i j * (P0 : GL (Fin 5) K)⁻¹) *
            ((P0 : GL (Fin 5) K) * Dg * (P0 : GL (Fin 5) K)⁻¹)⁻¹ =
          (P0 : GL (Fin 5) K) * (Dg * KFSU5.swapUnit K i j * Dg⁻¹) *
            (P0 : GL (Fin 5) K)⁻¹ := by group
        _ = (P0 : GL (Fin 5) K) * KFSU5.swapUnit K i j * (P0 : GL (Fin 5) K)⁻¹ := by
          rw [← hc]
          group
  · push Not at hrep
    obtain ⟨d, hd⟩ := KFU.exists_diagU_of_isDiag hDdiag
    have hDg5 : Dg ^ 5 = 1 := by
      have h1 : (P0⁻¹ * P' * P0) ^ 5 = 1 := by
        rw [show P0⁻¹ * P' * P0 = P0⁻¹ * P' * P0⁻¹⁻¹ by simp, conj_pow, hP'5u]
        group
      have := congrArg Subtype.val h1
      rw [hDg]
      simpa using this
    have hd5 : ∀ k, d k ^ 5 = 1 := by
      have h1 := hDg5
      rw [← hd, KFU.diagU_pow, ← KFU.diagU_one] at h1
      intro k
      exact congrFun (KFU.diagU_injective h1) k
    have hdinj : Function.Injective d := by
      intro i j hij
      by_contra hne
      apply hrep i j hne
      rw [← hd, KFU.diagU_apply_same, KFU.diagU_apply_same, hij]
    obtain ⟨ζ0, hζ0⟩ := KFU.exists_isPrimitiveRoot h Nat.prime_five h5
    obtain ⟨z, hz⟩ := hζ0.isUnit (by norm_num)
    have hzp : IsPrimitiveRoot z 5 := IsPrimitiveRoot.coe_units_iff.mp (hz ▸ hζ0)
    have hprod : ∏ k, d k = 1 := prod_eq_one_of_injective_pow_five ⟨z, hzp⟩ hd5 hdinj
    have hdet : ((P' : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).det = 1 := by
      have h1 : Matrix.GeneralLinearGroup.det (P' : GL (Fin 5) K) =
          Matrix.GeneralLinearGroup.det Dg := by
        rw [hP'eq, map_mul, map_mul, map_inv]
        simp
      have h2 := congrArg (fun u : Kˣ => (u : K)) h1
      simp only [Matrix.GeneralLinearGroup.val_det_apply] at h2
      rw [h2, ← hd, KFU.det_diagU, ← Units.coe_prod, hprod, Units.val_one]
    have hPg : (P' : GL (Fin 5) K) ∈ gamma5 h := mem_gramSU.mpr ⟨P'.2, hdet⟩
    apply hinn
    refine ⟨proj5 h ⟨P', hPg⟩, ?_⟩
    rw [← hαP']
    refine MulEquiv.ext fun x => QuotientGroup.induction_on x fun g => ?_
    rw [primeFormConjHom_mk, MulAut.conj_apply]
    have : (⟨(P' : GL (Fin 5) K) * (g : GL (Fin 5) K) * (P' : GL (Fin 5) K)⁻¹,
        conj_mem_gramSU h _ P'.2 g.2⟩ : gramSU h ((1 : GL (Fin 5) K) :
          Matrix (Fin 5) (Fin 5) K)) = ⟨P', hPg⟩ * g * ⟨P', hPg⟩⁻¹ := Subtype.ext rfl
    rw [this]
    rfl

end DCase

section FCase

theorem innerAut_le_primeFormD :
    innerAut (psu5 h) ≤ primeFormD h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) := by
  rintro _ ⟨y, rfl⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  refine ⟨⟨(g : GL (Fin 5) K), ((mem_gramSU_iff_unitary h).mp g.2).1⟩, ?_⟩
  refine MulEquiv.ext fun x => QuotientGroup.induction_on x fun g' => ?_
  rw [primeFormConjHom_mk, MulAut.conj_apply]
  have : (⟨(g : GL (Fin 5) K) * (g' : GL (Fin 5) K) * (g : GL (Fin 5) K)⁻¹,
      conj_mem_gramSU h _ ((mem_gramSU_iff_unitary h).mp g.2).1 g'.2⟩ :
        gramSU h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) = g * g' * g⁻¹ :=
    Subtype.ext rfl
  rw [this]
  rfl

theorem psu5_twisted_apply (M : unit5 h) (φ : K ≃+* K) (g : gamma5 h) :
    (primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) M *
        primeFormFieldHom h (isPrimeFormGram_one (n := 5)) φ *
        (primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) M)⁻¹)
        ((g : gamma5 h) : psu5 h) =
      ((primeFormConjSU h _ M (primeFormFieldSU h isPrimeFormGram_one φ
        (primeFormConjSU h _ M⁻¹ g)) : gamma5 h) : psu5 h) := by
  simp only [MulAut.mul_apply]
  rw [← map_inv, primeFormConjHom, MonoidHom.coe_mk, OneHom.coe_mk, primeFormConjAut_mk,
    primeFormFieldHom, MonoidHom.coe_mk, OneHom.coe_mk, primeFormFieldAut_mk, primeFormConjAut_mk]

theorem coe_twisted (M : unit5 h) (φ : K ≃+* K) (g : gamma5 h) :
    ((primeFormConjSU h _ M (primeFormFieldSU h isPrimeFormGram_one φ
        (primeFormConjSU h _ M⁻¹ g)) : gamma5 h) : GL (Fin 5) K) =
      (M : GL (Fin 5) K) * glAut φ ((M : GL (Fin 5) K)⁻¹ * (g : GL (Fin 5) K) *
        (M : GL (Fin 5) K)) * (M : GL (Fin 5) K)⁻¹ := by
  show (M : GL (Fin 5) K) * glAut φ (((M⁻¹ : unit5 h) : GL (Fin 5) K) * (g : GL (Fin 5) K) *
    ((M⁻¹ : unit5 h) : GL (Fin 5) K)⁻¹) * (M : GL (Fin 5) K)⁻¹ = _
  simp only [Subgroup.coe_inv, inv_inv]

theorem psu5_F_case (h5 : 5 ∣ 2 ^ f + 1) {ψ : MulAut (psu5 h)} (hψ5 : orderOf ψ = 5)
    (hψD : ψ ∉ primeFormD h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K))
    (hra : LocalRankAut 5 (psu5 h) ψ) : False := by
  classical
  have hψ5' : ψ ^ 5 = 1 := by
    have := pow_orderOf_eq_one ψ
    rwa [hψ5] at this
  have hψinn : ψ ∉ innerAut (psu5 h) := fun hinn => hψD (innerAut_le_primeFormD h hinn)
  rcases psu5_aut_classification h ψ hψ5' with ⟨P, c, -, -, hψP⟩ | ⟨φ, M, hφ5, hφ1, -, -, hM⟩
  · exact hψD ⟨P, hψP.symm⟩
  · have hψeq : ψ = primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) M *
        primeFormFieldHom h (isPrimeFormGram_one (n := 5)) φ *
        (primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) M)⁻¹ := by
      rw [← hM]
      group
    have key : ∀ g : gamma5 h, ψ (proj5 h g) = proj5 h (primeFormConjSU h _ M
        (primeFormFieldSU h isPrimeFormGram_one φ (primeFormConjSU h _ M⁻¹ g))) := fun g => by
      rw [hψeq]
      exact psu5_twisted_apply h M φ g
    refine not_localRankAut_of_frame h h5 M (i := 0) (j := 1) (by decide) ψ hψ5' hψinn ?_ ?_ hra
    · intro a ha
      obtain ⟨t, ht, hat⟩ := exists_of_mem_frameA ha
      rw [key]
      congr 1
      apply Subtype.ext
      rw [coe_twisted, hat]
      have h1 : (M : GL (Fin 5) K)⁻¹ * ((M : GL (Fin 5) K) * t * (M : GL (Fin 5) K)⁻¹) *
          (M : GL (Fin 5) K) = t := by group
      have hφt : glAut φ t = t := Units.ext (Matrix.ext fun r s => by
        rw [coe_glAut]
        exact apply_eq_of_mem_torusEq φ hφ5 ht r s)
      rw [h1, hφt]
    · rw [key]
      congr 1
      apply Subtype.ext
      rw [coe_twisted, coe_frameR]
      have h1 : (M : GL (Fin 5) K)⁻¹ * ((M : GL (Fin 5) K) * KFSU5.swapUnit K (0 : Fin 5) 1 *
          (M : GL (Fin 5) K)⁻¹) * (M : GL (Fin 5) K) = KFSU5.swapUnit K (0 : Fin 5) 1 := by group
      have hφs : glAut φ (KFSU5.swapUnit K (0 : Fin 5) 1) = KFSU5.swapUnit K (0 : Fin 5) 1 :=
        Units.ext (by
          rw [coe_glAut, KFSU5.swapUnit_val]
          exact KFSU5.swapMatrix_map φ.toRingHom (0 : Fin 5) 1)
      rw [h1, hφs]

theorem psu5_K2_core (h5 : 5 ∣ 2 ^ f + 1) (E : Subgroup (MulAut (psu5 h)))
    (hE : IsElementaryAbelian 5 ↥E)
    (hcard : Nat.card E = 5 ^ 2) (hEinn : E ⊓ innerAut (psu5 h) = ⊥)
    (hra : ∀ α ∈ E, LocalRankAut 5 (psu5 h) α) : False := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hn : 3 ≤ 5 := by norm_num
  have hq : ¬(5 = 3 ∧ 2 ^ f = 2) := fun hh => absurd hh.1 (by norm_num)
  have hfin : Finite K := h.finite
  set D := primeFormD h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) with hD
  by_cases hED : E ≤ D
  · obtain ⟨-, -, hcardDI, -⟩ := unitary_full_diagonal_outer_order h hn hq
    have hgcd : Nat.gcd 5 (2 ^ f + 1) = 5 := Nat.gcd_eq_left h5
    set I : Subgroup (MulAut (psu5 h)) :=
      CFSG.ComponentClassification.OuterAutomorphisms.inner (psu5 h) with hI
    let ρ : ↥E →* (↥D ⧸ I.subgroupOf D) :=
      (QuotientGroup.mk' (I.subgroupOf D)).comp (Subgroup.inclusion hED)
    have hρinj : Function.Injective ρ := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have h1 : (Subgroup.inclusion hED x : ↥D) ∈ I.subgroupOf D :=
        (QuotientGroup.eq_one_iff _).mp hx
      rw [Subgroup.mem_subgroupOf] at h1
      have h2 : (x : MulAut (psu5 h)) ∈ E ⊓ I := ⟨x.2, h1⟩
      have hEinn' : E ⊓ I = ⊥ := hEinn
      rw [hEinn', Subgroup.mem_bot] at h2
      exact Subtype.ext h2
    have h3 := Nat.card_le_card_of_injective ρ hρinj
    rw [hcard, hcardDI, hgcd] at h3
    omega
  · obtain ⟨ψ, hψE, hψD⟩ : ∃ ψ ∈ E, ψ ∉ D := by
      by_contra hcon
      push Not at hcon
      exact hED hcon
    have hψ5 : ψ ^ 5 = 1 := elemPow_eq_one_of_isElementaryAbelian (A := E) ψ hψE
    have hψ1 : ψ ≠ 1 := fun h1 => hψD (h1 ▸ D.one_mem)
    have hψord : orderOf ψ = 5 := orderOf_eq_prime hψ5 hψ1
    exact psu5_F_case h h5 hψord hψD (hra ψ hψE)

end FCase

end CFSG.RankThree.PartOne.Sec66T
