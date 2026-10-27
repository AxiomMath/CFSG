module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSLRestInner
public import CFSG.Timmesfeld.Orders.Bang

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Timmesfeld

namespace OrdPRest

section Arith

theorem not_dvd_two_pow_sub_one {r f n j : ℕ} (hr : IsPrimitivePrimeDivisor r (f * n))
    (hf : 1 ≤ f) (hj : 0 < j) (hjn : j < n) : ¬ r ∣ 2 ^ (f * j) - 1 := by
  intro h
  have hfn : 0 < f * n := Nat.mul_pos (by omega) (by omega)
  have h1 := (hr.dvd_sub_one_iff hfn (f * j)).mp h
  have h2 : n ∣ j := Nat.dvd_of_mul_dvd_mul_left (by omega) h1
  exact absurd (Nat.le_of_dvd hj h2) (by omega)

theorem lt_of_isPrimitivePrimeDivisor {r k : ℕ} (hr : IsPrimitivePrimeDivisor r k) (hk : 0 < k) :
    k < r := by
  have hr2 := hr.ne_two hk
  have : Fact r.Prime := ⟨hr.prime⟩
  have h : r ∣ 2 ^ (r - 1) - 1 :=
    (Bang.dvd_two_pow_sub_one_iff (r - 1)).mpr
      (ZMod.pow_card_sub_one_eq_one (Bang.two_ne_zero_zmod hr2))
  have h1 := (hr.dvd_sub_one_iff hk (r - 1)).mp h
  have hr1 : 0 < r - 1 := by have := hr.prime.two_le; omega
  have := Nat.le_of_dvd hr1 h1
  omega

theorem not_dvd_card_GL {r f n k : ℕ} (hr : IsPrimitivePrimeDivisor r (f * n)) (hf : 1 ≤ f)
    (hkn : k < n) {F : Type*} [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ f) :
    ¬ r ∣ Nat.card (GL (Fin k) F) := by
  rw [Matrix.card_GL_field, hF]
  intro h
  obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hr.prime.prime _).mp h
  have hik : (i : ℕ) < k := i.2
  have e : (2 ^ f) ^ k - (2 ^ f) ^ (i : ℕ) = 2 ^ (f * i) * (2 ^ (f * (k - i)) - 1) := by
    rw [← pow_mul, ← pow_mul, Nat.mul_sub_one, ← pow_add, ← Nat.mul_add,
      Nat.add_sub_cancel' hik.le]
  rw [e] at hi
  have hfn : 0 < f * n := Nat.mul_pos (by omega) (by omega)
  rcases (Nat.Prime.dvd_mul hr.prime).mp hi with h1 | h1
  · exact hr.ne_two hfn
      ((Nat.prime_dvd_prime_iff_eq hr.prime Nat.prime_two).mp (hr.prime.dvd_of_dvd_pow h1))
  · exact not_dvd_two_pow_sub_one hr hf (by omega) (by omega) h1

theorem not_dvd_card_GL' {r f n : ℕ} (hr : IsPrimitivePrimeDivisor r (f * n)) (hf : 1 ≤ f)
    {F : Type*} [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ f) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (hι : Fintype.card ι < n) : ¬ r ∣ Nat.card (GL ι F) := by
  have e : GL ι F ≃* GL (Fin (Fintype.card ι)) F :=
    Units.mapEquiv (Matrix.reindexAlgEquiv F F (Fintype.equivFin ι)).toRingEquiv.toMulEquiv
  rw [Nat.card_congr e.toEquiv]
  exact not_dvd_card_GL hr hf hι hF

theorem ringAut_eq_one {F : Type*} [Field F] {f r : ℕ} (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f)
    (hr : r.Prime) (hrf : ¬ r ∣ f) {σ : F ≃+* F} (hσ : σ ^ r = 1) : σ = 1 := by
  obtain ⟨-, -, -, -, hcard, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two hf hF
  have h1 : orderOf σ ∣ f := hcard ▸ orderOf_dvd_natCard σ
  have h2 : orderOf σ ∣ r := orderOf_dvd_of_pow_eq_one hσ
  rcases (Nat.dvd_prime hr).mp h2 with h | h
  · exact orderOf_eq_one_iff.mp h
  · exact absurd (h ▸ h1) hrf

end Arith

section Block

theorem exists_block {n r : ℕ} (hr : r.Prime) {F : Type*} [Field F] [DecidableEq F] {t : Fin n → F}
    {B : Matrix (Fin n) (Fin n) F} (hB : B * diagonal t = diagonal t * B) (hBr : B ^ r = 1)
    (hB1 : B ≠ 1) (ht : ∀ c, ∃ i, t i ≠ c) :
    ∃ c : F, Fintype.card {i // t i = c} < n ∧ ∃ M : GL {i // t i = c} F, orderOf M = r := by
  have : Fact r.Prime := ⟨hr⟩
  have hbd := TypeA.PGLTor.isBlockDiag_of_commute_diagonal hB
  obtain ⟨c, hc⟩ : ∃ c, B.toSquareBlock t c ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hB1
    ext i j
    by_cases hij : t i = t j
    · have h := congrFun (congrFun (hall (t j)) ⟨i, hij⟩) ⟨j, rfl⟩
      simpa only [toSquareBlock_def, of_apply, one_apply, Subtype.mk.injEq] using h
    · rw [hbd i j hij, one_apply_ne (fun h => hij (by rw [h]))]
  refine ⟨c, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := ht c
    calc Fintype.card {i // t i = c} < Fintype.card (Fin n) :=
          Fintype.card_subtype_lt (p := fun i => t i = c) (x := i) hi
      _ = n := Fintype.card_fin n
  · set Mc := B.toSquareBlock t c with hMc
    have hMr : Mc ^ r = 1 := by
      rw [hMc, ← TypeA.PGLTor.toSquareBlock_pow_of_isBlockDiag hbd, hBr,
        TypeA.PGLTor.toSquareBlock_one]
    have hr1 : r - 1 + 1 = r := Nat.sub_add_cancel hr.one_lt.le
    let Mu : GL {i // t i = c} F := ⟨Mc, Mc ^ (r - 1),
      by rw [← pow_succ', hr1, hMr], by rw [← pow_succ, hr1, hMr]⟩
    refine ⟨Mu, orderOf_eq_prime ?_ ?_⟩
    · apply Units.ext
      rw [Units.val_pow_eq_pow_val]
      exact hMr
    · exact fun h => hc (congrArg Units.val h)

end Block

section Centralizer

variable {m : ℕ} {F : Type} [Field F] {G : Type*} [Group G]
  {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}

theorem acts_of_conjAut (hm : 2 ≤ m) {c : G} (hc : c ∈ Subgroup.normalizer (ψ.range : Set G))
    {A : GL (Fin (m + 1)) F}
    (hα : ∀ y y' : SpecialLinearGroup (Fin (m + 1)) F,
      ψ y' = c⁻¹ * ψ y * c → conjAut (m + 1) F A (proj (m + 1) F y) = proj (m + 1) F y') :
    ∀ u, c⁻¹ * ψ u * c = ψ (InnerDiagA.conjSL A u) := by
  intro u
  have h := HypSixTypeA.conj_eq_of_conjAut hm hc hα (A₀ := 1) (D := A)
    (by rw [map_one, mul_inv_cancel]) u
  rw [map_one, mul_one, RootPlaneA.slConjugation_eq_conjSL] at h
  exact h

omit [Field F] in
theorem exists_pow_conjAut_fieldAut [Field F] (B : GL (Fin (m + 1)) F) (σ : F ≃+* F) (k : ℕ) :
    ∃ N : GL (Fin (m + 1)) F, (conjAut (m + 1) F B * fieldAut (m + 1) F σ) ^ k =
      conjAut (m + 1) F N * fieldAut (m + 1) F (σ ^ k) := by
  induction k with
  | zero => exact ⟨1, by rw [pow_zero, pow_zero, map_one, map_one, one_mul]⟩
  | succ k ih =>
    obtain ⟨N, hN⟩ := ih
    refine ⟨N * GeneralLinearGroup.map ((σ ^ k : F ≃+* F) : F →+* F) B, ?_⟩
    rw [pow_succ (conjAut (m + 1) F B * fieldAut (m + 1) F σ), hN, conjAut_mul_fieldAut_mul,
      ← pow_succ]

theorem commute_of_conj_scalar {A₀ X : GL (Fin (m + 1)) F} {c : F}
    (h : ((A₀ * X * A₀⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      scalar (Fin (m + 1)) c) (Y : GL (Fin (m + 1)) F) : X * Y = Y * X := by
  have hc : ∀ W : GL (Fin (m + 1)) F, A₀ * X * A₀⁻¹ * W = W * (A₀ * X * A₀⁻¹) := fun W =>
    Units.ext (by
      rw [Units.val_mul (A₀ * X * A₀⁻¹) W, Units.val_mul W (A₀ * X * A₀⁻¹), h]
      exact (scalar_commute c (fun r => Commute.all c r) _).eq)
  have hX : X = A₀ * X * A₀⁻¹ := by
    have h1 := hc A₀
    calc X = A₀⁻¹ * (A₀ * X * A₀⁻¹ * A₀) := by group
      _ = A₀⁻¹ * (A₀ * (A₀ * X * A₀⁻¹)) := by rw [h1]
      _ = A₀ * X * A₀⁻¹ := by group
  rw [hX]
  exact hc Y

end Centralizer

section Setting

variable {G : Type} [Group G] [Finite G] {p : ℕ} {Bs G₀ : Subgroup G} {m f : ℕ} {F : Type}
  [Field F] [Fintype F] [CharP F 2] {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}

theorem orderOf_ne_of_commute
    (hS : GGSixFusionSetting p Bs G₀ (SpecialLinear.rootDatum m F) .PSL (m + 1) f ψ)
    (h24 : GGTwoLocalRankFour p (Subgroup.normalizer (G₀ : Set G)))
    (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f) (hpF : p ∣ Nat.card F - 1) {r : ℕ}
    (hr : IsPrimitivePrimeDivisor r (f * (m + 1))) {b : G} (hb : b ∈ Bs) (hb1 : b ≠ 1) {z : G}
    (hzM : z ∈ Subgroup.normalizer (G₀ : Set G)) (hzb : z * b = b * z) : orderOf z ≠ r := by
  classical
  intro hzr
  obtain ⟨⟨-, hrank⟩, ⟨hrange, hker⟩, -, -⟩ := hS.presents
  have hm : 2 ≤ m := hrank
  have hn : 3 ≤ m + 1 := by omega
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact hS.centralizer_eq_bot
  have hzN : z ∈ Subgroup.normalizer (ψ.range : Set G) := by
    rw [hrange]
    exact hzM
  have hfn : 0 < f * (m + 1) := Nat.mul_pos (by omega) (by omega)
  have hrp := hr.prime
  have hr2 := hr.ne_two hfn
  have hrlt := lt_of_isPrimitivePrimeDivisor hr hfn
  have hffn : f ≤ f * (m + 1) := Nat.le_mul_of_pos_right f (by omega)
  have hzr1 : z ^ r = 1 := hzr ▸ pow_orderOf_eq_one z
  have hF' : Nat.card F = 2 ^ f := by rw [Nat.card_eq_fintype_card, hF]
  have hrq : ¬ r ∣ Nat.card F - 1 := by
    rw [hF', show 2 ^ f = 2 ^ (f * 1) by rw [mul_one]]
    exact not_dvd_two_pow_sub_one hr hf (by norm_num) (by omega)
  obtain ⟨α, hα⟩ := HypSixTypeA.exists_projAut hn hker hzN
  have hαr : α ^ r = 1 := by
    ext x
    obtain ⟨y, rfl⟩ := proj_surjective (m + 1) F x
    rw [MulAut.one_apply]
    apply HypSixTypeA.projAut_pow_apply hker hzN hα r y y
    rw [hzr1]
    group
  obtain ⟨B, σ, ε, hε, hαeq⟩ := (automorphism_generation (K := F) hn).2 α
  have hε0 : ε = 0 := HypSixTypeA.graph_exp_eq_zero hn (hrp.odd_of_ne_two hr2) hε
    (by rw [← hαeq]; exact hαr)
  subst hε0
  rw [pow_zero, mul_one] at hαeq
  have hσr : σ ^ r = 1 := by
    obtain ⟨N, hN⟩ := exists_pow_conjAut_fieldAut B σ r
    rw [← hαeq, hαr] at hN
    exact (eq_one_of_conjAut_mul_fieldAut_eq_one hn N (σ ^ r) hN.symm).1
  have hσ1 : σ = 1 := ringAut_eq_one hf hF' hrp
    (fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)) hσr
  rw [hσ1, map_one, mul_one] at hαeq
  have hzB := acts_of_conjAut hm hzN (A := B) fun y y' h => by rw [← hαeq]; exact hα y y' h
  have hcop : (Nat.card Fˣ).Coprime r := by
    rw [Nat.card_units]
    exact ((Nat.Prime.coprime_iff_not_dvd hrp).mpr hrq).symm
  obtain ⟨B', hB'r, hzB'⟩ := exists_pow_eq_one hker hzB hzr1 fun c _ =>
    ⟨(powCoprime hcop).symm c, by rw [← powCoprime_apply hcop, Equiv.apply_symm_apply]⟩
  obtain ⟨Ab, hAb⟩ := RootPlaneA.exists_gl_of_psiInnerDiag hm hker (hS.innerDiag b hb)
  have hbp : b ^ p = 1 := hS.elem.2 b hb
  obtain ⟨cb, hcb⟩ := exists_scalar_pow hker hAb hbp
  have hconj : conjAut (m + 1) F (Ab * B') = conjAut (m + 1) F (B' * Ab) := by
    refine RootPlaneA.conjAut_eq_of_psi_eq hker fun u => ?_
    have e1 : ψ (InnerDiagA.conjSL (Ab * B') u) = (z * b)⁻¹ * ψ u * (z * b) := by
      rw [RootPlaneA.conjSL_mul, ← hAb, ← hzB']
      group
    have e2 : ψ (InnerDiagA.conjSL (B' * Ab) u) = (b * z)⁻¹ * ψ u * (b * z) := by
      rw [RootPlaneA.conjSL_mul, ← hzB', ← hAb]
      group
    rw [e1, e2, hzb]
  obtain ⟨l, hl⟩ : ∃ l : Fˣ, Ab * B' = GeneralLinearGroup.scalar (Fin (m + 1)) l * (B' * Ab) := by
    have h1 : conjAut (m + 1) F ((Ab * B') * (B' * Ab)⁻¹) = 1 := by
      rw [map_mul, map_inv, hconj, mul_inv_cancel]
    have h2 := AutPSL.mem_center_of_conjAut_eq_one (by omega) h1
    rw [GeneralLinearGroup.center_eq_range_scalar] at h2
    obtain ⟨l, hl⟩ := h2
    exact ⟨l, by rw [hl]; group⟩
  set S := GeneralLinearGroup.scalar (Fin (m + 1)) l with hS'
  have hSr : S ^ r = 1 := by
    have h1 := TypeA.PGLTor.mul_pow_eq_of_mul_eq (TypeA.PGLTor.commute_scalar l B') hl r
    rw [hB'r, mul_one, one_mul] at h1
    exact mul_right_cancel (h1.symm.trans (one_mul Ab).symm)
  have hSp : S ^ p = 1 := by
    have hl' : B' * Ab = S⁻¹ * (Ab * B') := by rw [hl]; group
    have h1 := TypeA.PGLTor.mul_pow_eq_of_mul_eq (TypeA.PGLTor.commute_scalar l Ab).inv_left hl' p
    rw [hcb, ← mul_assoc, (TypeA.PGLTor.commute_scalar cb B').eq.symm] at h1
    have h2 := mul_right_cancel h1
    have h3 : (S⁻¹) ^ p = 1 := mul_right_cancel
      (h2.symm.trans (one_mul (GeneralLinearGroup.scalar (Fin (m + 1)) cb)).symm)
    rw [inv_pow, inv_eq_one] at h3
    exact h3
  have hpr : p.Coprime r := by
    refine (Nat.coprime_primes hS.prime hrp).mpr fun h => hrq ?_
    rw [← h]
    exact hpF
  have hS1 : S = 1 := by
    have h := pow_gcd_eq_one.mpr ⟨hSp, hSr⟩
    rwa [hpr.gcd_eq_one, pow_one] at h
  rw [hS1, one_mul] at hl
  obtain ⟨A₀, hA₀⟩ := bstar_toral hS h24 hpF
  have hD := hA₀ b hb Ab hAb
  set t : Fin (m + 1) → F :=
    Matrix.diag ((A₀ * Ab * A₀⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
    with ht
  have hDt : ((A₀ * Ab * A₀⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      diagonal t := hD.diagonal_diag.symm
  set B'' : GL (Fin (m + 1)) F := A₀ * B' * A₀⁻¹ with hB''
  have hB''comm : (B'' : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * diagonal t =
      diagonal t * (B'' : Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
    rw [← hDt, ← Units.val_mul, ← Units.val_mul]
    congr 1
    calc B'' * (A₀ * Ab * A₀⁻¹) = A₀ * (B' * Ab) * A₀⁻¹ := by rw [hB'']; group
      _ = A₀ * (Ab * B') * A₀⁻¹ := by rw [hl]
      _ = A₀ * Ab * A₀⁻¹ * B'' := by rw [hB'']; group
  have hB''r : (B'' : Matrix (Fin (m + 1)) (Fin (m + 1)) F) ^ r = 1 := by
    rw [← Units.val_pow_eq_pow_val, hB'', _root_.conj_pow, hB'r, mul_one, mul_inv_cancel,
      Units.val_one]
  have hB''1 : (B'' : Matrix (Fin (m + 1)) (Fin (m + 1)) F) ≠ 1 := by
    intro h
    have h1 : B'' = 1 := Units.ext h
    have hB'1 : B' = 1 := by
      calc B' = A₀⁻¹ * B'' * A₀ := by rw [hB'']; group
        _ = 1 := by rw [h1]; group
    have hz1 : z ∈ Subgroup.centralizer (ψ.range : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨u, rfl⟩
      have h2 := hzB' u
      rw [hB'1, RootPlaneA.conjSL_one] at h2
      calc ψ u * z = z * (z⁻¹ * ψ u * z) := by group
        _ = z * ψ u := by rw [h2]
    rw [hCψ, Subgroup.mem_bot] at hz1
    rw [hz1, orderOf_one] at hzr
    exact hrp.one_lt.ne hzr
  have htc : ∀ c, ∃ i, t i ≠ c := by
    intro c
    by_contra hall
    push Not at hall
    apply hb1
    have hsc : ((A₀ * Ab * A₀⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
        scalar (Fin (m + 1)) c := by
      rw [hDt]
      ext i j
      rw [scalar_apply, diagonal_apply, diagonal_apply, hall i]
    have hcomm := commute_of_conj_scalar hsc
    have hbC : b ∈ Subgroup.centralizer (ψ.range : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨u, rfl⟩
      have h2 := hAb u
      have h3 : InnerDiagA.conjSL Ab u = u := by
        apply SpecialLinearGroup.toGL_injective
        rw [RootPlaneA.toGL_conjSL, hcomm, mul_inv_cancel_right]
      rw [h3] at h2
      calc ψ u * b = b * (b⁻¹ * ψ u * b) := by group
        _ = b * ψ u := by rw [h2]
    rw [hCψ, Subgroup.mem_bot] at hbC
    exact hbC
  obtain ⟨c, hcard, M, hM⟩ := exists_block hrp hB''comm hB''r hB''1 htc
  exact not_dvd_card_GL' hr hf hF hcard (hM ▸ orderOf_dvd_natCard M)

theorem not_mem_center_of_orderOf {F : Type*} [Field F] [Fintype F] {n r : ℕ}
    {g : SpecialLinearGroup (Fin (n + 1)) F} (hgr : orderOf g = r)
    (hrq : ¬ r ∣ Fintype.card F - 1) :
    g ∉ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F) := by
  intro hgc
  set e := SpecialLinearGroup.center_equiv_rootsOfUnity' (n := Fin (n + 1)) (R := F) 0
  have h1 : orderOf (e ⟨g, hgc⟩) = r := by
    rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact hgr
  have h2 : orderOf ((e ⟨g, hgc⟩ : rootsOfUnity (Fintype.card (Fin (n + 1))) F) : Fˣ) = r := by
    rw [Subgroup.orderOf_coe]
    exact h1
  have h3 := orderOf_dvd_natCard ((e ⟨g, hgc⟩ : rootsOfUnity (Fintype.card (Fin (n + 1))) F) : Fˣ)
  rw [h2, Nat.card_units, Nat.card_eq_fintype_card] at h3
  exact hrq h3

end Setting

end OrdPRest

@[expose] def GGTwistedPPDInput : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (f n p r : ℕ), Fintype.card K = 2 ^ f → 1 ≤ f → 1 ≤ n →
    p.Prime → ∀ (A : GL (Fin n) K) (c : Kˣ), A ^ p = GeneralLinearGroup.scalar (Fin n) c →
      (∀ μ : Kˣ, μ ^ p ≠ c) → IsPrimitivePrimeDivisor r (f * n) →
        ∃ g : SpecialLinearGroup (Fin n) K, orderOf g = r ∧
          SpecialLinearGroup.toGL g * A = A * SpecialLinearGroup.toGL g

namespace OrdPRest

section Twisted

variable {G : Type} [Group G] [Finite G] {p : ℕ} {Bs G₀ : Subgroup G} {m f : ℕ} {F : Type}
  [Field F] [Fintype F] [CharP F 2] {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}

theorem false_of_twisted (hT : GGTwistedPPDInput)
    (hS : GGSixFusionSetting p Bs G₀ (SpecialLinear.rootDatum m F) .PSL (m + 1) f ψ)
    (h24 : GGTwoLocalRankFour p (Subgroup.normalizer (G₀ : Set G)))
    (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f) (hpF : p ∣ Nat.card F - 1) (hm3 : 3 ≤ m) {b : G}
    (hb : b ∈ Bs) {y : G} (hyM : y ∈ Subgroup.normalizer (G₀ : Set G)) (hyo : orderOf y = p)
    (hy : GGPsiInnerDiag (SpecialLinear.rootDatum m F) ψ y)
    (hnc : ∀ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∉ Bs)
    (hemb : GGCentralizerEmbeds (Subgroup.normalizer (G₀ : Set G)) y b) : False := by
  obtain ⟨⟨-, hrank⟩, ⟨hrange, hker⟩, -, -⟩ := hS.presents
  have hm : 2 ≤ m := hrank
  have hp := hS.prime
  have hF' : Nat.card F = 2 ^ f := by rw [Nat.card_eq_fintype_card, hF]
  have hyp : y ^ p = 1 := hyo ▸ pow_orderOf_eq_one y
  obtain ⟨A, hA⟩ := RootPlaneA.exists_gl_of_psiInnerDiag hm hker hy
  by_cases hroot : ∀ c : Fˣ, A ^ p = GeneralLinearGroup.scalar (Fin (m + 1)) c →
      ∃ μ : Fˣ, μ ^ p = c
  · obtain ⟨s, hs⟩ := exists_conj_mem_centralizer_of_root hS h24 hpF hyp hA hroot
    exact hS.not_conj_mem_centralizer hyp hnc (Subgroup.le_normalizer (hrange ▸ ⟨s, rfl⟩)) hs
  push Not at hroot
  obtain ⟨c, hc, hcμ⟩ := hroot
  have hn6 : f * (m + 1) ≠ 6 := by
    intro h6
    have hf1 : f = 1 := by
      by_contra hf1
      have : 2 * 4 ≤ f * (m + 1) := Nat.mul_le_mul (by omega) (by omega)
      omega
    rw [hF', hf1] at hpF
    exact hp.ne_one (Nat.dvd_one.mp hpF)
  have h2 : 2 ≤ f * (m + 1) :=
    le_trans (by omega : 2 ≤ m + 1) (Nat.le_mul_of_pos_left _ (by omega))
  obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor h2 hn6
  obtain ⟨g, hgr, hgA⟩ := hT F f (m + 1) p r hF hf (by omega) hp A c hc hcμ hr
  have : Fact r.Prime := ⟨hr.prime⟩
  have hfn : 0 < f * (m + 1) := by omega
  have hrq : ¬ r ∣ Fintype.card F - 1 := by
    rw [hF, show 2 ^ f = 2 ^ (f * 1) by rw [mul_one]]
    exact not_dvd_two_pow_sub_one hr hf (by norm_num) (by omega)
  have hg1 : ψ g ≠ 1 := fun h => not_mem_center_of_orderOf hgr hrq (hker h)
  have hψgr : orderOf (ψ g) = r := by
    refine orderOf_eq_prime ?_ hg1
    rw [← map_pow, ← hgr, pow_orderOf_eq_one, map_one]
  have hgy : ψ g ∈ Subgroup.normalizer (G₀ : Set G) ⊓ Subgroup.centralizer {y} := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer (hrange ▸ ⟨g, rfl⟩), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    have h1 : InnerDiagA.conjSL A g = g := by
      apply SpecialLinearGroup.toGL_injective
      rw [RootPlaneA.toGL_conjSL, ← hgA, mul_inv_cancel_right]
    have h3 := hA g
    rw [h1] at h3
    calc x * ψ g = x * (x⁻¹ * ψ g * x) := by rw [h3]
      _ = ψ g * x := by group
  obtain ⟨θ, hθinj, hθC, hθy⟩ := hemb
  have hb1 : b ≠ 1 := by
    intro hb1
    have hyy : y ∈ Subgroup.normalizer (G₀ : Set G) ⊓ Subgroup.centralizer {y} := by
      refine Subgroup.mem_inf.mpr ⟨hyM, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
    have h1 := hθy hyy
    rw [hb1, ← map_one θ] at h1
    have h3 : y = 1 := congrArg Subtype.val (hθinj h1)
    rw [h3, orderOf_one] at hyo
    exact hp.one_lt.ne hyo
  have hθr : orderOf (θ ⟨ψ g, hgy⟩) = r := by
    rw [orderOf_injective θ hθinj, ← Subgroup.orderOf_coe]
    exact hψgr
  obtain ⟨hθM, hθb⟩ := Subgroup.mem_inf.mp (hθC ⟨ψ g, hgy⟩)
  have hcomm : θ ⟨ψ g, hgy⟩ * b = b * θ ⟨ψ g, hgy⟩ :=
    (Subgroup.mem_centralizer_iff.mp hθb b (Set.mem_singleton b)).symm
  exact orderOf_ne_of_commute hS h24 hF hf hpF hr hb hb1 hθM hcomm hθr

end Twisted

end OrdPRest

section Family

theorem ggOrdPOutdiag_PSL_false (hT : GGTwistedPPDInput) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs G₀ : Subgroup G) (n f : ℕ)
      (ψ : (ggU .PSL n f).K →* G),
      GGSixFusionSetting p Bs G₀ (ggU .PSL n f).D .PSL n f ψ →
      GGTwoLocalRankFour p (Subgroup.normalizer (G₀ : Set G)) → GGOutdiagPrimeConfig p .PSL n f →
      ∀ b ∈ Bs, ∀ y ∈ Subgroup.normalizer (G₀ : Set G), orderOf y = p →
        GGPsiInnerDiag (ggU .PSL n f).D ψ y →
        (∀ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∉ Bs) →
        GGCentralizerEmbeds (Subgroup.normalizer (G₀ : Set G)) y b → False := by
  intro G _ _ p Bs G₀ n f ψ hS h24 hcfg b hb y hyM hyo hy hnc hemb
  have hpq : p ∣ 2 ^ f - 1 := by
    rcases hcfg with ⟨-, -, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    all_goals exact absurd h (by decide)
  obtain ⟨⟨hadm, hrank⟩, ⟨hrange, hker⟩, -, -⟩ := hS.presents
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
  have hm : 2 ≤ m := hrank
  have hf : 1 ≤ f := hadm.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | hm3
  · have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
      rw [hrange]
      exact hS.centralizer_eq_bot
    have hBsN : Bs ≤ Subgroup.normalizer (ψ.range : Set G) := by
      rw [hrange]
      exact hS.bstar_le
    exact AutPSL.pslThreeRankInput_holds G f ψ hf hker hCψ p Bs hS.prime hS.ne_two hS.elem
      (hS.pow_four_le h24) hBsN hS.innerDiag
  let : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  have hK : Fintype.card (GaloisField 2 f) = 2 ^ f := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 f (by omega)]
  have hpF : p ∣ Nat.card (GaloisField 2 f) - 1 := by
    rw [GaloisField.card 2 f (by omega)]
    exact hpq
  exact OrdPRest.false_of_twisted (F := GaloisField 2 f) hT hS h24 hK hf hpF hm3 hb hyM hyo hy
    hnc hemb

theorem ggOrdPOutdiagAt_PSL_of_twisted (hT : GGTwistedPPDInput) : GGOrdPOutdiagAt .PSL := by
  intro G _ _ p Bs G₀ n f ψ hS h24 hcfg b hb y hyM hyo hy hnc hemb
  exact (ggOrdPOutdiag_PSL_false hT G p Bs G₀ n f ψ hS h24 hcfg b hb y hyM hyo hy hnc
    hemb).elim

end Family

end CFSG.StandardType
