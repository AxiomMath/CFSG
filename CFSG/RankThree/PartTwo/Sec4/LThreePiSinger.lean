module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseA

public section

namespace CFSG.RankThree.PartTwo.Sec4

open Matrix Polynomial

variable {K : Type} [Field K]

theorem irreducible_X_pow_three_sub_C {ℓ : K} (hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ) :
    Irreducible (X ^ 3 - C ℓ : K[X]) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [natDegree_X_pow_sub_C]
    simp
  · intro μ hμ
    apply hℓ μ
    simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_C] at hμ
    exact sub_eq_zero.mp hμ

variable {y : Matrix (Fin 3) (Fin 3) K} {ℓ : K}

theorem linearIndependent_cyclic (hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ) (hy : y ^ 3 = ℓ • 1)
    {v : Fin 3 → K} (hv : v ≠ 0) : LinearIndependent K ![v, y *ᵥ v, (y ^ 2) *ᵥ v] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hne
  push Not at hne
  set P : K[X] := C (c 0) + C (c 1) * X + C (c 2) * X ^ 2 with hP
  have hP0 : P ≠ 0 := by
    intro h0
    obtain ⟨i, hi⟩ := hne
    have hcoef : ∀ k : Fin 3, P.coeff k = c k := by
      intro k
      fin_cases k <;> simp [hP, coeff_X, coeff_C, coeff_X_pow]
    apply hi
    rw [← hcoef i, h0, coeff_zero]
  have hdeg : P.natDegree < 3 := by
    rw [hP]
    apply lt_of_le_of_lt (natDegree_add_le _ _)
    refine max_lt (lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ ?_)) ?_
    · rw [natDegree_C]; omega
    · exact lt_of_le_of_lt ((natDegree_C_mul_le _ _).trans natDegree_X_le) (by norm_num)
    · exact lt_of_le_of_lt (natDegree_C_mul_X_pow_le _ 2) (by omega)
  have hirr := irreducible_X_pow_three_sub_C hℓ
  have hcop : IsCoprime (X ^ 3 - C ℓ) P := by
    rw [hirr.coprime_iff_not_dvd]
    intro hdvd
    have := natDegree_le_of_dvd hdvd hP0
    rw [natDegree_X_pow_sub_C] at this
    omega
  obtain ⟨A, B, hAB⟩ := hcop
  have hy0 : aeval y (X ^ 3 - C ℓ) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, hy, Algebra.algebraMap_eq_smul_one, sub_self]
  have hPv : aeval y P *ᵥ v = 0 := by
    have := hc
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at this
    rw [hP]
    simp only [map_add, map_mul, aeval_C, aeval_X, map_pow, Algebra.algebraMap_eq_smul_one,
      Matrix.add_mulVec, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact this
  have h1 : aeval y (A * (X ^ 3 - C ℓ) + B * P) = 1 := by rw [hAB, map_one]
  rw [map_add, map_mul, map_mul, hy0, mul_zero, zero_add] at h1
  have hev := congrArg (fun M => M *ᵥ v) h1
  simp only [Matrix.one_mulVec] at hev
  rw [← Matrix.mulVec_mulVec, hPv, Matrix.mulVec_zero] at hev
  exact hv hev.symm

theorem eq_bot_or_eq_top_of_invariant (hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ) (hy : y ^ 3 = ℓ • 1)
    {W : Submodule K (Fin 3 → K)} (hW : ∀ v ∈ W, y *ᵥ v ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨v, hvW, hv⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have hli := linearIndependent_cyclic hℓ hy hv
  have hyv : y *ᵥ v ∈ W := hW v hvW
  have hy2v : (y ^ 2) *ᵥ v ∈ W := by
    rw [sq, ← Matrix.mulVec_mulVec]
    exact hW _ hyv
  have hsp : Submodule.span K (Set.range ![v, y *ᵥ v, (y ^ 2) *ᵥ v]) ≤ W := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hvW
    · exact hyv
    · exact hy2v
  have h3 : Module.finrank K (Submodule.span K (Set.range ![v, y *ᵥ v, (y ^ 2) *ᵥ v])) = 3 := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hle := Submodule.finrank_mono hsp
  rw [h3] at hle
  apply Submodule.eq_top_of_finrank_eq
  have := Submodule.finrank_le W
  rw [Module.finrank_fin_fun] at this ⊢
  omega

@[expose] def companionThree (ℓ : K) : Matrix (Fin 3) (Fin 3) K := !![0, 0, ℓ; 1, 0, 0; 0, 1, 0]

theorem mul_colMat_apply (M : Matrix (Fin 3) (Fin 3) K) (b : Fin 3 → (Fin 3 → K)) (r i : Fin 3) :
    (M * colMat b) r i = (M *ᵥ b i) r := by
  simp [Matrix.mul_apply, colMat, Matrix.mulVec, dotProduct]

theorem mul_colMat_cyclic (hy : y ^ 3 = ℓ • 1) (v : Fin 3 → K) :
    y * colMat ![v, y *ᵥ v, (y ^ 2) *ᵥ v] =
      colMat ![v, y *ᵥ v, (y ^ 2) *ᵥ v] * companionThree ℓ := by
  have h2 : y *ᵥ (y *ᵥ v) = (y ^ 2) *ᵥ v := by rw [Matrix.mulVec_mulVec, sq]
  have h3 : y *ᵥ ((y ^ 2) *ᵥ v) = ℓ • v := by
    rw [Matrix.mulVec_mulVec, ← pow_succ', hy, Matrix.smul_mulVec, Matrix.one_mulVec]
  ext r i
  rw [mul_colMat_apply]
  fin_cases i
  · simp [Matrix.mul_apply, Fin.sum_univ_three, colMat, companionThree]
  · change (y *ᵥ (y *ᵥ v)) r = (colMat ![v, y *ᵥ v, (y ^ 2) *ᵥ v] * companionThree ℓ) r 1
    rw [h2]
    simp [Matrix.mul_apply, Fin.sum_univ_three, colMat, companionThree]
  · change (y *ᵥ ((y ^ 2) *ᵥ v)) r =
      (colMat ![v, y *ᵥ v, (y ^ 2) *ᵥ v] * companionThree ℓ) r 2
    rw [h3]
    simp [Matrix.mul_apply, Fin.sum_univ_three, colMat, companionThree, mul_comm]

theorem det_companionThree (ℓ : K) : (companionThree ℓ).det = ℓ := by
  simp [companionThree, det_fin_three]

theorem det_eq_of_cube (hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ) (hy : y ^ 3 = ℓ • 1) : y.det = ℓ := by
  have hv : (Pi.single 0 1 : Fin 3 → K) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  set P := colMat ![(Pi.single 0 1 : Fin 3 → K), y *ᵥ Pi.single 0 1, (y ^ 2) *ᵥ Pi.single 0 1]
  have hP : IsUnit P := isUnit_colMat (linearIndependent_cyclic hℓ hy hv)
  have hyP := mul_colMat_cyclic hy (Pi.single 0 1 : Fin 3 → K)
  have := congrArg Matrix.det hyP
  rw [det_mul, det_mul, det_companionThree, mul_comm] at this
  exact mul_left_cancel₀ ((Matrix.isUnit_iff_isUnit_det P).mp hP).ne_zero this

theorem commute_iff_eq_poly (hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ) (hy : y ^ 3 = ℓ • 1)
    (M : Matrix (Fin 3) (Fin 3) K) :
    M * y = y * M ↔ ∃ a b c : K, M = a • 1 + b • y + c • y ^ 2 := by
  constructor
  · intro hM
    set v : Fin 3 → K := Pi.single 0 1
    have hv : v ≠ 0 := by
      intro h
      have := congrFun h 0
      simp [v] at this
    have hli := linearIndependent_cyclic hℓ hy hv
    set B := basisOfLinearIndependentOfCardEqFinrank hli (by simp)
    set a := B.repr (M *ᵥ v) 0
    set b := B.repr (M *ᵥ v) 1
    set c := B.repr (M *ᵥ v) 2
    have hMv : M *ᵥ v = a • v + b • (y *ᵥ v) + c • ((y ^ 2) *ᵥ v) := by
      have h := (B.sum_repr (M *ᵥ v)).symm
      rw [Fin.sum_univ_three] at h
      have hB : ∀ i, B i = ![v, y *ᵥ v, (y ^ 2) *ᵥ v] i := fun i => by
        rw [coe_basisOfLinearIndependentOfCardEqFinrank]
      rw [hB, hB, hB] at h
      simpa using h
    set N := a • (1 : Matrix (Fin 3) (Fin 3) K) + b • y + c • y ^ 2
    have hNv : N *ᵥ v = M *ᵥ v := by
      rw [hMv]
      simp only [N, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    have hNy : N * y = y * N := by
      simp only [N, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, Matrix.mul_one, ← pow_succ, ← pow_succ']
    have hagree : ∀ k : ℕ, M *ᵥ ((y ^ k) *ᵥ v) = N *ᵥ ((y ^ k) *ᵥ v) := by
      intro k
      have hMk : M * y ^ k = y ^ k * M := (Commute.pow_right (show Commute M y from hM) k).eq
      have hNk : N * y ^ k = y ^ k * N := (Commute.pow_right (show Commute N y from hNy) k).eq
      rw [Matrix.mulVec_mulVec, hMk, ← Matrix.mulVec_mulVec, ← hNv, Matrix.mulVec_mulVec,
        ← hNk, ← Matrix.mulVec_mulVec]
    refine ⟨a, b, c, ?_⟩
    have hcol : M * colMat ![v, y *ᵥ v, (y ^ 2) *ᵥ v] =
        N * colMat ![v, y *ᵥ v, (y ^ 2) *ᵥ v] := by
      ext r i
      rw [mul_colMat_apply, mul_colMat_apply]
      have h0 := hagree 0
      have h1 := hagree 1
      have h2 := hagree 2
      simp only [pow_zero, Matrix.one_mulVec, pow_one] at h0 h1 h2
      fin_cases i
      · exact congrFun h0 r
      · exact congrFun h1 r
      · exact congrFun h2 r
    exact (isUnit_colMat hli).mul_left_inj.mp hcol
  · rintro ⟨a, b, c, rfl⟩
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, ← pow_succ, ← pow_succ']

section CubeField

variable (ℓ) in
abbrev cubeField : Type := AdjoinRoot (X ^ 3 - C ℓ : K[X])

theorem aeval_cube_eq_zero (hy : y ^ 3 = ℓ • 1) : aeval y (X ^ 3 - C ℓ : K[X]) = 0 := by
  rw [map_sub, map_pow, aeval_X, aeval_C, hy, Algebra.algebraMap_eq_smul_one, sub_self]

@[expose] noncomputable def cubeHom (hy : y ^ 3 = ℓ • 1) :
    cubeField ℓ →ₐ[K] Matrix (Fin 3) (Fin 3) K :=
  Ideal.Quotient.liftₐ (Ideal.span {(X ^ 3 - C ℓ : K[X])}) (aeval y) fun a ha => by
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, aeval_cube_eq_zero hy, mul_zero]

theorem cubeHom_mk (hy : y ^ 3 = ℓ • 1) (g : K[X]) :
    cubeHom hy (AdjoinRoot.mk _ g) = aeval y g :=
  rfl

theorem cubeHom_root (hy : y ^ 3 = ℓ • 1) : cubeHom hy (AdjoinRoot.root _) = y := by
  rw [AdjoinRoot.root, cubeHom_mk, aeval_X]

theorem monic_cube (ℓ : K) : (X ^ 3 - C ℓ : K[X]).Monic :=
  monic_X_pow_sub_C ℓ (by norm_num)

theorem natDegree_cube (ℓ : K) : (X ^ 3 - C ℓ : K[X]).natDegree = 3 :=
  natDegree_X_pow_sub_C

theorem card_cubeField [Finite K] (ℓ : K) : Nat.card (cubeField ℓ) = Nat.card K ^ 3 := by
  set pb := AdjoinRoot.powerBasis' (monic_cube ℓ)
  have hdim : pb.dim = 3 := natDegree_cube ℓ
  rw [Nat.card_congr pb.basis.equivFun.toEquiv, Nat.card_fun, Nat.card_fin, hdim]

theorem mem_range_cubeHom (hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ) (hy : y ^ 3 = ℓ • 1)
    (M : Matrix (Fin 3) (Fin 3) K) : (∃ e, cubeHom hy e = M) ↔ M * y = y * M := by
  constructor
  · rintro ⟨e, rfl⟩
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective e
    rw [cubeHom_mk]
    calc aeval y g * y = aeval y g * aeval y X := by rw [aeval_X]
      _ = aeval y (g * X) := (map_mul _ _ _).symm
      _ = aeval y (X * g) := by rw [mul_comm]
      _ = y * aeval y g := by rw [map_mul, aeval_X]
  · intro hM
    obtain ⟨a, b, c, rfl⟩ := (commute_iff_eq_poly hℓ hy M).mp hM
    refine ⟨AdjoinRoot.mk _ (C a + C b * X + C c * X ^ 2), ?_⟩
    rw [cubeHom_mk]
    simp only [map_add, map_mul, aeval_C, aeval_X, map_pow, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul]

theorem cubeHom_injective (hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ) (hy : y ^ 3 = ℓ • 1) :
    Function.Injective (cubeHom hy) := by
  have : Fact (Irreducible (X ^ 3 - C ℓ : K[X])) := ⟨irreducible_X_pow_three_sub_C hℓ⟩
  exact (cubeHom hy).toRingHom.injective

end CubeField

section Centralizer

variable {yG : GL (Fin 3) K}

@[expose] noncomputable def cubeUnitsHom (hy : (yG : Matrix (Fin 3) (Fin 3) K) ^ 3 = ℓ • 1) :
    (cubeField ℓ)ˣ →* GL (Fin 3) K :=
  Units.map (cubeHom hy).toMonoidHom

theorem coe_cubeUnitsHom (hy : (yG : Matrix (Fin 3) (Fin 3) K) ^ 3 = ℓ • 1) (e : (cubeField ℓ)ˣ) :
    ((cubeUnitsHom hy e : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      cubeHom hy (e : cubeField ℓ) :=
  rfl

theorem cubeUnitsHom_injective (hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ)
    (hy : (yG : Matrix (Fin 3) (Fin 3) K) ^ 3 = ℓ • 1) : Function.Injective (cubeUnitsHom hy) := by
  intro e e' h
  apply Units.ext
  apply cubeHom_injective hℓ hy
  have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h
  simpa [coe_cubeUnitsHom] using this

theorem range_cubeUnitsHom (hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ)
    (hy : (yG : Matrix (Fin 3) (Fin 3) K) ^ 3 = ℓ • 1) :
    (cubeUnitsHom hy).range = Subgroup.centralizer {yG} := by
  have : Fact (Irreducible (X ^ 3 - C ℓ : K[X])) := ⟨irreducible_X_pow_three_sub_C hℓ⟩
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨e, rfl⟩
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_cubeUnitsHom]
    exact ((mem_range_cubeHom hℓ hy _).mp ⟨_, rfl⟩)
  · intro hg
    have hgm : (g : Matrix (Fin 3) (Fin 3) K) * yG = yG * g := by
      have := congrArg Units.val hg
      simpa using this
    obtain ⟨e, he⟩ := (mem_range_cubeHom hℓ hy _).mpr hgm
    have he0 : e ≠ 0 := by
      rintro rfl
      rw [map_zero] at he
      have := congrArg Matrix.det he
      rw [det_zero, eq_comm] at this
      exact (g.isUnit.map (Matrix.detMonoidHom : Matrix (Fin 3) (Fin 3) K →* K)).ne_zero this
    refine ⟨Units.mk0 e he0, Units.ext ?_⟩
    rw [coe_cubeUnitsHom, Units.val_mk0, he]

theorem centralizer_cyclic_card [Finite K] (hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ)
    (hy : (yG : Matrix (Fin 3) (Fin 3) K) ^ 3 = ℓ • 1) :
    IsCyclic (Subgroup.centralizer {yG}) ∧
      Nat.card (Subgroup.centralizer {yG}) = Nat.card K ^ 3 - 1 := by
  have : Fact (Irreducible (X ^ 3 - C ℓ : K[X])) := ⟨irreducible_X_pow_three_sub_C hℓ⟩
  have : Finite (cubeField ℓ) := by
    have := card_cubeField ℓ
    exact Nat.finite_of_card_ne_zero (by
      rw [this]
      exact pow_ne_zero _ Nat.card_pos.ne')
  set e : (cubeField ℓ)ˣ ≃* Subgroup.centralizer {yG} :=
    (MonoidHom.ofInjective (cubeUnitsHom_injective hℓ hy)).trans
      (MulEquiv.subgroupCongr (range_cubeUnitsHom hℓ hy))
  refine ⟨isCyclic_of_surjective e.toMonoidHom e.surjective, ?_⟩
  rw [← Nat.card_congr e.toEquiv, Nat.card_units, card_cubeField]

end Centralizer

theorem eq_top_of_cube_le {G : Type*} [Group G] [IsCyclic G] {R : Subgroup G}
    (hcube : ∀ g : G, g ^ 3 ∈ R) {g₀ : G} (hg₀R : g₀ ∈ R) (hg₀ : ∀ h : G, h ^ 3 ≠ g₀) :
    R = ⊤ := by
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hγ g₀)
  have h3k : ¬ (3 : ℤ) ∣ k := by
    rintro ⟨m, rfl⟩
    apply hg₀ (γ ^ m)
    rw [← hk, ← zpow_natCast, ← _root_.zpow_mul, mul_comm]
    rfl
  have hcop : IsCoprime k 3 := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have hd : Int.gcd k 3 ∣ 3 := by
      have := Int.gcd_dvd_right (a := k) (b := 3)
      exact_mod_cast this
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact h
    · exfalso
      apply h3k
      have := Int.gcd_dvd_left (a := k) (b := 3)
      rw [h] at this
      exact_mod_cast this
  obtain ⟨a, b, hab⟩ := hcop
  rw [eq_top_iff]
  intro g _
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hγ g)
  have hγR : γ ∈ R := by
    have : γ = (γ ^ k) ^ a * (γ ^ (3 : ℤ)) ^ b := by
      rw [← _root_.zpow_mul, ← _root_.zpow_mul, ← _root_.zpow_add, mul_comm k a,
        mul_comm (3 : ℤ) b, hab, zpow_one]
    rw [this]
    refine mul_mem (zpow_mem (hk ▸ hg₀R) a) (zpow_mem ?_ b)
    rw [show (γ ^ (3 : ℤ)) = γ ^ (3 : ℕ) by norm_cast]
    exact hcube γ
  exact zpow_mem hγR n

section DetHom

variable {p f : ℕ} {π : Bool}

open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank

theorem det_mem_rootsOfUnity (hK : PiField π p f K) {g : GL (Fin 3) K}
    (hg : g ∈ glPi π 3 (p ^ f) K) :
    GeneralLinearGroup.det g ∈ rootsOfUnity (qSubPi π (p ^ f)) K := by
  cases π
  · have h := hK.unitary
    have hu := (mem_glPi_false h).mp hg
    have := congrArg Matrix.det hu
    rw [det_mul, det_transpose, show ((g : Matrix (Fin 3) (Fin 3) K).map h.bar).det =
      h.bar (g : Matrix (Fin 3) (Fin 3) K).det from (RingHom.map_det h.bar _).symm,
      det_one, h.bar_apply, ← pow_succ] at this
    rw [mem_rootsOfUnity]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, GeneralLinearGroup.val_det_apply, Units.val_one]
    exact this
  · have := hK.finite
    exact mem_rootsOfUnity_of_card (by simpa [piCard] using hK.card) _

@[expose] noncomputable def detCent (hK : PiField π p f K) (y : GL (Fin 3) K) :
    ↥(glPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y}) →* rootsOfUnity (qSubPi π (p ^ f)) K where
  toFun g := ⟨GeneralLinearGroup.det (g : GL (Fin 3) K),
    det_mem_rootsOfUnity hK (Subgroup.mem_inf.mp g.2).1⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g g' := Subtype.ext (by simp)

theorem range_detCent (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {y : GL (Fin 3) K} (hyH : y ∈ glPi π 3 (p ^ f) K) {ℓ : K} (hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ)
    (hy : (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = ℓ • 1) : (detCent hK y).range = ⊤ := by
  set H := glPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y}
  have hyy : y ∈ H := Subgroup.mem_inf.mpr ⟨hyH, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have : NeZero (qSubPi π (p ^ f)) := ⟨qSubPi_ne_zero hK hq⟩
  have := rootsOfUnity.isCyclic K (qSubPi π (p ^ f))
  refine eq_top_of_cube_le (g₀ := detCent hK y ⟨y, hyy⟩) (fun t => ?_) ⟨_, rfl⟩ fun t ht => ?_
  · have hsc : GeneralLinearGroup.scalar (Fin 3) (t : Kˣ) ∈ H := by
      refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.mem_centralizer_singleton_iff.mpr
        (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar _ y).eq.symm⟩
      cases π
      · rw [scalar_mem_glPi_false_iff hK.unitary]
        have := (mem_rootsOfUnity _ _).mp t.2
        have := congrArg Units.val this
        rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
      · exact mem_glPi_true _ _
    refine ⟨⟨_, hsc⟩, Subtype.ext (Units.ext ?_)⟩
    simp only [detCent, MonoidHom.coe_mk, OneHom.coe_mk, GeneralLinearGroup.val_det_apply,
      SubgroupClass.coe_pow, Units.val_pow_eq_pow_val]
    exact det_scalar _
  · apply hℓ ((t : Kˣ) : K)
    have := congrArg (fun t : rootsOfUnity _ K => ((t : Kˣ) : K)) ht
    simp only [detCent, MonoidHom.coe_mk, OneHom.coe_mk, GeneralLinearGroup.val_det_apply,
      SubgroupClass.coe_pow, Units.val_pow_eq_pow_val] at this
    rw [this]
    exact det_eq_of_cube hℓ hy

theorem card_centralizer_slPi_mul (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {y : GL (Fin 3) K} (hyH : y ∈ glPi π 3 (p ^ f) K) {ℓ : K} (hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ)
    (hy : (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = ℓ • 1) :
    Nat.card ↥(slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y}) * qSubPi π (p ^ f) =
      Nat.card ↥(glPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y}) := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  set H := glPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y}
  have hker : (detCent hK y).ker =
      (slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y}).subgroupOf H := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_slPi_iff hπ]
    constructor
    · intro h1
      have := congrArg (fun t : rootsOfUnity _ K => ((t : Kˣ) : K)) h1
      simp only [detCent, MonoidHom.coe_mk, OneHom.coe_mk, GeneralLinearGroup.val_det_apply,
        OneMemClass.coe_one, Units.val_one] at this
      exact ⟨⟨(Subgroup.mem_inf.mp g.2).1, this⟩, (Subgroup.mem_inf.mp g.2).2⟩
    · rintro ⟨⟨-, hdet⟩, -⟩
      apply Subtype.ext
      apply Units.ext
      simp only [detCent, MonoidHom.coe_mk, OneHom.coe_mk, GeneralLinearGroup.val_det_apply,
        OneMemClass.coe_one, Units.val_one]
      exact hdet
  have h1 := Subgroup.card_mul_index (detCent hK y).ker
  rw [Subgroup.index_ker, range_detCent hK hq hyH hℓ hy, Subgroup.card_top,
    card_rootsOfUnity_qSubPi hK hq, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_inf_right _ (slPi_le_glPi hπ))).toEquiv]
    at h1
  exact h1

end DetHom

section W

variable {p f : ℕ} {π : Bool}

open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank

theorem diag_mul_companion {τ : K} (hτ : τ ^ 3 = 1) (ℓ : K) :
    diagonal ![1, τ, τ ^ 2] * companionThree ℓ =
      τ • (companionThree ℓ * diagonal ![1, τ, τ ^ 2]) := by
  have h3 : τ * τ ^ 2 = 1 := by rw [← pow_succ']; exact hτ
  ext i j
  rw [Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [companionThree] <;>
    first | ring1 | linear_combination -ℓ * hτ

theorem exists_w_linear {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ)
    {y : Matrix (Fin 3) (Fin 3) K} (hy : y ^ 3 = ℓ • 1) :
    ∃ w : GL (Fin 3) K, (w : Matrix (Fin 3) (Fin 3) K).det = 1 ∧ w ^ 3 = 1 ∧
      (w : Matrix (Fin 3) (Fin 3) K) * y = τ • (y * w) := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  set v : Fin 3 → K := Pi.single 0 1
  have hv : v ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [v] at this
  set P := colMat ![v, y *ᵥ v, (y ^ 2) *ᵥ v]
  have hP : IsUnit P := isUnit_colMat (linearIndependent_cyclic hℓ hy hv)
  have hyP := mul_colMat_cyclic hy v
  set u : Kˣ := Units.mk0 τ hτ0
  set D := diagUnits 1 u (u ^ 2)
  have hD : (D : Matrix (Fin 3) (Fin 3) K) = diagonal ![1, τ, τ ^ 2] := by
    rw [coe_diagUnits]
    simp [u]
  set w := hP.unit * D * hP.unit⁻¹
  refine ⟨w, ?_, ?_, ?_⟩
  · have hPP : P.det * ((hP.unit⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
      rw [← det_mul, IsUnit.mul_val_inv, det_one]
    rw [Units.val_mul, Units.val_mul, det_mul, det_mul, IsUnit.unit_spec]
    calc P.det * (D : Matrix (Fin 3) (Fin 3) K).det *
          ((hP.unit⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det
        = (D : Matrix (Fin 3) (Fin 3) K).det *
          (P.det * ((hP.unit⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det) := by ring
      _ = 1 := by
        rw [hPP, mul_one, hD, det_diagonal, Fin.prod_univ_three]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons, one_mul]
        rw [← pow_succ']
        exact hτ
  · have hD3 : D ^ 3 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hD, Matrix.diagonal_pow, Units.val_one, ← diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp [← pow_mul, hτ]
      calc τ ^ (2 * 3) = (τ ^ 3) ^ 2 := by ring
        _ = 1 := by rw [hτ, one_pow]
    rw [show w ^ 3 = hP.unit * D ^ 3 * hP.unit⁻¹ by
      simp only [w, pow_succ, pow_zero, one_mul]; group, hD3, mul_one, mul_inv_cancel]
  ·
    have hy' : y = P * companionThree ℓ * (hP.unit⁻¹ : GL (Fin 3) K) := by
      calc y = y * (P * (hP.unit⁻¹ : GL (Fin 3) K)) := by rw [IsUnit.mul_val_inv, Matrix.mul_one]
        _ = (y * P) * (hP.unit⁻¹ : GL (Fin 3) K) := by rw [Matrix.mul_assoc]
        _ = P * companionThree ℓ * (hP.unit⁻¹ : GL (Fin 3) K) := by rw [hyP]
    have hPinv : ((hP.unit⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * P = 1 :=
      IsUnit.val_inv_mul hP
    simp only [w, Units.val_mul, IsUnit.unit_spec]
    rw [hy', hD]
    calc P * diagonal ![1, τ, τ ^ 2] * ↑hP.unit⁻¹ * (P * companionThree ℓ * ↑hP.unit⁻¹)
        = P * (diagonal ![1, τ, τ ^ 2] * (↑hP.unit⁻¹ * P) * companionThree ℓ) * ↑hP.unit⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = P * (diagonal ![1, τ, τ ^ 2] * companionThree ℓ) * ↑hP.unit⁻¹ := by
          rw [hPinv, Matrix.mul_one]
      _ = τ • (P * (companionThree ℓ * diagonal ![1, τ, τ ^ 2]) * ↑hP.unit⁻¹) := by
          rw [diag_mul_companion hτ, Matrix.mul_smul, Matrix.smul_mul]
      _ = τ • (P * companionThree ℓ * ↑hP.unit⁻¹ * (P * diagonal ![1, τ, τ ^ 2] *
            ↑hP.unit⁻¹)) := by
          congr 1
          rw [show P * companionThree ℓ * ↑hP.unit⁻¹ * (P * diagonal ![1, τ, τ ^ 2] *
            ↑hP.unit⁻¹) = P * companionThree ℓ * (↑hP.unit⁻¹ * P) * diagonal ![1, τ, τ ^ 2] *
              ↑hP.unit⁻¹ by simp only [Matrix.mul_assoc], hPinv, Matrix.mul_one]
          simp only [Matrix.mul_assoc]

@[expose] def cmat (ℓ a b c : K) : Matrix (Fin 3) (Fin 3) K :=
  !![a, c * ℓ, b * ℓ; b, a, c * ℓ; c, b, a]

theorem cmat_eq (ℓ a b c : K) :
    cmat ℓ a b c = a • 1 + b • companionThree ℓ + c • companionThree ℓ ^ 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cmat, companionThree, sq, mul_comm]

theorem det_cmat (ℓ a b c : K) :
    (cmat ℓ a b c).det = a ^ 3 + ℓ * b ^ 3 + ℓ ^ 2 * c ^ 3 - 3 * ℓ * a * b * c := by
  simp [cmat, det_fin_three]
  ring

theorem diag_cmat_pow_three {τ : K} (hs : 1 + τ + τ ^ 2 = 0) (ℓ a b c : K) :
    (diagonal ![1, τ, τ ^ 2] * cmat ℓ a b c) ^ 3 =
      (a ^ 3 + ℓ * b ^ 3 + ℓ ^ 2 * c ^ 3 - 3 * ℓ * a * b * c) • (1 : Matrix (Fin 3) (Fin 3) K) := by
  rw [pow_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cmat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply]
  · linear_combination (a*b*c*ℓ*τ^2 - a*b*c*ℓ*τ + 3*a*b*c*ℓ + b^3*ℓ*τ - b^3*ℓ +
      c^3*ℓ^2*τ - c^3*ℓ^2) * hs
  · linear_combination (a^2*c*ℓ + a*b^2*ℓ*τ^2 + b*c^2*ℓ^2*τ) * hs
  · linear_combination (a^2*b*ℓ*τ^2 - a^2*b*ℓ*τ + a^2*b*ℓ + a*c^2*ℓ^2*τ + b^2*c*ℓ^2*τ) * hs
  · linear_combination (a^2*b*τ + a*c^2*ℓ*τ^3 + b^2*c*ℓ*τ^2) * hs
  · linear_combination (a^3*τ - a^3 + a*b*c*ℓ*τ^3 + a*b*c*ℓ*τ^2 - 2*a*b*c*ℓ*τ + 3*a*b*c*ℓ +
      b^3*ℓ*τ - b^3*ℓ + c^3*ℓ^2*τ - c^3*ℓ^2) * hs
  · linear_combination (a^2*c*ℓ*τ^3 + a*b^2*ℓ*τ + b*c^2*ℓ^2*τ^2) * hs
  · linear_combination (a^2*c*τ^4 - a^2*c*τ^3 + a^2*c*τ^2 + a*b^2*τ^3 + b*c^2*ℓ*τ^3) * hs
  · linear_combination (a^2*b*τ^4 + a*c^2*ℓ*τ^2 + b^2*c*ℓ*τ^3) * hs
  · linear_combination (a^3*τ^4 - a^3*τ^3 + a^3*τ - a^3 + 2*a*b*c*ℓ*τ^3 + a*b*c*ℓ*τ^2 -
      3*a*b*c*ℓ*τ + 3*a*b*c*ℓ + b^3*ℓ*τ - b^3*ℓ + c^3*ℓ^2*τ - c^3*ℓ^2) * hs

theorem companionThree_pow_three (ℓ : K) : companionThree ℓ ^ 3 = ℓ • 1 := by
  rw [pow_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [companionThree, Matrix.mul_apply, Fin.sum_univ_three]

theorem exists_eq_diag_cmat {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ)
    {G : Matrix (Fin 3) (Fin 3) K} (hG : G * companionThree ℓ = τ • (companionThree ℓ * G)) :
    ∃ a b c : K, G = diagonal ![1, τ, τ ^ 2] * cmat ℓ a b c := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  set D := diagonal ![(1 : K), τ, τ ^ 2]
  set D' := diagonal ![(1 : K), τ ^ 2, τ]
  have hDD' : D * D' = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [← pow_succ', ← pow_succ, hτ]
  have hD'D : D' * D = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [← pow_succ', ← pow_succ, hτ]
  have hDC := diag_mul_companion hτ ℓ
  have hCD' : companionThree ℓ * D' = τ • (D' * companionThree ℓ) := by
    calc companionThree ℓ * D' = D' * (D * companionThree ℓ) * D' := by
          rw [← Matrix.mul_assoc, hD'D, Matrix.one_mul]
      _ = D' * (τ • (companionThree ℓ * D)) * D' := by rw [hDC]
      _ = τ • (D' * companionThree ℓ * (D * D')) := by
          rw [Matrix.mul_smul, Matrix.smul_mul]
          simp only [Matrix.mul_assoc]
      _ = τ • (D' * companionThree ℓ) := by rw [hDD', Matrix.mul_one]
  set M := D' * G
  have hM : M * companionThree ℓ = companionThree ℓ * M := by
    calc M * companionThree ℓ = D' * (G * companionThree ℓ) := by rw [Matrix.mul_assoc]
      _ = τ • (D' * companionThree ℓ * G) := by
          rw [hG, Matrix.mul_smul, Matrix.mul_assoc]
      _ = companionThree ℓ * M := by
          rw [show companionThree ℓ * M = (companionThree ℓ * D') * G by
            simp only [M, Matrix.mul_assoc], hCD', Matrix.smul_mul]
  obtain ⟨a, b, c, habc⟩ :=
    (commute_iff_eq_poly hℓ (companionThree_pow_three ℓ) M).mp hM
  refine ⟨a, b, c, ?_⟩
  rw [cmat_eq, ← habc]
  calc G = (D * D') * G := by rw [hDD', Matrix.one_mul]
    _ = D * M := by rw [Matrix.mul_assoc]

theorem pow_three_eq_det_smul_of_twisted {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    (hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ) {G : Matrix (Fin 3) (Fin 3) K}
    (hG : G * companionThree ℓ = τ • (companionThree ℓ * G)) : G ^ 3 = G.det • 1 := by
  obtain ⟨a, b, c, rfl⟩ := exists_eq_diag_cmat hτ hτ1 hℓ hG
  rw [diag_cmat_pow_three (one_add_tau_add_sq hτ hτ1), det_mul, det_diagonal, det_cmat,
    Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, one_mul]
  rw [← pow_succ', hτ, one_mul]

theorem pow_three_eq_det_smul {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ)
    {y : Matrix (Fin 3) (Fin 3) K} (hy : y ^ 3 = ℓ • 1) {g : Matrix (Fin 3) (Fin 3) K}
    (hg : g * y = τ • (y * g)) : g ^ 3 = g.det • 1 := by
  set v : Fin 3 → K := Pi.single 0 1
  have hv : v ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [v] at this
  set P := colMat ![v, y *ᵥ v, (y ^ 2) *ᵥ v]
  have hP : IsUnit P := isUnit_colMat (linearIndependent_cyclic hℓ hy hv)
  set Pi := ((hP.unit⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  have hPiP : Pi * P = 1 := IsUnit.val_inv_mul hP
  have hPPi : P * Pi = 1 := IsUnit.mul_val_inv hP
  have hyP := mul_colMat_cyclic hy v
  have hC : companionThree ℓ = Pi * y * P := by
    rw [Matrix.mul_assoc, hyP, ← Matrix.mul_assoc, hPiP, Matrix.one_mul]
  set G := Pi * g * P
  have hG : G * companionThree ℓ = τ • (companionThree ℓ * G) := by
    rw [hC]
    calc Pi * g * P * (Pi * y * P) = Pi * (g * y) * P := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc P Pi, hPPi, Matrix.one_mul]
      _ = τ • (Pi * (y * g) * P) := by rw [hg, Matrix.mul_smul, Matrix.smul_mul]
      _ = τ • (Pi * y * P * (Pi * g * P)) := by
          congr 1
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc P Pi, hPPi, Matrix.one_mul]
  have h3 := pow_three_eq_det_smul_of_twisted hτ hτ1 hℓ hG
  have hgG : g = P * G * Pi := by
    simp only [G, Matrix.mul_assoc]
    rw [hPPi, Matrix.mul_one, ← Matrix.mul_assoc, hPPi, Matrix.one_mul]
  have hdet' : (P * G * Pi).det = G.det := by
    rw [det_mul, det_mul, show P.det * G.det * Pi.det = G.det * (P.det * Pi.det) by ring,
      ← det_mul, hPPi, det_one, mul_one]
  rw [hgG, show (P * G * Pi) ^ 3 = P * G ^ 3 * Pi by
    simp only [pow_three, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Pi P, hPiP, Matrix.one_mul, ← Matrix.mul_assoc Pi P, hPiP,
      Matrix.one_mul], h3, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPPi, hdet']

theorem cube_root_cases {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {c : K} (hc : c ^ 3 = 1) :
    c = 1 ∨ c = τ ∨ c = τ ^ 2 := by
  have hs := one_add_tau_add_sq hτ hτ1
  have h : (c - 1) * (c - τ) * (c - τ ^ 2) = 0 := by
    linear_combination hc - c ^ 2 * hs + c * τ * hs - hτ
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h))

end W

section Structure

variable {p f : ℕ} {π : Bool}

open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank

theorem scalar_mem_slPi_of_cube (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {ζ : Kˣ}
    (hζ : (ζ : K) ^ 3 = 1) : GeneralLinearGroup.scalar (Fin 3) ζ ∈ slPi π 3 (p ^ f) K := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  rw [mem_slPi_iff hπ, det_scalar]
  refine ⟨?_, hζ⟩
  cases π
  · rw [scalar_mem_glPi_false_iff hK.unitary]
    exact pow_succ_eq_one_of_modThree hq hζ
  · exact mem_glPi_true _ _

theorem irreducible_centMod_structure (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {ℓ : K} (hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ)
    {y : GL (Fin 3) K} (hy : (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = ℓ • 1)
    {w : GL (Fin 3) K} (hwL : w ∈ slPi π 3 (p ^ f) K)
    (hwy : (w : Matrix (Fin 3) (Fin 3) K) * y = τ • ((y : Matrix (Fin 3) (Fin 3) K) * w)) :
    orderOf w = 3 ∧ w ∉ slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y} ∧
      centMod (slPi π 3 (p ^ f) K) y =
        (slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y}) ⊔ Subgroup.zpowers w ∧
      Nat.card ↥(slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer ({y, w} : Set (GL (Fin 3) K))) = 3 := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  set τu : Kˣ := Units.mk0 τ hτ0
  set sτ := GeneralLinearGroup.scalar (Fin 3) τu
  have hsτm : (sτ : Matrix (Fin 3) (Fin 3) K) = τ • 1 := by
    rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
    rfl
  have hwdet : (w : Matrix (Fin 3) (Fin 3) K).det = 1 := ((mem_slPi_iff hπ).mp hwL).2
  have hwyG : w * y = sτ * y * w := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, hwy, hsτm, Matrix.smul_mul, Matrix.one_mul,
      Matrix.smul_mul]
  have hconj : w * y * w⁻¹ = sτ * y := by rw [hwyG, mul_inv_cancel_right]
  have hw3 : w ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, pow_three_eq_det_smul hτ hτ1 hℓ hy hwy, hwdet, one_smul,
      Units.val_one]
  have hyunit : IsUnit (y : Matrix (Fin 3) (Fin 3) K) := y.isUnit
  have hwC : w ∉ slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y} := by
    intro hw
    have hc := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hw).2
    have hcm := congrArg Units.val hc
    simp only [Units.val_mul] at hcm
    rw [hwy] at hcm
    have h0 : (1 - τ) • ((y : Matrix (Fin 3) (Fin 3) K) * w) = 0 := by
      rw [sub_smul, one_smul, hcm, sub_self]
    rcases smul_eq_zero.mp h0 with h | h
    · exact hτ1 (sub_eq_zero.mp h).symm
    · have := congrArg Matrix.det h
      rw [det_mul, det_zero, hwdet, mul_one] at this
      exact ((Matrix.isUnit_iff_isUnit_det _).mp hyunit).ne_zero this
  have hw1 : w ≠ 1 := fun h => hwC (by rw [h]; exact one_mem _)
  have hord : orderOf w = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hw3 hw1
  refine ⟨hord, hwC, ?_, ?_⟩
  ·
    apply le_antisymm
    · intro l hl
      obtain ⟨hlL, z, ⟨c, rfl⟩, hz⟩ := mem_centMod_iff_scalar.mp hl
      have hc3 : (c : K) ^ 3 = 1 := by
        have h1 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K).det) hz
        simp only [Units.val_mul, det_mul, det_scalar] at h1
        have hli : (l : Matrix (Fin 3) (Fin 3) K).det *
            ((l⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
          rw [← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one]
        have hy0 := ((Matrix.isUnit_iff_isUnit_det _).mp hyunit).ne_zero
        have : (y : Matrix (Fin 3) (Fin 3) K).det * 1 =
            (y : Matrix (Fin 3) (Fin 3) K).det * (c : K) ^ 3 := by
          calc (y : Matrix (Fin 3) (Fin 3) K).det * 1
              = (y : Matrix (Fin 3) (Fin 3) K).det * ((l : Matrix (Fin 3) (Fin 3) K).det *
                ((l⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det) := by rw [hli]
            _ = (l : Matrix (Fin 3) (Fin 3) K).det * (y : Matrix (Fin 3) (Fin 3) K).det *
                ((l⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det := by ring
            _ = (c : K) ^ 3 * (y : Matrix (Fin 3) (Fin 3) K).det := h1
            _ = (y : Matrix (Fin 3) (Fin 3) K).det * (c : K) ^ 3 := by ring
        exact (mul_left_cancel₀ hy0 this).symm
      have hstep : ∀ m : GL (Fin 3) K, m ∈ slPi π 3 (p ^ f) K → m * y * m⁻¹ = y →
          m ∈ (slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y}) := by
        intro m hm hmy
        refine Subgroup.mem_inf.mpr ⟨hm, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        calc m * y = m * y * m⁻¹ * m := by group
          _ = y * m := by rw [hmy]
      have hsc : ∀ g : GL (Fin 3) K, g * sτ = sτ * g := fun g =>
        (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar τu g).eq
      have hcen : ∀ (g X : GL (Fin 3) K), g⁻¹ * (sτ * X) * g = sτ * (g⁻¹ * X * g) := by
        intro g X
        calc g⁻¹ * (sτ * X) * g = (g⁻¹ * sτ) * X * g := by group
          _ = (sτ * g⁻¹) * X * g := by rw [hsc g⁻¹]
          _ = sτ * (g⁻¹ * X * g) := by group
      have hwinv : w⁻¹ * y * w = sτ⁻¹ * y := by
        have h1 : y = sτ⁻¹ * (w * y * w⁻¹) := by rw [hconj, ← mul_assoc, inv_mul_cancel, one_mul]
        have h2 : w⁻¹ * (sτ * (w⁻¹ * y * w)) * w = sτ * (w⁻¹ * (w⁻¹ * y * w) * w) := hcen w _
        calc w⁻¹ * y * w = sτ⁻¹ * (sτ * (w⁻¹ * y * w)) := by group
          _ = sτ⁻¹ * (w⁻¹ * (sτ * y) * w) := by rw [hcen]
          _ = sτ⁻¹ * (w⁻¹ * (w * y * w⁻¹) * w) := by rw [hconj]
          _ = sτ⁻¹ * y := by group
      rcases cube_root_cases hτ hτ1 hc3 with h | h | h
      · have hc1 : c = 1 := Units.ext h
        subst hc1
        rw [map_one, one_mul] at hz
        exact Subgroup.mem_sup_left (hstep l hlL hz)
      · have hcτ : c = τu := Units.ext h
        subst hcτ
        have hm : w⁻¹ * l ∈ slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y} := by
          refine hstep _ (mul_mem (inv_mem hwL) hlL) ?_
          calc w⁻¹ * l * y * (w⁻¹ * l)⁻¹ = w⁻¹ * (l * y * l⁻¹) * w := by group
            _ = w⁻¹ * (sτ * y) * w := by rw [hz]
            _ = sτ * (w⁻¹ * y * w) := hcen w y
            _ = y := by rw [hwinv, ← mul_assoc, mul_inv_cancel, one_mul]
        have : l = w * (w⁻¹ * l) := by group
        rw [this]
        exact mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers w)) (Subgroup.mem_sup_left hm)
      · have hcτ : c = τu ^ 2 := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact h)
        subst hcτ
        have hm : w⁻¹ * w⁻¹ * l ∈ slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y} := by
          refine hstep _ (mul_mem (mul_mem (inv_mem hwL) (inv_mem hwL)) hlL) ?_
          calc w⁻¹ * w⁻¹ * l * y * (w⁻¹ * w⁻¹ * l)⁻¹ = w⁻¹ * (w⁻¹ * (l * y * l⁻¹) * w) * w := by
                simp only [_root_.mul_inv_rev, inv_inv, mul_assoc]
            _ = w⁻¹ * (w⁻¹ * (sτ * (sτ * y)) * w) * w := by rw [hz, map_pow, sq, mul_assoc sτ sτ y]
            _ = sτ * (sτ * (w⁻¹ * (w⁻¹ * y * w) * w)) := by simp only [hcen]
            _ = sτ * (sτ * (w⁻¹ * (sτ⁻¹ * y) * w)) := by rw [hwinv]
            _ = y := by
                have h3 : w⁻¹ * (sτ⁻¹ * y) * w = sτ⁻¹ * (w⁻¹ * y * w) := by
                  calc w⁻¹ * (sτ⁻¹ * y) * w = sτ⁻¹ * (sτ * (w⁻¹ * (sτ⁻¹ * y) * w)) := by group
                    _ = sτ⁻¹ * (w⁻¹ * (sτ * (sτ⁻¹ * y)) * w) := by rw [hcen]
                    _ = sτ⁻¹ * (w⁻¹ * y * w) := by group
                rw [h3, hwinv]
                group
        have : l = w * w * (w⁻¹ * w⁻¹ * l) := by group
        rw [this]
        exact mul_mem (mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers w))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers w))) (Subgroup.mem_sup_left hm)
    · refine sup_le (centralizer_le_centMod _ _) (Subgroup.zpowers_le.mpr ?_)
      exact mem_centMod_iff_scalar.mpr ⟨hwL, sτ, ⟨τu, rfl⟩, hconj⟩
  ·
    have h3dvd : 3 ∣ Nat.card K - 1 := by
      rw [hK.card]
      cases π
      · change p ^ f % 3 = 2 at hq
        change 3 ∣ (p ^ f) ^ 2 - 1
        have h1 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (pow_pos hK.prime.pos f)
        have : (p ^ f) ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq]
        omega
      · change p ^ f % 3 = 1 at hq
        change 3 ∣ p ^ f - 1
        omega
    have := hK.finite
    have hcard3 : Nat.card (rootsOfUnity 3 K) = 3 :=
      CFSG.LinearGroups.card_rootsOfUnity_of_dvd h3dvd
    have hS3 : slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer ({y, w} : Set (GL (Fin 3) K)) =
        (rootsOfUnity 3 K).map (GeneralLinearGroup.scalar (Fin 3)) := by
      ext M
      constructor
      · intro hM
        obtain ⟨hML, hMC⟩ := Subgroup.mem_inf.mp hM
        rw [Subgroup.mem_centralizer_iff] at hMC
        have hMy : (M : Matrix (Fin 3) (Fin 3) K) * y = y * M := by
          have := congrArg Units.val (hMC y (by simp))
          simpa using this.symm
        have hMw : (M : Matrix (Fin 3) (Fin 3) K) * w = w * M := by
          have := congrArg Units.val (hMC w (by simp))
          simpa using this.symm
        obtain ⟨a, b, c, habc⟩ := (commute_iff_eq_poly hℓ hy _).mp hMy
        have hwy2 : (w : Matrix (Fin 3) (Fin 3) K) * (y : Matrix (Fin 3) (Fin 3) K) ^ 2 =
            τ ^ 2 • ((y : Matrix (Fin 3) (Fin 3) K) ^ 2 * w) := by
          rw [sq, ← Matrix.mul_assoc, hwy, Matrix.smul_mul, Matrix.mul_assoc, hwy, Matrix.mul_smul,
            smul_smul, ← sq, ← Matrix.mul_assoc, ← sq]
        have hwM : (w : Matrix (Fin 3) (Fin 3) K) * M =
            (a • 1 + (b * τ) • (y : Matrix (Fin 3) (Fin 3) K) +
              (c * τ ^ 2) • (y : Matrix (Fin 3) (Fin 3) K) ^ 2) * w := by
          rw [habc, Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
            Matrix.mul_smul, Matrix.mul_one, hwy, hwy2, Matrix.add_mul, Matrix.add_mul,
            Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, smul_smul,
            smul_smul]
        rw [← hMw, habc] at hwM
        have hcancel := (w.isUnit).mul_left_inj.mp hwM
        set v : Fin 3 → K := Pi.single 0 1
        have hv : v ≠ 0 := by
          intro h
          have := congrFun h 0
          simp [v] at this
        have hli := linearIndependent_cyclic hℓ hy hv
        have hcv := congrArg (fun N => N *ᵥ v) hcancel
        simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hcv
        rw [Fintype.linearIndependent_iff] at hli
        have h0 := hli ![0, b * (τ - 1), c * (τ ^ 2 - 1)] (by
          simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, zero_smul, zero_add]
          rw [mul_sub, mul_sub, sub_smul, sub_smul, mul_one, mul_one]
          rw [← sub_eq_zero.mpr hcv.symm]
          abel)
        have hb : b = 0 := by
          have := h0 1
          simp only [Matrix.cons_val_one] at this
          exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hτ1)
        have hc : c = 0 := by
          have := h0 2
          simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at this
          have hτ2 : τ ^ 2 ≠ 1 := by
            intro h
            apply hτ1
            calc τ = τ ^ 3 / τ ^ 2 := by field_simp
              _ = 1 := by rw [hτ, h, div_one]
          exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hτ2)
        rw [hb, hc, zero_smul, zero_smul, add_zero, add_zero] at habc
        have hdet : a ^ 3 = 1 := by
          have := ((mem_slPi_iff hπ).mp hML).2
          rw [habc, det_smul, det_one, mul_one, Fintype.card_fin] at this
          exact this
        have ha0 : a ≠ 0 := by
          rintro rfl
          simp at hdet
        refine ⟨Units.mk0 a ha0, (mem_rootsOfUnity _ _).mpr (Units.ext (by
          rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]; exact hdet)), ?_⟩
        apply Units.ext
        rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.val_mk0, habc,
          Matrix.smul_one_eq_diagonal]
      · rintro ⟨ζ, hζ, rfl⟩
        have hζ3 : (ζ : K) ^ 3 = 1 := by
          have := congrArg Units.val ((mem_rootsOfUnity _ _).mp hζ)
          rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
        refine Subgroup.mem_inf.mpr ⟨scalar_mem_slPi_of_cube hK hq hζ3, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro g _
        exact (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ g).eq
    rw [hS3, Subgroup.card_map_of_injective, hcard3]
    intro c c' h
    have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) h
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_apply_eq] at this
    exact Units.ext this

end Structure

end CFSG.RankThree.PartTwo.Sec4
