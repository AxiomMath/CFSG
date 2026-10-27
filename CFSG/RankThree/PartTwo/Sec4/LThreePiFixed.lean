module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes

public section

namespace CFSG.RankThree.PartTwo.Sec4

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

section SubGL

@[expose] noncomputable def subGL (S : Subfield K) : GL (Fin 3) S →* GL (Fin 3) K :=
  Units.map (S.subtype.mapMatrix :
    Matrix (Fin 3) (Fin 3) S →+* Matrix (Fin 3) (Fin 3) K).toMonoidHom

variable (S : Subfield K)

theorem coe_subGL (B : GL (Fin 3) S) :
    ((subGL S B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (B : Matrix (Fin 3) (Fin 3) S).map S.subtype :=
  rfl

theorem subGL_injective : Function.Injective (subGL S) := by
  intro B B' h
  apply Units.ext
  apply Matrix.map_injective (f := S.subtype) Subtype.val_injective
  exact congrArg Units.val h

theorem subGL_scalar (u : Sˣ) :
    subGL S (GeneralLinearGroup.scalar (Fin 3) u) =
      GeneralLinearGroup.scalar (Fin 3) (Units.map (S.subtype : S →* K) u) := by
  apply Units.ext
  rw [coe_subGL, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero _)]
  rfl

theorem trace_subGL (B : GL (Fin 3) S) :
    ((subGL S B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace =
      ((B : Matrix (Fin 3) (Fin 3) S).trace : K) := by
  rw [coe_subGL, Matrix.trace, Matrix.trace, Fin.sum_univ_three, Fin.sum_univ_three]
  simp [Matrix.diag]

theorem det_subGL (B : GL (Fin 3) S) :
    ((subGL S B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det =
      ((B : Matrix (Fin 3) (Fin 3) S).det : K) := by
  rw [coe_subGL]
  exact (RingHom.map_det S.subtype _).symm

theorem mem_statedScalars_of_subGL {B : GL (Fin 3) S}
    (h : subGL S B ∈ StatedScalars (Fin 3) K) : B ∈ StatedScalars (Fin 3) S := by
  obtain ⟨u, hu⟩ := h
  have hent : ∀ i k, (((B : Matrix (Fin 3) (Fin 3) S) i k : S) : K) =
      if i = k then (u : K) else 0 := by
    intro i k
    have := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) i k) hu
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
      coe_subGL, Matrix.map_apply, Subfield.coe_subtype] at this
    rw [← this]
  have h2 : (((B : Matrix (Fin 3) (Fin 3) S) 0 0 : S) : K) = u := by
    rw [hent 0 0, ite_eq_left rfl]
  have h00 : (B : Matrix (Fin 3) (Fin 3) S) 0 0 ≠ 0 := by
    intro h0
    rw [h0] at h2
    exact u.ne_zero (by rw [← h2]; rfl)
  refine ⟨Units.mk0 _ h00, Units.ext ?_⟩
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.val_mk0]
  ext i k
  rw [Matrix.diagonal_apply]
  have h1 := hent i k
  split_ifs with hik
  · rw [h1, ite_eq_left hik, h2]
  · rw [h1, ite_eq_right hik]
    rfl

variable {S}

theorem frobGL_subGL {φ : K ≃+* K} (hS : ∀ c, c ∈ S ↔ φ c = c) (B : GL (Fin 3) S) :
    frobGL φ (subGL S B) = subGL S B := by
  apply Units.ext
  rw [coe_frobGL, coe_subGL]
  ext i k
  exact (hS _).mp ((B : Matrix (Fin 3) (Fin 3) S) i k).2

theorem exists_subGL_eq {φ : K ≃+* K} (hS : ∀ c, c ∈ S ↔ φ c = c) {A : GL (Fin 3) K}
    (hA : frobGL φ A = A) : ∃ B, subGL S B = A := by
  have hent : ∀ A : GL (Fin 3) K, frobGL φ A = A → ∀ i k,
      (A : Matrix (Fin 3) (Fin 3) K) i k ∈ S := by
    intro A hA i k
    apply (hS _).mpr
    have := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) i k) hA
    simpa [coe_frobGL] using this
  have hAinv : frobGL φ A⁻¹ = A⁻¹ := by rw [map_inv, hA]
  let pre : ∀ A : GL (Fin 3) K, frobGL φ A = A → Matrix (Fin 3) (Fin 3) S :=
    fun A hA => Matrix.of fun i k => ⟨(A : Matrix (Fin 3) (Fin 3) K) i k, hent A hA i k⟩
  have hpre : ∀ A hA, (pre A hA).map S.subtype = (A : Matrix (Fin 3) (Fin 3) K) := by
    intro A hA
    ext i k
    rfl
  refine ⟨⟨pre A hA, pre A⁻¹ hAinv, ?_, ?_⟩, ?_⟩
  · apply Matrix.map_injective (f := S.subtype) Subtype.val_injective
    change (pre A hA * pre A⁻¹ hAinv).map S.subtype =
      (1 : Matrix (Fin 3) (Fin 3) S).map S.subtype
    rw [Matrix.map_mul, hpre A hA, hpre A⁻¹ hAinv, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  · apply Matrix.map_injective (f := S.subtype) Subtype.val_injective
    change (pre A⁻¹ hAinv * pre A hA).map S.subtype =
      (1 : Matrix (Fin 3) (Fin 3) S).map S.subtype
    rw [Matrix.map_mul, hpre A⁻¹ hAinv, hpre A hA, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  · apply Units.ext
    exact hpre A hA

theorem subGL_mem_glPi_iff (hK : PiField π p f K) {f₀ : ℕ} (hf : f = 3 * f₀) {φ : K ≃+* K}
    (hφ : ∀ c, φ c = c ^ piCard π (p ^ f₀)) (hS : ∀ c, c ∈ S ↔ φ c = c)
    (hS₀ : PiField π p f₀ S) (B : GL (Fin 3) S) :
    subGL S B ∈ glPi π 3 (p ^ f) K ↔ B ∈ glPi π 3 (p ^ f₀) S := by
  cases π
  · have hU := hK.unitary
    have hU₀ := hS₀.unitary
    rw [mem_glPi_false hU, mem_glPi_false hU₀, coe_subGL]
    have hbj : ∀ c : S, hU.bar (c : K) = ((hU₀.bar c : S) : K) := by
      intro c
      have h2 : (c : K) ^ (p ^ f₀) ^ 2 = c := by
        have := (hS _).mp c.2
        rwa [hφ] at this
      rw [hU.bar_apply, hU₀.bar_apply, SubmonoidClass.coe_pow, hf, pow_mul',
        show (p ^ f₀) ^ 3 = (p ^ f₀) ^ 2 * p ^ f₀ by ring, pow_mul, h2]
    have hmap : ((B : Matrix (Fin 3) (Fin 3) S).map S.subtype).map hU.bar =
        ((B : Matrix (Fin 3) (Fin 3) S).map hU₀.bar).map S.subtype := by
      ext i k
      exact hbj _
    rw [hmap, ← Matrix.transpose_map, ← Matrix.map_mul]
    constructor
    · intro h1
      exact Matrix.map_injective (f := S.subtype) Subtype.val_injective
        (h1.trans (Matrix.map_one _ (map_zero _) (map_one _)).symm)
    · intro h1
      rw [h1, Matrix.map_one _ (map_zero _) (map_one _)]
  · exact ⟨fun _ => mem_glPi_true _ _, fun _ => mem_glPi_true _ _⟩

theorem subGL_mem_slPi_iff (hK : PiField π p f K) {f₀ : ℕ} (hf : f = 3 * f₀) {φ : K ≃+* K}
    (hφ : ∀ c, φ c = c ^ piCard π (p ^ f₀)) (hS : ∀ c, c ∈ S ↔ φ c = c)
    (hS₀ : PiField π p f₀ S) (B : GL (Fin 3) S) :
    subGL S B ∈ slPi π 3 (p ^ f) K ↔ B ∈ slPi π 3 (p ^ f₀) S := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hπ₀ : π = false → UnitaryFieldData p f₀ S := fun h => by subst h; exact hS₀.unitary
  rw [mem_slPi_iff hπ, mem_slPi_iff hπ₀, subGL_mem_glPi_iff hK hf hφ hS hS₀, det_subGL]
  refine and_congr_right fun _ => ⟨fun h1 => Subtype.val_injective (by rw [h1]; rfl),
    fun h1 => by rw [h1]; rfl⟩

theorem subGL_mem_zPi (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {f₀ : ℕ}
    (hf : f = 3 * f₀) {φ : K ≃+* K} (hφ : ∀ c, φ c = c ^ piCard π (p ^ f₀))
    (hS : ∀ c, c ∈ S ↔ φ c = c) (hS₀ : PiField π p f₀ S) (hq₀ : ModThree π (p ^ f₀))
    {B : GL (Fin 3) S} (hB : B ∈ zPi π 3 (p ^ f₀) S) : subGL S B ∈ zPi π 3 (p ^ f) K := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have hπ₀ : π = false → UnitaryFieldData p f₀ S := fun h => by subst h; exact hS₀.unitary
  have hq₀' : π = false → ModThree false (p ^ f₀) := fun h => by subst h; exact hq₀
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨τ₀, hτ₀, hτ₀1⟩ := exists_tau hS₀ hq₀
  rw [zPi_eq hπ₀ hq₀' hτ₀ hτ₀1] at hB
  rw [zPi_eq hπ hq' hτ hτ1]
  obtain ⟨hBH, u, rfl⟩ := Subgroup.mem_inf.mp hB
  refine Subgroup.mem_inf.mpr ⟨(subGL_mem_glPi_iff hK hf hφ hS hS₀ _).mpr hBH, ?_⟩
  rw [subGL_scalar]
  exact ⟨_, rfl⟩

theorem type123_one_subGL (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {f₀ : ℕ}
    (hf : f = 3 * f₀) {φ : K ≃+* K} (hφ : ∀ c, φ c = c ^ piCard π (p ^ f₀))
    (hS : ∀ c, c ∈ S ↔ φ c = c) (hS₀ : PiField π p f₀ S) (hq₀ : ModThree π (p ^ f₀))
    {y₀ : GL (Fin 3) S} (h : Type123 π (p ^ f₀) S y₀ 1) :
    Type123 π (p ^ f) K (subGL S y₀) 1 := by
  obtain ⟨τ₀, hτ₀, hτ₀1, z₀, hz₀, g₀, hg₀, hD⟩ := h
  have hτ : ((τ₀ : S) : K) ^ 3 = 1 := by
    rw [← SubmonoidClass.coe_pow, hτ₀]
    rfl
  refine ⟨(τ₀ : K), hτ, fun h1 => hτ₀1 (Subtype.val_injective h1), subGL S z₀,
    subGL_mem_zPi hK hq hf hφ hS hS₀ hq₀ hz₀, subGL S g₀,
    (subGL_mem_glPi_iff hK hf hφ hS hS₀ _).mpr hg₀, ?_⟩
  rw [← map_mul, ← map_inv, ← map_mul, ← map_mul, hD]
  apply Units.ext
  rw [coe_subGL, coe_diagTau_eq_diagonal, coe_diagTau_eq_diagonal,
    Matrix.diagonal_map (map_zero _)]
  congr 1
  funext i
  fin_cases i <;> simp

end SubGL

section TypeThree

theorem trace_eq_zero_of_type3 (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {x : GL (Fin 3) K} (h3 : Type123 π (p ^ f) K x 3) :
    (x : Matrix (Fin 3) (Fin 3) K).trace = 0 := by
  classical
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨-, hx3, hirr⟩ := h3
  obtain ⟨ℓ, hℓ⟩ := mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hx3
  set X : Matrix (Fin 3) (Fin 3) K := (x : Matrix (Fin 3) (Fin 3) K) with hX
  have hX3 : X ^ 3 = (ℓ : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
    rw [hX, ← Units.val_pow_eq_pow_val, ← hℓ, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
  set v : Fin 3 → K := Pi.single 0 1 with hv
  have hv0 : v ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [hv] at this
  set b : Fin 3 → (Fin 3 → K) := ![v, X *ᵥ v, X *ᵥ (X *ᵥ v)] with hb
  have hspan_lt : ∀ s : Finset (Fin 3 → K), s.card < 3 →
      Submodule.span K (s : Set (Fin 3 → K)) ≠ ⊤ := by
    intro s hs htop
    have h1 := finrank_span_finset_le_card (R := K) s
    rw [Set.finrank, htop, finrank_top, Module.finrank_fin_fun] at h1
    omega
  have hinv : ∀ W : Submodule K (Fin 3 → K), (∀ w ∈ W, X *ᵥ w ∈ W) → v ∈ W → W = ⊤ := by
    intro W hW hvW
    rcases hirr W hW with h | h
    · rw [h, Submodule.mem_bot] at hvW
      exact absurd hvW hv0
    · exact h
  have hli : LinearIndependent K b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_three, hb, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hg
    have hg2 : g 2 = 0 := by
      by_contra h2
      have hmem : X *ᵥ (X *ᵥ v) ∈ Submodule.span K {v, X *ᵥ v} := by
        have : X *ᵥ (X *ᵥ v) = (-(g 2)⁻¹ * g 0) • v + (-(g 2)⁻¹ * g 1) • (X *ᵥ v) := by
          have e := congrArg (fun w => (g 2)⁻¹ • w) hg
          simp only [smul_add, smul_smul, inv_mul_cancel₀ h2, one_smul, smul_zero] at e
          rw [← sub_eq_zero, ← e]
          simp only [neg_mul, neg_smul]
          abel
        rw [this]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      have hW : ∀ w ∈ Submodule.span K {v, X *ᵥ v}, X *ᵥ w ∈ Submodule.span K {v, X *ᵥ v} := by
        intro w hw
        obtain ⟨a, c, rfl⟩ := Submodule.mem_span_pair.mp hw
        rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ hmem)
      have htop := hinv _ hW (Submodule.subset_span (by simp))
      apply hspan_lt {v, X *ᵥ v} (Finset.card_le_two.trans_lt (by norm_num))
      rw [Finset.coe_insert, Finset.coe_singleton]
      exact htop
    have hg1 : g 1 = 0 := by
      by_contra h1
      rw [hg2, zero_smul, add_zero] at hg
      have hmem : X *ᵥ v ∈ Submodule.span K {v} := by
        have : X *ᵥ v = (-(g 1)⁻¹ * g 0) • v := by
          have e := congrArg (fun w => (g 1)⁻¹ • w) hg
          simp only [smul_add, smul_smul, inv_mul_cancel₀ h1, one_smul, smul_zero] at e
          rw [← sub_eq_zero, ← e]
          simp only [neg_mul, neg_smul]
          abel
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      have hW : ∀ w ∈ Submodule.span K {v}, X *ᵥ w ∈ Submodule.span K {v} := by
        intro w hw
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
        rw [Matrix.mulVec_smul]
        exact Submodule.smul_mem _ _ hmem
      have htop := hinv _ hW (Submodule.mem_span_singleton_self _)
      apply hspan_lt {v} (by simp)
      rw [Finset.coe_singleton]
      exact htop
    have hg0 : g 0 = 0 := by
      rw [hg2, hg1, zero_smul, zero_smul, add_zero, add_zero] at hg
      exact (smul_eq_zero.mp hg).resolve_right hv0
    intro i
    fin_cases i
    · exact hg0
    · exact hg1
    · exact hg2
  set P : Matrix (Fin 3) (Fin 3) K := Matrix.of fun r k => b k r with hP
  have hPu : IsUnit P := by
    have hcol : P.col = b := by
      funext i r
      rfl
    exact (Matrix.linearIndependent_cols_iff_isUnit (A := P)).mp (hcol ▸ hli)
  set C : Matrix (Fin 3) (Fin 3) K := !![0, 0, (ℓ : K); 1, 0, 0; 0, 1, 0] with hC
  have hXP : X * P = P * C := by
    have h3v : X *ᵥ (X *ᵥ (X *ᵥ v)) = (ℓ : K) • v := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← pow_two, ← pow_succ, hX3,
        Matrix.smul_mulVec, Matrix.one_mulVec]
    have hb2 : X *ᵥ b 2 = (ℓ : K) • b 0 := by
      simpa [hb] using h3v
    ext r k
    have eXP : (X * P) r k = (X *ᵥ b k) r := rfl
    rw [eXP, Matrix.mul_apply, Fin.sum_univ_three]
    fin_cases k
    · simp [hP, hC, hb]
    · simp [hP, hC, hb]
    · have e2 : (X *ᵥ b 2) r = (ℓ : K) * b 0 r := by
        rw [hb2, Pi.smul_apply, smul_eq_mul]
      simp only [Fin.reduceFinMk, Fin.isValue] at e2 ⊢
      rw [e2]
      simp [hP, hC, mul_comm]
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  have hXeq : X = P * C * P⁻¹ := by
    rw [← hXP, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPdet, Matrix.mul_one]
  rw [hXeq, Matrix.trace_mul_cycle, Matrix.nonsing_inv_mul _ hPdet, Matrix.one_mul, hC]
  simp [Matrix.trace, Fin.sum_univ_three]

end TypeThree

section HilbertNinety

theorem exists_norm_eq (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {f₀ : ℕ}
    (hf : f = 3 * f₀) {φ : K ≃+* K} (hφ : ∀ c, φ c = c ^ piCard π (p ^ f₀))
    {ζ : Kˣ} (hζT : ζ ∈ rootsOfUnity (qSubPi π (p ^ f)) K) (hφζ : φ (ζ : K) = ζ) :
    ∃ s ∈ rootsOfUnity (qSubPi π (p ^ f)) K,
      ((s : Kˣ) : K) * φ (s : K) * φ (φ (s : K)) = ζ := by
  have := hK.finite
  set q₀ := p ^ f₀ with hq₀def
  have hqq : p ^ f = q₀ ^ 3 := by rw [hf, pow_mul']
  have hq₀1 : 1 ≤ q₀ := Nat.one_le_pow _ _ hK.prime.pos
  have hq₀ : ModThree π q₀ := modThree_of_cube (hqq ▸ hq)
  set M := 3 * (3 * (q₀ / 3) ^ 2 + 3 * (q₀ / 3) + 1) with hMdef
  have hNM : qSubPi π (p ^ f) = qSubPi π q₀ * M := by rw [hqq, qSubPi_cube_eq hq₀]
  have hN0 : qSubPi π (p ^ f) ≠ 0 := qSubPi_ne_zero hK hq
  have hM0 : 0 < M := by omega
  have hζ' : (ζ : K) ^ piCard π q₀ = ζ := by rw [← hφ]; exact hφζ
  have hζq₀ : (ζ : K) ^ qSubPi π q₀ = 1 := by
    have hζN := congrArg Units.val ((mem_rootsOfUnity _ _).mp hζT)
    rw [Units.val_pow_eq_pow_val, Units.val_one, hqq] at hζN
    exact pow_qSubPi_eq_one_of_fixed hq₀1 ζ.ne_zero hζ' hζN
  have : NeZero (qSubPi π (p ^ f)) := ⟨hN0⟩
  have := rootsOfUnity.isCyclic K (qSubPi π (p ^ f))
  have hTcard := card_rootsOfUnity_qSubPi hK hq
  set t : rootsOfUnity (qSubPi π (p ^ f)) K := ⟨ζ, hζT⟩ with htdef
  have hexp : Nat.card (rootsOfUnity (qSubPi π (p ^ f)) K) / M = qSubPi π q₀ := by
    rw [hTcard, hNM, Nat.mul_div_cancel _ hM0]
  have ht : t ^ (Nat.card (rootsOfUnity (qSubPi π (p ^ f)) K) / M) = 1 := by
    rw [hexp]
    apply Subtype.ext
    apply Units.ext
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one, Units.val_pow_eq_pow_val,
      Units.val_one]
    exact hζq₀
  obtain ⟨s, hs⟩ := exists_pow_eq_of_pow_div (by rw [hTcard, hNM]; exact dvd_mul_left M _) ht
  refine ⟨s, s.2, ?_⟩
  have hsM : ((s : Kˣ) : K) ^ M = ζ := by
    have := congrArg (fun u : rootsOfUnity (qSubPi π (p ^ f)) K => ((u : Kˣ) : K)) hs
    simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val] at this
    rw [this]
  have hsN : ((s : Kˣ) : K) ^ qSubPi π (p ^ f) = 1 := by
    have := congrArg Units.val ((mem_rootsOfUnity _ _).mp s.2)
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
  obtain ⟨j, hj⟩ := norm_exponent hq₀
  rw [hφ (φ _), hφ]
  calc ((s : Kˣ) : K) * ((s : Kˣ) : K) ^ piCard π q₀ *
        (((s : Kˣ) : K) ^ piCard π q₀) ^ piCard π q₀ =
      ((s : Kˣ) : K) ^ (1 + piCard π q₀ + piCard π q₀ ^ 2) := by ring
    _ = ((s : Kˣ) : K) ^ M * (((s : Kˣ) : K) ^ qSubPi π (p ^ f)) ^ j := by
        rw [hj, ← hqq, pow_add, pow_mul, mul_comm j]
        ring
    _ = ζ := by rw [hsM, hsN, one_pow, mul_one]

theorem ringAut_sq_apply (φ : K ≃+* K) (c : K) : (φ ^ 2) c = φ (φ c) := by
  rw [pow_two, RingAut.mul_apply]

theorem ringAut_apply_three' {φ : K ≃+* K} (hφ3 : orderOf φ = 3) {ψ : K ≃+* K}
    (hψ : ψ = φ ∨ ψ = φ ^ 2) (c : K) : ψ (ψ (ψ c)) = c := by
  rcases hψ with rfl | rfl
  · exact ringAut_apply_three hφ3 c
  · simp only [ringAut_sq_apply, ringAut_apply_three hφ3]

theorem frobGL_three' {φ : K ≃+* K} (hφ3 : orderOf φ = 3) {ψ : K ≃+* K}
    (hψ : ψ = φ ∨ ψ = φ ^ 2) (A : GL (Fin 3) K) : frobGL ψ (frobGL ψ (frobGL ψ A)) = A := by
  apply Units.ext
  rw [coe_frobGL, coe_frobGL, coe_frobGL]
  ext i k
  simp only [Matrix.map_apply, ringAut_apply_three' hφ3 hψ]

theorem fixed_iff_of_sq {φ : K ≃+* K} (hφ3 : orderOf φ = 3) {ψ : K ≃+* K}
    (hψ : ψ = φ ∨ ψ = φ ^ 2) (c : K) : ψ c = c ↔ φ c = c := by
  rcases hψ with rfl | rfl
  · rfl
  · rw [ringAut_sq_apply]
    constructor
    · intro h
      calc φ c = φ (φ (φ (φ c))) := by rw [ringAut_apply_three hφ3]
        _ = c := by rw [h, h]
    · intro h
      rw [h, h]

theorem exists_frob_mul_eq (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {f₀ : ℕ}
    (hf : f = 3 * f₀) {φ : K ≃+* K} (hφ : ∀ c, φ c = c ^ piCard π (p ^ f₀))
    (hφ3 : orderOf φ = 3) {ψ : K ≃+* K} (hψ : ψ = φ ∨ ψ = φ ^ 2) {ℓ : Kˣ}
    (hℓ : ℓ ∈ rootsOfUnity (qSubPi π (p ^ f)) K) (hN : (ℓ : K) * ψ ℓ * ψ (ψ ℓ) = 1) :
    ∃ μ ∈ rootsOfUnity (qSubPi π (p ^ f)) K, ψ (μ : K) * ℓ = μ := by
  have := hK.finite
  set n := qSubPi π (p ^ f) with hn
  have hψ3 := ringAut_apply_three' hφ3 hψ
  let ψT : rootsOfUnity n K →* rootsOfUnity n K :=
    { toFun := fun x => ⟨Units.map (ψ : K →* K) x, (mem_rootsOfUnity _ _).mpr (by
        rw [← map_pow, (mem_rootsOfUnity _ _).mp x.2, map_one])⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ _ _) }
  have hψT : ∀ x, (((ψT x : rootsOfUnity n K) : Kˣ) : K) = ψ ((x : Kˣ) : K) := fun x => rfl
  let δ : rootsOfUnity n K →* rootsOfUnity n K := MonoidHom.id _ / ψT
  let Nm : rootsOfUnity n K →* rootsOfUnity n K := MonoidHom.id _ * ψT * ψT.comp ψT
  have hval : ∀ x y : rootsOfUnity n K, x = y ↔ ((x : Kˣ) : K) = ((y : Kˣ) : K) :=
    fun x y => ⟨fun h => by rw [h], fun h => Subtype.ext (Units.ext h)⟩
  have hδ : ∀ x, (((δ x : rootsOfUnity n K) : Kˣ) : K) = ((x : Kˣ) : K) / ψ ((x : Kˣ) : K) := by
    intro x
    change (((x / ψT x : rootsOfUnity n K) : Kˣ) : K) = _
    rw [div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul,
      Units.val_inv_eq_inv_val, hψT, div_eq_mul_inv]
  have hNm : ∀ x, (((Nm x : rootsOfUnity n K) : Kˣ) : K) =
      ((x : Kˣ) : K) * ψ ((x : Kˣ) : K) * ψ (ψ ((x : Kˣ) : K)) := by
    intro x
    change (((x * ψT x * ψT (ψT x) : rootsOfUnity n K) : Kˣ) : K) = _
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hψT, hψT, hψT]
  have hne : ∀ x : rootsOfUnity n K, ((x : Kˣ) : K) ≠ 0 := fun x => Units.ne_zero _
  have hkerδ : δ.ker = Nm.range := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_range, hval, hδ]
    simp only [OneMemClass.coe_one, Units.val_one]
    rw [div_eq_one_iff_eq (by simp)]
    constructor
    · intro hx
      have hφx : φ ((x : Kˣ) : K) = ((x : Kˣ) : K) :=
        (fixed_iff_of_sq hφ3 hψ _).mp hx.symm
      obtain ⟨s, hsT, hs⟩ := exists_norm_eq hK hq hf hφ x.2 hφx
      refine ⟨⟨s, hsT⟩, (hval _ _).mpr ?_⟩
      rw [hNm]
      change ((s : K)) * ψ (s : K) * ψ (ψ (s : K)) = _
      rcases hψ with rfl | rfl
      · exact hs
      · rw [ringAut_sq_apply, ringAut_sq_apply, ringAut_apply_three hφ3, ← hs]
        ring
    · rintro ⟨y, rfl⟩
      rw [hNm, map_mul, map_mul, hψ3]
      ring
  have hle : δ.range ≤ Nm.ker := by
    rintro _ ⟨x, rfl⟩
    rw [MonoidHom.mem_ker, hval, hNm, hδ, map_div₀, map_div₀, hψ3]
    simp only [OneMemClass.coe_one, Units.val_one]
    have h1 := hne x
    have h2 : ψ ((x : Kˣ) : K) ≠ 0 := by simp
    have h3 : ψ (ψ ((x : Kˣ) : K)) ≠ 0 := by simp
    field_simp
  have hcard1 := Subgroup.card_mul_index δ.ker
  have hcard2 := Subgroup.card_mul_index Nm.ker
  rw [Subgroup.index_ker] at hcard1 hcard2
  rw [hkerδ] at hcard1
  have heq : δ.range = Nm.ker := by
    apply Subgroup.eq_of_le_of_card_ge hle
    have hpos : 0 < Nat.card Nm.range := Nat.card_pos
    have : Nat.card Nm.range * Nat.card Nm.ker = Nat.card Nm.range * Nat.card δ.range := by
      rw [hcard1, mul_comm, hcard2]
    exact (Nat.eq_of_mul_eq_mul_left hpos this).le
  have hℓker : (⟨ℓ, hℓ⟩ : rootsOfUnity n K) ∈ Nm.ker := by
    rw [MonoidHom.mem_ker, hval, hNm]
    simpa using hN
  rw [← heq] at hℓker
  obtain ⟨μ, hμ⟩ := hℓker
  refine ⟨μ, μ.2, ?_⟩
  have h1 := (hval _ _).mp hμ
  rw [hδ] at h1
  change ((μ : Kˣ) : K) / ψ ((μ : Kˣ) : K) = (ℓ : K) at h1
  have h2 : ψ ((μ : Kˣ) : K) ≠ 0 := by simp
  rw [← h1]
  field_simp

end HilbertNinety

section Normalize

theorem frobGL_pow_two (φ : K ≃+* K) (A : GL (Fin 3) K) :
    frobGL (φ ^ 2) A = frobGL φ (frobGL φ A) := by
  apply Units.ext
  rw [coe_frobGL, coe_frobGL, coe_frobGL]
  ext i k
  simp only [Matrix.map_apply, ringAut_sq_apply]

theorem exists_conj_frob (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {f₀ : ℕ}
    (hf : f = 3 * f₀) {φ : K ≃+* K} (hφ : ∀ c, φ c = c ^ piCard π (p ^ f₀))
    (hφ3 : orderOf φ = 3) {g : GL (Fin 3) K} (hg : g ∈ glPi π 3 (p ^ f) K)
    (hσ3 : ∀ A ∈ slPi π 3 (p ^ f) K,
      g * frobGL φ (g * frobGL φ (g * frobGL φ A * g⁻¹) * g⁻¹) * g⁻¹ = A) :
    ∃ h ∈ glPi π 3 (p ^ f) K, ∀ A, g * frobGL φ A * g⁻¹ = h * frobGL φ (h⁻¹ * A * h) * h⁻¹ := by
  obtain ⟨s, hsT, hcoc⟩ := exists_cocycle_eq_one hK hq hf hφ hφ3 hg hσ3
  have hg₁H : g * GeneralLinearGroup.scalar (Fin 3) s ∈ glPi π 3 (p ^ f) K :=
    mul_mem hg ((scalar_mem_glPi_iff hK s).mpr hsT)
  obtain ⟨h, hhH, hgh⟩ := exists_lang_glPi hK hf hφ hφ3 hg₁H hcoc
  refine ⟨h, hhH, fun A => ?_⟩
  have hc := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar s (frobGL φ A)).eq
  have hg₁ : g * GeneralLinearGroup.scalar (Fin 3) s = h * (frobGL φ h)⁻¹ := by
    calc g * GeneralLinearGroup.scalar (Fin 3) s =
        g * GeneralLinearGroup.scalar (Fin 3) s * frobGL φ h * (frobGL φ h)⁻¹ := by group
      _ = h * (frobGL φ h)⁻¹ := by rw [hgh]
  calc g * frobGL φ A * g⁻¹ = g * (frobGL φ A * GeneralLinearGroup.scalar (Fin 3) s) *
        (GeneralLinearGroup.scalar (Fin 3) s)⁻¹ * g⁻¹ := by group
    _ = (g * GeneralLinearGroup.scalar (Fin 3) s) * frobGL φ A *
        (g * GeneralLinearGroup.scalar (Fin 3) s)⁻¹ := by rw [hc]; group
    _ = h * frobGL φ (h⁻¹ * A * h) * h⁻¹ := by
        rw [hg₁, map_mul, map_mul, map_inv]
        group

theorem exists_conj_frobGL (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {f₀ : ℕ}
    (hf : f = 3 * f₀) {φ : K ≃+* K} (hφ : ∀ c, φ c = c ^ piCard π (p ^ f₀))
    (hφ3 : orderOf φ = 3) {ψ : K ≃+* K} (hψ : ψ = φ ∨ ψ = φ ^ 2) {g : GL (Fin 3) K}
    (hg : g ∈ glPi π 3 (p ^ f) K)
    (hσ3 : ∀ A ∈ slPi π 3 (p ^ f) K,
      g * frobGL ψ (g * frobGL ψ (g * frobGL ψ A * g⁻¹) * g⁻¹) * g⁻¹ = A) :
    ∃ h ∈ glPi π 3 (p ^ f) K, ∀ A ∈ slPi π 3 (p ^ f) K,
      g * frobGL ψ A * g⁻¹ = h * frobGL ψ (h⁻¹ * A * h) * h⁻¹ := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  rcases hψ with rfl | rfl
  · obtain ⟨h, hh, hA⟩ := exists_conj_frob hK hq hf hφ hφ3 hg hσ3
    exact ⟨h, hh, fun A _ => hA A⟩
  · have hΦ3 := frobGL_three hφ3
    obtain ⟨S, hS⟩ : ∃ S : GL (Fin 3) K → GL (Fin 3) K,
        S = fun A => g * frobGL (φ ^ 2) A * g⁻¹ := ⟨_, rfl⟩
    obtain ⟨g₂, hg₂⟩ : ∃ g₂, g₂ = g * frobGL φ (frobGL φ g) := ⟨_, rfl⟩
    have hTS : ∀ A, S (S A) = g₂ * frobGL φ A * g₂⁻¹ := by
      intro A
      rw [hS, hg₂]
      simp only [frobGL_pow_two, map_mul, map_inv, hΦ3]
      group
    have hSL : ∀ A ∈ slPi π 3 (p ^ f) K, S A ∈ slPi π 3 (p ^ f) K := by
      intro A hA
      rw [hS]
      exact conj_mem_slPi hπ hg (frobGL_mem_slPi hK _ hA)
    have hS3 : ∀ A ∈ slPi π 3 (p ^ f) K, S (S (S A)) = A := by
      intro A hA
      rw [hS]
      exact hσ3 A hA
    have hg₂H : g₂ ∈ glPi π 3 (p ^ f) K := by
      rw [hg₂]
      exact mul_mem hg (frobGL_mem_glPi hK φ (frobGL_mem_glPi hK φ hg))
    have hT3 : ∀ A ∈ slPi π 3 (p ^ f) K,
        g₂ * frobGL φ (g₂ * frobGL φ (g₂ * frobGL φ A * g₂⁻¹) * g₂⁻¹) * g₂⁻¹ = A := by
      intro A hA
      rw [← hTS, ← hTS, ← hTS, hS3 _ (hSL _ (hSL _ (hSL _ hA))), hS3 A hA]
    obtain ⟨h, hh, hT⟩ := exists_conj_frob hK hq hf hφ hφ3 hg₂H hT3
    refine ⟨h, hh, fun A hA => ?_⟩
    have hS4 : S A = S (S (S (S A))) := by rw [hS3 _ (hSL _ hA)]
    have e1 : h⁻¹ * (h * frobGL φ (h⁻¹ * A * h) * h⁻¹) * h = frobGL φ (h⁻¹ * A * h) := by group
    calc g * frobGL (φ ^ 2) A * g⁻¹ = S A := by rw [hS]
      _ = S (S (S (S A))) := hS4
      _ = g₂ * frobGL φ (g₂ * frobGL φ A * g₂⁻¹) * g₂⁻¹ := by rw [hTS, hTS]
      _ = h * frobGL φ (h⁻¹ * (h * frobGL φ (h⁻¹ * A * h) * h⁻¹) * h) * h⁻¹ := by
          rw [hT (g₂ * frobGL φ A * g₂⁻¹), hT A]
      _ = h * frobGL (φ ^ 2) (h⁻¹ * A * h) * h⁻¹ := by rw [e1, frobGL_pow_two]

end Normalize

end CFSG.RankThree.PartTwo.Sec4
