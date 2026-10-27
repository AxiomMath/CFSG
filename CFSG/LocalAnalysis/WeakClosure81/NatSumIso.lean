module

public import CFSG.Quasithin.EmptyFaithful.T1521SA5Two
public import CFSG.GH74.GLS.LU.Local.FiveCbarF
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NatSum

open scoped Matrix

private noncomputable def mulVecAddEquiv {K : Type} [Field K]
    (h : Matrix.SpecialLinearGroup (Fin 2) K) : (Fin 2 → K) ≃+ (Fin 2 → K) where
  toFun v := (h : Matrix (Fin 2) (Fin 2) K) *ᵥ v
  invFun v := ((h⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
    Matrix (Fin 2) (Fin 2) K) *ᵥ v
  left_inv v := by
    show ((h⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
      ((h : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  right_inv v := by
    show (h : Matrix (Fin 2) (Fin 2) K) *ᵥ
      (((h⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  map_add' v w := by
    show (h : Matrix (Fin 2) (Fin 2) K) *ᵥ (v + w) =
      (h : Matrix (Fin 2) (Fin 2) K) *ᵥ v + (h : Matrix (Fin 2) (Fin 2) K) *ᵥ w
    rw [Matrix.mulVec_add]

@[simp] private theorem mulVecAddEquiv_apply {K : Type} [Field K]
    (h : Matrix.SpecialLinearGroup (Fin 2) K) (v : Fin 2 → K) :
    mulVecAddEquiv h v = (h : Matrix (Fin 2) (Fin 2) K) *ᵥ v := rfl

private theorem exists_smul_one_of_commute_two {K : Type} [Field K]
    (M : Matrix (Fin 2) (Fin 2) K)
    (h1 : M * (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) K) =
      (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) K) * M)
    (h2 : M * (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) K) =
      (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) K) * M) :
    ∃ μ : K, M = μ • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [Matrix.eta_fin_two M] at h1 h2
  simp only [Matrix.mul_fin_two] at h1 h2
  have a1 := congrFun (congrFun h1 0) 0
  have a2 := congrFun (congrFun h1 0) 1
  have a3 := congrFun (congrFun h2 0) 0
  simp at a1 a2 a3
  have c11 : M 1 1 = M 0 0 := by linear_combination -a2
  refine ⟨M 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [a1, a3, c11]

@[simp] private theorem slMap_id {K : Type} [CommRing K]
    (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    Matrix.SpecialLinearGroup.map (RingHom.id K) A = A := by
  apply Subtype.ext
  simp [Matrix.SpecialLinearGroup.map_apply_coe]

private theorem slMap_comp {K L M : Type} [CommRing K] [CommRing L] [CommRing M]
    (f : K →+* L) (g : L →+* M) (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    Matrix.SpecialLinearGroup.map g (Matrix.SpecialLinearGroup.map f A) =
      Matrix.SpecialLinearGroup.map (g.comp f) A := by
  apply Subtype.ext
  ext i j
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.map_apply, RingHom.comp_apply]

private noncomputable def slMapEquiv {K L : Type} [CommRing K] [CommRing L] (e : K ≃+* L) :
    Matrix.SpecialLinearGroup (Fin 2) K ≃* Matrix.SpecialLinearGroup (Fin 2) L where
  toFun A := Matrix.SpecialLinearGroup.map e.toRingHom A
  invFun B := Matrix.SpecialLinearGroup.map e.symm.toRingHom B
  left_inv A := by
    change Matrix.SpecialLinearGroup.map e.symm.toRingHom
      (Matrix.SpecialLinearGroup.map e.toRingHom A) = A
    rw [slMap_comp]
    simp
  right_inv B := by
    change Matrix.SpecialLinearGroup.map e.toRingHom
      (Matrix.SpecialLinearGroup.map e.symm.toRingHom B) = B
    rw [slMap_comp]
    simp
  map_mul' A B := map_mul _ A B

private theorem nat_card_mulAut_of_equiv_alt5 {X : Type} [Group X]
    (hA5 : Nonempty (X ≃* alternatingGroup (Fin 5))) : Nat.card (MulAut X) = 120 := by
  obtain ⟨e⟩ := hA5
  rw [Nat.card_congr (MulAut.congr e).toEquiv]
  exact CFSG.GH74.GLS.LU.Local.Five.nat_card_mulAut_alternatingGroup_five

private theorem nat_card_of_equiv_alt5 {X : Type} [Group X]
    (hA5 : Nonempty (X ≃* alternatingGroup (Fin 5))) : Nat.card X = 60 := by
  obtain ⟨e⟩ := hA5
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.GH74.GLS.LU.Local.Five.nat_card_alternatingGroup_five

private theorem conj_injective_of_equiv_alt5 {X : Type} [Group X]
    (hA5 : Nonempty (X ≃* alternatingGroup (Fin 5))) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  obtain ⟨e⟩ := hA5
  rw [← MonoidHom.ker_eq_bot_iff]
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hcomm : ∀ y : X, x * y = y * x := by
    intro y
    have h1 : x * y * x⁻¹ = y := by
      have := congrArg (fun f : MulAut X => f y) hx
      rwa [MulAut.conj_apply, MulAut.one_apply] at this
    calc x * y = x * y * x⁻¹ * x := by group
      _ = y * x := by rw [h1]
  have hcent : e x = 1 := by
    apply CFSG.GH74.GLS.LU.Local.Five.alternatingGroup_five_central_eq_one
    intro b
    obtain ⟨y, rfl⟩ := e.surjective b
    show e y * e x = e x * e y
    rw [← map_mul, ← map_mul, hcomm y]
  exact e.injective (by rw [hcent, map_one])

private theorem inner_index_two {X : Type} [Group X]
    (hA5 : Nonempty (X ≃* alternatingGroup (Fin 5))) :
    (MulAut.conj : X →* MulAut X).range.index = 2 := by
  have hinj := conj_injective_of_equiv_alt5 hA5
  have hcardX := nat_card_of_equiv_alt5 hA5
  have hcardAut := nat_card_mulAut_of_equiv_alt5 hA5
  have hker : Nat.card (MulAut.conj : X →* MulAut X).ker = 1 := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr hinj]
    exact Subgroup.card_bot
  have hrange : Nat.card (MulAut.conj : X →* MulAut X).range = 60 := by
    have h := Subgroup.card_ker_mul_card_range (MulAut.conj : X →* MulAut X)
    rw [hker, one_mul, hcardX] at h
    exact h
  have hmain := Subgroup.card_mul_index
    (H := (MulAut.conj : X →* MulAut X).range)
  rw [hrange, hcardAut] at hmain
  omega

private theorem mulAut_eq_conj_or_conj_mul {X : Type} [Group X]
    {α : MulAut X} (hα : α ∉ (MulAut.conj : X →* MulAut X).range)
    (hidx : (MulAut.conj : X →* MulAut X).range.index = 2) (β : MulAut X) :
    (∃ x : X, β = MulAut.conj x) ∨ (∃ x : X, β = MulAut.conj x * α) := by
  have h := (Subgroup.index_eq_two_iff_exists_notMem_and).mp hidx
  obtain ⟨a, ha, ha'⟩ := h
  have haα : α * a ∈ (MulAut.conj : X →* MulAut X).range := (ha' α).resolve_right hα
  by_cases hβ : β ∈ (MulAut.conj : X →* MulAut X).range
  · left
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hβ
    exact ⟨x, hx.symm⟩
  · right
    have hβa : β * a ∈ (MulAut.conj : X →* MulAut X).range := (ha' β).resolve_right hβ
    have hmem : β * α⁻¹ ∈ (MulAut.conj : X →* MulAut X).range := by
      have h1 : (β * a) * (α * a)⁻¹ ∈ (MulAut.conj : X →* MulAut X).range :=
        Subgroup.mul_mem (H := (MulAut.conj : X →* MulAut X).range) hβa
          (Subgroup.inv_mem (H := (MulAut.conj : X →* MulAut X).range) haα)
      have heq : (β * a) * (α * a)⁻¹ = β * α⁻¹ := by group
      rwa [heq] at h1
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hmem
    exact ⟨x, by rw [hx]; group⟩

private theorem frobenius_not_inner {X : Type} [Group X]
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4)
    {φ' : X →* Matrix.SpecialLinearGroup (Fin 2) K}
    (hφ' : Function.Bijective φ') {α : MulAut X}
    (hα : ∀ g : X, φ' (α g) =
      Matrix.SpecialLinearGroup.map (frobenius K 2) (φ' g)) :
    α ∉ (MulAut.conj : X →* MulAut X).range := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  intro hαInn
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hαInn
  have hαx : ∀ g : X, α g = x * g * x⁻¹ := by
    intro g
    rw [← hx]
    rfl
  have hfall : ∀ M : Matrix.SpecialLinearGroup (Fin 2) K,
      Matrix.SpecialLinearGroup.map (frobenius K 2) M =
        φ' x * M * (φ' x)⁻¹ := by
    intro M
    obtain ⟨g, rfl⟩ := hφ'.2 M
    rw [← hα g, hαx g]
    simp only [map_mul, map_inv]
  let M₁ : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  let M₂ : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  have hfix₁ : Matrix.SpecialLinearGroup.map (frobenius K 2) M₁ = M₁ := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [M₁]
  have hfix₂ : Matrix.SpecialLinearGroup.map (frobenius K 2) M₂ = M₂ := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [M₂]
  have hc₁ : φ' x * M₁ = M₁ * φ' x := by
    have h1 : φ' x * M₁ * (φ' x)⁻¹ = M₁ := by rw [← hfall M₁, hfix₁]
    have h2 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) K => A * φ' x) h1
    simpa [mul_assoc] using h2
  have hc₂ : φ' x * M₂ = M₂ * φ' x := by
    have h1 : φ' x * M₂ * (φ' x)⁻¹ = M₂ := by rw [← hfall M₂, hfix₂]
    have h2 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) K => A * φ' x) h1
    simpa [mul_assoc] using h2
  have hc₁' : (φ' x : Matrix (Fin 2) (Fin 2) K) * (M₁ : Matrix (Fin 2) (Fin 2) K) =
      (M₁ : Matrix (Fin 2) (Fin 2) K) * (φ' x : Matrix (Fin 2) (Fin 2) K) := by
    have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) K =>
      (A : Matrix (Fin 2) (Fin 2) K)) hc₁
    simpa [Matrix.SpecialLinearGroup.coe_mul] using this
  have hc₂' : (φ' x : Matrix (Fin 2) (Fin 2) K) * (M₂ : Matrix (Fin 2) (Fin 2) K) =
      (M₂ : Matrix (Fin 2) (Fin 2) K) * (φ' x : Matrix (Fin 2) (Fin 2) K) := by
    have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) K =>
      (A : Matrix (Fin 2) (Fin 2) K)) hc₂
    simpa [Matrix.SpecialLinearGroup.coe_mul] using this
  obtain ⟨μ, hμ⟩ := exists_smul_one_of_commute_two (φ' x : Matrix (Fin 2) (Fin 2) K)
    (by simpa [M₁] using hc₁') (by simpa [M₂] using hc₂')
  have hμ2 : μ ^ 2 = 1 := by
    have hdet : (μ • (1 : Matrix (Fin 2) (Fin 2) K)).det = 1 := by
      rw [← hμ, Matrix.SpecialLinearGroup.det_coe]
    rwa [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one] at hdet
  have hμ1 : μ = 1 := by
    have hsq : (μ - 1) ^ 2 = 0 := by
      have hchar : (2 : K) = 0 := CharP.cast_eq_zero K 2
      linear_combination hμ2 + (1 - μ) * hchar
    exact sub_eq_zero.mp ((pow_eq_zero_iff (show (2 : ℕ) ≠ 0 by norm_num)).mp hsq)
  have hx1 : φ' x = 1 := by
    apply Subtype.ext
    rw [hμ, hμ1, one_smul, Matrix.SpecialLinearGroup.coe_one]
  have hconst : ∀ M : Matrix.SpecialLinearGroup (Fin 2) K,
      Matrix.SpecialLinearGroup.map (frobenius K 2) M = M := by
    intro M
    rw [hfall M, hx1]
    simp
  have hcard : Fintype.card K = 4 := by
    rw [← Nat.card_eq_fintype_card]; exact hK
  have htwo : 2 < Fintype.card K := by rw [hcard]; norm_num
  have hlt : ({0, 1} : Finset K).card < (Finset.univ : Finset K).card := by
    have h2 : ({0, 1} : Finset K).card = 2 :=
      (Finset.card_pair_eq_two_iff).mpr (by simp)
    rw [Finset.card_univ, Fintype.card_eq_nat_card, hK, h2]
    norm_num
  obtain ⟨ω, -, hω⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hω0 : ω ≠ 0 := fun h => hω (by rw [h]; simp)
  have hω1 : ω ≠ 1 := fun h => hω (by rw [h]; simp)
  let M₃ : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨!![1, ω; 0, 1], by simp [Matrix.det_fin_two]⟩
  have h3 : (frobenius K 2) ((M₃ : Matrix (Fin 2) (Fin 2) K) 0 1) =
      (M₃ : Matrix (Fin 2) (Fin 2) K) 0 1 := by
    have h4 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) K =>
      (A : Matrix (Fin 2) (Fin 2) K) 0 1) (hconst M₃)
    rwa [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply] at h4
  have hωsq : ω ^ 2 = ω := by
    rw [frobenius_def] at h3
    simpa [M₃] using h3
  have hne : ω ^ 2 ≠ ω := by
    intro h
    have hz : ω * (ω - 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp hz with h0 | h0
    · exact hω0 h0
    · exact hω1 (sub_eq_zero.mp h0)
  exact hne hωsq

private theorem core {X : Type} [Group X]
    (hA5 : Nonempty (X ≃* alternatingGroup (Fin 5)))
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    {φ φ' : X →* Matrix.SpecialLinearGroup (Fin 2) K}
    (hφ : Function.Bijective φ) (hφ' : Function.Bijective φ') :
    ∃ T : (Fin 2 → K) ≃+ (Fin 2 → K), ∀ (g : X) (v : Fin 2 → K),
      T ((φ' g : Matrix (Fin 2) (Fin 2) K).mulVec v) =
        (φ g : Matrix (Fin 2) (Fin 2) K).mulVec (T v) := by
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      (k := 2) Nat.prime_two (by omega) (by rw [hK]; norm_num)
  have hFr : Function.Bijective (frobenius K 2) :=
    (Finite.injective_iff_bijective).mp (frobenius_inj K 2)
  let FrR : K ≃+* K := RingEquiv.ofBijective (frobenius K 2) hFr
  have hFrbij : Function.Bijective (Matrix.SpecialLinearGroup.map (n := Fin 2)
      (frobenius K 2)) := by
    have hpoint : ∀ A : Matrix.SpecialLinearGroup (Fin 2) K,
        Matrix.SpecialLinearGroup.map (frobenius K 2) A =
          Matrix.SpecialLinearGroup.map FrR.toRingHom A := by
      intro A
      apply Subtype.ext
      ext i j
      simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
        Matrix.map_apply, FrR]
    rw [funext hpoint]
    exact (slMapEquiv FrR).bijective
  let eφ' : X ≃* Matrix.SpecialLinearGroup (Fin 2) K := MulEquiv.ofBijective φ' hφ'
  let FrME : Matrix.SpecialLinearGroup (Fin 2) K ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    MulEquiv.ofBijective (Matrix.SpecialLinearGroup.map (frobenius K 2)) hFrbij
  let α : MulAut X := eφ'.trans (FrME.trans eφ'.symm)
  have hα : ∀ g : X, φ' (α g) =
      Matrix.SpecialLinearGroup.map (frobenius K 2) (φ' g) := by
    intro g
    change eφ' (eφ'.symm (FrME (eφ' g))) =
      Matrix.SpecialLinearGroup.map (frobenius K 2) (φ' g)
    rw [eφ'.apply_symm_apply]
    rfl
  have hαni : α ∉ (MulAut.conj : X →* MulAut X).range :=
    frobenius_not_inner hK hφ' hα
  have hidx : (MulAut.conj : X →* MulAut X).range.index = 2 := inner_index_two hA5
  let eφ : X ≃* Matrix.SpecialLinearGroup (Fin 2) K := MulEquiv.ofBijective φ hφ
  let β : MulAut X := eφ.trans eφ'.symm
  have hβ : ∀ g : X, φ g = φ' (β g) := by
    intro g
    change eφ g = eφ' (eφ'.symm (eφ g))
    rw [eφ'.apply_symm_apply]
  rcases mulAut_eq_conj_or_conj_mul hαni hidx β with ⟨x, hx⟩ | ⟨x, hx⟩
  · have hgSL : ∀ g : X, φ g = φ' x * φ' g * (φ' x)⁻¹ := by
      intro g
      have h1 : φ g = φ' (MulAut.conj x g) := by rw [hβ g, hx]
      rw [h1, MulAut.conj_apply, map_mul, map_mul, map_inv]
    have hmat : ∀ g : X, (φ' x : Matrix (Fin 2) (Fin 2) K) * (φ' g : Matrix (Fin 2) (Fin 2) K) =
        (φ g : Matrix (Fin 2) (Fin 2) K) * (φ' x : Matrix (Fin 2) (Fin 2) K) := by
      intro g
      have h1 : φ' x * φ' g = φ g * φ' x := by rw [hgSL g]; group
      exact congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) K =>
        (A : Matrix (Fin 2) (Fin 2) K)) h1
    refine ⟨mulVecAddEquiv (φ' x), fun g v => ?_⟩
    rw [mulVecAddEquiv_apply, mulVecAddEquiv_apply, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, hmat g]
  · have hgSL : ∀ g : X, φ g = φ' x *
        Matrix.SpecialLinearGroup.map (frobenius K 2) (φ' g) * (φ' x)⁻¹ := by
      intro g
      have h1 : φ g = φ' (x * α g * x⁻¹) := by
        rw [hβ g, hx, MulAut.mul_apply, MulAut.conj_apply]
      rw [h1]
      simp only [map_mul, map_inv, hα g]
    let frVec : (Fin 2 → K) ≃+ (Fin 2 → K) :=
      AddEquiv.piCongrRight (fun _ => FrR.toAddEquiv)
    have hfr : ∀ (M : Matrix.SpecialLinearGroup (Fin 2) K) (v : Fin 2 → K),
        frVec ((M : Matrix (Fin 2) (Fin 2) K) *ᵥ v) =
          ((M : Matrix (Fin 2) (Fin 2) K).map (frobenius K 2)) *ᵥ frVec v := by
      intro M v
      funext i
      have h1 : frVec ((M : Matrix (Fin 2) (Fin 2) K) *ᵥ v) i =
          (frobenius K 2) (((M : Matrix (Fin 2) (Fin 2) K) *ᵥ v) i) := by
        simp [frVec, FrR]
      rw [h1, RingHom.map_mulVec]
      rfl
    have hmat : ∀ g : X, (φ' x : Matrix (Fin 2) (Fin 2) K) *
          ((φ' g : Matrix (Fin 2) (Fin 2) K).map (frobenius K 2)) =
        (φ g : Matrix (Fin 2) (Fin 2) K) * (φ' x : Matrix (Fin 2) (Fin 2) K) := by
      intro g
      have h1 : φ' x * Matrix.SpecialLinearGroup.map (frobenius K 2) (φ' g) =
          φ g * φ' x := by rw [hgSL g]; group
      have h2 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) K =>
        (A : Matrix (Fin 2) (Fin 2) K)) h1
      simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.map_apply_coe,
        RingHom.mapMatrix_apply] using h2
    refine ⟨frVec.trans (mulVecAddEquiv (φ' x)), fun g v => ?_⟩
    simp only [AddEquiv.trans_apply, mulVecAddEquiv_apply]
    rw [hfr (φ' g) v, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hmat g]

theorem exists_equiv_of_natural {X : Type} [Group X] (hX : CFSG.Quasithin.IsPSL 2 2 2 X)
    {K₁ K₂ : Type} [Field K₁] [Field K₂] [Finite K₁] [Finite K₂]
    (h₁ : Nat.card K₁ = 4) (h₂ : Nat.card K₂ = 4)
    {φ₁ : X →* Matrix.SpecialLinearGroup (Fin 2) K₁}
    {φ₂ : X →* Matrix.SpecialLinearGroup (Fin 2) K₂}
    (hφ₁ : Function.Bijective φ₁) (hφ₂ : Function.Bijective φ₂) :
    ∃ T : (Fin 2 → K₂) ≃+ (Fin 2 → K₁), ∀ (g : X) (v : Fin 2 → K₂),
      T ((φ₂ g : Matrix (Fin 2) (Fin 2) K₂).mulVec v) =
        (φ₁ g : Matrix (Fin 2) (Fin 2) K₁).mulVec (T v) := by
  obtain ⟨eA5⟩ := CFSG.Quasithin.nonempty_equiv_alt5_of_isPSL_two_two_two hX
  haveI : Fintype K₁ := Fintype.ofFinite K₁
  haveI : Fintype K₂ := Fintype.ofFinite K₂
  have hcard : Fintype.card K₂ = Fintype.card K₁ := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, h₂, h₁]
  let ε : K₂ ≃+* K₁ := FiniteField.ringEquivOfCardEq hcard
  let T₀ : (Fin 2 → K₂) ≃+ (Fin 2 → K₁) :=
    AddEquiv.piCongrRight (fun _ => ε.toAddEquiv)
  have hT₀ : ∀ (M : Matrix.SpecialLinearGroup (Fin 2) K₂) (v : Fin 2 → K₂),
      T₀ ((M : Matrix (Fin 2) (Fin 2) K₂).mulVec v) =
        ((Matrix.SpecialLinearGroup.map ε.toRingHom M :
            Matrix.SpecialLinearGroup (Fin 2) K₁) :
          Matrix (Fin 2) (Fin 2) K₁).mulVec (T₀ v) := by
    intro M v
    funext i
    have h1 : T₀ ((M : Matrix (Fin 2) (Fin 2) K₂).mulVec v) i =
        ε (((M : Matrix (Fin 2) (Fin 2) K₂).mulVec v) i) := by
      simp [T₀]
    rw [h1]
    have h2 : ((Matrix.SpecialLinearGroup.map ε.toRingHom M :
          Matrix.SpecialLinearGroup (Fin 2) K₁) :
        Matrix (Fin 2) (Fin 2) K₁) = ε.mapMatrix (M : Matrix (Fin 2) (Fin 2) K₂) :=
      Matrix.SpecialLinearGroup.map_apply_coe _ M
    rw [h2]
    have h3 : T₀ v = ⇑ε.toRingHom ∘ v := by
      funext j
      rfl
    rw [h3]
    exact RingHom.map_mulVec ε.toRingHom (M : Matrix (Fin 2) (Fin 2) K₂) v i
  let φ₂' : X →* Matrix.SpecialLinearGroup (Fin 2) K₁ :=
    (Matrix.SpecialLinearGroup.map ε.toRingHom).comp φ₂
  have hφ₂' : Function.Bijective φ₂' := by
    have h := (slMapEquiv ε).bijective.comp hφ₂
    simpa [φ₂', slMapEquiv] using h
  obtain ⟨T₁, hT₁⟩ := core ⟨eA5⟩ h₁ hφ₁ hφ₂'
  refine ⟨T₀.trans T₁, fun g v => ?_⟩
  change T₁ (T₀ ((φ₂ g : Matrix (Fin 2) (Fin 2) K₂).mulVec v)) =
    (φ₁ g : Matrix (Fin 2) (Fin 2) K₁).mulVec (T₁ (T₀ v))
  rw [hT₀ (φ₂ g) v]
  exact hT₁ g (T₀ v)

end CFSG.LocalAnalysis.WeakClosure81.NatSum

end
