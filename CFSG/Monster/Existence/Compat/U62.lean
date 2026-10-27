module

public import CFSG.Monster.Existence.Compat.U62Center
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.Monster.Existence.Compat

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Open Matrix

theorem expChar_F4 : ExpChar F4 2 := inferInstance

theorem herm_iff (M : Matrix (Fin 6) (Fin 6) F4) :
    (∀ x y, monsterHerm (M *ᵥ x) (M *ᵥ y) = monsterHerm x y) ↔ Mᵀ * M.map (· ^ 2) = 1 := by
  have := expChar_F4
  constructor
  · intro h
    ext j k
    have h1 := h (Pi.single j 1) (Pi.single k 1)
    simp only [monsterHerm, mulVec_single_one, Matrix.col_apply, Pi.single_apply] at h1
    rw [Matrix.mul_apply, one_apply]
    simp only [transpose_apply, map_apply]
    rw [h1]
    by_cases hjk : j = k
    · subst hjk; simp
    · simp only [hjk, ite_false]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hij : i = j
      · subst hij; simp [hjk]
      · simp [hij]
  · intro h x y
    have hsq : ∀ i, ((M *ᵥ y) i) ^ 2 = (M.map (· ^ 2) *ᵥ fun j => y j ^ 2) i := by
      intro i
      simp only [mulVec, dotProduct, map_apply]
      rw [sum_pow_char 2]
      exact Finset.sum_congr rfl fun j _ => mul_pow _ _ _
    have h2 : (fun i => ((M *ᵥ y) i) ^ 2) = M.map (· ^ 2) *ᵥ fun j => y j ^ 2 := funext hsq
    show (M *ᵥ x) ⬝ᵥ (fun i => ((M *ᵥ y) i) ^ 2) = x ⬝ᵥ (fun i => y i ^ 2)
    rw [h2, dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm,
      mulVec_mulVec, h, one_mulVec]

section Transport

variable {K : Type} [Field K]

@[expose] noncomputable def glMapEquiv (φ : K ≃+* F4) : GL (Fin 6) K ≃* GL (Fin 6) F4 where
  toFun := Matrix.GeneralLinearGroup.map (n := Fin 6) (φ : K →+* F4)
  invFun := Matrix.GeneralLinearGroup.map (n := Fin 6) (φ.symm : F4 →+* K)
  left_inv A := Units.ext (Matrix.ext fun i j => by
    simp [Matrix.GeneralLinearGroup.map_apply])
  right_inv A := Units.ext (Matrix.ext fun i j => by
    simp [Matrix.GeneralLinearGroup.map_apply])
  map_mul' A B := map_mul _ A B

theorem coe_glMapEquiv (φ : K ≃+* F4) (A : GL (Fin 6) K) :
    ((glMapEquiv φ A : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      (A : Matrix (Fin 6) (Fin 6) K).map φ := rfl

theorem glMapEquiv_scalar (φ : K ≃+* F4) (c : Kˣ) :
    glMapEquiv φ (Matrix.GeneralLinearGroup.scalar (Fin 6) c) =
      Matrix.GeneralLinearGroup.scalar (Fin 6) (Units.map (φ : K →* F4) c) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [coe_glMapEquiv, Matrix.GeneralLinearGroup.coe_scalar, Matrix.GeneralLinearGroup.coe_scalar]
  by_cases h : i = j
  · subst h; simp [Matrix.scalar_apply]
  · simp [Matrix.scalar_apply, h]

@[expose] def suGen (K : Type) [Field K] : Set (GL (Fin 6) K) :=
  {A | (A : Matrix (Fin 6) (Fin 6) K).det = 1 ∧
    ((A : Matrix (Fin 6) (Fin 6) K).map (· ^ 2))ᵀ * (A : Matrix (Fin 6) (Fin 6) K) = 1}

theorem stated_mem_suGen_iff (φ : K ≃+* F4) (A : GL (Fin 6) K) :
    A ∈ suGen K ↔ IsHermSU (glMapEquiv φ A) := by
  have key : ∀ N : Matrix (Fin 6) (Fin 6) K, N.map φ = 1 ↔ N = 1 := by
    intro N
    constructor
    · intro h
      refine Matrix.map_injective φ.injective ?_
      simpa [Matrix.map_one _ (map_zero φ) (map_one φ)] using h
    · rintro rfl
      exact Matrix.map_one _ (map_zero φ) (map_one φ)
  have hdet : ((A : Matrix (Fin 6) (Fin 6) K).map φ).det = 1 ↔
      (A : Matrix (Fin 6) (Fin 6) K).det = 1 := by
    have : ((A : Matrix (Fin 6) (Fin 6) K).map φ).det = φ (A : Matrix (Fin 6) (Fin 6) K).det :=
      (RingHom.map_det (φ : K →+* F4) _).symm
    rw [this]
    exact ⟨fun h => φ.injective (by rw [h, map_one]), fun h => by rw [h, map_one]⟩
  have hsq : ∀ B : Matrix (Fin 6) (Fin 6) K, (B.map φ).map (· ^ 2) = (B.map (· ^ 2)).map φ := by
    intro B; ext i j; simp [map_pow]
  rw [IsHermSU, coe_glMapEquiv, herm_iff, hdet]
  refine and_congr Iff.rfl ?_
  have h1 : ((A : Matrix (Fin 6) (Fin 6) K).map φ)ᵀ *
        ((A : Matrix (Fin 6) (Fin 6) K).map φ).map (· ^ 2) =
      ((A : Matrix (Fin 6) (Fin 6) K)ᵀ * (A : Matrix (Fin 6) (Fin 6) K).map (· ^ 2)).map φ := by
    rw [Matrix.map_mul, hsq, Matrix.transpose_map]
  rw [h1, key]
  constructor
  · intro h
    have := congrArg Matrix.transpose h
    simpa [Matrix.transpose_mul] using this
  · intro h
    have := congrArg Matrix.transpose h
    simpa [Matrix.transpose_mul] using this

theorem map_statedSU (φ : K ≃+* F4) :
    (StatedSU 6 2 K).map (glMapEquiv φ).toMonoidHom = monsterSU62 := by
  show Subgroup.map _ (Subgroup.closure (suGen K)) = Subgroup.closure {A | IsHermSU A}
  rw [MonoidHom.map_closure]
  congr 1
  ext A'
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact (stated_mem_suGen_iff φ A).1 hA
  · intro hA'
    refine ⟨(glMapEquiv φ).symm A', ?_, MulEquiv.apply_symm_apply _ _⟩
    rw [stated_mem_suGen_iff φ]
    simpa using hA'

@[expose] noncomputable def suEquiv (φ : K ≃+* F4) : StatedSU 6 2 K ≃* monsterSU62 :=
  ((glMapEquiv φ).subgroupMap (StatedSU 6 2 K)).trans
    (MulEquiv.subgroupCongr (map_statedSU φ))

theorem coe_suEquiv (φ : K ≃+* F4) (A : StatedSU 6 2 K) :
    ((suEquiv φ A : monsterSU62) : GL (Fin 6) F4) = glMapEquiv φ (A : GL (Fin 6) K) := rfl

theorem coe_suEquiv_symm (φ : K ≃+* F4) (x : monsterSU62) :
    (((suEquiv φ).symm x : StatedSU 6 2 K) : GL (Fin 6) K) =
      (glMapEquiv φ).symm (x : GL (Fin 6) F4) := by
  apply (glMapEquiv φ).injective
  rw [MulEquiv.apply_symm_apply, ← coe_suEquiv, MulEquiv.apply_symm_apply]

theorem scalar_mem_center (c : F4ˣ)
    (hc : Matrix.GeneralLinearGroup.scalar (Fin 6) c ∈ monsterSU62) :
    (⟨Matrix.GeneralLinearGroup.scalar (Fin 6) c, hc⟩ : monsterSU62) ∈
      Subgroup.center monsterSU62 := by
  rw [Subgroup.mem_center_iff]
  intro a
  apply Subtype.ext
  have hz : Matrix.GeneralLinearGroup.scalar (Fin 6) c ∈ Subgroup.center (GL (Fin 6) F4) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  exact Subgroup.mem_center_iff.1 hz (a : GL (Fin 6) F4)

theorem map_statedScalars (φ : K ≃+* F4) :
    ((StatedScalars (Fin 6) K).subgroupOf (StatedSU 6 2 K)).map (suEquiv φ).toMonoidHom =
      Subgroup.center monsterSU62 := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, coe_suEquiv_symm]
  constructor
  · rintro ⟨c, hc⟩
    have hx : (x : GL (Fin 6) F4) =
        Matrix.GeneralLinearGroup.scalar (Fin 6) (Units.map (φ : K →* F4) c) := by
      rw [← glMapEquiv_scalar, hc, MulEquiv.apply_symm_apply]
    have : x = ⟨Matrix.GeneralLinearGroup.scalar (Fin 6) (Units.map (φ : K →* F4) c), hx ▸ x.2⟩ :=
      Subtype.ext hx
    rw [this]
    exact scalar_mem_center _ _
  · intro hx
    obtain ⟨c, hc⟩ := center_monsterSU62_scalar x hx
    refine ⟨Units.map (φ.symm : F4 →* K) c, ?_⟩
    rw [MulEquiv.eq_symm_apply, glMapEquiv_scalar, hc]
    congr 1
    exact Units.ext (by simp)

@[expose] noncomputable def statedProjEquivU62 (φ : K ≃+* F4) :
    StatedProj (StatedSU 6 2 K) ≃* MonsterU62 :=
  QuotientGroup.congr _ _ (suEquiv φ) (map_statedScalars φ)

end Transport

noncomputable def ringEquivF4 {K : Type} [Field K] [Finite K] (h : Nat.card K = 4) : K ≃+* F4 := by
  have := Fintype.ofFinite K
  have := Fintype.ofFinite F4
  refine FiniteField.ringEquivOfCardEq ?_
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, h, card_F4]

theorem u62_equiv_of_lieModel (X : Type) [Group X] (h : LieModel X .PSU 6 2 1) :
    Nonempty (X ≃* MonsterU62) := by
  rcases h with ⟨-, -, K, _, hfin, hK, ⟨e⟩⟩ | ⟨h6, -⟩ | ⟨h6, -⟩ | ⟨h6, -⟩
  · have hK4 : Nat.card K = 4 := by simpa using hK
    exact ⟨e.trans (statedProjEquivU62 (ringEquivF4 hK4))⟩
  all_goals exact absurd h6 (by norm_num)

end CFSG.Monster.Existence.Compat
