module

public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisStructure
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bAut

public section

namespace CFSG.RankThree.PartOne

namespace KCRootAxis

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.ComponentClassification.OuterAutomorphisms

section Entrywise

variable (K : Type) [Field K]

@[expose] def slFieldAut : (K ≃+* K) →* MulAut (SL₂ K) where
  toFun σ := MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map σ.toRingHom)
    (Matrix.SpecialLinearGroup.map σ.symm.toRingHom)
    (by ext x i j; simp) (by ext x i j; simp)
  map_one' := by
    ext x i j
    rfl
  map_mul' σ τ := by
    ext x i j
    rfl

variable {K}

theorem slFieldAut_apply (σ : K ≃+* K) (M : SL₂ K) (i j : Fin 2) :
    (slFieldAut K σ M) i j = σ (M i j) :=
  rfl

end Entrywise

section Projective

variable {K : Type} [Field K] [CharP K 2]

variable (K) in
@[expose] def slToPSL : SL₂ K →* PSL2 K :=
  QuotientGroup.mk' (Subgroup.center _)

theorem slToPSL_injective : Function.Injective (slToPSL K) := by
  rw [injective_iff_map_eq_one]
  intro M hM
  have h := (QuotientGroup.eq_one_iff M).mp hM
  rw [sl2_center_eq_bot] at h
  exact h

omit [CharP K 2] in
theorem slToPSL_surjective : Function.Surjective (slToPSL K) :=
  QuotientGroup.mk'_surjective _

variable (K) in
@[expose] noncomputable def slEquivPSL : SL₂ K ≃* PSL2 K :=
  MulEquiv.ofBijective (slToPSL K) ⟨slToPSL_injective, slToPSL_surjective⟩

theorem slEquivPSL_apply (M : SL₂ K) : slEquivPSL K M = slToPSL K M :=
  rfl

theorem toPGL_surjective_of_char_two [Finite K] :
    Function.Surjective (Matrix.ProjectiveSpecialLinearGroup.toPGL : PSL2 K →* PGL2 K) := by
  intro g
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  obtain ⟨d, hd⟩ := exists_sq_eq (A.det : K)
  have hd_ne : d ≠ 0 := by
    intro hd0
    apply Units.ne_zero A.det
    rw [← hd, hd0]
    simp
  let dU : Kˣ := Units.mk0 d hd_ne
  let B : GL (Fin 2) K := Matrix.GeneralLinearGroup.scalar (Fin 2) dU⁻¹ * A
  have hBdetUnit : Matrix.GeneralLinearGroup.det B = 1 := by
    dsimp [B]
    rw [map_mul, Matrix.GeneralLinearGroup.det_scalar]
    apply Units.ext
    change d⁻¹ ^ 2 * (A.det : K) = 1
    rw [← hd]
    field_simp
  have hBdet : Matrix.det (B : Matrix (Fin 2) (Fin 2) K) = 1 :=
    congrArg Units.val hBdetUnit
  let Bs : SL₂ K := ⟨(B : Matrix (Fin 2) (Fin 2) K), hBdet⟩
  refine ⟨QuotientGroup.mk' (Subgroup.center _) Bs, ?_⟩
  change Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL Bs) =
    Matrix.ProjGenLinGroup.mk A
  have htoGL : Matrix.SpecialLinearGroup.toGL Bs = B := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rfl
  rw [htoGL]
  dsimp [B]
  rw [map_mul, Matrix.ProjGenLinGroup.mk_scalar, one_mul]

omit [CharP K 2] in
theorem slToPSL_slFieldAut (σ : K ≃+* K) (M : SL₂ K) :
    slToPSL K (slFieldAut K σ M) = psl2FieldAut K σ (slToPSL K M) := by
  rw [psl2FieldAut_apply]
  exact (psl2RingEquiv_mk σ M).symm

theorem congr_slFieldAut (σ : K ≃+* K) :
    MulAut.congr (slEquivPSL K) (slFieldAut K σ) = psl2FieldAut K σ := by
  ext z
  obtain ⟨M, rfl⟩ := (slEquivPSL K).surjective z
  rw [MulAut.congr_apply]
  simp only [MulEquiv.coe_trans, Function.comp_apply, MulEquiv.symm_apply_apply]
  exact slToPSL_slFieldAut σ M

theorem congr_conj_eq_pglAction (M : SL₂ K) :
    MulAut.congr (slEquivPSL K) (MulAut.conj M) =
      pglAction K (Matrix.ProjectiveSpecialLinearGroup.toPGL (slEquivPSL K M)) := by
  rw [pglAction_toPGL, congr_conj]

theorem exists_conj_mul_slFieldAut [Finite K] (φ : MulAut (SL₂ K)) :
    ∃ (M : SL₂ K) (σ : K ≃+* K), φ = MulAut.conj M * slFieldAut K σ := by
  obtain ⟨x, hx⟩ := semilinearAction_surjective K (MulAut.congr (slEquivPSL K) φ)
  obtain ⟨y, hy⟩ := toPGL_surjective_of_char_two (K := K) x.left
  obtain ⟨M, rfl⟩ := (slEquivPSL K).surjective y
  refine ⟨M, x.right, ?_⟩
  apply (MulAut.congr (slEquivPSL K)).injective
  have hx' : semilinearAction K x = pglAction K x.left * psl2FieldAut K x.right := by
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right x]
    rw [map_mul, semilinearAction_inl, semilinearAction_inr]
  rw [map_mul, congr_conj_eq_pglAction, congr_slFieldAut, hy, ← hx', hx]

theorem conj_mul_slFieldAut_inj [Finite K] {M M' : SL₂ K} {σ σ' : K ≃+* K}
    (h : MulAut.conj M * slFieldAut K σ = MulAut.conj M' * slFieldAut K σ') :
    M = M' ∧ σ = σ' := by
  have key : ∀ (N : SL₂ K) (τ : K ≃+* K),
      MulAut.congr (slEquivPSL K) (MulAut.conj N * slFieldAut K τ) =
        semilinearAction K (SemidirectProduct.inl
          (Matrix.ProjectiveSpecialLinearGroup.toPGL (slEquivPSL K N)) *
          SemidirectProduct.inr τ) := by
    intro N τ
    rw [map_mul, map_mul, congr_conj_eq_pglAction, congr_slFieldAut, semilinearAction_inl,
      semilinearAction_inr]
  have h1 := congrArg (MulAut.congr (slEquivPSL K)) h
  rw [key, key] at h1
  have h2 := semilinearAction_injective K h1
  have hl := congrArg SemidirectProduct.left h2
  have hr := congrArg SemidirectProduct.right h2
  simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
    SemidirectProduct.left_inl, SemidirectProduct.right_inl, SemidirectProduct.left_inr,
    SemidirectProduct.right_inr, map_one, one_mul, mul_one] at hl hr
  exact ⟨(slEquivPSL K).injective (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective hl), hr⟩

variable (K) in
@[expose] noncomputable def outFieldHom : (K ≃+* K) →* Outer (SL₂ K) :=
  (QuotientGroup.mk' (inner (SL₂ K))).comp (slFieldAut K)

theorem outFieldHom_bijective [Finite K] : Function.Bijective (outFieldHom K) := by
  constructor
  · rw [injective_iff_map_eq_one]
    intro σ hσ
    obtain ⟨M, hM⟩ : slFieldAut K σ ∈ inner (SL₂ K) := (QuotientGroup.eq_one_iff _).mp hσ
    have h : MulAut.conj M * slFieldAut K 1 = MulAut.conj 1 * slFieldAut K σ := by
      rw [map_one, mul_one, map_one, one_mul]
      exact hM
    exact (conj_mul_slFieldAut_inj h).2.symm
  · intro c
    obtain ⟨φ, rfl⟩ := QuotientGroup.mk_surjective c
    obtain ⟨M, σ, rfl⟩ := exists_conj_mul_slFieldAut φ
    refine ⟨σ, ?_⟩
    have h1 : (QuotientGroup.mk (MulAut.conj M) : Outer (SL₂ K)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨M, rfl⟩
    change QuotientGroup.mk (slFieldAut K σ) = QuotientGroup.mk (MulAut.conj M * slFieldAut K σ)
    rw [QuotientGroup.mk_mul, h1, one_mul]

variable (K) in
@[expose] noncomputable def outFieldEquiv [Finite K] : (K ≃+* K) ≃* Outer (SL₂ K) :=
  MulEquiv.ofBijective (outFieldHom K) outFieldHom_bijective

theorem out_sl2_isCyclic [Finite K] : IsCyclic (Outer (SL₂ K)) :=
  (outFieldEquiv K).isCyclic.mp (fieldAut_isCyclic K)

theorem natCard_out_sl2 [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) :
    Nat.card (Outer (SL₂ K)) = n := by
  obtain ⟨Fr, -, hord, hzp⟩ := CFSG.QuasithinUnique.Setup.X7b.exists_frobenius_data hn hK
  have h : Nat.card (K ≃+* K) = n := by
    rw [← hord, ← Nat.card_zpowers, hzp]
    exact Subgroup.card_top.symm
  rw [← h]
  exact Nat.card_congr (outFieldEquiv K).toEquiv.symm

end Projective

section Frobenius

variable (K : Type) [Field K] [Finite K]

@[expose] noncomputable def frobRingEquiv [CharP K 2] : K ≃+* K :=
  frobeniusEquiv K 2

variable {K}

theorem frobRingEquiv_apply [CharP K 2] (x : K) : frobRingEquiv K x = x ^ 2 := by
  simp [frobRingEquiv, frobeniusEquiv_apply, frobenius_def]

theorem frobRingEquiv_data [CharP K 2] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) :
    orderOf (frobRingEquiv K) = n ∧ Subgroup.zpowers (frobRingEquiv K) = ⊤ := by
  obtain ⟨Fr, hFr, hord, hzp⟩ := CFSG.QuasithinUnique.Setup.X7b.exists_frobenius_data hn hK
  have : Fr = frobRingEquiv K := RingEquiv.ext fun x => by rw [hFr, frobRingEquiv_apply]
  rw [← this]
  exact ⟨hord, hzp⟩

variable (K) in
@[expose] noncomputable def frobSL [CharP K 2] : MulAut (SL₂ K) :=
  slFieldAut K (frobRingEquiv K)

theorem frobSL_pow_apply [CharP K 2] (k : ℕ) (M : SL₂ K) (i j : Fin 2) :
    ((frobSL K ^ k) M) i j = (M i j) ^ 2 ^ k := by
  induction k generalizing M with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, MulAut.mul_apply, ih, frobSL, slFieldAut_apply, frobRingEquiv_apply,
      ← pow_mul, pow_succ, mul_comm]

end Frobenius

end KCRootAxis

end CFSG.RankThree.PartOne
