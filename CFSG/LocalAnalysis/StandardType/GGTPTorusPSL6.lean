module

public import CFSG.LocalAnalysis.StandardType.GGTPWeightDefs
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private def ggTP_zmod3Hom {G : Type} [Monoid G] (g : G) (hg : orderOf g = 3) :
    Multiplicative (ZMod 3) →* G where
  toFun a := g ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    show g ^ (Multiplicative.toAdd (a * b)).val =
      g ^ (Multiplicative.toAdd a).val * g ^ (Multiplicative.toAdd b).val
    rw [show Multiplicative.toAdd (a * b) =
        Multiplicative.toAdd a + Multiplicative.toAdd b from rfl, ZMod.val_add]
    have h1 : ((Multiplicative.toAdd a).val + (Multiplicative.toAdd b).val) % 3
        = ((Multiplicative.toAdd a).val + (Multiplicative.toAdd b).val) % orderOf g := by
      rw [hg]
    rw [h1, pow_mod_orderOf, pow_add]

private lemma ggTP_zmod3Hom_eq_one_iff {G : Type} [Monoid G] (g : G) (hg : orderOf g = 3)
    (c : Multiplicative (ZMod 3)) : ggTP_zmod3Hom g hg c = 1 ↔ c = 1 := by
  constructor
  · intro hc
    have hpow : g ^ (Multiplicative.toAdd c).val = 1 := hc
    have hdvd : orderOf g ∣ (Multiplicative.toAdd c).val :=
      orderOf_dvd_iff_pow_eq_one.mpr hpow
    rw [hg] at hdvd
    have hzero : (Multiplicative.toAdd c).val = 0 :=
      Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt _)
    have h0 : Multiplicative.toAdd c = 0 := (ZMod.val_eq_zero _).mp hzero
    exact (Equiv.injective Multiplicative.toAdd) (by simpa using h0)
  · intro hc
    rw [hc]
    exact map_one _

private lemma ggTP_zmod3Hom_injective {G : Type} [Group G] (g : G) (hg : orderOf g = 3) :
    Function.Injective (ggTP_zmod3Hom g hg) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext c
  rw [MonoidHom.mem_ker, Subgroup.mem_bot]
  exact ggTP_zmod3Hom_eq_one_iff g hg c

private def ggTP_diagUnitHom {K : Type} [Field K] (ω : Kˣ) (hω : orderOf ω = 3) :
    (Fin 6 → Multiplicative (ZMod 3)) →* (Fin 6 → K)ˣ where
  toFun x :=
    { val := fun i => (ggTP_zmod3Hom ω hω (x i) : K)
      inv := fun i => ((ggTP_zmod3Hom ω hω (x i))⁻¹ : K)
      val_inv := by ext i; simp
      inv_val := by ext i; simp }
  map_one' := by
    apply Units.ext
    ext i
    simp
  map_mul' a b := by
    apply Units.ext
    ext i
    simp [Pi.mul_apply, map_mul]

private def ggTP_diagHom {K : Type} [Field K] (ω : Kˣ) (hω : orderOf ω = 3) :
    (Fin 6 → Multiplicative (ZMod 3)) →* GL (Fin 6) K :=
  (Units.map (Matrix.diagonalRingHom (Fin 6) K)).comp (ggTP_diagUnitHom ω hω)

private lemma ggTP_diagHom_coe {K : Type} [Field K] (ω : Kˣ) (hω : orderOf ω = 3)
    (x : Fin 6 → Multiplicative (ZMod 3)) :
    (ggTP_diagHom ω hω x : Matrix (Fin 6) (Fin 6) K)
      = Matrix.diagonal (fun i => (ggTP_zmod3Hom ω hω (x i) : K)) := by
  simp only [ggTP_diagHom, MonoidHom.comp_apply, Units.coe_map,
    Matrix.diagonalRingHom_apply]
  rfl

private lemma ggTP_diagHom_mem_sl {K : Type} [Field K] [CharP K 2] (ω : Kˣ)
    (hω : orderOf ω = 3) (x : GGTPTorus) :
    ggTP_diagHom ω hω (x : Fin 6 → Multiplicative (ZMod 3)) ∈
      LargeEvenSLGroup (Fin 6) K := by
  rw [LargeEvenSLGroup, MonoidHom.mem_ker]
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, ggTP_diagHom_coe, Matrix.det_diagonal]
  have hprod : (∏ i, ggTP_zmod3Hom ω hω ((x : Fin 6 → Multiplicative (ZMod 3)) i)) = 1 := by
    rw [← map_prod (ggTP_zmod3Hom ω hω)
      (fun i => (x : Fin 6 → Multiplicative (ZMod 3)) i) Finset.univ]
    rw [x.2, map_one]
  rw [← Units.coe_prod, hprod]

private def ggTP_permGL {K : Type} [Field K] (σ : Equiv.Perm (Fin 6)) : GL (Fin 6) K where
  val := Equiv.Perm.permMatrix K σ.symm
  inv := Equiv.Perm.permMatrix K σ
  val_inv := by
    rw [← Matrix.permMatrix_mul (σ := σ) (τ := σ.symm), Equiv.Perm.mul_symm]
    exact Matrix.permMatrix_one
  inv_val := by
    rw [← Matrix.permMatrix_mul (σ := σ.symm) (τ := σ), Equiv.Perm.symm_mul]
    exact Matrix.permMatrix_one

private lemma ggTP_sign_cast_eq_one {K : Type} [Field K] [CharP K 2]
    (σ : Equiv.Perm (Fin 6)) : ((Equiv.Perm.sign σ : ℤˣ) : K) = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h]; simp
  · rw [h]; simp [CharTwo.neg_eq]

private lemma ggTP_permGL_mem_sl {K : Type} [Field K] [CharP K 2]
    (σ : Equiv.Perm (Fin 6)) : ggTP_permGL σ ∈ LargeEvenSLGroup (Fin 6) K := by
  rw [LargeEvenSLGroup, MonoidHom.mem_ker]
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  change Matrix.det (Equiv.Perm.permMatrix K σ.symm) = 1
  rw [Matrix.det_permutation]
  exact ggTP_sign_cast_eq_one σ.symm

private lemma ggTP_permMatrix_conj {K : Type} [Field K] (σ : Equiv.Perm (Fin 6))
    (d : Fin 6 → K) :
    Equiv.Perm.permMatrix K σ.symm * Matrix.diagonal d * Equiv.Perm.permMatrix K σ
      = Matrix.diagonal (d ∘ σ.symm) := by
  rw [Matrix.mul_assoc]
  change σ.symm.toPEquiv.toMatrix * (Matrix.diagonal d * σ.toPEquiv.toMatrix)
    = Matrix.diagonal (d ∘ ⇑σ.symm)
  rw [PEquiv.mul_toMatrix_toPEquiv]
  rw [PEquiv.toMatrix_toPEquiv_mul]
  simp only [Matrix.submatrix_submatrix, Function.id_comp, Function.comp_id,
    Matrix.submatrix_diagonal_equiv]

private lemma ggTP_diag_mem_scalar_iff {K : Type} [Field K] (ω : Kˣ) (hω : orderOf ω = 3)
    (x : Fin 6 → Multiplicative (ZMod 3)) :
    ggTP_diagHom ω hω x ∈ (Matrix.GeneralLinearGroup.scalar (Fin 6)).range
      ↔ ∀ i j, x i = x j := by
  constructor
  · rintro ⟨c, hc⟩
    have hmat : (Matrix.GeneralLinearGroup.scalar (Fin 6) c : Matrix (Fin 6) (Fin 6) K)
        = (ggTP_diagHom ω hω x : Matrix (Fin 6) (Fin 6) K) := by rw [hc]
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ggTP_diagHom_coe,
        Matrix.diagonal_eq_diagonal_iff] at hmat
    intro i j
    have h1 : ggTP_zmod3Hom ω hω (x i) = ggTP_zmod3Hom ω hω (x j) := by
      apply Units.ext
      exact (hmat i).symm.trans (hmat j)
    exact ggTP_zmod3Hom_injective ω hω h1
  · intro hconst
    refine ⟨ggTP_zmod3Hom ω hω (x 0), ?_⟩
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ggTP_diagHom_coe,
        Matrix.diagonal_eq_diagonal_iff]
    intro i
    exact congrArg (fun u => (ggTP_zmod3Hom ω hω u : K)) (hconst 0 i)

private def ggTP_slHom {K : Type} [Field K] [CharP K 2] (ω : Kˣ) (hω : orderOf ω = 3) :
    GGTPTorus →* ↥(LargeEvenSLGroup (Fin 6) K) :=
  MonoidHom.codRestrict ((ggTP_diagHom ω hω).comp GGTPTorus.subtype)
    (LargeEvenSLGroup (Fin 6) K) (fun x => ggTP_diagHom_mem_sl ω hω x)

private lemma ggTP_slHom_coe {K : Type} [Field K] [CharP K 2] (ω : Kˣ) (hω : orderOf ω = 3)
    (x : GGTPTorus) :
    ((ggTP_slHom ω hω x : ↥(LargeEvenSLGroup (Fin 6) K)) : GL (Fin 6) K)
      = ggTP_diagHom ω hω (x : Fin 6 → Multiplicative (ZMod 3)) := rfl

theorem ggTPTorus_PSL6 {K : Type} [Field K] [Finite K] [CharP K 2] (h3 : 3 ∣ Nat.card K - 1) :
    ∃ (δ : GGTPTorus →* LargeEvenProj (LargeEvenSLGroup (Fin 6) K))
      (w : Equiv.Perm (Fin 6) → LargeEvenProj (LargeEvenSLGroup (Fin 6) K)),
      (∀ x : GGTPTorus, δ x = 1 ↔ (x : Fin 6 → Multiplicative (ZMod 3)) ∈ GGTPTorusConst) ∧
        ∀ (σ : Equiv.Perm (Fin 6)) (x : GGTPTorus), w σ * δ x * (w σ)⁻¹ = δ (ggTPPermAct σ x) := by
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rw [Nat.card_units]; exact h3)
  let N : Subgroup ↥(LargeEvenSLGroup (Fin 6) K) :=
    (LargeEvenScalars (Fin 6) K).subgroupOf (LargeEvenSLGroup (Fin 6) K)
  let δ : GGTPTorus →* LargeEvenProj (LargeEvenSLGroup (Fin 6) K) :=
    (QuotientGroup.mk' N).comp (ggTP_slHom ω hω)
  let w : Equiv.Perm (Fin 6) → LargeEvenProj (LargeEvenSLGroup (Fin 6) K) :=
    fun σ => (QuotientGroup.mk' N)
      ⟨ggTP_permGL σ, ggTP_permGL_mem_sl σ⟩
  refine ⟨δ, w, ?_, ?_⟩
  · intro x
    have h1 : δ x = 1 ↔ (ggTP_slHom ω hω x) ∈ N := by
      dsimp only [δ, MonoidHom.comp_apply]
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rw [h1, Subgroup.mem_subgroupOf, ggTP_slHom_coe, largeEvenScalars_def,
        ggTP_diag_mem_scalar_iff]
    rfl
  · intro σ x
    have hlift : (⟨ggTP_permGL σ, ggTP_permGL_mem_sl σ⟩ : ↥(LargeEvenSLGroup (Fin 6) K))
          * ggTP_slHom ω hω x
          * (⟨ggTP_permGL σ, ggTP_permGL_mem_sl σ⟩ : ↥(LargeEvenSLGroup (Fin 6) K))⁻¹
        = ggTP_slHom ω hω (ggTPPermAct σ x) := by
      apply Subtype.ext
      apply Units.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Matrix.GeneralLinearGroup.coe_mul]
      change Equiv.Perm.permMatrix K σ.symm
          * Matrix.diagonal (fun i => (ggTP_zmod3Hom ω hω
              ((x : Fin 6 → Multiplicative (ZMod 3)) i) : K))
          * Equiv.Perm.permMatrix K σ
        = Matrix.diagonal (fun i => (ggTP_zmod3Hom ω hω
            (((ggTPPermAct σ x : GGTPTorus) : Fin 6 → Multiplicative (ZMod 3)) i) : K))
      rw [ggTP_permMatrix_conj]
      rfl
    dsimp only [δ, w, MonoidHom.comp_apply]
    rw [← MonoidHom.map_inv, ← MonoidHom.map_mul, ← MonoidHom.map_mul, hlift]

end CFSG.StandardType

end
