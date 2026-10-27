module

public import CFSG.Quasithin.Background.F918Z4bDef
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoPglFaithful

public section

namespace CFSG.Quasithin

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem pglAction_injective_of_finite (K : Type) [Field K] [Finite K] :
    Function.Injective (pglAction K) :=
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction_injective K

@[expose] noncomputable def autFieldPart (K : Type) [Field K] [Finite K] :
    MulAut (PSL2 K) →* (K ≃+* K) :=
  SemidirectProduct.rightHom.comp (semilinearEquivAut K).symm.toMonoidHom

theorem mem_range_pglAction_of_autFieldPart_eq_one {K : Type} [Field K] [Finite K]
    {α : MulAut (PSL2 K)} (h : autFieldPart K α = 1) : α ∈ (pglAction K).range := by
  set x := (semilinearEquivAut K).symm α with hx
  have hα : semilinearAction K x = α := (semilinearEquivAut K).apply_symm_apply α
  have hr : x.right = 1 := h
  have hx2 := congrArg (semilinearAction K) (SemidirectProduct.inl_left_mul_inr_right x)
  rw [map_mul, semilinearAction_inl, semilinearAction_inr, hr, map_one, mul_one, hα] at hx2
  exact ⟨x.left, hx2⟩

theorem exists_toPGL_eq_of_charTwo {K : Type} [Field K] [Finite K] [CharP K 2] (g : PGL2 K) :
    ∃ x : PSL2 K, Matrix.ProjectiveSpecialLinearGroup.toPGL x = g := by
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  obtain ⟨d, hd⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (A.det : K)
  have hd_ne : d ≠ 0 := by
    intro hd0
    apply Units.ne_zero A.det
    rw [hd, hd0, mul_zero]
  set dU : Kˣ := Units.mk0 d hd_ne with hdU
  set B : GL (Fin 2) K := Matrix.GeneralLinearGroup.scalar (Fin 2) dU⁻¹ * A with hB
  have hBdet : Matrix.det (B : Matrix (Fin 2) (Fin 2) K) = 1 := by
    have h1 : Matrix.GeneralLinearGroup.det B = 1 := by
      rw [hB, map_mul, Matrix.GeneralLinearGroup.det_scalar]
      apply Units.ext
      change d⁻¹ ^ 2 * (A.det : K) = 1
      rw [hd]
      field_simp
    exact congrArg Units.val h1
  set Bs : Matrix.SpecialLinearGroup (Fin 2) K := ⟨(B : Matrix (Fin 2) (Fin 2) K), hBdet⟩
  refine ⟨QuotientGroup.mk' (Subgroup.center _) Bs, ?_⟩
  change Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL Bs) =
    Matrix.ProjGenLinGroup.mk A
  have htoGL : Matrix.SpecialLinearGroup.toGL Bs = B := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rfl
  rw [htoGL, hB, map_mul, Matrix.ProjGenLinGroup.mk_scalar, one_mul]

theorem exists_conj_of_autFieldPart_eq_one {K : Type} [Field K] [Finite K] [CharP K 2]
    {α : MulAut (PSL2 K)} (h : autFieldPart K α = 1) : ∃ x : PSL2 K, α = MulAut.conj x := by
  obtain ⟨g, rfl⟩ := mem_range_pglAction_of_autFieldPart_eq_one h
  obtain ⟨x, rfl⟩ := exists_toPGL_eq_of_charTwo g
  exact ⟨x, pglAction_toPGL K x⟩

theorem rk_le_rk_inf_inner_add_one_psl2 {K : Type} [Field K] [Finite K] [CharP K 2]
    {E : Subgroup (MulAut (PSL2 K))} (hE : IsElemAb2 E) :
    rk E ≤ rk ↥(E ⊓ (MulAut.conj : PSL2 K →* MulAut (PSL2 K)).range) + 1 := by
  classical
  let f : ↥E →* (K ≃+* K) := (autFieldPart K).comp E.subtype
  have : IsCyclic (K ≃+* K) := fieldAut_isCyclic K
  have : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hrange : Nat.card f.range ∣ 2 := by
    rw [← IsCyclic.exponent_eq_card]
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    rintro ⟨_, a, rfl⟩
    refine Subtype.ext ?_
    change f a ^ 2 = 1
    rw [← map_pow, show a ^ 2 = 1 from Subtype.ext (hE.2 a a.2), map_one]
  have hcard : Nat.card E = Nat.card f.range * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  have hker : f.ker.map E.subtype ≤ E ⊓ (MulAut.conj : PSL2 K →* MulAut (PSL2 K)).range := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨a.2, ?_⟩
    obtain ⟨x, hx⟩ := exists_conj_of_autFieldPart_eq_one (MonoidHom.mem_ker.mp ha)
    exact ⟨x, hx.symm⟩
  have h1 : rk f.ker ≤ rk ↥(E ⊓ (MulAut.conj : PSL2 K →* MulAut (PSL2 K)).range) := by
    rw [← rk_map_eq_of_injective E.subtype Subtype.val_injective]
    exact rk_mono hker
  have h2 : padicValNat 2 (Nat.card f.range) ≤ 1 :=
    (padicValNat_two_le_of_dvd (by norm_num) hrange).trans (padicValNat.self (by norm_num)).le
  unfold rk at h1 ⊢
  rw [hcard, padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne']
  omega

end CFSG.Quasithin
