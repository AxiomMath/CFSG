module

public import CFSG.Quasithin.Vol2.Ch11SecEFacts4
public import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedLinear
public import CFSG.LieType.SteinbergBRSemidirectSLEven

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

namespace O5

theorem out2Closed_of_comm {X : Type*} [Group X] [Finite X]
    (h : ∀ σ τ : MulAut X, σ * τ * σ⁻¹ * τ⁻¹ ∈ (MulAut.conj : X →* MulAut X).range) :
    Out2Closed X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup (MulAut X) := (MulAut.conj : X →* MulAut X).range with hN
  have : N.Normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal X
  have hcomm : ∀ a b : MulAut X ⧸ N, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H σ =>
      induction b using QuotientGroup.induction_on with
      | H τ =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        have e : (σ * τ)⁻¹ * (τ * σ) = τ⁻¹ * σ⁻¹ * τ⁻¹⁻¹ * σ⁻¹⁻¹ := by group
        rw [e]
        exact h τ⁻¹ σ⁻¹
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 (MulAut X ⧸ N)))
  have hSn : (S : Subgroup (MulAut X ⧸ N)).Normal :=
    ⟨fun s hs g => by rwa [hcomm g s, mul_inv_cancel_right]⟩
  refine ⟨(S : Subgroup (MulAut X ⧸ N)).comap (QuotientGroup.mk' N),
    Subgroup.Normal.comap hSn _, fun x hx => ?_, fun α hα => ?_, fun α => ?_⟩
  · rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  · obtain ⟨k, hk⟩ := S.isPGroup' ⟨QuotientGroup.mk' N α, hα⟩
    refine ⟨k, (QuotientGroup.eq_one_iff _).mp ?_⟩
    rw [QuotientGroup.mk_pow]
    exact congrArg Subtype.val hk
  · refine ⟨(S : Subgroup (MulAut X ⧸ N)).index, ?_, ?_⟩
    · rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
      exact S.not_dvd_index
    · rw [Subgroup.mem_comap, map_pow]
      exact Subgroup.pow_index_mem _ _

theorem out2Closed_of_mulEquiv_psl2 {X : Type} [Group X] [Finite X] {K : Type} [Field K]
    [Finite K] (e : X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) : Out2Closed X := by
  refine out2Closed_of_comm fun σ τ => ?_
  set c : MulAut X ≃* MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := MulAut.congr e
  have h := CFSG.LocalAnalysis.ComponentInitial.OuterDerived.outer_psl2_mul_comm K
    (c σ : Outer _) (c τ)
  have h1 : (QuotientGroup.mk (c σ * c τ * (c σ)⁻¹ * (c τ)⁻¹) :
      Outer (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, h]
    group
  obtain ⟨y, hy⟩ := (QuotientGroup.eq_one_iff _).mp h1
  refine ⟨e.symm y, c.injective ?_⟩
  rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, e.apply_symm_apply, hy]
  simp only [map_mul, map_inv]

end O5

open O5

theorem factOut2SL2_holds : FactOut2SL2 := by
  intro F _ _ n hn hF X _ ⟨e⟩
  have : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have : Finite X := Finite.of_equiv _ e.symm.toEquiv
  have hZ := CFSG.LieType.SteinbergBR.center_SL_eq_bot_of_charTwo (F := F) (m := 2) (by norm_num)
    (Or.inl rfl)
  exact out2Closed_of_mulEquiv_psl2 (e.trans
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm)

theorem factOut2L2p_holds : FactOut2L2p := by
  intro X _ _ p _ _ h
  obtain ⟨-, F, _, _, -, ⟨e⟩⟩ := h
  exact out2Closed_of_mulEquiv_psl2
    (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm)

end CFSG.Quasithin.Vol2.Ch11.SecE
