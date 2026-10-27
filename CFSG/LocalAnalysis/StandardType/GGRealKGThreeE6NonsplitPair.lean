module

public import CFSG.LocalAnalysis.StandardType.GGRealKGExcNegJ
public import CFSG.RankThree.Classical2.NegativeExchangedSL2
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompChain
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.SLnShape
public import CFSG.RankThree.PartOne.KE.ThreeA1Group

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KE CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem WSL_mul_mapFr_eq_negFrobSL {K L : Type} [Field K] [Fintype K] [Field L] [Algebra K L]
    [CharP L 2] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Fintype.card K) (A : SL2 L) :
    (WSL : SL2 L) * Matrix.SpecialLinearGroup.map Fr A * WSL = negFrobSL K L 2 A := by
  classical
  let B : SL2 L := Matrix.SpecialLinearGroup.map Fr A
  have hB : (B : Matrix (Fin 2) (Fin 2) L) =
      (A : Matrix (Fin 2) (Fin 2) L).map (· ^ Fintype.card K) := by
    ext i j
    simp only [B, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply]
    rw [hFr]
  have hA : (WSL : SL2 L) * Matrix.SpecialLinearGroup.map Fr A * WSL =
      (WSL : SL2 L) * B * WSL := rfl
  have hBinv : ((B : Matrix (Fin 2) (Fin 2) L))⁻¹ =
      ((B⁻¹ : SL2 L) : Matrix (Fin 2) (Fin 2) L) := by
    rw [Matrix.SpecialLinearGroup.coe_inv]
    have h : Matrix.adjugate (B : Matrix (Fin 2) (Fin 2) L) *
        (B : Matrix (Fin 2) (Fin 2) L) = 1 := by
      rw [Matrix.adjugate_mul, B.2, one_smul]
    exact Matrix.inv_eq_left_inv h
  rw [hA]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    coe_negFrobSL, ← hB, hBinv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [WSL, Matrix.mul_apply, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail,
      Fin.sum_univ_two, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.transpose_apply, CharTwo.neg_eq]


theorem ggKGExcY_range_of_stepFixed_perfect_E6 {K : Type} [Field K] [Finite K] [CharP K 2]
    {E : Subgroup (adjointGroup .E6 K)} (F : ExcFrame .E6 K 3 E)
    {P : Subgroup (ModGL .E6 (AlgebraicClosure K))} [Finite P]
    (hPC : P ≤ adjointGroup .E6 (AlgebraicClosure K))
    (hPF : P ≤ F.D.step.eqLocus (MonoidHom.id _))
    (hPperf : ⁅P, P⁆ = P) : P ≤ (ggKGExcY F).range := by
  classical
  obtain ⟨Fr, hFr, hΦ⟩ := F.frob
  let P' : Subgroup (ModGL .E6 (AlgebraicClosure K)) :=
    P.map (MulAut.conj F.D.g0).toMonoidHom
  have hP'fin : Finite P' := by
    refine Finite.of_surjective
      (fun x : P => (⟨MulAut.conj F.D.g0 (x : ModGL .E6 _), ?_⟩ : P')) ?_
    · exact Subgroup.mem_map_of_mem _ x.2
    · intro x
      obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.1 x.2
      exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩
  have : Finite P' := hP'fin
  have hP'C : P' ≤ adjointGroup .E6 (AlgebraicClosure K) := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hx
    exact mul_mem (mul_mem F.D.g0_mem (hPC hp)) (inv_mem F.D.g0_mem)
  have hP'F : ∀ x ∈ P', Units.map (entrywiseHom Fr) x = x := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hx
    have hstep : F.D.n * F.D.Φ p * F.D.n⁻¹ = p := hPF hp
    calc
      Units.map (entrywiseHom Fr) (F.D.g0 * p * F.D.g0⁻¹)
          = F.D.Φ (F.D.g0 * p * F.D.g0⁻¹) := (hΦ _).symm
      _ = F.D.Φ F.D.g0 * F.D.Φ p * (F.D.Φ F.D.g0)⁻¹ := by
        rw [map_mul, map_mul, map_inv]
      _ = (F.D.g0 * F.D.n) * F.D.Φ p * (F.D.g0 * F.D.n)⁻¹ := by rw [F.D.lang]
      _ = F.D.g0 * (F.D.n * F.D.Φ p * F.D.n⁻¹) * F.D.g0⁻¹ := by group
      _ = F.D.g0 * p * F.D.g0⁻¹ := by rw [hstep]
  have hP'perf : ⁅P', P'⁆ = P' := by
    dsimp only [P']
    rw [← Subgroup.map_commutator, hPperf]
  have hle : P' ≤ (adjointGroup .E6 K).map
      (baseChangeGL (algebraMap K (AlgebraicClosure K))) :=
    (finite_fixed_subgroup_rational_perfect (τ := .E6) (K := K)
      (L := AlgebraicClosure K) 3 (Or.inl ⟨rfl, rfl⟩) Fr hFr P' hP'C hP'F).2.2
      P' le_rfl hP'perf
  intro q hq
  have hq' : F.D.g0 * q * F.D.g0⁻¹ ∈ P' := Subgroup.mem_map_of_mem _ hq
  obtain ⟨r, hr, hrq⟩ := hle hq'
  refine ⟨⟨r, hr⟩, ?_⟩
  rw [ggKGExcY_apply]
  change F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) r * F.D.g0 = q
  rw [hrq]
  group

theorem e6NonsplitPair_rationalRoot {K : Type} [Field K] [Finite K] [CharP K 2]
    {E : Subgroup (adjointGroup .E6 K)} (F : ExcFrame .E6 K 3 E)
    {β γ : Fin Tag.E6.rank → ℤ} (hβ : IsRoot .E6 β) (hγ : IsRoot .E6 γ)
    (horth : iform β γ = 0) (hβγ : F.w • β = -γ) (hγβ : F.w • γ = -β)
    (hq : 4 ≤ Nat.card K) :
    ∃ J : Subgroup (adjointGroup .E6 K),
      J = ((rootRankOneGroup .E6 (AlgebraicClosure K) β ⊔
              rootRankOneGroup .E6 (AlgebraicClosure K) γ) ⊓
            F.D.step.eqLocus (MonoidHom.id _)).comap (ggKGExcY F) ∧
      J.map (ggKGExcY F) = ((rootRankOneGroup .E6 (AlgebraicClosure K) β ⊔
              rootRankOneGroup .E6 (AlgebraicClosure K) γ) ⊓
            F.D.step.eqLocus (MonoidHom.id _)) ∧
      CFSG.IsQuasisimple J ∧
      (3 ∣ Nat.card K + 1 → 3 ∣ Nat.card J) ∧
      ∃ r ∈ J, ggKGExcY F r =
        canonicalRep (coxeterSystem .E6) (AlgebraicClosure K)
          (rootReflection β * rootReflection γ) := by
  classical
  let : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Fr, hFr, hΦ⟩ := F.frob
  have hFr' : ∀ c, Fr c = c ^ Fintype.card K := by
    simpa only [Nat.card_eq_fintype_card] using hFr
  let f : SL2 (AlgebraicClosure K) →* ModGL .E6 (AlgebraicClosure K) :=
    rootSL2 .E6 (AlgebraicClosure K) β
  let g : SL2 (AlgebraicClosure K) →* ModGL .E6 (AlgebraicClosure K) :=
    rootSL2 .E6 (AlgebraicClosure K) γ
  have hfinj_f : Function.Injective f := rootSL2_injective_of_field β
  have hfinj_g : Function.Injective g := rootSL2_injective_of_field γ
  have hcomm : ∀ A B, Commute (f A) (g B) := fun A B =>
    commute_rootSL2_of_iform_eq_zero (by exact Or.inr (Or.inl rfl)) hβ hγ horth A B
  have hθf : ∀ A, F.D.step (f A) = g (negFrobSL K (AlgebraicClosure K) 2 A) := by
    intro A
    change F.D.step (rootSL2 .E6 (AlgebraicClosure K) β A) =
      rootSL2 .E6 (AlgebraicClosure K) γ (negFrobSL K (AlgebraicClosure K) 2 A)
    rw [ggRealKGNeg_step_rootSL2 (τ := .E6) F hΦ hβ hβγ A,
      WSL_mul_mapFr_eq_negFrobSL (K := K) (L := AlgebraicClosure K) Fr hFr' A]
  have hθg : ∀ A, F.D.step (g A) = f (negFrobSL K (AlgebraicClosure K) 2 A) := by
    intro A
    change F.D.step (rootSL2 .E6 (AlgebraicClosure K) γ A) =
      rootSL2 .E6 (AlgebraicClosure K) β (negFrobSL K (AlgebraicClosure K) 2 A)
    rw [ggRealKGNeg_step_rootSL2 (τ := .E6) F hΦ hγ hγβ A,
      WSL_mul_mapFr_eq_negFrobSL (K := K) (L := AlgebraicClosure K) Fr hFr' A]
  let eta : SL2 (frobSqFixedField K (AlgebraicClosure K)) →*
      ModGL .E6 (AlgebraicClosure K) := negExchangedPairEta K (AlgebraicClosure K) f g hcomm
  let Qfix : Subgroup (ModGL .E6 (AlgebraicClosure K)) :=
    (rootRankOneGroup .E6 (AlgebraicClosure K) β ⊔
      rootRankOneGroup .E6 (AlgebraicClosure K) γ) ⊓ F.D.step.eqLocus (MonoidHom.id _)
  have hQfix_eq : Qfix = eta.range := by
    dsimp only [Qfix, eta]
    have h := negExchangedPair_fixed_range K (AlgebraicClosure K) f g hfinj_f hfinj_g hcomm
      F.D.step hθf hθg
    simpa only [f, g, rootRankOneGroup] using h
  have hEtaQuasi : CFSG.IsQuasisimple eta.range := by
    dsimp only [eta]
    exact negExchangedPairEta_range_isQuasisimple K (AlgebraicClosure K) f g hfinj_f hfinj_g
      hcomm hq
  have hQfixQuasi : CFSG.IsQuasisimple Qfix := by
    rw [hQfix_eq]
    exact hEtaQuasi
  have : Finite (frobSqFixedField K (AlgebraicClosure K)) :=
    NegExchangedLayer.finite_frobSqFixedField (k := K) (Ω := AlgebraicClosure K)
  have hEtaFin : Finite eta.range := by
    have : Finite (SL2 (frobSqFixedField K (AlgebraicClosure K))) := inferInstance
    exact Finite.of_surjective eta.rangeRestrict (MonoidHom.rangeRestrict_surjective eta)
  have hQfixFin : Finite Qfix := by
    rw [hQfix_eq]
    exact hEtaFin
  have : Finite Qfix := hQfixFin
  have hQfixC : Qfix ≤ adjointGroup .E6 (AlgebraicClosure K) :=
    inf_le_left.trans (sup_le
      ((exceptional_Lang_root_rank_one_data .E6 (AlgebraicClosure K) β).2.2.2.2.2.1)
      ((exceptional_Lang_root_rank_one_data .E6 (AlgebraicClosure K) γ).2.2.2.2.2.1))
  have hQfixStep : Qfix ≤ F.D.step.eqLocus (MonoidHom.id _) := inf_le_right
  have hQfixLeRange : Qfix ≤ (ggKGExcY F).range :=
    ggKGExcY_range_of_stepFixed_perfect_E6 F hQfixC hQfixStep
      (LayerFacts.ggCommutator_eq_of_isQuasisimple hQfixQuasi)
  let J : Subgroup (adjointGroup .E6 K) := Qfix.comap (ggKGExcY F)
  have hJmap : J.map (ggKGExcY F) = Qfix := by
    dsimp only [J]
    refine le_antisymm (Subgroup.map_comap_le _ _) ?_
    rw [Subgroup.map_comap_eq]
    exact le_inf hQfixLeRange le_rfl
  let eJ : J ≃* J.map (ggKGExcY F) :=
    Subgroup.equivMapOfInjective J (ggKGExcY F) (ggKGExcY_injective F)
  let e : J ≃* Qfix := eJ.trans (MulEquiv.subgroupCongr hJmap)
  have hJquasi : CFSG.IsQuasisimple J :=
    (CFSG.IsQuasisimple.congr e).mpr hQfixQuasi
  have hJcard : Nat.card J = Nat.card Qfix := Nat.card_congr e.toEquiv
  have hQfixCard : Nat.card Qfix = Nat.card (SL2 (frobSqFixedField K (AlgebraicClosure K))) := by
    rw [hQfix_eq]
    exact (Nat.card_congr (negExchangedPairEtaEquiv K (AlgebraicClosure K) f g hfinj_f hfinj_g
      hcomm).toEquiv).symm
  have hk2 : Nat.card (frobSqFixedField K (AlgebraicClosure K)) = Nat.card K ^ 2 := by
    rw [natCard_frobSqFixedField, Nat.card_eq_fintype_card]
  have h3dvd : 3 ∣ Nat.card K + 1 → 3 ∣ Nat.card J := by
    intro h3
    rw [hJcard, hQfixCard, CFSG.Wreathed.CentralSL2.card_SL_two, hk2]
    have hq2 : 3 ∣ Nat.card K ^ 2 - 1 := by
      have hsq : Nat.card K ^ 2 - 1 = (Nat.card K + 1) * (Nat.card K - 1) := by
        simpa using Nat.sq_sub_sq (Nat.card K) 1
      rw [hsq]
      exact dvd_mul_of_dvd_left h3 _
    have hq4 : 3 ∣ (Nat.card K ^ 2) ^ 2 - 1 := by
      have hsq : (Nat.card K ^ 2) ^ 2 - 1 =
          (Nat.card K ^ 2 + 1) * (Nat.card K ^ 2 - 1) := by
        simpa using Nat.sq_sub_sq (Nat.card K ^ 2) 1
      rw [hsq]
      exact dvd_mul_of_dvd_right hq2 _
    exact dvd_mul_of_dvd_right hq4 _
  have hnegWSL : negFrobSL K (AlgebraicClosure K) 2
      (WSL : SL2 (AlgebraicClosure K)) = WSL := by
    have h := WSL_mul_mapFr_eq_negFrobSL (K := K) (L := AlgebraicClosure K)
      (FiniteField.frobeniusAlgHom K (AlgebraicClosure K))
      (fun c => by
        change (FiniteField.frobeniusAlgHom K (AlgebraicClosure K)) c =
          c ^ Fintype.card K
        rw [FiniteField.frobeniusAlgHom_apply]) (WSL : SL2 (AlgebraicClosure K))
    rw [CFSG.LieType.Chevalley.map_WSL, ggKGTj_WSL_sq_one, one_mul] at h
    exact h.symm
  have hq0eta : eta (WSL : SL2 (frobSqFixedField K (AlgebraicClosure K))) =
      rootSL2 .E6 (AlgebraicClosure K) β WSL *
        rootSL2 .E6 (AlgebraicClosure K) γ WSL := by
    dsimp only [eta, f, g]
    rw [negExchangedPairEta_apply, mapFrobSqFixedSL2_apply,
      CFSG.LieType.Chevalley.map_WSL, hnegWSL]
  have hβcanon : rootSL2 .E6 (AlgebraicClosure K) β WSL =
      canonicalRep (coxeterSystem .E6) (AlgebraicClosure K) (rootReflection β) := by
    rw [← CFSG.RankThree.Chevalley.EvenF4QPlus.rootWeylSL2_one_eq_canonicalRep_of_charTwo hβ]
    simp only [rootWeylSL2, nSL_one]
  have hγcanon : rootSL2 .E6 (AlgebraicClosure K) γ WSL =
      canonicalRep (coxeterSystem .E6) (AlgebraicClosure K) (rootReflection γ) := by
    rw [← CFSG.RankThree.Chevalley.EvenF4QPlus.rootWeylSL2_one_eq_canonicalRep_of_charTwo hγ]
    simp only [rootWeylSL2, nSL_one]
  have hq0canon : eta (WSL : SL2 (frobSqFixedField K (AlgebraicClosure K))) =
      canonicalRep (coxeterSystem .E6) (AlgebraicClosure K)
        (rootReflection β * rootReflection γ) := by
    rw [hq0eta, hβcanon, hγcanon]
    exact (CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo
      (rootReflection β) (rootReflection γ)).symm
  have hq0Q : eta (WSL : SL2 (frobSqFixedField K (AlgebraicClosure K))) ∈ Qfix := by
    rw [hQfix_eq]
    exact ⟨(WSL : SL2 (frobSqFixedField K (AlgebraicClosure K))), rfl⟩
  have hq0map : eta (WSL : SL2 (frobSqFixedField K (AlgebraicClosure K))) ∈
      J.map (ggKGExcY F) := by
    rw [hJmap]
    exact hq0Q
  obtain ⟨r, hr, hrY⟩ := Subgroup.mem_map.1 hq0map
  refine ⟨J, ?_, hJmap, hJquasi, h3dvd, r, hr, ?_⟩
  · dsimp only [J, Qfix]
  · exact hrY.trans hq0canon

end CFSG.StandardType

end
