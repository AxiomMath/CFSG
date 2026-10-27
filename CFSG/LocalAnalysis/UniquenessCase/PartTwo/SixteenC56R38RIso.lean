module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165OrdA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin
open scoped MatrixGroups Matrix

namespace OmegaModel

variable {W : Type} [CommGroup W] (S : OmegaModel W)

private theorem smulAutHom_injective' : Function.Injective (smulAutHom S) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  change smulAut S c = 1 at hc
  have hw : S.smul (c : S.K) (S.ofVec (Pi.single (Sum.inl 0) (1 : S.K))) =
      S.ofVec (Pi.single (Sum.inl 0) (1 : S.K)) := by
    have h := congrArg (fun f : MulAut W =>
      f (S.ofVec (Pi.single (Sum.inl 0) (1 : S.K)))) hc
    simpa [smulAut_apply] using h
  have hv := congrArg S.vec hw
  rw [S.vec_smul, S.vec_ofVec] at hv
  have h0 := congrFun hv (Sum.inl 0)
  simp at h0
  exact h0

theorem card_scalarSub_of_card_four (hK : Nat.card S.K = 4) : Nat.card (scalarSub S) = 3 := by
  have hinj := smulAutHom_injective' S
  have hcard : Nat.card (scalarSub S) = Nat.card S.Kˣ :=
    Nat.card_congr (MonoidHom.ofInjective (f := smulAutHom S) hinj).toEquiv.symm
  rw [hcard, Nat.card_units S.K, hK]

private theorem card_isometryCore' {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀) :
    Nat.card (CFSG.MatrixModel.isometryCore Q₀) =
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  have h : CFSG.MatrixModel.isometryCore Q₀ =
      (TauCeti.QuadraticMap.orthogonalGroup Q).comap
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).toMonoidHom :=
    CFSG.ClassicalGroups.Orthogonal.closure_isometries_eq_comap hQ
  have key : (TauCeti.QuadraticMap.orthogonalGroup Q).comap
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).toMonoidHom =
      (TauCeti.QuadraticMap.orthogonalGroup Q).map
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).symm.toMonoidHom :=
    Subgroup.comap_equiv_eq_map_symm (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K) _
  rw [h, key]
  exact Subgroup.card_map_of_injective (MulEquiv.injective _)

private theorem cast_prod' {q : ℕ} (hq : 1 ≤ q) (m : ℕ) :
    ((∏ i ∈ Finset.Icc 1 m, (q ^ (2 * i) - 1) : ℕ) : ℤ) =
      ∏ i ∈ Finset.Icc 1 m, ((q : ℤ) ^ (2 * i) - 1) := by
  rw [Nat.cast_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Nat.cast_sub (Nat.one_le_pow _ _ hq)]
  push_cast
  ring

private theorem card_isoCore_quadPlus' (m : ℕ) :
    Nat.card (CFSG.MatrixModel.isometryCore (StatedQuadPlus (m + 1) S.K)) =
      2 * Nat.card S.K ^ (m * (m + 1)) * (Nat.card S.K ^ (m + 1) - 1) *
        ∏ i ∈ Finset.Icc 1 m, (Nat.card S.K ^ (2 * i) - 1) := by
  rw [card_isometryCore' (CFSG.LieType.Universal.Spin.coe_quadPlus (m + 1) S.K)]
  have hq : 1 ≤ Nat.card S.K := Finite.card_pos
  apply Nat.cast_injective (R := ℤ)
  rw [(CFSG.ClassicalInvolution.card_singular_and_orthogonalGroup_quadPlus
    (K := S.K) m).2]
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_sub (Nat.one_le_pow _ _ hq), cast_prod' hq]
  push_cast
  ring

theorem card_isoSub_of_card_four (hK : Nat.card S.K = 4) : Nat.card (isoSub S) = 7200 := by
  change Nat.card
    ((CFSG.MatrixModel.isometryCore (StatedQuadPlus 2 S.K)).map S.actHom) = 7200
  rw [Subgroup.card_map_of_injective S.actHom_injective]
  rw [card_isoCore_quadPlus' S 1, hK, Finset.Icc_self, Finset.prod_singleton]
  norm_num

private theorem card_sup_of_commute_of_inf_eq_bot' {G : Type*} [Group G] {A B : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hd : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  have hcomm : ∀ (a : ↥A) (b : ↥B), Commute (A.subtype a) (B.subtype b) :=
    fun a b => hc a a.2 b b.2
  have hinj : Function.Injective (MonoidHom.noncommCoprod A.subtype B.subtype hcomm) := by
    refine (MonoidHom.noncommCoprod_injective A.subtype B.subtype hcomm).2 ?_
    refine ⟨A.subtype_injective, B.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype, disjoint_iff]
    exact hd
  have hrange : (MonoidHom.noncommCoprod A.subtype B.subtype hcomm).range = A ⊔ B := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  calc Nat.card ↥(A ⊔ B)
      = Nat.card (MonoidHom.noncommCoprod A.subtype B.subtype hcomm).range := by
        rw [hrange]
    _ = Nat.card (↥A × ↥B) := (Nat.card_congr (Equiv.ofInjective _ hinj)).symm
    _ = Nat.card A * Nat.card B := Nat.card_prod _ _

theorem card_scalarSub_sup_isoSub_of_card_four (hK : Nat.card S.K = 4) :
    Nat.card (scalarSub S ⊔ isoSub S : Subgroup (MulAut W)) = 3 * 7200 := by
  have hcomm : ∀ a ∈ scalarSub S, ∀ b ∈ isoSub S, a * b = b * a :=
    fun a ha b hb => scalarSub_commute S ha ((mem_isoSub_iff S).mp hb).1
  rw [card_sup_of_commute_of_inf_eq_bot' hcomm (scalarSub_inf_isoSub S),
    card_scalarSub_of_card_four S hK, card_isoSub_of_card_four S hK]

end OmegaModel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
