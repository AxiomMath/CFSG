module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Model
public import CFSG.ClassicalInvolution.Orders.OrthogonalCount
public import CFSG.ClassicalGroups.Orthogonal.Matrix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin
open scoped MatrixGroups Matrix

namespace OmegaModel

variable {W : Type} [CommGroup W] (S : OmegaModel W)

@[expose] def linSub : Subgroup (MulAut W) where
  carrier := {g | ∀ (c : S.K) (w : W), g (S.smul c w) = S.smul c (g w)}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro g h hg hh c w
    rw [MulAut.mul_apply, MulAut.mul_apply, hh, hg]
  inv_mem' := by
    intro g hg c w
    have h1 : g (S.smul c (g⁻¹ w)) = S.smul c w := by
      rw [hg, MulAut.apply_inv_self]
    calc g⁻¹ (S.smul c w) = g⁻¹ (g (S.smul c (g⁻¹ w))) := by rw [h1]
      _ = S.smul c (g⁻¹ w) := MulAut.inv_apply_self W g _

@[expose] def smulAut (c : S.Kˣ) : MulAut W where
  toFun := S.smul c
  invFun := S.smul (c⁻¹ : S.Kˣ)
  left_inv w := by
    rw [smul_smul_eq]
    simp [smul_one_eq]
  right_inv w := by
    rw [smul_smul_eq]
    simp [smul_one_eq]
  map_mul' := S.smul_mul_eq c

@[expose] def smulAutHom : S.Kˣ →* MulAut W where
  toFun := smulAut S
  map_one' := by
    ext w
    exact S.smul_one_eq w
  map_mul' c d := by
    ext w
    exact (S.smul_smul_eq c d w).symm

@[expose] def scalarSub : Subgroup (MulAut W) := (smulAutHom S).range

@[expose] def isoSub : Subgroup (MulAut W) :=
  (CFSG.MatrixModel.isometryCore (StatedQuadPlus 2 S.K)).map S.actHom

abbrev omegaNorm : Subgroup (MulAut W) :=
  Subgroup.normalizer (S.omega : Set (MulAut W))

theorem mem_linSub_iff {g : MulAut W} :
    g ∈ linSub S ↔ ∀ (c : S.K) (w : W), g (S.smul c w) = S.smul c (g w) :=
  Iff.rfl

theorem smulAut_apply (c : S.Kˣ) (w : W) : smulAut S c w = S.smul c w := rfl

private theorem statedOmega_le_isometryCore (Q₀ : (OmI → S.K) → S.K) :
    StatedOmega Q₀ ≤ CFSG.MatrixModel.isometryCore Q₀ := by
  have h : StatedOmega Q₀ =
      ⁅CFSG.MatrixModel.isometryCore Q₀, CFSG.MatrixModel.isometryCore Q₀⁆ :=
    rfl
  rw [h]
  refine Subgroup.commutator_le.2 fun a ha b hb => ?_
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
    (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)

theorem omega_le_isoSub : S.omega ≤ isoSub S := by
  change (StatedOmega (StatedQuadPlus 2 S.K)).map S.actHom ≤
    (CFSG.MatrixModel.isometryCore (StatedQuadPlus 2 S.K)).map S.actHom
  exact Subgroup.map_mono (statedOmega_le_isometryCore S (StatedQuadPlus 2 S.K))

theorem scalarSub_le_linSub : scalarSub S ≤ linSub S := by
  rintro z ⟨c, rfl⟩
  change smulAut S c ∈ linSub S
  intro c' w
  rw [smulAut_apply, smulAut_apply, smul_smul_eq, smul_smul_eq, mul_comm]

theorem scalarSub_commute {z g : MulAut W} (hz : z ∈ scalarSub S) (hg : g ∈ linSub S) :
    z * g = g * z := by
  obtain ⟨c, rfl⟩ := hz
  change smulAut S c * g = g * smulAut S c
  ext w
  rw [MulAut.mul_apply, MulAut.mul_apply, smulAut_apply, smulAut_apply]
  exact (hg c w).symm

private theorem mem_isometryCore_iff {Q₀ : (OmI → S.K) → S.K} (A : GL OmI S.K) :
    A ∈ CFSG.MatrixModel.isometryCore Q₀ ↔
      ∀ v : OmI → S.K, Q₀ ((A : Matrix OmI OmI S.K) *ᵥ v) = Q₀ v := by
  constructor
  · intro hA
    unfold CFSG.MatrixModel.isometryCore at hA
    induction hA using Subgroup.closure_induction with
    | mem x hx => exact hx
    | one => intro v; simp
    | mul x y _ _ hx hy =>
        intro v
        rw [Units.val_mul, ← Matrix.mulVec_mulVec, hx, hy]
    | inv x _ hx =>
        intro v
        have h1 : (x : Matrix OmI OmI S.K) *
            ((x⁻¹ : GL OmI S.K) : Matrix OmI OmI S.K) = 1 := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
        have h := hx (((x⁻¹ : GL OmI S.K) : Matrix OmI OmI S.K) *ᵥ v)
        rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] at h
        exact h.symm
  · exact fun h => Subgroup.subset_closure h

theorem mem_isoSub_iff {g : MulAut W} :
    g ∈ isoSub S ↔ g ∈ linSub S ∧ ∀ w : W, S.Q (g w) = S.Q w := by
  constructor
  · intro hg
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hg
    constructor
    · intro c w
      apply S.vec_injective
      rw [S.actHom_vec, S.vec_smul, Matrix.mulVec_smul, S.vec_smul, S.actHom_vec]
    · intro w
      have hpres := (mem_isometryCore_iff S γ).mp hγ (S.vec w)
      simpa only [Q, S.actHom_vec] using hpres
  · rintro ⟨hg, hQ⟩
    obtain ⟨γ, hγ⟩ := S.exists_actHom_of_smul_comm ((mem_linSub_iff S).mp hg)
    refine Subgroup.mem_map.mpr ⟨γ, ?_, hγ⟩
    refine (mem_isometryCore_iff S γ).mpr fun v => ?_
    have h1 : S.vec (g (S.ofVec v)) = (γ : Matrix OmI OmI S.K) *ᵥ v := by
      rw [← hγ, S.actHom_vec, S.vec_ofVec]
    rw [← h1]
    show S.Q (g (S.ofVec v)) = StatedQuadPlus 2 S.K v
    rw [hQ (S.ofVec v)]
    show StatedQuadPlus 2 S.K (S.vec (S.ofVec v)) = StatedQuadPlus 2 S.K v
    rw [S.vec_ofVec]

private theorem smulAutHom_injective : Function.Injective (smulAutHom S) := by
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

theorem card_scalarSub (hK : Nat.card S.K = 8) : Nat.card (scalarSub S) = 7 := by
  have hinj := smulAutHom_injective S
  have hcard : Nat.card (scalarSub S) = Nat.card S.Kˣ :=
    Nat.card_congr (MonoidHom.ofInjective (f := smulAutHom S) hinj).toEquiv.symm
  rw [hcard, Nat.card_units S.K, hK]

theorem scalarSub_inf_isoSub : scalarSub S ⊓ isoSub S = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hz1, hz2⟩
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hz1
  rw [Subgroup.mem_bot, ← hc]
  change smulAut S c = 1
  have hpres : ∀ w : W, S.Q (smulAut S c w) = S.Q w := by
    intro w
    have hz2' : smulAutHom S c ∈ isoSub S := by rw [hc]; exact hz2
    exact ((mem_isoSub_iff S).mp hz2').2 w
  obtain ⟨w, hw⟩ := S.exists_Q_ne_zero
  have hsq : (c : S.K) ^ 2 = 1 := by
    have h1 : (c : S.K) ^ 2 * S.Q w = S.Q w := by
      rw [← S.Q_smul]
      exact hpres w
    exact (mul_right_cancel₀ hw) (by rw [h1, one_mul])
  have hc1 : c = 1 := Units.ext (CharTwo.sq_inj.mp (by simpa using hsq))
  rw [hc1]
  exact map_one (smulAutHom S)

private theorem card_isometryCore {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
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

private theorem cast_prod {q : ℕ} (hq : 1 ≤ q) (m : ℕ) :
    ((∏ i ∈ Finset.Icc 1 m, (q ^ (2 * i) - 1) : ℕ) : ℤ) =
      ∏ i ∈ Finset.Icc 1 m, ((q : ℤ) ^ (2 * i) - 1) := by
  rw [Nat.cast_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Nat.cast_sub (Nat.one_le_pow _ _ hq)]
  push_cast
  ring

private theorem card_isoCore_quadPlus (m : ℕ) :
    Nat.card (CFSG.MatrixModel.isometryCore (StatedQuadPlus (m + 1) S.K)) =
      2 * Nat.card S.K ^ (m * (m + 1)) * (Nat.card S.K ^ (m + 1) - 1) *
        ∏ i ∈ Finset.Icc 1 m, (Nat.card S.K ^ (2 * i) - 1) := by
  rw [card_isometryCore (CFSG.LieType.Universal.Spin.coe_quadPlus (m + 1) S.K)]
  have hq : 1 ≤ Nat.card S.K := Finite.card_pos
  apply Nat.cast_injective (R := ℤ)
  rw [(CFSG.ClassicalInvolution.card_singular_and_orthogonalGroup_quadPlus
    (K := S.K) m).2]
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_sub (Nat.one_le_pow _ _ hq), cast_prod hq]
  push_cast
  ring

theorem card_isoSub (hK : Nat.card S.K = 8) : Nat.card (isoSub S) = 508032 := by
  change Nat.card
    ((CFSG.MatrixModel.isometryCore (StatedQuadPlus 2 S.K)).map S.actHom) = 508032
  rw [Subgroup.card_map_of_injective S.actHom_injective]
  rw [card_isoCore_quadPlus S 1, hK, Finset.Icc_self, Finset.prod_singleton]
  norm_num

private theorem card_sup_of_commute_of_inf_eq_bot {G : Type*} [Group G] {A B : Subgroup G}
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

theorem card_scalarSub_sup_isoSub (hK : Nat.card S.K = 8) :
    Nat.card (scalarSub S ⊔ isoSub S : Subgroup (MulAut W)) = 7 * 508032 := by
  have hcomm : ∀ a ∈ scalarSub S, ∀ b ∈ isoSub S, a * b = b * a :=
    fun a ha b hb => scalarSub_commute S ha ((mem_isoSub_iff S).mp hb).1
  rw [card_sup_of_commute_of_inf_eq_bot hcomm (scalarSub_inf_isoSub S),
    card_scalarSub S hK, card_isoSub S hK]

end OmegaModel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
