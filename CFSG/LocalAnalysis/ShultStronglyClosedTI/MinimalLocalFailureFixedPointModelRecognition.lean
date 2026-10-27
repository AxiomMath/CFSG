module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearModelPointStructureTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryModelPointStructure
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCyclicOddQuotientSets
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.StrongEmbeddingMaximality
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LocalEmbeddingInheritance
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePointQuotient
public import CFSG.StronglyEmbedded.BenderNormalSeries
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma312
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.PairInvolutionFixedFieldAlgebra
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePointRoot

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.FixedPointModel

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePoint
  (native_rank_two_of_two_le_twoRank)
open scoped MatrixGroups

variable {L : Type*} [Group L] [Finite L]

theorem fusionStronglyEmbedded_map_quotient
    {M N : Subgroup L} [N.Normal]
    (hM : fusionStronglyEmbedded M) (hNM : N ≤ M) (hN : Odd (Nat.card N)) :
    fusionStronglyEmbedded (M.map (QuotientGroup.mk' N)) :=
  order_strong_embedding_of_native
    (IsStronglyEmbedded.map_quotient_of_odd_kernel (fusionStronglyEmbedded.to_native hM) hNM hN)

omit [Finite L] in
theorem card_involutions_map_mulEquiv {P : Type*} [Group P] (e : L ≃* P) (B : Subgroup L) :
    Nat.card {g : P | g ∈ B.map e.toMonoidHom ∧ orderOf g = 2} =
      Nat.card {g : L | g ∈ B ∧ orderOf g = 2} := by
  symm
  apply Nat.card_congr
  refine
    { toFun := fun g => ⟨e g, Subgroup.mem_map_of_mem _ g.2.1, (e.orderOf_eq g).trans g.2.2⟩
      invFun := fun g => ⟨e.symm g, Subgroup.mem_map_equiv.mp g.2.1,
        (e.orderOf_eq (e.symm g)).symm.trans (by rw [e.apply_symm_apply]; exact g.2.2)⟩
      left_inv := fun g => Subtype.ext (e.symm_apply_apply g)
      right_inv := fun g => Subtype.ext (e.apply_symm_apply g) }

omit [Finite L] in
theorem coset_equiv_of_stabilizer {P X : Type*} [Group P] [MulAction P X]
    (htrans : MulAction.IsPretransitive P X) (ρ : L →* P) (hρ : Function.Surjective ρ)
    (x₀ : X) {M : Subgroup L} (hM : ∀ l, l ∈ M ↔ ρ l ∈ MulAction.stabilizer P x₀) :
    ∃ φ : L ⧸ M ≃ X, φ (QuotientGroup.mk 1) = x₀ ∧
      ∀ (l : L) (x : L ⧸ M), φ (l • x) = ρ l • φ x := by
  let : MulAction L X := MulAction.compHom X ρ
  have hstab : MulAction.stabilizer L x₀ = M := by
    ext l
    rw [hM]
    rfl
  have hsurj : Function.Surjective (MulAction.ofQuotientStabilizer L x₀) := by
    intro x
    obtain ⟨p, hp⟩ := MulAction.exists_smul_eq P x₀ x
    obtain ⟨l, rfl⟩ := hρ p
    exact ⟨QuotientGroup.mk l, hp⟩
  let ψ := Equiv.ofBijective _ ⟨MulAction.injective_ofQuotientStabilizer L x₀, hsurj⟩
  refine ⟨(Subgroup.quotientEquivOfEq hstab.symm).trans ψ, ?_, ?_⟩
  · change MulAction.ofQuotientStabilizer L x₀
      (Subgroup.quotientEquivOfEq hstab.symm (QuotientGroup.mk 1)) = x₀
    rw [Subgroup.quotientEquivOfEq_mk, MulAction.ofQuotientStabilizer_mk, one_smul]
  · intro l x
    induction x using QuotientGroup.induction_on with
    | H y =>
      change MulAction.ofQuotientStabilizer L x₀
          (Subgroup.quotientEquivOfEq hstab.symm (QuotientGroup.mk (l * y))) =
        ρ l • MulAction.ofQuotientStabilizer L x₀
          (Subgroup.quotientEquivOfEq hstab.symm (QuotientGroup.mk y))
      rw [Subgroup.quotientEquivOfEq_mk, Subgroup.quotientEquivOfEq_mk,
        MulAction.ofQuotientStabilizer_mk, MulAction.ofQuotientStabilizer_mk, mul_smul]
      rfl

theorem strongly_embedded_model_transfer
    {P X : Type*} [Group P] [Finite P] [MulAction P X]
    (htrans : MulAction.IsPretransitive P X) {M : Subgroup L} (hM : fusionStronglyEmbedded M)
    (hNM : CFSG.oddCore L ≤ M) (hNZ : CFSG.oddCore L ≤ Subgroup.center L)
    (e : L ⧸ CFSG.oddCore L ≃* P) (x₀ : X)
    (hB : fusionStronglyEmbedded (MulAction.stabilizer P x₀)) (hrank : TwoRankAtLeastTwo P) :
    ∃ e' : L ⧸ CFSG.oddCore L ≃* P,
      (M.map (QuotientGroup.mk' (CFSG.oddCore L))).map e'.toMonoidHom =
          MulAction.stabilizer P x₀ ∧
        Nat.card {x : L | x ∈ M ∧ orderOf x = 2} =
          Nat.card {g : P | g ∈ MulAction.stabilizer P x₀ ∧ orderOf g = 2} ∧
        ∃ φ : L ⧸ M ≃ X, φ (QuotientGroup.mk 1) = x₀ ∧
          ∀ (l : L) (x : L ⧸ M), φ (l • x) = e' (QuotientGroup.mk l) • φ x := by
  let N := CFSG.oddCore L
  let π := QuotientGroup.mk' N
  have hNodd : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card L
  have hker : π.ker = N := QuotientGroup.ker_mk' N
  have hMbar : fusionStronglyEmbedded (M.map π) := fusionStronglyEmbedded_map_quotient hM hNM hNodd
  obtain ⟨g, hg⟩ := rank_two_strongEmbedding_conjugate hrank _ _ (hMbar.map_mulEquiv e) hB
  let e' : L ⧸ N ≃* P := e.trans (MulAut.conj g⁻¹)
  have he' : (M.map π).map e'.toMonoidHom = MulAction.stabilizer P x₀ := by
    rw [← hg, Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
    rfl
  refine ⟨e', he', ?_, ?_⟩
  · rw [CyclicPair.OddQuotient.subgroup_involution_card π (QuotientGroup.mk'_surjective N)
      (by rw [hker]; exact hNZ) (by rw [hker]; exact hNodd) M (by rw [hker]; exact hNM), ← he',
      card_involutions_map_mulEquiv]
  · apply coset_equiv_of_stabilizer htrans (e'.toMonoidHom.comp π)
      (e'.surjective.comp (QuotientGroup.mk'_surjective N)) x₀
    intro l
    rw [← he', Subgroup.mem_map_equiv]
    change l ∈ M ↔ e'.symm (e' (π l)) ∈ M.map π
    rw [MulEquiv.symm_apply_apply]
    constructor
    · exact Subgroup.mem_map_of_mem π
    · intro hl
      obtain ⟨m, hm, hml⟩ := Subgroup.mem_map.mp hl
      have hdiff : m⁻¹ * l ∈ N := by
        rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hml, inv_mul_cancel]
      have hlm : l = m * (m⁻¹ * l) := by group
      rw [hlm]
      exact M.mul_mem hm (hNM hdiff)

omit [Finite L] in
theorem parameter_eq_of_card {q q' : ℕ} (h : q - 1 = q' - 1) (hq' : 4 ≤ q') : q = q' := by
  omega

section Linear

open CFSG.GorensteinWalter
open scoped LinearAlgebra.Projectivization

theorem linear_point_data {f : ℕ} (hf : 2 ≤ f) :
    MulAction.IsPretransitive (PSL2MatrixGroup (GaloisField 2 f))
        (ℙ (GaloisField 2 f) (Fin 2 → GaloisField 2 f)) ∧
      fusionStronglyEmbedded (psl2Borel (GaloisField 2 f)) ∧
      TwoRankAtLeastTwo (PSL2MatrixGroup (GaloisField 2 f)) ∧
      Nat.card {g : PSL2MatrixGroup (GaloisField 2 f) |
        g ∈ psl2Borel (GaloisField 2 f) ∧ orderOf g = 2} = 2 ^ f - 1 ∧
      Nat.card (ℙ (GaloisField 2 f) (Fin 2 → GaloisField 2 f)) = 2 ^ f + 1 := by
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have h := LinearModel.linearPointAction_psl2 hcard
  have := h.isMultiplyPretransitive
  refine ⟨MulAction.isPretransitive_of_is_two_pretransitive, h.stronglyEmbedded, ?_, ?_,
    h.card_eq⟩
  · exact native_rank_two_of_two_le_twoRank (hf.trans h.le_twoRank)
  · rw [Nat.card_coe_set_eq]
    exact h.ncard_involutions

theorem linear_model_recognition
    {M : Subgroup L} (hM : fusionStronglyEmbedded M)
    (hNM : CFSG.oddCore L ≤ M) (hNZ : CFSG.oddCore L ≤ Subgroup.center L)
    {f : ℕ} (hf : 2 ≤ f) (e : L ⧸ CFSG.oddCore L ≃* PSL(2, GaloisField 2 f)) {q : ℕ}
    (hinv : Nat.card {x : L | x ∈ M ∧ orderOf x = 2} = q - 1) :
    q = 2 ^ f ∧ M.index = q + 1 ∧
      ∃ (e' : L ⧸ CFSG.oddCore L ≃* PSL(2, GaloisField 2 f))
        (φ : L ⧸ M ≃ ℙ (GaloisField 2 f) (Fin 2 → GaloisField 2 f)),
        (M.map (QuotientGroup.mk' (CFSG.oddCore L))).map e'.toMonoidHom =
            psl2Borel (GaloisField 2 f) ∧
          φ (QuotientGroup.mk 1) = psl2ProjectiveInfinity (GaloisField 2 f) ∧
          ∀ (l : L) (x : L ⧸ M), φ (l • x) = e' (QuotientGroup.mk l) • φ x := by
  obtain ⟨htrans, hB, hrank, hcount, hdeg⟩ := linear_point_data hf
  obtain ⟨e', he', hcard, φ, hφ1, hφ⟩ :=
    strongly_embedded_model_transfer htrans hM hNM hNZ e (psl2ProjectiveInfinity _) hB hrank
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hq : q = 2 ^ f := parameter_eq_of_card (hinv.symm.trans (hcard.trans hcount)) h4
  refine ⟨hq, ?_, e', φ, he', hφ1, hφ⟩
  rw [Subgroup.index, Nat.card_congr φ, hdeg, hq]

end Linear

section Suzuki

open CFSG.LieType.Ree CFSG.Blueprint

theorem suzuki_point_data
    {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    MulAction.IsPretransitive (suzukiGroup a K) (suzukiOmegaSub hK) ∧
      fusionStronglyEmbedded (MulAction.stabilizer (suzukiGroup a K)
        (⟨suzukiInfty K, suzukiInfty_mem_suzukiOmega a K⟩ : suzukiOmegaSub hK)) ∧
      TwoRankAtLeastTwo (suzukiGroup a K) ∧
      Nat.card {g : suzukiGroup a K | g ∈ MulAction.stabilizer (suzukiGroup a K)
        (⟨suzukiInfty K, suzukiInfty_mem_suzukiOmega a K⟩ : suzukiOmegaSub hK) ∧
          orderOf g = 2} = 2 ^ (2 * a + 1) - 1 ∧
      Nat.card (suzukiOmegaSub hK) = (2 ^ (2 * a + 1)) ^ 2 + 1 := by
  have h := SuzukiModel.suzukiPointAction_suzukiGroup hK
  have := h.isMultiplyPretransitive
  refine ⟨MulAction.isPretransitive_of_is_two_pretransitive, h.stronglyEmbedded,
    native_rank_two_of_two_le_twoRank (le_trans (by omega) h.le_twoRank), ?_, h.card_eq⟩
  rw [Nat.card_coe_set_eq]
  exact h.ncard_involutions

theorem suzuki_model_recognition
    {M : Subgroup L} (hM : fusionStronglyEmbedded M)
    (hNM : CFSG.oddCore L ≤ M) (hNZ : CFSG.oddCore L ≤ Subgroup.center L)
    {a : ℕ} (ha : 1 ≤ a) (e : L ⧸ CFSG.oddCore L ≃* Sz a) {q : ℕ}
    (hinv : Nat.card {x : L | x ∈ M ∧ orderOf x = 2} = q - 1) :
    q = 2 ^ (2 * a + 1) ∧ M.index = q ^ 2 + 1 ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (hK : Nat.card K = 2 ^ (2 * a + 1))
        (e' : L ⧸ CFSG.oddCore L ≃* suzukiGroup a K) (φ : L ⧸ M ≃ suzukiOmegaSub hK),
        (M.map (QuotientGroup.mk' (CFSG.oddCore L))).map e'.toMonoidHom = suzukiB a K ∧
          φ (QuotientGroup.mk 1) = ⟨suzukiInfty K, suzukiInfty_mem_suzukiOmega a K⟩ ∧
          ∀ (l : L) (x : L ⧸ M), φ (l • x) = e' (QuotientGroup.mk l) • φ x := by
  have hK : Nat.card (GaloisField 2 (2 * a + 1)) = 2 ^ (2 * a + 1) :=
    GaloisField.card 2 (2 * a + 1) (by omega)
  let e₁ : L ⧸ CFSG.oddCore L ≃* suzukiGroup a (GaloisField 2 (2 * a + 1)) :=
    e.trans ((suzukiCoverNativeEquiv a).trans
      (SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hK).symm)
  obtain ⟨htrans, hB, hrank, hcount, hdeg⟩ := suzuki_point_data ha hK
  obtain ⟨e', he', hcard, φ, hφ1, hφ⟩ :=
    strongly_embedded_model_transfer htrans hM hNM hNZ e₁ _ hB hrank
  have h4 : 4 ≤ 2 ^ (2 * a + 1) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq : q = 2 ^ (2 * a + 1) :=
    parameter_eq_of_card (hinv.symm.trans (hcard.trans hcount)) h4
  refine ⟨hq, ?_, GaloisField 2 (2 * a + 1), inferInstance, inferInstance, hK, e', φ,
    he'.trans (suzuki_ovoid_stabilizer hK).2, hφ1, hφ⟩
  rw [Subgroup.index, Nat.card_congr φ, hdeg, hq]

end Suzuki

section Unitary

open TwoCoreGrowth
open scoped LinearAlgebra.Projectivization

theorem unitary_point_involution_card {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
    {f : ℕ} (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Nat.card {g : ProjectiveSpecialUnitaryMatrixGroup J |
      g ∈ unitaryCoordinateStabilizer J 0 ∧ orderOf g = 2} = 2 ^ f - 1 := by
  let G := ProjectiveSpecialUnitaryMatrixGroup J
  let : Fintype K := Fintype.ofFinite K
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f * 2) (by
    simpa only [Nat.card_eq_fintype_card, ← pow_mul] using hcard)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hUT, -, -, -, ⟨S, hS⟩, -, -, -, -, -,
    hinvc, -, -⟩ := UnitaryModel.unitary_three_point_structure J f hf hcard hfixed hJ
  obtain ⟨-, -, hZsq, hZcard, -⟩ :=
    bender_projectiveSpecialUnitary_borel J f hf hcard hfixed hJ S
  let Z : Subgroup G := (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype
  have hZ : Nat.card Z = 2 ^ f := by
    rw [Subgroup.card_map_of_injective (S : Subgroup G).subtype_injective, hZcard]
  have hUB : (S : Subgroup G) ≤ unitaryCoordinateStabilizer J 0 := hS ▸ hUT ▸ le_sup_left
  have hset : {g : G | g ∈ unitaryCoordinateStabilizer J 0 ∧ orderOf g = 2} =
      (Z : Set G) \ {1} := by
    ext g
    constructor
    · rintro ⟨hgB, hg2⟩
      obtain ⟨hgU, hgc⟩ := hinvc g hgB hg2
      have hgS : g ∈ (S : Subgroup G) := hS ▸ hgU
      refine ⟨⟨⟨g, hgS⟩, Subgroup.mem_center_iff.mpr fun x => Subtype.ext ?_, rfl⟩, ?_⟩
      · exact hgc x (hS ▸ x.2)
      · intro hg1
        rw [Set.mem_singleton_iff.mp hg1, orderOf_one] at hg2
        exact absurd hg2 (by norm_num)
    · rintro ⟨⟨z, hz, rfl⟩, hz1⟩
      have hz1' : (z : G) ≠ 1 := fun h => hz1 (Set.mem_singleton_iff.mpr h)
      refine ⟨hUB z.2, orderOf_eq_prime ?_ hz1'⟩
      change (z : G) ^ 2 = 1
      rw [← Subgroup.coe_pow, hZsq z hz, Subgroup.coe_one]
  rw [hset, PairInvolutionFixedField.card_diff_one, hZ]

theorem unitary_model_recognition
    {M : Subgroup L} (hM : fusionStronglyEmbedded M)
    (hNM : CFSG.oddCore L ≤ M) (hNZ : CFSG.oddCore L ≤ Subgroup.center L)
    {f : ℕ} (hf : 2 ≤ f) (e : L ⧸ CFSG.oddCore L ≃* PSU3 2 f) {q : ℕ}
    (hinv : Nat.card {x : L | x ∈ M ∧ orderOf x = 2} = q - 1) :
    q = 2 ^ f ∧ M.index = q ^ 3 + 1 ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (J : HermitianForm 3 K)
        (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]),
        Nat.card K = q ^ 2 ∧ Nat.card {x : K // J.conj x = x} = q ∧
        ∃ (e' : L ⧸ CFSG.oddCore L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
          (φ : L ⧸ M ≃ unitaryIsotropicPoints J),
          (M.map (QuotientGroup.mk' (CFSG.oddCore L))).map e'.toMonoidHom =
              unitaryCoordinateStabilizer J 0 ∧
            φ (QuotientGroup.mk 1) = unitaryOuterIsotropicPoint J hJ 0 (by decide) ∧
            ∀ (l : L) (x : L ⧸ M),
              ((φ (l • x) : unitaryIsotropicPoints J) : ℙ K (Fin 3 → K)) =
                ((e' (QuotientGroup.mk l) : ProjectiveSpecialUnitaryMatrixGroup J) :
                    Matrix.ProjGenLinGroup (Fin 3) K) •
                  ((φ x : unitaryIsotropicPoints J) : ℙ K (Fin 3 → K)) := by
  let K := FiniteField.Extension (GaloisField 2 f) 2 2
  let J := binaryQuadraticHermitian f (by omega)
  have hcard : Nat.card K = (2 ^ f) ^ 2 := by
    rw [FiniteField.natCard_extension, GaloisField.card 2 f (by omega)]
  have hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f :=
    quadraticBinaryFrobenius_fixed_card f (by omega)
  have hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  let G := ProjectiveSpecialUnitaryMatrixGroup J
  let Ω := unitaryIsotropicPoints J
  have hmodel : PSU3Model f = PSU3 2 f := CFSG.Models.benderPSU3Model_eq_psu3 f
  let u : G ≃* PSU3 2 f :=
    (projectiveSpecialUnitary_equiv_PSU3Model J f hf hJ hcard hfixed).some.trans
      (MulEquiv.subgroupCongr hmodel)
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let : Finite G := Finite.of_injective
    (fun x : G => (x : Matrix.ProjGenLinGroup (Fin 3) K)) Subtype.coe_injective
  obtain ⟨-, -, -, -, -, rho, -, hnative, hΩcard, htwo, hstab, -, -, -, -, -, -, -, -, -, -,
    hB, hrank2, -, -, -, -⟩ := UnitaryModel.unitary_three_point_structure J f hf hcard hfixed hJ
  let : MulAction G Ω := MulAction.compHom Ω rho
  let α := unitaryOuterIsotropicPoint J hJ 0 (by decide)
  have hstab' : MulAction.stabilizer G α = unitaryCoordinateStabilizer J 0 := by
    rw [← hstab]
    rfl
  have htrans : MulAction.IsPretransitive G Ω := by
    refine ⟨fun x y => ?_⟩
    by_cases hxy : x = y
    · exact ⟨1, by rw [hxy, one_smul]⟩
    · obtain ⟨g, hg, -⟩ := htwo x y y x hxy (Ne.symm hxy)
      exact ⟨g, hg⟩
  obtain ⟨e', he', hcount, φ, hφ1, hφ⟩ :=
    strongly_embedded_model_transfer htrans hM hNM hNZ (e.trans u.symm) α (hstab' ▸ hB)
      (native_rank_two_of_two_le_twoRank hrank2)
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hq : q = 2 ^ f := by
    refine parameter_eq_of_card (hinv.symm.trans (hcount.trans ?_)) h4
    rw [hstab']
    exact unitary_point_involution_card J hf hcard hfixed hJ
  refine ⟨hq, ?_, K, inferInstance, inferInstance, J, hJ, hq ▸ hcard, hq ▸ hfixed, e', φ,
    he'.trans hstab', hφ1, fun l x => ?_⟩
  · rw [Subgroup.index, Nat.card_congr φ, hΩcard, hq]
  · rw [hφ l x]
    exact hnative _ _

end Unitary

section Recognition

open CFSG.GorensteinWalter CFSG.LieType.Ree CFSG.Blueprint TwoCoreGrowth
open scoped LinearAlgebra.Projectivization

@[expose] def IsModelCosetAction
    (L : Type*) [Group L] (M : Subgroup L) (q i : ℕ) : Prop :=
  (i = 1 ∧ ∃ f : ℕ, 2 ≤ f ∧ q = 2 ^ f ∧
    ∃ (e : L ⧸ CFSG.oddCore L ≃* PSL(2, GaloisField 2 f))
      (φ : L ⧸ M ≃ ℙ (GaloisField 2 f) (Fin 2 → GaloisField 2 f)),
      (M.map (QuotientGroup.mk' (CFSG.oddCore L))).map e.toMonoidHom =
          psl2Borel (GaloisField 2 f) ∧
        φ (QuotientGroup.mk 1) = psl2ProjectiveInfinity (GaloisField 2 f) ∧
        ∀ (l : L) (x : L ⧸ M), φ (l • x) = e (QuotientGroup.mk l) • φ x) ∨
  (i = 2 ∧ ∃ a : ℕ, 1 ≤ a ∧ q = 2 ^ (2 * a + 1) ∧ Nonempty (L ⧸ CFSG.oddCore L ≃* Sz a) ∧
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (hK : Nat.card K = 2 ^ (2 * a + 1))
      (e : L ⧸ CFSG.oddCore L ≃* suzukiGroup a K) (φ : L ⧸ M ≃ suzukiOmegaSub hK),
      (M.map (QuotientGroup.mk' (CFSG.oddCore L))).map e.toMonoidHom = suzukiB a K ∧
        φ (QuotientGroup.mk 1) = ⟨suzukiInfty K, suzukiInfty_mem_suzukiOmega a K⟩ ∧
        ∀ (l : L) (x : L ⧸ M), φ (l • x) = e (QuotientGroup.mk l) • φ x) ∨
  (i = 3 ∧ ∃ f : ℕ, 2 ≤ f ∧ q = 2 ^ f ∧ Nonempty (L ⧸ CFSG.oddCore L ≃* PSU3 2 f) ∧
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (J : HermitianForm 3 K)
      (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]),
      Nat.card K = q ^ 2 ∧ Nat.card {x : K // J.conj x = x} = q ∧
      ∃ (e : L ⧸ CFSG.oddCore L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
        (φ : L ⧸ M ≃ unitaryIsotropicPoints J),
        (M.map (QuotientGroup.mk' (CFSG.oddCore L))).map e.toMonoidHom =
            unitaryCoordinateStabilizer J 0 ∧
          φ (QuotientGroup.mk 1) = unitaryOuterIsotropicPoint J hJ 0 (by decide) ∧
          ∀ (l : L) (x : L ⧸ M),
            ((φ (l • x) : unitaryIsotropicPoints J) : ℙ K (Fin 3 → K)) =
              ((e (QuotientGroup.mk l) : ProjectiveSpecialUnitaryMatrixGroup J) :
                  Matrix.ProjGenLinGroup (Fin 3) K) •
                ((φ x : unitaryIsotropicPoints J) : ℙ K (Fin 3 → K)))

theorem fixed_point_model_recognition
    {M : Subgroup L} (hM : fusionStronglyEmbedded M)
    (hNM : CFSG.oddCore L ≤ M) (hNZ : CFSG.oddCore L ≤ Subgroup.center L)
    (hmodel : fusionIsBenderGroup (L ⧸ CFSG.oddCore L)) {q : ℕ}
    (hinv : Nat.card {x : L | x ∈ M ∧ orderOf x = 2} = q - 1) :
    fusionStronglyEmbedded (M.map (QuotientGroup.mk' (CFSG.oddCore L))) ∧
      Nat.card {y : L ⧸ CFSG.oddCore L |
        y ∈ M.map (QuotientGroup.mk' (CFSG.oddCore L)) ∧ orderOf y = 2} = q - 1 ∧
      ∃ i : ℕ, IsModelCosetAction L M q i ∧ M.index = q ^ i + 1 := by
  let N := CFSG.oddCore L
  have hNodd : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card L
  have hker : (QuotientGroup.mk' N).ker = N := QuotientGroup.ker_mk' N
  refine ⟨fusionStronglyEmbedded_map_quotient hM hNM hNodd, ?_, ?_⟩
  · rw [← CyclicPair.OddQuotient.subgroup_involution_card (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N) (by rw [hker]; exact hNZ) (by rw [hker]; exact hNodd) M
      (by rw [hker]; exact hNM), hinv]
  · rcases hmodel with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
    · obtain ⟨hq, hindex, h⟩ := linear_model_recognition hM hNM hNZ hf e hinv
      exact ⟨1, Or.inl ⟨rfl, f, hf, hq, h⟩, by rw [hindex, pow_one]⟩
    · obtain ⟨hq, hindex, h⟩ := unitary_model_recognition hM hNM hNZ hf e hinv
      exact ⟨3, Or.inr (Or.inr ⟨rfl, f, hf, hq, ⟨e⟩, h⟩), hindex⟩
    · obtain ⟨hq, hindex, h⟩ := suzuki_model_recognition hM hNM hNZ ha e hinv
      exact ⟨2, Or.inr (Or.inl ⟨rfl, a, ha, hq, ⟨e⟩, h⟩), hindex⟩

omit [Finite L] in
theorem coset_two_transitive_of_equiv {M : Subgroup L} {P X : Type*} {ρ : L → P}
    (hρ : Function.Surjective ρ) (act : P → X → X) (φ : L ⧸ M ≃ X)
    (hφ : ∀ (l : L) (x : L ⧸ M), φ (l • x) = act (ρ l) (φ x))
    (htwo : ∀ b c d e : X, b ≠ c → d ≠ e → ∃ g : P, act g b = d ∧ act g c = e) :
    ∀ x₁ x₂ x₃ x₄ : L ⧸ M, x₁ ≠ x₂ → x₃ ≠ x₄ → ∃ l : L, l • x₁ = x₃ ∧ l • x₂ = x₄ := by
  intro x₁ x₂ x₃ x₄ h₁₂ h₃₄
  obtain ⟨g, hg₁, hg₂⟩ := htwo _ _ _ _ (φ.injective.ne h₁₂) (φ.injective.ne h₃₄)
  obtain ⟨l, rfl⟩ := hρ g
  exact ⟨l, φ.injective (by rw [hφ, hg₁]), φ.injective (by rw [hφ, hg₂])⟩

omit [Finite L] in
theorem IsModelCosetAction.two_transitive {M : Subgroup L} {q i : ℕ}
    (h : IsModelCosetAction L M q i) :
    ∀ x₁ x₂ x₃ x₄ : L ⧸ M, x₁ ≠ x₂ → x₃ ≠ x₄ → ∃ l : L, l • x₁ = x₃ ∧ l • x₂ = x₄ := by
  have hπ : Function.Surjective (QuotientGroup.mk : L → L ⧸ CFSG.oddCore L) :=
    QuotientGroup.mk_surjective
  rcases h with ⟨-, f, hf, -, e, φ, -, -, hφ⟩ | ⟨-, a, -, -, -, K, _, _, hK, e, φ, -, -, hφ⟩ |
    ⟨-, f, hf, hq, -, K, _, _, J, hJ, hcard, hfixed, e, φ, -, -, hφ⟩
  · have h2 := (LinearModel.linearPointAction_psl2
      (GaloisField.card 2 f (by omega))).isMultiplyPretransitive
    exact coset_two_transitive_of_equiv (e.surjective.comp hπ) (fun g x => g • x) φ hφ
      (fun b c d e hbc hde => MulAction.is_two_pretransitive_iff.mp h2 hbc hde)
  · have h2 := (SuzukiModel.suzukiPointAction_suzukiGroup hK).isMultiplyPretransitive
    exact coset_two_transitive_of_equiv (e.surjective.comp hπ) (fun g x => g • x) φ hφ
      (fun b c d e hbc hde => MulAction.is_two_pretransitive_iff.mp h2 hbc hde)
  · subst hq
    obtain ⟨-, -, -, -, -, rho, -, hnative, -, htwo, -⟩ :=
      UnitaryModel.unitary_three_point_structure J f hf hcard hfixed hJ
    refine coset_two_transitive_of_equiv (e.surjective.comp hπ) (fun g x => rho g x) φ
      (fun l x => Subtype.ext ((hφ l x).trans (hnative _ _).symm)) htwo

end Recognition

end CFSG.ShultStronglyClosedTI.FixedPointModel
