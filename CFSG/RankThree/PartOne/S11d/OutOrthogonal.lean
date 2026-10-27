module

public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.RankThree.PartOne.KC.OrthogonalCommutatorCore
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearTags
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearBridge

public section

namespace CFSG.RankThree.PartOne.OutStructure

open Matrix Subgroup QuadraticMap CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
open scoped commutatorElement

section Generic

variable {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

theorem matrixProjectiveConjugation_incl (A : matrixDerived Q) (B : matrixDerived Q) :
    matrixProjectiveConjugation Q (matrixDerivedInclusion Q A) (matrixProjectiveProjection Q B) =
      MulAut.conj (matrixProjectiveProjection Q A) (matrixProjectiveProjection Q B) := by
  rw [matrixProjectiveConjugation_mk, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem inner_le_range (δ : MulAut (matrixProjectiveDerived Q))
    (hδ : δ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q)) :
    ∃ A : matrixDerived Q, matrixProjectiveConjugationHom Q (matrixDerivedInclusion Q A) = δ := by
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hδ
  obtain ⟨A, rfl⟩ := matrixProjectiveProjection_surjective Q x
  refine ⟨A, MulEquiv.ext fun y => ?_⟩
  obtain ⟨B, rfl⟩ := matrixProjectiveProjection_surjective Q y
  exact matrixProjectiveConjugation_incl Q A B

open CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer (matrixLinearEquiv_scalar)

theorem exists_isometry_of_linear [Finite K] [CharP K 2] (hQ : ∃ v, Q v ≠ 0)
    (g : linearSimilarityPairs Q) :
    ∃ B : matrixIsometries Q, ∀ C : matrixDerived Q,
      (matrixDerivedConjugation Q g.val C).val = B.val * C.val * B.val⁻¹ := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨c, hc⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2)
    (multiplierHom Q hQ g : K)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc
    exact (multiplierHom Q hQ g).ne_zero hc
  set u : Kˣ := Units.mk0 c hc0 with hu
  set A : GL (Fin d) K := g.val.val.left with hA
  set B : GL (Fin d) K := (GeneralLinearGroup.scalar (Fin d) u)⁻¹ * A with hB
  have hAB : A = GeneralLinearGroup.scalar (Fin d) u * B := by rw [hB]; group
  have hBiso : B ∈ matrixIsometries Q := by
    rw [mem_matrixIsometries_iff]
    intro v
    have h1 := multiplierHom_spec Q hQ g v
    have h2 : matrixLinearEquiv g.val.val.left v = (u : K) • matrixLinearEquiv B v := by
      rw [← hA, hAB, matrixLinearEquiv_mul, LinearEquiv.mul_apply, matrixLinearEquiv_scalar]
    have h3 : Q (matrixLinearEquiv g.val.val.left v) = (u : K) ^ 2 * Q (matrixLinearEquiv B v) := by
      rw [h2, QuadraticMap.map_smul, smul_eq_mul, _root_.sq]
    have h4 : (multiplierHom Q hQ g : K) = (u : K) ^ 2 := by rw [hc, hu, _root_.sq]; rfl
    rw [h3, h4] at h1
    exact mul_left_cancel₀ (pow_ne_zero 2 u.ne_zero) h1
  refine ⟨⟨B, hBiso⟩, fun C => ?_⟩
  rw [matrixDerivedConjugation_val, (mem_linearSimilarityPairs_iff Q g.val).mp g.property]
  have hs : GeneralLinearGroup.scalar (Fin d) u ∈ Subgroup.center (GL (Fin d) K) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨u, rfl⟩
  have hcomm : ∀ M : GL (Fin d) K, GeneralLinearGroup.scalar (Fin d) u * M =
      M * GeneralLinearGroup.scalar (Fin d) u := fun M =>
    (Subgroup.mem_center_iff.mp hs M).symm
  have hid : (CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldAut (Fin d) K 1)
      C.val = C.val := by
    rw [map_one, MulAut.one_apply]
  rw [hid]
  change A * C.val * A⁻¹ = B * C.val * B⁻¹
  rw [hAB, _root_.mul_inv_rev]
  generalize GeneralLinearGroup.scalar (Fin d) u = s at hcomm ⊢
  calc s * B * C.val * (B⁻¹ * s⁻¹) = s * (B * C.val * B⁻¹) * s⁻¹ := by simp only [mul_assoc]
    _ = ((B * C.val * B⁻¹) * s) * s⁻¹ := by rw [hcomm]
    _ = B * C.val * B⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]

noncomputable def orthD : Subgroup (MulAut (matrixProjectiveDerived Q)) :=
  (linearSimilarityPairs Q).map (matrixProjectiveConjugationHom Q)

theorem mem_orthD_iff (δ : MulAut (matrixProjectiveDerived Q)) :
    δ ∈ orthD Q ↔ ∃ g : linearSimilarityPairs Q, matrixProjectiveConjugationHom Q g.val = δ := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g.val, g.property, rfl⟩

theorem inner_le_orthD :
    CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q) ≤
      orthD Q := by
  intro δ hδ
  obtain ⟨A, rfl⟩ := inner_le_range Q δ hδ
  exact ⟨matrixDerivedInclusion Q A, rfl, rfl⟩

theorem orthD_sq_mem_inner [Finite K] [CharP K 2] (hQ : ∃ v, Q v ≠ 0)
    (hnd : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {δ : MulAut (matrixProjectiveDerived Q)} (hδ : δ ∈ orthD Q) :
    δ ^ 2 ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q) := by
  obtain ⟨g, rfl⟩ := (mem_orthD_iff Q δ).mp hδ
  obtain ⟨B, hB⟩ := exists_isometry_of_linear Q hQ g
  have hsq : B.val * B.val ∈ matrixDerived Q := by
    obtain ⟨-, -, -, -, -, hsq, -⟩ :=
      CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hnd hT
    have h1 := hsq (matrixLinearIso B.val) B.property
    rw [pow_two, ← map_mul, ← CFSG.RankThree.PartOne.KCOrthogonalAut.map_matrixDerived Q] at h1
    obtain ⟨z, hz, hzx⟩ := h1
    have : z = B.val * B.val := matrixLinearIso.injective hzx
    rwa [this] at hz
  refine MonoidHom.mem_range.mpr ⟨matrixProjectiveProjection Q ⟨B.val * B.val, hsq⟩, ?_⟩
  refine MulEquiv.ext fun y => ?_
  obtain ⟨C, rfl⟩ := matrixProjectiveProjection_surjective Q y
  rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, pow_two, MulAut.mul_apply]
  have e1 : ∀ C' : matrixDerived Q, matrixProjectiveConjugationHom Q g.val
      (matrixProjectiveProjection Q C') =
      matrixProjectiveProjection Q (matrixDerivedConjugation Q g.val C') :=
    fun C' => matrixProjectiveConjugation_mk Q g.val C'
  rw [e1, e1]
  congr 1
  apply Subtype.ext
  rw [hB, hB]
  change (B.val * B.val) * C.val * (B.val * B.val)⁻¹ = B.val * (B.val * C.val * B.val⁻¹) * B.val⁻¹
  group

theorem orthD_D2 [Finite K] [CharP K 2] (hQ : ∃ v, Q v ≠ 0) (hnd : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {δ : MulAut (matrixProjectiveDerived Q)} (hδ : δ ∈ orthD Q)
    {k : ℕ}
    (hk : δ ^ (p ^ k) ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (matrixProjectiveDerived Q)) :
    δ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q) := by
  have hsq := orthD_sq_mem_inner Q hQ hnd hT hδ
  obtain ⟨m, hm⟩ := (Nat.Prime.odd_of_ne_two hp hp2).pow (n := k)
  have h2 : ((δ ^ 2)⁻¹) ^ m ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q) :=
    Subgroup.pow_mem _ (inv_mem hsq) m
  have : δ = δ ^ (p ^ k) * ((δ ^ 2)⁻¹) ^ m := by
    rw [hm]
    group
  rw [this]
  exact mul_mem hk h2

theorem comm_mem_orthD [Finite K] (g h : similarityPairs Q) :
    ⁅matrixProjectiveConjugationHom Q g, matrixProjectiveConjugationHom Q h⁆ ∈ orthD Q := by
  rw [← map_commutatorElement]
  exact ⟨⁅g, h⁆, similarity_commutator_le_linear Q
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top h)), rfl⟩

theorem exists_gen [Finite K] :
    ∃ g₀ : similarityPairs Q, ∀ h : similarityPairs Q, ∃ k : ℤ,
      g₀ ^ k * h ∈ linearSimilarityPairs Q := by
  have hcyc := fieldQuotient_cyclic Q
  obtain ⟨γ, hγ⟩ := hcyc.exists_generator
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective γ
  refine ⟨g₀, fun h => ?_⟩
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hγ (QuotientGroup.mk h))
  refine ⟨-m, ?_⟩
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_zpow, _root_.zpow_neg,
    ← hm]
  simp

theorem outPNice_of_image_top [Finite K] [CharP K 2] (hnd : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (htop : matrixProjectiveImage Q = ⊤) :
    OutPNice p (matrixProjectiveDerived Q) := by
  have hQ : ∃ v, Q v ≠ 0 := CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  obtain ⟨g₀, hg₀⟩ := exists_gen Q
  have hmem : ∀ α : MulAut (matrixProjectiveDerived Q),
      ∃ g : similarityPairs Q, matrixProjectiveConjugationHom Q g = α := fun α =>
    (mem_matrixProjectiveImage_iff Q α).mp (htop ▸ Subgroup.mem_top α)
  exact outPNice_of_tower hp (matrixProjectiveConjugationHom Q g₀) (D := orthD Q) (E := ⊤)
    (fun δ hδ => inner_le_orthD Q hδ) (fun δ hδ k hk => orthD_D2 Q hQ hnd hT hp hp2 hδ hk)
    (fun α _ => trivial)
    (fun γ α _ => by
      obtain ⟨g, rfl⟩ := hmem γ
      obtain ⟨h, rfl⟩ := hmem α
      exact comm_mem_orthD Q g h)
    (fun α _ => by
      obtain ⟨h, rfl⟩ := hmem α
      obtain ⟨k, hk⟩ := hg₀ h
      exact ⟨k, ⟨g₀ ^ k * h, hk, by rw [map_mul, map_zpow]⟩⟩)

theorem outPChain_of_image_index_le_three [Finite K] [CharP K 2]
    (hnd : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hidx : (matrixProjectiveImage Q).index ≤ 3) :
    OutPChain p (matrixProjectiveDerived Q) := by
  have hQ : ∃ v, Q v ≠ 0 := CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have hp2 : p ≠ 2 := by omega
  obtain ⟨g₀, hg₀⟩ := exists_gen Q
  have : Finite (matrixProjectiveDerived Q) := inferInstance
  have : Finite (MulAut (matrixProjectiveDerived Q)) := inferInstance
  have hDE : orthD Q ≤ matrixProjectiveImage Q := Subgroup.map_le_range _ _
  have hRing : Finite (K ≃+* K) :=
    Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) DFunLike.coe_injective
  have hfin : Finite (similarityPairs Q) :=
    Finite.of_injective (fun g : similarityPairs Q => (g.val.left, g.val.right)) fun g h hgh =>
      Subtype.ext (SemidirectProduct.ext (congrArg Prod.fst hgh) (congrArg Prod.snd hgh))
  have hDn : ((orthD Q).comap (matrixProjectiveConjugationHom Q)).Normal := ⟨fun d hd x => by
    obtain ⟨ℓ, hℓ, hℓd⟩ := Subgroup.mem_comap.mp hd
    refine Subgroup.mem_comap.mpr ⟨x * ℓ * x⁻¹, (linearPairsNormal Q).conj_mem ℓ hℓ x, ?_⟩
    simp only [map_mul, map_inv]
    rw [hℓd]⟩
  refine ⟨orthD Q, matrixProjectiveImage Q, fun δ hδ => inner_le_orthD Q hδ,
    fun δ hδ k hk => orthD_D2 Q hQ hnd hT hp hp2 hδ hk, ?_, ?_⟩
  · rintro α ⟨k, hk⟩
    exact mem_of_pow_mem_of_index_le_three _ hidx hp hp3 (hDE hk)
  · rintro α hα β hβ ⟨k, hk⟩ ⟨l, hl⟩
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hα
    obtain ⟨h, rfl⟩ := MonoidHom.mem_range.mp hβ
    have hk' : ∃ k : ℕ, g ^ (p ^ k) ∈ (orthD Q).comap (matrixProjectiveConjugationHom Q) :=
      ⟨k, Subgroup.mem_comap.mpr (by rw [map_pow]; exact hk)⟩
    have hl' : ∃ l : ℕ, h ^ (p ^ l) ∈ (orthD Q).comap (matrixProjectiveConjugationHom Q) :=
      ⟨l, Subgroup.mem_comap.mpr (by rw [map_pow]; exact hl)⟩
    have hE : ∀ x : similarityPairs Q, ∃ k : ℤ,
        g₀ ^ k * x ∈ (orthD Q).comap (matrixProjectiveConjugationHom Q) := fun x => by
      obtain ⟨k, hk⟩ := hg₀ x
      exact ⟨k, Subgroup.mem_comap.mpr ⟨_, hk, rfl⟩⟩
    rcases chain_of_cyclic_quotient hp g₀ hE g h hk' hl' with ⟨m, hm⟩ | ⟨m, hm⟩
    · exact Or.inl ⟨m, by simpa [map_mul, map_zpow] using Subgroup.mem_comap.mp hm⟩
    · exact Or.inr ⟨m, by simpa [map_mul, map_zpow] using Subgroup.mem_comap.mp hm⟩

end Generic

section Models

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open scoped Pointwise

theorem outPNice_POmegaPlus_ge_five {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Type} [Group X]
    {n m : ℕ} (hn : 5 ≤ n) (h : StatedClassicalModel X .POmegaPlus n 2 m) : OutPNice p X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := m) (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_plus h K hK e
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K n hn
  exact OutPNice.of_mulEquiv (coordinatePlusWitnessEquiv K e)
    (outPNice_of_image_top (coordinateQuadPlus n K) hnd hT hp hp2 htop)

theorem outPNice_POmegaMinus {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Type} [Group X]
    {n m : ℕ} (hn : 4 ≤ n) (h : StatedClassicalModel X .POmegaMinus n 2 m) : OutPNice p X := by
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := id h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := m) (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_minus h K hK b c hirr e
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn b c
    hirr
  exact OutPNice.of_mulEquiv (coordinateMinusWitnessEquiv K (by omega) b c e)
    (outPNice_of_image_top _ hnd hT hp hp2 htop)

theorem outPChain_POmegaPlus_four {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {X : Type} [Group X]
    {m : ℕ} (h : StatedClassicalModel X .POmegaPlus 4 2 m) : OutPChain p X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := m) (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_plus h K hK e
  have hEA := (orthogonal_geometry_plus_model_stabilizer_preserving_image h K hK e).1
  have horbit := orthogonal_geometry_plus_point_family_orbit h hK e
  have hidx : (matrixProjectiveImage (coordinateQuadPlus 4 K)).index ≤ 3 := by
    have hst : (projectivePointFamilyAut (coordinateQuadPlus 4 K)).index =
        (MulAction.orbit (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))
          (projectivePointFamily (coordinateQuadPlus 4 K))).ncard :=
      MulAction.index_stabilizer _ _
    rw [← hEA, hst]
    exact (horbit.2.2.2.2.2 rfl).2
  exact OutPChain.of_mulEquiv (coordinatePlusWitnessEquiv K e)
    (outPChain_of_image_index_le_three _ hnd hT hp hp3 hidx)

end Models

end CFSG.RankThree.PartOne.OutStructure
