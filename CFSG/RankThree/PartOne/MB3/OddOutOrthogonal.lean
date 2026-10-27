module

public import CFSG.RankThree.PartOne.S11d.OutOrthogonal
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic

public section

namespace CFSG.RankThree.PartOne.OutStructure

open Matrix Subgroup QuadraticMap CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open scoped commutatorElement

section Generic

variable {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

theorem linearConjugationHom_range_eq_orthD :
    (linearConjugationHom Q).range = orthD Q := by
  ext δ
  rw [mem_orthD_iff, MonoidHom.mem_range]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g, rfl⟩

theorem orthD_relIndex_inner_not_dvd [Finite K] (hQ : ∃ v, Q v ≠ 0)
    (hab : Nat.card (Abelianization (matrixIsometries Q)) ≤ 4) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) :
    ¬ p ∣ (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (matrixProjectiveDerived Q)).relIndex (orthD Q) := by
  have h1 : CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q) ≤
      (isometryConjugationHom Q).range := by
    rw [inner_eq_map_commutator Q]
    exact Subgroup.map_le_range _ _
  have h2 : (isometryConjugationHom Q).range ≤ (linearConjugationHom Q).range :=
    isometryConjugationHom_range_le Q
  rw [← linearConjugationHom_range_eq_orthD, ← Subgroup.relIndex_mul_relIndex _ _ _ h1 h2]
  intro hdvd
  have : Finite (Abelianization (matrixIsometries Q)) := inferInstance
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
  · have h3 := h.trans (relIndex_inner_dvd Q)
    have h4 := Nat.le_of_dvd Nat.card_pos h3
    omega
  · have h3 := h.trans (relIndex_isometryRange_dvd Q hQ)
    have hsq : (powMonoidHom 2 : Kˣ →* Kˣ).range.index = Nat.gcd (Nat.card K - 1) 2 := by
      rw [IsCyclic.index_powMonoidHom_range, Nat.card_units]
    rw [hsq] at h3
    have h4 := Nat.le_of_dvd (by norm_num) (h3.trans (Nat.gcd_dvd_right _ _))
    omega

theorem orthD_D2_of_bound [Finite K] (hQ : ∃ v, Q v ≠ 0)
    (hab : Nat.card (Abelianization (matrixIsometries Q)) ≤ 4) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {δ : MulAut (matrixProjectiveDerived Q)} (hδ : δ ∈ orthD Q) {k : ℕ}
    (hk : δ ^ (p ^ k) ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (matrixProjectiveDerived Q)) :
    δ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q) := by
  set D := orthD Q with hD
  set I := CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q)
    with hI
  set x : D ⧸ I.subgroupOf D := QuotientGroup.mk (⟨δ, hδ⟩ : D) with hx
  have hxk : x ^ (p ^ k) = 1 := by
    rw [hx, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hk
  have hcard : Nat.card (D ⧸ I.subgroupOf D) = I.relIndex D := (Subgroup.index_eq_card _).symm
  have hdvd1 : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one hxk
  have hdvd2 : orderOf x ∣ I.relIndex D := hcard ▸ orderOf_dvd_natCard x
  have hcop : Nat.Coprime (p ^ k) (I.relIndex D) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr
      (orthD_relIndex_inner_not_dvd Q hQ hab hp hp5))
  have hx1 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
  have : x = 1 := orderOf_eq_one_iff.mp hx1
  have hmem := (QuotientGroup.eq_one_iff (⟨δ, hδ⟩ : D)).mp this
  exact Subgroup.mem_subgroupOf.mp hmem

theorem outPNice_of_image_top_gen [Finite K] (hQ : ∃ v, Q v ≠ 0)
    (hab : Nat.card (Abelianization (matrixIsometries Q)) ≤ 4) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (htop : matrixProjectiveImage Q = ⊤) :
    OutPNice p (matrixProjectiveDerived Q) := by
  obtain ⟨g₀, hg₀⟩ := exists_gen Q
  have hmem : ∀ α : MulAut (matrixProjectiveDerived Q),
      ∃ g : similarityPairs Q, matrixProjectiveConjugationHom Q g = α := fun α =>
    (mem_matrixProjectiveImage_iff Q α).mp (htop ▸ Subgroup.mem_top α)
  exact outPNice_of_tower hp (matrixProjectiveConjugationHom Q g₀) (D := orthD Q) (E := ⊤)
    (fun δ hδ => inner_le_orthD Q hδ)
    (fun δ hδ k hk => orthD_D2_of_bound Q hQ hab hp hp5 hδ hk)
    (fun α _ => trivial)
    (fun γ α _ => by
      obtain ⟨g, rfl⟩ := hmem γ
      obtain ⟨h, rfl⟩ := hmem α
      exact comm_mem_orthD Q g h)
    (fun α _ => by
      obtain ⟨h, rfl⟩ := hmem α
      obtain ⟨k, hk⟩ := hg₀ h
      exact ⟨k, (mem_orthD_iff Q _).mpr ⟨⟨g₀ ^ k * h, hk⟩, by rw [map_mul, map_zpow]⟩⟩)

theorem outPChain_of_image_index_le_three_gen [Finite K] (hQ : ∃ v, Q v ≠ 0)
    (hab : Nat.card (Abelianization (matrixIsometries Q)) ≤ 4) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hidx : (matrixProjectiveImage Q).index ≤ 3) :
    OutPChain p (matrixProjectiveDerived Q) := by
  have hp3 : 3 < p := by omega
  obtain ⟨g₀, hg₀⟩ := exists_gen Q
  have : Finite (matrixProjectiveDerived Q) := inferInstance
  have : Finite (MulAut (matrixProjectiveDerived Q)) := inferInstance
  have hDE : orthD Q ≤ matrixProjectiveImage Q := fun δ hδ => by
    obtain ⟨g, rfl⟩ := (mem_orthD_iff Q δ).mp hδ
    exact (mem_matrixProjectiveImage_iff Q _).mpr ⟨g.val, rfl⟩
  have hRing : Finite (K ≃+* K) :=
    Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) DFunLike.coe_injective
  have hfin : Finite (similarityPairs Q) :=
    Finite.of_injective (fun g : similarityPairs Q => (g.val.left, g.val.right)) fun g h hgh =>
      Subtype.ext (SemidirectProduct.ext (congrArg Prod.fst hgh) (congrArg Prod.snd hgh))
  refine ⟨orthD Q, matrixProjectiveImage Q, fun δ hδ => inner_le_orthD Q hδ,
    fun δ hδ k hk => orthD_D2_of_bound Q hQ hab hp hp5 hδ hk, ?_, ?_⟩
  · rintro α ⟨k, hk⟩
    exact mem_of_pow_mem_of_index_le_three _ hidx hp hp3 (hDE hk)
  · rintro α hα β hβ ⟨k, hk⟩ ⟨l, hl⟩
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hα
    obtain ⟨h, rfl⟩ := MonoidHom.mem_range.mp hβ
    have hDn : ((orthD Q).comap (matrixProjectiveConjugationHom Q)).Normal := ⟨fun d hd x => by
      obtain ⟨ℓ, hℓ⟩ := (mem_orthD_iff Q _).mp (Subgroup.mem_comap.mp hd)
      refine Subgroup.mem_comap.mpr ((mem_orthD_iff Q _).mpr
        ⟨⟨x * ℓ.val * x⁻¹, (linearPairsNormal Q).conj_mem ℓ.val ℓ.property x⟩, ?_⟩)
      simp only [map_mul, map_inv]
      rw [hℓ]⟩
    have hk' : ∃ k : ℕ, g ^ (p ^ k) ∈ (orthD Q).comap (matrixProjectiveConjugationHom Q) :=
      ⟨k, Subgroup.mem_comap.mpr (by rw [map_pow]; exact hk)⟩
    have hl' : ∃ l : ℕ, h ^ (p ^ l) ∈ (orthD Q).comap (matrixProjectiveConjugationHom Q) :=
      ⟨l, Subgroup.mem_comap.mpr (by rw [map_pow]; exact hl)⟩
    have hE : ∀ x : similarityPairs Q, ∃ k : ℤ,
        g₀ ^ k * x ∈ (orthD Q).comap (matrixProjectiveConjugationHom Q) := fun x => by
      obtain ⟨k, hk⟩ := hg₀ x
      exact ⟨k, Subgroup.mem_comap.mpr ((mem_orthD_iff Q _).mpr ⟨⟨_, hk⟩, rfl⟩)⟩
    rcases chain_of_cyclic_quotient hp g₀ hE g h hk' hl' with ⟨m, hm⟩ | ⟨m, hm⟩
    · exact Or.inl ⟨m, by simpa [map_mul, map_zpow] using Subgroup.mem_comap.mp hm⟩
    · exact Or.inr ⟨m, by simpa [map_mul, map_zpow] using Subgroup.mem_comap.mp hm⟩

end Generic

section Models

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.Automorphisms
open scoped Pointwise

theorem outPNice_POmegaOdd_gen {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {X : Type} [Group X]
    {n r m : ℕ} (h : StatedClassicalModel X .POmegaOdd n r m) : OutPNice p X := by
  have h0 := h
  obtain ⟨⟨-, -, hn, hr2⟩, K, _, _, hK, ⟨e⟩⟩ := h0
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨hchar, hnd, hT, -⟩ := coordinate_model_witness_odd h K hK e
  have hQ : ∃ v, coordinateQuadOdd n K v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have hab := orthogonal_model_isometry_abelianization_order_bound X .POmegaOdd (.inl rfl) n r m
    h K hK (quadOdd n K) (coe_quadOdd n K) e
  have hab' := card_abelianization_le_four_of_bound (oddIndexEquiv n) (quadOdd n K) hab
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_odd K n hn
    (by rw [hchar]; exact hr2)
  exact OutPNice.of_mulEquiv (coordinateOddWitnessEquiv K e)
    (outPNice_of_image_top_gen _ hQ hab' hp hp5 htop)

theorem outPNice_POmegaPlus_gen_ge_five {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {X : Type}
    [Group X] {n r m : ℕ} (hn : 5 ≤ n) (h : StatedClassicalModel X .POmegaPlus n r m) :
    OutPNice p X := by
  have h0 := h
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h0
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_plus h K hK e
  have hQ : ∃ v, coordinateQuadPlus n K v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have hab := orthogonal_model_isometry_abelianization_order_bound X .POmegaPlus
    (.inr (.inl rfl)) n r m h K hK (quadPlus n K) (coe_quadPlus n K) e
  have hab' := card_abelianization_le_four_of_bound (plusIndexEquiv n) (quadPlus n K) hab
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K n hn
  exact OutPNice.of_mulEquiv (coordinatePlusWitnessEquiv K e)
    (outPNice_of_image_top_gen _ hQ hab' hp hp5 htop)

theorem outPNice_POmegaMinus_gen {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {X : Type} [Group X]
    {n r m : ℕ} (h : StatedClassicalModel X .POmegaMinus n r m) : OutPNice p X := by
  have h0 := h
  obtain ⟨⟨-, -, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h0
  have hn1 : 1 ≤ n := by omega
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_minus h K hK b c hirr e
  have hQ : ∃ v, coordinateQuadMinus n K hn1 b c v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have hab := orthogonal_model_isometry_abelianization_order_bound X .POmegaMinus
    (.inr (.inr rfl)) n r m h K hK b c hirr (quadMinus n K b c) (coe_quadMinus n K b c) e
  have hab' := card_abelianization_le_four_of_bound (minusIndexEquiv n hn1) (quadMinus n K b c) hab
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn
    b c hirr
  exact OutPNice.of_mulEquiv (coordinateMinusWitnessEquiv K hn1 b c e)
    (outPNice_of_image_top_gen _ hQ hab' hp hp5 htop)

theorem outPChain_POmegaPlus_four_gen {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {X : Type}
    [Group X] {r m : ℕ} (h : StatedClassicalModel X .POmegaPlus 4 r m) : OutPChain p X := by
  have h0 := h
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h0
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_plus h K hK e
  have hQ : ∃ v, coordinateQuadPlus 4 K v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have hab := orthogonal_model_isometry_abelianization_order_bound X .POmegaPlus
    (.inr (.inl rfl)) 4 r m h K hK (quadPlus 4 K) (coe_quadPlus 4 K) e
  have hab' := card_abelianization_le_four_of_bound (plusIndexEquiv 4) (quadPlus 4 K) hab
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
    (outPChain_of_image_index_le_three_gen _ hQ hab' hp hp5 hidx)

end Models

end CFSG.RankThree.PartOne.OutStructure
