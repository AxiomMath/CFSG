module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionAutKClassical

public section

namespace CFSG.StandardType

open Matrix Subgroup QuadraticMap CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
  CFSG.RankThree.PartOne.OutStructure CFSG.Assembly CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

theorem ggNot_three_dvd_card_abelianization {K : Type} [Field K] [Finite K] {ι : Type}
    [Fintype ι] [DecidableEq ι] {d ℓ : ℕ} (e : ι ≃ Fin d) (Q₀ : QuadraticForm K (ι → K))
    (hab : IsometryAbelianizationBound ℓ Q₀) :
    ¬ 3 ∣ Nat.card (Abelianization (matrixIsometries (reindexQuadraticForm e Q₀))) := by
  have : Finite (Abelianization (matrixIsometries (reindexQuadraticForm e Q₀))) := inferInstance
  have : Finite (Abelianization (TauCeti.QuadraticMap.orthogonalGroup Q₀)) :=
    Finite.of_equiv _ (MulEquiv.abelianizationCongr (matrixIsometriesReindexEquiv e Q₀)).toEquiv
  rw [card_abelianization_matrixIsometries_reindex]
  have : CFSG.IsElementaryAbelian 2 (Abelianization (TauCeti.QuadraticMap.orthogonalGroup Q₀)) :=
    hab.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (CFSG.IsElementaryAbelian.isPGroup 2
    (Abelianization (TauCeti.QuadraticMap.orthogonalGroup Q₀)))
  rw [hk]
  intro h3
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.prime_three.dvd_of_dvd_pow h3)
  omega

section Generic

variable {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

theorem ggOrthD_relIndex_inner_not_dvd_three [Finite K] (hQ : ∃ v, Q v ≠ 0)
    (hab : ¬ 3 ∣ Nat.card (Abelianization (matrixIsometries Q))) :
    ¬ 3 ∣ (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (matrixProjectiveDerived Q)).relIndex (orthD Q) := by
  have h1 : CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q) ≤
      (isometryConjugationHom Q).range := by
    rw [inner_eq_map_commutator Q]
    exact Subgroup.map_le_range _ _
  have h2 : (isometryConjugationHom Q).range ≤ (linearConjugationHom Q).range :=
    isometryConjugationHom_range_le Q
  rw [← linearConjugationHom_range_eq_orthD, ← Subgroup.relIndex_mul_relIndex _ _ _ h1 h2]
  intro hdvd
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hdvd with h | h
  · exact hab (h.trans (relIndex_inner_dvd Q))
  · have h3 := h.trans (relIndex_isometryRange_dvd Q hQ)
    have hsq : (powMonoidHom 2 : Kˣ →* Kˣ).range.index = Nat.gcd (Nat.card K - 1) 2 := by
      rw [IsCyclic.index_powMonoidHom_range, Nat.card_units]
    rw [hsq] at h3
    have h4 := Nat.le_of_dvd (by norm_num) (h3.trans (Nat.gcd_dvd_right _ _))
    omega

theorem ggOrthD_mem_inner_of_not_dvd {p : ℕ} (hp : p.Prime)
    (hnd : ¬ p ∣ (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (matrixProjectiveDerived Q)).relIndex (orthD Q))
    {δ : MulAut (matrixProjectiveDerived Q)} (hδ : δ ∈ orthD Q) {k : ℕ}
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
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd)
  have hx1 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
  have : x = 1 := orderOf_eq_one_iff.mp hx1
  have hmem := (QuotientGroup.eq_one_iff (⟨δ, hδ⟩ : D)).mp this
  exact Subgroup.mem_subgroupOf.mp hmem

theorem ggOutPNice_of_image_top_of_not_dvd [Finite K] {p : ℕ} (hp : p.Prime)
    (hnd : ¬ p ∣ (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (matrixProjectiveDerived Q)).relIndex (orthD Q))
    (htop : matrixProjectiveImage Q = ⊤) : OutPNice p (matrixProjectiveDerived Q) := by
  obtain ⟨g₀, hg₀⟩ := exists_gen Q
  have hmem : ∀ α : MulAut (matrixProjectiveDerived Q),
      ∃ g : similarityPairs Q, matrixProjectiveConjugationHom Q g = α := fun α =>
    (mem_matrixProjectiveImage_iff Q α).mp (htop ▸ Subgroup.mem_top α)
  exact outPNice_of_tower hp (matrixProjectiveConjugationHom Q g₀) (D := orthD Q) (E := ⊤)
    (fun δ hδ => inner_le_orthD Q hδ)
    (fun δ hδ k hk => ggOrthD_mem_inner_of_not_dvd Q hp hnd hδ hk)
    (fun α _ => trivial)
    (fun γ α _ => by
      obtain ⟨g, rfl⟩ := hmem γ
      obtain ⟨h, rfl⟩ := hmem α
      exact comm_mem_orthD Q g h)
    (fun α _ => by
      obtain ⟨h, rfl⟩ := hmem α
      obtain ⟨k, hk⟩ := hg₀ h
      exact ⟨k, (mem_orthD_iff Q _).mpr ⟨⟨g₀ ^ k * h, hk⟩, by rw [map_mul, map_zpow]⟩⟩)

end Generic

section Index

variable {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

theorem ggNoOuterPlane_of_image_index_le_three [Finite K] {m : ℕ} (hm3 : ¬ 3 ∣ m)
    (hnd3 : ¬ 3 ∣ (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (matrixProjectiveDerived Q)).relIndex (orthD Q))
    (hidx : (matrixProjectiveImage Q).index ≤ 3)
    (hfield : ∀ g : similarityPairs Q, g ^ m ∈ linearSimilarityPairs Q) :
    GGNoOuterPlane 3 (matrixProjectiveDerived Q) := by
  intro E hE hcard hEI
  have : Finite (matrixProjectiveDerived Q) := inferInstance
  have : Finite (MulAut (matrixProjectiveDerived Q)) := inferInstance
  have hEA : E ⊓ matrixProjectiveImage Q = ⊥ := by
    rw [eq_bot_iff]
    rintro α ⟨hαE, g, rfl⟩
    have h3 : (matrixProjectiveConjugationHom Q g) ^ 3 = 1 := hE.2 _ hαE
    have hm : (matrixProjectiveConjugationHom Q g) ^ m ∈ orthD Q := by
      rw [← map_pow]
      exact (mem_orthD_iff Q _).mpr ⟨⟨g ^ m, hfield g⟩, rfl⟩
    have hpow : (matrixProjectiveConjugationHom Q g) ^ m =
        (matrixProjectiveConjugationHom Q g) ^ (m % 3) := by
      conv_lhs => rw [← Nat.div_add_mod m 3, pow_add, pow_mul, h3, one_pow, one_mul]
    have hD : matrixProjectiveConjugationHom Q g ∈ orthD Q := by
      rcases (by omega : m % 3 = 1 ∨ m % 3 = 2) with h1 | h2
      · rwa [hpow, h1, pow_one] at hm
      · rw [hpow, h2] at hm
        have e4 : matrixProjectiveConjugationHom Q g =
            ((matrixProjectiveConjugationHom Q g) ^ 2) ^ 2 := by
          rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, h3, one_mul]
        rw [e4]
        exact pow_mem hm 2
    have hI := ggOrthD_mem_inner_of_not_dvd Q Nat.prime_three hnd3 hD (k := 1)
      (by rw [pow_one, h3]; exact Subgroup.one_mem _)
    have hmem : matrixProjectiveConjugationHom Q g ∈
        E ⊓ (MulAut.conj : matrixProjectiveDerived Q →* MulAut _).range := ⟨hαE, hI⟩
    rw [hEI] at hmem
    exact hmem
  have h1 : (matrixProjectiveImage Q).relIndex E = Nat.card E := by
    rw [← Subgroup.inf_relIndex_right, inf_comm, hEA, Subgroup.relIndex_bot_left]
  have h2 : (matrixProjectiveImage Q).relIndex E ≤ (matrixProjectiveImage Q).index := by
    rw [← Subgroup.relIndex_top_right]
    exact Subgroup.relIndex_le_of_le_right le_top
      (by rw [Subgroup.relIndex_top_right]; exact Subgroup.index_ne_zero_of_finite)
  rw [h1, hcard] at h2
  omega

end Index

section Models

open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Automorphisms
open scoped Pointwise

theorem ggOutPNice_POmegaOdd_three {X : Type} [Group X] {n r m : ℕ}
    (h : StatedClassicalModel X .POmegaOdd n r m) : OutPNice 3 X := by
  have h0 := h
  obtain ⟨⟨-, -, hn, hr2⟩, K, _, _, hK, ⟨e⟩⟩ := h0
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨hchar, hnd, hT, -⟩ := coordinate_model_witness_odd h K hK e
  have hQ : ∃ v, coordinateQuadOdd n K v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have hab := orthogonal_model_isometry_abelianization_order_bound X .POmegaOdd (.inl rfl) n r m
    h K hK (quadOdd n K) (coe_quadOdd n K) e
  have hab3 := ggNot_three_dvd_card_abelianization (oddIndexEquiv n) (quadOdd n K) hab
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_odd K n hn
    (by rw [hchar]; exact hr2)
  exact OutPNice.of_mulEquiv (coordinateOddWitnessEquiv K e)
    (ggOutPNice_of_image_top_of_not_dvd _ Nat.prime_three
      (ggOrthD_relIndex_inner_not_dvd_three _ hQ hab3) htop)

theorem ggOutPNice_POmegaPlus_three {X : Type} [Group X] {n r m : ℕ} (hn : 5 ≤ n)
    (h : StatedClassicalModel X .POmegaPlus n r m) : OutPNice 3 X := by
  have h0 := h
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h0
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_plus h K hK e
  have hQ : ∃ v, coordinateQuadPlus n K v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have hab := orthogonal_model_isometry_abelianization_order_bound X .POmegaPlus
    (.inr (.inl rfl)) n r m h K hK (quadPlus n K) (coe_quadPlus n K) e
  have hab3 := ggNot_three_dvd_card_abelianization (plusIndexEquiv n) (quadPlus n K) hab
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K n hn
  exact OutPNice.of_mulEquiv (coordinatePlusWitnessEquiv K e)
    (ggOutPNice_of_image_top_of_not_dvd _ Nat.prime_three
      (ggOrthD_relIndex_inner_not_dvd_three _ hQ hab3) htop)

theorem ggOutPNice_POmegaMinus_three {X : Type} [Group X] {n r m : ℕ}
    (h : StatedClassicalModel X .POmegaMinus n r m) : OutPNice 3 X := by
  have h0 := h
  obtain ⟨⟨-, -, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h0
  have hn1 : 1 ≤ n := by omega
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_minus h K hK b c hirr e
  have hQ : ∃ v, coordinateQuadMinus n K hn1 b c v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have hab := orthogonal_model_isometry_abelianization_order_bound X .POmegaMinus
    (.inr (.inr rfl)) n r m h K hK b c hirr (quadMinus n K b c) (coe_quadMinus n K b c) e
  have hab3 := ggNot_three_dvd_card_abelianization (minusIndexEquiv n hn1) (quadMinus n K b c) hab
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn
    b c hirr
  exact OutPNice.of_mulEquiv (coordinateMinusWitnessEquiv K hn1 b c e)
    (ggOutPNice_of_image_top_of_not_dvd _ Nat.prime_three
      (ggOrthD_relIndex_inner_not_dvd_three _ hQ hab3) htop)

theorem ggNoOuterPlane_POmegaPlus_four_three {X : Type} [Group X] {m : ℕ} (hm3 : ¬ 3 ∣ m)
    (h : StatedClassicalModel X .POmegaPlus 4 3 m) : GGNoOuterPlane 3 X := by
  have h0 := h
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h0
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_plus h K hK e
  have hQ : ∃ v, coordinateQuadPlus 4 K v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have hab := orthogonal_model_isometry_abelianization_order_bound X .POmegaPlus
    (.inr (.inl rfl)) 4 3 m h K hK (quadPlus 4 K) (coe_quadPlus 4 K) e
  have hab3 := ggNot_three_dvd_card_abelianization (plusIndexEquiv 4) (quadPlus 4 K) hab
  have hEA := (orthogonal_geometry_plus_model_stabilizer_preserving_image h K hK e).1
  have horbit := orthogonal_geometry_plus_point_family_orbit h hK e
  have hidx : (matrixProjectiveImage (coordinateQuadPlus 4 K)).index ≤ 3 := by
    have hst : (projectivePointFamilyAut (coordinateQuadPlus 4 K)).index =
        (MulAction.orbit (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))
          (projectivePointFamily (coordinateQuadPlus 4 K))).ncard :=
      MulAction.index_stabilizer _ _
    rw [← hEA, hst]
    exact (horbit.2.2.2.2.2 rfl).2
  have hring := card_ringAut_and_isCyclic Nat.prime_three K hK
  have hfield : ∀ g : similarityPairs (coordinateQuadPlus 4 K),
      g ^ m ∈ linearSimilarityPairs (coordinateQuadPlus 4 K) := fun g => by
    show fieldProjection (coordinateQuadPlus 4 K) (g ^ m) = 1
    rw [map_pow, ← hring.1]
    exact pow_card_eq_one'
  exact GGNoOuterPlane.of_mulEquiv (coordinatePlusWitnessEquiv K e)
    (ggNoOuterPlane_of_image_index_le_three _ hm3
      (ggOrthD_relIndex_inner_not_dvd_three _ hQ hab3) hidx hfield)

end Models

theorem ggLieOutRankTwoAt_B_three (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.B r q).Valid) (hr : 3 ≤ r) (hq3 : q.p = 3) :
    GGLieOutRankTwoAt ⟨.B r q, hv⟩ := by
  refine ggLieOutRankTwoAt_of_char (TauCeti.LieTypeIndex.characteristic_B r q) fun hp2 => ?_
  rcases CFSG.Models.lieModel_B (G := (TauCeti.CFSGIndex.lie ⟨.B r q, hv⟩).Group) r q hv
      (MulEquiv.refl _) with hm | hm
  · exact (ggOutPNice_PSp_ge_three_odd hr q.prime_p hp2
      (ggStatedClassicalModel_of_lieModel (Or.inr (Or.inr (Or.inl rfl))) hm)).toChain
  · rw [hq3]
    exact (ggOutPNice_POmegaOdd_three
      (ggStatedClassicalModel_of_lieModel (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hm)).toChain

theorem ggLieOutRankTwoAt_D_three (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.D r q).Valid) (hq3 : q.p = 3) :
    GGLieOutRankTwoAt ⟨.D r q, hv⟩ := by
  have hm := ggStatedClassicalModel_of_lieModel (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (CFSG.Models.lieModel_D (G := (TauCeti.CFSGIndex.lie ⟨.D r q, hv⟩).Group) r q hv
      (MulEquiv.refl _))
  rw [hq3] at hm
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  by_cases hr5 : 5 ≤ r
  · refine ggLieOutRankTwoAt_of_char (TauCeti.LieTypeIndex.characteristic_D r q) fun _ => ?_
    rw [hq3]
    exact (ggOutPNice_POmegaPlus_three hr5 hm).toChain
  · have hr4 : r = 4 := by omega
    subst hr4
    by_cases ha : 3 ∣ q.exponent
    · exact fun _ _ _ _ _ _ _ _ => ⟨q, rfl, hq3, ha⟩
    · refine ggLieOutRankTwoAt_of_noOuterPlane (TauCeti.LieTypeIndex.characteristic_D 4 q)
        fun _ => ?_
      rw [hq3]
      exact ggNoOuterPlane_POmegaPlus_four_three ha hm

theorem ggLieOutRankTwoAt_twistedD_three (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedD r q).Valid) (hq3 : q.p = 3) :
    GGLieOutRankTwoAt ⟨.twistedD r q, hv⟩ := by
  refine ggLieOutRankTwoAt_of_char (TauCeti.LieTypeIndex.characteristic_twistedD r q) fun _ => ?_
  have hm := ggStatedClassicalModel_of_lieModel (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    (CFSG.Models.lieModel_twistedD (G := (TauCeti.CFSGIndex.lie ⟨.twistedD r q, hv⟩).Group) r q
      hv (MulEquiv.refl _))
  rw [hq3] at hm ⊢
  exact (ggOutPNice_POmegaMinus_three hm).toChain

end CFSG.StandardType
