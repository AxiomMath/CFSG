module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaSplit
public import CFSG.RankThree.PartOne.KC.OrthogonalRegularCoverage
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarElementary
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarCentralizer
public import CFSG.RankThree.PartOne.KC.OrthogonalBinaryDickson
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticNormalForms
public import CFSG.CharacterTheory.Burnside
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.RankThree.PartOne.KC.OrthogonalBlockProduct

public section

namespace CFSG.StandardType

namespace LayerCores

namespace OrthRegular

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonal

variable {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] {Q : QuadraticForm K W}

omit [Field K] [Finite K] [CharP K 2] in
theorem isSolvable_of_no_prime_gt_three' {G : Type*} [Group G] [Finite G]
    (h : ∀ (g : G) (q : ℕ), q.Prime → 3 < q → orderOf g ≠ q) : Group.IsSolvable G := by
  have hpos : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hprime : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card G → ℓ = 2 ∨ ℓ = 3 := by
    intro ℓ hℓ hdvd
    have : Fact ℓ.Prime := ⟨hℓ⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := G) ℓ hdvd
    by_contra hne
    push Not at hne
    have h4 : 3 < ℓ := by
      have := hℓ.two_le
      omega
    exact h g ℓ hℓ h4 hg
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd hpos
  have hm3 : ∀ {d : ℕ}, d.Prime → d ∣ m → d = 3 := by
    intro d hd hdm
    have hdG : d ∣ Nat.card G := hn ▸ Dvd.dvd.mul_left hdm _
    rcases hprime d hd hdG with rfl | rfl
    · exact absurd (hm.of_dvd_nat hdm) (by decide)
    · rfl
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  have hm' : m = 3 ^ m.primeFactorsList.length := Nat.eq_prime_pow_of_unique_prime_dvd hm0 hm3
  have : Fintype G := Fintype.ofFinite G
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (a := a) (b := m.primeFactorsList.length)
    (by rw [← Nat.card_eq_fintype_card, hn, ← hm'])

omit [Finite K] [FiniteDimensional K W] in
theorem finrank_ne_one (hQ : (polarBilin Q).Nondegenerate) : finrank K W ≠ 1 := by
  intro h1
  have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨x, hx⟩ := exists_ne (0 : W)
  apply hx
  refine eq_zero_of_polar_eq_zero hQ fun y => ?_
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' x hx).mp h1 y
  rw [polar_smul_right, polar_self, two_nsmul, CharTwo.add_self_eq_zero, smul_zero]

omit [Finite K] in
theorem isSolvable_orthogonalGroup_of_finrank_le_two (hQ : (polarBilin Q).Nondegenerate)
    (h2 : finrank K W ≤ 2) : Group.IsSolvable (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  rcases (show finrank K W = 0 ∨ finrank K W = 1 ∨ finrank K W = 2 by omega) with h0 | h1 | h2
  · have hW : ∀ x : W, x = 0 := finrank_zero_iff_forall_zero.mp h0
    have : Subsingleton (TauCeti.QuadraticMap.orthogonalGroup Q) :=
      ⟨fun a b => Subtype.ext (LinearEquiv.ext fun x => by rw [hW x, map_zero, map_zero])⟩
    infer_instance
  · exact absurd h1 (finrank_ne_one hQ)
  · set δ := CFSG.RankThree.OrthogonalInvolutions.dicksonHom Q hQ
    have : Group.IsSolvable δ.ker := Group.isSolvable_of_comm fun a b => Subtype.ext (Subtype.ext
      (commute_of_dicksonHom_eq_one hQ h2 a.1.2 b.1.2 a.2 b.2))
    have : Group.IsSolvable (Multiplicative (ZMod 2)) :=
      Group.isSolvable_of_comm fun a b => mul_comm a b
    exact Group.isSolvable_of_ker_le_range δ.ker.subtype δ (by rw [Subgroup.range_subtype])

omit [Finite K] [CharP K 2] [FiniteDimensional K W] in
theorem supportedDerived_top_le :
    supportedDerived Q ⊤ ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  intro g hg
  obtain ⟨-, h, hh, he⟩ := mem_supportedDerived.mp hg
  let c : ((⊤ : Submodule K W) ≃ₗ[K] (⊤ : Submodule K W)) →* (W ≃ₗ[K] W) :=
    { toFun := fun k => (Submodule.topEquiv : (⊤ : Submodule K W) ≃ₗ[K] W).symm.trans
        (k.trans (Submodule.topEquiv : (⊤ : Submodule K W) ≃ₗ[K] W))
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hcO : (TauCeti.QuadraticMap.orthogonalGroup
      (Q.comp (⊤ : Submodule K W).subtype)).map c ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨k, hk, rfl⟩
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v =>
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hk ⟨v, Submodule.mem_top⟩
  have hg' : g = c h := LinearEquiv.ext fun v => (he ⟨v, Submodule.mem_top⟩).symm
  rw [hg']
  have hmem : c h ∈
      (CFSG.RankThree.Classical2.orthDerived (Q.comp (⊤ : Submodule K W).subtype)).map c :=
    ⟨h, hh, rfl⟩
  rw [CFSG.RankThree.Classical2.orthDerived, Subgroup.map_commutator] at hmem
  exact Subgroup.commutator_mono hcO hcO hmem

theorem eq_one_of_commute_orthDerived (hQ : (polarBilin Q).Nondegenerate) (h3 : 3 ≤ finrank K W)
    (hnexc : ¬ SmallFixedException Q) {z : W ≃ₗ[K] W}
    (hzO : z ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hzc : ∀ y ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆,
      z * y = y * z) : z = 1 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hT3 : 3 ≤ finrank K (⊤ : Submodule K W) := by rw [finrank_top]; exact h3
  have hTnd : (polarBilin (Q.comp (⊤ : Submodule K W).subtype)).Nondegenerate := by
    constructor
    · intro x hx
      exact Subtype.ext (eq_zero_of_polar_eq_zero hQ fun y => hx ⟨y, Submodule.mem_top⟩)
    · intro y hy
      refine Subtype.ext (eq_zero_of_polar_eq_zero hQ fun x => ?_)
      rw [polar_comm]
      exact hy ⟨x, Submodule.mem_top⟩
  have hsing : ∃ e ∈ (⊤ : Submodule K W), e ≠ 0 ∧ Q e = 0 :=
    CFSG.ComponentClassification.UnbalancedCatalog.exists_singular_of_three_le
      (polarNondegOn_top hQ) hT3
  have hM : ElementaryMapsMem Q ⊤ := elementaryMapsMem_of_regular hTnd hT3 fun hK hd4 U hU => by
    by_contra hcon
    push Not at hcon
    apply hnexc
    refine Or.inr ⟨⟨by rwa [finrank_top] at hd4, U.map (⊤ : Submodule K W).subtype, ?_, ?_⟩,
      Or.inl hK⟩
    · rw [Submodule.finrank_map_subtype_eq]
      exact hU
    · rintro _ ⟨u, hu, rfl⟩
      exact hcon u hu
  have hcomm : ∀ g ∈ supportedDerived Q ⊤, ∀ v, z.toAddEquiv (g v) = g (z.toAddEquiv v) :=
    fun g hg v => by
      have := hzc g (supportedDerived_top_le hg)
      show z (g v) = g (z v)
      rw [← LinearEquiv.mul_apply, this, LinearEquiv.mul_apply]
  have hFQ : ∀ v, Q (z.toAddEquiv v) = (1 : K) * (RingEquiv.refl K) (Q v) := fun v => by
    rw [one_mul]
    exact map_of_mem hzO v
  obtain ⟨-, c, -, hc⟩ := scalar_restriction_of_commute z.toAddEquiv (RingEquiv.refl K) 1 hFQ
    hcomm hQ hTnd hT3 hsing hM (fun c v => by simp)
  have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨w, hw⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_map_ne_zero hQ
  have hcc : c * c = 1 := by
    have h1 := map_of_mem hzO w
    have h5 : z w = c • w := hc w Submodule.mem_top
    rw [h5, QuadraticMap.map_smul, smul_eq_mul] at h1
    exact mul_right_cancel₀ hw (by rw [one_mul]; exact h1)
  have hc1 : c = 1 := by
    have h8 : (c - 1) ^ 2 = 0 := by
      have : (c - 1) ^ 2 = c * c - 1 - 2 * (c - 1) := by ring
      rw [this, hcc, h2]
      ring
    exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h8)
  refine LinearEquiv.ext fun v => ?_
  show z.toAddEquiv v = v
  rw [hc v Submodule.mem_top, hc1, one_smul]

end OrthRegular

end LayerCores

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonal
  LayerCores LayerCores.OrthRegular CFSG.Assembly

theorem ggOrthRegularCoreInput_holds : GGOrthRegularCoreInput := by
  intro K _ _ _ W _ _ _ Q hQ
  classical
  have := finite_linearEquiv (K := K) (V := W)
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO
  by_cases h3 : 3 ≤ finrank K W
  · obtain ⟨hexc, hcov⟩ := orthogonal_regular_space_coverage Q hQ h3
    by_cases hsmall : SmallFixedException Q
    · exact ⟨Empty, _, isSubCoreFamily_of_isSolvable
        (isSolvable_of_no_prime_gt_three' (hexc hsmall))⟩
    · obtain ⟨-, ⟨n, L, -, -, hsup, hL, -⟩, -⟩ := hcov hsmall
      have hcomm_eq : (⨆ i, (L i).map O.subtype) = ⁅O, O⁆ := by
        rw [← Subgroup.map_iSup, hsup, Subgroup.map_subtype_commutator]
      refine ⟨Fin n, fun i => (L i).map O.subtype, fun i => Subgroup.map_subtype_le _,
        fun i => ?_, fun i => ?_, ⟨1, ?_⟩, fun z hz hzc _ => ?_⟩
      · have hnorm : ((commutator ↥O).subgroupOf (⊤ : Subgroup ↥O)).Normal :=
          (Subgroup.normal_subgroupOf_iff le_top).mpr fun x k hx _ =>
            (inferInstance : (commutator ↥O).Normal).conj_mem x hx k
        have h1 : IsSubnormal (L i) ⊤ := IsSubnormal.step (hL i).2.1 (hL i).2.2
          (IsSubnormal.step le_top hnorm (IsSubnormal.refl ⊤))
        have h2 := ggSubnormal_map O.subtype h1
        rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
      · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
          ((L i).equivMapOfInjective _ O.subtype_injective) (hL i).1
      · rw [LayerFacts.ggDer_succ, LayerFacts.ggDer_zero, hcomm_eq]
      · rw [hcomm_eq] at hz hzc
        exact eq_one_of_commute_orthDerived hQ h3 hsmall (LayerFacts.ggCommutator_self_le O hz)
          hzc
  · exact ⟨Empty, _, isSubCoreFamily_of_isSolvable
      (isSolvable_orthogonalGroup_of_finrank_le_two hQ (by omega))⟩

end CFSG.StandardType
