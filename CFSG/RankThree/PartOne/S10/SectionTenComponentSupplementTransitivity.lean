module

public import CFSG.RankThree.PartOne.S10.ThetaContract
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
import CFSG.RankThree.PartOne.S10.EmbeddingTransport
public import CFSG.RankThree.GroupTheory.SteinbergBYRelativeCores
public import CFSG.RankThree.GroupTheory.SteinbergCEQuotientKernelMonotonicity

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.GroupTheory.SteinbergBY

theorem section_ten_component_supplement_transitivity_of
    (hnorm : SelectedPrimeElementsNormalizeThetaComponents)
    (hemb : LocalThetaComponentEmbeddingFrontier) :
    SectionTenComponentSupplementTransitivity := by
  intro hS G _ _ _ hnonab hKP hE p hp hp3 A hA L hL K hK J hJ hLK hKJ
  have := hA
  obtain ⟨a, haA, ha1, hJa⟩ := mem_thetaComponentFamily_iff.mp hJ
  obtain ⟨cK, hcKA, hcK1, hKc⟩ := mem_thetaComponentFamily_iff.mp hK
  obtain ⟨cL, hcLA, hcL1, hLc⟩ := mem_thetaComponentFamily_iff.mp hL
  have hordA : orderOf a = p := EmbeddingFixedResidual.orderOf_eq_of_isElementaryAbelian hp haA ha1
  have hordK : orderOf cK = p :=
    EmbeddingFixedResidual.orderOf_eq_of_isElementaryAbelian hp hcKA hcK1
  have hordL : orderOf cL = p :=
    EmbeddingFixedResidual.orderOf_eq_of_isElementaryAbelian hp hcLA hcL1
  have hacK : cK * a = a * cK := congrArg Subtype.val (hA.is_comm.comm ⟨cK, hcKA⟩ ⟨a, haA⟩)
  have hacL : cL * a = a * cL := congrArg Subtype.val (hA.is_comm.comm ⟨cL, hcLA⟩ ⟨a, haA⟩)
  have hAL : A ≤ Subgroup.normalizer (L : Set G) := hnorm.2 G hE p hp hp3 A hA L hL
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := hnorm.2 G hE p hp hp3 A hA K hK
  have hJC : J ≤ Subgroup.centralizer ({a} : Set G) := (mem_thetaComponentsAt_iff.mp hJa).1
  have hord : ∃ k : ℕ, orderOf a = p ^ k := ⟨1, by rw [pow_one]; exact hordA⟩
  have htrK : ∀ k ∈ K, a * k * a⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) K :=
    EmbeddingFixedResidual.trivial_action_of_eq_sup_centralizing (hAK haA) hJC hKJ
  have htrL : ∀ l ∈ L, a * l * a⁻¹ * l⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) L := by
    obtain ⟨-, hmono⟩ :=
      solvable_prime_complement_supplement_quotient_kernel_monotonicity hp hAL hAK hLK
    exact (mem_thetaQuotientCentralizer_iff.mp
      (hmono (mem_thetaQuotientCentralizer_iff.mpr ⟨haA, hAK haA, htrK⟩))).2.2
  obtain ⟨hKsup, PK', hPK', hPKeq⟩ := EmbeddingFixedResidual.fixed_residual_ambient hp hacK
    hord hKc (hAK haA) htrK
  obtain ⟨hLsup, PL', hPL', hPLeq⟩ := EmbeddingFixedResidual.fixed_residual_ambient hp hacL
    hord hLc (hAL haA) htrL
  have hHK : CFSG.IsKGroup (Subgroup.centralizer ({a} : Set G)) :=
    hKP _ (EmbeddingFixedResidual.centralizer_ne_top_of_simple hnonab ha1)
  have hHE : evenRank (Subgroup.centralizer ({a} : Set G)) ≤ 3 :=
    (Sec9A.evenRank_subgroup_le _).trans hE
  obtain ⟨XK₀, hXK₀, hPKX⟩ := hemb hS _ hHK hHE p hp hp3 _
    (by rw [← Subgroup.orderOf_coe]; exact hordK) PK' hPK'
  obtain ⟨XL₀, hXL₀, hPLX⟩ := hemb hS _ hHK hHE p hp hp3 _
    (by rw [← Subgroup.orderOf_coe]; exact hordL) PL' hPL'
  have hXK : XK₀.map (Subgroup.centralizer ({a} : Set G)).subtype ∈ thetaComponentsAt p a :=
    ⟨XK₀, hXK₀, rfl⟩
  have hXL : XL₀.map (Subgroup.centralizer ({a} : Set G)).subtype ∈ thetaComponentsAt p a :=
    ⟨XL₀, hXL₀, rfl⟩
  have hPKle : inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({a} : Set G)) ≤
      XK₀.map (Subgroup.centralizer ({a} : Set G)).subtype := hPKeq ▸ Subgroup.map_mono hPKX
  have hPLle : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({a} : Set G)) ≤
      XL₀.map (Subgroup.centralizer ({a} : Set G)).subtype := hPLeq ▸ Subgroup.map_mono hPLX
  have hqK := isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt hp hKc
  have hqL := isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt hp hLc
  have hKJnotsol : ¬ Group.IsSolvable ↥(K ⊓ J) := fun hsol => by
    have hsolQ := Group.isSolvable_of_surjective
      (EmbeddingFixedResidual.surjective_inclusion_quotient (inf_le_left : K ⊓ J ≤ K) hKJ)
    have := LocalCores.isQuasisimple_nontrivial hqK
    have := hqK.1
    exact Group.IsPerfect.not_isSolvable _ hsolQ
  have hVK : inSubgroup perfectResidual (K ⊓ J) ≤ K ⊓ J := Subgroup.map_subtype_le _
  have hXKJ : XK₀.map (Subgroup.centralizer ({a} : Set G)).subtype = J :=
    EmbeddingFixedResidual.eq_of_perfect_le_of_mem_thetaComponentsAt hp hXK hJa
      (EmbeddingFixedResidual.ne_bot_inSubgroup_perfectResidual_of_not_isSolvable hKJnotsol)
      (EmbeddingFixedResidual.isPerfect_inSubgroup_perfectResidual _)
      ((EmbeddingTransport.le_inSubgroup_perfectResidual_of_isPerfect
        (hVK.trans (inf_le_inf_left K hJC))
        (EmbeddingFixedResidual.isPerfect_inSubgroup_perfectResidual _)).trans hPKle)
      (hVK.trans inf_le_right)
  have hPKJ : inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({a} : Set G)) ≤ J :=
    hXKJ ▸ hPKle
  have hCMnotsol := EmbeddingFixedResidual.not_isSolvable_inf_centralizer hp
    (inf_le_left : L ⊓ K ≤ L) hLK (hAL haA) (mem_normalizer_inf (hAL haA) (hAK haA)) hord hqL
    htrL
  have hCML : (L ⊓ K) ⊓ Subgroup.centralizer ({a} : Set G) ≤
      L ⊓ Subgroup.centralizer ({a} : Set G) := inf_le_inf_right _ inf_le_left
  have hCMK : (L ⊓ K) ⊓ Subgroup.centralizer ({a} : Set G) ≤
      K ⊓ Subgroup.centralizer ({a} : Set G) := inf_le_inf_right _ inf_le_right
  have hVLperf := EmbeddingFixedResidual.isPerfect_inSubgroup_perfectResidual
    ((L ⊓ K) ⊓ Subgroup.centralizer ({a} : Set G))
  have hVLle : inSubgroup perfectResidual ((L ⊓ K) ⊓ Subgroup.centralizer ({a} : Set G)) ≤
      (L ⊓ K) ⊓ Subgroup.centralizer ({a} : Set G) := Subgroup.map_subtype_le _
  have hVLPL := EmbeddingTransport.le_inSubgroup_perfectResidual_of_isPerfect
    (hVLle.trans hCML) hVLperf
  have hVLPK := EmbeddingTransport.le_inSubgroup_perfectResidual_of_isPerfect
    (hVLle.trans hCMK) hVLperf
  have hXLJ : XL₀.map (Subgroup.centralizer ({a} : Set G)).subtype = J :=
    EmbeddingFixedResidual.eq_of_perfect_le_of_mem_thetaComponentsAt hp hXL hJa
      (EmbeddingFixedResidual.ne_bot_inSubgroup_perfectResidual_of_not_isSolvable hCMnotsol)
      hVLperf (hVLPL.trans hPLle) (hVLPK.trans hPKJ)
  have hPLJ : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({a} : Set G)) ≤ J :=
    hXLJ ▸ hPLle
  have hPLL : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({a} : Set G)) ≤ L :=
    (Subgroup.map_subtype_le _).trans inf_le_left
  refine le_antisymm ?_ (sup_le inf_le_left (Subgroup.map_subtype_le _))
  calc L = inSubgroup (aschbacherSolvableCore p) L ⊔
        inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({a} : Set G)) := hLsup.symm
    _ ≤ (L ⊓ J) ⊔ inSubgroup (aschbacherSolvableCore p) L :=
      sup_le le_sup_right (le_sup_of_le_left (le_inf hPLL hPLJ))

end CFSG.RankThree.PartOne
