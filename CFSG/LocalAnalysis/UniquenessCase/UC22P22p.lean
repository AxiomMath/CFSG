module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem uc22p22p_le_T_of_inCalV (D : Data G) {V : Subgroup G} (hV : InCalV D.M V) : V ≤ D.T :=
  (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hV.2.1 hV.2.2.1
    (uc22p22e_isPGroup_of_elem hV.2.2.2)).trans (uc22p22e_pCoreOf_le_T D)

theorem uc22p22p_le_proofE (D : Data G) {V : Subgroup G} (hV : InCalV D.M V)
    (hJ : jOf D.T ≤ centralizer (V : Set G)) : V ≤ proofE D := by
  intro v hv
  refine uc22p22e_mem_omegaZJ'.2 ⟨uc22p22p_le_T_of_inCalV D hV hv, fun j hj => ?_, hV.2.2.2.2 v hv⟩
  exact (Subgroup.mem_centralizer_iff.1 (hJ hj) v hv).symm

theorem uc22p22p_conj_jOf (D : Data G) {V : Subgroup G} (hJ : jOf D.T ≤ centralizer (V : Set G))
    {y : G} (hy : y ∈ normalizer ((D.T ⊓ centralizer (V : Set G) : Subgroup G) : Set G)) :
    ∀ x ∈ jOf D.T, y * x * y⁻¹ ∈ jOf D.T := by
  refine uc22p22e_conj_jOf (fun x hx => ?_)
  have hxC : x ∈ D.T ⊓ centralizer (V : Set G) := ⟨uc22p22e_jOf_le_self D.T hx, hJ hx⟩
  exact ((Subgroup.mem_normalizer_iff.1 hy x).1 hxC).1

theorem uc22p22p_conj_proofE (D : Data G) {V : Subgroup G} (hJ : jOf D.T ≤ centralizer (V : Set G))
    {y : G} (hy : y ∈ normalizer ((D.T ⊓ centralizer (V : Set G) : Subgroup G) : Set G)) :
    ∀ z ∈ proofE D, y * z * y⁻¹ ∈ proofE D :=
  uc22p22e_conj_omegaZJ (uc22p22p_conj_jOf D hJ hy)
    (fun x hx => by simpa using uc22p22p_conj_jOf D hJ (inv_mem hy) x hx)

theorem uc22p22p_conj_proofS (D : Data G) {V : Subgroup G} (hV : InCalV D.M V)
    (hJ : jOf D.T ≤ centralizer (V : Set G)) {y : G}
    (hy : y ∈ normalizer ((D.T ⊓ centralizer (V : Set G) : Subgroup G) : Set G)) :
    ∀ s ∈ proofS D, y * s * y⁻¹ ∈ proofS D := by
  intro s hs
  obtain ⟨hsT, hsC⟩ := Subgroup.mem_inf.1 hs
  have hsV : s ∈ centralizer (V : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.2 (uc22p22p_le_proofE D hV hJ)) hsC
  have h1 : y * s * y⁻¹ ∈ D.T ⊓ centralizer (V : Set G) :=
    (Subgroup.mem_normalizer_iff.1 hy s).1 ⟨hsT, hsV⟩
  refine Subgroup.mem_inf.2 ⟨h1.1, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have he' : y⁻¹ * e * y ∈ proofE D := by
    simpa using uc22p22p_conj_proofE D hJ (inv_mem hy) e he
  have h2 := Subgroup.mem_centralizer_iff.1 hsC _ he'
  calc e * (y * s * y⁻¹) = y * ((y⁻¹ * e * y) * s) * y⁻¹ := by group
    _ = y * (s * (y⁻¹ * e * y)) * y⁻¹ := by rw [h2]
    _ = y * s * y⁻¹ * e := by group

theorem uc22p22p_exists_max_ge {H : Subgroup G} (hH : IsTwoLocal H) :
    ∃ N : Subgroup G, rankThreeIsMaxTwoLocal N ∧ H ≤ N := by
  classical
  set S : Set (Subgroup G) := {N | IsTwoLocal N ∧ H ≤ N} with hS
  obtain ⟨N, ⟨hN, hHN⟩, hmax⟩ :=
    Set.exists_max_image S (fun N => Nat.card N) (Set.toFinite S) ⟨H, hH, le_rfl⟩
  refine ⟨N, ⟨hN, fun K hK hNK => ?_⟩, hHN⟩
  have hKS : K ∈ S := ⟨hK, hHN.trans hNK⟩
  exact (Subgroup.eq_of_le_of_card_ge hNK (hmax K hKS)).symm

theorem uc22p22p_le_of_uniqueMax {M R H : Subgroup G} (hU : UniqueMax M R) (hH : IsTwoLocal H)
    (hRH : R ≤ H) : H ≤ M := by
  obtain ⟨N, hN, hHN⟩ := uc22p22p_exists_max_ge hH
  have hmem : N ∈ calMOf R := ⟨hN, hRH.trans hHN⟩
  have hM : calMOf R = {M} := hU
  rw [hM] at hmem
  exact hHN.trans (le_of_eq (Set.mem_singleton_iff.1 hmem))

theorem uc22p22p_calCGS_le_of_normalizes (D : Data G) {R S : Subgroup G} (hST : S ≤ D.T)
    (hRS : R ≤ normalizer (S : Set G))
    (hloc : ∀ H : Subgroup G, IsTwoLocal H → R ≤ H → H ≤ D.M) : UC6.calCGS S ≤ D.M := by
  unfold UC6.calCGS
  refine iSup_le fun C => iSup_le fun hC1 => iSup_le fun hC2 => iSup_le fun hC3 => ?_
  haveI := hC3
  have hCmap : (C.subgroupOf S).map S.subtype = C := Subgroup.map_subgroupOf_eq_of_le hC2
  have key : ∀ y ∈ normalizer (S : Set G), ∀ c ∈ C, y * c * y⁻¹ ∈ C := by
    intro y hy c hc
    have h1 : c ∈ (C.subgroupOf S).map S.subtype := by rw [hCmap]; exact hc
    have h2 := uc22br4_conj_mem_map_of_characteristic (D := C.subgroupOf S) hy h1
    rwa [hCmap] at h2
  have hRC : R ≤ normalizer (C : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact key x (hRS hx) h hh
    · intro hh
      have := key x⁻¹ (hRS (R.inv_mem hx)) _ hh
      simpa [mul_assoc] using this
  have hCp : IsPGroup 2 C := D.sylowM.isPGroup.to_le (hC2.trans hST)
  exact hloc _ ⟨C, hC1, hCp, rfl⟩ hRC

theorem uc22p22p_calCGS_le_of_inCalV (D : Data G) {V : Subgroup G} (hV : InCalV D.M V)
    (hV1 : UniqueMax D.M (D.M ⊓ normalizer ((D.T ⊓ centralizer (V : Set G) : Subgroup G) : Set G)))
    (hJ : ⁅jOf D.T, V⁆ = ⊥) : UC6.calCGS (proofS D) ≤ D.M := by
  have hJc : jOf D.T ≤ centralizer (V : Set G) := commutator_eq_bot_iff_le_centralizer.1 hJ
  refine uc22p22p_calCGS_le_of_normalizes D (inf_le_left : proofS D ≤ D.T) ?_
    (fun H hH hRH => uc22p22p_le_of_uniqueMax hV1 hH hRH)
  intro y hy
  obtain ⟨-, hyN⟩ := Subgroup.mem_inf.1 hy
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · exact fun hs => uc22p22p_conj_proofS D hV hJc hyN s hs
  · intro hs
    have := uc22p22p_conj_proofS D hV hJc (inv_mem hyN) _ hs
    simpa [mul_assoc] using this

theorem uc22p22p_not_calCGS_le_of_6_40 (D : Data G) (h640 : UC6.R6_40_2 D)
    (hCle : centralizer (D.Z : Set G) ≤ D.M) : ¬ UC6.calCGS (proofS D) ≤ D.M := fun h =>
  uc22br4_M_ne_top D (top_le_iff.1 (h640.2.le.trans (sup_le h hCle)))

theorem uc22p22p_jT_ne_of_inCalV (D : Data G) (h640 : UC6.R6_40_2 D) {V : Subgroup G}
    (hV : InCalV D.M V)
    (hV1 : UniqueMax D.M (D.M ⊓ normalizer ((D.T ⊓ centralizer (V : Set G) : Subgroup G) : Set G)))
    (hCle : centralizer (D.Z : Set G) ≤ D.M) : ⁅jOf D.T, V⁆ ≠ ⊥ := fun hJ =>
  uc22p22p_not_calCGS_le_of_6_40 D h640 hCle (uc22p22p_calCGS_le_of_inCalV D hV hV1 hJ)

theorem uc22p22p_r1225_one_of_6_40 (D : Data G) (h640 : UC6.R6_40_2 D) :
    ∀ V : Subgroup G, InCalW D.M D.T V → centralizer (D.Z : Set G) ≤ D.M →
      ⁅jOf D.T, V⁆ ≠ ⊥ ∧ ¬ UC6.calCGS (CFSG.RankThree.PartOne.pushingUpS D.T) ≤ D.M :=
  fun _ hW hCle => ⟨uc22p22p_jT_ne_of_inCalV D h640 hW.1.1 hW.1.2 hCle,
    uc22p22p_not_calCGS_le_of_6_40 D h640 hCle⟩

theorem uc22p22p_mbarImage_ne_bot (D : Data G) {V : Subgroup G} (hVU : V ≤ D.U)
    (hJ : ⁅jOf D.T, V⁆ ≠ ⊥) : mbarImage D.M D.U (proofN D) ≠ ⊥ := by
  intro hbot
  apply hJ
  have hle : proofN D ≤ centralizer (D.U : Set G) :=
    (uc22br4_mbarImage_eq_bot_iff D.M D.U (proofN D) (le_normalizer_uCore D.M D.T)
      (uc22p22e_jOf_le_self D.M)).1 hbot
  exact commutator_eq_bot_iff_le_centralizer.2 (((uc22p22e_jOf_le D.sylowM).trans hle).trans
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hVU)))

theorem uc22p22p_jT_ne_of_6_40 (D : Data G) (h640 : UC6.R6_40_2 D)
    (hV1 : UniqueMax D.M (D.M ⊓ normalizer ((D.T ⊓ centralizer (D.U : Set G) : Subgroup G) : Set G)))
    (hCle : centralizer (D.Z : Set G) ≤ D.M) : ⁅F12.jOf D.T, D.U⁆ ≠ ⊥ :=
  uc22p22p_jT_ne_of_inCalV D h640 (uc22p22e_inCalV_U D) hV1 hCle

theorem uc22p22p_s22_3_1_of (D : Data G) (Ch : Choice2011 G) (h640 : UC6.R6_40_2 D)
    (hV1 : H1930 D → ∀ _ : Ctx22c D Ch,
      UniqueMax D.M (D.M ⊓ normalizer ((D.T ⊓ centralizer (D.U : Set G) : Subgroup G) : Set G))) :
    S22_3_1 D Ch := by
  intro h1930 c
  have hJ := uc22p22p_jT_ne_of_6_40 D h640 (hV1 h1930 c) c.hCle
  exact ⟨uc22p22p_mbarImage_ne_bot D le_rfl hJ, uc22p22p_not_calCGS_le_of_6_40 D h640 c.hCle⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
