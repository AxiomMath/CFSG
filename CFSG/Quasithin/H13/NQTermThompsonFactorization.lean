module

public import CFSG.Quasithin.H13.NQTermInternalModule
public import CFSG.Quasithin.Background.B2FactorizationSolvable
public import CFSG.Quasithin.Background.BlueprintB2Bridge
public import CFSG.Quasithin.Background.A1a
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.Quasithin.H13.NQTerm

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conjClosure_top_eq_normalClosure (Z : Subgroup G) :
    conjClosure Z ⊤ = Subgroup.normalClosure (Z : Set G) := by
  unfold conjClosure Subgroup.normalClosure
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Group.mem_conjugatesOfSet_iff, mem_top, true_and, isConj_iff]
  constructor
  · rintro ⟨h, z, hz, rfl⟩
    exact ⟨z, hz, h, rfl⟩
  · rintro ⟨z, hz, h, rfl⟩
    exact ⟨h, z, hz, rfl⟩

theorem solvable_characteristic_two_three_free_thompson_factorization [Group.IsSolvable G]
    (hF : generalizedFitting G = pCore 2 G) (h3 : ¬ 3 ∣ Nat.card G) (T : Sylow 2 G)
    {Z U J : Subgroup G} (hZ : Z = quasithinOmegaOneCenter (T : Subgroup G))
    (hU : U = Subgroup.normalClosure (Z : Set G))
    (hJ : J = (elemThompson (T : Subgroup G) 2).map (T : Subgroup G).subtype) :
    IsCharacteristicP 2 G ∧ IsPrimeReduced 2 U ∧ J ≤ Subgroup.centralizer (U : Set G) ∧
    (∃ _ : U.Normal, Group.IsSolvable (G ⧸ Subgroup.centralizer (U : Set G)) ∧
      pCore 2 (G ⧸ Subgroup.centralizer (U : Set G)) = ⊥ ∧
      ¬ 3 ∣ Nat.card (G ⧸ Subgroup.centralizer (U : Set G))) ∧
    ((Subgroup.normalizer (J : Set G) : Set G) * (Subgroup.centralizer (U : Set G) : Set G) =
        Set.univ ∧
      (Subgroup.centralizer (U : Set G) : Set G) * (Subgroup.normalizer (J : Set G) : Set G) =
        Set.univ ∧
      (Subgroup.normalizer (J : Set G) : Set G) * (Subgroup.centralizer (Z : Set G) : Set G) =
        Set.univ ∧
      (Subgroup.centralizer (Z : Set G) : Set G) * (Subgroup.normalizer (J : Set G) : Set G) =
        Set.univ) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : IsCharacteristicP 2 G :=
    (isCharacteristicP_iff_generalizedFitting_eq_pCore G 2).mpr hF
  have hred : IsPrimeReduced 2 U := by
    rw [hU, hZ]
    exact (QuasithinUnique.Setup.qt_characteristic_p_Sylow_center_reduced_closure 2 hchar T
      (quasithinOmegaOneCenter_le_centerTorsion (T : Subgroup G))).2.1
  have hcharTop : CharTwo (⊤ : Subgroup G) := by
    unfold CharTwo
    rw [pCoreOf_top]
    exact inf_le_right.trans hchar
  have hT : IsSylowTwoOf (T : Subgroup G) ⊤ := by
    refine ⟨le_top, T.isPGroup', ?_⟩
    change ¬ 2 ∣ (T : Subgroup G).relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact T.not_dvd_index
  have hsolvTop : Group.IsSolvable (⊤ : Subgroup G) :=
    Group.isSolvable_of_surjective (f := (Subgroup.topEquiv (G := G)).symm.toMonoidHom)
      (Subgroup.topEquiv (G := G)).symm.surjective
  obtain ⟨hUel, -, hcase, -⟩ := B2_16 hsolvTop hcharTop hT rfl
  have hVU : conjClosure (quasithinOmegaOneCenter (T : Subgroup G)) ⊤ = U := by
    rw [conjClosure_top_eq_normalClosure, hU, hZ]
  have hJT : J = thompsonJ (T : Subgroup G) := by
    rw [hJ, elemThompson_map_subtype_eq_thompsonJ]
  have hUn : U.Normal := by rw [hU]; infer_instance
  have hNV : (⊤ : Subgroup G) ≤ Subgroup.normalizer
      ((conjClosure (quasithinOmegaOneCenter (T : Subgroup G)) ⊤ : Subgroup G) : Set G) := by
    rw [hVU, Subgroup.normalizer_eq_top]
  have hJC : thompsonJ (T : Subgroup G) ≤ Subgroup.centralizer
      ((conjClosure (quasithinOmegaOneCenter (T : Subgroup G)) ⊤ : Subgroup G) : Set G) := by
    rcases hcase with ⟨hJ', -⟩ | ⟨hJ', I, -, hJH, -, -, hnat, -⟩
    · exact hJ'
    · exfalso
      by_cases hI : I = ∅
      · subst hI
        have hbot : autI hUel (thompsonJ (⊤ : Subgroup G)) = ⊥ := by
          rw [hJH]
          simp
        rw [autI_eq_bot_iff hUel (le_top.trans hNV)] at hbot
        exact hJ' ((thompsonJ_le_thompsonJ_of_isSylowTwoOf hT).trans hbot)
      · obtain ⟨L, hL⟩ := Finset.nonempty_iff_ne_empty.mpr hI
        obtain ⟨e, -, -⟩ := hnat L hL
        have hL6 : Nat.card L = 6 := by
          rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
          decide
        have hLle : L ≤ autI hUel ⊤ := by
          refine (le_iSup₂_of_le L hL le_rfl : L ≤ ⨆ L' ∈ I, L').trans ?_
          rw [← hJH]
          exact autI_mono hUel le_top
        have hdvd : Nat.card L ∣ Nat.card G := by
          refine (Subgroup.card_dvd_of_le hLle).trans ?_
          unfold autI
          refine (Subgroup.card_map_dvd _ _).trans ?_
          exact (Subgroup.card_subgroup_dvd_card _).trans (Subgroup.card_subgroup_dvd_card _)
        rw [hL6] at hdvd
        exact h3 ((by norm_num : (3 : ℕ) ∣ 6).trans hdvd)
  rw [hVU] at hJC
  have hJU : J ≤ Subgroup.centralizer (U : Set G) := hJT ▸ hJC
  have hJC' := hJC
  rw [← hVU] at hJC'
  obtain ⟨-, hfact⟩ := B2_7_of_le_factor (V := conjClosure (quasithinOmegaOneCenter
    (T : Subgroup G)) ⊤) hNV hT hJC'
  rw [hVU] at hfact
  have hCZ : Subgroup.centralizer (U : Set G) ≤ Subgroup.centralizer (Z : Set G) :=
    Subgroup.centralizer_le (by rw [hU]; exact Subgroup.subset_normalClosure)
  have hNC : (Subgroup.normalizer (J : Set G) : Set G) *
      (Subgroup.centralizer (U : Set G) : Set G) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨n, hn, c, hc, rfl⟩ := hfact x (mem_top x)
    rw [← hJT] at hn
    exact ⟨n, hn.2, c, hc.2, rfl⟩
  have hCN : (Subgroup.centralizer (U : Set G) : Set G) *
      (Subgroup.normalizer (J : Set G) : Set G) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨n, hn, c, hc, hx⟩ := hfact x⁻¹ (mem_top _)
    rw [← hJT] at hn
    refine ⟨c⁻¹, (Subgroup.centralizer _).inv_mem hc.2, n⁻¹,
      (Subgroup.normalizer _).inv_mem hn.2, ?_⟩
    change c⁻¹ * n⁻¹ = x
    rw [← mul_inv_rev, ← hx, inv_inv]
  refine ⟨hchar, hred, hJU, ⟨hUn, ?_, ?_, ?_⟩, hNC, hCN, ?_, ?_⟩
  · exact Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)
  · obtain ⟨hn, -, hp⟩ := hred
    exact hp
  · exact fun h => h3 (h.trans (Subgroup.card_quotient_dvd_card _))
  · exact Set.eq_univ_of_univ_subset (hNC ▸ Set.mul_subset_mul_left hCZ)
  · exact Set.eq_univ_of_univ_subset (hCN ▸ Set.mul_subset_mul_right hCZ)

end CFSG.Quasithin.H13.NQTerm
