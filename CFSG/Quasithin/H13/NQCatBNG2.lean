module

public import CFSG.Quasithin.H13.NQCatBNSolv
public import CFSG.Quasithin.H13.NQCatLieOverRank2

public section

namespace CFSG.Quasithin.H13.NQCat.BN

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.QuasithinUnique

variable {K : Type} [Field K]

theorem solvOver_map_of_ker_le_center {C Q : Type} [Group C] [Group Q] {U B : Subgroup C}
    (π : C →* Q) (hπ : Function.Surjective π) (hker : π.ker ≤ center C)
    (hBN : B ≤ normalizer (U : Set C))
    (h : ∀ A : Subgroup C, U ≤ A → Group.IsSolvable A → A ≤ B) : SolvOver Q (U.map π) := by
  intro X hUX hX
  have hUA : U ≤ X.comap π := fun u hu => hUX (mem_map_of_mem _ hu)
  have hcomm : ∀ a b : (π.subgroupComap X).ker, a * b = b * a := by
    rintro ⟨⟨a, ha⟩, ha'⟩ ⟨⟨b, hb⟩, hb'⟩
    have hac : a ∈ center C :=
      hker (MonoidHom.mem_ker.mpr (congrArg Subtype.val (MonoidHom.mem_ker.mp ha')))
    exact Subtype.ext (Subtype.ext (mem_center_iff.mp hac b).symm)
  have hkS : Group.IsSolvable (π.subgroupComap X).ker := Group.isSolvable_of_comm hcomm
  have hAS : Group.IsSolvable (X.comap π) :=
    Group.isSolvable_of_ker_le_range (π.subgroupComap X).ker.subtype (π.subgroupComap X)
      (by rw [range_subtype])
  calc X = (X.comap π).map π := (map_comap_eq_self_of_surjective hπ X).symm
    _ ≤ (normalizer (U : Set C)).map π := map_mono ((h _ hUA hAS).trans hBN)
    _ ≤ _ := le_normalizer_map π

theorem isSylowTwoOf_map {C Q : Type} [Group C] [Group Q] [Finite C] (π : C →* Q)
    (hπ : Function.Surjective π) {U : Subgroup C} (hU : IsSylowTwoOf U ⊤) :
    IsSylowTwoOf (U.map π) ⊤ := by
  refine ⟨le_top, hU.2.1.map π, fun h => hU.2.2 ?_⟩
  rw [show (U.subgroupOf ⊤).index = U.index from relIndex_top_right _]
  rw [show ((U.map π).subgroupOf ⊤).index = (U.map π).index from relIndex_top_right _] at h
  exact h.trans (index_map_dvd U hπ)

theorem posUnipotent_adjDatum
    (τ : Tag) [Finite K] :
    posUnipotent (adjDatum (rootOperatorFamily τ) K) = (nativeData τ K).U := by
  apply le_antisymm
  · refine iSup₂_le fun γ hγ => ?_
    have hr : IsRoot τ γ := mem_adjDatum_roots.1 hγ.1
    change rootGroup (rootOperatorFamily τ) K γ ≤ _
    rw [rootGroup_of_isRoot hr]
    exact RootGroupData.X_le_U (D := nativeData τ K) (α := ⟨γ, hr⟩) hγ.2
  · refine iSup₂_le fun α hα => ?_
    have h1 : (nativeData τ K).X α = (adjDatum (rootOperatorFamily τ) K).rootGroup α.1 := by
      change (rootOperatorFamily τ).rootSubgroup K α = rootGroup (rootOperatorFamily τ) K α.1
      rw [rootGroup_of_isRoot α.2]
    rw [h1]
    exact rootGroup_le_posUnipotent (mem_adjDatum_roots.2 α.2) hα

theorem borel_adjDatum_le
    (τ : Tag) [Finite K] :
    borel (adjDatum (rootOperatorFamily τ) K) (torus (τ := τ) K) ≤ (nativeData τ K).B := by
  refine sup_le (iSup_le fun i => ?_) ((posUnipotent_adjDatum τ).le.trans RootGroupData.U_le_B)
  rintro _ ⟨t, rfl⟩
  exact RootGroupData.H_le_B (torusElement_mem_H (nativeRootSubgroups τ K) i t)

theorem rankOne_not_solvable_g2
    [Finite K] [CharP K 2]
    (hK4 : ∃ s : Finset K, s.card = 4) (i : Fin (Tag.rank .G2)) :
    ¬ Group.IsSolvable (rankOne (g2Datum K).rootGroup i) := by
  obtain ⟨φ, hφ, hup, hlow⟩ := g2_exists_sl2_hom (K := K) i
  have hle : φ.range ≤ rankOne (g2Datum K).rootGroup i := by
    rw [MonoidHom.range_eq_map, ← CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower,
      MonoidHom.map_closure, closure_le]
    rintro _ ⟨g, hg | hg, rfl⟩
    · obtain ⟨c, rfl⟩ := hg
      have h1 := hup c
      change φ (sl2Upper c) ∈ _
      rw [h1, ← xPar_simple]
      exact xPar_single_mem_rankOne i c
    · obtain ⟨c, rfl⟩ := hg
      have h1 := hlow c
      change φ (sl2Lower c) ∈ _
      rw [h1, ← xPar_neg_simple]
      exact xPar_neg_single_mem_rankOne i c
  intro hsol
  have := Vol2Native.A312L.sl2_isSimple hK4
  obtain ⟨a, b, hab⟩ := Vol2Native.A312L.sl2_nonabelian hK4
  have hrs : Group.IsSolvable φ.range :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  have hs : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) K) :=
    Group.isSolvable_of_isSolvable_injective (f := φ.rangeRestrict)
      (MonoidHom.rangeRestrict_injective_iff.mpr hφ)
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hs a b)

theorem exists_sylow_posUnipotent_g2
    [Finite K] [CharP K 2]
    (hK4 : ∃ s : Finset K, s.card = 4) :
    ∃ S : Sylow 2 (adjointGroup .G2 K), (S : Subgroup (adjointGroup .G2 K)) =
      posUnipotent (g2Datum K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU : IsPGroup 2 (posUnipotent (g2Datum K)) := by
    rw [posUnipotent_adjDatum]
    exact (nativeRootSubgroups .G2 K).isPGroup_U 2
  refine CFSG.LieType.BorelTits.Weighted.exists_sylow_eq_of_normalizer 2 hU
    fun t ht ⟨k, hk⟩ => ?_
  have hz : IsPGroup 2 (zpowers t) := by
    rintro ⟨x, m, rfl⟩
    refine ⟨k, Subtype.ext ?_⟩
    change (t ^ m) ^ 2 ^ k = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
  have hA := hz.to_sup_of_normal_right' hU ((zpowers_le (G := adjointGroup .G2 K)).2 ht)
  have : Group.IsNilpotent ↥(zpowers t ⊔ posUnipotent (g2Datum K)) := hA.isNilpotent
  have hB := le_borel_of_isSolvable (g2_isCTGroupDatum K) (g2_steinbergExtras K)
    (rankOne_not_solvable_g2 hK4) (A := zpowers t ⊔ posUnipotent (g2Datum K)) le_sup_right
    inferInstance
  have htU := (nativeRootSubgroups .G2 K).mem_U_of_pow_eq_one 2
    (borel_adjDatum_le .G2 (hB (mem_sup_left (mem_zpowers t)))) hk
  rw [posUnipotent_adjDatum]
  exact htU

theorem solvOver_adjointQuotient_g2
    [Finite K] [CharP K 2]
    (hK4 : ∃ s : Finset K, s.card = 4) :
    SolvOver (AdjointQuotient .G2 K)
      ((posUnipotent (g2Datum K)).map (QuotientGroup.mk' (center (adjointGroup .G2 K)))) :=
  solvOver_map_of_ker_le_center _ (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _).le
    (borel_le_normalizer_posUnipotent (g2_isCTGroupDatum K)) fun _ hUA hA =>
      le_borel_of_isSolvable (g2_isCTGroupDatum K) (g2_steinbergExtras K)
        (rankOne_not_solvable_g2 hK4) hUA hA

theorem solvOver_of_isG2
    {S : Type} [Group S] [Finite S]
    {k : ℕ} (hk : 2 ≤ k) (h : CFSG.Quasithin.IsG2 2 k S) {P : Subgroup S} (hP : IsSylowTwoOf P ⊤) :
    SolvOver S P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ := h
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hcard
  have hK4 := exists_finset_card_four_of_card hk hcard
  obtain ⟨Q, hQ⟩ := exists_sylow_posUnipotent_g2 hK4
  have hU₀ := isSylowTwoOf_map _ (QuotientGroup.mk'_surjective (center (adjointGroup .G2 K)))
    (hQ ▸ isSylowTwoOf_top_of_sylow Q)
  exact solvOver_of_sylow (solvOver_adjointQuotient_g2 hK4) hU₀ e.symm hP

end CFSG.Quasithin.H13.NQCat.BN
