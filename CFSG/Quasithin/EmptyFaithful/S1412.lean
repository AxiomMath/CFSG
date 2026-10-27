module

public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Quasithin.Background.Equivariance
public import CFSG.Quasithin.Background.A1cRank

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem normalizer_le_normalizer_of_characteristic_subgroupOf {S C : Subgroup G} (hCS : C ≤ S)
    (hchar : (C.subgroupOf S).Characteristic) :
    Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (C : Set G) := by
  have h := normalizer_le_normalizer_map_of_characteristic (C.subgroupOf S)
  rwa [Subgroup.map_subgroupOf_eq_of_le hCS] at h

theorem le_sylow_of_isTwoReducedIn (T : Sylow 2 G) {M V : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M) (hV : IsTwoReducedIn M V) : V ≤ T :=
  (le_pCoreOf_of_le_normalizer 2 hV.1 hV.2.1 (isPGroup_of_isElemAbelian hV.2.2.1)).trans
    (pCoreOf_two_le_sylow M T hTM)

theorem lemma_14_1_2_one (T : Sylow 2 G) {M V : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (hV : IsTwoReducedIn M V)
    (hJ : thompsonJ (T : Subgroup G) ≤ M ⊓ Subgroup.centralizer (V : Set G)) :
    V ≤ omegaOneCenterOf (thompsonJ (T : Subgroup G)) ∧
      baum (T : Subgroup G) = baum ((T : Subgroup G) ⊓ Subgroup.centralizer (V : Set G)) := by
  have hVT : V ≤ T := le_sylow_of_isTwoReducedIn T hTM hV
  have hJ' : thompsonJ (T : Subgroup G) ≤
      (T : Subgroup G) ⊓ Subgroup.centralizer (V : Set G) :=
    le_inf (iSup₂_le fun _ hA => hA.1) fun x hx => (hJ hx).2
  refine ⟨?_, baum_eq_baum_centralizer hV.2.2.1 hVT hJ'⟩
  rw [← (omegaOne_centralizer_thompsonJ (T : Subgroup G)).1]
  intro v hv
  refine Subgroup.subset_closure ⟨⟨hVT hv, Subgroup.mem_centralizer_iff.mpr fun j hj => ?_⟩,
    hV.2.2.1.2 v hv⟩
  exact (Subgroup.mem_centralizer_iff.mp (hJ' hj).2 v hv).symm

theorem lemma_14_1_2_two (hEven : quasithinEvenCharacteristic G) (T : Sylow 2 G)
    {M V : Subgroup G} (hmax : IsOrdMaximalIn (T : Subgroup G) (InM (T : Subgroup G)) M)
    (hV : IsTwoReducedIn M V)
    (hJ : thompsonJ (T : Subgroup G) ≤ M ⊓ Subgroup.centralizer (V : Set G))
    (hcase : A57.CaseA (T : Subgroup G) M V ∨ (V ≠ ⊥ ∧ A57.CaseB (T : Subgroup G) M V)) :
    IsUniqueM (M ⊓ Subgroup.normalizer (baum (T : Subgroup G) : Set G)) M ∧
      CGS (baum (T : Subgroup G)) ≤ M := by
  set R : Subgroup G := (T : Subgroup G) ⊓ Subgroup.centralizer (V : Set G) with hR
  have hTM : (T : Subgroup G) ≤ M := hmax.1.2
  have hS : baum (T : Subgroup G) = baum R := (lemma_14_1_2_one T hTM hV hJ).2
  have hU := A57.isUniqueM hEven T hmax hcase
  have hle : M ⊓ Subgroup.normalizer (R : Set G) ≤
      M ⊓ Subgroup.normalizer (baum (T : Subgroup G) : Set G) := by
    rw [hS]
    exact inf_le_inf_left M (normalizer_le_normalizer_baum R)
  have hUS : IsUniqueM (M ⊓ Subgroup.normalizer (baum (T : Subgroup G) : Set G)) M :=
    ⟨⟨hmax.1.1, inf_le_left⟩, fun M' hM' => hU.2 M' ⟨hM'.1, hle.trans hM'.2⟩⟩
  refine ⟨hUS, ?_⟩
  refine iSup_le fun C => iSup_le fun hCS => iSup_le fun hC1 => iSup_le fun hchar => ?_
  have hCp : IsPGroup 2 C := T.isPGroup'.to_le (hCS.trans inf_le_left)
  obtain ⟨M'', hM'', hNM''⟩ :=
    exists_maxTwoLocal_ge (L := Subgroup.normalizer (C : Set G)) ⟨C, hC1, hCp, rfl⟩
  have hNS : M ⊓ Subgroup.normalizer (baum (T : Subgroup G) : Set G) ≤ M'' :=
    (inf_le_right.trans (normalizer_le_normalizer_of_characteristic_subgroupOf hCS hchar)).trans
      hNM''
  rw [← hUS.2 M'' ⟨hM'', hNS⟩]
  exact hNM''

end CFSG.Quasithin
