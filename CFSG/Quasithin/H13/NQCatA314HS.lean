module

public import CFSG.Quasithin.H13.NQCatA314Lat
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE68SporHS
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3TabM12
public import CFSG.Quasithin.Background.A3Structure314Excl
public import CFSG.RankThree.PartOne.K1214.Basic
public import CFSG.Sporadic.HS
public import CFSG.CharacterTheory.Semidihedral.ElementStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoKernel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3TabBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKCover
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKQuot
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Listed

public section

namespace CFSG.Quasithin.H13.NQCat.A314D

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat
  CFSG.QuasithinUnique.Ch1.SporLat.HS CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2
  CFSG.Blueprint CFSG.Quasithin.E6.Spor CFSG.Quasithin.S151S9T CFSG.Quasithin.S151S9T.LatAux
  CFSG.Quasithin.E2P.SporB
open CFSG.Sporadic.HS.Native (hsData)

theorem hs_centralizer :
    ∃ z₀ : J hsData, orderOf z₀ = 2 ∧
      z₀ ∈ hsCtx.S ⊓ Subgroup.centralizer (hsCtx.S : Set (J hsData)) ∧
      Subgroup.centralizer ({z₀} : Set (J hsData)) = hsCtx.Y 1 := by
  obtain ⟨z₀, hz2, hZ, hzT⟩ := hsCtx_centre
  have : FaithfulSMul (J hsData) (Fin hsData.n) :=
    faithfulSMul_of_base (base_lt hs_facts) (base_property hs_facts)
  obtain ⟨-, hw⟩ := Certificates.certificate4214
  obtain ⟨hnc, hR⟩ := hw z₀ hzT
  have hL : hsCtx.D.Om.map (fun o => o.lbl.size) = #[1, 15, 21, 3, 3] := hs_Om_map
  have hZ' : hsCtx.S ⊓ Subgroup.centralizer (hsCtx.S : Set (J hsData)) = Subgroup.zpowers z₀ :=
    hZ
  have hmax : ∀ j < (#[1, 15, 21, 3, 3] : Array ℕ).size, hsCtx.Y 1 ≤ hsCtx.Y j → j = 1 := by
    intro j hj hle
    have h1 := Subgroup.card_dvd_of_le hle
    rw [lat_card hsCtx hL 1 (by decide), lat_card hsCtx hL j hj] at h1
    have hk : hsCtx.k = 9 := rfl
    rw [hk] at h1
    have hj5 : j < 5 := hj
    revert h1
    interval_cases j <;> decide
  refine ⟨z₀, hz2, hZ' ▸ Subgroup.mem_zpowers z₀, ?_⟩
  exact centralizer_eq_member hsCtx hL hZ' hnc (q := 1) (by decide) hmax hR (by decide)

theorem desc_hs
    (G : Type) [Group G] [Finite G]
    (L T B : Subgroup G) (hT : IsSylowTwoOf T L) (hB : B ∈ lFamily T) (hBL : B ≤ L)
    (hne : B ≠ L) (hH : IsSporadic .HS ↥L)
    (hext : IsExt ↥B (fun V _ => IsZ4StarExtra2 V) (fun Y _ => IsAlt 5 Y)) :
    ∃ z : G, IsTwoCentralInvolution L z ∧
      B = perfectCore (L ⊓ Subgroup.centralizer ({z} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eL⟩ := hH
  have : IsSimpleGroup (NativeSporadic.Carrier .HS) := CFSG.Sporadic.HS.isSimpleGroup_HS
  have hLs : IsSimpleGroup ↥L := eL.isSimpleGroup
  have hTL := hT.1
  obtain ⟨V, hVn, ⟨Z, E, hZ4, -, hE, hZc, hZE, hZEi⟩, hA⟩ := hext
  have hVc : Nat.card V = 64 := by
    have : Z.Normal := ⟨fun z hz g => by
      rw [Subgroup.mem_center_iff.mp (hZc hz) g, mul_inv_cancel_right]
      exact hz⟩
    have h1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_normal E Z
    rw [sup_comm, hZE, inf_comm, hZEi, hZ4, hE.2, Subgroup.card_top] at h1
    norm_num at h1
    omega
  have hBc : Nat.card B = 3840 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup V
    rw [A314.card_isAlt_five hA, hVc] at h1
    norm_num at h1
    exact h1
  have hX := sup_ne_of_isSimpleGroup hB hBL hne hLs
  have hXT : T.subgroupOf L ≤ (B ⊔ T).subgroupOf L := Subgroup.subgroupOf_mono L le_sup_right
  have hXc : Nat.card ↥(B ⊔ T) = 7680 := by
    have hd := card_dvd_sup B T
    rw [hBc] at hd
    rcases hs_overgroups ⟨eL⟩ (isSylowTwoOf_top_subgroupOf hT) hXT with htop | ⟨m, hm, hcm, -⟩
    · exact absurd (le_antisymm (sup_le hBL hTL) (Subgroup.subgroupOf_eq_top.mp htop)) hX
    · rw [card_sup_subgroupOf hBL hTL] at hcm
      rw [hcm] at hd ⊢
      simp only [hsMems, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl
      all_goals first | rfl | exact absurd hd (by decide)
  obtain ⟨z₀, hz02, hz0Z, hC⟩ := hs_centralizer
  have hL : hsCtx.D.Om.map (fun o => o.lbl.size) = #[1, 15, 21, 3, 3] := hs_Om_map
  have hN : hsCtx.D.O.lbl.size = 86625 := hs_O_size
  have hY1 : Nat.card (hsCtx.Y 1) = 7680 := by
    rw [lat_card hsCtx hL 1 (by decide)]
    rfl
  have huniq : ∀ Zs : Subgroup (J hsData), hsCtx.S ≤ Zs →
      Nat.card Zs = Nat.card (Subgroup.centralizer ({z₀} : Set (J hsData))) →
        Zs = Subgroup.centralizer ({z₀} : Set (J hsData)) := by
    intro Zs hS hc
    rw [hC] at hc ⊢
    exact eq_member_of_card hsCtx hL (q := 1) (by decide) (by decide) (by rw [hN]; decide) hS hc
  have hXL : Nat.card ↥((B ⊔ T).subgroupOf L) =
      Nat.card (Subgroup.centralizer ({z₀} : Set (J hsData))) := by
    rw [card_sup_subgroupOf hBL hTL, hXc, hC, hY1]
  obtain ⟨z', hz'T, hz'c, hz'o, hXeq⟩ := @exists_eq_centralizer_of_unique (J hsData) ↥L
    (Subgroup.toGroup _) _ _ _ (eL.trans (seedEquiv hs_facts.toBaseFacts)) hsCtx.S hs_S_sylow z₀
    hz0Z huniq (T.subgroupOf L) ((B ⊔ T).subgroupOf L) (isSylowTwoOf_top_subgroupOf hT) hXT hXL
  set z : G := (z' : G) with hzdef
  have hCX : L ⊓ Subgroup.centralizer ({z} : Set G) = B ⊔ T := by
    ext g
    constructor
    · rintro ⟨hgL, hgc⟩
      have h1 : (⟨g, hgL⟩ : L) ∈ Subgroup.centralizer ({z'} : Set ↥L) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hgc)
      rw [← hXeq] at h1
      exact Subgroup.mem_subgroupOf.mp h1
    · intro hg
      have hgL : g ∈ L := sup_le hBL hTL hg
      have h1 : (⟨g, hgL⟩ : L) ∈ (B ⊔ T).subgroupOf L := Subgroup.mem_subgroupOf.mpr hg
      rw [hXeq, Subgroup.mem_centralizer_singleton_iff] at h1
      exact ⟨hgL, Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val h1)⟩
  refine ⟨z, ⟨z'.2, ?_, T, hT, Subgroup.mem_subgroupOf.mp hz'T, fun s hs => ?_⟩, ?_⟩
  · rw [hzdef, Subgroup.orderOf_coe, hz'o, hz02]
  · have h1 := hz'c ⟨s, hTL hs⟩ (Subgroup.mem_subgroupOf.mpr hs)
    exact congrArg Subtype.val h1
  · rw [hCX]
    exact (A312S.perfectCore_eq_of_index_two le_sup_left (by rw [hXc, hBc])
      (perfect_of_mem_cComp hB)).symm

end CFSG.Quasithin.H13.NQCat.A314D
