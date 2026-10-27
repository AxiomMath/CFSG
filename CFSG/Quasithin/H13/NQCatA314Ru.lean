module

public import CFSG.Quasithin.H13.NQCatA314Lat
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE68SporRu
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRu
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRu
public import CFSG.Quasithin.Background.A3Structure314Excl
public import CFSG.Sporadic.Ru

public section

namespace CFSG.Quasithin.H13.NQCat.A314D

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat
  CFSG.QuasithinUnique.Ch1.SporLat.Ru CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2
  CFSG.Blueprint CFSG.Quasithin.E6.Spor CFSG.Quasithin.S151S9T CFSG.Quasithin.S151S9T.LatAux
  CFSG.Quasithin.E2P.SporB CFSG.QuasithinUnique.Ch1.SporLat.RuCert
open CFSG.Sporadic.Ru.Native (ruData)

theorem ru_centralizer :
    ∃ z₀ : J ruData, orderOf z₀ = 2 ∧
      z₀ ∈ ruCtx.S ⊓ Subgroup.centralizer (ruCtx.S : Set (J ruData)) ∧
      Subgroup.centralizer ({z₀} : Set (J ruData)) = ruCtx.Y 1 := by
  obtain ⟨z₀, hz2, hZ, hzT⟩ := ruCtx_centre
  have : FaithfulSMul (J ruData) (Fin ruData.n) :=
    faithfulSMul_of_base (base_lt ru_facts) (base_property ru_facts)
  have hsT : ruCtx.D.sTabs = ruSTabsL := ru_D_sTabs
  obtain ⟨-, hr, hnc⟩ := Certificates.certificate4215
  have hnc2 : ncChk ruData.n ruCtx.ta ruSLPL[154]! = true := hnc
  have hnc' := not_central_of_ncChk (n := ruData.n) ruCtx.ha hzT hnc2
  have hL : ruCtx.D.Om.map (fun o => o.lbl.size) = #[1, 15, 21, 3, 3] :=
    ru_Om_map
  have hZ' : ruCtx.S ⊓ Subgroup.centralizer (ruCtx.S : Set (J ruData)) = Subgroup.zpowers z₀ :=
    hZ
  have hmax : ∀ j < (#[1, 15, 21, 3, 3] : Array ℕ).size, ruCtx.Y 1 ≤ ruCtx.Y j → j = 1 := by
    intro j hj hle
    have h1 := Subgroup.card_dvd_of_le hle
    rw [lat_card ruCtx hL 1 (by decide), lat_card ruCtx hL j hj] at h1
    have hk : ruCtx.k = 14 := rfl
    rw [hk] at h1
    have hj5 : j < 5 := hj
    revert h1
    interval_cases j <;> decide
  refine ⟨z₀, hz2, hZ' ▸ Subgroup.mem_zpowers z₀, ?_⟩
  exact centralizer_eq_member ruCtx hL hZ' hnc' (q := 1) (by decide) hmax
    (rChk_sound ruCtx hsT hzT (by norm_num) hr) (by decide)

theorem desc_ru
    (G : Type) [Group G] [Finite G] (L T B : Subgroup G) (hT : IsSylowTwoOf T L)
    (hB : B ∈ lFamily T) (hBL : B ≤ L) (hne : B ≠ L) (hR : IsSporadic .Ru ↥L)
    (hA : IsAlt 5 (ModO2 B)) (hO : Nat.card (CFSG.pCore 2 ↥B) = 2 ^ 11) :
    ∃ z : G, IsTwoCentralInvolution L z ∧
      B = perfectCore (L ⊓ Subgroup.centralizer ({z} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eL⟩ := hR
  have : IsSimpleGroup (NativeSporadic.Carrier .Ru) := CFSG.Sporadic.Ru.isSimpleGroup_Ru
  have hLs : IsSimpleGroup ↥L := eL.isSimpleGroup
  have hTL := hT.1
  have hBc : Nat.card B = 122880 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥B)
    rw [show Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) = 60 from A314.card_isAlt_five hA, hO] at h1
    norm_num at h1
    exact h1
  have hX := sup_ne_of_isSimpleGroup hB hBL hne hLs
  have hXT : T.subgroupOf L ≤ (B ⊔ T).subgroupOf L := Subgroup.subgroupOf_mono L le_sup_right
  have hXc : Nat.card ↥(B ⊔ T) = 245760 := by
    have hd := card_dvd_sup B T
    rw [hBc] at hd
    rcases ru_overgroups ⟨eL⟩ (isSylowTwoOf_top_subgroupOf hT) hXT with htop | ⟨m, hm, hcm, -⟩
    · exact absurd (le_antisymm (sup_le hBL hTL) (Subgroup.subgroupOf_eq_top.mp htop)) hX
    · rw [card_sup_subgroupOf hBL hTL] at hcm
      rw [hcm] at hd ⊢
      simp only [ruMems, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl
      all_goals first | rfl | exact absurd hd (by decide)
  obtain ⟨z₀, hz02, hz0Z, hC⟩ := ru_centralizer
  have hL : ruCtx.D.Om.map (fun o => o.lbl.size) = #[1, 15, 21, 3, 3] :=
    ru_Om_map
  have hN : ruCtx.D.O.lbl.size = 8906625 := ru_orbit_card
  have hY1 : Nat.card (ruCtx.Y 1) = 245760 := by
    rw [lat_card ruCtx hL 1 (by decide)]
    rfl
  have huniq : ∀ Zs : Subgroup (J ruData), ruCtx.S ≤ Zs →
      Nat.card Zs = Nat.card (Subgroup.centralizer ({z₀} : Set (J ruData))) →
        Zs = Subgroup.centralizer ({z₀} : Set (J ruData)) := by
    intro Zs hS hc
    rw [hC] at hc ⊢
    exact eq_member_of_card ruCtx hL (q := 1) (by decide) (by decide) (by rw [hN]; decide) hS hc
  have hXL : Nat.card ↥((B ⊔ T).subgroupOf L) =
      Nat.card (Subgroup.centralizer ({z₀} : Set (J ruData))) := by
    rw [card_sup_subgroupOf hBL hTL, hXc, hC, hY1]
  obtain ⟨z', hz'T, hz'c, hz'o, hXeq⟩ := @exists_eq_centralizer_of_unique (J ruData) ↥L
    (Subgroup.toGroup _) _ _ _ (eL.trans (seedEquiv ru_facts.toBaseFacts)) ruCtx.S ru_S_sylow z₀
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
