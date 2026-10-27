module

public import CFSG.Quasithin.H13.NQCoreChiefChain
public import CFSG.Quasithin.H13.NQCoreA3PushingFamily
public import CFSG.Quasithin.H13.NQCoreAtMostOneNoncentral
public import CFSG.Quasithin.SteinbergBSNormalSylowA3Family

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
open scoped commutatorElement

theorem stmtCoreContainedAtLeastTwoNoncentral_holds : StmtCoreContainedAtLeastTwoNoncentral := by
  intro G _ _ hev he2 F H T M V R hTsyl hTF hTH hHs hHc hTn hMH hMmax hTM hMu hVF hVn hVe hV1
    hVQ hR hRFn hRn hstrict hUe n hn
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hn2
  push Not at hn2
  set U := ⨆ (h : G) (_ : h ∈ H), V.map (MulAut.conj h).toMonoidHom with hUdef
  set Q := (CFSG.pCore 2 ↥H).map H.subtype with hQ
  have hT : IsSylowTwoOf T H :=
    ⟨hTH, hTsyl.1, fun h2 => hTsyl.2 (h2.trans (relIndex_dvd_index_of_le hTH))⟩
  have hQeq : Q = pCoreOf 2 H := by rw [hQ, pCoreOf]
  have hQT : Q ≤ T := hQeq ▸ EscapingLocal.pCoreOf_le_of_isSylowTwoOf hT
  have hHQ : H ≤ normalizer (Q : Set G) := hQeq ▸ LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hVR : V ≤ R := by
    rw [hR]
    exact le_inf (hVQ.trans hQT) (le_centralizer_iff_isMulCommutative.mpr hVe.1)
  have hRT : R ≤ T := hR ▸ inf_le_left
  have hRH : R ≤ H := hRT.trans hTH
  have hFV : F ≤ normalizer (V : Set G) := (normal_subgroupOf_iff_le_normalizer hVF).mp hVn
  have hFR : F ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (hRT.trans hTF)).mp hRFn
  have hcontra : ∀ X : Subgroup G, X ≤ R → X ≠ ⊥ → F ⊔ H ≤ normalizer (X : Set G) → False :=
    fun X hXR hX1 hXn => hRn X hXR hX1 ((normal_subgroupOf_iff_le_normalizer
      (hXR.trans ((hRT.trans hTF).trans le_sup_left))).mpr hXn)
  have hU2 : IsPGroup 2 U := hT.2.1.to_le ((SteinbergCD.iSup_conj_le hVQ hHQ).trans hQT)
  have hVU : V ≤ U := SteinbergCD.le_iSup_conj
  have hHK : H ≤ oddOrderSubgroup H ⊔ T := SteinbergCD.le_oddOrderSubgroup_sup_of_isSylowTwoOf hT
  interval_cases n
  ·
    have hKV : oddOrderSubgroup H ≤ centralizer (V : Set G) := by
      have h0 := D14.commutator_eq_bot_of_zero hU2 hn rfl
      rw [commutator_comm] at h0
      exact (commutator_eq_bot_iff_le_centralizer.mp h0).trans
        (centralizer_le (SetLike.coe_subset_coe.mpr hVU))
    exact hcontra V hVR hV1 (sup_le hFV (hHK.trans
      (sup_le (hKV.trans (centralizer_le_normalizer _)) (hTF.trans hFV))))
  ·
    obtain ⟨k, C, hC0, hCk, hCn, hCs, -, h1⟩ := exists_chain_of_isChiefSeriesFrom hn
    obtain ⟨-, -, -, -, -, hRsyl, -⟩ :=
      single_noncentral_chief_factor_forces_normal_core_intersection_and_residual_Sylow hTF hT
        hHs hTn hMH hMmax hTM hMu hQ hVF hVn hVe hV1 hVQ hR hRFn hRn hstrict hUdef hUe
        ⟨k, C, hC0, hCk, hCn, hCs, h1 rfl⟩ rfl rfl rfl
    have hback : ∀ Y : Subgroup ↥H, (Y.map H.subtype).subgroupOf H = Y := fun Y =>
      comap_map_eq_self_of_injective H.subtype_injective Y
    have hchar : CharTwo (⊤ : Subgroup ↥H) := Wreath.charTwo_top_of_charTwo hHc
    have hT' : IsSylowTwoOf (T.subgroupOf H) ⊤ := Layer.isSylowTwoOf_subgroupOf_top' hT
    have hMlt : M.subgroupOf H < ⊤ :=
      lt_top_iff_ne_top.mpr fun h => hMH.ne (le_antisymm hMH.le (subgroupOf_eq_top.mp h))
    have hTM' : T.subgroupOf H ≤ M.subgroupOf H := fun x hx =>
      mem_subgroupOf.mpr (hTM (mem_subgroupOf.mp hx))
    have hmax : ∀ Y : Subgroup ↥H, T.subgroupOf H ≤ Y → Y < ⊤ → Y ≤ M.subgroupOf H := by
      intro Y hTY hY
      obtain ⟨Y₁, hY₁, hYY₁⟩ := (eq_top_or_exists_le_coatom Y).resolve_left hY.ne
      have hlt : Y₁.map H.subtype < H := by
        refine lt_of_le_of_ne (map_subtype_le Y₁) fun h => hY₁.1 ?_
        rw [← hback Y₁, h, subgroupOf_self]
      have hmaxY : ∀ Z : Subgroup G, Y₁.map H.subtype < Z → Z ≤ H → Z = H := by
        intro Z hZ hZH
        have hlt' : Y₁ < Z.subgroupOf H := by
          refine lt_of_le_of_ne ?_ fun h => hZ.ne ?_
          · rw [← hback Y₁]
            exact fun x hx => hZ.le hx
          · rw [h, map_subgroupOf_eq_of_le hZH]
        have h2 := hY₁.2 _ hlt'
        calc Z = (Z.subgroupOf H).map H.subtype := (map_subgroupOf_eq_of_le hZH).symm
          _ = H := by rw [h2, ← MonoidHom.range_eq_map, range_subtype]
      have hTY₁ : T ≤ Y₁.map H.subtype := by
        rw [← map_subgroupOf_eq_of_le hTH]
        exact map_mono (hTY.trans hYY₁)
      calc Y ≤ Y₁ := hYY₁
        _ = (Y₁.map H.subtype).subgroupOf H := (hback Y₁).symm
        _ = M.subgroupOf H := by rw [hMu _ hlt hmaxY hTY₁]
    have hR1 : R.subgroupOf H ≠ ⊥ := by
      intro h
      have h2 := map_subgroupOf_eq_of_le hRH
      rw [h, Subgroup.map_bot] at h2
      exact hV1 (le_bot_iff.mp (hVR.trans h2.ge))
    have hRT' : R.subgroupOf H ≤ T.subgroupOf H := fun x hx =>
      mem_subgroupOf.mpr (hRT (mem_subgroupOf.mp hx))
    have hRTn : T.subgroupOf H ≤ normalizer ((R.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
      intro t ht
      rw [mem_normalizer_iff]
      intro x
      rw [mem_subgroupOf, mem_subgroupOf, coe_mul, coe_mul, coe_inv]
      exact mem_normalizer_iff.mp (hFR (hTF (mem_subgroupOf.mp ht))) x
    have hKmap : (oddOrderSubgroup (⊤ : Subgroup ↥H) ⊔ R.subgroupOf H).map H.subtype =
        oddOrderSubgroup H ⊔ R := by
      rw [Subgroup.map_sup, Wreath.oddOrderSubgroup_top_map, map_subgroupOf_eq_of_le hRH]
    have hRsyl' : IsSylowTwoOf (R.subgroupOf H)
        (oddOrderSubgroup (⊤ : Subgroup ↥H) ⊔ R.subgroupOf H) := by
      obtain ⟨hle, h2, hidx⟩ := hRsyl
      refine ⟨?_, h2.of_equiv (subgroupOfEquivOfLe hRH).symm, fun hd => hidx ?_⟩
      · rw [← map_le_map_iff_of_injective H.subtype_injective, hKmap,
          map_subgroupOf_eq_of_le hRH]
        exact hle
      · have h3 := relIndex_map_map_of_injective (R.subgroupOf H)
          (oddOrderSubgroup (⊤ : Subgroup ↥H) ⊔ R.subgroupOf H) H.subtype_injective
        rw [hKmap, map_subgroupOf_eq_of_le hRH] at h3
        change 2 ∣ R.relIndex (oddOrderSubgroup H ⊔ R)
        rw [h3]
        exact hd
    have hnoChar : Campbell.NoCharNormal (R.subgroupOf H) ⊤ :=
      Wreath.noCharNormal_top_of hRH fun X hX1 hXR hXc hHX => hcontra X hXR hX1
        (sup_le (hFR.trans (normalizer_le_normalizer_of_characteristic hXR hXc)) hHX)
    obtain ⟨r, L, hfam⟩ := SteinbergBS.solvable_normal_Sylow_part_commuting_A3_family hHs hchar
      hT' hTn hMlt hTM' hmax hR1 hRT' hRTn hRsyl' hnoChar
    have hK : ∀ i, IsShort2 ((L i).map H.subtype) := fun i =>
      Wreath.IsShort2.map_of_injective H.subtype H.subtype_injective (hfam.short i)
    have h3 : ∀ i, Nat.card (↥((L i).map H.subtype) ⧸ CFSG.pCore 2 ↥((L i).map H.subtype)) = 3 :=
      fun i => (Wreath.card_quot_pCore_map_injective H.subtype H.subtype_injective (L i)).trans
        (hfam.card_quot i)
    have hcomm : ∀ i j, i ≠ j → ⁅(L i).map H.subtype, (L j).map H.subtype⁆ = ⊥ :=
      fun i j hij => by rw [← Subgroup.map_commutator, hfam.commute i j hij, Subgroup.map_bot]
    have hmapconj : ∀ (X : Subgroup ↥H) (h : ↥H), (X.map (MulAut.conj h).toMonoidHom).map
        H.subtype = (X.map H.subtype).map (MulAut.conj (h : G)).toMonoidHom := by
      intro X h
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
    set Tsyl : Sylow 2 G := hTsyl.1.toSylow hTsyl.2 with hTsyldef
    have hperm : ∀ t ∈ (Tsyl : Subgroup G), ∀ i, ∃ j,
        CFSG.conjugate ((L i).map H.subtype) t = (L j).map H.subtype := by
      intro t ht i
      have htH : (⟨t, hTH ht⟩ : ↥H) ∈ T.subgroupOf H := mem_subgroupOf.mpr ht
      obtain ⟨j, hj⟩ := hfam.permuted _ (inv_mem htH) i
      refine ⟨j, ?_⟩
      have h2 := hmapconj (L i) (⟨t, hTH ht⟩ : ↥H)⁻¹
      rw [hj] at h2
      rw [h2]
      rfl
    have htrans : ∀ i j, ∃ t ∈ (Tsyl : Subgroup G),
        CFSG.conjugate ((L i).map H.subtype) t = (L j).map H.subtype := by
      intro i j
      obtain ⟨t, ht, hij⟩ := hfam.transitive i j
      refine ⟨(t : G)⁻¹, inv_mem (mem_subgroupOf.mp ht), ?_⟩
      have h2 := hmapconj (L i) t
      rw [hij] at h2
      simp only [CFSG.conjugate, inv_inv]
      exact h2.symm
    have hKeq : (⨆ i, (L i).map H.subtype) = oddOrderSubgroup H := by
      rw [← Subgroup.map_iSup, ← hfam.odd_eq, Wreath.oddOrderSubgroup_top_map]
    have hRsylE : IsSylowTwoOf R ((⨆ i, (L i).map H.subtype) ⊔ R) := by
      rw [hKeq]
      exact hRsyl
    have hJR : (thompsonJ (R.subgroupOf H)).map H.subtype = Campbell.elemThompsonIn 2 R := by
      have h2 : Campbell.elemThompsonIn 2 (R.subgroupOf H) = thompsonJ (R.subgroupOf H) :=
        elemThompson_map_subtype_eq_thompsonJ _
      rw [← h2, Wreath.elemThompsonIn_subgroupOf_map_eq hRH]
      exact (elemThompson_map_subtype_eq_thompsonJ R).symm
    have hJ : ∀ i, ⁅(L i).map H.subtype, Campbell.elemThompsonIn 2 R⁆ = (L i).map H.subtype :=
      fun i => by rw [← hJR, ← Subgroup.map_commutator, hfam.perfect_J i]
    obtain ⟨-, hR01, -, hR0S, hSR, hR0N⟩ :=
      two_local_rank_actual_A3_pushing_family_common_normal_subgroup hev he2 Tsyl (M := F)
        (R := R) hTF hRT hFR hfam.one_le (fun i => (L i).map H.subtype) hK h3 hcomm hperm htrans
        hRsylE hJ
    have hHle : H ≤ (⨆ i, (L i).map H.subtype) ⊔ (Tsyl : Subgroup G) := by
      rw [hKeq]
      exact hHK
    exact hcontra _ (hR0S.trans hSR) hR01 ((sup_le_sup_left hHle F).trans hR0N)

theorem stmtIntrinsicActionExclusion_of_inputs
    (hA7u : U3.SylowNormalizedMaximalLocalUniqueNormalizer)
    (hA7n : NQBlock.SylowNormalizedLocalNormalComponent) (hsing : StmtOriginalWitnessSingleton) :
    StmtIntrinsicActionExclusion :=
  stmtIntrinsicActionExclusion_of_atLeastTwo hA7u hA7n hsing
    stmtCoreContainedAtLeastTwoNoncentral_holds

end CFSG.Quasithin.H13.NQCore
