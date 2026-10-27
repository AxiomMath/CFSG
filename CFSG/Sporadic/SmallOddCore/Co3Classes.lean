module

public import CFSG.Sporadic.SmallOddCore.Co3FusionCheck
public import CFSG.Sporadic.SmallOddCore.CentSpec
public import CFSG.Sporadic.SmallOddCore.TableFacts
public import CFSG.Sporadic.Schreier.Co3Centralizers

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Schreier.Co3
open CFSG.Certificates
open CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem co3TTbls_size : co3TTbls.size = 8 := by
  simp [co3TTbls, co3TArrs_size]

theorem co3TTbls_get {k : ℕ} (hk : k < 8) : co3TTbls[k]! = co3TArrs[k]!.map UInt32.ofNat := by
  have hs : k < co3TTbls.size := by rw [co3TTbls_size]; exact hk
  rw [getElem!_pos _ k hs]
  simp only [co3TTbls, Array.getElem_map]
  rw [← getElem!_pos _ k (by simp [co3TArrs_size]; omega), co3TExtract_get hk]

theorem rep_co3TTbl
    {k : ℕ} (hk : k < 8) : Rep 276 co3TTbls[k]! (co3TGen k) := by
  rw [co3TTbls_get hk]
  exact rep_arrayMap_ofNat (by norm_num) (rep_co3TGen (by omega))

theorem rep_co3ZTbl :
    Rep 276 co3ZTbl co3Z := rep_arrayMap_ofNat (by norm_num) rep_co3Z

theorem rep_co3TtTbl :
    Rep 276 co3TtTbl co3Tt := rep_arrayMap_ofNat (by norm_num) rep_co3Tt

theorem mem_co3P_of_co3Sift
    {T : Table} {g : Equiv.Perm (Fin 276)} (hT : Rep 276 T g)
    (h : co3Sift T = true) : g ∈ co3P :=
  mem_co3P_of_sift (co2Rep_natArr_iff.2 hT) h

theorem co3_fusion_parts :
    (∀ g ∈ co3TTbls, permOK 276 g = true) ∧ (∀ g ∈ co3TTbls, invOK 276 g (invT 276 g) = true) ∧
      mulTreeOK 276 co3TTbls (mulClosureH 276 co3TTbls 2000).1
        (mulClosureH 276 co3TTbls 2000).2.1 (mulClosureH 276 co3TTbls 2000).2.2 = true ∧
      closedOK 276 (co3TTbls ++ co3TTbls.map (invT 276)) (mulClosureH 276 co3TTbls 2000).1 =
        true ∧
      hkeysDistinct 276 (mulClosureH 276 co3TTbls 2000).1.toList = true ∧
      (mulClosureH 276 co3TTbls 2000).1.size = 1024 ∧
      (∀ w ∈ co3FusionWits,
        permOK 276 w.1 = true ∧ invOK 276 w.1 (invT 276 w.1) = true ∧ co3Sift w.1 = true) ∧
      ((mulClosureH 276 co3TTbls 2000).1.filter (involOK 276)).size = 191 ∧
      (∀ s ∈ (mulClosureH 276 co3TTbls 2000).1.filter (involOK 276),
        ∃ w ∈ co3FusionWits, co3FusesTo s w = true) ∧
      (((mulClosureH 276 co3TTbls 2000).1.filter (involOK 276)).filter fun s =>
        co3FusionWits.any fun w => w.2 && co3FusesTo s w).size = 55 ∧
      (((mulClosureH 276 co3TTbls 2000).1.filter (involOK 276)).filter fun s =>
        co3FusionWits.any fun w => !w.2 && co3FusesTo s w).size = 136 := by
  have h := co3_fusionOK
  simp only [co3FusionOK, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true', List.all_eq_true,
    List.any_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hg, htree⟩, hclosed⟩, hdist⟩, hsize⟩, hw⟩, hI⟩, hcov⟩, hz⟩, ht⟩ := h
  exact ⟨fun g hg' => (hg g hg').1, fun g hg' => (hg g hg').2, htree, hclosed, hdist, hsize,
    fun w hw' => ⟨(hw w hw').1.1, (hw w hw').1.2, (hw w hw').2⟩, hI, hcov, hz, ht⟩

theorem co3_closure_TTbls :
    closure (tp 276 '' {x | x ∈ co3TTbls}) = co3T := by
  rw [co3T_eq]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem hx
    rw [co3TTbls_size] at hk
    have hr := rep_co3TTbl hk
    rw [getElem!_pos _ k (by rw [co3TTbls_size]; exact hk)] at hr
    have hp := co3_fusion_parts.1 _ (Array.getElem_mem (by rw [co3TTbls_size]; exact hk))
    exact ⟨⟨k, hk⟩, rep_unique hr (rep_tp hp)⟩
  · rintro ⟨k, rfl⟩
    have hk := k.2
    have hr := rep_co3TTbl hk
    have hmem := getElem!_mem_array (A := co3TTbls) (l := k) (by rw [co3TTbls_size]; exact hk)
    exact ⟨_, hmem, rep_unique (rep_tp (co3_fusion_parts.1 _ hmem)) hr⟩

theorem co3_T_enum :
    (∀ k < (mulClosureH 276 co3TTbls 2000).1.size,
        Rep 276 (mulClosureH 276 co3TTbls 2000).1[k]!
          (tablePerm 276 (mulClosureH 276 co3TTbls 2000).1[k]!) ∧
        tablePerm 276 (mulClosureH 276 co3TTbls 2000).1[k]! ∈ co3T) ∧
      (∀ x ∈ co3T, ∃ k < (mulClosureH 276 co3TTbls 2000).1.size,
        Rep 276 (mulClosureH 276 co3TTbls 2000).1[k]! x) := by
  obtain ⟨hp, hinv, htree, hclosed, hdist, -⟩ := co3_fusion_parts
  have h := enum_spec (by norm_num) hp hinv htree hclosed hdist
  rw [co3_closure_TTbls] at h
  exact ⟨h.1, h.2.1⟩

theorem ncard_eq_length_of_nodup {α : Type*} {S : Set α} {L : List α} (hL : L.Nodup)
    (h : ∀ x, x ∈ S ↔ x ∈ L) : S.ncard = L.length := by
  classical
  have : S = (L.toFinset : Set α) := by
    ext x
    rw [h x, Finset.mem_coe, List.mem_toFinset]
  rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup hL]

theorem co3_count_filter
    (p : Table → Bool) (Q : Equiv.Perm (Fin 276) → Prop)
    (hpQ : ∀ k < (mulClosureH 276 co3TTbls 2000).1.size,
      (p (mulClosureH 276 co3TTbls 2000).1[k]! = true ↔
        Q (tablePerm 276 (mulClosureH 276 co3TTbls 2000).1[k]!))) :
    {x | x ∈ co3T ∧ Q x}.ncard = ((mulClosureH 276 co3TTbls 2000).1.filter p).size := by
  classical
  set E := (mulClosureH 276 co3TTbls 2000).1
  obtain ⟨hE, hall⟩ := co3_T_enum
  have hrep : ∀ k < E.size, Rep 276 E[k]! (tablePerm 276 E[k]!) := fun k hk => (hE k hk).1
  have hnodup : (E.toList.map (tablePerm 276)).Nodup :=
    nodup_of_hkeysDistinct (forall₂_tablePerm hrep) co3_fusion_parts.2.2.2.2.1
  rw [← Array.length_toList, Array.toList_filter, ← List.length_map (tablePerm 276)]
  refine ncard_eq_length_of_nodup (hnodup.sublist (List.filter_sublist.map _)) fun x => ?_
  simp only [Set.mem_ofPred_eq, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨hx, hQ⟩
    obtain ⟨k, hk, hkx⟩ := hall x hx
    have hx' : tablePerm 276 E[k]! = x := tablePerm_eq hkx
    refine ⟨E[k]!, ⟨Array.mem_toList_iff.2 (getElem!_mem_array hk), ?_⟩, hx'⟩
    rw [hpQ k hk, hx']
    exact hQ
  · rintro ⟨T, ⟨hT, hpT⟩, rfl⟩
    obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.1 hT)
    rw [← getElem!_pos E k hk] at hpT ⊢
    exact ⟨(hE k hk).2, (hpQ k hk).1 hpT⟩

theorem co3_z_not_conj_t :
    ¬ ∃ g ∈ co3P, co3Tt = g * co3Z * g⁻¹ := by
  rintro ⟨g, hg, h⟩
  have h1 : Nat.card ↥(co3P ⊓ centralizer ({co3Tt} : Set (Equiv.Perm (Fin 276)))) =
      Nat.card ↥(co3P ⊓ centralizer ({co3Z} : Set (Equiv.Perm (Fin 276)))) := by
    rw [h, inf_centralizer_conj co3P hg, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  rw [← co3M1_eq_centralizer, ← co3M_eq_centralizer, card_co3M1, card_co3M] at h1
  omega

theorem co3_fusesTo_spec
    {s : Table} {S : Equiv.Perm (Fin 276)} (hs : Rep 276 s S)
    {w : Table × Bool} (hw : w ∈ co3FusionWits) (h : co3FusesTo s w = true) :
    ∃ g ∈ co3P, S = g * (if w.2 then co3Z else co3Tt) * g⁻¹ := by
  obtain ⟨hperm, hinv, hsift⟩ := co3_fusion_parts.2.2.2.2.2.2.1 w hw
  have hr := rep_tp hperm
  have hP := mem_co3P_of_co3Sift hr hsift
  have hc : Rep 276 (conjT 276 w.1 (invT 276 w.1) s) (tp 276 w.1 * S * (tp 276 w.1)⁻¹) :=
    (hr.compT hs).compT (rep_invT hr hinv)
  have htarget : Rep 276 (if w.2 then co3ZTbl else co3TtTbl) (if w.2 then co3Z else co3Tt) := by
    cases w.2
    · rw [ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true]; exact rep_co3TtTbl
    · rw [ite_eq_left rfl, ite_eq_left rfl]; exact rep_co3ZTbl
  have he := (tblEq_iff_eq hc htarget).1 h
  refine ⟨(tp 276 w.1)⁻¹, co3P.inv_mem hP, ?_⟩
  rw [← he]
  group

theorem ctuc_co3_complete_inner_involution_classes :
    {s | s ∈ co3T ∧ orderOf s = 2}.ncard = 191 ∧
      {s | s ∈ co3T ∧ (orderOf s = 2 ∧ ∃ g ∈ co3P, s = g * co3Z * g⁻¹)}.ncard = 55 ∧
      {s | s ∈ co3T ∧ (orderOf s = 2 ∧ ∃ g ∈ co3P, s = g * co3Tt * g⁻¹)}.ncard = 136 ∧
      (∀ u ∈ co3P, orderOf u = 2 →
        ((∃ g ∈ co3P, u = g * co3Z * g⁻¹) ↔ ¬ ∃ g ∈ co3P, u = g * co3Tt * g⁻¹)) ∧
      (conjClass co3P co3Z).ncard = 170775 ∧ (conjClass co3P co3Tt).ncard = 2608200 := by
  classical
  obtain ⟨-, -, -, -, -, -, -, hI, hcov, hz55, ht136⟩ := co3_fusion_parts
  set E := (mulClosureH 276 co3TTbls 2000).1
  obtain ⟨hE, hall⟩ := co3_T_enum
  have hn : 276 < 2 ^ 32 := by norm_num
  have hinvol : ∀ k < E.size,
      (involOK 276 E[k]! = true ↔ orderOf (tablePerm 276 E[k]!) = 2) := fun k hk =>
    ⟨orderOf_eq_two_of_involOK hn (hE k hk).1, involOK_of_orderOf hn (hE k hk).1⟩
  have hzt : ∀ x : Equiv.Perm (Fin 276), (∃ g ∈ co3P, x = g * co3Z * g⁻¹) →
      ¬ ∃ g ∈ co3P, x = g * co3Tt * g⁻¹ := by
    rintro x ⟨g, hg, rfl⟩ ⟨h, hh, he⟩
    apply co3_z_not_conj_t
    refine ⟨h⁻¹ * g, co3P.mul_mem (co3P.inv_mem hh) hg, ?_⟩
    have : co3Tt = h⁻¹ * (g * co3Z * g⁻¹) * h := by rw [he]; group
    rw [this]
    group
  have hfuse : ∀ k < E.size, involOK 276 E[k]! = true →
      ∃ w ∈ co3FusionWits, co3FusesTo E[k]! w = true := by
    intro k hk hk2
    have hmem : E[k]! ∈ E.filter (involOK 276) := by
      rw [Array.mem_filter]
      exact ⟨getElem!_mem_array hk, hk2⟩
    exact hcov _ hmem
  have hzw : ∀ k < E.size, involOK 276 E[k]! = true →
      ((co3FusionWits.any fun w => w.2 && co3FusesTo E[k]! w) = true ↔
        ∃ g ∈ co3P, tablePerm 276 E[k]! = g * co3Z * g⁻¹) := by
    intro k hk hk2
    rw [List.any_eq_true]
    constructor
    · rintro ⟨w, hw, hb⟩
      rw [Bool.and_eq_true] at hb
      obtain ⟨g, hg, he⟩ := co3_fusesTo_spec (hE k hk).1 hw hb.2
      rw [hb.1, ite_eq_left rfl] at he
      exact ⟨g, hg, he⟩
    · intro hconj
      obtain ⟨w, hw, hb⟩ := hfuse k hk hk2
      refine ⟨w, hw, ?_⟩
      cases hw2 : w.2
      · exfalso
        obtain ⟨g, hg, he⟩ := co3_fusesTo_spec (hE k hk).1 hw hb
        rw [hw2, ite_eq_right Bool.false_ne_true] at he
        exact hzt _ hconj ⟨g, hg, he⟩
      · simpa [hw2] using hb
  have htw : ∀ k < E.size, involOK 276 E[k]! = true →
      ((co3FusionWits.any fun w => !w.2 && co3FusesTo E[k]! w) = true ↔
        ∃ g ∈ co3P, tablePerm 276 E[k]! = g * co3Tt * g⁻¹) := by
    intro k hk hk2
    rw [List.any_eq_true]
    constructor
    · rintro ⟨w, hw, hb⟩
      rw [Bool.and_eq_true] at hb
      obtain ⟨g, hg, he⟩ := co3_fusesTo_spec (hE k hk).1 hw hb.2
      rw [Bool.not_eq_true'] at hb
      rw [hb.1, ite_eq_right Bool.false_ne_true] at he
      exact ⟨g, hg, he⟩
    · intro hconj
      obtain ⟨w, hw, hb⟩ := hfuse k hk hk2
      refine ⟨w, hw, ?_⟩
      cases hw2 : w.2
      · simpa [hw2] using hb
      · exfalso
        obtain ⟨g, hg, he⟩ := co3_fusesTo_spec (hE k hk).1 hw hb
        rw [hw2, ite_eq_left rfl] at he
        exact hzt _ ⟨g, hg, he⟩ hconj
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [co3_count_filter (involOK 276) (fun x => orderOf x = 2) hinvol, hI]
  · have hz := hz55
    simp only [Array.filter_filter] at hz
    rw [co3_count_filter (fun s => (co3FusionWits.any fun w => w.2 && co3FusesTo s w) &&
      involOK 276 s) (fun x => orderOf x = 2 ∧ ∃ g ∈ co3P, x = g * co3Z * g⁻¹) fun k hk => by
        rw [Bool.and_eq_true, hinvol k hk]
        constructor
        · rintro ⟨hw, h2⟩
          exact ⟨h2, (hzw k hk ((hinvol k hk).2 h2)).1 hw⟩
        · rintro ⟨h2, hc⟩
          exact ⟨(hzw k hk ((hinvol k hk).2 h2)).2 hc, h2⟩]
    exact hz
  · have ht := ht136
    simp only [Array.filter_filter] at ht
    rw [co3_count_filter (fun s => (co3FusionWits.any fun w => !w.2 && co3FusesTo s w) &&
      involOK 276 s) (fun x => orderOf x = 2 ∧ ∃ g ∈ co3P, x = g * co3Tt * g⁻¹) fun k hk => by
        rw [Bool.and_eq_true, hinvol k hk]
        constructor
        · rintro ⟨hw, h2⟩
          exact ⟨h2, (htw k hk ((hinvol k hk).2 h2)).1 hw⟩
        · rintro ⟨h2, hc⟩
          exact ⟨(htw k hk ((hinvol k hk).2 h2)).2 hc, h2⟩]
    exact ht
  ·
    intro u hu hu2
    refine ⟨hzt u, fun hnt => ?_⟩
    have hT : Nat.card co3T = 2 ^ (Nat.card co3P).factorization 2 := by
      rw [card_co3T, card_co3P, show (495766656000 : ℕ) = 2 ^ 10 * 484147125 by norm_num,
        factorization_two_pow_mul (by norm_num)]
      norm_num
    obtain ⟨x, hx, hxT⟩ := exists_conj_mem_of_card co3T_le_P hT hu hu2
    obtain ⟨k, hk, hkx⟩ := hall _ hxT
    have hkx' : tablePerm 276 E[k]! = x⁻¹ * u * x := tablePerm_eq hkx
    have h2 : orderOf (tablePerm 276 E[k]!) = 2 := by
      rw [hkx', show x⁻¹ * u * x = MulAut.conj x⁻¹ u by simp [mul_assoc],
        MulEquiv.orderOf_eq, hu2]
    obtain ⟨w, hw, hb⟩ := hfuse k hk ((hinvol k hk).2 h2)
    obtain ⟨g, hg, he⟩ := co3_fusesTo_spec (hE k hk).1 hw hb
    have hu' : u = (x * g) * (if w.2 then co3Z else co3Tt) * (x * g)⁻¹ := by
      have : u = x * (x⁻¹ * u * x) * x⁻¹ := by group
      rw [this, ← hkx', he]
      group
    cases hw2 : w.2
    · rw [hw2, ite_eq_right Bool.false_ne_true] at hu'
      exact absurd ⟨x * g, co3P.mul_mem hx hg, by simpa using hu'⟩ hnt
    · rw [hw2, ite_eq_left rfl] at hu'
      exact ⟨x * g, co3P.mul_mem hx hg, by simpa using hu'⟩
  · have h := ncard_conjClass_mul_card co3P co3Z
    have hc : Nat.card ↥(co3P ⊓ centralizer ({co3Z} : Set (Equiv.Perm (Fin 276)))) = 2903040 :=
      co3M_eq_centralizer ▸ card_co3M
    rw [hc, card_co3P] at h
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2903040)
      (h.trans (by norm_num : (495766656000 : ℕ) = 170775 * 2903040))
  · have h := ncard_conjClass_mul_card co3P co3Tt
    have hc : Nat.card ↥(co3P ⊓ centralizer ({co3Tt} : Set (Equiv.Perm (Fin 276)))) = 190080 :=
      co3M1_eq_centralizer ▸ card_co3M1
    rw [hc, card_co3P] at h
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 190080)
      (h.trans (by norm_num : (495766656000 : ℕ) = 2608200 * 190080))

end CFSG.Sporadic.SmallOddCore
