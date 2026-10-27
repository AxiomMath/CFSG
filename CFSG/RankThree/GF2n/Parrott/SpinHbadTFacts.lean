module

public import CFSG.RankThree.GF2n.Parrott.SpinTFacts
public import CFSG.RankThree.GF2n.Parrott.SpinHbadTChecks
public import CFSG.RankThree.GF2n.Parrott.SpinStabW0

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.RankThree.GF2n.Parrott.SpinRigid
open scoped Matrix

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "Mat8" => Matrix (Fin 8) (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s1A" => (⟨sigma1, sigma1_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s2A" => (⟨sigma2, sigma2_mem_A⟩ : A45)

private theorem hbadT_cols_t :
    colsOf (((rhoA tA : GL8) : Mat8)) = bT := by
  unfold bT
  rw [← spinMat_apply, cols_tA]

private theorem hbadT_cols_sigma :
    colsOf (((rhoA (s1A * s2A⁻¹) : GL8) : Mat8)) = bRho := by
  have h : s1A * s2A⁻¹ = evalSpinWord spinGenA (toW lRho) := by
    apply eq_evalSpinWord_of
    show permTab (sigma1 * sigma2⁻¹) = evalT t3 (toW lRho)
    decide +kernel
  rw [h, ← spinMat_apply]
  exact colsOf_spinMat_word _

private theorem hbadT_bitmask_t (v : V) :
    bitmask (((rhoA tA : GL8) : Mat8) *ᵥ v) = bapply bT (bitmask v) := by
  rw [← bapply_colsOf, hbadT_cols_t]

private theorem hbadT_bitmask_sigma (v : V) :
    bitmask (((rhoA (s1A * s2A⁻¹) : GL8) : Mat8) *ᵥ v) = bapply bRho (bitmask v) := by
  rw [← bapply_colsOf, hbadT_cols_sigma]

private theorem hbadT_bitmask_add3 (a b c : V) :
    bitmask (a + b + c) = bitmask a ^^^ bitmask b ^^^ bitmask c := by
  rw [bitmask_add, bitmask_add, Nat.xor_assoc]

private theorem hbadT_bitmask_t_add (m : V) :
    bitmask (((rhoA tA : GL8) : Mat8) *ᵥ m + m) =
      bapply bT (bitmask m) ^^^ bitmask m := by
  rw [bitmask_add, hbadT_bitmask_t]

private theorem hbadT_exists_of_mem_image {v : V} (hv : bitmask v ∈ hbadTImage) :
    ∃ m : V, ((rhoA tA : GL8) : Mat8) *ᵥ m + m = v := by
  refine ⟨vecOfNat (hbadTPreOf (bitmask v)), ?_⟩
  apply bitmask_injective
  rw [bitmask_add, hbadT_bitmask_t,
    bitmask_vecOfNat _ (hbadTPreOf_lt _ hv), hbadTImage_pre _ hv]

private theorem hbadT_vec_fixed {m : Nat} (hm : m ∈ hbadTFixedList) :
    ((rhoA tA : GL8) : Mat8) *ᵥ vecOfNat m = vecOfNat m := by
  apply bitmask_injective
  rw [hbadT_bitmask_t, bitmask_vecOfNat m (hbadTFixedList_lt m hm)]
  have hfix : fixesT m = true := (hbadTFixedList_mem (hbadTFixedList_lt m hm)).1 hm
  simpa [fixesT, bT] using hfix

private theorem hbadT_add_self_fixed (m : V) :
    ((rhoA tA : GL8) : Mat8) *ᵥ
        (((rhoA tA : GL8) : Mat8) *ᵥ m + m) =
      ((rhoA tA : GL8) : Mat8) *ᵥ m + m := by
  have h2 : ((rhoA tA : GL8) : Mat8) *ᵥ
      (((rhoA tA : GL8) : Mat8) *ᵥ m) = m := by
    have h := rhoA_mulVec_mul tA tA m
    rw [tA_mul_self, map_one, Units.val_one, Matrix.one_mulVec] at h
    exact h.symm
  rw [Matrix.mulVec_add, h2]
  exact add_comm _ _

private theorem hbadT_bitmask_mem_four {x A B C D : V}
    (h : x ∈ ({A, B, C, D} : Set V)) :
    bitmask x ∈ [bitmask A, bitmask B, bitmask C, bitmask D] := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with rfl | rfl | rfl | rfl <;> simp

private def hbadTElem (w : List Nat) : A45 := evalSpinWord spinGenA (toW w)

private def hbadTMatOf (w : List Nat) : B8 := evalB b3 (toW w)

private def hbadTList : List A45 := hbadTWords.map hbadTElem

private def hbadTCent : Subgroup A45 := Subgroup.centralizer ({tA} : Set A45)

private theorem hbadT_cols_elem (w : List Nat) :
    colsOf (((rhoA (hbadTElem w) : GL8) : Mat8)) = hbadTMatOf w := by
  unfold hbadTElem hbadTMatOf
  rw [← spinMat_apply]
  exact colsOf_spinMat_word _

private theorem hbadTElem_comm (w : List Nat) (hw : w ∈ hbadTWords) :
    hbadTElem w * tA = tA * hbadTElem w := by
  have hA : hbadTMatOf w ∈ hbadTMats := by
    rw [← hbadTMats_eq]
    exact List.mem_map_of_mem hw
  have hcomm : bmul (hbadTMatOf w) bT = bmul bT (hbadTMatOf w) :=
    b8Code_injective (hbadTMats_comm_t _ hA)
  apply rhoA_injective
  rw [map_mul, map_mul]
  apply Units.ext
  apply colsOf_injective
  rw [Units.val_mul, Units.val_mul, colsOf_mul, colsOf_mul, hbadT_cols_elem,
    hbadT_cols_t]
  exact hcomm

private theorem hbadTList_map_cols :
    hbadTList.map (fun a => colsOf (((rhoA a : GL8) : Mat8))) = hbadTMats := by
  unfold hbadTList
  rw [List.map_map]
  change hbadTWords.map (fun w => colsOf (((rhoA (hbadTElem w) : GL8) : Mat8))) =
    hbadTMats
  have hfun : (fun w => colsOf (((rhoA (hbadTElem w) : GL8) : Mat8))) = hbadTMatOf :=
    funext hbadT_cols_elem
  rw [hfun]
  exact hbadTMats_eq

private theorem hbadTList_nodup : hbadTList.Nodup := by
  have hmap := hbadTList_map_cols
  exact List.Nodup.of_map _ (by rw [hmap]; exact hbadTMats_nodup)

private theorem hbadTList_length : hbadTList.length = 1152 := by
  unfold hbadTList
  rw [List.length_map, hbadTWords_length]

private theorem hbadTList_toFinset_card : hbadTList.toFinset.card = 1152 := by
  rw [List.toFinset_card_of_nodup hbadTList_nodup, hbadTList_length]

private theorem hbadTElem_mem_C (a : A45) (ha : a ∈ hbadTList) : a ∈ hbadTCent := by
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 ha
  rw [hbadTCent, Subgroup.mem_centralizer_iff]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact (hbadTElem_comm w hw).symm

private theorem hbadT_mem_cent {a : A45} :
    a ∈ hbadTCent ↔ a * tA = tA * a := by
  rw [hbadTCent, Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact (h tA (Set.mem_singleton tA)).symm
  · intro h x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact h.symm

section Centralizer

private theorem hbadT_mem_list_of_mem_cent {a : A45} (ha : a ∈ hbadTCent) :
    a ∈ hbadTList := by
  have hCcard : Nat.card hbadTCent = 1152 := (qa45_involution_centralizers).1
  have hsub : (hbadTList.toFinset : Set A45) ⊆ (hbadTCent : Set A45) := by
    intro a ha
    exact hbadTElem_mem_C a (List.mem_toFinset.1 ha)
  have hEq : (hbadTList.toFinset : Set A45) = (hbadTCent : Set A45) := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_
    rw [← Nat.card_coe_set_eq]
    change Nat.card hbadTCent ≤ (hbadTList.toFinset : Set A45).ncard
    rw [hCcard, Set.ncard_coe_finset, hbadTList_toFinset_card]
  have : a ∈ (hbadTList.toFinset : Set A45) := by rw [hEq]; exact ha
  exact List.mem_toFinset.1 this

private theorem hbadT_cols_mem_mats {a : A45} (ha : a ∈ hbadTCent) :
    colsOf (((rhoA a : GL8) : Mat8)) ∈ hbadTMats := by
  have h := List.mem_map_of_mem (f := fun a => colsOf (((rhoA a : GL8) : Mat8)))
    (hbadT_mem_list_of_mem_cent ha)
  rwa [hbadTList_map_cols] at h

private theorem hbadTFilter_nodup (j0 l j1 : Nat) (hj0 : j0 ∈ hbadTClassReps) :
    (hbadTFilter j0 l j1).Nodup := by
  rw [hbadTFilter]
  exact List.Nodup.filter _ (hbadTGoodMats_nodup hj0)

private theorem hbadT_mem_filter {a : A45} {j ℓ j₁ : V} {j0 r : Nat}
    (haC : a ∈ hbadTCent)
    (haP : ∀ k : V, ((rhoA tA : GL8) : Mat8) *ᵥ k = k → b j k = 0 →
      ((rhoA a : GL8) : Mat8) *ᵥ k + k ∈ ({0, ℓ, j₁, j₁ + ℓ} : Set V))
    (hj0 : j0 ∈ hbadTClassReps) (hr : r ∈ hbadTImage)
    (hjr : bitmask j = j0 ^^^ r)
    (hl : bitmask ℓ ∈ hbadTImage)
    (hj1class : bitmask j₁ ∈ hbadTImage.map (fun r => j0 ^^^ r)) :
    colsOf (((rhoA a : GL8) : Mat8)) ∈
      hbadTFilter j0 (bitmask ℓ) (bitmask j₁) := by
  let A : B8 := colsOf (((rhoA a : GL8) : Mat8))
  have hM : A ∈ hbadTMats := hbadT_cols_mem_mats haC
  have hbits : ∀ m ∈ hbadTQ j0,
      bapply A m ^^^ m ∈ [0, bitmask ℓ, bitmask j₁, bitmask j₁ ^^^ bitmask ℓ] := by
    intro m hm
    rw [hbadTQ, List.mem_filter] at hm
    obtain ⟨hm_fixed, hmq⟩ := hm
    have hm_lt : m < 256 := hbadTFixedList_lt m hm_fixed
    have hmq' : bq j0 m = 0 := beq_iff_eq.1 hmq
    have hbqj : bq (bitmask j) m = 0 := by
      rw [hjr, hbadTbq_xor j0 hj0 r hr m hm_fixed, hmq',
        hbadTImage_perp r hr m hm_fixed]
      rfl
    have hfixk := hbadT_vec_fixed hm_fixed
    have hbjk : b j (vecOfNat m) = 0 := by
      rw [b_eq_zero_iff, bitmask_vecOfNat m hm_lt]
      exact hbqj
    have hP := haP _ hfixk hbjk
    have hmem4 : bitmask (((rhoA a : GL8) : Mat8) *ᵥ vecOfNat m + vecOfNat m) ∈
        [bitmask (0 : V), bitmask ℓ, bitmask j₁, bitmask (j₁ + ℓ)] :=
      hbadT_bitmask_mem_four hP
    rw [bitmask_zero, bitmask_add] at hmem4
    have hbm : bitmask (((rhoA a : GL8) : Mat8) *ᵥ vecOfNat m + vecOfNat m) =
        bapply A m ^^^ m := by
      rw [bitmask_add, ← bapply_colsOf, bitmask_vecOfNat m hm_lt]
    rwa [hbm] at hmem4
  have hpred : hbadTPred j0 (bitmask ℓ) (bitmask j₁) A = true := by
    unfold hbadTPred
    exact List.all_eq_true.2 fun m hm => by
      simp only [decide_eq_true_eq]
      exact hbits m hm
  have hgood : hbadTGood j0 A = true := by
    unfold hbadTGood
    exact List.all_eq_true.2 fun m hm => by
      simp only [decide_eq_true_eq]
      exact hbadTAdmissible j0 hj0 (bitmask ℓ) hl (bitmask j₁) hj1class _ (hbits m hm)
  rw [hbadTFilter, List.mem_filter]
  exact ⟨(hbadTGoodMats_mem hj0).2 ⟨hM, hgood⟩, hpred⟩

private theorem hbadT_filter_bound {j ℓ j₁ : V} {j0 r : Nat}
    (hj0 : j0 ∈ hbadTClassReps) (hr : r ∈ hbadTImage)
    (hjr : bitmask j = j0 ^^^ r)
    (hl : bitmask ℓ ∈ hbadTImage)
    (hj1class : bitmask j₁ ∈ hbadTImage.map (fun r => j0 ^^^ r)) :
    Nat.card {a : A45 // a * tA = tA * a ∧ ∀ k : V,
      ((rhoA tA : GL8) : Mat8) *ᵥ k = k → b j k = 0 →
      ((rhoA a : GL8) : Mat8) *ᵥ k + k ∈ ({0, ℓ, j₁, j₁ + ℓ} : Set V)} ≤ 16 := by
  classical
  let S := {a : A45 // a * tA = tA * a ∧ ∀ k : V,
    ((rhoA tA : GL8) : Mat8) *ᵥ k = k → b j k = 0 →
    ((rhoA a : GL8) : Mat8) *ᵥ k + k ∈ ({0, ℓ, j₁, j₁ + ℓ} : Set V)}
  change Nat.card S ≤ 16
  let f : S → B8 := fun a => colsOf (((rhoA (a : A45) : GL8) : Mat8))
  have hf_inj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply rhoA_injective
    apply Units.ext
    exact colsOf_injective hab
  have hf_mem : ∀ a : S, f a ∈
      (hbadTFilter j0 (bitmask ℓ) (bitmask j₁)).toFinset := by
    intro a
    apply List.mem_toFinset.2
    exact hbadT_mem_filter (hbadT_mem_cent.2 a.2.1) a.2.2 hj0 hr hjr hl hj1class
  have hle := Set.ncard_le_ncard_of_injOn (s := (Set.univ : Set S)) (t :=
    (hbadTFilter j0 (bitmask ℓ) (bitmask j₁)).toFinset) f (fun a _ => hf_mem a)
    (fun a _ b _ h => hf_inj h) (Set.toFinite _)
  rw [Set.ncard_univ, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup (hbadTFilter_nodup j0 (bitmask ℓ) (bitmask j₁) hj0)] at hle
  exact hle.trans (hbadTBound j0 hj0 (bitmask ℓ) hl (bitmask j₁) hj1class)

end Centralizer

theorem spin_q_mul_t_add_eq_zero (m : V) :
    q (((rhoA tA : GL8) : Mat8) *ᵥ m + m) = 0 := by
  rw [q_eq_zero_iff, bitmask_add, hbadT_bitmask_t]
  exact hbadTQSing _ (bitmask_lt m)

theorem spin_exists_eq_mul_t_add_of_perp (v : V)
    (hv : ∀ k : V, ((rhoA tA : GL8) : Mat8) *ᵥ k = k → b v k = 0) :
    ∃ m : V, v = ((rhoA tA : GL8) : Mat8) *ᵥ m + m := by
  have hperpmask : ∀ k ∈ hbadTFixedList, bq (bitmask v) k = 0 := by
    intro k hk
    have hfixk := hbadT_vec_fixed hk
    have hbk := hv _ hfixk
    rwa [b_eq_zero_iff, bitmask_vecOfNat k (hbadTFixedList_lt k hk)] at hbk
  have hmem := hbadTPerp _ (bitmask_lt v) hperpmask
  obtain ⟨m, hm⟩ := hbadT_exists_of_mem_image hmem
  exact ⟨m, hm.symm⟩

theorem spin_fixed_t_eq_sigma_add (k : V) (hk : ((rhoA tA : GL8) : Mat8) *ᵥ k = k) :
    ∃ u : V, ((rhoA tA : GL8) : Mat8) *ᵥ u = u ∧ ∃ m : V,
      k = ((rhoA (s1A * s2A⁻¹) : GL8) : Mat8) *ᵥ u + u + (((rhoA tA : GL8) : Mat8) *ᵥ m + m) := by
  have hkmem : bitmask k ∈ hbadTFixedList :=
    (hbadTFixedList_mem (bitmask_lt k)).2 ((fixesT_iff k).1 hk)
  obtain ⟨p, hp, hpk⟩ := hbadTSigmaCover _ hkmem
  obtain ⟨-, h2, h3, h4⟩ := hbadTSigmaPre_spec p hp
  have hu_lt : p.2.1 < 256 := hbadTFixedList_lt p.2.1 h2
  have hu_fix : bapply bT p.2.1 = p.2.1 := by
    have h := (hbadTFixedList_mem hu_lt).1 h2
    simpa [fixesT, bT] using h
  refine ⟨vecOfNat p.2.1, ?_, vecOfNat p.2.2, ?_⟩
  · apply bitmask_injective
    rw [hbadT_bitmask_t, bitmask_vecOfNat p.2.1 hu_lt, hu_fix]
  · apply bitmask_injective
    rw [hbadT_bitmask_add3, hbadT_bitmask_sigma, bitmask_vecOfNat p.2.1 hu_lt,
      hbadT_bitmask_t_add, bitmask_vecOfNat p.2.2 h3]
    rw [← hpk]
    exact h4

private theorem hbadT_count_fixed_perp (j : V) :
    Nat.card {k : V // ((rhoA tA : GL8) : Mat8) *ᵥ k = k ∧ b j k = 0} =
      (hbadTFixedPerp (bitmask j)).length := by
  classical
  change Nat.card (↥({k : V | ((rhoA tA : GL8) : Mat8) *ᵥ k = k ∧ b j k = 0} : Set V)) =
    (hbadTFixedPerp (bitmask j)).length
  rw [Nat.card_coe_set_eq]
  let T : Set Nat := (hbadTFixedPerp (bitmask j)).toFinset
  have hT : T.ncard = (hbadTFixedPerp (bitmask j)).length := by
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup]
    exact List.Nodup.filter _ (List.nodup_range)
  rw [← hT]
  refine Set.ncard_congr (fun v _ => bitmask v) ?_ ?_ ?_
  · intro v hv
    simp only [Set.mem_setOf_eq] at hv
    obtain ⟨htv, hbv⟩ := hv
    change bitmask v ∈ (hbadTFixedPerp (bitmask j)).toFinset
    rw [List.mem_toFinset, hbadTFixedPerp, List.mem_filter, List.mem_range]
    refine ⟨bitmask_lt v, ?_⟩
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨(fixesT_iff v).1 htv, (b_eq_zero_iff j v).1 hbv⟩
  · intro v1 _ v2 _ h
    exact bitmask_injective h
  · intro m hm
    change m ∈ (hbadTFixedPerp (bitmask j)).toFinset at hm
    rw [List.mem_toFinset, hbadTFixedPerp, List.mem_filter, List.mem_range] at hm
    obtain ⟨hm_lt, hm_b⟩ := hm
    simp only [Bool.and_eq_true, beq_iff_eq] at hm_b
    obtain ⟨hfix, hbq⟩ := hm_b
    refine ⟨vecOfNat m, ?_, bitmask_vecOfNat m hm_lt⟩
    refine ⟨?_, ?_⟩
    · apply bitmask_injective
      rw [hbadT_bitmask_t, bitmask_vecOfNat m hm_lt]
      simpa [fixesT, bT] using hfix
    · rw [b_eq_zero_iff, bitmask_vecOfNat m hm_lt]
      exact hbq

theorem spin_card_fixed_t_perp (j : V) (hj : ((rhoA tA : GL8) : Mat8) *ᵥ j = j)
    (hj' : ¬ ∃ m : V, j = ((rhoA tA : GL8) : Mat8) *ᵥ m + m) :
    Nat.card {k : V // ((rhoA tA : GL8) : Mat8) *ᵥ k = k ∧ b j k = 0} = 32 := by
  have hjmem : bitmask j ∈ hbadTFixedList :=
    (hbadTFixedList_mem (bitmask_lt j)).2 ((fixesT_iff j).1 hj)
  have hjn : bitmask j ∉ hbadTImage := by
    intro h
    obtain ⟨m, hm⟩ := hbadT_exists_of_mem_image h
    exact hj' ⟨m, hm.symm⟩
  rw [hbadT_count_fixed_perp j, hbadTFixedPerp_length _ hjmem hjn]

theorem spin_exists_of_perp_fixed_t_perp (j : V) (hj : ((rhoA tA : GL8) : Mat8) *ᵥ j = j)
    (v : V) (hv : ((rhoA tA : GL8) : Mat8) *ᵥ v = v)
    (hperp : ∀ k : V, ((rhoA tA : GL8) : Mat8) *ᵥ k = k → b j k = 0 → b v k = 0) :
    ∃ m : V, v = ((rhoA tA : GL8) : Mat8) *ᵥ m + m ∨
      v = j + (((rhoA tA : GL8) : Mat8) *ᵥ m + m) := by
  have hjmem : bitmask j ∈ hbadTFixedList :=
    (hbadTFixedList_mem (bitmask_lt j)).2 ((fixesT_iff j).1 hj)
  have hvmem : bitmask v ∈ hbadTFixedList :=
    (hbadTFixedList_mem (bitmask_lt v)).2 ((fixesT_iff v).1 hv)
  have hcheck : ∀ k ∈ hbadTFixedList,
      bq (bitmask j) k = 0 → bq (bitmask v) k = 0 := by
    intro k hk hjk
    have hfixk := hbadT_vec_fixed hk
    have hbjk : b j (vecOfNat k) = 0 := by
      rw [b_eq_zero_iff, bitmask_vecOfNat k (hbadTFixedList_lt k hk)]
      exact hjk
    have hbvk := hperp _ hfixk hbjk
    rwa [b_eq_zero_iff, bitmask_vecOfNat k (hbadTFixedList_lt k hk)] at hbvk
  rcases hbadTPerpFixed _ hjmem _ hvmem hcheck with h | h
  · obtain ⟨m, hm⟩ := hbadT_exists_of_mem_image h
    exact ⟨m, Or.inl hm.symm⟩
  · have hmem : bitmask (v + j) ∈ hbadTImage := by
      rw [bitmask_add]
      exact h
    obtain ⟨m, hm⟩ := hbadT_exists_of_mem_image hmem
    refine ⟨m, Or.inr ?_⟩
    rw [hm, add_comm j (v + j), add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem spin_card_centralizer_t_le_sixteen (j : V)
    (hj : ((rhoA tA : GL8) : Mat8) *ᵥ j = j)
    (hj' : ¬ ∃ m : V, j = ((rhoA tA : GL8) : Mat8) *ᵥ m + m)
    (ℓ j₁ : V) (hℓ : ∃ m : V, ℓ = ((rhoA tA : GL8) : Mat8) *ᵥ m + m)
    (hj₁ : ∃ m : V, j₁ = j + (((rhoA tA : GL8) : Mat8) *ᵥ m + m)) :
    Nat.card {a : A45 // a * tA = tA * a ∧ ∀ k : V, ((rhoA tA : GL8) : Mat8) *ᵥ k = k →
      b j k = 0 → ((rhoA a : GL8) : Mat8) *ᵥ k + k ∈ ({0, ℓ, j₁, j₁ + ℓ} : Set V)} ≤ 16 := by
  have hjmem : bitmask j ∈ hbadTFixedList :=
    (hbadTFixedList_mem (bitmask_lt j)).2 ((fixesT_iff j).1 hj)
  have hjn : bitmask j ∉ hbadTImage := by
    intro h
    obtain ⟨m, hm⟩ := hbadT_exists_of_mem_image h
    exact hj' ⟨m, hm.symm⟩
  obtain ⟨j0, hj0, r, hr, hjr⟩ := hbadTClassCover _ hjmem hjn
  obtain ⟨mℓ, hmℓ⟩ := hℓ
  have hl : bitmask ℓ ∈ hbadTImage := by
    rw [hmℓ, bitmask_add, hbadT_bitmask_t]
    exact hbadTImage_cover _ (bitmask_lt mℓ)
  obtain ⟨m₁, hm₁⟩ := hj₁
  have hfix₁ : ((rhoA tA : GL8) : Mat8) *ᵥ
        (((rhoA tA : GL8) : Mat8) *ᵥ m₁ + m₁) =
      ((rhoA tA : GL8) : Mat8) *ᵥ m₁ + m₁ :=
    hbadT_add_self_fixed m₁
  have hj1T : ((rhoA tA : GL8) : Mat8) *ᵥ j₁ = j₁ := by
    rw [hm₁, Matrix.mulVec_add, hj, hfix₁]
  have hj1class : bitmask j₁ ∈ hbadTImage.map (fun r => j0 ^^^ r) := by
    have hs : bapply bT (bitmask m₁) ^^^ bitmask m₁ ∈ hbadTImage :=
      hbadTImage_cover _ (bitmask_lt m₁)
    obtain ⟨r', hr', hxor⟩ :=
      hbadTClassCover_mul j0 hj0 r hr (bapply bT (bitmask m₁) ^^^ bitmask m₁) hs
    refine List.mem_map.2 ⟨r', hr', ?_⟩
    have hb1 : bitmask j₁ = (j0 ^^^ r) ^^^ (bapply bT (bitmask m₁) ^^^ bitmask m₁) := by
      rw [hm₁, bitmask_add, bitmask_add, hbadT_bitmask_t, hjr]
    rw [hb1, hxor]
  exact hbadT_filter_bound hj0 hr hjr hl hj1class

end CFSG.RankThree.GF2n.Parrott
