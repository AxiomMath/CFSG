module

public import CFSG.RankThree.GF2n.Parrott.SpinStabW0Checks
public import CFSG.RankThree.GF2n.Parrott.SpinTFacts

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

theorem bitmask_spinSingBase : bitmask spinSingBase = 2 := by
  decide +kernel

theorem q_spinSingBase : q spinSingBase = 0 := by
  rw [q_eq_zero_iff, bitmask_spinSingBase]
  decide +kernel

theorem spinSingBase_ne_zero : spinSingBase ≠ 0 := by
  intro h
  have := congrFun h 1
  simp [spinSingBase, basis] at this

private theorem stabMats_nodup : stabMats.Nodup := by
  have hpair := List.isChain_iff_pairwise.1 stabKey_chain
  exact List.Nodup.of_map stabKey (hpair.imp ne_of_lt)

private theorem stabMats_toFinset_card : stabMats.toFinset.card = 384 := by
  rw [List.toFinset_card_of_nodup stabMats_nodup, stabMats_length]

section Spin

theorem exists_rhoA_mulVec_eq_spinSingBase (w : V) (hw : w ≠ 0) (hq : q w = 0) :
    ∃ a : A45, ((rhoA a : GL8) : Mat8) *ᵥ w = spinSingBase := by
  obtain ⟨a, ha⟩ := spinSingular_transitive spinSingBase w spinSingBase_ne_zero hw q_spinSingBase hq
  refine ⟨a⁻¹, ?_⟩
  calc ((rhoA a⁻¹ : GL8) : Mat8) *ᵥ w
      = ((rhoA a⁻¹ : GL8) : Mat8) *ᵥ (((rhoA a : GL8) : Mat8) *ᵥ spinSingBase) := by rw [ha]
    _ = spinSingBase := rhoA_mulVec_inv a spinSingBase

theorem exists_mem_spinStab_of_mem_stabMats {M : B8} (hM : M ∈ stabMats) :
    ∃ a ∈ spinStab spinSingBase, colsOf ((rhoA a : GL8) : Mat8) = M := by
  have hM0 : M ∈ stabMats := hM
  rw [← stabMats_eq] at hM
  obtain ⟨w, -, hw⟩ := List.mem_map.1 hM
  refine ⟨evalSpinWord spinGenA (toW w), ?_, ?_⟩
  · apply mem_spinStab_iff.2
    apply (spinFixes_iff _ _).2
    rw [colsOf_spinMat_word, hw, bitmask_spinSingBase]
    exact stabMats_fix M hM0
  · exact (colsOf_spinMat_word (toW w)).trans hw

private noncomputable def stabMap (a : spinStab spinSingBase) : B8 :=
  colsOf ((rhoA (a : A45) : GL8) : Mat8)

private theorem card_spinStab_spinSingBase_le : Nat.card (spinStab spinSingBase) ≤ 384 := by
  let rep : Fin orbWords.length → A45 := fun i =>
    evalSpinWord spinGenA (toW (orbWords.get i))
  let g : List Nat → Nat := fun w => bapply (evalB b3 (toW w)) w0m
  have hmap_nodup : (orbWords.map g).Nodup := by
    have h : orbWords.map g = singList := orbWords_eq
    rw [h]
    exact (List.isChain_iff_pairwise.1 singList_chain).imp ne_of_lt
  have hrep : ∀ i : Fin orbWords.length,
      bitmask (((rhoA (rep i) : GL8) : Mat8) *ᵥ spinSingBase) =
        (orbWords.map g)[i.1]'(by simp) := by
    intro i
    change bitmask (((rhoA (evalSpinWord spinGenA (toW (orbWords.get i))) : GL8) : Mat8) *ᵥ
      spinSingBase) = (orbWords.map g)[i.1]'(by simp)
    rw [bitmask_rhoA_mulVec_word, bitmask_spinSingBase]
    change bapply (evalB b3 (toW (orbWords.get i))) w0m =
      (orbWords.map g)[i.1]'(by simp)
    rw [List.getElem_map]
    rfl
  have hinj : Function.Injective (fun p : Fin orbWords.length × spinStab spinSingBase =>
      rep p.1 * (p.2 : A45)) := by
    intro p q hpq
    change rep p.1 * (p.2 : A45) = rep q.1 * (q.2 : A45) at hpq
    have hbm := congrArg (fun a : A45 =>
      bitmask (((rhoA a : GL8) : Mat8) *ᵥ spinSingBase)) hpq
    simp only [rhoA_mulVec_mul] at hbm
    rw [show ((rhoA (p.2 : A45) : GL8) : Mat8) *ᵥ spinSingBase = spinSingBase from p.2.2,
      show ((rhoA (q.2 : A45) : GL8) : Mat8) *ᵥ spinSingBase = spinSingBase from q.2.2,
      hrep p.1, hrep q.1] at hbm
    have hij : p.1 = q.1 := Fin.ext ((List.Nodup.getElem_inj_iff hmap_nodup).1 hbm)
    have hs : (p.2 : A45) = (q.2 : A45) := by
      rw [hij] at hpq
      exact mul_left_cancel hpq
    exact Prod.ext hij (Subtype.ext hs)
  have hcard := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod, Nat.card_fin, card_A45, orbWords_length] at hcard
  omega

theorem card_spinStab_spinSingBase : Nat.card (spinStab spinSingBase) = 384 := by
  have hle : 384 ≤ Nat.card (spinStab spinSingBase) := by
    have hsub : (stabMats.toFinset : Set B8) ⊆ stabMap '' Set.univ := by
      intro M hM
      obtain ⟨a, ha, hMa⟩ := exists_mem_spinStab_of_mem_stabMats (List.mem_toFinset.1 hM)
      exact (Set.mem_image stabMap Set.univ M).2 ⟨⟨a, ha⟩, Set.mem_univ _, hMa⟩
    have himg : (stabMap '' Set.univ : Set B8).ncard ≤ Nat.card (spinStab spinSingBase) := by
      calc (stabMap '' Set.univ : Set B8).ncard ≤ (Set.univ : Set (spinStab spinSingBase)).ncard :=
            Set.ncard_image_le (s := Set.univ) (f := stabMap)
        _ = Nat.card (spinStab spinSingBase) := Set.ncard_univ _
    have hcard : (stabMats.toFinset : Set B8).ncard ≤ (stabMap '' Set.univ : Set B8).ncard :=
      Set.ncard_le_ncard hsub
    rw [Set.ncard_coe_finset, stabMats_toFinset_card] at hcard
    omega
  have hupp : Nat.card (spinStab spinSingBase) ≤ 384 := card_spinStab_spinSingBase_le
  omega

private theorem image_stabMap :
    (stabMap '' Set.univ : Set B8) = (stabMats.toFinset : Set B8) := by
  have hsub : (stabMats.toFinset : Set B8) ⊆ stabMap '' Set.univ := by
    intro M hM
    obtain ⟨a, ha, hMa⟩ := exists_mem_spinStab_of_mem_stabMats (List.mem_toFinset.1 hM)
    exact (Set.mem_image stabMap Set.univ M).2 ⟨⟨a, ha⟩, Set.mem_univ _, hMa⟩
  refine (Set.eq_of_subset_of_ncard_le hsub ?_).symm
  rw [Set.ncard_coe_finset, stabMats_toFinset_card]
  calc (stabMap '' Set.univ : Set B8).ncard ≤ (Set.univ : Set (spinStab spinSingBase)).ncard :=
        Set.ncard_image_le (s := Set.univ) (f := stabMap)
    _ = Nat.card (spinStab spinSingBase) := Set.ncard_univ _
    _ ≤ 384 := card_spinStab_spinSingBase_le

private theorem stabMap_injective : Function.Injective stabMap := by
  have h1 : (stabMap '' Set.univ).ncard = (Set.univ : Set (spinStab spinSingBase)).ncard := by
    rw [image_stabMap, Set.ncard_coe_finset, stabMats_toFinset_card, Set.ncard_univ,
      card_spinStab_spinSingBase]
  exact Set.injOn_univ.mp (Set.injOn_of_ncard_image_eq h1)

theorem colsOf_mem_stabMats {a : A45} (ha : a ∈ spinStab spinSingBase) :
    colsOf ((rhoA a : GL8) : Mat8) ∈ stabMats := by
  have hmem : colsOf ((rhoA a : GL8) : Mat8) ∈ (stabMap '' Set.univ : Set B8) :=
    (Set.mem_image stabMap Set.univ _).2 ⟨⟨a, ha⟩, Set.mem_univ _, rfl⟩
  rw [image_stabMap] at hmem
  exact List.mem_toFinset.1 hmem

theorem rhoA_injective : Function.Injective (rhoA : A45 →* GL8) := by
  intro a b hab
  let c : A45 := a * b⁻¹
  have hc : rhoA c = 1 := by
    dsimp [c]
    rw [map_mul, hab, map_inv]
    simp
  have hcS : c ∈ spinStab spinSingBase := by
    rw [mem_spinStab_iff]
    show ((rhoA c : GL8) : Mat8) *ᵥ spinSingBase = spinSingBase
    rw [hc]
    simp
  have hmap : stabMap ⟨c, hcS⟩ = stabMap ⟨1, (spinStab spinSingBase).one_mem⟩ := by
    unfold stabMap
    rw [show ((rhoA c : GL8) : Mat8) = 1 by rw [hc]; rfl]
    simp [colsOf_one]
  have hc1 : c = 1 := congrArg Subtype.val (stabMap_injective hmap)
  calc a = a * b⁻¹ * b := by group
    _ = 1 * b := by rw [show a * b⁻¹ = 1 from hc1]
    _ = b := one_mul b

theorem eq_one_of_fixes_perp_spinSingBase {a : A45} (ha : a ∈ spinStab spinSingBase)
    (h : ∀ v : V, b v spinSingBase = 0 → ((rhoA a : GL8) : Mat8) *ᵥ v = v) : a = 1 := by
  have hM : colsOf ((rhoA a : GL8) : Mat8) ∈ stabMats := colsOf_mem_stabMats ha
  have hfix : ∀ m ∈ perpList, bapply (colsOf ((rhoA a : GL8) : Mat8)) m = m := by
    intro m hm
    have hm256 : m < 256 := perpList_lt m hm
    have hmq : bq m w0m = 0 := beq_iff_eq.1 (List.mem_filter.1 hm).2
    have hbv : b (vecOfNat m) spinSingBase = 0 := by
      rw [b_eq_zero_iff, bitmask_vecOfNat m hm256, bitmask_spinSingBase]
      simpa [w0m] using hmq
    have hav := h (vecOfNat m) hbv
    calc bapply (colsOf ((rhoA a : GL8) : Mat8)) m
        = bapply (colsOf ((rhoA a : GL8) : Mat8)) (bitmask (vecOfNat m)) := by
          rw [bitmask_vecOfNat m hm256]
      _ = bitmask (((rhoA a : GL8) : Mat8) *ᵥ vecOfNat m) := by rw [bapply_colsOf]
      _ = bitmask (vecOfNat m) := by rw [hav]
      _ = m := bitmask_vecOfNat m hm256
  have hbone : colsOf ((rhoA a : GL8) : Mat8) = bone := fin5 _ hM hfix
  have hmap : stabMap ⟨a, ha⟩ = stabMap ⟨1, (spinStab spinSingBase).one_mem⟩ := by
    unfold stabMap
    rw [hbone]
    simp [colsOf_one]
  exact congrArg Subtype.val (stabMap_injective hmap)

end Spin

theorem eq_zero_or_eq_spinSingBase_of_perp (v : V)
    (h : ∀ w : V, b w spinSingBase = 0 → b v w = 0) : v = 0 ∨ v = spinSingBase := by
  have hm : bitmask v ∈ List.range 256 := List.mem_range.2 (bitmask_lt v)
  have hbq : ∀ n ∈ perpList, bq (bitmask v) n = 0 := by
    intro n hn
    have hn256 : n < 256 := perpList_lt n hn
    have hnq : bq n w0m = 0 := beq_iff_eq.1 (List.mem_filter.1 hn).2
    have hb : b (vecOfNat n) spinSingBase = 0 := by
      rw [b_eq_zero_iff, bitmask_vecOfNat n hn256, bitmask_spinSingBase]
      simpa [w0m] using hnq
    have hbn : b v (vecOfNat n) = 0 := h _ hb
    rwa [b_eq_zero_iff, bitmask_vecOfNat n hn256] at hbn
  rcases fin6 (bitmask v) hm hbq with h0 | h2
  · left
    exact bitmask_injective (by rw [h0, bitmask_zero])
  · right
    exact bitmask_injective (by rw [h2, bitmask_spinSingBase]; rfl)

theorem exists_b_spinSingBase_ne_zero : ∃ v : V, b v spinSingBase ≠ 0 := by
  obtain ⟨m, hm, hne⟩ := nondeg
  refine ⟨vecOfNat m, ?_⟩
  intro h0
  apply hne
  have hm256 : m < 256 := List.mem_range.1 hm
  have hbq : bq m w0m = 0 := by
    have := (b_eq_zero_iff (vecOfNat m) spinSingBase).1 h0
    rw [bitmask_vecOfNat m hm256, bitmask_spinSingBase] at this
    simpa [w0m] using this
  exact hbq

section Main

theorem false_of_spinStab_config (W : Set V) (ℬ : Set Mat8)
    (hW0 : (0 : V) ∈ W) (hWadd : ∀ v ∈ W, ∀ w ∈ W, v + w ∈ W) (hw₀ : spinSingBase ∈ W)
    (hWq : ∀ v ∈ W, q v = 0)
    (hWinv : ∀ a ∈ spinStab spinSingBase, ∀ v ∈ W, ((rhoA a : GL8) : Mat8) *ᵥ v ∈ W)
    (hℬ : ∀ σ ∈ ℬ, ∃ a ∈ spinStab spinSingBase, σ = ((rhoA a : GL8) : Mat8))
    (hℬ1 : (1 : Mat8) ∈ ℬ) (hℬmul : ∀ σ ∈ ℬ, ∀ σ' ∈ ℬ, σ * σ' ∈ ℬ)
    (hℬnorm : ∀ a ∈ spinStab spinSingBase, ∀ σ ∈ ℬ,
      ((rhoA a : GL8) : Mat8) * σ * ((rhoA a⁻¹ : GL8) : Mat8) ∈ ℬ)
    (hperp : ∀ σ ∈ ℬ, ∀ v : V, b v spinSingBase = 0 → σ *ᵥ v + v ∈ W)
    (hflag : ∀ σ ∈ ℬ, ∀ v ∈ W, σ *ᵥ v + v = 0 ∨ σ *ᵥ v + v = spinSingBase)
    (hcard : ℬ.ncard * W.ncard = 128)
    (hfaith : (∀ v : V, (∀ w ∈ W, b v w = 0) → v ∈ W) →
      ∀ σ ∈ ℬ, (∀ v ∈ W, σ *ᵥ v = v) → σ = 1) :
    False := by
  classical
  obtain ⟨tauA, htauS, htauCols⟩ := exists_mem_spinStab_of_mem_stabMats
    (p4Mats_sub tauMat tau_mem)
  let Tau : Mat8 := ((rhoA tauA : GL8) : Mat8)
  have hTauCols : colsOf Tau = tauMat := htauCols
  have hTauNe : Tau ≠ 1 := by
    intro h
    apply tau_ne_one
    rw [← hTauCols, h, colsOf_one]
  have hTauSq : Tau * Tau = 1 := by
    apply colsOf_injective
    rw [colsOf_mul, hTauCols, tau_sq, colsOf_one]
  obtain ⟨gA, hgS, hgCols⟩ := exists_mem_spinStab_of_mem_stabMats g_mem
  let G : Mat8 := ((rhoA gA : GL8) : Mat8)
  have hGCols : colsOf G = gMat := hgCols
  obtain ⟨xA, hxS, hxCols⟩ := exists_mem_spinStab_of_mem_stabMats
    (p4Mats_sub xMat x_mem)
  let X : Mat8 := ((rhoA xA : GL8) : Mat8)
  have hXCols : colsOf X = xMat := hxCols
  let P4set : Set Mat8 := {A | colsOf A ∈ p4Mats}
  have hP4card : P4set.ncard = 16 := by
    have himg : colsOf '' P4set = (p4Mats.toFinset : Set B8) := by
      ext M
      constructor
      · rintro ⟨A, hA, rfl⟩
        exact List.mem_toFinset.2 hA
      · intro hM
        have hMstab : M ∈ stabMats := p4Mats_sub M (List.mem_toFinset.1 hM)
        obtain ⟨a, haS, hMc⟩ := exists_mem_spinStab_of_mem_stabMats hMstab
        refine ⟨((rhoA a : GL8) : Mat8), ?_, hMc⟩
        change colsOf ((rhoA a : GL8) : Mat8) ∈ p4Mats
        rw [hMc]
        exact List.mem_toFinset.1 hM
    calc P4set.ncard = (colsOf '' P4set).ncard :=
          (Set.ncard_image_of_injective _ colsOf_injective).symm
      _ = (p4Mats.toFinset : Set B8).ncard := by rw [himg]
      _ = p4Mats.toFinset.card := Set.ncard_coe_finset _
      _ = 16 := by rw [List.toFinset_card_of_nodup p4Mats_nodup, p4Mats_length]
  have hbe : ∀ v ∈ W, b v spinSingBase = 0 := by
    intro v hv
    have hsum : v + spinSingBase ∈ W := hWadd v hv spinSingBase hw₀
    have hq1 : q (v + spinSingBase) = 0 := hWq _ hsum
    have hqv : q v = 0 := hWq v hv
    unfold b
    rw [hq1, hqv, q_spinSingBase]
    decide
  have hWsub : ∀ v ∈ W, bitmask v ∈ w4List := by
    intro v hv
    have hqv : q v = 0 := hWq v hv
    have hbv : b v spinSingBase = 0 := hbe v hv
    have hqtab : qTab.getD (bitmask v) 0 = 0 := (q_eq_zero_iff v).1 hqv
    have hmperp : bitmask v ∈ perpList := by
      rw [perpList, List.mem_filter]
      refine ⟨List.mem_range.2 (bitmask_lt v), ?_⟩
      have hbq : bq (bitmask v) w0m = 0 := by
        have := (b_eq_zero_iff v spinSingBase).1 hbv
        simpa [bitmask_spinSingBase, w0m] using this
      simpa [beq_iff_eq] using hbq
    by_contra hnot
    obtain ⟨M, hM, hMne⟩ := fin1 (bitmask v) hmperp hqtab hnot
    obtain ⟨a, haS, hMa⟩ := exists_mem_spinStab_of_mem_stabMats hM
    have hMne' : bq (bitmask v) (bitmask (((rhoA a : GL8) : Mat8) *ᵥ v)) ≠ 0 := by
      have h := hMne
      rw [← hMa, bapply_colsOf] at h
      exact h
    have hav : ((rhoA a : GL8) : Mat8) *ᵥ v ∈ W := hWinv a haS v hv
    have hsum : v + ((rhoA a : GL8) : Mat8) *ᵥ v ∈ W := hWadd v hv _ hav
    have hq1 := hWq _ hsum
    have hqv' := hWq v hv
    have hqav := hWq _ hav
    have hb0 : b v (((rhoA a : GL8) : Mat8) *ᵥ v) = 0 := by
      unfold b
      rw [hq1, hqv', hqav]
      decide
    exact hMne' ((b_eq_zero_iff v _).1 hb0)
  let WB : Set Nat := bitmask '' W
  have hWBsub : WB ⊆ (w4List.toFinset : Set Nat) := by
    intro m hm
    obtain ⟨v, hv, rfl⟩ := (Set.mem_image bitmask W m).1 hm
    exact List.mem_toFinset.2 (hWsub v hv)
  have hWncard : WB.ncard = W.ncard :=
    Set.ncard_image_of_injective _ bitmask_injective
  by_cases hL2 : WB ⊆ (l2List.toFinset : Set Nat)
  ·
    have hWle : W.ncard ≤ 4 := by
      calc W.ncard = WB.ncard := hWncard.symm
        _ ≤ (l2List.toFinset : Set Nat).ncard := Set.ncard_le_ncard hL2
        _ = l2List.toFinset.card := Set.ncard_coe_finset _
        _ = 4 := by rw [List.toFinset_card_of_nodup l2_nodup, l2_length]
    have hBsub : ℬ ⊆ ({1, Tau} : Set Mat8) := by
      intro σ hσ
      obtain ⟨a, haS, rfl⟩ := hℬ σ hσ
      have hM : colsOf ((rhoA a : GL8) : Mat8) ∈ stabMats := colsOf_mem_stabMats haS
      have hcond : ∀ m ∈ perpList,
          (bapply (colsOf ((rhoA a : GL8) : Mat8)) m ^^^ m) ∈ l2List := by
        intro m hm
        have hm256 : m < 256 := perpList_lt m hm
        have hmq : bq m w0m = 0 := beq_iff_eq.1 (List.mem_filter.1 hm).2
        have hbv : b (vecOfNat m) spinSingBase = 0 := by
          rw [b_eq_zero_iff, bitmask_vecOfNat m hm256, bitmask_spinSingBase]
          simpa [w0m] using hmq
        have hsum : ((rhoA a : GL8) : Mat8) *ᵥ vecOfNat m + vecOfNat m ∈ W :=
          hperp _ hσ _ hbv
        have hmem : bitmask (((rhoA a : GL8) : Mat8) *ᵥ vecOfNat m + vecOfNat m) ∈
            l2List.toFinset := hL2 ⟨_, hsum, rfl⟩
        have hbm : bitmask (((rhoA a : GL8) : Mat8) *ᵥ vecOfNat m + vecOfNat m) =
            bapply (colsOf ((rhoA a : GL8) : Mat8)) m ^^^ m := by
          rw [bitmask_add, ← bapply_colsOf, bitmask_vecOfNat m hm256]
        rw [← hbm]
        exact List.mem_toFinset.1 hmem
      rcases fin3 _ hM hcond with h | h
      · exact Or.inl (colsOf_injective (h.trans colsOf_one.symm))
      · exact Or.inr (colsOf_injective (h.trans hTauCols.symm))
    have hBne : ℬ.Nonempty := ⟨1, hℬ1⟩
    have hBpos : 0 < ℬ.ncard := (Set.ncard_pos (Set.toFinite ℬ)).2 hBne
    have hBle : ℬ.ncard ≤ 2 := by
      calc ℬ.ncard ≤ ({1, Tau} : Set Mat8).ncard := Set.ncard_le_ncard hBsub
        _ = 2 := Set.ncard_pair (Ne.symm hTauNe)
    have hmul : ℬ.ncard * W.ncard ≤ 2 * 4 := Nat.mul_le_mul hBle hWle
    omega
  ·
    have hL2' : ∃ m ∈ WB, m ∉ (l2List.toFinset : Set Nat) := by
      by_contra h
      apply hL2
      intro x hx
      by_contra hx'
      exact h ⟨x, hx, hx'⟩
    clear hL2
    obtain ⟨m, hmWB, hml2⟩ := hL2'
    obtain ⟨v, hv, hbmv⟩ := (Set.mem_image bitmask W m).1 hmWB
    have hmw4 : m ∈ w4List := List.mem_toFinset.1 (hWBsub ⟨v, hv, hbmv⟩)
    obtain ⟨M1, hM1, M2, hM2, hspan⟩ := fin2 m hmw4 hml2
    obtain ⟨a1, ha1S, hcols1⟩ := exists_mem_spinStab_of_mem_stabMats hM1
    obtain ⟨a2, ha2S, hcols2⟩ := exists_mem_spinStab_of_mem_stabMats hM2
    have hW4sub : (w4List.toFinset : Set Nat) ⊆ WB := by
      intro n hn
      have hnw4 : n ∈ w4List := List.mem_toFinset.1 hn
      obtain ⟨e, he⟩ := hspan n hnw4
      have hv1W : ((rhoA a1 : GL8) : Mat8) *ᵥ v ∈ W := hWinv a1 ha1S v hv
      have hv2W : ((rhoA a2 : GL8) : Mat8) *ᵥ v ∈ W := hWinv a2 ha2S v hv
      let u : V := (if e.val % 2 = 1 then spinSingBase else 0) +
        (if e.val / 2 % 2 = 1 then v else 0) +
        (if e.val / 4 % 2 = 1 then ((rhoA a1 : GL8) : Mat8) *ᵥ v else 0) +
        (if e.val / 8 % 2 = 1 then ((rhoA a2 : GL8) : Mat8) *ᵥ v else 0)
      have hif_mem (p : Prop) [Decidable p] (x : V) (hx : x ∈ W) :
          (if p then x else 0) ∈ W := by
        by_cases hp : p <;> simp [hp, hx, hW0]
      have huW : u ∈ W := by
        have h1 := hif_mem (e.val % 2 = 1) spinSingBase hw₀
        have h2 := hif_mem (e.val / 2 % 2 = 1) v hv
        have h3 := hif_mem (e.val / 4 % 2 = 1) (((rhoA a1 : GL8) : Mat8) *ᵥ v) hv1W
        have h4 := hif_mem (e.val / 8 % 2 = 1) (((rhoA a2 : GL8) : Mat8) *ᵥ v) hv2W
        dsimp [u]
        exact hWadd _ h1 _ h2 |> fun h12 => hWadd _ h12 _ h3 |> fun h123 => hWadd _ h123 _ h4
      have hbm_ite (p : Prop) [Decidable p] (x : V) :
          bitmask (if p then x else 0) = if p then bitmask x else 0 := by
        by_cases hp : p <;> simp [hp, bitmask_zero]
      have hbm_u : bitmask u = n := by
        rw [he]
        dsimp [u]
        rw [bitmask_add, bitmask_add, bitmask_add,
          hbm_ite, hbm_ite, hbm_ite, hbm_ite, bitmask_spinSingBase,
          ← bapply_colsOf, ← bapply_colsOf, hcols1, hcols2, hbmv]
        rfl
      have hvec : vecOfNat n ∈ W := by
        have hEq : vecOfNat n = u := bitmask_injective (by
          rw [bitmask_vecOfNat n (w4_lt n hnw4), hbm_u])
        rwa [hEq]
      exact ⟨vecOfNat n, hvec, by rw [bitmask_vecOfNat n (w4_lt n hnw4)]⟩
    have hWB_eq : WB = (w4List.toFinset : Set Nat) :=
      le_antisymm hWBsub hW4sub
    have hWcard : W.ncard = 16 := by
      calc W.ncard = WB.ncard := hWncard.symm
        _ = (w4List.toFinset : Set Nat).ncard := by rw [hWB_eq]
        _ = w4List.toFinset.card := Set.ncard_coe_finset _
        _ = 16 := by rw [List.toFinset_card_of_nodup w4_nodup, w4_length]
    have hBcard : ℬ.ncard = 8 := by
      have := hcard
      rw [hWcard] at this
      omega
    have hfaith_prem : ∀ v : V, (∀ w ∈ W, b v w = 0) → v ∈ W := by
      intro v hvperp
      have hvW_of_bit : ∀ n ∈ w4List, vecOfNat n ∈ W := by
        intro n hn
        have hmem : n ∈ WB := by rw [hWB_eq]; exact List.mem_toFinset.2 hn
        obtain ⟨w, hw, hwm⟩ := (Set.mem_image bitmask W n).1 hmem
        have hEq : vecOfNat n = w := bitmask_injective (by
          rw [bitmask_vecOfNat n (w4_lt n hn), hwm])
        rwa [hEq]
      have hbq : ∀ n ∈ w4List, bq (bitmask v) n = 0 := by
        intro n hn
        have hb : b v (vecOfNat n) = 0 := hvperp _ (hvW_of_bit n hn)
        have := (b_eq_zero_iff v (vecOfNat n)).1 hb
        rwa [bitmask_vecOfNat n (w4_lt n hn)] at this
      have hmemw4 : bitmask v ∈ w4List := fin7 (bitmask v) (List.mem_range.2 (bitmask_lt v)) hbq
      have hmem : bitmask v ∈ WB := by rw [hWB_eq]; exact List.mem_toFinset.2 hmemw4
      obtain ⟨w, hw, hwm⟩ := (Set.mem_image bitmask W (bitmask v)).1 hmem
      have hEq : v = w := bitmask_injective (by rw [hwm])
      rwa [hEq]
    have hfaithW := hfaith hfaith_prem
    have hTauNotB : Tau ∉ ℬ := by
      intro hTauB
      have hfix : ∀ v ∈ W, Tau *ᵥ v = v := by
        intro v hv
        have hmw4 : bitmask v ∈ w4List := hWsub v hv
        have hbfix : bapply tauMat (bitmask v) = bitmask v := tau_fix_w4 _ hmw4
        have hb : bitmask (Tau *ᵥ v) = bitmask v := by
          rw [← bapply_colsOf, hTauCols]
          exact hbfix
        exact bitmask_injective hb
      exact hTauNe (hfaithW Tau hTauB hfix)
    have hBsubP4 : ℬ ⊆ P4set := by
      intro σ hσ
      obtain ⟨a, haS, rfl⟩ := hℬ σ hσ
      have hM : colsOf ((rhoA a : GL8) : Mat8) ∈ stabMats := colsOf_mem_stabMats haS
      have hcond1 : ∀ n ∈ perpList,
          (bapply (colsOf ((rhoA a : GL8) : Mat8)) n ^^^ n) ∈ w4List := by
        intro n hn
        have hn256 : n < 256 := perpList_lt n hn
        have hnq : bq n w0m = 0 := beq_iff_eq.1 (List.mem_filter.1 hn).2
        have hbv : b (vecOfNat n) spinSingBase = 0 := by
          rw [b_eq_zero_iff, bitmask_vecOfNat n hn256, bitmask_spinSingBase]
          simpa [w0m] using hnq
        have hsum : ((rhoA a : GL8) : Mat8) *ᵥ vecOfNat n + vecOfNat n ∈ W :=
          hperp _ hσ _ hbv
        have hbm : bitmask (((rhoA a : GL8) : Mat8) *ᵥ vecOfNat n + vecOfNat n) =
            bapply (colsOf ((rhoA a : GL8) : Mat8)) n ^^^ n := by
          rw [bitmask_add, ← bapply_colsOf, bitmask_vecOfNat n hn256]
        rw [← hbm]
        exact hWsub _ hsum
      have hcond2 : ∀ n ∈ w4List,
          (bapply (colsOf ((rhoA a : GL8) : Mat8)) n ^^^ n) = 0 ∨
            (bapply (colsOf ((rhoA a : GL8) : Mat8)) n ^^^ n) = w0m := by
        intro n hn
        have hmem : n ∈ WB := by rw [hWB_eq]; exact List.mem_toFinset.2 hn
        obtain ⟨w, hw, hwm⟩ := (Set.mem_image bitmask W n).1 hmem
        have hEq : vecOfNat n = w := bitmask_injective (by
          rw [bitmask_vecOfNat n (w4_lt n hn), hwm])
        have hnW : vecOfNat n ∈ W := by rwa [hEq]
        have hflag' := hflag _ hσ _ hnW
        have hbm : bitmask (((rhoA a : GL8) : Mat8) *ᵥ vecOfNat n + vecOfNat n) =
            bapply (colsOf ((rhoA a : GL8) : Mat8)) n ^^^ n := by
          rw [bitmask_add, ← bapply_colsOf, bitmask_vecOfNat n (w4_lt n hn)]
        rcases hflag' with h | h
        · left
          have := congrArg bitmask h
          rw [bitmask_zero] at this
          rwa [hbm] at this
        · right
          have := congrArg bitmask h
          rw [bitmask_spinSingBase] at this
          rwa [hbm] at this
      exact (p4_spec _ hM).1 ⟨hcond1, hcond2⟩
    let TB : Set Mat8 := (fun B => Tau * B) '' ℬ
    have hTBcard : TB.ncard = 8 := by
      calc TB.ncard = ℬ.ncard := by
            apply Set.ncard_image_of_injective
            intro B1 B2 h
            change Tau * B1 = Tau * B2 at h
            calc B1 = Tau * Tau * B1 := by rw [hTauSq, one_mul]
              _ = Tau * (Tau * B1) := by rw [mul_assoc]
              _ = Tau * (Tau * B2) := by rw [h]
              _ = Tau * Tau * B2 := by rw [mul_assoc]
              _ = B2 := by rw [hTauSq, one_mul]
        _ = 8 := hBcard
    have hTBsubP4 : TB ⊆ P4set := by
      rintro _ ⟨B, hB, rfl⟩
      change colsOf (Tau * B) ∈ p4Mats
      rw [colsOf_mul, hTauCols]
      exact p4_mul_tau _ (hBsubP4 hB)
    have hdisj : Disjoint ℬ TB := by
      rw [Set.disjoint_left]
      intro B hB hTB
      obtain ⟨B', hB', hEq⟩ := hTB
      have hBsq : B * B = 1 := by
        apply colsOf_injective
        rw [colsOf_mul, colsOf_one]
        exact p4_sq _ (hBsubP4 hB)
      change Tau * B' = B at hEq
      have hB'eq : B' = Tau * B := by
        calc B' = Tau * Tau * B' := by rw [hTauSq, one_mul]
          _ = Tau * (Tau * B') := by rw [mul_assoc]
          _ = Tau * B := by rw [hEq]
      have hprod : B' * B = Tau := by
        rw [hB'eq, mul_assoc, hBsq, mul_one]
      exact hTauNotB (hprod ▸ hℬmul B' hB' B hB)
    have hunion_sub : ℬ ∪ TB ⊆ P4set := Set.union_subset hBsubP4 hTBsubP4
    have hunion_card : (ℬ ∪ TB).ncard = 16 := by
      rw [Set.ncard_union_eq hdisj, hBcard, hTBcard]
    have hP4eq : P4set = ℬ ∪ TB :=
      (Set.eq_of_subset_of_ncard_le hunion_sub (by rw [hunion_card, hP4card])).symm
    have hXmemP4 : X ∈ P4set := by
      change colsOf X ∈ p4Mats
      rw [hXCols]
      exact x_mem
    have hXunion : X ∈ ℬ ∪ TB := by
      rw [← hP4eq]
      exact hXmemP4
    have hXsq : X * X = 1 := by
      apply colsOf_injective
      rw [colsOf_mul, hXCols, colsOf_one]
      exact p4_sq xMat x_mem
    have hGT : G * Tau = Tau * G := by
      apply colsOf_injective
      rw [colsOf_mul, colsOf_mul, hGCols, hTauCols]
      exact g_tau
    have hXT : X * Tau = Tau * X := by
      apply colsOf_injective
      rw [colsOf_mul, colsOf_mul, hXCols, hTauCols]
      exact p4_comm xMat x_mem tauMat tau_mem
    have hGX : G * X = X * Tau * G := by
      apply colsOf_injective
      rw [colsOf_mul, colsOf_mul, colsOf_mul, hGCols, hXCols, hTauCols]
      exact g_x
    have hGX' : gA * xA = xA * tauA * gA := by
      apply rhoA_injective
      apply Units.ext
      simpa [G, X, Tau, map_mul] using hGX
    have hGT' : gA * tauA = tauA * gA := by
      apply rhoA_injective
      apply Units.ext
      simpa [G, Tau, map_mul] using hGT
    have hTauSq' : tauA * tauA = 1 := by
      apply rhoA_injective
      apply Units.ext
      simpa [Tau, map_mul] using hTauSq
    rcases hXunion with hXB | hXTB
    ·
      have hconj : ((rhoA (gA * xA * gA⁻¹) : GL8) : Mat8) ∈ ℬ := by
        have h := hℬnorm gA hgS X hXB
        simpa [G, X, map_mul, map_inv] using h
      have hconj_eq : gA * xA * gA⁻¹ = xA * tauA := by
        calc gA * xA * gA⁻¹ = (xA * tauA * gA) * gA⁻¹ := by rw [hGX']
          _ = xA * tauA := by group
      have hxTB : X * Tau ∈ ℬ := by
        have h := hconj
        have hmat : ((rhoA (gA * xA * gA⁻¹) : GL8) : Mat8) = X * Tau := by
          rw [hconj_eq]
          simp [X, Tau, map_mul]
        rwa [hmat] at h
      have hTauB : Tau ∈ ℬ := by
        have hmul : (X * Tau) * X ∈ ℬ := hℬmul _ hxTB X hXB
        have heq : (X * Tau) * X = Tau := by
          calc (X * Tau) * X = Tau * (X * X) := by rw [hXT]; group
            _ = Tau := by rw [hXsq, mul_one]
        exact heq ▸ hmul
      exact hTauNotB hTauB
    ·
      have hXnotB : X ∉ ℬ := fun hXB => (Set.disjoint_left.1 hdisj) hXB hXTB
      obtain ⟨B, hB, hEq⟩ := hXTB
      obtain ⟨bA, hbS, hbMat⟩ := hℬ B hB
      have hXeq : ((rhoA xA : GL8) : Mat8) = Tau * B := hEq.symm
      have hxeq : xA = tauA * bA := by
        apply rhoA_injective
        apply Units.ext
        calc ((rhoA xA : GL8) : Mat8) = Tau * B := hXeq
          _ = ((rhoA tauA : GL8) : Mat8) * ((rhoA bA : GL8) : Mat8) := by rw [hbMat]
          _ = ((rhoA (tauA * bA) : GL8) : Mat8) := by rw [map_mul, Units.val_mul]
      have hXTmem : X * Tau ∈ ℬ := by
        have hBT : B * Tau = Tau * B := by
          apply colsOf_injective
          rw [colsOf_mul, colsOf_mul, hTauCols]
          exact p4_comm _ (hBsubP4 hB) tauMat tau_mem
        have heq : X * Tau = B := by
          rw [← hEq]
          calc (Tau * B) * Tau = Tau * (B * Tau) := by rw [mul_assoc]
            _ = Tau * (Tau * B) := by rw [hBT]
            _ = Tau * Tau * B := by rw [mul_assoc]
            _ = B := by rw [hTauSq, one_mul]
        rw [heq]
        exact hB
      have hconj_eq : gA * xA * tauA * gA⁻¹ = xA := by
        calc gA * xA * tauA * gA⁻¹ = (xA * tauA * gA) * tauA * gA⁻¹ := by rw [hGX']
          _ = xA * tauA * (gA * tauA) * gA⁻¹ := by group
          _ = xA * tauA * (tauA * gA) * gA⁻¹ := by rw [hGT']
          _ = xA * (tauA * tauA) * (gA * gA⁻¹) := by group
          _ = xA := by rw [hTauSq']; group
      have hconj : ((rhoA (gA * xA * tauA * gA⁻¹) : GL8) : Mat8) ∈ ℬ := by
        have h := hℬnorm gA hgS (X * Tau) hXTmem
        have hval : ((rhoA (gA * xA * tauA * gA⁻¹) : GL8) : Mat8) = X := by
          rw [hconj_eq]
        have hunit : rhoA (gA * xA * tauA * gA⁻¹) =
            rhoA gA * (rhoA xA * rhoA tauA) * rhoA gA⁻¹ := by
          rw [map_mul, map_mul, map_mul]
          group
        have hmat : ((rhoA gA : GL8) : Mat8) * (X * Tau) * ((rhoA gA⁻¹ : GL8) : Mat8) = X := by
          calc ((rhoA gA : GL8) : Mat8) * (X * Tau) * ((rhoA gA⁻¹ : GL8) : Mat8)
              = ((rhoA gA * (rhoA xA * rhoA tauA) * rhoA gA⁻¹ : GL8) : Mat8) := by
                simp [X, Tau, Units.val_mul]
            _ = ((rhoA (gA * xA * tauA * gA⁻¹) : GL8) : Mat8) := by rw [hunit]
            _ = X := hval
        rw [hval]
        rwa [hmat] at h
      have hxAB : X ∈ ℬ := by
        have h := hconj
        have hmat : ((rhoA (gA * xA * tauA * gA⁻¹) : GL8) : Mat8) = X := by
          rw [hconj_eq]
        rwa [hmat] at h
      exact hXnotB hxAB

end Main

end CFSG.RankThree.GF2n.Parrott
