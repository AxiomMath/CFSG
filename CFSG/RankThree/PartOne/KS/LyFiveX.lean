module

public import CFSG.RankThree.PartOne.KS.LyFiveSound
public import CFSG.RankThree.Native.LyFiveSpec
public import CFSG.RankThree.PartOne.KS.LyFiveClass

public section

set_option maxRecDepth 100000

namespace CFSG.RankThree.PartOne.LyFive

open CFSG.Sporadic.Ly CFSG.Sporadic.Ly.Native CFSG.Sporadic.LySchreier
  CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.He.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.RankThree.Native Subgroup

theorem repM_lyFiveXArr : RepM lyFiveXArr lyFiveXJ :=
  lyMatHom_XJ.symm

section Facts

theorem fiveA_eq : Omega.fiveA = lyFiveAJ := by
  unfold Omega.fiveA lyFiveAJ
  rfl

theorem fiveB_eq : Omega.fiveB = lyFiveBJ := by
  unfold Omega.fiveB lyFiveBJ
  rfl

theorem fiveX_eq : Omega.fiveX = lyFiveXJ := by
  unfold Omega.fiveX lyFiveXJ
  rw [fiveA_eq]

theorem fiveV_eq : Omega.fiveV = lyFiveVJ := by
  funext i
  unfold Omega.fiveV lyFiveVJ
  rw [fiveA_eq, fiveB_eq]

theorem fiveY_eq : Omega.fiveY = lyFiveVJ 0 * lyFiveVJ 1 := by
  unfold Omega.fiveY
  rw [fiveV_eq]

theorem five_tr_x :
    (evalWord seedFam xWord)⁻¹ * lyFiveXJ * evalWord seedFam xWord ∈ Sporadic.LySchreier.lyH := by
  have h := ly_five_facts.1
  rwa [fiveX_eq] at h

theorem five_tr_y3 : (evalWord seedFam y3Word)⁻¹ * (lyFiveVJ 0 * lyFiveVJ 1) *
    evalWord seedFam y3Word ∈ Sporadic.LySchreier.lyH := by
  have h := ly_five_facts.2.1
  rwa [fiveY_eq] at h

theorem five_tr_y1 : (evalWord seedFam y1Word)⁻¹ * (lyFiveVJ 0 * lyFiveVJ 1) *
    evalWord seedFam y1Word ∈ Sporadic.LySchreier.lyH := by
  have h := ly_five_facts.2.2.1
  rwa [fiveY_eq] at h

theorem five_conj_x : ∃ g : J, g * Omega.lyTA * g⁻¹ = lyFiveXJ := by
  have h := ly_five_facts.2.2.2.1
  rwa [fiveX_eq] at h

theorem five_conj_y : ∃ g : J, g * Omega.lyTB * g⁻¹ = lyFiveVJ 0 * lyFiveVJ 1 := by
  have h := ly_five_facts.2.2.2.2.1
  rwa [fiveY_eq] at h

end Facts

section Fix

attribute [local instance] lyXAction

theorem fix_finset_of_conj {t w : J} {k : ℕ} (hc : ∃ g : J, g * t * g⁻¹ = w)
    (hk : Nat.card {y : MulAction.orbit J Omega.opE // t • y = y} ≤ k) :
    ∃ F : Finset (Fin 8835156), F.card ≤ k ∧ ∀ p, lyAct w p = p → p ∈ F := by
  classical
  obtain ⟨g, hg⟩ := hc
  have : Fintype (MulAction.orbit J Omega.opE) := Fintype.ofFinite _
  let S : Finset (MulAction.orbit J Omega.opE) := Finset.univ.filter fun y => t • y = y
  refine ⟨S.image fun y => ptEquiv.symm (g • y), ?_, fun p hp => ?_⟩
  · refine (Finset.card_image_le).trans ?_
    have e : S.card = Nat.card {y : MulAction.orbit J Omega.opE // t • y = y} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [e]
    exact hk
  · have hw : w • ptEquiv p = ptEquiv p := (lyAct_eq_iff w p p).1 hp
    have ht : t = g⁻¹ * w * g := by rw [← hg]; group
    refine Finset.mem_image.2 ⟨g⁻¹ • ptEquiv p, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · rw [ht, mul_smul, mul_smul, smul_inv_smul, hw]
    · rw [smul_inv_smul, Equiv.symm_apply_apply]

theorem fix_of_conj_mem_lyH
    {w τ : J} (h : τ⁻¹ * w * τ ∈ Sporadic.LySchreier.lyH) :
    lyAct w (lyAct τ 0) = lyAct τ 0 := by
  rw [← stab_zero_eq, MulAction.mem_stabilizer_iff] at h
  have e : τ • ((τ⁻¹ * w * τ) • (0 : Fin 8835156)) = τ • (0 : Fin 8835156) := by rw [h]
  rw [← mul_smul, show τ * (τ⁻¹ * w * τ) = w * τ by group, mul_smul] at e
  exact e

end Fix

section X

attribute [local instance] lyXAction

theorem card_centralizer_xJ_le
    (hB : lyXClassOK = true) :
    Nat.card (Subgroup.centralizer ({lyFiveXJ} : Set J)) ≤ 2340000 := by
  have hfix := fix_of_conj_mem_lyH five_tr_x
  set d := lyAct (evalWord seedFam xWord) 0 with hd
  obtain ⟨root, T, hroot, hT, -, hN, -⟩ := classOK_facts repM_lyFiveXArr hB
  have h1 := card_centralizer_stab_mul_le lyFiveXJ (evalWord seedFam xWord) d hd.symm hfix
    hroot hT hN
  obtain ⟨F, hFcard, hFmem⟩ := fix_finset_of_conj five_conj_x ly_certificate.2.2.2.2.2.2.2.2.2.1
  have h2 := card_centralizer_le_of_fixed lyFiveXJ d F (fun p hp => hFmem p hp) hfix
  have h3 : Nat.card (Subgroup.centralizer ({lyFiveXJ} : Set J) ⊓
      MulAction.stabilizer J d : Subgroup J) ≤ 15000 := by
    have : Nat.card (Subgroup.centralizer ({lyFiveXJ} : Set J) ⊓
        MulAction.stabilizer J d : Subgroup J) * 390600 ≤ 5859000000 := h1
    omega
  calc Nat.card (Subgroup.centralizer ({lyFiveXJ} : Set J)) ≤
      F.card * Nat.card (Subgroup.centralizer ({lyFiveXJ} : Set J) ⊓
        MulAction.stabilizer J d : Subgroup J) := h2
    _ ≤ 156 * 15000 := Nat.mul_le_mul hFcard h3

end X

end CFSG.RankThree.PartOne.LyFive
