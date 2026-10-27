module

public import CFSG.RankThree.PartOne.KS.LyFiveYAlg
public import CFSG.RankThree.Native.LyFiveLocal
public import CFSG.RankThree.PartOne.KS.LyFiveX

public section

namespace CFSG.RankThree.PartOne.LyFive

open CFSG.Sporadic.Ly CFSG.Sporadic.Ly.Native CFSG.Sporadic.LySchreier
  CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.He.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.RankThree.Native Subgroup
open scoped Matrix

theorem repM_lyFiveYArr :
    RepM lyFiveYArr (lyFiveVJ 0 * lyFiveVJ 1) :=
  (RepM.mul (lyMatHom_VJ 0).symm (lyMatHom_VJ 1).symm)

section Y

attribute [local instance] lyXAction

theorem card_centralizer_yJ_le
    (h3 : lyY3ClassOK = true) (h1 : lyY1ClassOK = true) :
    Nat.card (Subgroup.centralizer ({lyFiveVJ 0 * lyFiveVJ 1} : Set J)) ≤ 3750 := by
  have hfix3 := fix_of_conj_mem_lyH five_tr_y3
  have hfix1 := fix_of_conj_mem_lyH five_tr_y1
  set d3 := lyAct (evalWord seedFam y3Word) 0 with hd3
  set d1 := lyAct (evalWord seedFam y1Word) 0 with hd1
  obtain ⟨root3, T3, hroot3, hT3, hN3, hle3, hcl3⟩ := classOK_facts repM_lyFiveYArr h3
  obtain ⟨root1, T1, hroot1, hT1, hN1, hle1, -⟩ := classOK_facts repM_lyFiveYArr h1
  obtain ⟨hclo3, hsize3⟩ := hcl3 rfl
  have hpos3 : 0 < T3.1.size := by omega
  have e3 := card_centralizer_stab_eq (lyFiveVJ 0 * lyFiveVJ 1) (evalWord seedFam y3Word)
    d3 hd3.symm hfix3 hroot3 hT3 hpos3 hclo3
  have e1 := card_centralizer_stab_mul_le (lyFiveVJ 0 * lyFiveVJ 1) (evalWord seedFam y1Word)
    d1 hd1.symm hfix1 hroot1 hT1 hle1
  rw [hsize3] at e3
  have hα : Nat.card (Subgroup.centralizer ({lyFiveVJ 0 * lyFiveVJ 1} : Set J) ⊓
      MulAction.stabilizer J d3 : Subgroup J) = 3750 := by omega
  have hβ : Nat.card (Subgroup.centralizer ({lyFiveVJ 0 * lyFiveVJ 1} : Set J) ⊓
      MulAction.stabilizer J d1 : Subgroup J) ≤ 1250 := by omega
  obtain ⟨F, hlen, hFmem⟩ := fix_finset_of_conj five_conj_y ly_certificate.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨m, m', hm, hm', hm1, hmm'⟩ := card_centralizer_two_points (lyFiveVJ 0 * lyFiveVJ 1)
    d3 d1 F (fun p hp => hFmem p hp) hfix3 hfix1 hα hβ (by norm_num)
  omega

end Y

theorem hom_comm_of_injective {G N : Type*} [Group G] [Monoid N] (f : G →* N)
    (hf : Function.Injective f) (a b : G) (h : f a * f b = f b * f a) : a * b = b * a :=
  hf (by rw [map_mul, map_mul]; exact h)

theorem lyMatHom_fiveWord
    (w : List ℤ) : lyMatHom (fiveWord lyFiveAJ lyFiveBJ w) = toMat 5 111 (fiveWordArr w) := by
  rw [fiveWord_eq_fiveWordM, lyFiveAJ_inv, lyFiveBJ_inv, fiveWordM_map, map_pow, map_pow,
    lyMatHom_AJ, lyMatHom_BJ, toMat_fiveWordArr]

theorem lyMatHom_nfArr
    (c : ℕ) (e : List ℕ) :
    lyMatHom (fiveNF lyFiveXJ lyFiveVJ (c : ZMod 5) (uvec e)) = toMat 5 111 (nfArr c e) := by
  rw [lyMatHom_nf]
  simp only [nfArr, uvec, ZMod.val_natCast]

theorem lyMatHom_dEl
    (d : List ℤ × ℕ × List ℕ) :
    lyMatHom (dEl lyFiveXJ lyFiveVJ lyFiveAJ lyFiveBJ d) =
      toMat 5 111 (mulM 5 111 (fiveWordArr d.1) (nfArr d.2.1 d.2.2)) := by
  unfold dEl
  rw [map_mul, lyMatHom_fiveWord, lyMatHom_nfArr, toMat_mulM]

theorem lyYComm_facts
    (h : lyYCommOK = true) :
    (∀ d ∈ dLifts, dEl lyFiveXJ lyFiveVJ lyFiveAJ lyFiveBJ d * (lyFiveVJ 0 * lyFiveVJ 1) =
      (lyFiveVJ 0 * lyFiveVJ 1) * dEl lyFiveXJ lyFiveVJ lyFiveAJ lyFiveBJ d) ∧
    (∀ u ∈ uVecs, fiveNF lyFiveXJ lyFiveVJ 0 (uvec u) * (lyFiveVJ 0 * lyFiveVJ 1) =
      (lyFiveVJ 0 * lyFiveVJ 1) * fiveNF lyFiveXJ lyFiveVJ 0 (uvec u)) := by
  unfold lyYCommOK at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hd, hu⟩ := h
  have hY : lyMatHom (lyFiveVJ 0 * lyFiveVJ 1) = toMat 5 111 lyFiveYArr :=
    (repM_lyFiveYArr).symm
  refine ⟨fun d hdm => ?_, fun u hum => ?_⟩
  · refine hom_comm_of_injective lyMatHom lyMatHom_injective _ _ ?_
    rw [lyMatHom_dEl, hY, ← toMat_mulM, ← toMat_mulM]
    exact toMat_eq_of_beq (hd d hdm)
  · have h0 : fiveNF lyFiveXJ lyFiveVJ 0 (uvec u) =
        fiveNF lyFiveXJ lyFiveVJ ((0 : ℕ) : ZMod 5) (uvec u) := by simp
    rw [h0]
    refine hom_comm_of_injective lyMatHom lyMatHom_injective _ _ ?_
    rw [lyMatHom_nfArr, hY, ← toMat_mulM, ← toMat_mulM]
    exact toMat_eq_of_beq (hu u hum)

theorem dLifts_let : ∀ d ∈ dLifts, ∀ l ∈ d.1, l = 1 ∨ l = 2 := by decide

theorem dLifts_card : dLifts.toFinset.card = 6 := by decide

theorem dLifts_dist : ∀ d ∈ dLifts, ∀ d' ∈ dLifts,
    rhoMat lyFiveAbar lyFiveBbar d = rhoMat lyFiveAbar lyFiveBbar d' → d = d' := by
  decide +kernel

theorem dLifts_fix : ∀ d ∈ dLifts, (∀ u ∈ uVecs,
    rhoMat lyFiveAbar lyFiveBbar d *ᵥ uvec u = uvec u) → rhoMat lyFiveAbar lyFiveBbar d = 1 := by
  decide +kernel

theorem centralizer_yJ_facts
    (hcomm : lyYCommOK = true)
    (hle : Nat.card (Subgroup.centralizer ({lyFiveVJ 0 * lyFiveVJ 1} : Set J)) ≤ 3750) :
    Nat.card (Subgroup.centralizer ({lyFiveVJ 0 * lyFiveVJ 1} : Set J)) = 3750 ∧
      FiveCoreAt' (lyFiveVJ 0 * lyFiveVJ 1) := by
  obtain ⟨-, -, -, -, h5, h6, -, -, -, h10, -, -, -, -, -, -, -, -, -⟩ :=
    lyFiveMRelJ.local_structure lyFiveCertJ
  obtain ⟨φ, hφ, -, -, -, ρ, hρ, hρA, hρB, hρker, -⟩ := h10
  obtain ⟨hc1, hc2⟩ := lyYComm_facts hcomm
  have ha : lyFiveAJ ∈ Subgroup.closure ({lyFiveAJ, lyFiveBJ} : Set J) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hb : lyFiveBJ ∈ Subgroup.closure ({lyFiveAJ, lyFiveBJ} : Set J) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  exact (y_core (G := J) lyFiveQRelJ (Subgroup.closure ({lyFiveAJ, lyFiveBJ} : Set J)) ha hb h5 h6
    φ hφ ρ lyFiveAbar lyFiveBbar hρ hρA hρB hρker hc1 hc2 dLifts_let dLifts_card dLifts_dist
    dLifts_fix hle).2

theorem fiveCoreAt'_yJ
    (hcomm : lyYCommOK = true)
    (hle : Nat.card (Subgroup.centralizer ({lyFiveVJ 0 * lyFiveVJ 1} : Set J)) ≤ 3750) :
    FiveCoreAt' (lyFiveVJ 0 * lyFiveVJ 1) :=
  (centralizer_yJ_facts hcomm hle).2

theorem card_centralizer_yJ_eq
    (h3 : lyY3ClassOK = true) (h1 : lyY1ClassOK = true) (hcomm : lyYCommOK = true) :
    Nat.card (Subgroup.centralizer ({lyFiveVJ 0 * lyFiveVJ 1} : Set J)) = 3750 :=
  (centralizer_yJ_facts hcomm (card_centralizer_yJ_le h3 h1)).1

theorem fiveCoreAt'_yJ_of_checks
    (h3 : lyY3ClassOK = true) (h1 : lyY1ClassOK = true) (hcomm : lyYCommOK = true) :
    FiveCoreAt' (lyFiveVJ 0 * lyFiveVJ 1) :=
  fiveCoreAt'_yJ hcomm (card_centralizer_yJ_le h3 h1)

end CFSG.RankThree.PartOne.LyFive
