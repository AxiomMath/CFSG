module

public import Certificates.Certificate14985
public import CFSG.RankThree.PartOne.KS.HNFiveMatrix
public import CFSG.Sporadic.GLQ.HNTwoRank
public import CFSG.RankThree.PartOne.KS.HNFiveBasic

public section

namespace CFSG.RankThree.PartOne.KS.HNFive

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.Sporadic.GLQ CFSG.Monster.B.Pinned
open scoped Matrix

section Sound

variable {M V : Type} {O : Ops M V} {p d : ℕ} {Sp : OpsSpec O p d} {G : Type*} [Group G]
  {φ : G →* Matrix (Fin d) (Fin d) (ZMod p)}

theorem eq_of_toMat (hφ : Function.Injective φ) {g h : G} {X Y : M} (hX : Sp.WF X)
    (hY : Sp.WF Y) (hg : Sp.toMat X = φ g) (hh : Sp.toMat Y = φ h) (e : O.eq X Y = true) :
    g = h :=
  hφ (by rw [← hg, ← hh]; exact Sp.toMat_eq hX hY e)

theorem powOK_sound (hφ : Function.Injective φ) {g : G} {X : M × M} (hg : Rep Sp φ g X) {e : ℕ}
    (h : powOK O X.1 e = true) : g ^ e = 1 := by
  obtain ⟨hw, -, ht, -⟩ := Rep.pow hg e
  exact eq_of_toMat hφ hw Sp.one_wf ht (by rw [Sp.toMat_one, map_one]) h

theorem commOK_sound (hφ : Function.Injective φ) {g h : G} {X Y : M × M} (hg : Rep Sp φ g X)
    (hh : Rep Sp φ h Y) (hc : commOK O X.1 Y.1 = true) : g * h = h * g := by
  obtain ⟨hw1, -, ht1, -⟩ := Rep.mul hg hh
  obtain ⟨hw2, -, ht2, -⟩ := Rep.mul hh hg
  exact eq_of_toMat hφ hw1 hw2 ht1 ht2 hc

theorem neOne_sound {g : G} {X : M × M} (hg : Rep Sp φ g X) {t : ℕ}
    (h : neOne O X.1 t = true) : g ≠ 1 := by
  intro hg1
  have h1 := Sp.toVec_ne h
  apply h1
  rw [Sp.toVec_vmul (Sp.unit_wf t) hg.1, hg.2.2.1, hg1, map_one, Matrix.vecMul_one]

theorem bcomm_sound (hφ : Function.Injective φ) {g h z : G} {X Y Z : M × M} (hg : Rep Sp φ g X)
    (hh : Rep Sp φ h Y) (hz : Rep Sp φ z Z) {e : ℕ}
    (hc : O.eq (pBcomm O X Y) (O.pow Z.1 e) = true) : bcomm g h = z ^ e := by
  obtain ⟨hw1, -, ht1, -⟩ := Rep.mul (Rep.mul hg.inv hh.inv) (Rep.mul hg hh)
  obtain ⟨hw2, -, ht2, -⟩ := Rep.pow hz e
  have := eq_of_toMat hφ hw1 hw2 ht1 ht2 hc
  rw [← this, bcomm, mul_assoc, mul_assoc]

theorem ofFn_prod4 (q : Fin 4 → G) (a : Fin 4 → ℕ) :
    (List.ofFn fun j => q j ^ a j).prod =
      q 0 ^ a 0 * (q 1 ^ a 1 * (q 2 ^ a 2 * (q 3 ^ a 3 * 1))) := by
  simp [List.ofFn_succ]

theorem prodPow_sound {q : Fin 4 → G} {z : G} {Q : Fin 4 → M × M} {Z : M × M}
    (hq : ∀ j, Rep Sp φ (q j) (Q j)) (hz : Rep Sp φ z Z) (a : Fin 4 → ℕ) (c : ℕ) :
    Sp.WF (prodPow O (fun j => (Q j).1) Z.1 a c) ∧
      Sp.toMat (prodPow O (fun j => (Q j).1) Z.1 a c) =
        φ ((List.ofFn fun j => q j ^ a j).prod * z ^ c) := by
  have hr := Rep.mul (Rep.mul (Rep.pow (hq 0) (a 0)) (Rep.mul (Rep.pow (hq 1) (a 1))
    (Rep.mul (Rep.pow (hq 2) (a 2)) (Rep.mul (Rep.pow (hq 3) (a 3)) Rep.one)))) (Rep.pow hz c)
  rw [ofFn_prod4]
  exact ⟨hr.1, hr.2.2.1⟩

theorem conj_sound (hφ : Function.Injective φ) {g z : G} {q : Fin 4 → G} {X Z : M × M}
    {Q : Fin 4 → M × M} (hg : Rep Sp φ g X) (hq : ∀ j, Rep Sp φ (q j) (Q j))
    (hz : Rep Sp φ z Z) (i : Fin 4) (a : Fin 4 → ℕ) (c : ℕ)
    (hc : O.eq (pConj O X (Q i)) (prodPow O (fun j => (Q j).1) Z.1 a c) = true) :
    g⁻¹ * q i * g = (List.ofFn fun j => q j ^ a j).prod * z ^ c := by
  obtain ⟨hw1, -, ht1, -⟩ := Rep.mul (Rep.mul hg.inv (hq i)) hg
  obtain ⟨hw2, ht2⟩ := prodPow_sound hq hz a c
  have := eq_of_toMat hφ hw1 hw2 ht1 ht2 hc
  rw [← this, mul_assoc]

end Sound

theorem hnFive_check : hnFiveCheck = true :=
  Certificates.certificate14985

theorem allFin_iff {n : ℕ} {f : Fin n → Bool} : allFin n f = true ↔ ∀ i, f i = true := by
  simp [allFin, List.all_eq_true, List.mem_finRange]

section Inst

open CFSG.Sporadic.GLQ.HNTwoRank

theorem iZ_lt : iZ < hnFiveN := by decide +kernel

theorem iX_lt : iX < hnFiveN := by decide +kernel

theorem iQ_lt : ∀ j, iQ j < hnFiveN := by decide +kernel

theorem iR_lt : ∀ j, iR j < hnFiveN := by decide +kernel


@[expose] noncomputable def Rg : ℕ → GLHN := runProg (initRegs gA gB) hnFiveProg

theorem Rg_mem (r : ℕ) : Rg r ∈ J := by
  have hgA : gA ∈ J := Subgroup.subset_closure (Set.mem_insert _ _)
  have hgB : gB ∈ J := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  exact runProg_mem J hnFiveProg (initRegs_mem J hgA hgB) r

theorem hnFive_regsRep (h : hnFiveCheck = true) :
    RegsRep (specP 5 133) φ hnFiveN Rg hnFiveRegs := by
  have hprog : hnFiveProg.all (Instr.lt hnFiveN) = true := by
    simp only [hnFiveCheck, Bool.and_eq_true] at h
    exact h.1
  exact regsRep_runProg hnFiveProg hprog (regsRep_initRegs rep_gA rep_gB)

theorem hnFive_rel :
    Rel (fun j => Rg (iQ j)) (Rg iZ) (Rg iX) (fun j => Rg (iR j)) Mm XU cx BU cr := by
  have h : hnFiveCheck = true := hnFive_check
  have hrels : relsOK (opsP 5 133) hnFiveRegs = true := by
    simp only [hnFiveCheck, Bool.and_eq_true] at h
    exact h.2
  have hR : ∀ {r : ℕ}, r < hnFiveN → Rep (specP 5 133) φ (Rg r) hnFiveRegs[r]! :=
    fun hr => (hnFive_regsRep h).2 _ hr
  have hz := hR iZ_lt
  have hx := hR iX_lt
  have hq : ∀ j, Rep (specP 5 133) φ (Rg (iQ j)) hnFiveRegs[iQ j]! := fun j => hR (iQ_lt j)
  have hr : ∀ j, Rep (specP 5 133) φ (Rg (iR j)) hnFiveRegs[iR j]! := fun j => hR (iR_lt j)
  unfold relsOK at hrels
  simp only [Bool.and_eq_true, allFin_iff] at hrels
  obtain ⟨⟨⟨⟨⟨⟨⟨hz5, hzne⟩, hqpc⟩, hbc⟩, hx5⟩, hxz⟩, hxc⟩, hrr⟩ := hrels
  have hval_X : ∀ i j, ((XU : Matrix (Fin 4) (Fin 4) (ZMod 5)) i j).val = exX i j :=
    fun i j => by rw [XU_val]; exact val_exX i j
  have hval_B : ∀ j i l, ((BU j : Matrix (Fin 4) (Fin 4) (ZMod 5)) i l).val = exR j i l :=
    fun j i l => by rw [BU_val]; exact val_exR j i l
  have hbq : ∀ i j, bcomm (Rg (iQ i)) (Rg (iQ j)) = Rg iZ ^ exM i j :=
    fun i j => bcomm_sound φ_injective (hq i) (hq j) hz (hbc i j)
  have hz_eq : bcomm (Rg (iQ 0)) (Rg (iQ 1)) = Rg iZ := by
    rw [hbq 0 1]
    exact pow_one _
  refine ⟨⟨fun i => powOK_sound φ_injective (hq i) (hqpc i).1, ?_,
    fun i => commOK_sound φ_injective (hq i) hz (hqpc i).2, fun i j => ?_, Mm_isUnit_det, ?_⟩,
    hz_eq, powOK_sound φ_injective hx hx5, commOK_sound φ_injective hx hz hxz, fun i => ?_,
    fun j => commOK_sound φ_injective (hr j) hz (hrr j).1, fun j i => ?_⟩
  · have := fact5
    exact orderOf_eq_prime (powOK_sound φ_injective hz hz5) (neOne_sound hz hzne)
  · rw [hbq i j, ← val_exM i j]
  · rw [← hz_eq]
    unfold bcomm
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.inv_mem _ (Subgroup.subset_closure ⟨0, rfl⟩))
      (Subgroup.inv_mem _ (Subgroup.subset_closure ⟨1, rfl⟩))) (Subgroup.subset_closure ⟨0, rfl⟩))
      (Subgroup.subset_closure ⟨1, rfl⟩)
  · have := conj_sound φ_injective hx hq hz i (exX i) (cx i) (hxc i)
    simpa only [hval_X] using this
  · have := conj_sound φ_injective (hr j) hq hz i (exR j i) (cr j i) ((hrr j).2 i)
    simpa only [hval_B] using this

end Inst

end CFSG.RankThree.PartOne.KS.HNFive
