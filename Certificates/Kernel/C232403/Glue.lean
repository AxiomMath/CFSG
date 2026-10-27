module

public import Certificates.Kernel.C232403.Checks
public import Certificates.Kernel.LocalComp.WittCount
public import Certificates.Kernel.LocalComp.WittWords
public import Certificates.Kernel.Item434.M22Facts
public import CFSG.Certificates.Kernel.Item434.PkSound
public import CFSG.Certificates.Kernel.WittBadSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases

public section

namespace CertificateChecks.KernelC232403

open Equiv CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K CFSG.KC.WCnt
open CFSG.KC.Item434 CFSG.KS.PCnt CFSG.ComponentClassification.WittDesign
open CertificateChecks.KernelItem434 CertificateChecks.KernelLC.Witt
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2324Q CFSG.Monster.B.Co2.Native
open CFSG.RankThree.PartTwo.Sec4.Item434SporGen

theorem pkV {k : ℕ} (hk : k < 6) : Pk 22 5 (m22VArr k) (vK k) := by
  have h := k232403v k hk
  simp only [vOK, Bool.and_eq_true] at h
  exact ⟨arrBind_sound h.1.1.1, h.1.1.2⟩

theorem pkE {j : ℕ} (hj : j < 3) : Pk 22 5 (m22EArr j) (eK j) := by
  have h := k232403e
  simp only [Bool.and_eq_true] at h
  interval_cases j
  · rw [Nat.eq_of_beq_eq_true h.1.1.1.1.1.2]
    exact ⟨arrBind_sound m22E1B, m22PP.1⟩
  · rw [Nat.eq_of_beq_eq_true h.1.1.1.1.2]
    exact ⟨arrBind_sound m22E2B, m22PP.2⟩
  · exact ⟨arrBind_sound h.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2⟩

theorem elt : m22VEltCheck = true := by
  have h := k232403e
  simp only [Bool.and_eq_true] at h
  have p1 : Pk 22 5 m22E1 (M22E 2) := ⟨arrBind_sound m22E1B, m22PP.1⟩
  have p2 : Pk 22 5 m22E2 (M22E 3) := ⟨arrBind_sound m22E2B, m22PP.2⟩
  have p12 : Pk 22 5 m22E12 (eK 2) := pkE (j := 2) (by norm_num)
  unfold m22VEltCheck
  simp only [Bool.and_eq_true]
  refine ⟨⟨?_, CFSG.Monster.B.Co2.allLt_iff.2 fun k hk => ?_⟩,
    CFSG.Monster.B.Co2.allLt_iff.2 fun j hj => ?_⟩
  · rw [eqA_pk m22W (pk_comp m22W p1 p2) p12]
    exact h.1.1.1.2
  · have pk := pkV hk
    have hv := k232403v k hk
    simp only [vOK, Bool.and_eq_true] at hv
    simp only [Bool.and_eq_true]
    refine ⟨⟨isInvA_pk pk, m22SiftP pk.1 hv.1.2⟩, ?_⟩
    rw [eqA_pk m22W (pk_comp m22W pk pk) (pk_id m22W)]
    exact hv.2
  · have hr : eRel j = true := by
      interval_cases j
      exacts [h.1.1.2, h.1.2, h.2]
    simp only [eRel, Bool.and_eq_true] at hr
    have q0 := pkV (k := 2 * j) (by omega)
    have q1 := pkV (k := 2 * j + 1) (by omega)
    have qe := pkE hj
    simp only [Bool.and_eq_true]
    rw [eqA_pk m22W qe (pk_id m22W), eqA_pk m22W (pk_comp m22W q0 q1) (pk_comp m22W q1 q0),
      eqA_pk m22W (pk_comp m22W q0 qe) (pk_comp m22W qe q0),
      eqA_pk m22W (pk_comp m22W q1 qe) (pk_comp m22W qe q1)]
    exact hr.1

theorem pk_prod : ∀ w : List ℕ, (∀ k ∈ w, k < 6) → Pk 22 5 (m22VProd w) (prodV w)
  | [], _ => by
    rw [m22VProd]
    exact pk_id m22W
  | k :: w, h => by
    rw [m22VProd]
    exact pk_comp m22W (pkV (h k List.mem_cons_self))
      (pk_prod w fun i hi => h i (List.mem_cons_of_mem _ hi))

theorem gen : m22VGenCheck = true := by
  have hw : ∀ k ∈ m22VWordA ++ m22VWordB, k < 6 := by decide
  have h := k232403g
  simp only [Bool.and_eq_true] at h
  unfold m22VGenCheck
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  refine ⟨⟨hw, ?_⟩, ?_⟩
  · rw [eqA_pk m22W (pk_prod _ fun k hk => hw k (List.mem_append_left _ hk))
      ⟨arrBind_sound m22AB, h.1.1.1⟩]
    exact h.1.2
  · rw [eqA_pk m22W (pk_prod _ fun k hk => hw k (List.mem_append_right _ hk))
      ⟨arrBind_sound m22BB, h.1.1.2⟩]
    exact h.2

theorem intertw_iff (g u w : Fin 22 → Fin 22) :
    m22Intertw g u w = true ↔ ∀ x, g (u x) = w (g x) := by
  simp [m22Intertw, List.all_eq_true, List.mem_finRange]

theorem conjIn_iff (g u v v' v'' : Fin 22 → Fin 22) :
    m22ConjIn g u v v' v'' = true ↔ ∃ j : Fin 3, ∀ x, g (u x) = ![v, v', v''] j (g x) := by
  rw [m22ConjIn, Bool.or_eq_true, Bool.or_eq_true, intertw_iff, intertw_iff, intertw_iff]
  constructor
  · rintro ((h | h) | h)
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]
  · rintro ⟨j, h⟩
    fin_cases j
    exacts [Or.inl (Or.inl h), Or.inl (Or.inr h), Or.inr h]

theorem fn_comp (t u : Array ℕ) (hu : ∀ i : Fin 22, u[i.val]! < 22) (i : Fin 22) :
    m22Fn (compA 22 t u) i = m22Fn t (m22Fn u i) := by
  have h : (compA 22 t u)[i.val]! = t[u[i.val]!]! := by
    rw [compA, getElem!_pos (Array.ofFn _) i.val (by simp)]
    simp
  apply Fin.ext
  simp only [m22Fn, Nat.mod_eq_of_lt (hu i)]
  rw [h]

@[expose] def tgt (j : ℕ) : Fin 3 → Fin 22 → Fin 22 :=
  ![m22Fn (m22VArr (2 * j)), m22Fn (m22VArr (2 * j + 1)),
    m22Fn (compA 22 (m22VArr (2 * j)) (m22VArr (2 * j + 1)))]

theorem badB_iff (j : ℕ) (τ : Fin 22 → Fin 22) : m22BadB j τ = true ↔
    (∀ x, τ (m22Fn (m22EArr j) x) = m22Fn (m22EArr j) (τ x)) ∧
      ¬((∃ i : Fin 3, ∀ x, τ (m22Fn (m22VArr (2 * j)) x) = tgt j i (τ x)) ∧
        ∃ i : Fin 3, ∀ x, τ (m22Fn (m22VArr (2 * j + 1)) x) = tgt j i (τ x)) := by
  have h1 := intertw_iff τ (m22Fn (m22EArr j)) (m22Fn (m22EArr j))
  have h2 := conjIn_iff τ (m22Fn (m22VArr (2 * j))) (m22Fn (m22VArr (2 * j)))
    (m22Fn (m22VArr (2 * j + 1))) (m22Fn (compA 22 (m22VArr (2 * j)) (m22VArr (2 * j + 1))))
  have h3 := conjIn_iff τ (m22Fn (m22VArr (2 * j + 1))) (m22Fn (m22VArr (2 * j)))
    (m22Fn (m22VArr (2 * j + 1))) (m22Fn (compA 22 (m22VArr (2 * j)) (m22VArr (2 * j + 1))))
  rw [m22BadB, m22NormB]
  cases a : m22Intertw τ (m22Fn (m22EArr j)) (m22Fn (m22EArr j)) <;>
    cases b : m22ConjIn τ (m22Fn (m22VArr (2 * j))) (m22Fn (m22VArr (2 * j)))
      (m22Fn (m22VArr (2 * j + 1))) (m22Fn (compA 22 (m22VArr (2 * j)) (m22VArr (2 * j + 1)))) <;>
    cases c : m22ConjIn τ (m22Fn (m22VArr (2 * j + 1))) (m22Fn (m22VArr (2 * j)))
      (m22Fn (m22VArr (2 * j + 1))) (m22Fn (compA 22 (m22VArr (2 * j)) (m22VArr (2 * j + 1)))) <;>
    rw [a] at h1 <;> rw [b] at h2 <;> rw [c] at h3 <;> simp_all [tgt]

theorem hb (j : ℕ) (hj : j < 3) (τ : Perm (Fin 22)) :
    badT (eK j) (vK (2 * j)) (vK (2 * j + 1)) [vK (2 * j), vK (2 * j + 1), wK j] (pkw 5 τ) =
      decide (m22BadB j ⇑τ = true) := by
  have h0 := k232403ptV ⟨2 * j, by omega⟩
  have h1 := k232403ptV ⟨2 * j + 1, by omega⟩
  have hP : ∀ i : Fin 3, ∀ x : Fin 22,
      pt ([vK (2 * j), vK (2 * j + 1), wK j].getD i.val 0) x.val = (tgt j i x).val := by
    intro i x
    fin_cases i
    · exact h0 x
    · exact h1 x
    · change pt (wK j) x.val = (m22Fn (compA 22 (m22VArr (2 * j)) (m22VArr (2 * j + 1))) x).val
      rw [k232403ptW ⟨j, hj⟩ x, h1 x, h0, fn_comp _ _ (k232403entries ⟨2 * j + 1, by omega⟩)]
  rw [Bool.eq_iff_iff, decide_eq_true_iff,
    badT_pkw_iff τ _ _ _ (tgt j) _ _ _ _ rfl (k232403ptE ⟨j, hj⟩) h0 h1 hP, badB_iff]

theorem cov (e : Fin 22 → Fin 22) (E F D : ℕ) (d : Perm (Fin 22)) (hd : pkw 5 d = D)
    (x0 x1 p : Fin 22) (hE : ∀ i : Fin 22, pt E i.val = (e i).val)
    (hF1 : ∀ y : Fin 22, inM F y.val = true → e y = y)
    (hF2 : ∀ y : Fin 22, e y = y → inM F y.val = true) (hx1 : e x0 = x1) (hx0 : e x0 ≠ x0)
    (hp : e p = p) (h0 : pt D x0.val = 0) (h1 : pt D x1.val = 1) (h2 : pt D p.val = 2)
    (σ : Perm (Fin 22)) (hc : ∀ x, (σ * d) (e x) = e ((σ * d) x)) :
    bIf(inM F (σ 0).val, false, true) = true ∧ Nat.beq (σ 1).val (pt E (σ 0).val) = true ∧
      inM F (σ 2).val = true := by
  have a0 : (σ * d) x0 = σ 0 := mul_apply_of_pk hd σ (i := 0) h0
  have a1 : (σ * d) x1 = σ 1 := mul_apply_of_pk hd σ (i := 1) h1
  have a2 : (σ * d) p = σ 2 := mul_apply_of_pk hd σ (i := 2) h2
  refine ⟨?_, ?_, ?_⟩
  · cases hm : inM F (σ 0).val
    · rfl
    · exfalso
      have hfix := hF1 _ hm
      have h := hc x0
      rw [a0, hfix, ← a0] at h
      exact hx0 ((σ * d).injective h)
  · have h := hc x0
    rw [hx1, a1, a0] at h
    rw [h, hE]
    exact Nat.beq_refl _
  · apply hF2
    have h := hc p
    rw [hp, a2] at h
    exact h.symm

theorem pkT {j : ℕ} (hj : j < 3) : pkw 5 (CertificateChecks.KernelLC.wordPerm (tK j)) = dK j := by
  interval_cases j
  · exact Nat.eq_of_beq_eq_true (by quickRfl)
  · exact Nat.eq_of_beq_eq_true (by quickRfl)
  · exact Nat.eq_of_beq_eq_true (by quickRfl)

theorem counts {j : ℕ} (hj : j < 3) :
    m22Count (fun g => m22BadB j g = true) = 0 := by
  have hc : cntK j = 0 := by
    interval_cases j
    exacts [Nat.eq_of_beq_eq_true k232403c0, Nat.eq_of_beq_eq_true k232403c1,
      Nat.eq_of_beq_eq_true k232403c2]
  unfold cntK cntW at hc
  have hpts := k232403pts ⟨j, hj⟩
  have hE := k232403ptE ⟨j, hj⟩
  have hfx := k232403fix ⟨j, hj⟩
  refine (m22Count_eq_wcB _ _ (hb j hj) _ (CertificateChecks.KernelLC.wordPerm_mem _) _ (pkT hj)
    (fun x => bIf(inM (fK j) x, false, true)) (fun x0 x1 => Nat.beq x1 (pt (eK j) x0))
    (fun _ _ x2 => inM (fK j) x2) fun σ h => ?_).trans hc
  have h' : m22BadB j ⇑(σ * CertificateChecks.KernelLC.wordPerm (tK j)) = true := h
  have hcm := ((badB_iff j ⇑(σ * CertificateChecks.KernelLC.wordPerm (tK j))).1 h').1
  exact cov (m22Fn (m22EArr j)) (eK j) (fK j) (dK j) _ (pkT hj) ⟨_, hpts.1⟩ ⟨_, hpts.2.1⟩
    ⟨_, hpts.2.2.1⟩ hE (fun y hy => Fin.ext ((hE y).symm.trans ((hfx y).1 hy)))
    (fun y hy => (hfx y).2 ((hE y).trans (congrArg Fin.val hy)))
    (Fin.ext ((hE _).symm.trans hpts.2.2.2.1))
    (fun hh => hpts.2.2.2.2.1 ((hE _).trans (congrArg Fin.val hh)))
    (Fin.ext ((hE _).symm.trans hpts.2.2.2.2.2.1)) hpts.2.2.2.2.2.2.1 hpts.2.2.2.2.2.2.2.1
    hpts.2.2.2.2.2.2.2.2 σ hcm

theorem facts232403 :
    m22VEltCheck = true ∧ m22Count (fun g => m22BadB 0 g = true) = 0 ∧
      m22Count (fun g => m22BadB 1 g = true) = 0 ∧ m22Count (fun g => m22BadB 2 g = true) = 0 ∧
      m22VGenCheck = true :=
  ⟨elt, counts (by norm_num), counts (by norm_num), counts (by norm_num), gen⟩

end CertificateChecks.KernelC232403

end
