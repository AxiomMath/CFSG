module

public import Certificates.Kernel.CF23L34.HeJChecks
public import Certificates.Kernel.LocalComp.HeFixBind
public import CFSG.Certificates.Kernel.CF23L34.SlpSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.HeJ

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.CF23L34
open CFSG.QuasithinUnique.Setup.X1 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.HeldB CFSG.ComponentClassification.GSThmB.CF23L34
open CFSG.LieType.Multipliers.L34 CFSG.ComponentClassification.GrSLit.L34Facts
open CertificateChecks.KernelLC.HeFix

@[expose, irreducible] noncomputable def hjR : List (Equiv.Perm (Fin 8330)) :=
  gRun [heGenPerm 0, heGenPerm 1] hjProg

@[expose] noncomputable def V (z : ℤ) : Equiv.Perm (Fin 8330) := gLetter hjR z

theorem V_neg (z : ℤ) : V (-z) = (V z)⁻¹ := gLetter_neg _ _

theorem V_zero : V 0 = 1 := gLetter_zero _

@[expose] def wfB : List (ℤ × ℤ) → ℕ → Bool
  | [], _ => true
  | p :: rest, m => decide (p.1.natAbs ≤ m + 2) && decide (p.2.natAbs ≤ m + 2) && wfB rest (m + 1)

theorem wfB_spec : ∀ (l : List (ℤ × ℤ)) (m : ℕ), wfB l m = true →
    ∀ k (hk : k < l.length), (l[k].1).natAbs ≤ m + k + 2 ∧ (l[k].2).natAbs ≤ m + k + 2
  | [], _, _, k, hk => absurd hk (by simp)
  | p :: rest, m, h, k, hk => by
    simp only [wfB, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases k with _ | k
    · simpa using h.1
    · have := wfB_spec rest (m + 1) h.2 k (by simpa using hk)
      simp only [List.getElem_cons_succ]
      omega

theorem hjProg_wf : ∀ k (hk : k < hjProg.length),
    (hjProg[k].1).natAbs ≤ k + 2 ∧ (hjProg[k].2).natAbs ≤ k + 2 := by
  have h := wfB_spec hjProg 0 (by decide +kernel)
  intro k hk
  have := h k hk
  omega

theorem V_reg (r : ℕ) (hr : 3 ≤ r) :
    V (r : ℤ) = V (hjProg.getD (r - 3) (0, 0)).1 * V (hjProg.getD (r - 3) (0, 0)).2 := by
  unfold V
  rw [hjR]
  exact gRun_reg hjProg _ rfl hjProg_wf r hr

theorem gLetter_one {G : Type*} [Group G] (a b : G) (T : List G) :
    gLetter ([a, b] ++ T) 1 = a := by
  simp [gLetter]

theorem gLetter_two {G : Type*} [Group G] (a b : G) (T : List G) :
    gLetter ([a, b] ++ T) 2 = b := by
  simp [gLetter]

theorem V_1 : V 1 = heGenPerm 0 := by
  unfold V
  obtain ⟨T, hT⟩ := gRun_append [heGenPerm 0, heGenPerm 1] hjProg
  rw [hjR, hT]
  exact gLetter_one _ _ T

theorem V_2 : V 2 = heGenPerm 1 := by
  unfold V
  obtain ⟨T, hT⟩ := gRun_append [heGenPerm 0, heGenPerm 1] hjProg
  rw [hjR, hT]
  exact gLetter_two _ _ T


theorem V_mem (z : ℤ) : V z ∈ heP := by
  unfold V
  refine gLetter_mem (fun g hg => ?_) z
  rw [hjR] at hg
  refine gRun_mem hjProg (fun g hg => ?_) g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact heGenPerm_mem (by norm_num)
  · exact heGenPerm_mem (by norm_num)

theorem pRep_pair {a b : Array ℕ} {g : Equiv.Perm (Fin 8330)} (ha : Rep 8330 a g)
    (hb : Rep 8330 b g⁻¹) : PRep 8330 (a, b) g :=
  ⟨ha, hb⟩

theorem pRep_gen (k : ℕ) (hk : k < 2) :
    PRep 8330 (heGen k, invCand 8330 (heGen k)) (heGenPerm k) :=
  pRep_pair (rep_heGen hk) (rep_heGen_inv hk)

theorem pRep_V (z : ℤ) : PRep 8330 (pLetter 8330 hjRegs z) (V z) := by
  have h : List.Forall₂ (PRep 8330) hjGens [heGenPerm 0, heGenPerm 1] :=
    .cons (pRep_gen 0 (by norm_num)) (.cons (pRep_gen 1 (by norm_num)) .nil)
  unfold V
  rw [hjR]
  exact pLetter_rel (pRun_rel hjProg h) z

@[expose] def good (z : ℤ) : Prop :=
  Rep 8330 (unpack 8330 14 (HeJT (hjIdx z))) (V z) ∧ PP 8330 14 (HeJT (hjIdx z))

theorem inv_parts {T : ℕ → ℕ} {j : ℕ} (h : hjInvOK T j = true) :
    permOK 8330 14 (mask 14) (8330 * 14) (T (Nat.mul 2 j)) (T (Nat.add (Nat.mul 2 j) 1)) = true ∧
      permOK 8330 14 (mask 14) (8330 * 14) (T (Nat.add (Nat.mul 2 j) 1)) (T (Nat.mul 2 j)) =
        true := by
  rw [hjInvOK.eq_1, bAnd_iff] at h
  exact h

theorem szOK8330 : szOK 8330 14 = true := by decide +kernel

theorem good_neg {z : ℤ} {j : ℕ} (hz : good z) (hinv : hjInvOK HeJT j = true)
    (h1 : hjIdx z = Nat.mul 2 j) (h2 : hjIdx (-z) = Nat.add (Nat.mul 2 j) 1) : good (-z) := by
  obtain ⟨p1, p2⟩ := inv_parts hinv
  unfold good at hz ⊢
  rw [h1] at hz
  rw [h2, V_neg]
  exact rep_inv_of_permOK szOK8330 hz.1 p1 p2

theorem good_of_sub {S : List ℤ} (hS : ∀ z ∈ S, good z) {L : List ℤ}
    (h : L.all (fun z => decide (z ∈ S)) = true) : ∀ z ∈ L, good z := fun z hz => by
  rw [List.all_eq_true] at h
  exact hS z (of_decide_eq_true (h z hz))

theorem good_tab {j : ℕ} {r : ℕ} (hj : hjTabOK HeJT j = true) (hr : hjKeep.getD j 0 = r)
    (h3 : 3 ≤ r) (hpos : hjIdx (r : ℤ) = Nat.add 4 (Nat.mul 2 j)) (hall : ∀ z ∈ hjD r, good z) :
    good (r : ℤ) := by
  rw [hjTabOK.eq_1, hr] at hj
  have e := Nat.eq_of_beq_eq_true hj
  obtain ⟨h1, h2⟩ := wzK_rep (V := V) szOK8330 (hjD r) hall
  have hp : ((hjD r).map V).prod = V r := by
    rw [hjD]
    exact slpR_prod V_neg V_zero V_reg 400 r h3
  rw [hp, e] at h1
  rw [e] at h2
  unfold good
  rw [hpos]
  exact ⟨h1, h2⟩

theorem good_gen0 : good 1 ∧ good (-1) := by
  have hg := ch22226_gen
  simp only [Bool.and_eq_true] at hg
  obtain ⟨p1, -⟩ := inv_parts (j := 0) ch22226i_0
  have p1' : permOK 8330 14 (mask 14) (8330 * 14) (HeJT 0) (HeJT 1) = true := p1
  have g1 : good 1 := by
    unfold good
    have e0 : hjIdx 1 = 0 := by decide
    rw [Nat.eq_of_beq_eq_true hg.1] at p1'
    rw [e0, Nat.eq_of_beq_eq_true hg.1, ← heGen_eq (k := 0) (by norm_num), V_1]
    exact ⟨rep_heGen (by norm_num), pp_of_permOK szOK8330 p1'⟩
  exact ⟨g1, good_neg g1 ch22226i_0 (by decide) (by decide)⟩

theorem good_gen1 : good 2 ∧ good (-2) := by
  have hg := ch22226_gen
  simp only [Bool.and_eq_true] at hg
  obtain ⟨p1, -⟩ := inv_parts (j := 1) ch22226i_1
  have p1' : permOK 8330 14 (mask 14) (8330 * 14) (HeJT 2) (HeJT 3) = true := p1
  have g1 : good 2 := by
    unfold good
    have e0 : hjIdx 2 = 2 := by decide
    rw [Nat.eq_of_beq_eq_true hg.2] at p1'
    rw [e0, Nat.eq_of_beq_eq_true hg.2, ← heGen_eq (k := 1) (by norm_num), V_2]
    exact ⟨rep_heGen (by norm_num), pp_of_permOK szOK8330 p1'⟩
  exact ⟨g1, good_neg g1 ch22226i_1 (by decide) (by decide)⟩

@[expose] def goodL : List ℤ :=
  [1, -1, 2, -2, 32, -32, 86, -86, 103, -103, 173, -173, 216, 217, -217, 226, 227, -227,
    250, -250, 277, -277, 278, 279, 280, 281, 282]

theorem cons_good {a : ℤ} {L : List ℤ} (ha : good a) (hL : ∀ z ∈ L, good z) :
    ∀ z ∈ a :: L, good z :=
  List.forall_mem_cons.2 ⟨ha, hL⟩

theorem nil_good : ∀ z ∈ ([] : List ℤ), good z := fun _ h => by simp at h

theorem goodL_all : ∀ z ∈ goodL, good z := by
  obtain ⟨g1, g1'⟩ := good_gen0
  obtain ⟨g2, g2'⟩ := good_gen1
  have S0 : ∀ z ∈ ([1, -1, 2, -2] : List ℤ), good z :=
    cons_good g1 (cons_good g1' (cons_good g2 (cons_good g2' nil_good)))
  have t32 : good 32 := good_tab ch22226t_0 rfl (by norm_num) (by decide)
    (good_of_sub S0 (by decide +kernel))
  have t32' := good_neg t32 ch22226i_2 (j := 2) (by decide) (by decide)
  have t86 : good 86 := good_tab ch22226t_1 rfl (by norm_num) (by decide)
    (good_of_sub S0 (by decide +kernel))
  have t86' := good_neg t86 ch22226i_3 (j := 3) (by decide) (by decide)
  have t103 : good 103 := good_tab ch22226t_2 rfl (by norm_num) (by decide)
    (good_of_sub S0 (by decide +kernel))
  have t103' := good_neg t103 ch22226i_4 (j := 4) (by decide) (by decide)
  have t173 : good 173 := good_tab ch22226t_3 rfl (by norm_num) (by decide)
    (good_of_sub S0 (by decide +kernel))
  have t173' := good_neg t173 ch22226i_5 (j := 5) (by decide) (by decide)
  have S1 : ∀ z ∈ ([1, -1, 2, -2, 32, -32, 86, -86, 103, -103, 173, -173] : List ℤ), good z :=
    cons_good g1 (cons_good g1' (cons_good g2 (cons_good g2' (cons_good t32 (cons_good t32'
      (cons_good t86 (cons_good t86' (cons_good t103 (cons_good t103' (cons_good t173
        (cons_good t173' nil_good)))))))))))
  have t216 : good 216 := good_tab ch22226t_4 rfl (by norm_num) (by decide)
    (good_of_sub S1 (by decide +kernel))
  have t217 : good 217 := good_tab ch22226t_5 rfl (by norm_num) (by decide)
    (good_of_sub (S := [216]) (cons_good t216 nil_good) (by decide +kernel))
  have t217' := good_neg t217 ch22226i_6 (j := 7) (by decide) (by decide)
  have t226 : good 226 := good_tab ch22226t_6 rfl (by norm_num) (by decide)
    (good_of_sub S1 (by decide +kernel))
  have t227 : good 227 := good_tab ch22226t_7 rfl (by norm_num) (by decide)
    (good_of_sub (S := [226]) (cons_good t226 nil_good) (by decide +kernel))
  have t227' := good_neg t227 ch22226i_7 (j := 9) (by decide) (by decide)
  have S2 : ∀ z ∈ ([217, -217, 227, -227] : List ℤ), good z :=
    cons_good t217 (cons_good t217' (cons_good t227 (cons_good t227' nil_good)))
  have t250 : good 250 := good_tab ch22226t_8 rfl (by norm_num) (by decide)
    (good_of_sub S2 (by decide +kernel))
  have t250' := good_neg t250 ch22226i_8 (j := 10) (by decide) (by decide)
  have t277 : good 277 := good_tab ch22226t_9 rfl (by norm_num) (by decide)
    (good_of_sub S2 (by decide +kernel))
  have t277' := good_neg t277 ch22226i_9 (j := 11) (by decide) (by decide)
  have t278 : good 278 := good_tab ch22226t_10 rfl (by norm_num) (by decide)
    (good_of_sub S0 (by decide +kernel))
  have t279 : good 279 := good_tab ch22226t_11 rfl (by norm_num) (by decide)
    (good_of_sub (S := [278, 2]) (cons_good t278 (cons_good g2 nil_good)) (by decide +kernel))
  have t280 : good 280 := good_tab ch22226t_12 rfl (by norm_num) (by decide)
    (good_of_sub (S := [279, 2]) (cons_good t279 (cons_good g2 nil_good)) (by decide +kernel))
  have t281 : good 281 := good_tab ch22226t_13 rfl (by norm_num) (by decide)
    (good_of_sub (S := [280, 2]) (cons_good t280 (cons_good g2 nil_good)) (by decide +kernel))
  have t282 : good 282 := good_tab ch22226t_14 rfl (by norm_num) (by decide)
    (good_of_sub (S := [281, 2]) (cons_good t281 (cons_good g2 nil_good)) (by decide +kernel))
  unfold goodL
  exact cons_good g1 (cons_good g1' (cons_good g2 (cons_good g2' (cons_good t32 (cons_good t32'
    (cons_good t86 (cons_good t86' (cons_good t103 (cons_good t103' (cons_good t173
    (cons_good t173' (cons_good t216 (cons_good t217 (cons_good t217' (cons_good t226
    (cons_good t227 (cons_good t227' (cons_good t250 (cons_good t250' (cons_good t277
    (cons_good t277' (cons_good t278 (cons_good t279 (cons_good t280 (cons_good t281
    (cons_good t282 nil_good))))))))))))))))))))))))))

theorem good_rep {L : List ℤ} (h : ∀ z ∈ L, z ∈ goodL) :
    ∀ z ∈ L, Rep 8330 (unpack 8330 14 (HeJT (hjIdx z))) (V z) :=
  fun z hz => (goodL_all z (h z hz)).1

theorem prod_mem (L : List ℤ) : (L.map V).prod ∈ heP := by
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨z, -, rfl⟩ := List.mem_map.1 hg
  exact V_mem z

theorem eqB_sound {L₁ L₂ : List ℤ} (h : hjEqB HeJT L₁ L₂ = true) (h₁ : ∀ z ∈ L₁, z ∈ goodL)
    (h₂ : ∀ z ∈ L₂, z ∈ goodL) : (L₁.map V).prod = (L₂.map V).prod := by
  rw [hjEqB.eq_1, CFSG.KS.Raw.Orb.allN_iff] at h
  have e : ((L₂.map V).prod)⁻¹ * (L₁.map V).prod = 1 := by
    refine eq_one_of_fix_base (heP.mul_mem (heP.inv_mem (prod_mem L₂)) (prod_mem L₁)) ?_
    intro b hb
    have hb' := Nat.eq_of_beq_eq_true (h b hb)
    rw [hjTr.eq_1, hjTr.eq_1, tzK_rep L₁ (good_rep h₁) b, tzK_rep L₂ (good_rep h₂) b] at hb'
    rw [Equiv.Perm.mul_apply, Fin.ext hb']
    exact Equiv.symm_apply_apply _ _
  exact (inv_mul_eq_one.1 e).symm

theorem neAt_sound {L₁ L₂ : List ℤ} {x : ℕ} (hx : x < 8330) (h : hjNeAt HeJT L₁ L₂ x = true)
    (h₁ : ∀ z ∈ L₁, z ∈ goodL) (h₂ : ∀ z ∈ L₂, z ∈ goodL) : (L₁.map V).prod ≠ (L₂.map V).prod := by
  intro e
  have e1 : tzK 14 HeJT hjIdx L₁ x = ((L₁.map V).prod ⟨x, hx⟩ : ℕ) :=
    tzK_rep L₁ (good_rep h₁) ⟨x, hx⟩
  have e2 : tzK 14 HeJT hjIdx L₂ x = ((L₂.map V).prod ⟨x, hx⟩ : ℕ) :=
    tzK_rep L₂ (good_rep h₂) ⟨x, hx⟩
  rw [hjNeAt.eq_1, hjTr.eq_1, hjTr.eq_1, e1, e2, e, Nat.beq_refl] at h
  exact absurd h (by decide)

theorem cl_mem (l : Fin 2 × Bool) : hjCl l ∈ goodL := by
  unfold hjCl
  split_ifs <;> decide

theorem cw_mem (w : List (Fin 2 × Bool)) : ∀ z ∈ hjCw w, z ∈ goodL := fun z hz => by
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hz
  exact cl_mem l

theorem mem_app {L₁ L₂ : List ℤ} (h₁ : ∀ z ∈ L₁, z ∈ goodL) (h₂ : ∀ z ∈ L₂, z ∈ goodL) :
    ∀ z ∈ L₁ ++ L₂, z ∈ goodL := fun z hz => (List.mem_append.1 hz).elim (h₁ z) (h₂ z)

theorem lit_mem {L : List ℤ} (h : L.all (fun z => decide (z ∈ goodL)) = true) :
    ∀ z ∈ L, z ∈ goodL := fun z hz => by
  rw [List.all_eq_true] at h
  exact of_decide_eq_true (h z hz)

theorem pRep_let {x y : PArr} (hx : PRep 8330 x (V 250)) (hy : PRep 8330 y (V 277))
    (l : Fin 2 × Bool) : PRep 8330 (hjLet x y l) (V (hjCl l)) := by
  unfold hjLet hjCl
  split_ifs
  · exact hx
  · rw [V_neg]
    exact hx.inv
  · exact hy
  · rw [V_neg]
    exact hy.inv

theorem pRep_word {x y : PArr} (hx : PRep 8330 x (V 250)) (hy : PRep 8330 y (V 277)) :
    ∀ w : List (Fin 2 × Bool), PRep 8330 (hjWord x y w) ((hjCw w).map V).prod
  | [] => by simpa [hjWord, hjCw] using (pRep_id (n := 8330))
  | l :: w => by
    rw [hjWord, hjCw, List.map_cons, List.map_cons, List.prod_cons]
    exact (pRep_let hx hy l).mul (pRep_word hx hy w)

theorem pRep_A : PRep 8330 hjA (V 250) := pRep_V 250

theorem pRep_B : PRep 8330 hjB (V 277) := pRep_V 277

theorem pRep_G : PRep 8330 hjG (V 32) := pRep_V 32

theorem rep_t : Rep 8330 (heGen 0) (V 1) := by
  rw [V_1]
  exact rep_heGen (by norm_num)

@[expose] noncomputable def Z1 : Equiv.Perm (Fin 8330) := ((hjCw zOne).map V).prod

theorem rep_Z1 : Rep 8330 hjZ1.1 Z1 := (pRep_word pRep_A pRep_B zOne).1

theorem eqA_false {t u : Array ℕ} {g h : Equiv.Perm (Fin 8330)} (ht : Rep 8330 t g)
    (hu : Rep 8330 u h) (hne : g ≠ h) : eqA 8330 t u = false := by
  cases e : eqA 8330 t u
  · rfl
  · exact absurd ((eqA_iff ht hu).1 e) hne

theorem comm_true {t u : Array ℕ} {g h : Equiv.Perm (Fin 8330)} (ht : Rep 8330 t g)
    (hu : Rep 8330 u h) (e : g * h = h * g) : hjComm t u = true :=
  (eqA_iff (rep_compA ht hu) (rep_compA hu ht)).2 e

theorem comm_false {t u : Array ℕ} {g h : Equiv.Perm (Fin 8330)} (ht : Rep 8330 t g)
    (hu : Rep 8330 u h) (e : g * h ≠ h * g) : hjComm t u = false :=
  eqA_false (rep_compA ht hu) (rep_compA hu ht) e

theorem pair_eq {a b : ℤ} (h : hjEqB HeJT [a, b] [b, a] = true) (ha : a ∈ goodL)
    (hb : b ∈ goodL) : V a * V b = V b * V a := by
  have := eqB_sound h (lit_mem (by simp [ha, hb])) (lit_mem (by simp [ha, hb]))
  simpa using this

theorem rels_true : ∀ w ∈ coverWs ++ [zThree],
    eqA 8330 (hjWord hjA hjB w).1 (idA 8330) = true := by
  intro w hw
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
  have hi' : i < 21 := by
    have := ch22226_len.1
    rw [hjRelW] at this
    omega
  have hc : hjEqB HeJT (hjCw (hjRelW.getD i [])) [] = true := by
    interval_cases i
    exacts [ch22226w_0, ch22226w_1, ch22226w_2, ch22226w_3, ch22226w_4, ch22226w_5, ch22226w_6,
      ch22226w_7, ch22226w_8, ch22226w_9, ch22226w_10, ch22226w_11, ch22226w_12, ch22226w_13,
      ch22226w_14, ch22226w_15, ch22226w_16, ch22226w_17, ch22226w_18, ch22226w_19, ch22226w_20]
  rw [hjRelW, List.getD_eq_getElem _ _ hi] at hc
  have e := eqB_sound hc (cw_mem _) (by simp)
  rw [List.map_nil, List.prod_nil] at e
  exact (eqA_iff (pRep_word pRep_A pRep_B _).1 rep_idA).2 e

theorem rep_NF (k a b : ℕ) : Rep 8330 (hjNF k a b)
    (((hjCw (tw k)).map V).prod * (if a = 1 then Z1 else 1) * (if b = 1 then V 1 else 1)) := by
  unfold hjNF
  refine rep_compA (rep_compA (pRep_word pRep_A pRep_B _).1 ?_) ?_
  · split_ifs
    · exact rep_Z1
    · exact rep_idA
  · split_ifs
    · exact rep_t
    · exact rep_idA

theorem hjX_prod (r : ℤ) : ((hjX r).map V).prod = V r := by
  rw [hjX, frz_prod V_neg, slpX_prod V_neg V_zero V_reg]

theorem label_of {l : ℕ × ℕ × ℕ × ℤ} (hc : hjLabK HeJT l = true)
    (hx : ∀ z ∈ hjX l.2.2.2, z ∈ goodL) : hjLabelOK l = true := by
  rw [hjLabK.eq_1] at hc
  have h1 : ∀ z ∈ (hjLabW l).1, z ∈ goodL := mem_app hx (lit_mem (by decide))
  have h2 : ∀ z ∈ (hjLabW l).2, z ∈ goodL := by
    intro z hz
    simp only [hjLabW, List.mem_cons, List.mem_append] at hz
    rcases hz with rfl | ((hz | hz) | hz) | hz
    · decide
    · exact cw_mem _ z hz
    · split_ifs at hz
      · exact cw_mem _ z hz
      · simp at hz
    · split_ifs at hz
      · simp only [List.mem_singleton] at hz
        rw [hz]
        decide
      · simp at hz
    · exact hx z hz
  have e := eqB_sound hc h1 h2
  have e1 : ((hjLabW l).1.map V).prod = V l.2.2.2 * V 1 := by
    simp only [hjLabW, List.map_append, List.prod_append, hjX_prod, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one]
  have e2 : ((hjLabW l).2.map V).prod = V 1 * (((hjCw (tw l.1)).map V).prod *
      (if l.2.1 = 1 then Z1 else 1) * (if l.2.2.1 = 1 then V 1 else 1)) * V l.2.2.2 := by
    simp only [hjLabW, List.map_append, List.prod_append, hjX_prod, List.map_cons,
      List.prod_cons, Z1]
    split_ifs <;> simp [mul_assoc]
  rw [e1, e2] at e
  have pR := pRep_V l.2.2.2
  unfold hjLabelOK
  refine (eqA_iff (rep_compA (rep_compA pR.1 rep_t) pR.2) (rep_compA rep_t (rep_NF _ _ _))).2 ?_
  rw [mul_inv_eq_iff_eq_mul, e]

theorem label_true {l : ℕ × ℕ × ℕ × ℤ} (hl : l ∈ hjLabels) : hjLabelOK l = true := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
  have hi' : i < 3 := by
    have := ch22226_len.2.2.2
    omega
  rw [← List.getD_eq_getElem _ (0, 0, 0, 0) hi]
  interval_cases i
  · exact label_of ch22226l_0 (lit_mem (by decide +kernel))
  · exact label_of ch22226l_1 (lit_mem (by decide +kernel))
  · exact label_of ch22226l_2 (lit_mem (by decide +kernel))

theorem hjFusOK_true : hjFusOK = true := by
  have hcomm := ch22226_comm
  have hz := ch22226_z
  have hne := ch22226_ne
  simp only [Bool.and_eq_true] at hcomm hz hne
  have gA : (250 : ℤ) ∈ goodL := by decide
  have gB : (277 : ℤ) ∈ goodL := by decide
  have gG : (32 : ℤ) ∈ goodL := by decide
  have g1 : (1 : ℤ) ∈ goodL := by decide
  have hZ2 : ((hjCw zTwo).map V).prod = V 1 := by
    simpa using eqB_sound hz.1 (cw_mem _) (lit_mem (by decide))
  have hZ1 : Z1 * Z1 = 1 := by
    have := eqB_sound hz.2 (mem_app (cw_mem _) (cw_mem _)) (by simp)
    simpa [Z1] using this
  have n1 : Z1 ≠ 1 := by
    have := neAt_sound (by norm_num) hne.1.1.1 (cw_mem _) (by simp)
    simpa [Z1] using this
  have n2 : Z1 ≠ V 1 := by
    have := neAt_sound (by norm_num) hne.1.1.2 (cw_mem _) (lit_mem (by decide))
    simpa [Z1] using this
  have n3 : V 250 * V 277 ≠ V 277 * V 250 := by
    have := neAt_sound (by norm_num) hne.1.2 (lit_mem (by decide)) (lit_mem (by decide))
    simpa using this
  have n4 : V 32 * Z1 ≠ Z1 * V 32 := by
    have := neAt_sound (by norm_num) hne.2
      (fun z hz => (List.mem_cons.1 hz).elim (fun e => e ▸ gG) (cw_mem _ z))
      (mem_app (cw_mem _) (lit_mem (by decide)))
    simpa [Z1, List.prod_append] using this
  unfold hjFusOK
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, rels_true⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, fun l hl => label_true hl⟩
  · exact comm_true pRep_A.1 rep_t (pair_eq hcomm.1.1 gA g1)
  · exact comm_true pRep_B.1 rep_t (pair_eq hcomm.1.2 gB g1)
  · exact (eqA_iff (pRep_word pRep_A pRep_B zTwo).1 rep_t).2 hZ2
  · exact (eqA_iff (rep_compA rep_Z1 rep_Z1) rep_idA).2 hZ1
  · exact eqA_false rep_Z1 rep_idA n1
  · exact eqA_false rep_Z1 rep_t n2
  · exact comm_false pRep_A.1 pRep_B.1 n3
  · exact comm_true pRep_G.1 rep_t (pair_eq hcomm.2 gG g1)
  · exact comm_false pRep_G.1 rep_Z1 n4

end CertificateChecks.KernelLC.HeJ

end
