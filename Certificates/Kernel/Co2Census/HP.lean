module

public import Certificates.Kernel.Co2Census.HPQ
public import Certificates.Kernel.Co2Census.HPK0
public import Certificates.Kernel.Co2Census.HPK1
public import Certificates.Kernel.Co2Census.HPK2
public import Certificates.Kernel.Co2Census.HPK3
public import Certificates.Kernel.Co2Census.HPKF
public import Certificates.Kernel.Co2Census.HPKE
public import CFSG.Sporadic.Co2Smith.ClassCount
public import Certificates.Kernel.Co2Census.S0Cent
public import Certificates.Kernel.Co2Census.S0Inv

public section

namespace CertificateChecks.KernelCo2Census

open CFSG.Sporadic.Co2Smith CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.KC.Co2InvS
  CFSG.KC.Co2Census CFSG.KC.Loop Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

section HP


theorem F1_misc_spec : SK 0 = IDP ∧ SK 1 = ABt 0 ∧ SK 2 = ABt 1 ∧
    (List.range 5).map Lrt = [0, 1, 64, 379, 1324] ∧ Z0 < 2 ^ 484 ∧ QKt 0 = IDP ∧
    QKt 256 = Z0 := by
  have h := F1_misc
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq, beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem Z0_lt : Z0 < 2 ^ 484 := F1_misc_spec.2.2.2.2.1

theorem QK_eq : ∀ e < 512, QKt e = KernelCo2SmithS.nfS (e / 256) (e % 256) :=
  fun e he => Nat.eq_of_beq_eq_true (Q_ok e he)

theorem cElt_zero_zero : cElt 0 0 = 1 := by
  have h := repK_cElt (e := 0) (by norm_num) 0
  rw [← QK_eq 0 (by norm_num), F1_misc_spec.2.2.2.2.2.1, F1_misc_spec.1] at h
  exact repK_fun h (by rw [show mulV IDP IDP = IDP by decide +kernel]; exact repK_one)

theorem fpElt_zero_zero : fpElt 0 0 = 1 :=
  Subtype.ext (Prod.ext (Subtype.ext cElt_zero_zero) pLift_zero)

theorem hpElt_zero_zero' : hpElt 0 0 = 1 := by
  rw [hpElt_eq_mk, fpElt_zero_zero, map_one]

theorem cElt_z : cElt 256 0 = z0 := by
  have h := repK_cElt (e := 256) (by norm_num) 0
  rw [← QK_eq 256 (by norm_num), F1_misc_spec.2.2.2.2.2.2, F1_misc_spec.1] at h
  refine repK_fun h ?_
  have e : mulV IDP Z0 = Z0 := by
    have := repK_mul repK_one (repK_z0 Z0_lt)
    rw [one_mul] at this
    exact repK_unique this (repK_z0 Z0_lt)
  rw [e]
  exact repK_z0 Z0_lt

theorem hpElt_z_central (g : Hprime) : g * hpElt 256 0 = hpElt 256 0 * g := by
  obtain ⟨⟨⟨h, p⟩, hp⟩, rfl⟩ := QuotientGroup.mk_surjective g
  change mkHP _ * mkHP (fpElt 256 0) = mkHP (fpElt 256 0) * mkHP _
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  refine Prod.ext (Subtype.ext ?_) ?_
  · change (h : K) * cElt 256 0 = cElt 256 0 * (h : K)
    rw [cElt_z]
    exact Subgroup.mem_centralizer_singleton_iff.mp h.2
  · change p * pLift 0 = pLift 0 * p
    rw [pLift_zero, mul_one, one_mul]

theorem piK_mem (y : Hprime) : piK y ∈ S0 := (piHP y).2

theorem f1n_rep {j : ℕ} (hj : j < 5) : repK (sElt (f1n j)) (LPt (Lrt j)) := by
  obtain ⟨-, -, -, -, h4, h5, -, h7⟩ := L_misc_spec
  by_cases h0 : j = 0
  · subst h0
    rw [h4, h5, show f1n 0 = 0 from rfl, ← F1_misc_spec.1]
    exact repK_sElt 0
  · obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0
    rw [(h7 j' (by omega)).1]
    have hj' : j' < 4 := by omega
    have e : f1n (j' + 1) = s0Reps.getD j' 0 := by
      interval_cases j' <;> rfl
    rw [e]
    exact repK_sElt _

theorem hp_card_inv : Nat.card {y : Hprime // y * y = 1} = 146432 := by
  have e : ∀ y : Hprime, y * y = 1 ↔ hpPred (hpElt 0 0) (hpElt 0 0) false y := by
    intro y
    simp [hpPred, hpElt_zero_zero']
  rw [Nat.card_congr (Equiv.subtypeEquivRight e)]
  have hs : ConjSteps repK stL 2 fun l => piK (hpElt 0 (l + 1)) := by
    refine conjSteps_of (fun l hl => ?_) (fun l hl => ?_)
    · rw [piK_hpElt]
      rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
      · rw [← F1_misc_spec.2.1]
        exact repK_sElt 1
      · rw [← F1_misc_spec.2.2.1]
        exact repK_sElt 2
    · obtain ⟨-, -, h2, h3, -⟩ := L_misc_spec
      rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
      · exact ⟨h2, ABIt_lt (by norm_num)⟩
      · exact ⟨h3, ABIt_lt (by norm_num)⟩
  have hw : ∀ l < 2, ∀ y, hpPred (hpElt 0 0) (hpElt 0 0) false
      (hpElt 0 (l + 1) * y * (hpElt 0 (l + 1))⁻¹) ↔ hpPred (hpElt 0 0) (hpElt 0 0) false y := by
    intro l _ y
    exact hpPred_conj (by rw [hpElt_zero_zero', mul_one, one_mul])
      (by rw [hpElt_zero_zero', mul_one, one_mul]) false y
  have hL := F1_misc_spec.2.2.2.1
  have hdist : ∀ j < 5, ∀ j' < 5, Lrt j = Lrt j' → j = j' := by
    intro j hj j' hj' e
    have h1 : Lrt j = [0, 1, 64, 379, 1324].getD j 0 := by
      rw [← hL, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range]
    have h2 : Lrt j' = [0, 1, 64, 379, 1324].getD j' 0 := by
      rw [← hL, List.getD_eq_getElem _ _ (by simpa using hj'), List.getElem_map, List.getElem_range]
    rw [h1, h2] at e
    interval_cases j <;> interval_cases j' <;> simp_all
  have hrk : ∀ j < 5, Lrt j < 5104 ∧ rtOf LXt (Lrt j) = Lrt j ∧
      repK (sElt (f1n j)) (LPt (Lrt j)) := fun j hj =>
    ⟨(L_misc_spec.2.2.2.2.2.2.1 j hj).1, (L_misc_spec.2.2.2.2.2.2.1 j hj).2.1, f1n_rep hj⟩
  have hsupp : ∀ y, hpPred (hpElt 0 0) (hpElt 0 0) false y → ∃ i < 5104, repK (piK y) (LPt i) := by
    intro y hy
    have h2 := congrArg piK hy.2
    rw [map_mul, hpElt_zero_zero', map_one] at h2
    exact s0_inv_iff.1 ⟨piK_mem y, h2⟩
  rw [card_query piK _ (hi := 80) hs hw L_tree (fun i hi => L_roots_spec hi) hdist hrk hsupp
      (by norm_num),
    ← F1_total, ← sum_range_list]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  congr 1
  have hRR : repK (((fpElt 0 0).1.1 : Cz) : K) (mulV (SK 0) (QKt 0)) := by
    rw [fpElt_fst, QK_eq 0 (by norm_num)]
    exact repK_cElt (by norm_num) 0
  have hok := List.all_eq_true.1 F1_ok j (List.mem_range.2 hj')
  have hn : f1n j < 1451520 := by interval_cases j <;> decide
  exact fib_hp_eq Z0_lt QK_eq hRR (fpElt_snd _ _) hRR (fpElt_snd _ _) false hn hok

theorem sqrtCnt_eq_pred (c r : Hprime) :
    sqrtCnt c r = Nat.card {y : Hprime // hpPred r c true y} := by
  unfold sqrtCnt hpPred
  exact Nat.card_congr (Equiv.subtypeEquivRight fun y => by simp)

theorem piK_z : piK (hpElt 256 0) = 1 := by rw [piK_hpElt, sElt_zero]

theorem suppZ {Pt Zc : ℕ → ℕ} {N nr er : ℕ}
    (hpos : ∀ j < 5104, posK (fun x => Nat.beq (mulV x (SK nr)) (mulV (SK nr) x)) LPt Pt Zc N j =
      true) {c : Hprime} (hc : piK c = 1) :
    ∀ y, hpPred (hpElt er nr) c true y → ∃ i < N, repK (piK y) (Pt i) := by
  intro y hy
  have h1 := congrArg piK (hy.1 rfl)
  rw [map_mul, map_mul, piK_hpElt] at h1
  have h2 := congrArg piK hy.2
  rw [map_mul, hc] at h2
  obtain ⟨j, hj, hrep⟩ := s0_inv_iff.1 ⟨piK_mem y, h2⟩
  have ht : Nat.beq (mulV (LPt j) (SK nr)) (mulV (SK nr) (LPt j)) = true := by
    rw [Nat.beq_eq]
    exact repK_unique (h1 ▸ repK_mul hrep (repK_sElt nr)) (repK_mul (repK_sElt nr) hrep)
  obtain ⟨hp, he⟩ := posK_sound hpos j hj ht
  exact ⟨_, hp, he ▸ hrep⟩

theorem supp2331 {Pt Rc : ℕ → ℕ} {N er : ℕ}
    (hpos : ∀ j < 4608, posK (fun x => Nat.beq (mulV x x) (SK 2331)) C2331Pt Pt Rc N j = true) :
    ∀ y, hpPred (hpElt er 2331) (hpElt er 2331) true y → ∃ i < N, repK (piK y) (Pt i) := by
  intro y hy
  have h2 := congrArg piK hy.2
  rw [map_mul, piK_hpElt] at h2
  have hc : piK y ∈ centS0 (sElt 2331) := ⟨piK_mem y, by rw [← h2, ← mul_assoc]⟩
  rw [← cent_2331] at hc
  obtain ⟨j, hj, hrep⟩ := hc
  have ht : Nat.beq (mulV (C2331Pt j) (C2331Pt j)) (SK 2331) = true := by
    rw [Nat.beq_eq]
    exact repK_unique (h2 ▸ repK_mul hrep hrep) (repK_sElt 2331)
  obtain ⟨hp, he⟩ := posK_sound hpos j hj ht
  exact ⟨_, hp, he ▸ hrep⟩

theorem all_lt {f : ℕ → Bool} {n : ℕ} (h : (List.range n).all f = true) : ∀ j < n, f j = true :=
  fun j hj => List.all_eq_true.1 h j (List.mem_range.2 hj)

theorem hp_sqrt0 : sqrtCnt (hpElt 256 0) (hpElt 1 0) = 5376 ∧
    sqrtCnt (hpElt 1 0) (hpElt 1 0) = 5376 := by
  rw [sqrtCnt_eq_pred, sqrtCnt_eq_pred]
  constructor
  · rw [card_hp_query Z0_lt QK_eq (G := H0Gt) (GR := H0GRt) (GI := H0GIt) (Pt := H0ZPt)
      (IX := H0ZXt) (RT := H0Zrt) (N := 5104) (hi := 80) (nroots := 18) (by norm_num)
      (by norm_num) true (fun w _ => hpElt_z_central w) (all_lt H0_gens) H0Z_tree
      (all_lt H0Z_roots) H0Z_cover (suppZ H0Z_pos piK_z) (by norm_num), H0Z_total]
  · rw [card_hp_query Z0_lt QK_eq (G := H0Gt) (GR := H0GRt) (GI := H0GIt) (Pt := H0ZPt)
      (IX := H0ZXt) (RT := H0Zrt) (N := 5104) (hi := 80) (nroots := 18) (by norm_num)
      (by norm_num) true (fun w h => h) (all_lt H0_gens) H0Z_tree
      (all_lt H0Z_roots) H0Z_cover (suppZ H0Z_pos (by rw [piK_hpElt, sElt_zero])) (by norm_num),
      H0R_total]

theorem hp_sqrt1 : sqrtCnt (hpElt 256 0) (hpElt 0 2331) = 1152 ∧
    sqrtCnt (hpElt 0 2331) (hpElt 0 2331) = 768 := by
  rw [sqrtCnt_eq_pred, sqrtCnt_eq_pred]
  constructor
  · rw [card_hp_query Z0_lt QK_eq (G := H1Gt) (GR := H1GRt) (GI := H1GIt) (Pt := H1ZPt)
      (IX := H1ZXt) (RT := H1Zrt) (N := 368) (hi := 6) (nroots := 14) (by norm_num)
      (by norm_num) true (fun w _ => hpElt_z_central w) (all_lt H1_gens) H1Z_tree
      (all_lt H1Z_roots) H1Z_cover (suppZ H1Z_pos piK_z) (by norm_num), H1Z_total]
  · rw [card_hp_query Z0_lt QK_eq (G := H1Gt) (GR := H1GRt) (GI := H1GIt) (Pt := H1RPt)
      (IX := H1RXt) (RT := H1Rrt) (N := 48) (hi := 1) (nroots := 4) (by norm_num)
      (by norm_num) true (fun w h => h) (all_lt H1_gens) H1R_tree
      (all_lt H1R_roots) H1R_cover (supp2331 H1R_pos) (by norm_num), H1R_total]

theorem hp_sqrt2 : sqrtCnt (hpElt 256 0) (hpElt 2 2331) = 448 ∧
    sqrtCnt (hpElt 2 2331) (hpElt 2 2331) = 128 := by
  rw [sqrtCnt_eq_pred, sqrtCnt_eq_pred]
  constructor
  · rw [card_hp_query Z0_lt QK_eq (G := H2Gt) (GR := H2GRt) (GI := H2GIt) (Pt := H2ZPt)
      (IX := H2ZXt) (RT := H2Zrt) (N := 368) (hi := 6) (nroots := 40) (by norm_num)
      (by norm_num) true (fun w _ => hpElt_z_central w) (all_lt H2_gens) H2Z_tree
      (all_lt H2Z_roots) H2Z_cover (suppZ H2Z_pos piK_z) (by norm_num), H2Z_total]
  · rw [card_hp_query Z0_lt QK_eq (G := H2Gt) (GR := H2GRt) (GI := H2GIt) (Pt := H2RPt)
      (IX := H2RXt) (RT := H2Rrt) (N := 48) (hi := 1) (nroots := 7) (by norm_num)
      (by norm_num) true (fun w h => h) (all_lt H2_gens) H2R_tree
      (all_lt H2R_roots) H2R_cover (supp2331 H2R_pos) (by norm_num), H2R_total]

theorem hp_sqrt3 : sqrtCnt (hpElt 256 0) (hpElt 0 144) = 96 ∧
    sqrtCnt (hpElt 0 144) (hpElt 0 144) = 0 := by
  constructor
  · rw [sqrtCnt_eq_pred, card_hp_query Z0_lt QK_eq (G := H3Gt) (GR := H3GRt) (GI := H3GIt)
      (Pt := H3ZPt) (IX := H3ZXt) (RT := H3Zrt) (N := 112) (hi := 2) (nroots := 24)
      (by norm_num) (by norm_num) true (fun w _ => hpElt_z_central w) (all_lt H3_gens) H3Z_tree
      (all_lt H3Z_roots) H3Z_cover (suppZ H3Z_pos piK_z) (by norm_num), H3Z_total]
  · unfold sqrtCnt
    rw [Nat.card_eq_zero]
    left
    refine ⟨fun ⟨y, _, hy⟩ => ?_⟩
    have h2 := congrArg piK hy
    rw [map_mul, piK_hpElt] at h2
    have hc : piK y ∈ centS0 (sElt 144) := ⟨piK_mem y, by rw [← h2, ← mul_assoc]⟩
    rw [← cent_144] at hc
    obtain ⟨j, hj, hrep⟩ := hc
    have ht := C144_noroot j hj
    rw [Bool.not_eq_true'] at ht
    exact Nat.ne_of_beq_eq_false ht (repK_unique (h2 ▸ repK_mul hrep hrep) (repK_sElt 144))

theorem repK_hp (e n : ℕ) (he : e < 512) :
    repK (((fpElt e n).1.1 : Cz) : K) (mulV (SK n) (QKt e)) := by
  rw [fpElt_fst, QK_eq e he]
  exact repK_cElt he n

theorem hp_rep {i : ℕ} (hi : i < 4) :
    hpElt (hpRepE i) (hpRepN i) * hpElt (hpRepE i) (hpRepN i) = 1 ∧
      hpElt (hpRepE i) (hpRepN i) ≠ 1 ∧ hpElt (hpRepE i) (hpRepN i) ≠ hpElt 256 0 := by
  have h := all_lt rep_ok i hi
  unfold repOK at h
  simp only [letB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨hk, hnz⟩, hsq⟩, hrows⟩, hne'⟩ := h
  have hne : SK (hpRepN i) ≠ IDP ∨ (mulV (SK (hpRepN i)) (QKt (hpRepE i)) ≠ IDP ∧
      mulV (SK (hpRepN i)) (QKt (hpRepE i)) ≠ Z0) := by
    rcases hne' with h1 | ⟨h1, h2⟩
    · exact Or.inl (Nat.ne_of_beq_eq_false h1)
    · exact Or.inr ⟨Nat.ne_of_beq_eq_false h1, Nat.ne_of_beq_eq_false h2⟩
  have he : hpRepE i < 512 := by interval_cases i <;> decide
  have hn : hpRepN i < 1451520 := by interval_cases i <;> decide
  set e := hpRepE i
  set n := hpRepN i
  have hR := repK_hp e n he
  have hone : repK (((fpElt 0 0).1.1 : Cz) : K) IDP := by
    rw [fpElt_fst, cElt_zero_zero]
    exact repK_one
  have hz : repK (((fpElt 256 0).1.1 : Cz) : K) Z0 := by
    rw [fpElt_fst, cElt_z]
    exact repK_z0 Z0_lt
  have hsq' : sElt n * sElt n = sElt 0 :=
    repK_fun (hsq ▸ repK_mul (repK_sElt n) (repK_sElt n)) (F1_misc_spec.1 ▸ repK_sElt 0)
  have hcov : covMap (pLift n * pLift n) = covMap (pLift 0) := by
    simp only [map_mul, covMap_pLift']
    exact Subtype.ext hsq'
  have hk2 := sign_cases hcov (spin_prod n n) (spin_one 0) (length_spinMV _ _) hnz hk
  refine ⟨?_, ?_, ?_⟩
  · rw [← hpElt_zero_zero', hpElt_eq_mk, hpElt_eq_mk, ← map_mul]
    refine (mkHP_iff_sign Z0_lt ?_ (repK_mul hR hR) hone).2 hrows
    rcases hk2 with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact Or.inl ⟨h0, h1⟩
    · exact Or.inr ⟨h0, h1⟩
  · intro e1
    have hpi := congrArg piK e1
    rw [piK_hpElt, map_one] at hpi
    rcases hne with h1 | ⟨h1, h2⟩
    · exact h1 (repK_unique (hpi ▸ repK_sElt n) repK_one)
    · have hn0 : n = 0 := sElt_injOn hn (by norm_num) (hpi.trans sElt_zero.symm)
      rw [← hpElt_zero_zero', hpElt_eq_mk, hpElt_eq_mk,
        mkHP_eq_same (by rw [fpElt_snd, fpElt_snd, hn0])] at e1
      exact h1 (repK_unique (e1 ▸ hR) hone)
  · intro e1
    have hpi := congrArg piK e1
    rw [piK_hpElt, piK_hpElt, sElt_zero] at hpi
    rcases hne with h1 | ⟨h1, h2⟩
    · exact h1 (repK_unique (hpi ▸ repK_sElt n) repK_one)
    · have hn0 : n = 0 := sElt_injOn hn (by norm_num) (hpi.trans sElt_zero.symm)
      rw [hpElt_eq_mk, hpElt_eq_mk, mkHP_eq_same (by rw [fpElt_snd, fpElt_snd, hn0])] at e1
      exact h2 (repK_unique (e1 ▸ hR) hz)

theorem fibOK_spec {F : ℕ → ℕ} {er nr j : ℕ} (her : er < 512) (h : fibOK QKt F er nr j = true) :
    fld21 (F j) 0 < 512 ∧ (j = 0 ∨ fld21 (F (j - 1)) 0 < fld21 (F j) 0) ∧
      hpElt (fld21 (F j) 1) (fld21 (F j) 2) * hpElt er nr =
        hpElt (fld21 (F j) 0) nr * hpElt (fld21 (F j) 1) (fld21 (F j) 2) := by
  unfold fibOK at h
  simp only [letB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨he2, heh⟩, hnh⟩, hord⟩, hcomm⟩, hk⟩, hnz⟩, hrows⟩ := h
  refine ⟨he2, hord, ?_⟩
  set e2 := fld21 (F j) 0
  set eh := fld21 (F j) 1
  set nh := fld21 (F j) 2
  have hsc : sElt nh * sElt nr = sElt nr * sElt nh :=
    repK_fun (hcomm ▸ repK_mul (repK_sElt nh) (repK_sElt nr)) (repK_mul (repK_sElt nr) (repK_sElt nh))
  have hcov : covMap (pLift nh * pLift nr) = covMap (pLift nr * pLift nh) := by
    simp only [map_mul, covMap_pLift']
    exact Subtype.ext hsc
  have hk1 := sign_cases hcov (spin_prod nh nr) (spin_prod nr nh) (length_spinMV _ _) hnz hk
  rw [hpElt_eq_mk, hpElt_eq_mk, hpElt_eq_mk, ← map_mul, ← map_mul]
  refine (mkHP_iff_sign Z0_lt ?_ (repK_mul (repK_hp eh nh heh) (repK_hp er nr her))
    (repK_mul (repK_hp e2 nr he2) (repK_hp eh nh heh))).2 hrows
  rcases hk1 with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact Or.inl ⟨h0, h1⟩
  · exact Or.inr ⟨h0, h1⟩

theorem strict_inj {F : ℕ → ℕ} {nf : ℕ} (h : ∀ j < nf, j = 0 ∨ fld21 (F (j - 1)) 0 < fld21 (F j) 0) :
    ∀ j < nf, ∀ j' < nf, fld21 (F j) 0 = fld21 (F j') 0 → j = j' :=
  roots_strict h

theorem hp_cls_le {F : ℕ → ℕ} {er nr nf slot : ℕ} (her : er < 512) (hnr : nr < 1451520)
    (hslot : slot < 5) (hrep : s0Rep slot = sElt nr) (hF : ∀ j < nf, fibOK QKt F er nr j = true) :
    s0Sizes.getD slot 0 * nf ≤ (conjSet (hpElt er nr)).ncard := by
  classical
  have hfs := fun j hj => fibOK_spec her (hF j hj)
  obtain ⟨hcl, hcard⟩ := s0_class hslot
  rw [hcl, hrep] at hcard
  set KS : Set K := {y | ∃ w ∈ S0, y = w * sElt nr * w⁻¹}
  set FS : Set ℕ := {j | j < nf}
  have hFS : FS.ncard = nf := by
    rw [show FS = (Finset.range nf : Set ℕ) by ext j; simp [FS], Set.ncard_coe_finset,
      Finset.card_range]
  have hlift : ∀ s ∈ KS, ∃ h : Hprime, piK h * sElt nr * (piK h)⁻¹ = s := by
    rintro s ⟨w, hw, rfl⟩
    obtain ⟨m, -, hm⟩ := exists_sElt hw
    exact ⟨hpElt 0 m, by rw [piK_hpElt, hm]⟩
  let lift : K → Hprime := fun s => if h : ∃ h : Hprime, piK h * sElt nr * (piK h)⁻¹ = s then
    h.choose else 1
  have hlift' : ∀ s ∈ KS, piK (lift s) * sElt nr * (piK (lift s))⁻¹ = s := by
    intro s hs
    simp only [lift, dif_pos (hlift s hs)]
    exact (hlift s hs).choose_spec
  let Φ : K × ℕ → Hprime := fun p => lift p.1 * hpElt (fld21 (F p.2) 0) nr * (lift p.1)⁻¹
  have hmaps : Set.MapsTo Φ (KS ×ˢ FS) (conjSet (hpElt er nr)) := by
    rintro ⟨s, j⟩ ⟨_, hj⟩
    obtain ⟨-, -, hc⟩ := hfs j hj
    set u := hpElt (fld21 (F j) 1) (fld21 (F j) 2)
    refine ⟨lift s * u, ?_⟩
    have hy : hpElt (fld21 (F j) 0) nr = u * hpElt er nr * u⁻¹ := by
      rw [hc]
      group
    simp only [Φ]
    rw [hy]
    group
  have hinj : Set.InjOn Φ (KS ×ˢ FS) := by
    rintro ⟨s, j⟩ ⟨hs, hj⟩ ⟨s', j'⟩ ⟨hs', hj'⟩ e
    simp only [Φ] at e
    have hpi := congrArg piK e
    simp only [map_mul, map_inv, piK_hpElt] at hpi
    rw [hlift' s hs, hlift' s' hs'] at hpi
    subst hpi
    have e2 : hpElt (fld21 (F j) 0) nr = hpElt (fld21 (F j') 0) nr :=
      mul_left_cancel (mul_right_cancel e)
    have e3 := (hpElt_injOn (hfs j hj).1 (hfs j' hj').1 hnr hnr e2).1
    rw [strict_inj (fun j hj => (hfs j hj).2.1) j hj j' hj' e3]
  have := Set.ncard_le_ncard_of_injOn Φ hmaps hinj (Set.toFinite _)
  rw [Set.ncard_prod, hcard, hFS] at this
  exact this

theorem fpElt_snd_zero (e : ℕ) : (fpElt e 0).1.2 = 1 := pLift_zero

theorem hpElt_zero_mul (e e' : ℕ) : hpElt e 0 * hpElt e' 0 = mkHP (fpElt e 0 * fpElt e' 0) := by
  rw [hpElt_eq_mk, hpElt_eq_mk, map_mul]

theorem E_comm_iff {e e' : ℕ} (he : e < 512) (he' : e' < 512) :
    hpElt e 0 * hpElt e' 0 = hpElt e' 0 * hpElt e 0 ↔
      mulV (ER e) (ER e') = mulV (ER e') (ER e) := by
  rw [hpElt_zero_mul, hpElt_zero_mul]
  rw [mkHP_eq_same (by
    change (fpElt e 0).1.2 * (fpElt e' 0).1.2 = (fpElt e' 0).1.2 * (fpElt e 0).1.2
    rw [fpElt_snd_zero, fpElt_snd_zero])]
  have h1 := repK_mul (repK_hp e 0 he) (repK_hp e' 0 he')
  have h2 := repK_mul (repK_hp e' 0 he') (repK_hp e 0 he)
  constructor
  · intro h
    change (((fpElt e 0).1.1 : Cz) : K) * (((fpElt e' 0).1.1 : Cz) : K) =
      (((fpElt e' 0).1.1 : Cz) : K) * (((fpElt e 0).1.1 : Cz) : K) at h
    rw [h] at h1
    exact repK_unique h1 h2
  · intro h
    rw [ER, ER] at h
    rw [h] at h1
    exact repK_fun h1 h2

theorem hypMat_symm (i j : Fin 8) : hypMat i j = hypMat j i := by
  revert i j
  decide

theorem hypMat_diag (i : Fin 8) : hypMat i i = 0 := by
  revert i
  decide

theorem cElt_zero (e : ℕ) : cElt e 0 = qElt e := by rw [cElt, sElt_zero, one_mul]

theorem hp_E_comm (e e' : ℕ) :
    hpElt e 0 * hpElt e' 0 = hpElt e' 0 * hpElt e 0 ∨
      hpElt e 0 * hpElt e' 0 = hpElt 256 0 * (hpElt e' 0 * hpElt e 0) := by
  have hq := CFSG.Certificates.ExtraspecialNF.nf_mul_comm hE_rel hypMat_symm hypMat_diag
    ((e / 256 : ℕ) : ZMod 2) ((e' / 256 : ℕ) : ZMod 2) (bitVec (e % 256)) (bitVec (e' % 256))
  have hP : ∀ a b c : ℕ, (fpElt a 0 * fpElt b 0).1.2 = (fpElt c 0 * (fpElt b 0 * fpElt a 0)).1.2 := by
    intro a b c
    change (fpElt a 0).1.2 * (fpElt b 0).1.2 = (fpElt c 0).1.2 * ((fpElt b 0).1.2 * (fpElt a 0).1.2)
    rw [fpElt_snd_zero, fpElt_snd_zero, fpElt_snd_zero, one_mul, one_mul]
  rcases CFSG.Certificates.ExtraspecialNF.zmod_two_cases
      (CFSG.Certificates.ExtraspecialNF.bil hypMat (bitVec (e % 256)) (bitVec (e' % 256))) with
    h0 | h1
  · left
    rw [h0, ZMod.val_zero, pow_zero, mul_one] at hq
    rw [hpElt_zero_mul, hpElt_zero_mul, mkHP_eq_same (by
      change (fpElt e 0).1.2 * (fpElt e' 0).1.2 = (fpElt e' 0).1.2 * (fpElt e 0).1.2
      rw [fpElt_snd_zero, fpElt_snd_zero])]
    change cElt e 0 * cElt e' 0 = cElt e' 0 * cElt e 0
    rw [cElt_zero, cElt_zero]
    exact hq
  · right
    rw [h1, CFSG.Certificates.ExtraspecialNF.val_one_two, pow_one] at hq
    rw [hpElt_zero_mul, hpElt_zero_mul, show hpElt 256 0 = mkHP (fpElt 256 0) from rfl, ← map_mul,
      mkHP_eq_same (hP e e' 256)]
    change cElt e 0 * cElt e' 0 = cElt 256 0 * (cElt e' 0 * cElt e 0)
    rw [cElt_zero, cElt_zero, cElt_z, show qElt e * qElt e' = qElt e' * qElt e * z0 from hq]
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (Cz.mul_mem (Qsub_le_Cz (qElt_mem e')) (Qsub_le_Cz (qElt_mem e)))

theorem hp_E_center {e : ℕ} (he : e < 512)
    (h : ∀ e' < 512, hpElt e 0 * hpElt e' 0 = hpElt e' 0 * hpElt e 0) : e = 0 ∨ e = 256 := by
  have hc := E_center e he
  simp only [Bool.or_eq_true, Nat.beq_eq, List.any_eq_true, List.mem_range,
    Bool.not_eq_true'] at hc
  rcases hc with (h0 | h0) | ⟨i, hi, hne⟩
  · exact Or.inl h0
  · exact Or.inr h0
  · have hi' : 2 ^ i < 512 := by
      calc 2 ^ i < 2 ^ 9 := Nat.pow_lt_pow_right (by norm_num) (by omega)
        _ = 512 := by norm_num
    exact absurd ((E_comm_iff he hi').1 (h _ hi')) (Nat.ne_of_beq_eq_false hne)

theorem hp_E_misc : hpElt 2 0 * hpElt 2 0 = 1 ∧ hpElt 32 0 * hpElt 32 0 = 1 ∧
    hpElt 2 0 * hpElt 1 0 = hpElt 1 0 * hpElt 2 0 ∧
    hpElt 32 0 * hpElt 1 0 = hpElt 1 0 * hpElt 32 0 ∧
    hpElt 2 0 * hpElt 32 0 ≠ hpElt 32 0 * hpElt 2 0 := by
  have h := E_misc
  simp only [Bool.and_eq_true, Nat.beq_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have sq : ∀ e < 512, mulV (ER e) (ER e) = ER 0 → hpElt e 0 * hpElt e 0 = 1 := by
    intro e he hs
    rw [← hpElt_zero_zero', hpElt_zero_mul, hpElt_eq_mk, mkHP_eq_same (by
      change (fpElt e 0).1.2 * (fpElt e 0).1.2 = (fpElt 0 0).1.2
      rw [fpElt_snd_zero, fpElt_snd_zero, mul_one])]
    have := repK_mul (repK_hp e 0 he) (repK_hp e 0 he)
    rw [show mulV (mulV (SK 0) (QKt e)) (mulV (SK 0) (QKt e)) = ER 0 from hs] at this
    exact repK_fun this (repK_hp 0 0 (by norm_num))
  exact ⟨sq 2 (by norm_num) h1, sq 32 (by norm_num) h2,
    (E_comm_iff (by norm_num) (by norm_num)).2 h3, (E_comm_iff (by norm_num) (by norm_num)).2 h4,
    fun e => Nat.ne_of_beq_eq_false h5 ((E_comm_iff (by norm_num) (by norm_num)).1 e)⟩

end HP

end CertificateChecks.KernelCo2Census

end
