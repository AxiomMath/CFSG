module

public import CFSG.Quasithin.Background.ShultG53TotPack
public import CFSG.Quasithin.H13.A6G5
public import CFSG.Quasithin.H13.A6S13834F

public section

namespace CFSG.Quasithin.ShultG53.IdentPack

open CFSG.Permutation.FinPack CFSG.Quasithin.ShultG53.Pack CFSG.Quasithin.ShultG53.TotPack
  CFSG.Quasithin.H13.A6
  CFSG.Quasithin.RonanG51 Equiv Matrix

@[expose] noncomputable def cAK (c : ℕ) : Bool := Nat.beq (mulK 6 c 4530945) (mulK 6 4530945 c)

@[expose] def g5K (c : ℕ) : Bool :=
  (Nat.beq (rd c 4) 4 && Nat.beq (rd c 5) 5) || (Nat.beq (rd c 4) 5 && Nat.beq (rd c 5) 4)

@[expose] noncomputable def lineK (L : List ℕ) (c : ℕ) : Bool :=
  allK (fun x => !memK x L || memK (hK c x) L) codes16

@[expose] def lineA : List ℕ := [0, 1, 4, 5]

@[expose] def lineB : List ℕ := [0, 1, 12, 13]

theorem enc_iota0 : enc iota0 = 4530945 := by decide +kernel

theorem mem_cA6_iff (σ : Perm (Fin 6)) (hs : Perm.sign σ = 1) :
    σ ∈ cA6 ↔ cAK (enc σ) = true := by
  change (σ * iota0 = iota0 * σ ∧ Perm.sign σ = 1) ↔ _
  rw [and_iff_left hs, cAK, Nat.beq_eq, ← enc_iota0, ← enc_mul (by norm_num),
    ← enc_mul (by norm_num)]
  exact ⟨congrArg enc, enc_inj (by norm_num)⟩

theorem g5_pair : ∀ a b : Fin 6, (a = 4 ∧ b = 5 ∨ a = 5 ∧ b = 4) ↔
    ((Nat.beq a 4 && Nat.beq b 5) || (Nat.beq a 5 && Nat.beq b 4)) = true := by
  decide +kernel

theorem mem_g5G1_iff (σ : Perm (Fin 6)) (hs : Perm.sign σ = 1) :
    σ ∈ g5G1 ↔ g5K (enc σ) = true := by
  change (Perm.sign σ = 1 ∧ (σ 4 = 4 ∧ σ 5 = 5 ∨ σ 4 = 5 ∧ σ 5 = 4)) ↔ _
  rw [and_iff_right hs, g5_pair, g5K]
  have h4 : rd (enc σ) 4 = σ 4 := rd_enc (by norm_num) σ 4
  have h5 : rd (enc σ) 5 = σ 5 := rd_enc (by norm_num) σ 5
  rw [h4, h5]

theorem lineA_iff : ∀ v : V4, predLine4a v ↔ memK (vc v) lineA = true := by decide +kernel

theorem lineB_iff : ∀ v : V4, predLine4b v ↔ memK (vc v) lineB = true := by decide +kernel

theorem line_iff {P : V4 → Prop} {L : List ℕ} (hP : ∀ v, P v ↔ memK (vc v) L = true)
    {M : Matrix (Fin 4) (Fin 4) (ZMod 2)} {c : ℕ} (hM : ∀ v, vc (M *ᵥ v) = hK c (vc v)) :
    (∀ y, P y → P (M *ᵥ y)) ↔ lineK L c = true := by
  rw [lineK, allK_iff, ← forall_vc (P := fun x => (!memK x L || memK (hK c x) L) = true)]
  refine forall_congr' fun v => ?_
  rw [hP, hP, hM, Bool.or_eq_true, Bool.not_eq_true', ← Bool.not_eq_true]
  exact imp_iff_not_or

theorem check_Hx0 :
    allK (fun p => Nat.beq (hK (lo6 p) 5) 5 == g5K (lo6 p)) evenCodes6 = true := by
  decide +kernel

theorem check_Hx1 :
    allK (fun q => Nat.beq (hK (tR q) 1) 1 == cAK (lo6 (pR q))) evenTot = true := by
  decide +kernel

theorem check_Hl0 : allK (fun p => lineK lineA (lo6 p) == cAK (lo6 p)) evenCodes6 = true := by
  decide +kernel

theorem check_Hl1 :
    allK (fun q => lineK lineB (tR q) == g5K (lo6 (pR q))) evenTot = true := by
  decide +kernel

theorem vc_e5 : vc (![1, 0, 1, 0] : V4) = 5 := by decide

theorem vc_e1 : vc (![1, 0, 0, 0] : V4) = 1 := by decide

theorem Hx0_iff_code (σ : Perm (Fin 6)) (hs : Perm.sign σ = 1) :
    (Matrix.mulVec (Rm 0 σ) (![1, 0, 1, 0] : V4) = ![1, 0, 1, 0] ↔ σ ∈ g5G1) := by
  have h := allK_iff.1 check_Hx0 _ (memK_iff.1 (pc6_mem_even σ hs))
  rw [lo6_pc6, beq_iff_eq] at h
  rw [mem_g5G1_iff σ hs, ← h, Nat.beq_eq, vc_eq_iff, vc_Rm0, vc_e5]

theorem Hx1_iff_code (σ : Perm (Fin 6)) (hs : Perm.sign σ = 1) :
    (Matrix.mulVec (Rm 1 σ) (![1, 0, 0, 0] : V4) = ![1, 0, 0, 0] ↔ σ ∈ cA6) := by
  obtain ⟨q, hq, hp, ht⟩ := exists_tot σ hs
  have h := allK_iff.1 check_Hx1 q hq
  rw [hp, ht, lo6_pc6, beq_iff_eq] at h
  rw [mem_cA6_iff σ hs, ← h, Nat.beq_eq, vc_eq_iff, vc_Rm1, vc_e1]

theorem Hl0_iff_code (σ : Perm (Fin 6)) (hs : Perm.sign σ = 1) :
    ((∀ y : V4, predLine4a y → predLine4a (Matrix.mulVec (Rm 0 σ) y)) ↔ σ ∈ cA6) := by
  have h := allK_iff.1 check_Hl0 _ (memK_iff.1 (pc6_mem_even σ hs))
  rw [lo6_pc6, beq_iff_eq] at h
  rw [mem_cA6_iff σ hs, ← h]
  exact line_iff lineA_iff (vc_Rm0 σ)

theorem Hl1_iff_code (σ : Perm (Fin 6)) (hs : Perm.sign σ = 1) :
    ((∀ y : V4, predLine4b y → predLine4b (Matrix.mulVec (Rm 1 σ) y)) ↔ σ ∈ g5G1) := by
  obtain ⟨q, hq, hp, ht⟩ := exists_tot σ hs
  have h := allK_iff.1 check_Hl1 q hq
  rw [hp, ht, lo6_pc6, beq_iff_eq] at h
  rw [mem_g5G1_iff σ hs, ← h]
  exact line_iff lineB_iff (vc_Rm1 σ)

@[expose] def Wg : List (Perm (Fin 6)) :=
  [swap 0 1 * swap 1 2, swap 1 2 * swap 2 3, swap 0 1 * swap 4 5, swap 2 3 * swap 4 5]

@[expose] def Wc : List (Perm (Fin 6)) :=
  [swap 0 2 * swap 2 4 * swap 1 3 * swap 3 5, swap 0 1 * swap 2 3, swap 2 4 * swap 3 5,
    swap 0 2 * swap 1 3]

theorem check_Wg : allK g5K (Wg.map enc) = true := by decide +kernel

theorem check_Wc : allK cAK (Wc.map enc) = true := by decide +kernel

theorem Wg_mem : ∀ σ ∈ Wg, Perm.sign σ = 1 ∧ g5K (enc σ) = true := by
  intro σ hσ
  refine ⟨?_, allK_iff.1 check_Wg _ (List.mem_map.2 ⟨σ, hσ, rfl⟩)⟩
  simp only [Wg, List.mem_cons, List.not_mem_nil, or_false] at hσ
  rcases hσ with rfl | rfl | rfl | rfl <;> exact sign_swap2 _ _ _ _ (by decide) (by decide)

theorem Wc_mem : ∀ σ ∈ Wc, Perm.sign σ = 1 ∧ cAK (enc σ) = true := by
  intro σ hσ
  refine ⟨?_, allK_iff.1 check_Wc _ (List.mem_map.2 ⟨σ, hσ, rfl⟩)⟩
  simp only [Wc, List.mem_cons, List.not_mem_nil, or_false] at hσ
  rcases hσ with rfl | rfl | rfl | rfl
  · exact sign_swap4 _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)
  all_goals exact sign_swap2 _ _ _ _ (by decide) (by decide)

theorem check_nofix_g5 : allK (fun x => Nat.beq x 0 ||
    anyK (fun c => !Nat.beq (hK (totK c) x) x) (Wg.map enc)) codes16 = true := by
  decide +kernel

theorem check_nofix_cA : allK (fun x => Nat.beq x 0 ||
    anyK (fun c => !Nat.beq (hK c x) x) (Wc.map enc)) codes16 = true := by
  decide +kernel

theorem vc_zero : vc (0 : V4) = 0 := by decide

theorem beq_vc_zero {m : V4} (hm : m ≠ 0) : Nat.beq (vc m) 0 = false := by
  rw [Bool.eq_false_iff, Ne, Nat.beq_eq]
  exact fun e => hm (vc_inj _ _ (e.trans vc_zero.symm))

theorem nofix_g5G1_code : ∀ m : V4, m ≠ 0 →
    ∃ σ : Perm (Fin 6), σ ∈ g5G1 ∧ Matrix.mulVec (Rm 1 σ) m ≠ m := by
  intro m hm
  have h := allK_iff.1 check_nofix_g5 _ (vc_mem m)
  rw [beq_vc_zero hm, Bool.false_or, anyK_iff] at h
  obtain ⟨c, hc, hmv⟩ := h
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hc
  obtain ⟨hs, hg⟩ := Wg_mem σ hσ
  refine ⟨σ, (mem_g5G1_iff σ hs).2 hg, fun e => ?_⟩
  rw [vc_eq_iff, vc_Rm1] at e
  rw [e] at hmv
  simp at hmv

theorem nofix_cA6_code : ∀ m : V4, m ≠ 0 →
    ∃ σ : Perm (Fin 6), σ ∈ cA6 ∧ Matrix.mulVec (Rm 0 σ) m ≠ m := by
  intro m hm
  have h := allK_iff.1 check_nofix_cA _ (vc_mem m)
  rw [beq_vc_zero hm, Bool.false_or, anyK_iff] at h
  obtain ⟨c, hc, hmv⟩ := h
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hc
  obtain ⟨hs, hg⟩ := Wc_mem σ hσ
  refine ⟨σ, (mem_cA6_iff σ hs).2 hg, fun e => ?_⟩
  rw [vc_eq_iff, vc_Rm0] at e
  rw [e] at hmv
  simp at hmv

end CFSG.Quasithin.ShultG53.IdentPack
