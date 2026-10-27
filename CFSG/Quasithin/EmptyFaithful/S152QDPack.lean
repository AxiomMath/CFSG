module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3AA6FrameKFA6Pack

public section

namespace CFSG.Quasithin.S152QDPack

open Equiv Finset CFSG.Permutation.FinPack CFSG.LocalAnalysis.RankThreeTheoremC.KFA6Pack

@[expose] def swapCodes6 : List ℕ :=
  [5517825, 5517330, 5505555, 5255700, 274965, 5517600, 5509680, 5321280, 1323600, 5514000,
    5387280, 2372880, 5456400, 3428880, 4534800]

@[expose] noncomputable def centCnt (c : ℕ) : ℕ :=
  cntK (fun q => commLaneK 6 (lo6 q) c) evenCodes6

theorem card_cent_eq (σ : Perm (Fin 6)) :
    Fintype.card {a : alternatingGroup (Fin 6) // (a : Perm (Fin 6)) * σ = σ * (a : Perm (Fin 6))} =
      centCnt (enc σ) := by
  let f : ℕ → Bool := fun d => commLaneK 6 d (enc σ)
  let e : {τ : alternatingGroup (Fin 6) // (τ : Perm (Fin 6)) * σ = σ * τ} ≃
      {g : Perm (Fin 6) // Perm.sign g = 1 ∧ f (enc g) = true} :=
    { toFun := fun τ => ⟨τ.1.1, Perm.mem_alternatingGroup.1 τ.1.2,
        (commLaneK_iff (by norm_num) _ _).2 τ.2⟩
      invFun := fun g => ⟨⟨g.1, Perm.mem_alternatingGroup.2 g.2.1⟩,
        (commLaneK_iff (by norm_num) _ _).1 g.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_subtype, card_even_filter f]
  rfl

theorem check_swaps : allK (fun c => Nat.beq (centCnt c) 24) swapCodes6 = true := by decide +kernel

theorem swap_mem : ∀ i j : Fin 6, i ≠ j → memK (enc (swap i j)) swapCodes6 = true := by
  decide +kernel

@[expose] noncomputable def invB8 (c : ℕ) : Bool :=
  !(Nat.beq (mulK 6 c c) ID6 && !(Nat.beq c ID6)) || Nat.beq (centCnt c) 8

theorem check_inv8 : allK (fun p => invB8 (lo6 p)) evenCodes6 = true := by decide +kernel

theorem card_swap (i j : Fin 6) (hij : i ≠ j) :
    Fintype.card {a : alternatingGroup (Fin 6) //
      (a : Perm (Fin 6)) * swap i j = swap i j * (a : Perm (Fin 6))} = 24 := by
  rw [card_cent_eq]
  exact Nat.eq_of_beq_eq_true (allK_iff.1 check_swaps _ (memK_iff.1 (swap_mem i j hij)))

theorem card_invol (g : alternatingGroup (Fin 6)) (h2 : g * g = 1) (h1 : g ≠ 1) :
    Fintype.card {a : alternatingGroup (Fin 6) //
      (a : Perm (Fin 6)) * (g : Perm (Fin 6)) = (g : Perm (Fin 6)) * (a : Perm (Fin 6))} = 8 := by
  rw [card_cent_eq]
  have h := allK_iff.1 check_inv8 _
    (memK_iff.1 (pc6_mem_even (g : Perm (Fin 6)) (Perm.mem_alternatingGroup.1 g.2)))
  rw [lo6_pc6] at h
  have h' : (!(Nat.beq (mulK 6 (enc (g : Perm (Fin 6))) (enc (g : Perm (Fin 6)))) ID6 &&
      !(Nat.beq (enc (g : Perm (Fin 6))) ID6)) ||
      Nat.beq (centCnt (enc (g : Perm (Fin 6)))) 8) = true := h
  have hsq : Nat.beq (mulK 6 (enc (g : Perm (Fin 6))) (enc (g : Perm (Fin 6)))) ID6 = true := by
    rw [← enc_mul6, ← eq_one_iff]
    have h2' := congrArg Subtype.val h2
    exact h2'
  have hne : Nat.beq (enc (g : Perm (Fin 6))) ID6 = false := by
    cases hb : Nat.beq (enc (g : Perm (Fin 6))) ID6
    · rfl
    · exact absurd (Subtype.ext ((eq_one_iff _).2 hb)) h1
  rw [hsq, hne] at h'
  simp only [Bool.not_false, Bool.and_true, Bool.not_true, Bool.false_or] at h'
  exact Nat.eq_of_beq_eq_true h'

end CFSG.Quasithin.S152QDPack
