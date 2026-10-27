module

public import CFSG.Quasithin.H13.VolIAltCover
public import CFSG.Permutation.FinPackWalk

public section

namespace CFSG.Quasithin.H13.VolI.A7WordsK

open Equiv CFSG.Permutation.FinPack

@[expose] def andB (x y : Bool) : Bool := Bool.rec (motive := fun _ => Bool) false y x

@[expose] def dig (w k : ℕ) : ℕ := Nat.mod (Nat.div w k) 3

@[expose] def pkd (e c q d : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) q c (Nat.beq d 1)) e
    (Nat.beq d 0)

@[expose] noncomputable def wordK (w : ℕ) : ℕ :=
  mulK 7 (mulK 7 (mulK 7 (mulK 7 (mulK 7 (pkd 106181136 106180641 106180866 (dig w 1))
    (pkd 106181136 106054416 106112016 (dig w 3))) (pkd 106181136 106180641 106180866 (dig w 9)))
    (pkd 106181136 106054416 106112016 (dig w 27))) (pkd 106181136 106180641 106180866 (dig w 81)))
    (pkd 106181136 106054416 106112016 (dig w 243))

@[expose] def findK (c : ℕ) (L : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun e _ r => Bool.rec (motive := fun _ => ℕ) r
    (Nat.land e 1023) (Nat.beq (Nat.shiftRight e 10) c)) L

@[expose] def tbl : List ℕ :=
  [108452696215, 108452972614, 108453202994, 108456643704, 108457119823, 108457411623,
    108460806197, 108461098026, 108461574278, 108465014797, 108465245206, 108465521668,
    108515626105, 108515856464, 108516132904, 108523475096, 108524273735, 108524473392,
    108527683627, 108528144435, 108528697476, 108531846167, 108532383758, 108532598789,
    108582457494, 108582995013, 108583210033, 108586404986, 108587126862, 108587434025,
    108594745396, 108595052588, 108595774597, 108598969356, 108599184405, 108599721987,
    108649580560, 108649795609, 108650333191, 108653482010, 108654034961, 108654495752,
    108657705999, 108657905688, 108658704390, 108666046865, 108666323343, 108666553744,
    108716657741, 108716934210, 108717164702, 108720605251, 108721081419, 108721373340,
    108724767820, 108725059652, 108725535901, 108728976385, 108729206786, 108729483264]

@[expose] noncomputable def wordQ (c : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) true (Nat.beq (wordK (findK c tbl)) c)
    (andB (Nat.beq (rd c 5) 5) (andB (Nat.beq (rd c 6) 6) (evenK 7 c)))

theorem check : walkK 7 wordQ 7 0 0 0 = true := by decide +kernel

theorem hn7 : (7 : ℕ) ≤ 16 := by norm_num

@[expose] def pwA (g : ↥(alternatingGroup (Fin 7))) (d : ℕ) : ↥(alternatingGroup (Fin 7)) :=
  if d = 0 then 1 else if d = 1 then g else g * g

@[expose] def wordA (g₁ g₂ : ↥(alternatingGroup (Fin 7))) (w : ℕ) : ↥(alternatingGroup (Fin 7)) :=
  pwA g₁ (dig w 1) * pwA g₂ (dig w 3) * pwA g₁ (dig w 9) * pwA g₂ (dig w 27) * pwA g₁ (dig w 81) *
    pwA g₂ (dig w 243)

theorem pwA_mem (g : ↥(alternatingGroup (Fin 7))) (d : ℕ) : pwA g d ∈ [1, g, g * g] := by
  unfold pwA
  split_ifs <;> simp

theorem isWord6_wordA (g₁ g₂ : ↥(alternatingGroup (Fin 7))) (w : ℕ) :
    IsWord6 g₁ g₂ (wordA g₁ g₂ w) :=
  ⟨_, pwA_mem g₁ _, _, pwA_mem g₂ _, _, pwA_mem g₁ _, _, pwA_mem g₂ _, _, pwA_mem g₁ _, _,
    pwA_mem g₂ _, rfl⟩

theorem beq_false_of_ne {d m : ℕ} (h : d ≠ m) : Nat.beq d m = false := by
  cases hb : Nat.beq d m
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem enc_pwA (g : ↥(alternatingGroup (Fin 7))) (d : ℕ) :
    enc ((pwA g d : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7)) =
      pkd (enc (1 : Perm (Fin 7))) (enc (g : Perm (Fin 7)))
        (enc ((g : Perm (Fin 7)) * (g : Perm (Fin 7)))) d := by
  unfold pwA pkd
  by_cases h0 : d = 0
  · subst h0
    rfl
  · rw [if_neg h0, beq_false_of_ne h0]
    by_cases h1 : d = 1
    · subst h1
      rfl
    · rw [if_neg h1, beq_false_of_ne h1]
      rfl

theorem enc_wordA {g₁ g₂ : ↥(alternatingGroup (Fin 7))}
    (h1 : enc (g₁ : Perm (Fin 7)) = 106180641)
    (h11 : enc ((g₁ : Perm (Fin 7)) * (g₁ : Perm (Fin 7))) = 106180866)
    (h2 : enc (g₂ : Perm (Fin 7)) = 106054416)
    (h22 : enc ((g₂ : Perm (Fin 7)) * (g₂ : Perm (Fin 7))) = 106112016)
    (he : enc (1 : Perm (Fin 7)) = 106181136) (w : ℕ) :
    enc ((wordA g₁ g₂ w : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7)) = wordK w := by
  unfold wordA
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul,
    enc_mul hn7, enc_mul hn7, enc_mul hn7, enc_mul hn7, enc_mul hn7, enc_pwA, enc_pwA, enc_pwA,
    enc_pwA, enc_pwA, enc_pwA, h1, h11, h2, h22, he]
  rfl

theorem words {g₁ g₂ : ↥(alternatingGroup (Fin 7))}
    (h1 : enc (g₁ : Perm (Fin 7)) = 106180641)
    (h11 : enc ((g₁ : Perm (Fin 7)) * (g₁ : Perm (Fin 7))) = 106180866)
    (h2 : enc (g₂ : Perm (Fin 7)) = 106054416)
    (h22 : enc ((g₂ : Perm (Fin 7)) * (g₂ : Perm (Fin 7))) = 106112016)
    (σ : ↥(alternatingGroup (Fin 7))) (h5 : (σ : Perm (Fin 7)) 5 = 5)
    (h6 : (σ : Perm (Fin 7)) 6 = 6) : IsWord6 g₁ g₂ σ := by
  have he : enc (1 : Perm (Fin 7)) = 106181136 := by decide +kernel
  have hz := walkK_sound check (σ : Perm (Fin 7))
  have c5 : Nat.beq (rd (enc (σ : Perm (Fin 7))) 5) 5 = true := by
    rw [Nat.beq_eq]
    have h := rd_enc hn7 (σ : Perm (Fin 7)) 5
    rw [h5] at h
    exact h
  have c6 : Nat.beq (rd (enc (σ : Perm (Fin 7))) 6) 6 = true := by
    rw [Nat.beq_eq]
    have h := rd_enc hn7 (σ : Perm (Fin 7)) 6
    rw [h6] at h
    exact h
  have ce : evenK 7 (enc (σ : Perm (Fin 7))) = true :=
    (sign_eq_one_iff_evenK hn7 _).1 (Perm.mem_alternatingGroup.1 σ.2)
  unfold wordQ at hz
  rw [c5, c6, ce] at hz
  have hw : Nat.beq (wordK (findK (enc (σ : Perm (Fin 7))) tbl)) (enc (σ : Perm (Fin 7))) =
      true := hz
  rw [Nat.beq_eq, ← enc_wordA h1 h11 h2 h22 he] at hw
  rw [Subtype.ext (enc_inj hn7 hw).symm]
  exact isWord6_wordA g₁ g₂ _

end CFSG.Quasithin.H13.VolI.A7WordsK

end
