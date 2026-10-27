module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35N9AGen1
public import CFSG.Quasithin.EmptyFaithful.SzF53MTab
public import CFSG.Permutation.FinPackPow
public import CFSG.Permutation.FinPackOrb

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.N9K

open Equiv CFSG.Permutation.FinPack CFSG.Quasithin.F53Mod CFSG.Quasithin.F53.Stellmacher.S35.N9

theorem h16 : 5 ≤ 16 := by norm_num

@[expose] def sylL : List (Perm (Fin 5)) :=
  [1, S5g, S5g ^ 2, S5g ^ 3, swap 0 2, S5g * swap 0 2, S5g ^ 2 * swap 0 2, S5g ^ 3 * swap 0 2]

@[expose] def SylC : List ℕ := [274960, 262945, 266290, 270595, 274450, 262435, 266800, 271105]

theorem sylL_enc : sylL.map enc = SylC := by decide +kernel

theorem mem_sylL (s : Perm (Fin 5)) : s ∈ S5SylF ↔ s ∈ sylL := by
  unfold S5SylF
  simp [sylL]

theorem mem_S5SylF_iff (s : Perm (Fin 5)) : s ∈ S5SylF ↔ memK (enc s) SylC = true := by
  rw [mem_sylL, mem_iff_enc h16, sylL_enc, memK_iff]

theorem exists_of_mem_SylC {d : ℕ} (hd : d ∈ SylC) : ∃ s ∈ S5SylF, enc s = d := by
  rw [← sylL_enc, List.mem_map] at hd
  obtain ⟨s, hs, rfl⟩ := hd
  exact ⟨s, (mem_sylL s).2 hs, rfl⟩

@[expose] noncomputable def keyK (c : ℕ) : ℕ :=
  Nat.add (Nat.add (Nat.add (Nat.add (rd c 0) (Nat.mul 5 (rd c 1))) (Nat.mul 25 (rd c 2)))
    (Nat.mul 125 (rd c 3))) (Nat.mul 625 (rd c 4))

theorem mem_reach_iff (gens : List (Perm (Fin 5))) :
    ∀ n (x : Fin 5), x ∈ reach gens n ↔ (orbK 5 (gens.map enc) n 1).testBit x = true := by
  intro n
  induction n with
  | zero =>
    intro x
    change x ∈ ({0} : Finset (Fin 5)) ↔ (1 : ℕ).testBit x = true
    rw [Finset.mem_singleton, Fin.ext_iff, Nat.testBit_one_eq_true_iff_self_eq_zero]
    rfl
  | succ n ih =>
    intro x
    rw [orbK_succ, testBit_stepK, ← ih]
    simp only [reach, step, Finset.mem_union, Finset.mem_biUnion, List.mem_toFinset,
      List.mem_map, exists_exists_and_eq_and]
    refine or_congr Iff.rfl ⟨?_, ?_⟩
    · rintro ⟨s, hs, g, hg, rfl⟩
      exact ⟨g, hg, s, s.isLt, (ih s).1 hs, rd_enc h16 g s⟩
    · rintro ⟨g, hg, i, hi, h1, h2⟩
      refine ⟨⟨i, hi⟩, (ih ⟨i, hi⟩).2 h1, g, hg, Fin.ext ?_⟩
      rw [← h2]
      exact (rd_enc h16 g ⟨i, hi⟩).symm

theorem reach_eq_univ {gens : List (Perm (Fin 5))} {n : ℕ}
    (h : Nat.beq (orbK 5 (gens.map enc) n 1) 31 = true) : reach gens n = Finset.univ := by
  rw [Nat.beq_eq] at h
  refine Finset.eq_univ_of_forall fun x => (mem_reach_iff gens n x).2 ?_
  rw [h]
  revert x
  decide

@[expose] noncomputable def conjK (g gi a : ℕ) : ℕ := mulK 5 (mulK 5 g a) gi

@[expose] noncomputable def condK (A B C : ℕ) : Bool :=
  memK A SylC || (memK B SylC || (memK (mulK 5 (invPK 5 A) B) SylC || (Nat.beq (rd C 4) 4 ||
    Nat.beq (orbK 5 [274450, 266800, A, B, C] 4 1) 31)))

@[expose] noncomputable def coreK (g : ℕ) : Bool :=
  passK (invPK 5 g) fun gi => allK (fun a => passK (conjK g gi a) fun A =>
    allK (fun b => passK (conjK g gi b) fun B =>
      allK (fun c => passK (conjK g gi c) fun C => condK A B C) SylC) SylC) SylC

@[expose] noncomputable def condAK (A B : ℕ) : Bool :=
  !Nat.beq (rd A 4) 4 || (!Nat.beq (rd B 4) 4 || (memK A SylC || (memK B SylC ||
    memK (mulK 5 (invPK 5 A) B) SylC)))

@[expose] noncomputable def coreAK (g : ℕ) : Bool :=
  passK (invPK 5 g) fun gi => allK (fun a => passK (conjK g gi a) fun A =>
    allK (fun b => passK (conjK g gi b) fun B => condAK A B) SylC) SylC

@[expose] noncomputable def repK (g : ℕ) : Bool :=
  allK (fun s => Nat.ble (keyK g) (keyK (mulK 5 g s))) SylC

theorem core_walk : walkK 5 (fun g => !repK g || (coreAK g && coreK g)) 5 0 0 0 = true := by
  decide +kernel

theorem enc_conj (g a : Perm (Fin 5)) :
    enc (g * a * g⁻¹) = conjK (enc g) (invPK 5 (enc g)) (enc a) := by
  rw [conjK, enc_mul h16, enc_mul h16, enc_inv h16]

theorem enc_swap02 : enc (swap (0 : Fin 5) 2) = 274450 := by decide +kernel

theorem enc_swap13 : enc (swap (1 : Fin 5) 3) = 266800 := by decide +kernel

theorem reach_of_condK (A B C : Perm (Fin 5))
    (h : Nat.beq (orbK 5 [274450, 266800, enc A, enc B, enc C] 4 1) 31 = true) :
    reach [swap 0 2, swap 1 3, A, B, C] 4 = Finset.univ := by
  rw [← enc_swap02, ← enc_swap13] at h
  exact reach_eq_univ h

theorem cond_of (A B C : Perm (Fin 5)) (h : condK (enc A) (enc B) (enc C) = true)
    (ha : A ∉ S5SylF) (hb : B ∉ S5SylF) (hab : A⁻¹ * B ∉ S5SylF) (hc : C 4 ≠ 4) :
    reach [swap 0 2, swap 1 3, A, B, C] 4 = Finset.univ := by
  rw [condK.eq_1] at h
  rw [mem_S5SylF_iff, Bool.not_eq_true] at ha hb hab
  rw [enc_mul h16, enc_inv h16] at hab
  rw [ha, hb, hab, Bool.false_or, Bool.false_or, Bool.false_or, Bool.or_eq_true] at h
  rcases h with h | h
  · refine absurd (Fin.ext ?_) hc
    rw [← rd_enc h16 C 4]
    exact Nat.eq_of_beq_eq_true h
  · exact reach_of_condK A B C h

theorem false_of_condAK (A B : Perm (Fin 5)) (h : condAK (enc A) (enc B) = true)
    (ha4 : A 4 = 4) (hb4 : B 4 = 4) (ha : A ∉ S5SylF) (hb : B ∉ S5SylF)
    (hab : A⁻¹ * B ∉ S5SylF) : False := by
  have e : ∀ {C : Perm (Fin 5)}, C 4 = 4 → Nat.beq (rd (enc C) 4) 4 = true := fun {C} hc => by
    rw [Nat.beq_eq]
    exact (rd_enc h16 C 4).trans (congrArg Fin.val hc)
  rw [condAK.eq_1, e ha4, e hb4] at h
  rw [mem_S5SylF_iff, Bool.not_eq_true] at ha hb hab
  rw [enc_mul h16, enc_inv h16] at hab
  rw [ha, hb, hab] at h
  exact absurd h Bool.false_ne_true

end CFSG.Quasithin.F53.Stellmacher.S35.N9K
