module

public import CFSG.RankThree.PartOne.CTP.AsmPair
public import CFSG.RankThree.PartOne.CTP.Frame1214

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG CFSG.RankThree.PartOne CFSG.RankThree
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G] [Finite G]

section Frame

variable {L B K : Subgroup G} {f₀ : ℕ} {b : G} {c : G} {F : LFam L B f₀ b K} {I : Subgroup G}

@[expose] def rotP (i : Fin 4) : Equiv.Perm (Fin 5) := (finRotate 5) ^ (i : ℕ)

omit [Group G] [Finite G] in
theorem rotP_zero (i : Fin 4) : rotP i (e3 0) = Fin.castSucc i := by
  fin_cases i <;> decide

omit [Group G] [Finite G] in
theorem rotP_one (i : Fin 4) : rotP i (e3 1) = Fin.succ i := by
  fin_cases i <;> decide

@[expose] def Mfr (F : LFam L B f₀ b K) (I : Subgroup G) (i : Fin 4) : Subgroup G :=
  Msg F I (rotP i) 0 1

omit [Finite G] in
theorem Mfr_isMP (i : Fin 4) : IsMP F I (Fin.castSucc i) (Fin.succ i) (Mfr F I i) :=
  ⟨rotP i, 0, 1, by decide, rotP_zero i, rotP_one i, rfl⟩

omit [Group G] [Finite G] in
theorem rotP_val_zero (i : Fin 4) : (rotP i (e3 0)).val = i.val := by
  rw [rotP_zero]
  rfl

omit [Group G] [Finite G] in
theorem rotP_val_one (i : Fin 4) : (rotP i (e3 1)).val = i.val + 1 := by
  rw [rotP_one]
  rfl

omit [Group G] [Finite G] in
theorem rotP_val_two (i : Fin 4) (hi : i.val ≤ 2) : (rotP i (e3 2)).val = i.val + 2 := by
  fin_cases i <;> simp at hi <;> decide

omit [Finite G] in
theorem IsMP.of_eq {u v u' v' : Fin 5} {M : Subgroup G} (h : IsMP F I u v M) (hu : u = u')
    (hv : v = v') : IsMP F I u' v' M := by
  subst hu hv
  exact h

omit [Finite G] in
theorem IsMP.msg (σ : Equiv.Perm (Fin 5)) {x y : Fin 3} (hxy : x ≠ y) :
    IsMP F I (σ (e3 x)) (σ (e3 y)) (Msg F I σ x y) :=
  ⟨σ, x, y, hxy, rfl, rfl, rfl⟩

theorem Mfr_sup (A : Asm c F I) {i j : Fin 4} (hij : i.val + 1 = j.val) :
    Mfr F I i ⊔ Mfr F I j = Isg F I (rotP i) := by
  have e : Mfr F I j = Msg F I (rotP i) 1 2 := by
    refine A.Msg_eq_of_pair (by decide) (by decide) ?_ ?_
    · apply Fin.ext
      rw [rotP_val_zero, rotP_val_one]
      omega
    · apply Fin.ext
      rw [rotP_val_one, rotP_val_two i (by omega)]
      omega
  rw [e]
  exact A.adj_sup (rotP i)

theorem Mfr_zero_eq (A : Asm c F I) {σ : Equiv.Perm (Fin 5)} (h0 : σ (e3 0) = 0)
    (h1 : σ (e3 1) = 1) : Mfr F I 0 = Msg F I σ 0 1 :=
  (Mfr_isMP 0).eq A ((IsMP.msg σ (by decide)).of_eq h0 h1)

@[expose] def sigC : Equiv.Perm (Fin 5) := Equiv.swap 2 4 * Equiv.swap 3 4

theorem Mfr_comm (A : Asm c F I) {i j : Fin 4} (hij : i.val + 2 ≤ j.val) :
    ∀ m ∈ Mfr F I j, ∀ n ∈ Mfr F I i, m * n = n * m := by
  have hcase : (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 1 ∧ j = 3) := by
    revert i j
    decide
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  ·
    have hM : Mfr F I 0 = Msg F I sigC 0 1 := Mfr_zero_eq A (by decide) (by decide)
    have hM' : IsMP F I (sigC 3) (sigC 4) (Mfr F I 2) :=
      (Mfr_isMP 2).of_eq (by decide) (by decide)
    exact IsMP.comm_of A (by decide) hM hM'
  ·
    have hM : Mfr F I 0 = Msg F I 1 0 1 := Mfr_zero_eq A (by decide) (by decide)
    have hM' : IsMP F I ((1 : Equiv.Perm (Fin 5)) 3) ((1 : Equiv.Perm (Fin 5)) 4) (Mfr F I 3) :=
      (Mfr_isMP 3).of_eq (by decide) (by decide)
    exact IsMP.comm_of A (by decide) hM hM'
  ·
    have hM : Mfr F I 1 = Msg F I 1 1 2 :=
      (Mfr_isMP 1).eq A ((IsMP.msg 1 (by decide)).of_eq (by decide) (by decide))
    have hM' : IsMP F I ((1 : Equiv.Perm (Fin 5)) 3) ((1 : Equiv.Perm (Fin 5)) 4) (Mfr F I 3) :=
      (Mfr_isMP 3).of_eq (by decide) (by decide)
    exact IsMP.comm_of A (by decide) hM hM'

theorem Mfr_nonadj (A : Asm c F I) {i j : Fin 4} (hij : i ≠ j) (hadj : ¬ chainAdj i j) :
    Mfr F I i ≤ Subgroup.centralizer (Mfr F I j : Set G) ∧ Mfr F I i ⊓ Mfr F I j = ⊥ := by
  have hle : Mfr F I i ≤ Subgroup.centralizer (Mfr F I j : Set G) := by
    have hv : i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val := by
      have h1 : i.val ≠ j.val := fun h => hij (Fin.ext h)
      unfold chainAdj at hadj
      omega
    rcases hv with hv | hv
    · intro x hx
      exact Subgroup.mem_centralizer_iff.mpr fun m hm => Mfr_comm A hv m hm x hx
    · intro x hx
      exact Subgroup.mem_centralizer_iff.mpr fun m hm => (Mfr_comm A hv x hx m hm).symm
  refine ⟨hle, ?_⟩
  have hc := (Mfr_isMP (F := F) (I := I) i).center_trivial A
  rw [eq_bot_iff, ← hc]
  intro x hx
  refine ⟨hx.1, Subgroup.mem_centralizer_iff.mpr fun n hn => ?_⟩
  have := Subgroup.mem_centralizer_iff.mp (hle hn) x hx.2
  exact this.symm

omit [Finite G] in
theorem pair_ne : ∀ i j : Fin 4, i ≠ j →
    ¬ ((Fin.castSucc i = Fin.castSucc j ∧ Fin.succ i = Fin.succ j) ∨
      (Fin.castSucc i = Fin.succ j ∧ Fin.succ i = Fin.castSucc j)) := by
  decide

theorem dvd25_pow5 {x : ℕ} (h : 5 ∣ x + 1) : 25 ∣ x ^ 5 + 1 := by
  have h2 : x % 25 = 4 ∨ x % 25 = 9 ∨ x % 25 = 14 ∨ x % 25 = 19 ∨ x % 25 = 24 := by omega
  apply Nat.dvd_of_mod_eq_zero
  rw [Nat.add_mod, Nat.pow_mod]
  rcases h2 with h2 | h2 | h2 | h2 | h2 <;> rw [h2]

theorem frame_of_asm (A : Asm c F I) {E : Subgroup G} (hBE : B ≤ E)
    (hEcard : Nat.card E = 5 * Nat.card B) (hEgen : E = Subgroup.zpowers c ⊔ B) :
    Frame1214 c E := by
  have hcfg := A.cfg 1
  have h25 : 25 ∣ 2 ^ (5 * f₀) + 1 := by
    rw [mul_comm, pow_mul]
    exact dvd25_pow5 hcfg.dvd5
  refine ⟨5 * f₀, ⨆ i, Mfr F I i, B, Mfr F I, ?_⟩
  refine ⟨by have := hcfg.f_two; omega, dvd_trans (by norm_num) h25, h25,
    fun i => le_iSup (Mfr F I) i, rfl, ?_, fun i => (Mfr_isMP i).model A, ?_, ?_, F.B_elem,
    F.B_card, ?_, hBE, hEcard, hEgen, fun i => (Mfr_isMP i).c_norm A, (Mfr_isMP 0).c_outer A⟩
  ·
    have hl : ∀ i : Fin 4, ∀ u v : Fin 5, Fin.castSucc i = u → Fin.succ i = v →
        B ⊓ F.J u v ≤ ⨆ i, Mfr F I i := by
      intro i u v hu hv
      exact ((Mfr_isMP (F := F) (I := I) i).of_eq hu hv |>.line_le A).trans
        (inf_le_right.trans (le_iSup (Mfr F I) i))
    calc B = (B ⊓ F.J 0 1) ⊔ (B ⊓ F.J 1 2) ⊔ (B ⊓ F.J 2 3) ⊔ (B ⊓ F.J 3 4) := F.B_gen
      _ ≤ _ := sup_le (sup_le (sup_le (hl 0 0 1 (by decide) (by decide))
        (hl 1 1 2 (by decide) (by decide))) (hl 2 2 3 (by decide) (by decide)))
        (hl 3 3 4 (by decide) (by decide))
  ·
    intro i j hij hadj
    exact Mfr_nonadj A hij hadj
  ·
    rintro i j (hij | hji)
    · rw [Mfr_sup A hij]
      exact Or.inr (A.facts (rotP i)).I_model
    · rw [sup_comm, Mfr_sup A hji]
      exact Or.inr (A.facts (rotP j)).I_model
  ·
    refine ⟨fun i => (Mfr_isMP i).ct_single A, fun i j hij => ?_⟩
    have := (Mfr_isMP (F := F) (I := I) i).ct_pair A (Mfr_isMP (F := F) (I := I) j)
      (pair_ne i j hij)
    rw [this]
    norm_num

end Frame

end CFSG.RankThree.PartOne.CTP
