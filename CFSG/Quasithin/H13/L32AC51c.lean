module

public import CFSG.Quasithin.H13.L32AC51b

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.ComponentClassification
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.QuasithinUnique.Vol2Native.A312L (bigBlockHom bigBlockHom_surjective bigBlockHom_coe
  blockLeft_of_cut blockRight_of_cut perfectCore_eq_bot_of_small mem_unitriangular_of_blocks
  blkAt_zero)
open CFSG.QuasithinUnique.Vol2Native.L239.L52 (blkSLTwo blkSLTwo_coe blkAt_one_eq_one)

namespace Lin

variable {n : ℕ}

abbrev par2 (n i j : ℕ) : Subgroup (SLn n) :=
  flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {i, j})

theorem mem_cuts2 {i j c : ℕ} :
    c ∈ Set.Icc 1 (n - 1) \ {i, j} ↔ 1 ≤ c ∧ c ≤ n - 1 ∧ c ≠ i ∧ c ≠ j := by
  simp only [Set.mem_sdiff, Set.mem_Icc, Set.mem_insert_iff, Set.mem_singleton_iff, not_or,
    and_assoc]

theorem par_le_par2 (i j : ℕ) : par n i ≤ par2 n i j :=
  BinaryParabolic.flagStabilizer_anti fun c hc => by
    rw [mem_cuts2] at hc
    exact ⟨⟨hc.1, hc.2.1⟩, fun h => hc.2.2.1 (Set.mem_singleton_iff.mp h)⟩

theorem refl_mem_par2 (i : ℕ) {j : ℕ} (hj : 1 ≤ j) (hjn : j < n) :
    reflection n (ZMod 2) j hj hjn ∈ par2 n i j :=
  ((subflag_stabilizer_generation _).2.2 j hj hjn).mpr fun h => (mem_cuts2.mp h).2.2.2 rfl

theorem isSolvable_par2 (hn : 1 ≤ n) {i j : ℕ} (hij : i + 2 ≤ j ∨ j + 2 ≤ i) :
    Group.IsSolvable ↥(par2 n i j) := by
  rw [isSolvable_iff_perfectCore_eq_bot]
  refine perfectCore_eq_bot_of_small card_zmod_two hn fun a m ham _ _ hno => ?_
  by_contra hm
  have h1 := hno (a + 1)
  have h2 := hno (a + 2)
  rw [mem_cuts2] at h1 h2
  omega

theorem left3 {i : ℕ} (hi : 1 ≤ i) (hin : i + 2 ≤ n) :
    i - 1 = 0 ∨ i - 1 ∈ Set.Icc 1 (n - 1) \ {i, i + 1} := by
  rcases Nat.eq_zero_or_pos (i - 1) with h | h
  · exact Or.inl h
  · right
    rw [mem_cuts2]
    omega

theorem right3 {i : ℕ} (hi : 1 ≤ i) (hin : i + 2 ≤ n) :
    i - 1 + 3 = n ∨ i - 1 + 3 ∈ Set.Icc 1 (n - 1) \ {i, i + 1} := by
  rcases Nat.lt_or_ge (i + 2) n with h | h
  · right
    rw [mem_cuts2]
    omega
  · left
    omega

theorem no3 {i : ℕ} (hi : 1 ≤ i) :
    ∀ c ∈ Set.Icc 1 (n - 1) \ {i, i + 1}, ¬ (i - 1 < c ∧ c < i - 1 + 3) := by
  intro c hc
  rw [mem_cuts2] at hc
  omega

@[expose] noncomputable def blk3 {i : ℕ} (hi : 1 ≤ i) (hin : i + 2 ≤ n) :
    ↥(par2 n i (i + 1)) →* SLn 3 :=
  blkSLTwo card_zmod_two (par2 n i (i + 1)) (i - 1) 3 (by omega)
    (blockLeft_of_cut 3 (left3 hi hin)) (blockRight_of_cut (right3 hi hin))

theorem blk3_coe {i : ℕ} (hi : 1 ≤ i) (hin : i + 2 ≤ n) (x : ↥(par2 n i (i + 1))) :
    ((blk3 hi hin x : SLn 3) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      CFSG.QuasithinUnique.Vol2Native.A312L.blkAt (i - 1) 3 (by omega)
        ((x : SLn n) : Matrix (Fin n) (Fin n) (ZMod 2)) := rfl

theorem blk3_surjective {i : ℕ} (hi : 1 ≤ i) (hin : i + 2 ≤ n) :
    Function.Surjective (blk3 (n := n) hi hin) := by
  intro s
  obtain ⟨x, hx⟩ := bigBlockHom_surjective (K := ZMod 2) card_zmod_two (n := n) (by omega)
    (le_refl 3) (left3 hi hin) (right3 hi hin) (no3 hi) s
  refine ⟨⟨x, perfectCore_le _ x.2⟩, Subtype.ext ?_⟩
  rw [blk3_coe, ← hx, bigBlockHom_coe]

theorem blk3_ker {i : ℕ} (hi : 1 ≤ i) (hin : i + 2 ≤ n) (x : ↥(par2 n i (i + 1)))
    (hx : blk3 hi hin x = 1) : (x : SLn n) ∈ unitriangular n (ZMod 2) := by
  refine mem_unitriangular_of_blocks x.2 fun a m h ha hb hno => ?_
  rcases Nat.lt_or_ge m 2 with hm | hm
  · rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl
    · exact blkAt_zero a h _
    · exact blkAt_one_eq_one card_zmod_two _ a h (blockLeft_of_cut 1 ha) (blockRight_of_cut hb) x
  ·
    have h1 := hno (a + 1)
    rw [mem_cuts2] at h1
    have hai : a = i - 1 := by
      rcases ha with ha | ha
      · omega
      · rw [mem_cuts2] at ha
        omega
    subst hai
    have hm3 : m = 3 := by
      have h3 := hno (i - 1 + 3)
      rw [mem_cuts2] at h3
      rcases hb with hb | hb
      · omega
      · rw [mem_cuts2] at hb
        omega
    subst hm3
    have := congrArg (fun s : SLn 3 => (s : Matrix (Fin 3) (Fin 3) (ZMod 2))) hx
    simpa [blk3_coe] using this

end Lin

end CFSG.Quasithin.H13.L32A.C
