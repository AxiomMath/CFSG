module

public import CFSG.Quasithin.Recognition.St84.Sec6Basic
public import CFSG.Quasithin.Recognition.St84.Sec6ZTools

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86
  CFSG.Quasithin.F6.GoldAmL3T

open scoped Pointwise commutatorElement

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

namespace Setup

variable (X : Setup Γ G)

@[expose] def shift (a : ℤ) : Setup Γ G where
  line :=
    { vert := fun k => X.vert (k + a)
      adj := fun k => by
        simpa [add_assoc, add_comm, add_left_comm] using X.line.adj (k + a)
      nb := fun k => by
        simpa [add_assoc, add_comm, add_left_comm] using X.line.nb (k + a) }
  τ := X.τ
  trans i := by
    simpa [add_assoc, add_comm, add_left_comm] using X.trans (i + a)
  K := X.K
  K_fix := by
    intro k hk i
    change k • X.vert (i + a) = X.vert (i + a)
    exact X.K_fix k hk (i + a)
  τ_norm := X.τ_norm
  hyp := X.hyp
  K_inf := by
    simpa [Setup.edgeSylow, add_comm] using X.K_inf_edgeSylow a
  K_sup := by
    simpa [Setup.edgeSylow, add_comm] using X.K_sup_edgeSylow a

@[simp] theorem shift_vert (a k : ℤ) : (X.shift a).vert k = X.vert (k + a) := rfl

@[simp] theorem shift_τ (a : ℤ) : (X.shift a).τ = X.τ := rfl

@[simp] theorem shift_K (a : ℤ) : (X.shift a).K = X.K := rfl

@[simp] theorem shift_Gi (a i : ℤ) : (X.shift a).Gi i = X.Gi (i + a) := rfl

@[simp] theorem shift_Q (a i : ℤ) : (X.shift a).Q i = X.Q (i + a) := rfl

@[simp] theorem shift_L (a i : ℤ) : (X.shift a).L i = X.L (i + a) := rfl

@[simp] theorem shift_Z (a i : ℤ) : (X.shift a).Z i = X.Z (i + a) := rfl

@[simp] theorem shift_Ki (a i : ℤ) : (X.shift a).Ki i = X.Ki (i + a) := rfl

@[simp] theorem shift_n (a i : ℤ) : (X.shift a).n i = X.n (i + a) := rfl

@[simp] theorem shift_S (a : ℤ) : (X.shift a).S = X.edgeSylow a := by
  unfold Setup.S Setup.edgeSylow
  rw [shift_Gi, shift_Gi]
  congr 2 <;> ring_nf

theorem shift_arcStab (a m r : ℤ) :
    (X.shift a).arcStab m r = X.arcStab (m + a) (r + a) := by
  unfold Setup.arcStab
  congr 1
  ext v
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i + a, ?_, rfl⟩
    rw [Set.mem_Icc] at hi ⊢
    omega
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i - a, ?_, ?_⟩
    · rw [Set.mem_Icc] at hi ⊢
      omega
    · simp

theorem shift_GT (a : ℤ) : (X.shift a).GT = X.GT := by
  unfold Setup.GT
  congr 1
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i + a, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i - a, by simp⟩

@[expose] def swap (X : Setup Γ G) : Setup Γ G := X.reverse.shift (-1)

@[simp] theorem swap_vert (k : ℤ) : X.swap.vert k = X.vert (1 - k) := by
  unfold swap
  rw [shift_vert, reverse_vert]
  congr 1
  ring

@[simp] theorem swap_τ : X.swap.τ = X.τ⁻¹ := by
  unfold swap
  rw [shift_τ, reverse_τ]

@[simp] theorem swap_K : X.swap.K = X.K := by
  unfold swap
  rw [shift_K, reverse_K]

@[simp] theorem swap_Gi (k : ℤ) : X.swap.Gi k = X.Gi (1 - k) := by
  unfold swap
  rw [shift_Gi, reverse_Gi]
  congr 1
  ring

@[simp] theorem swap_Q (k : ℤ) : X.swap.Q k = X.Q (1 - k) := by
  unfold swap
  rw [shift_Q, reverse_Q]
  congr 1
  ring

@[simp] theorem swap_L (k : ℤ) : X.swap.L k = X.L (1 - k) := by
  unfold swap
  rw [shift_L, reverse_L]
  congr 1
  ring

@[simp] theorem swap_Z (k : ℤ) : X.swap.Z k = X.Z (1 - k) := by
  unfold swap
  rw [shift_Z, reverse_Z]
  congr 1
  ring

@[simp] theorem swap_Ki (k : ℤ) : X.swap.Ki k = X.Ki (1 - k) := by
  unfold swap
  rw [shift_Ki, reverse_Ki]
  congr 1
  ring

@[simp] theorem swap_n (k : ℤ) : X.swap.n k = X.n (1 - k) := by
  unfold swap
  rw [shift_n, reverse_n]
  congr 1
  ring

@[simp] theorem swap_S : X.swap.S = X.S := by
  unfold swap
  rw [shift_S]
  simp only [Setup.edgeSylow, Setup.S, reverse_Gi, zero_sub, neg_neg]
  rw [inf_comm]
  congr 2

@[simp] theorem swap_GT : X.swap.GT = X.GT := by
  unfold swap
  rw [shift_GT, reverse_GT]

theorem swap_arcStab (m r : ℤ) :
    X.swap.arcStab m r = X.arcStab (1 - r) (1 - m) := by
  unfold swap
  rw [shift_arcStab, reverse_arcStab]
  congr 2 <;> ring_nf

theorem swap_rightTransAt (m r : ℤ) :
    X.swap.RightTransAt m r ↔ X.LeftTransAt (1 - r) (1 - m) := by
  have h : (1 : ℤ) - (r - 1) = (1 - r) + 1 := by ring
  unfold Setup.RightTransAt Setup.LeftTransAt
  simp only [swap_vert, swap_arcStab, h]

theorem swap_leftTransAt (m r : ℤ) :
    X.swap.LeftTransAt m r ↔ X.RightTransAt (1 - r) (1 - m) := by
  have h1 : (1 : ℤ) - (m + 1) = (1 - m) - 1 := by ring
  unfold Setup.LeftTransAt Setup.RightTransAt
  simp only [swap_vert, swap_arcStab, h1]

private theorem arcStab_ne_GT_of_leftTransAt {m r : ℤ} (hmr : m < r)
    (h : X.LeftTransAt m r) : X.arcStab m r ≠ X.GT := by
  have hL : X.LeftTransAt (1 - (1 - m)) (1 - (1 - r)) := by
    simpa only [show (1 : ℤ) - (1 - m) = m by ring,
      show (1 : ℤ) - (1 - r) = r by ring] using h
  have h' : X.swap.RightTransAt (1 - r) (1 - m) :=
    (X.swap_rightTransAt (1 - r) (1 - m)).mpr hL
  have hne := X.swap.arcStab_ne_GT_of_rightTransAt (m := 1 - r) (r := 1 - m) (by omega) h'
  rw [X.swap_arcStab, X.swap_GT] at hne
  simpa only [show (1 : ℤ) - (1 - m) = m by ring,
    show (1 : ℤ) - (1 - r) = r by ring] using hne

abbrev Qg (r : ℕ) : Subgroup G := pCoreOf 2 (X.arcStab 0 r)

@[expose] def IsLongReg (r : ℕ) : Prop :=
  X.IsMaxReg 0 r ∧ ∀ (c : ℤ) (k : ℕ), r < k → X.arcStab c (c + k) = X.GT

theorem exists_isLongReg (hs : IsSingularity Γ G s) (hodd : Odd s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    ∃ m : ℕ, s - 1 ≤ 2 * m ∧ X.IsLongReg (2 * m) := by
  obtain ⟨m, hle, hmax⟩ := X.exists_isMaxReg hs hodd hX
  refine ⟨m, hle, hmax, ?_⟩
  intro c k hk
  have hkm : 2 * (m : ℤ) < (k : ℤ) := by exact_mod_cast hk
  have hconjGT : ∀ t : ℤ, conjSub (X.τ ^ t) X.GT = X.GT := fun t =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (zpow_mem X.tau_mem_normalizer_GT t)
  rcases Int.even_or_odd' c with ⟨t, hc | hc⟩
  · subst hc
    have h1 : X.arcStab (2 * t) (2 * t + (k : ℤ)) =
        conjSub (X.τ ^ t) (X.arcStab 0 (k : ℤ)) := by
      have h := X.arcStab_add t 0 (k : ℤ)
      rw [show (0 : ℤ) + 2 * t = 2 * t by ring,
        show (k : ℤ) + 2 * t = 2 * t + (k : ℤ) by ring] at h
      exact h
    rw [h1]
    have hgt : X.arcStab 0 (k : ℤ) = X.GT := by
      refine le_antisymm ?_ (X.GT_le_arcStab _ _)
      calc X.arcStab 0 (k : ℤ) ≤ X.arcStab 0 (((2 * m : ℕ) : ℤ) + 1) :=
            X.arcStab_anti le_rfl (by omega)
        _ = X.GT := hmax.2.2.2.1
    rw [hgt, hconjGT t]
  · subst hc
    have h1 : X.arcStab (2 * t + 1) (2 * t + 1 + (k : ℤ)) =
        conjSub (X.τ ^ (t + 1)) (X.arcStab (-1) ((k : ℤ) - 1)) := by
      have h := X.arcStab_add (t + 1) (-1) ((k : ℤ) - 1)
      rw [show (-1 : ℤ) + 2 * (t + 1) = 2 * t + 1 by ring,
        show ((k : ℤ) - 1) + 2 * (t + 1) = 2 * t + 1 + (k : ℤ) by ring] at h
      exact h
    rw [h1]
    have hgt : X.arcStab (-1) ((k : ℤ) - 1) = X.GT := by
      refine le_antisymm ?_ (X.GT_le_arcStab _ _)
      calc X.arcStab (-1) ((k : ℤ) - 1) ≤ X.arcStab (-1) ((2 * m : ℕ) : ℤ) :=
            X.arcStab_anti le_rfl (by omega)
        _ = X.GT := by simpa using hmax.2.2.2.2
    rw [hgt, hconjGT (t + 1)]

structure Sec4Hyp (X : Setup Γ G) (s r : ℕ) : Prop where
  char : CharTwoStab (V := V) (G := G)
  two_le_n : ∀ i : ℤ, 2 ≤ X.n i
  sing : IsSingularity Γ G s
  odd_s : Odd s
  five_le : 5 ≤ s
  odd_GT : Odd (Nat.card X.GT)
  longReg : X.IsLongReg r
  even_r : Even r
  le_r : s - 1 ≤ r
  ends_even : ∀ (a : ℤ) (k : ℕ), s ≤ k →
    (X.RightTransAt a (a + k) → Even (a + k)) ∧ (X.LeftTransAt a (a + k) → Even a)

theorem Sec4Hyp.swap {r : ℕ} (H : X.Sec4Hyp s r) (hr : r + 1 = s) : X.swap.Sec4Hyp s r := by
  have h5 : 5 ≤ s := H.five_le
  have hr1 : 1 ≤ r := by omega
  have hrs : r < s := by omega
  have hlong : X.swap.IsLongReg r := by
    have hreg := X.trans_of_lt H.sing (m := 1 - (r : ℤ)) hr1 hrs
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · exact H.longReg.1.1
    · exact (X.swap_leftTransAt 0 (r : ℤ)).mpr (by simpa using hreg.2)
    · exact (X.swap_rightTransAt 0 (r : ℤ)).mpr (by simpa using hreg.1)
    · rw [X.swap_arcStab, X.swap_GT]
      have h := H.longReg.2 (1 - ((r : ℤ) + 1)) (r + 1) (by omega)
      have e : (1 : ℤ) - ((r : ℤ) + 1) + ((r + 1 : ℕ) : ℤ) = 1 := by
        push_cast
        ring
      rw [e] at h
      simpa using h
    · rw [X.swap_arcStab, X.swap_GT]
      have h := H.longReg.2 (1 - (r : ℤ)) (r + 1) (by omega)
      have e : (1 : ℤ) - (r : ℤ) + ((r + 1 : ℕ) : ℤ) = 2 := by
        push_cast
        ring
      rw [e] at h
      simpa using h
    · intro c k hk
      rw [X.swap_arcStab, X.swap_GT]
      have h := H.longReg.2 (1 - (c + (k : ℤ))) k hk
      have e : (1 - (c + (k : ℤ))) + (k : ℤ) = 1 - c := by ring
      rw [e] at h
      exact h
  refine ⟨H.char, ?_, H.sing, H.odd_s, H.five_le, ?_, hlong, H.even_r, H.le_r, ?_⟩
  · intro i
    rw [X.swap_n]
    exact H.two_le_n _
  · rw [X.swap_GT]
    exact H.odd_GT
  · intro a k hk
    have hkr : r < k := by omega
    have hlt : a < a + (k : ℤ) := by
      have : 5 ≤ k := le_trans H.five_le hk
      omega
    constructor
    · intro hR
      exact absurd (hlong.2 a k hkr)
        (X.swap.arcStab_ne_GT_of_rightTransAt hlt hR)
    · intro hL
      exact absurd (hlong.2 a k hkr)
        (X.swap.arcStab_ne_GT_of_leftTransAt hlt hL)

@[expose] def HasB (i : ℤ) (d : ℕ) : Prop :=
  (∀ j : ℤ, j.natAbs ≤ d → X.Z i ≤ X.Gi (i + j)) ∧
    ¬ X.Z i ≤ X.Gi (i + d + 1) ∧ ¬ X.Z i ≤ X.Gi (i - d - 1)

end Setup

end CFSG.Quasithin.St84
