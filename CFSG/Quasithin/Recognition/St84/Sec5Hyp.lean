module

public import CFSG.Quasithin.Recognition.St84.Sec4Local

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86
  CFSG.Quasithin.F6.GoldAmL3T CFSG.GH74.QTGen4.DSGen4

open scoped Pointwise commutatorElement

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s n₀ : ℕ}

namespace Setup

@[expose] def mirror1 (X : Setup Γ G) : Setup Γ G := X.reverse.shift (-2)

@[simp] theorem mirror1_vert (X : Setup Γ G) (k : ℤ) :
    X.mirror1.vert k = X.vert (2 - k) := by
  rw [mirror1, shift_vert, reverse_vert]
  congr 1
  ring

@[simp] theorem mirror1_τ (X : Setup Γ G) : X.mirror1.τ = X.τ⁻¹ := by
  rw [mirror1, shift_τ, reverse_τ]

@[simp] theorem mirror1_K (X : Setup Γ G) : X.mirror1.K = X.K := by
  rw [mirror1, shift_K, reverse_K]

@[simp] theorem mirror1_Gi (X : Setup Γ G) (k : ℤ) :
    X.mirror1.Gi k = X.Gi (2 - k) := by
  rw [mirror1, shift_Gi, reverse_Gi]
  congr 1
  ring

@[simp] theorem mirror1_Q (X : Setup Γ G) (k : ℤ) :
    X.mirror1.Q k = X.Q (2 - k) := by
  rw [mirror1, shift_Q, reverse_Q]
  congr 1
  ring

@[simp] theorem mirror1_L (X : Setup Γ G) (k : ℤ) :
    X.mirror1.L k = X.L (2 - k) := by
  rw [mirror1, shift_L, reverse_L]
  congr 1
  ring

@[simp] theorem mirror1_Z (X : Setup Γ G) (k : ℤ) :
    X.mirror1.Z k = X.Z (2 - k) := by
  rw [mirror1, shift_Z, reverse_Z]
  congr 1
  ring

@[simp] theorem mirror1_Ki (X : Setup Γ G) (k : ℤ) :
    X.mirror1.Ki k = X.Ki (2 - k) := by
  rw [mirror1, shift_Ki, reverse_Ki]
  congr 1
  ring

@[simp] theorem mirror1_n (X : Setup Γ G) (k : ℤ) :
    X.mirror1.n k = X.n (2 - k) := by
  rw [mirror1, shift_n, reverse_n]
  congr 1
  ring

@[simp] theorem mirror1_GT (X : Setup Γ G) : X.mirror1.GT = X.GT := by
  rw [mirror1, shift_GT, reverse_GT]

structure Sec5Hyp (Y : Setup Γ G) (s n₀ : ℕ) : Prop where
  char : CharTwoStab (V := V) (G := G)
  two_le : 2 ≤ n₀
  n_zero : Y.n 0 = n₀
  n_one : Y.n 1 = 1
  sing : IsSingularity Γ G s
  odd_s : Odd s
  five_le : 5 ≤ s
  odd_GT : Odd (Nat.card Y.GT)

theorem Sec5Hyp.shift_two {Y : Setup Γ G} (H : Y.Sec5Hyp s n₀) (m : ℤ) :
    (Y.shift (2 * m)).Sec5Hyp s n₀ := by
  refine ⟨H.char, H.two_le, ?_, ?_, H.sing, H.odd_s, H.five_le, ?_⟩
  · rw [Setup.shift_n]
    exact (Y.n_add m 0).trans H.n_zero
  · rw [Setup.shift_n]
    exact (Y.n_add m 1).trans H.n_one
  · rw [Setup.shift_GT]
    exact H.odd_GT

theorem Sec5Hyp.reverse {Y : Setup Γ G} (H : Y.Sec5Hyp s n₀) :
    Y.reverse.Sec5Hyp s n₀ := by
  refine ⟨H.char, H.two_le, ?_, ?_, H.sing, H.odd_s, H.five_le, ?_⟩
  · rw [Setup.reverse_n]
    simpa using H.n_zero
  · rw [Setup.reverse_n, Setup.n_neg_one]
    exact H.n_one
  · rw [Setup.reverse_GT]
    exact H.odd_GT

theorem Sec5Hyp.mirror1 {Y : Setup Γ G} (H : Y.Sec5Hyp s n₀) :
    Y.mirror1.Sec5Hyp s n₀ := by
  have h := H.reverse.shift_two (-1)
  simpa [Setup.mirror1, show (2 : ℤ) * (-1) = -2 by norm_num] using h

@[expose] def IsMaxRegLen (Y : Setup Γ G) (r : ℕ) : Prop :=
  (∃ a : ℤ, Y.LeftTransAt a (a + (r : ℤ)) ∧ Y.RightTransAt a (a + (r : ℤ))) ∧
    ∀ (c : ℤ) (k : ℕ), r < k → Y.arcStab c (c + (k : ℤ)) = Y.GT

theorem IsMaxRegLen.unique {Y : Setup Γ G} {r r' : ℕ} (h : Y.IsMaxRegLen r)
    (h' : Y.IsMaxRegLen r') : r = r' := by
  rcases lt_trichotomy r r' with hlt | heq | hgt
  · obtain ⟨a, -, hR⟩ := h'.1
    have hEq : Y.arcStab a (a + (r' : ℤ)) = Y.GT := h.2 a r' hlt
    exact absurd hEq
      (Y.arcStab_ne_GT_of_rightTransAt (m := a) (r := a + (r' : ℤ)) (by omega) hR)
  · exact heq
  · obtain ⟨a, -, hR⟩ := h.1
    have hEq : Y.arcStab a (a + (r : ℤ)) = Y.GT := h'.2 a r hgt
    exact absurd hEq
      (Y.arcStab_ne_GT_of_rightTransAt (m := a) (r := a + (r : ℤ)) (by omega) hR)

private theorem exists_arcStab_neg_eq_GT (Y : Setup Γ G) :
    ∃ m₀ : ℕ, Y.arcStab (-(m₀ : ℤ)) (m₀ : ℤ) = Y.GT := by
  classical
  let f : ℕ → ℕ := fun m => Nat.card ↥(Y.arcStab (-(m : ℤ)) (m : ℤ))
  have hfanti : ∀ m, f (m + 1) ≤ f m := by
    intro m
    haveI : Finite ↥(Y.arcStab (-(((m + 1 : ℕ)) : ℤ)) (((m + 1 : ℕ)) : ℤ)) :=
      finite_of_le_stabilizer Y.hyp (H := Y.arcStab (-(((m + 1 : ℕ)) : ℤ)) (((m + 1 : ℕ)) : ℤ))
        (Y.arcStab_le_Gi_of_between (k := 0) (by omega) (by omega))
    haveI : Finite ↥(Y.arcStab (-(m : ℤ)) (m : ℤ)) :=
      finite_of_le_stabilizer Y.hyp (H := Y.arcStab (-(m : ℤ)) (m : ℤ))
        (Y.arcStab_le_Gi_of_between (k := 0) (by omega) (by omega))
    exact Subgroup.card_le_of_le (Y.arcStab_anti (by omega) (by omega))
  have hex : ∃ n, ∃ m, f m = n := ⟨f 0, 0, rfl⟩
  set nmin := Nat.find hex with hnmindef
  obtain ⟨m₀, hm₀⟩ := hnmindef.symm ▸ Nat.find_spec hex
  have hmin : ∀ m, nmin ≤ f m := by
    intro m
    by_contra hlt
    push Not at hlt
    exact Nat.find_min hex hlt ⟨m, rfl⟩
  have hcardconst : ∀ k, m₀ ≤ k → f k = nmin := by
    intro k hk
    have h1 : nmin ≤ f k := hmin k
    have h2 : f k ≤ f m₀ :=
      Nat.le_induction (m := m₀) (P := fun l _ => f l ≤ f m₀) le_rfl
        (fun l _ ih => (hfanti l).trans ih) k hk
    omega
  have hconst : ∀ k : ℕ, m₀ ≤ k →
      Y.arcStab (-(k : ℤ)) (k : ℤ) = Y.arcStab (-(m₀ : ℤ)) (m₀ : ℤ) := by
    intro k hk
    have hfk : Nat.card ↥(Y.arcStab (-(k : ℤ)) (k : ℤ)) = nmin := by
      have := hcardconst k hk
      simpa using this
    have hfm : Nat.card ↥(Y.arcStab (-(m₀ : ℤ)) (m₀ : ℤ)) = nmin := by
      have := hm₀
      simpa using this
    have hcard : Nat.card ↥(Y.arcStab (-(k : ℤ)) (k : ℤ)) =
        Nat.card ↥(Y.arcStab (-(m₀ : ℤ)) (m₀ : ℤ)) := by rw [hfk, hfm]
    haveI : Finite ↥(Y.arcStab (-(k : ℤ)) (k : ℤ)) :=
      finite_of_le_stabilizer Y.hyp (H := Y.arcStab (-(k : ℤ)) (k : ℤ))
        (Y.arcStab_le_Gi_of_between (k := 0) (by omega) (by omega))
    haveI : Finite ↥(Y.arcStab (-(m₀ : ℤ)) (m₀ : ℤ)) :=
      finite_of_le_stabilizer Y.hyp (H := Y.arcStab (-(m₀ : ℤ)) (m₀ : ℤ))
        (Y.arcStab_le_Gi_of_between (k := 0) (by omega) (by omega))
    have hle : Y.arcStab (-(k : ℤ)) (k : ℤ) ≤ Y.arcStab (-(m₀ : ℤ)) (m₀ : ℤ) :=
      Y.arcStab_anti (by omega) (by omega)
    exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  have hAeq : Y.arcStab (-(m₀ : ℤ)) (m₀ : ℤ) = Y.GT := by
    refine le_antisymm ?_ (Y.GT_le_arcStab _ _)
    intro g hg
    rw [Setup.GT, Fan86.mem_fixSet]
    rintro v ⟨i, rfl⟩
    have hk : ∀ k : ℕ, m₀ ≤ k → g ∈ Y.arcStab (-(k : ℤ)) (k : ℤ) := by
      intro k hk; rw [hconst k hk]; exact hg
    let k : ℕ := max m₀ i.natAbs
    have hmem := hk k (le_max_left _ _)
    have hi1 : i ≤ (k : ℤ) := by
      have h2 : (i.natAbs : ℤ) ≤ (k : ℤ) := by exact_mod_cast le_max_right m₀ i.natAbs
      have h3 : i ≤ (i.natAbs : ℤ) := Int.le_natAbs
      omega
    have hi2 : -(k : ℤ) ≤ i := by
      have h2 : (i.natAbs : ℤ) ≤ (k : ℤ) := by exact_mod_cast le_max_right m₀ i.natAbs
      have h4 : -i ≤ ((-i).natAbs : ℤ) := Int.le_natAbs
      rw [Int.natAbs_neg] at h4
      omega
    exact (Fan86.mem_fixSet.mp hmem) (Y.vert i) ⟨i, by rw [Set.mem_Icc]; exact ⟨hi2, hi1⟩, rfl⟩
  exact ⟨m₀, hAeq⟩

private theorem exists_forall_arcStab_eq_GT (Y : Setup Γ G) :
    ∃ N : ℕ, ∀ (a : ℤ) (ℓ : ℕ), N ≤ ℓ → Y.arcStab a (a + ℓ) = Y.GT := by
  obtain ⟨m₀, hAeq⟩ := Y.exists_arcStab_neg_eq_GT
  refine ⟨2 * m₀ + 1, ?_⟩
  have hbig : ∀ (a : ℤ) (ℓ : ℕ), 2 * m₀ + 1 ≤ ℓ → Y.arcStab a (a + ℓ) = Y.GT := by
    intro a ℓ hℓ
    refine le_antisymm ?_ (Y.GT_le_arcStab a (a + ℓ))
    have hconj : ∀ k : ℤ, Y.arcStab (-(m₀ : ℤ) + 2 * k) ((m₀ : ℤ) + 2 * k) = Y.GT := by
      intro k
      rw [Y.arcStab_add k (-(m₀ : ℤ)) (m₀ : ℤ), hAeq]
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (zpow_mem Y.tau_mem_normalizer_GT k)
    have hcast : (m₀ : ℤ) + 1 ≤ (ℓ : ℤ) := by
      have h1 : m₀ + 1 ≤ ℓ := by omega
      exact_mod_cast h1
    obtain ⟨j, hj | hj⟩ := Int.even_or_odd' (a + (m₀ : ℤ))
    · have hj1 : a ≤ -(m₀ : ℤ) + 2 * j := by linarith
      have hj2 : (m₀ : ℤ) + 2 * j ≤ a + ℓ := by linarith
      rw [← hconj j]
      exact Y.arcStab_anti hj1 hj2
    · have hj1 : a ≤ -(m₀ : ℤ) + 2 * (j + 1) := by linarith
      have hj2 : (m₀ : ℤ) + 2 * (j + 1) ≤ a + ℓ := by linarith
      rw [← hconj (j + 1)]
      exact Y.arcStab_anti hj1 hj2
  exact hbig

private theorem regular_of_ne_GT_of_succ_eq_GT (Y : Setup Γ G) {a : ℤ} {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) (ha : Y.arcStab a (a + ℓ) ≠ Y.GT)
    (h1 : ∀ c : ℤ, Y.arcStab c (c + ((ℓ + 1 : ℕ) : ℤ)) = Y.GT) :
    Y.LeftTransAt a (a + ℓ) ∧ Y.RightTransAt a (a + ℓ) := by
  have hright : Y.RightTransAt a (a + (ℓ : ℤ)) := by
    by_contra hsing
    have hPleQ : pCoreOf 2 (Y.arcStab a (a + (ℓ : ℤ))) ≤ Y.Q (a + (ℓ : ℤ)) :=
      Y.pCoreOf_arcStab_le_Q_right a (a + (ℓ : ℤ)) (by omega) hsing
    have hKA : Y.K ≤ Y.arcStab a (a + (ℓ : ℤ)) :=
      Y.K_le_GT.trans (Y.GT_le_arcStab _ _)
    have hAle : Y.arcStab a (a + (ℓ : ℤ)) ≤
        Y.Gi (a + (ℓ : ℤ) - 1) ⊓ Y.Gi (a + (ℓ : ℤ) - 1 + 1) := by
      rw [show a + (ℓ : ℤ) - 1 + 1 = a + (ℓ : ℤ) by ring]
      exact le_inf (Y.arcStab_le_Gi_of_between (by omega) (by omega))
        (Y.arcStab_le_Gi_of_between (by omega) (by omega))
    obtain ⟨-, hAdecomp⟩ := Y.pCoreOf_eq_inf_edgeSylow (a + (ℓ : ℤ) - 1) hKA hAle
    have hA_le_Gb1 : Y.arcStab a (a + (ℓ : ℤ)) ≤ Y.Gi (a + (ℓ : ℤ) + 1) := by
      rw [← hAdecomp]
      exact sup_le (Y.K_le_Gi (a + (ℓ : ℤ) + 1))
        (hPleQ.trans ((Y.Q_le_Gi_adj (a + (ℓ : ℤ))).trans inf_le_right))
    have hGT : Y.arcStab a (a + ((ℓ + 1 : ℕ) : ℤ)) = Y.GT := h1 a
    have hAleGT : Y.arcStab a (a + (ℓ : ℤ)) ≤ Y.GT := by
      rw [← hGT, Y.arcStab_eq_inf (show a ≤ a + ((ℓ + 1 : ℕ) : ℤ) by omega)]
      refine le_inf (Y.arcStab_le_Gi_left (by omega)) ?_
      rw [show a + ((ℓ + 1 : ℕ) : ℤ) = a + (ℓ : ℤ) + 1 by push_cast; ring]
      exact hA_le_Gb1
    exact ha (le_antisymm hAleGT (Y.GT_le_arcStab _ _))
  have hleft : Y.LeftTransAt a (a + (ℓ : ℤ)) := by
    by_contra hsing
    have hPleQ : pCoreOf 2 (Y.arcStab a (a + (ℓ : ℤ))) ≤ Y.Q a :=
      Y.pCoreOf_arcStab_le_Q_left a (a + (ℓ : ℤ)) (by omega) hsing
    have hKA : Y.K ≤ Y.arcStab a (a + (ℓ : ℤ)) :=
      Y.K_le_GT.trans (Y.GT_le_arcStab _ _)
    have hAle : Y.arcStab a (a + (ℓ : ℤ)) ≤ Y.Gi a ⊓ Y.Gi (a + 1) :=
      le_inf (Y.arcStab_le_Gi_left (by omega))
        (Y.arcStab_le_Gi_of_between (by omega) (by omega))
    obtain ⟨-, hAdecomp⟩ := Y.pCoreOf_eq_inf_edgeSylow a hKA hAle
    have hA_le_Gam1 : Y.arcStab a (a + (ℓ : ℤ)) ≤ Y.Gi (a - 1) := by
      rw [← hAdecomp]
      exact sup_le (Y.K_le_Gi (a - 1))
        (hPleQ.trans ((Y.Q_le_Gi_adj a).trans inf_le_left))
    have hGT : Y.arcStab (a - 1) ((a - 1) + ((ℓ + 1 : ℕ) : ℤ)) = Y.GT := h1 (a - 1)
    have hAleGT : Y.arcStab a (a + (ℓ : ℤ)) ≤ Y.GT := by
      rw [← hGT, Y.arcStab_eq_inf (show a - 1 ≤ (a - 1) + ((ℓ + 1 : ℕ) : ℤ) by omega)]
      exact le_inf hA_le_Gam1 (by
        rw [show (a - 1) + ((ℓ + 1 : ℕ) : ℤ) = a + (ℓ : ℤ) by push_cast; ring]
        exact Y.arcStab_le_Gi_right (by omega))
    exact ha (le_antisymm hAleGT (Y.GT_le_arcStab _ _))
  exact ⟨hleft, hright⟩

private theorem even_of_regular_of_sing_le (Y : Setup Γ G) (hsing : IsSingularity Γ G s)
    (hodd : Odd s) {a : ℤ} {ℓ : ℕ} (hsℓ : s ≤ ℓ) (hL : Y.LeftTransAt a (a + ℓ))
    (hR : Y.RightTransAt a (a + ℓ)) : Even ℓ := by
  have hs1 : 1 ≤ s := hsing.1
  have hℓEven : Even ℓ := by
    by_cases hge : s ≤ ℓ
    · obtain ⟨o, _, hreg⟩ := exists_odd_orbit Y.hyp.isTree Y.hyp.adj_smul
        (fun v x y hx hy => Y.hyp.locTrans hx hy) Y.hyp.edgeTrans Y.hyp.preservesParts
        hsing hodd
      have hPL : LeftTransitive Γ G (Y.line.arc a ℓ).vert 0 ℓ :=
        (Y.leftTransitive_arc_iff a ℓ).mpr hL
      have hPR : RightTransitive Γ G (Y.line.arc a ℓ).vert 0 ℓ :=
        (Y.rightTransitive_arc_iff a (by omega)).mpr hR
      have hre := hreg ℓ hsℓ (Y.line.arc a ℓ) ⟨hPL, hPR⟩
      have hda : Even (Γ.dist o (Y.vert a)) := by simpa [Line.arc] using hre.1
      have hdb : Even (Γ.dist o (Y.vert (a + (ℓ : ℤ)))) := by
        simpa [Line.arc] using hre.2
      have htri := IsTree.even_dist_add_dist_add_dist Y.hyp.isTree o
        (Y.vert a) (Y.vert (a + (ℓ : ℤ)))
      have hd2 : Even (Γ.dist (Y.vert a) (Y.vert (a + (ℓ : ℤ)))) := by
        obtain ⟨i, hi⟩ := hda
        obtain ⟨j, hj⟩ := hdb
        obtain ⟨k, hk⟩ := htri
        exact ⟨k - i - j, by omega⟩
      have hdist : Γ.dist (Y.vert a) (Y.vert (a + (ℓ : ℤ))) = ℓ := by
        have h' := Line.dist_eq Y.hyp.isTree Y.line (i := a) (j := a + (ℓ : ℤ)) (by omega)
        rw [show a + (ℓ : ℤ) - a = (ℓ : ℤ) by ring] at h'
        simpa using h'
      rwa [hdist] at hd2
    · have hℓeq : ℓ = s - 1 := by omega
      obtain ⟨k, hk⟩ := hodd
      rw [hℓeq]
      exact ⟨k, by omega⟩
  exact hℓEven

theorem exists_isMaxRegLen (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    ∃ r : ℕ, s - 1 ≤ r ∧ Even r ∧ Y.IsMaxRegLen r := by
  have hs : IsSingularity Γ G s := H.sing
  have hfive : 5 ≤ s := H.five_le
  classical
  obtain ⟨N, hN⟩ := Y.exists_forall_arcStab_eq_GT
  let P : ℕ → Prop := fun ℓ => ∃ a : ℤ, Y.arcStab a (a + ℓ) ≠ Y.GT
  have hbdd : ∀ ℓ : ℕ, P ℓ → ℓ ≤ N := by
    rintro ℓ ⟨a, ha⟩
    by_contra h
    exact ha (hN a ℓ (by omega))
  have hPinit : P (s - 1) := by
    refine ⟨0, ?_⟩
    rw [show (0 : ℤ) + (((s - 1 : ℕ) : ℤ)) = ((s - 1 : ℕ) : ℤ) from zero_add _]
    intro hEq
    have hR : Y.RightTransAt 0 (((s - 1 : ℕ)) : ℤ) := by
      have h := (hs.2.1 (s - 1) (by omega) (by omega) (Y.line.arc 0 (s - 1))).2
      have h' := (Y.rightTransitive_arc_iff 0 (by omega)).mp h
      simpa using h'
    exact Y.arcStab_ne_GT_of_rightTransAt (m := 0) (r := (((s - 1 : ℕ)) : ℤ)) (by omega) hR hEq
  let ℓ : ℕ := Nat.findGreatest P N
  have hPℓ : P ℓ := Nat.findGreatest_spec (hbdd (s - 1) hPinit) hPinit
  have hmaxP : ∀ n, ℓ < n → n ≤ N → ¬ P n := (Nat.findGreatest_eq_iff.1 rfl).2.2
  have hPℓ1 : ¬ P (ℓ + 1) := by
    by_cases h : ℓ + 1 ≤ N
    · exact hmaxP (ℓ + 1) (by omega) h
    · rintro ⟨a, ha⟩
      exact absurd (hbdd (ℓ + 1) ⟨a, ha⟩) (by omega)
  obtain ⟨a, ha⟩ := hPℓ
  have hℓs : s - 1 ≤ ℓ := Nat.le_findGreatest (hbdd (s - 1) hPinit) hPinit
  have h1 : ∀ c : ℤ, Y.arcStab c (c + ((ℓ + 1 : ℕ) : ℤ)) = Y.GT := by
    intro c
    by_contra h
    exact hPℓ1 ⟨c, h⟩
  obtain ⟨hleft, hright⟩ :=
    Y.regular_of_ne_GT_of_succ_eq_GT (a := a) (ℓ := ℓ) (by omega) ha h1
  have hℓEven : Even ℓ := by
    by_cases hge : s ≤ ℓ
    · exact Y.even_of_regular_of_sing_le H.sing H.odd_s hge hleft hright
    · have hℓeq : ℓ = s - 1 := by omega
      obtain ⟨k, hk⟩ := H.odd_s
      rw [hℓeq]
      exact ⟨k, by omega⟩
  refine ⟨ℓ, hℓs, hℓEven, ⟨a, hleft, hright⟩, ?_⟩
  intro c k hk
  by_contra hne
  have hPk : P k := ⟨c, hne⟩
  by_cases hk2 : k ≤ N
  · exact hmaxP k hk hk2 hPk
  · exact hne (hN c k (by omega))

theorem dist_vert_natAbs (Y : Setup Γ G) (i : ℤ) :
    Γ.dist (Y.vert 0) (Y.vert i) = i.natAbs := by
  rcases Int.eq_nat_or_neg i with ⟨n, rfl | rfl⟩
  · rw [Line.dist_eq Y.hyp.isTree Y.line (show (0 : ℤ) ≤ n by omega)]; simp
  · rw [SimpleGraph.dist_comm,
      Line.dist_eq Y.hyp.isTree Y.line (show (-(n : ℤ)) ≤ 0 by omega)]; simp

theorem odd_dist_vert_iff (Y : Setup Γ G) (i : ℤ) :
    Odd (Γ.dist (Y.vert 0) (Y.vert i)) ↔ Odd i := by
  rw [Y.dist_vert_natAbs]
  exact Int.natAbs_odd

theorem exists_regular_parity (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    ∃ e : ZMod 2, ∀ (a : ℤ) (k : ℕ), s ≤ k → Y.LeftTransAt a (a + (k : ℤ)) →
      Y.RightTransAt a (a + (k : ℤ)) → (a : ZMod 2) = e := by
  obtain ⟨o, ho, hreg⟩ := exists_odd_orbit Y.hyp.isTree Y.hyp.adj_smul
    (fun v x y hx hy => Y.hyp.locTrans hx hy) Y.hyp.edgeTrans Y.hyp.preservesParts
    H.sing H.odd_s
  refine ⟨-(Γ.dist o (Y.vert 0) : ℕ), ?_⟩
  intro a k hsk hL hR
  have hk1 : 1 ≤ k := le_trans H.sing.1 hsk
  have hPL : LeftTransitive Γ G (Y.line.arc a k).vert 0 k :=
    (Y.leftTransitive_arc_iff a k).mpr hL
  have hPR : RightTransitive Γ G (Y.line.arc a k).vert 0 k :=
    (Y.rightTransitive_arc_iff a hk1).mpr hR
  have hregk := hreg k hsk (Y.line.arc a k) ⟨hPL, hPR⟩
  have hda : Even (Γ.dist o (Y.vert a)) := by
    simpa [Line.arc] using hregk.1
  have htri := IsTree.even_dist_add_dist_add_dist Y.hyp.isTree o (Y.vert 0) (Y.vert a)
  have htri' : ((Γ.dist o (Y.vert 0) + Γ.dist (Y.vert 0) (Y.vert a) +
      Γ.dist o (Y.vert a) : ℕ) : ZMod 2) = 0 := by
    rw [ZMod.natCast_eq_zero_iff_even]
    exact htri
  have hda' : ((Γ.dist o (Y.vert a) : ℕ) : ZMod 2) = 0 := by
    rw [ZMod.natCast_eq_zero_iff_even]
    exact hda
  push_cast at htri'
  rw [hda', Y.dist_vert_natAbs a, ZMod.natAbs_mod_two, add_zero] at htri'
  rw [eq_neg_iff_add_eq_zero]
  calc (a : ZMod 2) + ((Γ.dist o (Y.vert 0) : ℕ) : ZMod 2)
      = ((Γ.dist o (Y.vert 0) : ℕ) : ZMod 2) + (a : ZMod 2) := add_comm _ _
    _ = 0 := htri'

theorem regular_of_pCoreOf (Y : Setup Γ G) {a b : ℤ} (hab : a < b)
    (hr : ¬ pCoreOf 2 (Y.arcStab a b) ≤ Y.Gi (b + 1))
    (hl : ¬ pCoreOf 2 (Y.arcStab a b) ≤ Y.Gi (a - 1)) :
    Y.LeftTransAt a b ∧ Y.RightTransAt a b := by
  constructor
  · by_contra h
    exact hl ((Y.pCoreOf_arcStab_le_Q_left a b hab h).trans
      ((Y.Q_le_Gi_adj a).trans inf_le_left))
  · by_contra h
    exact hr ((Y.pCoreOf_arcStab_le_Q_right a b hab h).trans
      ((Y.Q_le_Gi_adj b).trans inf_le_right))

@[expose] def J2Arc (Y : Setup Γ G) : Prop :=
  (Y.LeftTransAt 1 7 ∧ Y.RightTransAt 1 7) ∧
    ¬ (Y.LeftTransAt 0 6 ∧ Y.RightTransAt 0 6)

private theorem card_pCoreOf_eq_pow_of_odd (Y : Setup Γ G) (i : ℤ) {A H : Subgroup G}
    (hKA : Y.K ≤ A) (hA : A ≤ Y.Gi i ⊓ Y.Gi (i + 1)) (hH : Odd (Nat.card H))
    {j : ℕ} (hcard : Nat.card A = 2 ^ j * Nat.card H) :
    Nat.card (pCoreOf 2 A) = 2 ^ j := by
  classical
  have hKcard := Y.card_eq_card_K_mul_card_pCoreOf i hKA hA
  haveI : Finite ↥A := finite_of_le_stabilizer Y.hyp (hA.trans inf_le_left)
  haveI : Finite ↥(pCoreOf 2 A) :=
    Finite.of_injective (Subgroup.inclusion (CFSG.LieType.BorelTits.pCoreOf_le 2 A))
      (Subgroup.inclusion_injective (CFSG.LieType.BorelTits.pCoreOf_le 2 A))
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (pCoreOf_isPGroup' A)
  have hKodd : Odd (Nat.card Y.K) := Y.odd_card_K
  have hseq : Nat.card Y.K * 2 ^ m = Nat.card H * 2 ^ j := by
    rw [mul_comm (Nat.card H) (2 ^ j), ← hcard, hKcard, hm]
  have hmj : m = j := by
    rcases lt_trichotomy m j with hlt | heq | hgt
    · exfalso
      have hd : Nat.card Y.K = Nat.card H * 2 ^ (j - m) := by
        have h' : Nat.card Y.K * 2 ^ m = (Nat.card H * 2 ^ (j - m)) * 2 ^ m := by
          rw [hseq, mul_assoc, pow_sub_mul_pow 2 hlt.le]
        exact Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num) m) h'
      have heven : Even (Nat.card H * 2 ^ (j - m)) := by
        rw [even_iff_two_dvd]
        exact dvd_mul_of_dvd_right (pow_dvd_pow 2 (by omega : 1 ≤ j - m)) _
      rw [hd] at hKodd
      exact (Nat.not_even_iff_odd.mpr hKodd) heven
    · exact heq
    · exfalso
      have hd : Nat.card H = Nat.card Y.K * 2 ^ (m - j) := by
        have h' : (Nat.card Y.K * 2 ^ (m - j)) * 2 ^ j = Nat.card H * 2 ^ j := by
          rw [mul_assoc, pow_sub_mul_pow 2 hgt.le]
          exact hseq
        exact (Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num) j) h').symm
      have heven : Even (Nat.card Y.K * 2 ^ (m - j)) := by
        rw [even_iff_two_dvd]
        exact dvd_mul_of_dvd_right (pow_dvd_pow 2 (by omega : 1 ≤ m - j)) _
      rw [hd] at hH
      exact (Nat.not_even_iff_odd.mpr hH) heven
  rw [hm, hmj]

private theorem card_pCoreOf_eq_one_of_arcStab_eq_GT (Y : Setup Γ G)
    (hodd : Odd (Nat.card Y.GT)) {a b : ℤ} (h : Y.arcStab a b = Y.GT) :
    Nat.card (pCoreOf 2 (Y.arcStab a b)) = 1 := by
  rw [h]
  have h2 : IsPGroup 2 (pCoreOf 2 Y.GT) := pCoreOf_isPGroup' Y.GT
  rcases h2.card_eq_or_dvd with h' | h'
  · exact h'
  · exact absurd (h'.trans (Subgroup.card_dvd_of_le
      (CFSG.LieType.BorelTits.pCoreOf_le 2 Y.GT))) hodd.not_two_dvd_nat

private theorem not_rightTransAt_of_regular_six (Y : Setup Γ G)
    (hs : IsSingularity Γ G 5) {a : ℤ}
    (h : Y.LeftTransAt a (a + 6) ∧ Y.RightTransAt a (a + 6)) :
    ¬ Y.RightTransAt a (a + 5) := by
  intro hR5
  obtain ⟨o, ho, hreg⟩ := exists_odd_orbit Y.hyp.isTree Y.hyp.adj_smul
    (fun v x y hx hy => Y.hyp.locTrans hx hy) Y.hyp.edgeTrans Y.hyp.preservesParts
    hs (by norm_num : Odd 5)
  have hPL : LeftTransitive Γ G (Y.line.arc a 6).vert 0 6 :=
    (Y.leftTransitive_arc_iff a 6).mpr h.1
  have hPR : RightTransitive Γ G (Y.line.arc a 6).vert 0 6 :=
    (Y.rightTransitive_arc_iff a (by norm_num)).mpr h.2
  have hre := hreg 6 (by norm_num) (Y.line.arc a 6) ⟨hPL, hPR⟩
  have hda : Even (Γ.dist o (Y.vert a)) := by simpa [Line.arc] using hre.1
  have hodd5 : Odd (Γ.dist o ((Y.line.arc a 5).vert 5)) := by
    have h' : Odd (Γ.dist o (Y.vert a) + 5) := by
      obtain ⟨k, hk⟩ := hda
      exact ⟨k + 2, by omega⟩
    have h'' : Odd (Γ.dist o ((Y.line.arc a 5).vert 0) + 5) := by
      simpa [Line.arc] using h'
    have hodd5' := (St84.odd_dist_vert_iff Y.hyp.isTree (Y.line.arc a 5) o).mpr h''
    simpa [Line.arc] using hodd5'
  exact (ho 5 (by norm_num) (Y.line.arc a 5)).1 hodd5
    ((Y.rightTransitive_arc_iff a (by norm_num)).mpr hR5)

private theorem arcStab_succ_eq_of_not_rightTransAt (Y : Setup Γ G) {a b : ℤ}
    (hab : a < b) (hsing : ¬ Y.RightTransAt a b) :
    Y.arcStab a b = Y.arcStab a (b + 1) := by
  apply le_antisymm
  · have hA : Y.arcStab a b ≤ Y.Gi a ⊓ Y.Gi (a + 1) :=
      le_inf (Y.arcStab_le_Gi_left hab)
        (Y.arcStab_le_Gi_of_between (by omega) hab)
    have hKA : Y.K ≤ Y.arcStab a b :=
      Y.K_le_GT.trans (Y.GT_le_arcStab a b)
    obtain ⟨-, hdecomp⟩ := Y.pCoreOf_eq_inf_edgeSylow a hKA hA
    rw [← hdecomp]
    refine sup_le ?_ ?_
    · exact Y.K_le_GT.trans (Y.GT_le_arcStab a (b + 1))
    · intro x hx
      have hxb : x ∈ Y.arcStab a b :=
        CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx
      rw [Y.arcStab_eq_inf (show a ≤ b + 1 by omega)]
      exact ⟨Y.arcStab_le_Gi_left (by omega) hxb,
        (Y.Q_le_Gi_adj b
          (Y.pCoreOf_arcStab_le_Q_right a b hab hsing hx)).2⟩
  · exact Y.arcStab_anti le_rfl (by omega)

private theorem card_pCoreOf_arcStab_of_succ_eq_GT (Y : Setup Γ G)
    (hodd : Odd (Nat.card Y.GT)) {a b : ℤ} (hab : a < b) (hR : Y.RightTransAt a b)
    (hGT : Y.arcStab a (b + 1) = Y.GT) :
    Nat.card (pCoreOf 2 (Y.arcStab a b)) = 2 ^ Y.n b := by
  have hrel : (Y.arcStab a (b + 1)).relIndex (Y.arcStab a b) = 2 ^ Y.n b :=
    Y.relIndex_arcStab_succ a b hab hR
  have hcardA : Nat.card (Y.arcStab a b) = 2 ^ Y.n b * Nat.card Y.GT := by
    have hcard := Subgroup.relIndex_mul_card
      (H := Y.arcStab a (b + 1)) (K := Y.arcStab a b)
    have hinf : Y.GT ⊓ Y.arcStab a b = Y.GT :=
      inf_eq_left.mpr (Y.GT_le_arcStab a b)
    rw [hrel, hGT, hinf] at hcard
    exact hcard.symm
  have hKA : Y.K ≤ Y.arcStab a b := Y.K_le_GT.trans (Y.GT_le_arcStab a b)
  have hA : Y.arcStab a b ≤ Y.Gi a ⊓ Y.Gi (a + 1) :=
    le_inf (Y.arcStab_le_Gi_left hab) (Y.arcStab_le_Gi_of_between (by omega) hab)
  exact Y.card_pCoreOf_eq_pow_of_odd a hKA hA hodd hcardA

theorem card_S_of_isMaxRegLen_four (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hr : Y.IsMaxRegLen 4) (h5 : s = 5) :
    Nat.card Y.S = 4 * 2 ^ (2 * n₀) := by
  subst h5
  have hGT : Y.arcStab 0 (((5 : ℕ) : ℤ)) = Y.GT := by
    have h := hr.2 0 5 (by norm_num)
    simpa using h
  have hpc : Nat.card (pCoreOf 2 (Y.arcStab 0 (((5 : ℕ) : ℤ)))) = 1 :=
    Y.card_pCoreOf_eq_one_of_arcStab_eq_GT H.odd_GT hGT
  rw [Y.card_S_eq_prod H.sing, hpc, mul_one]
  have hprod : (∏ r ∈ Finset.Icc (1 : ℕ) 4, (2 : ℕ) ^ Y.n (r : ℤ)) =
      4 * 2 ^ (2 * n₀) := by
    rw [show Finset.Icc (1 : ℕ) 4 = Finset.Icc 1 (2 * 2) from rfl,
      Y.prod_Icc_two_mul, H.n_zero, H.n_one,
      show 2 * (n₀ + 1) = 2 * n₀ + 2 by ring, pow_add]
    norm_num
    ring
  exact hprod

theorem card_S_of_isMaxRegLen_six_reg (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hr : Y.IsMaxRegLen 6) (h5 : s = 5)
    (h06 : Y.LeftTransAt 0 6 ∧ Y.RightTransAt 0 6) :
    Nat.card Y.S = 4 * 2 ^ (3 * n₀) := by
  subst h5
  have hsing5 : ¬ Y.RightTransAt 0 (((5 : ℕ) : ℤ)) :=
    Y.not_rightTransAt_of_regular_six H.sing (by simpa using h06)
  have hArc56 : Y.arcStab 0 (((5 : ℕ) : ℤ)) = Y.arcStab 0 (((6 : ℕ) : ℤ)) := by
    simpa using Y.arcStab_succ_eq_of_not_rightTransAt (a := 0) (b := 5) (by norm_num) hsing5
  have hn6 : Y.n (((6 : ℕ) : ℤ)) = n₀ := by
    rw [show (((6 : ℕ) : ℤ)) = 0 + 2 * 3 by norm_num, Y.n_add, H.n_zero]
  have hGT7 : Y.arcStab 0 (((7 : ℕ) : ℤ)) = Y.GT := by
    have h := hr.2 0 7 (by norm_num)
    simpa using h
  have hpc6 : Nat.card (pCoreOf 2 (Y.arcStab 0 (((6 : ℕ) : ℤ)))) = 2 ^ n₀ := by
    have h := Y.card_pCoreOf_arcStab_of_succ_eq_GT H.odd_GT (a := 0) (b := 6)
      (by norm_num) h06.2 hGT7
    rw [show (6 : ℤ) = ((6 : ℕ) : ℤ) by norm_num, hn6] at h
    exact h
  have hpc : Nat.card (pCoreOf 2 (Y.arcStab 0 (((5 : ℕ) : ℤ)))) = 2 ^ n₀ := by
    rw [hArc56]
    exact hpc6
  rw [Y.card_S_eq_prod H.sing, hpc]
  have hprod : (∏ r ∈ Finset.Icc (1 : ℕ) 4, (2 : ℕ) ^ Y.n (r : ℤ)) =
      4 * 2 ^ (2 * n₀) := by
    rw [show Finset.Icc (1 : ℕ) 4 = Finset.Icc 1 (2 * 2) from rfl,
      Y.prod_Icc_two_mul, H.n_zero, H.n_one,
      show 2 * (n₀ + 1) = 2 * n₀ + 2 by ring, pow_add]
    norm_num
    ring
  rw [hprod]
  rw [show 4 * 2 ^ (2 * n₀) * 2 ^ n₀ = 4 * 2 ^ (3 * n₀) by
    rw [mul_assoc, ← pow_add]
    congr 1
    ring]

theorem card_S_of_isMaxRegLen_six_J2Arc (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hr : Y.IsMaxRegLen 6) (hc : Y.J2Arc) (h5 : s = 5) :
    Nat.card Y.S = 8 * 2 ^ (2 * n₀) := by
  subst h5
  have hsing6 : ¬ Y.RightTransAt 1 (((6 : ℕ) : ℤ)) :=
    Y.not_rightTransAt_of_regular_six H.sing (a := 1) (by simpa using hc.1)
  have hArc67 : Y.arcStab 1 (((6 : ℕ) : ℤ)) = Y.arcStab 1 (((7 : ℕ) : ℤ)) := by
    simpa using Y.arcStab_succ_eq_of_not_rightTransAt (a := 1) (b := 6) (by norm_num) hsing6
  have hn7 : Y.n (((7 : ℕ) : ℤ)) = 1 := by
    rw [show (((7 : ℕ) : ℤ)) = 1 + 2 * 3 by norm_num, Y.n_add, H.n_one]
  have hGT8 : Y.arcStab 1 (((8 : ℕ) : ℤ)) = Y.GT := by
    have h := hr.2 1 7 (by norm_num)
    simpa using h
  have hpc7 : Nat.card (pCoreOf 2 (Y.arcStab 1 (((7 : ℕ) : ℤ)))) = 2 := by
    have h := Y.card_pCoreOf_arcStab_of_succ_eq_GT H.odd_GT (a := 1) (b := 7)
      (by norm_num) hc.1.2 hGT8
    rw [show (7 : ℤ) = ((7 : ℕ) : ℤ) by norm_num, hn7, pow_one] at h
    exact h
  have hshift := (Y.shift 1).card_S_eq_prod H.sing
  have hshift_S : Nat.card ↥(Y.shift 1).S = Nat.card Y.S := by
    rw [Setup.shift_S]
    exact Y.card_edgeSylow_eq 1
  have hshift_arc : (Y.shift 1).arcStab 0 (((5 : ℕ) : ℤ)) = Y.arcStab 1 (((6 : ℕ) : ℤ)) := by
    rw [Setup.shift_arcStab]
    norm_num
  have hpc : Nat.card (pCoreOf 2 ((Y.shift 1).arcStab 0 (((5 : ℕ) : ℤ)))) = 2 := by
    rw [hshift_arc, hArc67]
    exact hpc7
  have hprod : (∏ r ∈ Finset.Icc (1 : ℕ) 4, (2 : ℕ) ^ (Y.shift 1).n (r : ℤ)) =
      4 * 2 ^ (2 * n₀) := by
    have h0 : (Y.shift 1).n 0 = 1 := by rw [Setup.shift_n]; simpa using H.n_one
    have h1 : (Y.shift 1).n 1 = n₀ := by
      rw [Setup.shift_n]; simpa [Y.n_two] using H.n_zero
    rw [show Finset.Icc (1 : ℕ) 4 = Finset.Icc 1 (2 * 2) from rfl,
      Setup.prod_Icc_two_mul (Y.shift 1) 2, h0, h1,
      show 2 * (1 + n₀) = 2 * n₀ + 2 by ring, pow_add]
    norm_num
    ring
  rw [hshift_S, hprod, hpc] at hshift
  rw [hshift]
  rw [show 4 * 2 ^ (2 * n₀) * 2 = 8 * 2 ^ (2 * n₀) by ring]

theorem card_S_of_isMaxRegLen_six_sub (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hr : Y.IsMaxRegLen 6) (h7 : s = 7) :
    Nat.card Y.S = 2 ^ (3 * n₀ + 3) := by
  subst h7
  have hGT : Y.arcStab 0 (((7 : ℕ) : ℤ)) = Y.GT := by
    have h := hr.2 0 7 (by norm_num)
    simpa using h
  have hpc : Nat.card (pCoreOf 2 (Y.arcStab 0 (((7 : ℕ) : ℤ)))) = 1 :=
    Y.card_pCoreOf_eq_one_of_arcStab_eq_GT H.odd_GT hGT
  rw [Y.card_S_eq_prod H.sing, hpc, mul_one]
  have hprod : (∏ r ∈ Finset.Icc (1 : ℕ) 6, (2 : ℕ) ^ Y.n (r : ℤ)) =
      2 ^ (3 * n₀ + 3) := by
    rw [show Finset.Icc (1 : ℕ) 6 = Finset.Icc 1 (2 * 3) from rfl, Y.prod_Icc_two_mul,
      H.n_zero, H.n_one, show 3 * (n₀ + 1) = 3 * n₀ + 3 by ring]
  exact hprod

section TreeData

variable {V₀ : Type} {G₀ : Type} [Group G₀] [MulAction G₀ V₀] {Γ₀ : SimpleGraph V₀}

structure TreeU42Data (X : Setup Γ₀ G₀) : Prop where
  card_S : Nat.card X.S = 2 ^ 6
  elem_right : IsElemAbelian 2 (X.Q 1)
  card_right : Nat.card (X.Q 1) = 2 ^ 4
  notNat_right : ¬ NatSec (X.L 1) ⊥ (X.Q 1)
  special_left : IsSpecialPow 2 2 2 ↥(X.Q 0)
  nat_left : NatSec (X.L 0) (centerOf (X.Q 0)) (X.Q 0)
  not_le : ¬ X.Q 1 ≤ X.Q 0
  sup_eq : X.Q 1 ⊔ X.Q 0 = X.S

structure TreeJ2Data (X : Setup Γ₀ G₀) : Prop where
  card_S : Nat.card X.S = 2 ^ 7
  q8d8_right : IsQ8D8 ↥(X.Q 1)
  card_left : Nat.card (X.Q 0) = 2 ^ 6
  card_Z_left : Nat.card (X.Z 0) = 4
  elemZ_left : IsElemAbelian 2 (X.Z 0)
  nat_left : NatSec (X.L 0) ⊥ (X.Q 0)
  Z_left_le_right : X.Z 0 ≤ X.Q 1
  cent3_left : ∀ k ∈ X.Gi 0 ⊓ X.Gi 1, orderOf k = 3 →
    X.Q 0 ⊓ Subgroup.centralizer ({k} : Set G₀) = X.Z 0
  inv_left : ∃ x ∈ X.Q 0, x ∉ X.Q 1 ∧ x ^ 2 = 1

structure TreeD4Data (Y : Setup Γ₀ G₀) (n₀ : ℕ) : Prop where
  quot : IsL2Quot n₀ (oTwoQuot ↥(Y.L 0))
  card_S : Nat.card Y.S = 2 ^ (3 * n₀ + 3)
  card_Z : Nat.card (Y.Z 0) = 2
  center_eq : centerOf (Y.Q 0) = Y.Z 0
  sec : IsElemSec (Y.Z 0) (Y.Q 0)
  card_quot : (Y.Z 0).relIndex (Y.Q 0) = 2 ^ (2 * n₀ + 2)
  irred : ∀ W : Subgroup G₀, Y.Z 0 ≤ W → W ≤ Y.Q 0 →
    Y.L 0 ≤ Subgroup.normalizer (W : Set G₀) → W = Y.Z 0 ∨ W = Y.Q 0
  nontriv : ∃ l ∈ Y.L 0, ∃ v ∈ Y.Q 0, ⁅l, v⁆ ∉ Y.Z 0
  card_Q1 : Nat.card (Y.Q 1) = 2 ^ (3 * n₀ + 2)
  Z1 : Nat.card (Y.Z 1) = 4 ∧ NatSec (Y.L 1) ⊥ (Y.Z 1)

theorem TreeU42Data.congr {X Y : Setup Γ₀ G₀} (h0 : X.vert 0 = Y.vert 0)
    (h1 : X.vert 1 = Y.vert 1) (d : X.TreeU42Data) : Y.TreeU42Data := by
  have hG0 : X.Gi 0 = Y.Gi 0 := by rw [Setup.Gi, Setup.Gi, h0]
  have hG1 : X.Gi 1 = Y.Gi 1 := by rw [Setup.Gi, Setup.Gi, h1]
  have hQ0 : X.Q 0 = Y.Q 0 := by rw [Setup.Q, Setup.Q, hG0]
  have hQ1 : X.Q 1 = Y.Q 1 := by rw [Setup.Q, Setup.Q, hG1]
  have hL0 : X.L 0 = Y.L 0 := by rw [Setup.L, Setup.L, hG0]
  have hL1 : X.L 1 = Y.L 1 := by rw [Setup.L, Setup.L, hG1]
  have hS : X.S = Y.S := by rw [Setup.S, Setup.S, hG0, hG1]
  exact ⟨by simpa [hS] using d.card_S,
    by simpa [hQ1] using d.elem_right,
    by simpa [hQ1] using d.card_right,
    by simpa [hL1, hQ1] using d.notNat_right,
    (by rw [← hQ0]; exact d.special_left),
    by simpa [hL0, hQ0] using d.nat_left,
    by simpa [hQ0, hQ1] using d.not_le,
    by simpa [hS, hQ0, hQ1] using d.sup_eq⟩

theorem TreeJ2Data.congr {X Y : Setup Γ₀ G₀} (h0 : X.vert 0 = Y.vert 0)
    (h1 : X.vert 1 = Y.vert 1) (d : X.TreeJ2Data) : Y.TreeJ2Data := by
  have hG0 : X.Gi 0 = Y.Gi 0 := by rw [Setup.Gi, Setup.Gi, h0]
  have hG1 : X.Gi 1 = Y.Gi 1 := by rw [Setup.Gi, Setup.Gi, h1]
  have hQ0 : X.Q 0 = Y.Q 0 := by rw [Setup.Q, Setup.Q, hG0]
  have hQ1 : X.Q 1 = Y.Q 1 := by rw [Setup.Q, Setup.Q, hG1]
  have hL0 : X.L 0 = Y.L 0 := by rw [Setup.L, Setup.L, hG0]
  have hZ0 : X.Z 0 = Y.Z 0 := by
    unfold Setup.Z
    rw [hG0, hQ0]
  have hS : X.S = Y.S := by rw [Setup.S, Setup.S, hG0, hG1]
  exact ⟨by simpa [hS] using d.card_S,
    (by rw [← hQ1]; exact d.q8d8_right),
    by simpa [hQ0] using d.card_left,
    by simpa [hZ0] using d.card_Z_left,
    by simpa [hZ0] using d.elemZ_left,
    by simpa [hL0, hQ0] using d.nat_left,
    by simpa [hZ0, hQ1] using d.Z_left_le_right,
    by simpa [hG0, hG1, hQ0, hZ0] using d.cent3_left,
    by simpa [hQ0, hQ1] using d.inv_left⟩

end TreeData

end Setup

private theorem map_iSup_conj_subgroupOf {H : Type*} [Group H] {L W P : Subgroup H}
    (hWL : W ≤ L) (hPL : P ≤ L) :
    (⨆ l ∈ L.subgroupOf L,
        ((W.subgroupOf L) ⊓ Subgroup.centralizer ((P.subgroupOf L) : Set ↥L)).map
          (MulAut.conj l).toMonoidHom).map L.subtype =
      ⨆ l ∈ L, (W ⊓ Subgroup.centralizer (P : Set H)).map
        (MulAut.conj l).toMonoidHom := by
  let A : Subgroup ↥L := (W.subgroupOf L) ⊓ Subgroup.centralizer ((P.subgroupOf L) : Set ↥L)
  have hmapW : Subgroup.map L.subtype (W.subgroupOf L) = W :=
    Subgroup.map_subgroupOf_eq_of_le hWL
  have hAV : Subgroup.map L.subtype A = W ⊓ Subgroup.centralizer (P : Set H) := by
    have hAV' : A = (W.subgroupOf L) ⊓ (Subgroup.centralizer (P : Set H)).subgroupOf L := by
      apply le_antisymm
      · intro x hx
        obtain ⟨hxW, hxC⟩ := Subgroup.mem_inf.mp hx
        refine Subgroup.mem_inf.mpr ⟨hxW, ?_⟩
        rw [Subgroup.mem_subgroupOf]
        rw [Subgroup.mem_centralizer_iff] at hxC ⊢
        intro p hp
        have hp' : (⟨p, hPL hp⟩ : ↥L) ∈ P.subgroupOf L := hp
        exact congrArg Subtype.val (hxC ⟨p, hPL hp⟩ hp')
      · intro x hx
        obtain ⟨hxW, hxC⟩ := Subgroup.mem_inf.mp hx
        rw [Subgroup.mem_subgroupOf] at hxC
        refine Subgroup.mem_inf.mpr ⟨hxW, ?_⟩
        rw [Subgroup.mem_centralizer_iff] at hxC ⊢
        intro p hp
        have hpP : (p : H) ∈ P := hp
        exact Subtype.ext (hxC (p : H) hpP)
    rw [hAV', Subgroup.map_inf _ _ _ L.subtype_injective, hmapW,
      Subgroup.subgroupOf_map_subtype, ← inf_assoc,
      inf_eq_left.mpr (inf_le_left.trans hWL)]
  have hstep : ∀ l : ↥L,
      Subgroup.map L.subtype (A.map (MulAut.conj l).toMonoidHom) =
      (W ⊓ Subgroup.centralizer (P : Set H)).map
        (MulAut.conj (l : H)).toMonoidHom := by
    intro l
    rw [Subgroup.map_map]
    have hgf : L.subtype.comp (MulAut.conj l).toMonoidHom =
        (MulAut.conj (l : H)).toMonoidHom.comp L.subtype := by
      ext x; rfl
    rw [hgf, ← Subgroup.map_map, hAV]
  refine le_antisymm ?_ ?_
  · rw [Subgroup.map_iSup]
    refine iSup_le fun l => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hl => ?_
    rw [hstep l]
    exact le_iSup₂_of_le (l : H) (Subgroup.mem_subgroupOf.mp hl) le_rfl
  · refine iSup_le fun x => iSup_le fun hx => ?_
    have hxl : (⟨x, hx⟩ : ↥L) ∈ L.subgroupOf L := Subgroup.mem_subgroupOf.mpr hx
    have h1 : A.map (MulAut.conj (⟨x, hx⟩ : ↥L)).toMonoidHom ≤
        ⨆ l ∈ L.subgroupOf L, A.map (MulAut.conj l).toMonoidHom :=
      le_iSup₂_of_le (⟨x, hx⟩ : ↥L) hxl le_rfl
    have h2 := Subgroup.map_mono (f := L.subtype) h1
    rw [hstep (⟨x, hx⟩ : ↥L)] at h2
    exact h2

@[expose] def HigmanQuad (n₀ : ℕ) : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (L V Z P : Subgroup G),
    IsL2Quot n₀ (oTwoQuot ↥L) → IsSylowTwoOf P L → IsElemSec Z V →
      V ≤ pCoreOf 2 L →
      L ≤ Subgroup.normalizer (V : Set G) → L ≤ Subgroup.normalizer (Z : Set G) →
      (∀ q ∈ pCoreOf 2 L, ∀ v ∈ V, ⁅q, v⁆ ∈ Z) →
      (∀ v ∈ V, (∀ l ∈ L, ⁅v, l⁆ ∈ Z) → v ∈ Z) →
      (∀ v ∈ V, ∀ a ∈ P, ∀ b ∈ P, ⁅⁅v, a⁆, b⁆ ∈ Z) →
      V = (⨆ l ∈ L, (V ⊓ Subgroup.centralizer (P : Set G)).map
        (MulAut.conj l).toMonoidHom) ⊔ Z →
      ∀ k ∈ L, Odd (orderOf k) → k ≠ 1 → FixFree Z V k

private theorem pCoreOf_subgroupOf_top {H : Type*} [Group H] (L : Subgroup H) :
    pCoreOf 2 (L.subgroupOf L) = (pCoreOf 2 L).subgroupOf L := by
  have hmap : (pCoreOf 2 (L.subgroupOf L)).map L.subtype = pCoreOf 2 L := by
    have e := CFSG.LieType.BorelTits.map_pCore_mulEquiv (r := 2)
      (Subgroup.subgroupOfEquivOfLe (le_rfl : L ≤ L))
    rw [pCoreOf, pCoreOf, Subgroup.map_map, ← e, Subgroup.map_map]
    rfl
  apply Subgroup.map_injective L.subtype_injective
  rw [hmap, Subgroup.map_subgroupOf_eq_of_le (CFSG.LieType.BorelTits.pCoreOf_le 2 L)]

theorem HigmanQuad.fixFree {n₀ : ℕ} (h : HigmanQuad n₀) {H : Type} [Group H]
    {L W Z P : Subgroup H} [Finite ↥L] (hL2 : IsL2Quot n₀ (oTwoQuot ↥L))
    (hP : IsSylowTwoOf P L) (hsec : IsElemSec Z W) (hWL : W ≤ pCoreOf 2 L)
    (hLW : L ≤ Subgroup.normalizer (W : Set H)) (hLZ : L ≤ Subgroup.normalizer (Z : Set H))
    (hcent : ∀ q ∈ pCoreOf 2 L, ∀ w ∈ W, ⁅q, w⁆ ∈ Z)
    (hfixL : ∀ w ∈ W, (∀ l ∈ L, ⁅w, l⁆ ∈ Z) → w ∈ Z)
    (hquad : ∀ w ∈ W, ∀ a ∈ P, ∀ b ∈ P, ⁅⁅w, a⁆, b⁆ ∈ Z)
    (hgen : W = (⨆ l ∈ L, (W ⊓ Subgroup.centralizer (P : Set H)).map
      (MulAut.conj l).toMonoidHom) ⊔ Z) :
    ∀ k ∈ L, Odd (orderOf k) → k ≠ 1 → FixFree Z W k := by
  intro k hk hkodd hkne
  have hPL : P ≤ L := hP.1
  have hWLL : W ≤ L := hWL.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 L)
  have hZL : Z ≤ L := hsec.1.trans hWLL
  let L' : Subgroup ↥L := L.subgroupOf L
  let W' : Subgroup ↥L := W.subgroupOf L
  let Z' : Subgroup ↥L := Z.subgroupOf L
  let P' : Subgroup ↥L := P.subgroupOf L
  have hquot' : IsL2Quot n₀ (oTwoQuot ↥L') := by
    obtain ⟨e⟩ := hL2
    exact ⟨(QuotientGroup.congr (CFSG.Open.pCore 2 ↥L') (CFSG.Open.pCore 2 ↥L)
      (Subgroup.subgroupOfEquivOfLe (le_rfl : L ≤ L))
      (CFSG.LieType.BorelTits.map_pCore_mulEquiv 2
        (Subgroup.subgroupOfEquivOfLe (le_rfl : L ≤ L)))).trans e⟩
  have hsyl' : IsSylowTwoOf P' L' := by
    refine ⟨Subgroup.comap_mono hP.1, ?_, ?_⟩
    · exact hP.2.1.of_equiv
        (Subgroup.subgroupOfEquivOfLe (hP.1.trans le_rfl)).symm
    · have h1 : (P'.subgroupOf L').index = P'.relIndex L' := rfl
      rw [h1, Subgroup.relIndex_subgroupOf le_rfl]
      exact hP.2.2
  have hsec' : IsElemSec Z' W' := by
    refine ⟨Subgroup.subgroupOf_mono _ hsec.1, ?_, ?_⟩
    · intro x hx
      rw [Subgroup.mem_subgroupOf]
      have himg : (x : H) ∈ (⁅W', W'⁆).map L.subtype :=
        Subgroup.mem_map_of_mem _ hx
      rw [Subgroup.map_commutator,
        Subgroup.map_subgroupOf_eq_of_le hWLL] at himg
      exact hsec.2.1 himg
    · intro e he
      rw [Subgroup.mem_subgroupOf]
      exact hsec.2.2 (e : H) (Subgroup.mem_subgroupOf.mp he)
  have hpcl : pCoreOf 2 L' = (pCoreOf 2 L).subgroupOf L :=
    pCoreOf_subgroupOf_top L
  have hWL' : W' ≤ pCoreOf 2 L' := by
    rw [hpcl]
    exact Subgroup.subgroupOf_mono _ hWL
  have hLnV : L' ≤ Subgroup.normalizer (W' : Set ↥L) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro w
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp (hLW (Subgroup.mem_subgroupOf.mp hl)) (w : H)
  have hLnZ : L' ≤ Subgroup.normalizer (Z' : Set ↥L) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro z
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp (hLZ (Subgroup.mem_subgroupOf.mp hl)) (z : H)
  have hQc : ∀ q ∈ pCoreOf 2 L', ∀ v ∈ W', ⁅q, v⁆ ∈ Z' := by
    intro q hq v hv
    rw [hpcl] at hq
    rw [Subgroup.mem_subgroupOf]
    exact hcent (q : H) (Subgroup.mem_subgroupOf.mp hq) (v : H)
      (Subgroup.mem_subgroupOf.mp hv)
  have hCVZ : ∀ v ∈ W', (∀ l ∈ L', ⁅v, l⁆ ∈ Z') → v ∈ Z' := by
    intro v hv hvl
    have hvW : (v : H) ∈ W := Subgroup.mem_subgroupOf.mp hv
    have hvl' : ∀ l ∈ L, ⁅(v : H), l⁆ ∈ Z := by
      intro l hl
      have h := hvl ⟨l, hl⟩ hl
      rwa [Subgroup.mem_subgroupOf] at h
    rw [Subgroup.mem_subgroupOf]
    exact hfixL (v : H) hvW hvl'
  have hquad' : ∀ v ∈ W', ∀ a ∈ P', ∀ b ∈ P', ⁅⁅v, a⁆, b⁆ ∈ Z' := by
    intro v hv a ha b hb
    rw [Subgroup.mem_subgroupOf]
    exact hquad (v : H) (Subgroup.mem_subgroupOf.mp hv) (a : H)
      (Subgroup.mem_subgroupOf.mp ha) (b : H) (Subgroup.mem_subgroupOf.mp hb)
  have hgen' : W' = (⨆ l ∈ L', (W' ⊓ Subgroup.centralizer (P' : Set ↥L)).map
      (MulAut.conj l).toMonoidHom) ⊔ Z' := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hWLL, Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hZL, map_iSup_conj_subgroupOf hWLL hPL]
    exact hgen
  have hkL : (⟨k, hk⟩ : ↥L) ∈ L' := Subgroup.mem_subgroupOf.mpr hk
  have hff' : FixFree Z' W' (⟨k, hk⟩ : ↥L) :=
    h L' W' Z' P' hquot' hsyl' hsec' hWL' hLnV hLnZ hQc hCVZ hquad' hgen'
      ⟨k, hk⟩ hkL (by rw [← Subgroup.orderOf_coe]; exact hkodd)
      (by intro hh; exact hkne (Subtype.ext_iff.mp hh))
  intro w hw hwc
  have hwL : w ∈ L := hWLL hw
  have hxW : (⟨w, hwL⟩ : ↥L) ∈ W' := hw
  have hxZ : (⁅(⟨w, hwL⟩ : ↥L), (⟨k, hk⟩ : ↥L)⁆) ∈ Z' := by
    rw [Subgroup.mem_subgroupOf]
    exact hwc
  exact Subgroup.mem_subgroupOf.mp (hff' ⟨w, hwL⟩ hxW hxZ)


end CFSG.Quasithin.St84
