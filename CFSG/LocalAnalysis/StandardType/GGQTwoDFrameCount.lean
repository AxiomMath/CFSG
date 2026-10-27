module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameStd

public section

namespace CFSG.StandardType.QTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma plq_dSgn_ne_zero (ε : Bool) : dSgn ε ≠ 0 := by
  cases ε <;> decide

private lemma plq_dSgn_mul_eq_zero (ε : Bool) (x : ZMod 3) :
    dSgn ε * x = 0 ↔ x = 0 := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (plq_dSgn_ne_zero ε)
    · exact h'
  · rintro rfl
    simp

private lemma plq_dSgn_injective : Function.Injective dSgn := by
  decide

private lemma plq_pred_mul_pred (m : ℕ) :
    (m - 1) * (m - 1) = (m - 1) * (m - 2) + (m - 1) := by
  rcases m with _ | _ | k
  · simp
  · simp
  · have h1 : k + 2 - 1 = k + 1 := by omega
    have h2 : k + 2 - 2 = k := by omega
    rw [h1, h2]
    ring

private lemma plq_two_mul_choose_two (n : ℕ) : 2 * n.choose 2 + n = n * n := by
  rw [Nat.choose_two_right]
  have h2 : 2 * (n * (n - 1) / 2) = n * (n - 1) :=
    (mul_comm 2 _).trans
      (Nat.div_mul_cancel (even_iff_two_dvd.mp (Nat.even_mul_pred_self n)))
  rw [h2]
  rcases n with _ | k
  · simp
  · have hk : k + 1 - 1 = k := by omega
    rw [hk]
    ring

private lemma plq_not_card_ineq {m s t : ℕ} (hm : 5 ≤ m) (hst : s + t = m) (ht2 : 2 ≤ t) :
    ¬ (2 * (m - 1) * (m - 2) + 2 * s + t ≤ 2 * s ^ 2 + t ^ 2) := by
  intro hle
  have htlem : t ≤ m := by omega
  have hsZ : (s : ℤ) = (m : ℤ) - t := by omega
  have hm1 : (((m - 1 : ℕ)) : ℤ) = (m : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m)]
    simp
  have hm2 : (((m - 2 : ℕ)) : ℤ) = (m : ℤ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ m)]
    simp
  have hleZ : ((2 * (m - 1) * (m - 2) + 2 * s + t : ℕ) : ℤ) ≤
      ((2 * s ^ 2 + t ^ 2 : ℕ) : ℤ) := by
    exact_mod_cast hle
  push_cast at hleZ
  rw [hm1, hm2] at hleZ
  have ht2Z : (2 : ℤ) ≤ t := by exact_mod_cast ht2
  have hmZ : (5 : ℤ) ≤ m := by exact_mod_cast hm
  have htleZ : (t : ℤ) ≤ m := by exact_mod_cast htlem
  nlinarith [hleZ, hsZ, ht2Z, hmZ, htleZ]

theorem card_lt_pairs {α : Type} [LinearOrder α] (S : Finset α) :
    2 * ((S ×ˢ S).filter fun x : α × α => x.1 < x.2).card + S.card = S.card * S.card := by
  rw [Finset.card_product_filter_lt]
  exact plq_two_mul_choose_two S.card

@[expose] def dPairsPos (m : ℕ) : Finset (Fin m × Fin m × Bool) :=
  Finset.univ.filter fun x => 0 < x.1.val ∧ x.1 < x.2.1

theorem card_dPairsPos (m : ℕ) : (dPairsPos m).card = (m - 1) * (m - 2) := by
  set T : Finset (Fin m) := Finset.univ.filter fun i => 0 < i.val with hTdef
  set P : Finset (Fin m × Fin m) := (T ×ˢ T).filter fun x => x.1 < x.2 with hPdef
  have hT : T.card = m - 1 := by
    rcases m with _ | k
    · simp [hTdef]
    · have hT' : T = (Finset.univ : Finset (Fin (k + 1))).erase 0 := by
        ext i
        simp only [hTdef, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_erase]
        constructor
        · intro hi
          exact ⟨fun h0 => by rw [h0] at hi; exact Nat.lt_irrefl 0 hi, trivial⟩
        · intro hi
          exact Nat.pos_of_ne_zero (by simpa [Fin.val_eq_zero_iff] using hi.1)
      rw [hT', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_fin]
  have hP : P.card = (m - 1).choose 2 := by
    have h := Finset.card_product_filter_lt (s := T)
    rw [hT] at h
    exact h
  have hbij : (dPairsPos m).card = (P ×ˢ (Finset.univ : Finset Bool)).card := by
    refine Finset.card_nbij' (fun x : Fin m × Fin m × Bool => ((x.1, x.2.1), x.2.2))
      (fun y : (Fin m × Fin m) × Bool => (y.1.1, y.1.2, y.2)) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_coe, dPairsPos, Finset.mem_filter, Finset.mem_univ,
        true_and] at hx
      obtain ⟨hx1, hx2⟩ := hx
      refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩
      simp only [hPdef, hTdef, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
        true_and]
      exact ⟨⟨hx1, by omega⟩, hx2⟩
    · intro y hy
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_univ, true_and] at hy
      obtain ⟨hyP, _⟩ := hy
      obtain ⟨hyT, hy3⟩ := Finset.mem_filter.mp hyP
      obtain ⟨hy1, _hy2⟩ := Finset.mem_product.mp hyT
      simp only [hTdef, Finset.mem_filter, Finset.mem_univ, true_and] at hy1
      simp only [Finset.mem_coe, dPairsPos, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact ⟨hy1, hy3⟩
    · intro x _
      obtain ⟨a, b, e⟩ := x
      rfl
    · intro y _
      obtain ⟨⟨a, b⟩, e⟩ := y
      rfl
  rw [hbij, Finset.card_product, Finset.card_univ, Fintype.card_bool, hP]
  have hchoose := plq_two_mul_choose_two (m - 1)
  have hpred := plq_pred_mul_pred m
  omega

@[expose] def dPairsFix (m : ℕ) (v : DVec m) : Finset (Fin m × Fin m × Bool) :=
  Finset.univ.filter fun x => x.1 < x.2.1 ∧ v x.1 = dSgn x.2.2 * v x.2.1

theorem card_dPairsFix_le (m : ℕ) (v : DVec m) :
    2 * (dPairsFix m v).card + 2 * (Finset.univ.filter fun i => v i = 0).card +
        (Finset.univ.filter fun i => v i ≠ 0).card ≤
      2 * (Finset.univ.filter fun i => v i = 0).card ^ 2 +
        (Finset.univ.filter fun i => v i ≠ 0).card ^ 2 := by
  set Z : Finset (Fin m) := Finset.univ.filter fun i => v i = 0 with hZ
  set S : Finset (Fin m) := Finset.univ.filter fun i => v i ≠ 0 with hS
  set Y1 : Finset (Fin m × Fin m × Bool) := Finset.univ.filter fun x =>
    x.1 < x.2.1 ∧ v x.1 = 0 ∧ v x.2.1 = 0 with hY1
  set Y2 : Finset (Fin m × Fin m × Bool) := Finset.univ.filter fun x =>
    x.1 < x.2.1 ∧ v x.1 ≠ 0 ∧ v x.2.1 ≠ 0 ∧
      v x.1 = dSgn x.2.2 * v x.2.1 with hY2
  set A : Finset (Fin m × Fin m) := (Z ×ˢ Z).filter fun x => x.1 < x.2 with hA
  set B : Finset (Fin m × Fin m) := (S ×ˢ S).filter fun x => x.1 < x.2 with hB
  have hsub : dPairsFix m v ⊆ Y1 ∪ Y2 := by
    intro x hx
    simp only [dPairsFix, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨hlt, hfix⟩ := hx
    by_cases hv1 : v x.1 = 0
    · have hv2 : v x.2.1 = 0 :=
        (plq_dSgn_mul_eq_zero x.2.2 (v x.2.1)).mp (by rw [← hfix, hv1])
      simp only [Finset.mem_union, hY1, hY2, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact Or.inl ⟨hlt, hv1, hv2⟩
    · have hv2 : v x.2.1 ≠ 0 := by
        intro h0
        exact hv1 (by rw [hfix, h0, mul_zero])
      simp only [Finset.mem_union, hY1, hY2, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact Or.inr ⟨hlt, hv1, hv2, hfix⟩
  have hY1le : Y1.card ≤ 2 * A.card := by
    have hle := Finset.card_le_card_of_injOn
      (fun x : Fin m × Fin m × Bool => ((x.1, x.2.1), x.2.2))
      (s := Y1) (t := A ×ˢ (Finset.univ : Finset Bool))
      (fun x hx => by
        simp only [Finset.mem_coe, hY1, Finset.mem_filter, Finset.mem_univ,
          true_and] at hx
        obtain ⟨hxlt, hx1Z, hx2Z⟩ := hx
        rw [Finset.mem_coe]
        refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩
        rw [hA]
        refine Finset.mem_filter.mpr ⟨?_, hxlt⟩
        exact Finset.mem_product.mpr
          ⟨by rw [hZ]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx1Z⟩,
           by rw [hZ]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx2Z⟩⟩)
      (fun x _ x' _ heq => by
        simp only [Prod.mk.injEq] at heq
        exact Prod.ext heq.1.1 (Prod.ext heq.1.2 heq.2))
    rw [Finset.card_product, Finset.card_univ, Fintype.card_bool] at hle
    omega
  have hY2le : Y2.card ≤ B.card := by
    have hle := Finset.card_le_card_of_injOn
      (fun x : Fin m × Fin m × Bool => (x.1, x.2.1))
      (s := Y2) (t := B)
      (fun x hx => by
        simp only [Finset.mem_coe, hY2, Finset.mem_filter, Finset.mem_univ,
          true_and] at hx
        obtain ⟨hxlt, hx1S, hx2S, _⟩ := hx
        rw [Finset.mem_coe, hB]
        refine Finset.mem_filter.mpr ⟨?_, hxlt⟩
        exact Finset.mem_product.mpr
          ⟨by rw [hS]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx1S⟩,
           by rw [hS]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx2S⟩⟩)
      (fun x hx x' hx' heq => by
        simp only [Finset.mem_coe, hY2, Finset.mem_filter, Finset.mem_univ,
          true_and] at hx hx'
        obtain ⟨_, hx1S, hx2S, hxfix⟩ := hx
        obtain ⟨_, _, hx'2S, hx'fix⟩ := hx'
        simp only [Prod.mk.injEq] at heq
        obtain ⟨h1, h2⟩ := heq
        have hxfix' : v x'.1 = dSgn x.2.2 * v x'.2.1 := by
          rw [← h1, ← h2]
          exact hxfix
        have hmain : dSgn x.2.2 * v x'.2.1 = dSgn x'.2.2 * v x'.2.1 := by
          rw [← hxfix', hx'fix]
        have hs : dSgn x.2.2 = dSgn x'.2.2 := mul_right_cancel₀ hx'2S hmain
        have he : x.2.2 = x'.2.2 := plq_dSgn_injective hs
        exact Prod.ext h1 (Prod.ext h2 he))
    exact hle
  have hA : 2 * A.card + Z.card = Z.card * Z.card := card_lt_pairs Z
  have hB : 2 * B.card + S.card = S.card * S.card := card_lt_pairs S
  have hN : (dPairsFix m v).card ≤ Y1.card + Y2.card := by
    have h1 : (dPairsFix m v).card ≤ (Y1 ∪ Y2).card := Finset.card_le_card hsub
    have h2 : (Y1 ∪ Y2).card ≤ Y1.card + Y2.card := Finset.card_union_le Y1 Y2
    omega
  have hgoal : 2 * (dPairsFix m v).card + 2 * Z.card + S.card ≤
      2 * Z.card ^ 2 + S.card ^ 2 := by
    nlinarith [hN, hY1le, hY2le, hA, hB]
  simpa only [← hZ, ← hS] using hgoal

theorem exists_unique_support_of_card_le (m : ℕ) (hm : 5 ≤ m) (v : DVec m) (hv : v ≠ 0)
    (h : (m - 1) * (m - 2) ≤ (dPairsFix m v).card) :
    ∃ j : Fin m, v j ≠ 0 ∧ ∀ i, i ≠ j → v i = 0 := by
  have hcard := card_dPairsFix_le m v
  have hst : (Finset.univ.filter fun i => v i = 0).card +
        (Finset.univ.filter fun i => v i ≠ 0).card = m := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
      (p := fun i => v i = 0)
    simpa using this
  have hSpos : 1 ≤ (Finset.univ.filter fun i => v i ≠ 0).card := by
    have hne : (Finset.univ.filter fun i => v i ≠ 0).Nonempty := by
      by_contra hcon
      rw [Finset.not_nonempty_iff_eq_empty] at hcon
      apply hv
      funext i
      have hi : i ∉ Finset.univ.filter (fun i => v i ≠ 0) := by
        rw [hcon]
        simp
      simpa using hi
    exact Finset.card_pos.mpr hne
  have hSone : (Finset.univ.filter fun i => v i ≠ 0).card = 1 := by
    by_contra hne
    have h2 : 2 ≤ (Finset.univ.filter fun i => v i ≠ 0).card := by omega
    refine plq_not_card_ineq hm hst h2 ?_
    nlinarith [hcard, h]
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hSone
  refine ⟨j, ?_, ?_⟩
  · have : j ∈ Finset.univ.filter (fun i => v i ≠ 0) := by
      rw [hj]
      exact Finset.mem_singleton_self j
    simpa using this
  · intro i hi
    have : i ∉ Finset.univ.filter (fun i => v i ≠ 0) := by
      rw [hj]
      simp [hi]
    simpa using this

theorem card_dPairsFix_le_of_single (m : ℕ) {v : DVec m} {j : Fin m} (hj : v j ≠ 0)
    (h : ∀ i, i ≠ j → v i = 0) : (dPairsFix m v).card ≤ (m - 1) * (m - 2) := by
  have hZ : (Finset.univ.filter fun i => v i = 0) = Finset.univ.erase j := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · intro hi
      exact ⟨fun hij => hj (by rw [← hij]; exact hi), trivial⟩
    · intro hi
      exact h i hi.1
  have hS : (Finset.univ.filter fun i => v i ≠ 0) = {j} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hi
      by_contra hij
      exact hi (h i hij)
    · intro hij
      rw [hij]
      exact hj
  have hcard := card_dPairsFix_le m v
  rw [hZ, hS, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_singleton] at hcard
  simp only [Finset.card_univ, Fintype.card_fin] at hcard
  have hpred := plq_pred_mul_pred m
  nlinarith [hcard, hpred]

end CFSG.StandardType.QTwo

end
