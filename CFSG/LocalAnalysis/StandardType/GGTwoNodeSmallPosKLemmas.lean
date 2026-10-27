module

public import Certificates.Data.CFSGNative.TwoNodeSmall.CorePos
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabel
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem pks_cartanA_entry (m : ℕ) (i j : Fin m) :
    CartanMatrix.A m i j =
      if i = j then 2 else if (i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ) then -1 else 0 :=
  rfl

theorem pks_AN_mod (p N : ℕ) (i j : Fin (N - 1)) (hij : i ≠ j) :
    ((CartanMatrix.A (N - 1) i j : ℤ) : ZMod p) =
      (if (i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ) then ((-1 : ℤ) : ZMod p) else 0) := by
  rw [pks_cartanA_entry]
  simp only [hij, if_false]
  split_ifs <;> simp

theorem pks_card_fin_eq {ι : Type} [Fintype ι] {n : ℕ} (e : Fin n ≃ ι) :
    n = Fintype.card ι := by
  have h := Fintype.card_congr e
  rwa [Fintype.card_fin] at h

theorem pks_An_ne (n : ℕ) (hn3 : 3 ≤ n) (hn5 : n ≤ 5) (i j : Fin n) :
    (CoxeterMatrix.A n) i j ≠ 4 ∧ (CoxeterMatrix.A n) i j ≠ 6 := by
  interval_cases n <;>
    exact ⟨by fin_cases i <;> fin_cases j <;> decide,
           by fin_cases i <;> fin_cases j <;> decide⟩

theorem pks_Bn_no6 (n : ℕ) (hn3 : 3 ≤ n) (hn5 : n ≤ 5) (i j : Fin n) :
    (CoxeterMatrix.B n) i j ≠ 6 := by
  interval_cases n <;> fin_cases i <;> fin_cases j <;> decide

theorem pks_Dn_ne (n : ℕ) (hn4 : 4 ≤ n) (hn5 : n ≤ 5) (i j : Fin n) :
    (CFSG.StandardType.ggCoxeterMatrixD n) i j ≠ 4 ∧
      (CFSG.StandardType.ggCoxeterMatrixD n) i j ≠ 6 := by
  interval_cases n <;> constructor <;> fin_cases i <;> fin_cases j <;> decide

theorem pks_Bn_deg (n : ℕ) (hn3 : 3 ≤ n) (hn5 : n ≤ 5) (x : Fin n) :
    (Finset.univ.filter (fun y : Fin n => y ≠ x ∧ (CoxeterMatrix.B n) x y ≠ 2)).card ≤ 2 := by
  interval_cases n <;> fin_cases x <;> decide

theorem pks_F4_no6 (i j : Fin 4) : (CoxeterMatrix.F₄) i j ≠ 6 := by
  fin_cases i <;> fin_cases j <;> decide

theorem pks_F4_deg (x : Fin 4) :
    (Finset.univ.filter (fun y : Fin 4 => y ≠ x ∧ (CoxeterMatrix.F₄) x y ≠ 2)).card ≤ 2 := by
  fin_cases x <;> decide

theorem pks_neg_one_ne_zero (p : ℕ) [Fact p.Prime] : ((-1 : ℤ) : ZMod p) ≠ 0 := by
  intro h
  have h1 : (1 : ZMod p) = 0 := by
    have := congrArg (fun x : ZMod p => -x) h
    simpa using this
  exact one_ne_zero h1

theorem pks_two_ne_zero (p : ℕ) [Fact p.Prime] (hp3 : 3 ≤ p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
  have hpgt : 2 < p := by omega
  exact Nat.not_dvd_of_pos_of_lt (by norm_num) hpgt hdvd

theorem pks_neg_two_ne_zero (p : ℕ) [Fact p.Prime] (hp3 : 3 ≤ p) :
    ((-2 : ℤ) : ZMod p) ≠ 0 := by
  intro h
  have h1 : (2 : ZMod p) = 0 := by
    have := congrArg (fun x : ZMod p => -x) h
    simpa using this
  exact pks_two_ne_zero p hp3 h1

theorem pks_neg_two_ne_neg_one (p : ℕ) [Fact p.Prime] :
    ((-2 : ℤ) : ZMod p) ≠ ((-1 : ℤ) : ZMod p) := by
  intro h
  have h1 : ((-2 : ℤ) : ZMod p) - ((-1 : ℤ) : ZMod p) = 0 := sub_eq_zero.mpr h
  have h2 : ((-2 : ℤ) : ZMod p) - ((-1 : ℤ) : ZMod p) = ((-1 : ℤ) : ZMod p) := by
    push_cast; ring
  rw [h2] at h1
  exact pks_neg_one_ne_zero p h1

theorem pks_neg_three_ne_neg_one (p : ℕ) [Fact p.Prime] (hp3 : 3 ≤ p) :
    ((-3 : ℤ) : ZMod p) ≠ ((-1 : ℤ) : ZMod p) := by
  intro h
  have h1 : ((-3 : ℤ) : ZMod p) - ((-1 : ℤ) : ZMod p) = 0 := sub_eq_zero.mpr h
  have h2 : ((-3 : ℤ) : ZMod p) - ((-1 : ℤ) : ZMod p) = ((-2 : ℤ) : ZMod p) := by
    push_cast; ring
  rw [h2] at h1
  exact pks_neg_two_ne_zero p hp3 h1

theorem pks_neg_one_cast (p : ℕ) (hp : 1 ≤ p) :
    ((-1 : ℤ) : ZMod p) = ((p - 1 : ℕ) : ZMod p) := by
  have h : ((p - 1 : ℕ) : ZMod p) = -1 := by
    rw [Nat.cast_sub hp, ZMod.natCast_self]
    ring
  simp only [h, Int.cast_neg, Int.cast_one]

theorem pks_neg_two_cast (p : ℕ) (hp : 2 ≤ p) :
    ((-2 : ℤ) : ZMod p) = ((p - 2 : ℕ) : ZMod p) := by
  have h : ((p - 2 : ℕ) : ZMod p) = -2 := by
    rw [Nat.cast_sub hp, ZMod.natCast_self]
    ring
  simp only [h, Int.cast_neg, Int.cast_ofNat]

theorem pks_adj_vals (p : ℕ) [Fact p.Prime] (hp3 : 3 ≤ p)
    {Γ : Type*} {M : CoxeterMatrix Γ} {C : Matrix Γ Γ ℤ}
    (hC : CFSG.StandardType.GGIntCartan M C) {a b : Γ} (hab : a ≠ b)
    (ha : ((C a b : ℤ) : ZMod p) = ((-1 : ℤ) : ZMod p))
    (hb : ((C b a : ℤ) : ZMod p) = ((-1 : ℤ) : ZMod p)) :
    C a b = -1 ∧ M a b = 3 := by
  rcases hC.2 a b hab with
    ⟨hm, h1, h2⟩ | ⟨hm, h1, h2⟩ | ⟨hm, hpr, hn1, hn2⟩ | ⟨hm, hpr, hn1, hn2⟩
  · exfalso
    rw [h1] at ha
    simp only [Int.cast_zero] at ha
    exact (pks_neg_one_ne_zero p) ha.symm
  · exact ⟨h1, hm⟩
  · exfalso
    have hxle : C a b ≤ -1 := by omega
    have hxge : -2 ≤ C a b := by
      by_contra h
      push Not at h
      have h1 : (0 : ℤ) ≤ -(C a b) := by omega
      have h2 : (0 : ℤ) ≤ -(C b a) := by omega
      have hmul : (3 : ℤ) * 1 ≤ (-(C a b)) * (-(C b a)) :=
        mul_le_mul (by omega : (3 : ℤ) ≤ -(C a b)) (by omega : (1 : ℤ) ≤ -(C b a))
          (by norm_num) h1
      nlinarith [hpr, hmul]
    have hx : C a b = -1 ∨ C a b = -2 := by omega
    rcases hx with hx | hx
    · rw [hx] at hpr
      have hy : C b a = -2 := by omega
      rw [hy] at hb
      exact (pks_neg_two_ne_neg_one p) hb
    · rw [hx] at ha
      exact (pks_neg_two_ne_neg_one p) ha
  · exfalso
    have hxle : C a b ≤ -1 := by omega
    have hxge : -3 ≤ C a b := by
      by_contra h
      push Not at h
      have h1 : (0 : ℤ) ≤ -(C a b) := by omega
      have h2 : (0 : ℤ) ≤ -(C b a) := by omega
      have hmul : (4 : ℤ) * 1 ≤ (-(C a b)) * (-(C b a)) :=
        mul_le_mul (by omega : (4 : ℤ) ≤ -(C a b)) (by omega : (1 : ℤ) ≤ -(C b a))
          (by norm_num) h1
      nlinarith [hpr, hmul]
    have hx : C a b = -1 ∨ C a b = -2 ∨ C a b = -3 := by omega
    rcases hx with hx | hx | hx
    · rw [hx] at hpr
      have hy : C b a = -3 := by omega
      rw [hy] at hb
      exact (pks_neg_three_ne_neg_one p hp3) hb
    · rw [hx] at hpr
      omega
    · rw [hx] at ha
      exact (pks_neg_three_ne_neg_one p hp3) ha

theorem pks_nonadj_vals (p : ℕ) [Fact p.Prime] (hp3 : 3 ≤ p)
    {Γ : Type*} {M : CoxeterMatrix Γ} {C : Matrix Γ Γ ℤ}
    (hC : CFSG.StandardType.GGIntCartan M C) {a b : Γ} (hab : a ≠ b) (h6 : M a b ≠ 6)
    (ha : ((C a b : ℤ) : ZMod p) = 0) (hb : ((C b a : ℤ) : ZMod p) = 0) :
    C a b = 0 ∧ M a b = 2 := by
  rcases hC.2 a b hab with
    ⟨hm, h1, h2⟩ | ⟨hm, h1, h2⟩ | ⟨hm, hpr, hn1, hn2⟩ | ⟨hm, hpr, hn1, hn2⟩
  · exact ⟨h1, hm⟩
  · exfalso
    rw [h1] at ha
    exact (pks_neg_one_ne_zero p) ha
  · exfalso
    have hxle : C a b ≤ -1 := by omega
    have hxge : -2 ≤ C a b := by
      by_contra h
      push Not at h
      have h1 : (0 : ℤ) ≤ -(C a b) := by omega
      have h2 : (0 : ℤ) ≤ -(C b a) := by omega
      have hmul : (3 : ℤ) * 1 ≤ (-(C a b)) * (-(C b a)) :=
        mul_le_mul (by omega : (3 : ℤ) ≤ -(C a b)) (by omega : (1 : ℤ) ≤ -(C b a))
          (by norm_num) h1
      nlinarith [hpr, hmul]
    have hx : C a b = -1 ∨ C a b = -2 := by omega
    rcases hx with hx | hx
    · rw [hx] at ha
      exact (pks_neg_one_ne_zero p) ha
    · rw [hx] at ha
      exact (pks_neg_two_ne_zero p hp3) ha
  · exact absurd hm h6

theorem pks_card_filter_reindex {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (e : Fin m ≃ ι) (M : CoxeterMatrix ι) (N : CoxeterMatrix (Fin m))
    (hM : M = N.reindex e) (x : ι) :
    (Finset.univ.filter (fun y : ι => y ≠ x ∧ M x y ≠ 2)).card =
      (Finset.univ.filter (fun k : Fin m => k ≠ e.symm x ∧ N (e.symm x) k ≠ 2)).card := by
  have hMe : ∀ y : ι, M x y = N (e.symm x) (e.symm y) := by
    intro y
    rw [hM, CoxeterMatrix.reindex_apply]
  apply Finset.card_bij (fun y _ => e.symm y)
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact ⟨fun h => hy.1 (e.symm.injective h), by rw [← hMe y]; exact hy.2⟩
  · intro y1 _ y2 _ h
    exact e.symm.injective h
  · intro k hk
    refine ⟨e k, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact ⟨fun h => hk.1 (by simpa using congrArg e.symm h),
      by rw [hMe]; simpa using hk.2⟩

theorem pks_no_label6 {ι : Type} [Fintype ι] [DecidableEq ι] (c : ℕ)
    (hcard : Fintype.card ι = c) (hc3 : 3 ≤ c) (hc5 : c ≤ 5)
    {M : CoxeterMatrix ι} (hW : CFSG.StandardType.GGIsWeylMatrix M) (a b : ι) : M a b ≠ 6 := by
  rcases hW with
    ⟨n, e, hn1, hA | ⟨hn2, hB⟩ | ⟨hn4, hD⟩⟩ | ⟨e, hE6⟩ | ⟨e, hE7⟩ | ⟨e, hE8⟩ |
      ⟨e, hF4⟩ | ⟨e, hG2⟩
  · rw [hA, CoxeterMatrix.reindex_apply]
    have hn : n = c := by rw [pks_card_fin_eq e, hcard]
    subst n
    exact (pks_An_ne c hc3 hc5 _ _).2
  · rw [hB, CoxeterMatrix.reindex_apply]
    have hn : n = c := by rw [pks_card_fin_eq e, hcard]
    subst n
    exact pks_Bn_no6 c hc3 hc5 _ _
  · rw [hD, CoxeterMatrix.reindex_apply]
    have hn : n = c := by rw [pks_card_fin_eq e, hcard]
    subst n
    exact (pks_Dn_ne c hn4 hc5 _ _).2
  · intro h
    have hc6 : c = 6 := by
      have hh := pks_card_fin_eq e
      rw [hcard] at hh
      exact hh.symm
    omega
  · intro h
    have hc7 : c = 7 := by
      have hh := pks_card_fin_eq e
      rw [hcard] at hh
      exact hh.symm
    omega
  · intro h
    have hc8 : c = 8 := by
      have hh := pks_card_fin_eq e
      rw [hcard] at hh
      exact hh.symm
    omega
  · rw [hF4, CoxeterMatrix.reindex_apply]
    exact pks_F4_no6 _ _
  · intro h
    have hc2 : c = 2 := by
      have hh := pks_card_fin_eq e
      rw [hcard] at hh
      exact hh.symm
    omega

theorem pks_label4_deg {ι : Type} [Fintype ι] [DecidableEq ι] (c : ℕ)
    (hcard : Fintype.card ι = c) (hc3 : 3 ≤ c) (hc5 : c ≤ 5)
    {M : CoxeterMatrix ι} (hW : CFSG.StandardType.GGIsWeylMatrix M) (a b : ι) (hab : M a b = 4) :
    ∀ x : ι, (Finset.univ.filter (fun y => y ≠ x ∧ M x y ≠ 2)).card ≤ 2 := by
  rcases hW with
    ⟨n, e, hn1, hA | ⟨hn2, hB⟩ | ⟨hn4, hD⟩⟩ | ⟨e, hE6⟩ | ⟨e, hE7⟩ | ⟨e, hE8⟩ |
      ⟨e, hF4⟩ | ⟨e, hG2⟩
  · exfalso
    have hn : n = c := by rw [pks_card_fin_eq e, hcard]
    subst n
    rw [hA, CoxeterMatrix.reindex_apply] at hab
    exact (pks_An_ne c hc3 hc5 _ _).1 hab
  · have hn : n = c := by rw [pks_card_fin_eq e, hcard]
    subst n
    intro x
    rw [pks_card_filter_reindex e M (CoxeterMatrix.B c) hB x]
    exact pks_Bn_deg c hc3 hc5 (e.symm x)
  · exfalso
    have hn : n = c := by rw [pks_card_fin_eq e, hcard]
    subst n
    rw [hD, CoxeterMatrix.reindex_apply] at hab
    exact (pks_Dn_ne c hn4 hc5 _ _).1 hab
  · exfalso
    have hc6 : c = 6 := by
      have hh := pks_card_fin_eq e
      rw [hcard] at hh
      exact hh.symm
    omega
  · exfalso
    have hc7 : c = 7 := by
      have hh := pks_card_fin_eq e
      rw [hcard] at hh
      exact hh.symm
    omega
  · exfalso
    have hc8 : c = 8 := by
      have hh := pks_card_fin_eq e
      rw [hcard] at hh
      exact hh.symm
    omega
  · intro x
    rw [pks_card_filter_reindex e M (CoxeterMatrix.F₄) hF4 x]
    exact pks_F4_deg (e.symm x)
  · exfalso
    have hc2 : c = 2 := by
      have hh := pks_card_fin_eq e
      rw [hcard] at hh
      exact hh.symm
    omega

theorem pks_S_card (s N : ℕ) (hs : s ≤ 2) (hN : N = 5 ∨ N = 6 ∨ N = 7)
    (S : Finset (Fin (N - 1)))
    (hS : ∀ i : Fin (N - 1), i ∈ S ↔ s ≤ (i : ℕ) ∧ (i : ℕ) < s + (N - 3)) :
    S.card = N - 3 := by
  rcases hN with rfl | rfl | rfl
  · interval_cases s
    · have h : S = ({0, 1} : Finset (Fin 4)) := by
        ext i; rw [hS]; fin_cases i <;> decide
      rw [h]; decide
    · have h : S = ({1, 2} : Finset (Fin 4)) := by
        ext i; rw [hS]; fin_cases i <;> decide
      rw [h]; decide
    · have h : S = ({2, 3} : Finset (Fin 4)) := by
        ext i; rw [hS]; fin_cases i <;> decide
      rw [h]; decide
  · interval_cases s
    · have h : S = ({0, 1, 2} : Finset (Fin 5)) := by
        ext i; rw [hS]; fin_cases i <;> decide
      rw [h]; decide
    · have h : S = ({1, 2, 3} : Finset (Fin 5)) := by
        ext i; rw [hS]; fin_cases i <;> decide
      rw [h]; decide
    · have h : S = ({2, 3, 4} : Finset (Fin 5)) := by
        ext i; rw [hS]; fin_cases i <;> decide
      rw [h]; decide
  · interval_cases s
    · have h : S = ({0, 1, 2, 3} : Finset (Fin 6)) := by
        ext i; rw [hS]; fin_cases i <;> decide
      rw [h]; decide
    · have h : S = ({1, 2, 3, 4} : Finset (Fin 6)) := by
        ext i; rw [hS]; fin_cases i <;> decide
      rw [h]; decide
    · have h : S = ({2, 3, 4, 5} : Finset (Fin 6)) := by
        ext i; rw [hS]; fin_cases i <;> decide
      rw [h]; decide

theorem pks_mem_posOpts_simple (p N pos : ℕ) (h : pos < N - 3) :
    (pos, p - 1, p - 1) ∈ posOpts p N := by
  simp only [posOpts, List.mem_append]
  left
  exact List.mem_map.mpr ⟨pos, List.mem_range.mpr h, rfl⟩

theorem pks_mem_posOpts_double_fst (p N pos : ℕ) (h : pos = 0 ∨ pos = N - 4) :
    (pos, p - 1, p - 2) ∈ posOpts p N := by
  simp only [posOpts, List.mem_append]
  right
  rcases h with h | h
  · rw [h]
    exact List.mem_flatMap.mpr ⟨0, by simp, by simp⟩
  · rw [h]
    exact List.mem_flatMap.mpr ⟨N - 4, by simp, by simp⟩

theorem pks_mem_posOpts_double_snd (p N pos : ℕ) (h : pos = 0 ∨ pos = N - 4) :
    (pos, p - 2, p - 1) ∈ posOpts p N := by
  simp only [posOpts, List.mem_append]
  right
  rcases h with h | h
  · rw [h]
    exact List.mem_flatMap.mpr ⟨0, by simp, by simp⟩
  · rw [h]
    exact List.mem_flatMap.mpr ⟨N - 4, by simp, by simp⟩

end CFSG.TwoNodeSmall
