module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneAbstract

public section

namespace CFSG.StandardType

namespace ChoiceTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Plane

@[expose] def dot3 (a c : ZMod 3 × ZMod 3) : ZMod 3 := a.1 * c.1 + a.2 * c.2

@[expose] def det2 (x y : ZMod 3 × ZMod 3) : ZMod 3 := x.1 * y.2 - x.2 * y.1

@[expose] def perp3 (x : ZMod 3 × ZMod 3) : ZMod 3 × ZMod 3 := (x.2, -x.1)

@[expose] def norm3 (x : ZMod 3 × ZMod 3) : ZMod 3 × ZMod 3 :=
  if x.1 = 2 ∨ (x.1 = 0 ∧ x.2 = 2) then -x else x

theorem dot3_perp3_eq_zero_iff : ∀ x y : ZMod 3 × ZMod 3, dot3 (perp3 x) y = 0 ↔ det2 x y = 0 := by
  decide

theorem det2_eq_zero_iff : ∀ x y : ZMod 3 × ZMod 3, x ≠ 0 →
    (det2 x y = 0 ↔ (y = 0 ∨ y = x ∨ y = -x)) := by
  decide

theorem norm3_eq_norm3_iff : ∀ x y : ZMod 3 × ZMod 3, norm3 x = norm3 y ↔ (x = y ∨ x = -y) := by
  decide

theorem norm3_mem : ∀ x : ZMod 3 × ZMod 3,
    norm3 x ∈ ({(0, 0), (1, 0), (0, 1), (1, 1), (1, 2)} : Finset (ZMod 3 × ZMod 3)) := by
  decide

theorem norm3_mem_of_ne_zero : ∀ x : ZMod 3 × ZMod 3, x ≠ 0 →
    norm3 x ∈ ({(1, 0), (0, 1), (1, 1), (1, 2)} : Finset (ZMod 3 × ZMod 3)) := by
  decide

theorem perp3_ne_zero : ∀ x : ZMod 3 × ZMod 3, x ≠ 0 → perp3 x ≠ 0 := by decide

theorem dot3_zero_right : ∀ a : ZMod 3 × ZMod 3, dot3 a 0 = 0 := by decide

theorem card_dot3_ne_zero : ∀ c : ZMod 3 × ZMod 3,
    (Finset.univ.filter fun a : ZMod 3 × ZMod 3 => dot3 a c ≠ 0).card = if c = 0 then 0 else 6 := by
  decide

theorem sum_ite_zero_two :
    ∑ a : ZMod 3 × ZMod 3, (if a = 0 then 0 else 2 : ℕ) = 16 := by decide

theorem dot3_perp3_ne_zero (x y : ZMod 3 × ZMod 3) (hx : x ≠ 0) (hy : y ≠ 0) (hyx : y ≠ x)
    (hyx' : y ≠ -x) : dot3 (perp3 x) y ≠ 0 := by
  rw [Ne, dot3_perp3_eq_zero_iff, det2_eq_zero_iff x y hx]
  rintro (h | h | h)
  · exact hy h
  · exact hyx h
  · exact hyx' h

theorem dot3_perp3_self : ∀ x : ZMod 3 × ZMod 3, dot3 (perp3 x) x = 0 := by decide

theorem dot3_perp3_neg : ∀ x : ZMod 3 × ZMod 3, dot3 (perp3 x) (-x) = 0 := by decide

end Plane

section Chars

variable {s : ℕ}

theorem exists_ne_norm3_eq {S : Finset (ZMod 3 × ZMod 3)} {ι : Type} [Fintype ι]
    (hS : S.card < Fintype.card ι) (c : ι → ZMod 3 × ZMod 3) (hc : ∀ i, norm3 (c i) ∈ S) :
    ∃ i j, i ≠ j ∧ (c i = c j ∨ c i = -c j) := by
  obtain ⟨i, j, hij, h⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i => (⟨norm3 (c i), hc i⟩ : S)) (by rwa [Fintype.card_coe])
  exact ⟨i, j, hij, (norm3_eq_norm3_iff _ _).mp (congrArg Subtype.val h)⟩

variable (c : Fin s → ZMod 3 × ZMod 3)

@[expose] def wt3 (a : ZMod 3 × ZMod 3) : ℕ :=
  (Finset.univ.filter fun l => dot3 a (c l) ≠ 0).card

@[expose] def lowSupp : Finset (Fin s) :=
  Finset.univ.filter fun i => ∃ a, dot3 a (c i) ≠ 0 ∧ wt3 c a ≤ 3

variable {c}

theorem wt3_le_sub {a : ZMod 3 × ZMod 3} {T : Finset (Fin s)} (hT : ∀ l ∈ T, dot3 a (c l) = 0) :
    wt3 c a ≤ s - T.card := by
  have h1 : (Finset.univ.filter fun l => dot3 a (c l) ≠ 0) ⊆ Finset.univ \ T := by
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact fun hlT => hl (hT l hlT)
  have h2 := Finset.card_le_card h1
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin] at h2
  exact h2

theorem wt3_le_nonzero (a : ZMod 3 × ZMod 3) :
    wt3 c a ≤ (Finset.univ.filter fun l => c l ≠ 0).card := by
  refine Finset.card_le_card fun l hl => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
  intro h0
  rw [h0, dot3_zero_right] at hl
  exact hl rfl

theorem wt3_zero : wt3 c 0 = 0 := by
  rw [wt3, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro l _
  simp [dot3]

theorem sum_wt3 : ∑ a, wt3 c a = 6 * (Finset.univ.filter fun l => c l ≠ 0).card := by
  have h1 : ∀ a, wt3 c a = ∑ l, if dot3 a (c l) ≠ 0 then 1 else 0 := fun a => by
    rw [wt3, Finset.card_filter]
  simp only [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ l, (∑ a : ZMod 3 × ZMod 3, if dot3 a (c l) ≠ 0 then 1 else 0) =
      if c l = 0 then 0 else 6 := fun l => by
    rw [← Finset.card_filter, card_dot3_ne_zero]
  simp only [h2]
  rw [Finset.card_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hl : c l = 0 <;> simp [hl]

theorem chars_rel (hs : 4 ≤ s) (hind : ∀ a, a ≠ 0 → ∃ i, dot3 a (c i) ≠ 0)
    (hA : (lowSupp c).card ≤ 3) (hB : s = 4 → ∀ a, wt3 c a ≠ 3) :
    (∃ i j, i ≠ j ∧ (c i = c j ∨ c i = -c j)) ∧
      (s = 4 → ∃ i j, i ≠ j ∧ c i = 0 ∧ c j = 0) := by
  classical
  have hlow : ∀ i j, c i ≠ 0 → c j ≠ 0 → c i ≠ c j → c i ≠ -c j →
      wt3 c (perp3 (c j)) ≤ 3 → i ∈ lowSupp c := fun i j hi hj h1 h2 hw => by
    simp only [lowSupp, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨perp3 (c j), dot3_perp3_ne_zero _ _ hj hi h1 h2, hw⟩
  have part2 : s = 4 → ∃ i j, i ≠ j ∧ c i = 0 ∧ c j = 0 := by
    intro h4
    subst h4
    by_contra hno
    push Not at hno
    have hZ : (Finset.univ.filter fun l => c l = 0).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro i hi j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
      by_contra hij
      exact hno i j hij hi hj
    have hsplit : (Finset.univ.filter fun l => c l = 0).card +
        (Finset.univ.filter fun l => c l ≠ 0).card = 4 := by
      have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 4)))
        (fun l => c l = 0)
      rw [Finset.card_univ, Fintype.card_fin] at h
      exact h
    rcases (show (Finset.univ.filter fun l => c l = 0).card = 0 ∨
        (Finset.univ.filter fun l => c l = 0).card = 1 by omega) with hz0 | hz1
    ·
      have hall : ∀ i, c i ≠ 0 := fun i hi => by
        have : i ∈ Finset.univ.filter fun l => c l = 0 := by simp [hi]
        rw [Finset.card_eq_zero] at hz0
        rw [hz0] at this
        exact Finset.notMem_empty i this
      have hU : lowSupp c = Finset.univ := by
        refine Finset.eq_univ_of_forall fun i => ?_
        by_contra hiU
        have hpar : ∀ j, c j = c i ∨ c j = -c i := by
          intro j
          by_contra hj
          push Not at hj
          refine hiU (hlow i j (hall i) (hall j) (fun h => hj.1 h.symm) (fun h => hj.2 ?_) ?_)
          · rw [h, neg_neg]
          · refine (wt3_le_sub (T := {j}) fun l hl => ?_).trans (by simp)
            rw [Finset.mem_singleton] at hl
            rw [hl]
            exact dot3_perp3_self _
        obtain ⟨l, hl⟩ := hind (perp3 (c i)) (perp3_ne_zero _ (hall i))
        rcases hpar l with h | h
        · exact hl (by rw [h]; exact dot3_perp3_self _)
        · exact hl (by rw [h]; exact dot3_perp3_neg _)
      rw [hU, Finset.card_univ, Fintype.card_fin] at hA
      omega
    ·
      have hnz : (Finset.univ.filter fun l => c l ≠ 0).card = 3 := by omega
      have hle : ∀ a, wt3 c a ≤ if a = 0 then 0 else 2 := by
        intro a
        by_cases ha : a = 0
        · rw [ite_eq_left ha, ha, wt3_zero]
        · rw [ite_eq_right ha]
          have h1 := wt3_le_nonzero (c := c) a
          have h2 := hB rfl a
          omega
      have hsum := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => hle a
      rw [sum_wt3, hnz, sum_ite_zero_two] at hsum
      omega
  refine ⟨?_, part2⟩
  by_contra hno
  push Not at hno
  rcases (show s = 4 ∨ s = 5 ∨ 6 ≤ s by omega) with h4 | h5 | h6
  · obtain ⟨i, j, hij, hi, hj⟩ := part2 h4
    exact (hno i j hij).1 (hi.trans hj.symm)
  · subst h5
    have hZ : (Finset.univ.filter fun l => c l = 0).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro i hi j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
      by_contra hij
      exact (hno i j hij).1 (hi.trans hj.symm)
    have hNZ : (Finset.univ.filter fun l => c l ≠ 0).card ≤ 4 := by
      have hinj : Set.InjOn norm3 ((Finset.univ.filter fun l => c l ≠ 0).image c : Set _) := by
        intro x hx y hy hxy
        simp only [Finset.coe_image, Finset.coe_filter, Set.mem_image, Set.mem_ofPred_eq,
          Finset.mem_univ, true_and] at hx hy
        obtain ⟨i, -, rfl⟩ := hx
        obtain ⟨j, -, rfl⟩ := hy
        rcases (norm3_eq_norm3_iff _ _).mp hxy with h | h
        · exact h
        · by_cases hij : i = j
          · rw [hij]
          · exact absurd h (hno i j hij).2
      have himg : ((Finset.univ.filter fun l => c l ≠ 0).image c).card =
          (Finset.univ.filter fun l => c l ≠ 0).card := by
        refine Finset.card_image_of_injOn fun i hi j hj hij => ?_
        by_contra hne
        exact (hno i j hne).1 hij
      have hmap : ∀ x ∈ (Finset.univ.filter fun l => c l ≠ 0).image c,
          norm3 x ∈ ({(1, 0), (0, 1), (1, 1), (1, 2)} : Finset (ZMod 3 × ZMod 3)) := by
        intro x hx
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        obtain ⟨i, hi, rfl⟩ := hx
        exact norm3_mem_of_ne_zero _ hi
      have h1 := Finset.card_le_card_of_injOn norm3 hmap hinj
      rw [himg] at h1
      exact h1.trans (by decide)
    have hsplit : (Finset.univ.filter fun l => c l = 0).card +
        (Finset.univ.filter fun l => c l ≠ 0).card = 5 := by
      have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 5)))
        (fun l => c l = 0)
      rw [Finset.card_univ, Fintype.card_fin] at h
      exact h
    obtain ⟨z, hz⟩ : ∃ z, c z = 0 := by
      by_contra hz
      push Not at hz
      have : (Finset.univ.filter fun l => c l = 0).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        exact fun l _ => hz l
      omega
    have hsub : (Finset.univ.filter fun l => c l ≠ 0) ⊆ lowSupp c := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      obtain ⟨j, hji, hj⟩ : ∃ j, j ≠ i ∧ c j ≠ 0 := by
        by_contra hj
        push Not at hj
        have : (Finset.univ.filter fun l => c l ≠ 0) ⊆ {i} := by
          intro l hl
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
          rw [Finset.mem_singleton]
          by_contra hli
          exact hl (hj l hli)
        have h1 := Finset.card_le_card this
        rw [Finset.card_singleton] at h1
        omega
      have hzj : z ≠ j := fun h => hj (h ▸ hz)
      refine hlow i j hi hj (hno i j hji.symm).1 (hno i j hji.symm).2 ?_
      refine (wt3_le_sub (T := {z, j}) fun l hl => ?_).trans ?_
      · rw [Finset.mem_insert, Finset.mem_singleton] at hl
        rcases hl with rfl | rfl
        · rw [hz, dot3_zero_right]
        · exact dot3_perp3_self _
      · rw [Finset.card_pair hzj]
    have h1 := Finset.card_le_card hsub
    omega
  · obtain ⟨i, j, hij, h⟩ := exists_ne_norm3_eq (ι := Fin s)
      (S := {(0, 0), (1, 0), (0, 1), (1, 1), (1, 2)})
      (lt_of_lt_of_le (by decide : ({(0, 0), (1, 0), (0, 1), (1, 1), (1, 2)} :
        Finset (ZMod 3 × ZMod 3)).card < 6) (by rw [Fintype.card_fin]; exact h6))
      c fun i => norm3_mem _
    rcases h with h | h
    · exact (hno i j hij).1 h
    · exact (hno i j hij).2 h

end Chars

end ChoiceTwo

end CFSG.StandardType
