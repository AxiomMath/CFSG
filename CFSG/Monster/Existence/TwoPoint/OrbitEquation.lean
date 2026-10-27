module

public import CFSG.Monster.Existence.TwoPoint.Classes
public import CFSG.Monster.Existence.TwoPoint.OrbitSum
public import CFSG.Monster.GMS.OrbitCount
public import CFSG.Monster.Existence.Defs

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G]

@[expose] def tableVIIOf : Fin 5 → TableVIIClass :=
  ![.two_A, .two_B, .four_A, .four_B, .six_A]

@[expose] def nineClass (a z₀ : G) (i : Fin 9) (y : G) : Prop :=
  if h : i.val = 0 then y = a
  else if h' : i.val < 6 then y ∈ tableVIISet a z₀ a (tableVIIOf ⟨i.val - 1, by omega⟩)
  else y ∈ oddNbr a z₀ a ∧ OddNbrType z₀ a y ⟨i.val - 6, by omega⟩

theorem nineClass_zero {a z₀ y : G} : nineClass a z₀ 0 y ↔ y = a := by
  simp [nineClass]

theorem nineClass_even {a z₀ y : G} (j : Fin 5) :
    nineClass a z₀ ⟨j.val + 1, by omega⟩ y ↔ y ∈ tableVIISet a z₀ a (tableVIIOf j) := by
  have h1 : j.val + 1 ≠ 0 := by omega
  have h2 : j.val + 1 < 6 := by omega
  simp only [nineClass, h1, h2, dite_false, dite_true]
  rfl

theorem nineClass_odd {a z₀ y : G} (k : Fin 3) :
    nineClass a z₀ ⟨k.val + 6, by omega⟩ y ↔ y ∈ oddNbr a z₀ a ∧ OddNbrType z₀ a y k := by
  have h1 : k.val + 6 ≠ 0 := by omega
  have h2 : ¬ k.val + 6 < 6 := by omega
  simp only [nineClass, h1, h2, dite_false]
  rfl

theorem nineClass_cases (i : Fin 9) : i = 0 ∨ (∃ j : Fin 5, i = ⟨j.val + 1, by omega⟩) ∨
    (∃ k : Fin 3, i = ⟨k.val + 6, by omega⟩) := by
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨0, rfl⟩)
  · exact Or.inr (Or.inl ⟨1, rfl⟩)
  · exact Or.inr (Or.inl ⟨2, rfl⟩)
  · exact Or.inr (Or.inl ⟨3, rfl⟩)
  · exact Or.inr (Or.inl ⟨4, rfl⟩)
  · exact Or.inr (Or.inr ⟨0, rfl⟩)
  · exact Or.inr (Or.inr ⟨1, rfl⟩)
  · exact Or.inr (Or.inr ⟨2, rfl⟩)

theorem tableVIIOf_injective : Function.Injective tableVIIOf := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | (simp [tableVIIOf] at h)

theorem tableVIIOf_surjective (K : TableVIIClass) : ∃ j, tableVIIOf j = K := by
  cases K
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩

theorem isConj_of_mem_tableVIISet {a z₀ x y : G} {K : TableVIIClass}
    (h : y ∈ tableVIISet a z₀ x K) : IsConj a y := by
  cases K <;> exact h.1

theorem orderOf_mul_of_mem_tableVIISet {a z₀ x y : G} (ha : orderOf a = 2) (hz : orderOf z₀ = 2)
    {K : TableVIIClass} (h : y ∈ tableVIISet a z₀ x K) : orderOf (x * y) = tableVIIOrder K := by
  cases K
  · rw [← orderOf_eq_of_isConj h.2, ha]; rfl
  · rw [← orderOf_eq_of_isConj h.2, hz]; rfl
  · exact h.2.1
  · exact h.2.1
  · exact h.2.1

theorem conj_mem_tableVIISet {a z₀ x y c : G} (hc : c ∈ Subgroup.centralizer ({x} : Set G))
    {K : TableVIIClass} (h : y ∈ tableVIISet a z₀ x K) : c * y * c⁻¹ ∈ tableVIISet a z₀ x K := by
  have hy := isConj_of_mem_tableVIISet h
  have hcx : c * x * c⁻¹ = x := by
    have := Subgroup.mem_centralizer_singleton_iff.1 hc
    rw [this, mul_inv_cancel_right]
  have e : x * (c * y * c⁻¹) = c * (x * y) * c⁻¹ := by
    calc x * (c * y * c⁻¹) = (c * x * c⁻¹) * (c * y * c⁻¹) := by rw [hcx]
      _ = c * (x * y) * c⁻¹ := by group
  refine (mem_tableVIISet_iff_of_isConj hy (hy.trans (isConj_iff.2 ⟨c, rfl⟩)) ?_ K).1 h
  rw [e]
  exact isConj_iff.2 ⟨c, rfl⟩

variable {a z₀ : G}

theorem nineClass_conj {c y : G} (hc : c ∈ Subgroup.centralizer ({a} : Set G)) (i : Fin 9)
    (h : nineClass a z₀ i y) : nineClass a z₀ i (c * y * c⁻¹) := by
  rcases nineClass_cases i with rfl | ⟨j, rfl⟩ | ⟨k, rfl⟩
  · rw [nineClass_zero] at h ⊢
    rw [h, Subgroup.mem_centralizer_singleton_iff.1 hc, mul_inv_cancel_right]
  · rw [nineClass_even] at h ⊢
    exact conj_mem_tableVIISet hc h
  · rw [nineClass_odd] at h ⊢
    exact ⟨oddNbr.conj_mem hc h.1, OddNbrType.conj hc h.2⟩

variable [Finite G] {d₀ : B}

theorem nineClass_unique
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {y : G}
    {i j : Fin 9} (hi : nineClass a z₀ i y) (hj : nineClass a z₀ j y) : i = j := by
  have ha : orderOf a = 2 := hG.1.1
  have hz : orderOf z₀ = 2 := hG.2.1
  have ho1 : orderOf (a * a) = 1 := by
    rw [orderOf_eq_one_iff]; exact mul_self_of_isConj ha (IsConj.refl a)
  have heven : ∀ {K : TableVIIClass}, y ∈ tableVIISet a z₀ a K → Even (orderOf (a * y)) ∧
      y ≠ a := fun {K} hK => by
    have := orderOf_mul_of_mem_tableVIISet ha hz hK
    refine ⟨by rw [this]; cases K <;> decide, fun hya => ?_⟩
    rw [hya, ho1] at this
    cases K <;> simp [tableVIIOrder] at this
  have hodd : ∀ {k : Fin 3}, (y ∈ oddNbr a z₀ a ∧ OddNbrType z₀ a y k) →
      Odd (orderOf (a * y)) ∧ y ≠ a := fun {k} hk => ⟨hk.1.2.2.1, hk.1.2.1⟩
  rcases nineClass_cases i with rfl | ⟨j₁, rfl⟩ | ⟨k₁, rfl⟩ <;>
    rcases nineClass_cases j with rfl | ⟨j₂, rfl⟩ | ⟨k₂, rfl⟩
  · rfl
  · rw [nineClass_zero] at hi; rw [nineClass_even] at hj
    exact ((heven hj).2 hi).elim
  · rw [nineClass_zero] at hi; rw [nineClass_odd] at hj
    exact ((hodd hj).2 hi).elim
  · rw [nineClass_zero] at hj; rw [nineClass_even] at hi
    exact ((heven hi).2 hj).elim
  · rw [nineClass_even] at hi hj
    obtain ⟨K, -, hK⟩ := table7_classify I.sls I.tableV I.leech I.tableIII I.tableIVBaby hG
      (IsConj.refl a) (isConj_of_mem_tableVIISet hi) (heven hi).1
    have e := (hK _ hi).trans (hK _ hj).symm
    rw [tableVIIOf_injective e]
  · rw [nineClass_even] at hi; rw [nineClass_odd] at hj
    exact ((Nat.not_even_iff_odd.2 (hodd hj).1) (heven hi).1).elim
  · rw [nineClass_zero] at hj; rw [nineClass_odd] at hi
    exact ((hodd hi).2 hj).elim
  · rw [nineClass_odd] at hi; rw [nineClass_even] at hj
    exact ((Nat.not_even_iff_odd.2 (hodd hi).1) (heven hj).1).elim
  · rw [nineClass_odd] at hi hj
    obtain ⟨k, -, hk⟩ := s348_type I.sls I.tableV I.leech I.leechOddPair I.tableIV hG
      (IsConj.refl a) hi.1
    have e := (hk _ hi.2).trans (hk _ hj.2).symm
    rw [e]

theorem nineClass_cover
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hex : OddExhaustive a z₀) {y : G} (hy : IsConj a y) : ∃ i, nineClass a z₀ i y := by
  by_cases hya : y = a
  · exact ⟨0, nineClass_zero.2 hya⟩
  rcases Nat.even_or_odd (orderOf (a * y)) with hev | hodd
  · obtain ⟨K, hK, -⟩ := table7_classify I.sls I.tableV I.leech I.tableIII I.tableIVBaby hG
      (IsConj.refl a) hy hev
    obtain ⟨j, rfl⟩ := tableVIIOf_surjective K
    exact ⟨⟨j.val + 1, by omega⟩, (nineClass_even j).2 hK⟩
  · have hyN := hex a y (IsConj.refl a) hy hya hodd
    obtain ⟨k, hk, -⟩ := s348_type I.sls I.tableV I.leech I.leechOddPair I.tableIV hG
      (IsConj.refl a) hyN
    exact ⟨⟨k.val + 6, by omega⟩, (nineClass_odd k).2 ⟨hyN, hk⟩⟩

theorem nineClass_transitive
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {i : Fin 9}
    {y y' : G} (hy : nineClass a z₀ i y) (hy' : nineClass a z₀ i y') :
    ∃ c ∈ Subgroup.centralizer ({a} : Set G), c * y * c⁻¹ = y' := by
  rcases nineClass_cases i with rfl | ⟨j, rfl⟩ | ⟨k, rfl⟩
  · rw [nineClass_zero] at hy hy'
    exact ⟨1, one_mem _, by rw [hy, hy']; group⟩
  · rw [nineClass_even] at hy hy'
    exact table7_transitive I.sls I.tableV I.leech I.tableIII I.tableIVBaby I.threeSwap
      I.leechPair hG (IsConj.refl a) hy hy'
  · rw [nineClass_odd] at hy hy'
    exact s348_orbit I.sls I.tableV I.leech I.leechOddPair I.tableIV hG (IsConj.refl a) hy.1
      hy'.1 hy.2 hy'.2

theorem card_twoA_eq_sum
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hex : OddExhaustive a z₀) (b : Fin 9 → G) (hb : ∀ i, nineClass a z₀ i (b i)) :
    Nat.card {x : G // IsConj a x} =
      ∑ i, ((Subgroup.centralizer ({b i} : Set G)).subgroupOf
        (Subgroup.centralizer ({a} : Set G))).index := by
  have hbA : ∀ i, IsConj a (b i) := fun i => by
    rcases nineClass_cases i with rfl | ⟨j, rfl⟩ | ⟨k, rfl⟩
    · rw [nineClass_zero.1 (hb 0)]
    · exact isConj_of_mem_tableVIISet ((nineClass_even j).1 (hb _))
    · exact ((nineClass_odd k).1 (hb _)).1.1
  refine card_conjClass_eq_sum_index a b hbA (fun x hx => ?_) (fun i j c hc e => ?_)
  · obtain ⟨i, hi⟩ := nineClass_cover I hG hex hx
    exact ⟨i, nineClass_transitive I hG (hb i) hi⟩
  · have h1 := nineClass_conj hc i (hb i)
    rw [e] at h1
    exact nineClass_unique I hG h1 (hb j)

@[expose] def oddStabOrder : Fin 3 → ℕ :=
  ![CFSG.Open.monsterFi23Order, CFSG.Open.monsterThOrder, CFSG.Open.monsterHNOrder]

omit [Finite G] in
theorem relIndex_mul_card_inf (a c : G) :
    ((Subgroup.centralizer ({c} : Set G)).subgroupOf (Subgroup.centralizer ({a} : Set G))).index *
      Nat.card ↥(Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({c} : Set G)) =
    Nat.card (Subgroup.centralizer ({a} : Set G)) := by
  rw [inf_comm]
  exact Subgroup.relIndex_mul_card _ _

theorem odd_twoPoint_eq_of_bounds
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hex : OddExhaustive a z₀) (hcard : Nat.card G = CFSG.Open.monsterOrder)
    (hCa : Nat.card (Subgroup.centralizer ({a} : Set G)) = twoBabyOrder) (y : Fin 3 → G)
    (hy : ∀ k, y k ∈ oddNbr a z₀ a ∧ OddNbrType z₀ a (y k) k) (K : Fin 3 → Subgroup G)
    (hK : ∀ k, K k ≤ cent2 a (y k)) (h : Fin 3 → ℕ) (hKc : ∀ k, Nat.card (K k) = h k)
    (hsumh : ∑ k, twoBabyOrder / h k = 30528114911948570624) :
    ∀ k, K k = cent2 a (y k) := by
  classical
  have hne : ∀ j : Fin 5, (tableVIISet a z₀ a (tableVIIOf j)).Nonempty := fun j =>
    table7_nonempty I.sls I.tableV I.leech I.tableIII I.tableIVBaby hG (IsConj.refl a) _
  let b : Fin 9 → G := fun i =>
    if h : i.val = 0 then a
    else if h' : i.val < 6 then (hne ⟨i.val - 1, by omega⟩).some
    else y ⟨i.val - 6, by omega⟩
  have hb : ∀ i, nineClass a z₀ i (b i) := by
    intro i
    rcases nineClass_cases i with rfl | ⟨j, rfl⟩ | ⟨k, rfl⟩
    · exact nineClass_zero.2 (by simp [b])
    · rw [nineClass_even]
      have h1 : j.val + 1 ≠ 0 := by omega
      have h2 : j.val + 1 < 6 := by omega
      simp only [b, h1, h2, dite_false, dite_true]
      exact (hne ⟨j.val + 1 - 1, by omega⟩).some_mem
    · rw [nineClass_odd]
      have h1 : k.val + 6 ≠ 0 := by omega
      have h2 : ¬ k.val + 6 < 6 := by omega
      simp only [b, h1, h2, dite_false]
      exact hy ⟨k.val + 6 - 6, by omega⟩
  have hsum := card_twoA_eq_sum I hG hex b hb
  have hcl := card_conjClass_mul_card_centralizer a
  rw [hcard, hCa] at hcl
  have hA : Nat.card {x : G // IsConj a x} = 97239461142009186000 := by
    have h2 : twoBabyOrder ≠ 0 := by norm_num [twoBabyOrder]
    have : Nat.card {x : G // IsConj a x} = CFSG.Open.monsterOrder / twoBabyOrder := by
      rw [← hcl, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero h2)]
    rw [this]
    norm_num [CFSG.Open.monsterOrder, twoBabyOrder]
  set idx : Fin 9 → ℕ := fun i => ((Subgroup.centralizer ({b i} : Set G)).subgroupOf
    (Subgroup.centralizer ({a} : Set G))).index with hidx
  have hidxmul : ∀ i, idx i * Nat.card ↥(cent2 a (b i)) = twoBabyOrder := fun i => by
    rw [← hCa]
    exact relIndex_mul_card_inf a (b i)
  have hidx0 : idx 0 = 1 := by
    have e : b 0 = a := by simp [b]
    simp only [hidx, e, Subgroup.subgroupOf_self, Subgroup.index_top]
  have hidxe : ∀ j : Fin 5, idx ⟨j.val + 1, by omega⟩ = tableVIISize (tableVIIOf j) := by
    intro j
    have hm := (nineClass_even j).1 (hb ⟨j.val + 1, by omega⟩)
    have hc := table7_card I.sls I.tableV I.leech I.tableIII I.tableIVBaby I.threeSwap
      I.leechPair hG (IsConj.refl a) hm
    have h1 := hidxmul ⟨j.val + 1, by omega⟩
    rw [cent2, cent, cent, hc, ← tableVIIStab_mul_size (tableVIIOf j)] at h1
    exact Nat.eq_of_mul_eq_mul_right (tableVIIStab_pos _) (by rw [h1, mul_comm])
  set s : Fin 3 → ℕ := fun k => Nat.card ↥(cent2 a (y k)) with hs
  have hyb : ∀ k : Fin 3, b ⟨k.val + 6, by omega⟩ = y k := by
    intro k
    have h1 : k.val + 6 ≠ 0 := by omega
    have h2 : ¬ k.val + 6 < 6 := by omega
    simp only [b, h1, h2, dite_false]
    exact congrArg y (Fin.ext (by simp))
  have hidxo : ∀ k : Fin 3, idx ⟨k.val + 6, by omega⟩ = twoBabyOrder / s k := by
    intro k
    have h1 := hidxmul ⟨k.val + 6, by omega⟩
    rw [hyb k] at h1
    have hpos : 0 < s k := Nat.card_pos
    rw [← h1, Nat.mul_div_cancel _ hpos]
  have hoddval : ∑ k : Fin 3, twoBabyOrder / s k = 30528114911948570624 := by
    have e := hsum
    rw [hA] at e
    have e' : (97239461142009186000 : ℕ) = ∑ i, idx i := e
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at e' ⊢
    have h0 := hidx0
    have he0 := hidxe 0
    have he1 := hidxe 1
    have he2 := hidxe 2
    have he3 := hidxe 3
    have he4 := hidxe 4
    have ho0 := hidxo 0
    have ho1 := hidxo 1
    have ho2 := hidxo 2
    simp only [tableVIIOf, tableVIISize, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four] at he0 he1 he2 he3 he4
    have : idx 0 + (idx 1 + (idx 2 + (idx 3 + (idx 4 + (idx 5 + (idx 6 + (idx 7 + (idx 8 + 0))))))))
        = 97239461142009186000 := by
      rw [e']
      rfl
    rw [show (1 : Fin 9) = ⟨(0 : Fin 5).val + 1, by omega⟩ from rfl,
      show (2 : Fin 9) = ⟨(1 : Fin 5).val + 1, by omega⟩ from rfl,
      show (3 : Fin 9) = ⟨(2 : Fin 5).val + 1, by omega⟩ from rfl,
      show (4 : Fin 9) = ⟨(3 : Fin 5).val + 1, by omega⟩ from rfl,
      show (5 : Fin 9) = ⟨(4 : Fin 5).val + 1, by omega⟩ from rfl,
      show (6 : Fin 9) = ⟨(0 : Fin 3).val + 6, by omega⟩ from rfl,
      show (7 : Fin 9) = ⟨(1 : Fin 3).val + 6, by omega⟩ from rfl,
      show (8 : Fin 9) = ⟨(2 : Fin 3).val + 6, by omega⟩ from rfl, h0, he0, he1, he2, he3, he4,
      ho0, ho1, ho2] at this
    norm_num [twoBabyOrder] at this ⊢
    omega
  have hodd : ∑ k : Fin 3, twoBabyOrder / s k = ∑ k : Fin 3, twoBabyOrder / h k :=
    hoddval.trans hsumh.symm
  have hdivN : ∀ k ∈ (Finset.univ : Finset (Fin 3)), s k ∣ twoBabyOrder := fun k _ => by
    rw [← hCa]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hhs : ∀ k, h k ∣ s k := fun k => by
    rw [← hKc k]
    exact Subgroup.card_dvd_of_le (hK k)
  have heq := eq_of_sum_div_eq_sum_div Finset.univ (by norm_num [twoBabyOrder] : 0 < twoBabyOrder)
    hdivN (fun k hk => (hhs k).trans (hdivN k hk))
    (fun k _ => by rw [← hKc k]; exact Nat.card_pos)
    (fun k _ => Nat.le_of_dvd Nat.card_pos (hhs k)) hodd
  intro k
  refine Subgroup.eq_of_le_of_card_ge (hK k) ?_
  rw [hKc k]
  exact (heq k (Finset.mem_univ k)).le

theorem odd_twoPoint_eq
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hex : OddExhaustive a z₀) (hcard : Nat.card G = CFSG.Open.monsterOrder)
    (hCa : Nat.card (Subgroup.centralizer ({a} : Set G)) = twoBabyOrder) (y : Fin 3 → G)
    (σ : Equiv.Perm (Fin 3)) (hy : ∀ k, y k ∈ oddNbr a z₀ a ∧ OddNbrType z₀ a (y k) (σ k))
    (K : Fin 3 → Subgroup G) (hK : ∀ k, K k ≤ cent2 a (y k))
    (hKc : ∀ k, Nat.card (K k) = oddStabOrder k) :
    ∀ k, K k = cent2 a (y k) := by
  have hy' : ∀ j, y (σ.symm j) ∈ oddNbr a z₀ a ∧ OddNbrType z₀ a (y (σ.symm j)) j := fun j => by
    have := hy (σ.symm j)
    rwa [Equiv.apply_symm_apply] at this
  have hsum : ∑ j, twoBabyOrder / oddStabOrder (σ.symm j) = 30528114911948570624 := by
    rw [Equiv.sum_comp σ.symm (fun k => twoBabyOrder / oddStabOrder k)]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    norm_num [oddStabOrder, twoBabyOrder, CFSG.Open.monsterFi23Order, CFSG.Open.monsterThOrder,
      CFSG.Open.monsterHNOrder]
  have h := odd_twoPoint_eq_of_bounds I hG hex hcard hCa (fun j => y (σ.symm j)) hy'
    (fun j => K (σ.symm j)) (fun j => hK _) (fun j => oddStabOrder (σ.symm j)) (fun j => hKc _) hsum
  intro k
  have := h (σ k)
  simpa using this

end CFSG.Monster.Existence
