module

public import CFSG.Quasithin.Background.B4Models
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1KitGGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

private theorem s16t3_zmod_two_eq (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

private theorem s16t3_zmod_two_ne_zero (x : ZMod 2) : ¬ x = 0 ↔ x = 1 := by
  constructor
  · intro h
    rcases s16t3_zmod_two_eq x with h0 | h1
    · exact absurd h0 h
    · exact h1
  · intro h h0
    rw [h] at h0
    exact one_ne_zero h0

private theorem s16t3_two_triplet_finsets {n : ℕ} (hn : 8 ≤ n) (f : Fin n → ZMod 2) :
    ∃ P Q : Finset (Fin n), P.card = 3 ∧ Q.card = 3 ∧ Disjoint P Q ∧
      (∃ c : ZMod 2, ∀ i ∈ P, f i = c) ∧ (∃ c : ZMod 2, ∀ i ∈ Q, f i = c) := by
  classical
  set S0 : Finset (Fin n) := Finset.univ.filter (fun i => f i = 0) with hS0
  set S1 : Finset (Fin n) := Finset.univ.filter (fun i => f i = 1) with hS1
  have hmem0 : ∀ i, i ∈ S0 ↔ f i = 0 := by
    intro i
    rw [hS0]
    simp
  have hmem1 : ∀ i, i ∈ S1 ↔ f i = 1 := by
    intro i
    rw [hS1]
    simp
  have hS1' : (Finset.univ.filter fun i => ¬ f i = 0) = S1 := by
    ext i
    rw [Finset.mem_filter, hmem1]
    simp only [Finset.mem_univ, true_and]
    exact s16t3_zmod_two_ne_zero (f i)
  have hsum : S0.card + S1.card = n := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (p := fun i => f i = 0)
    rw [← hS0, hS1', Finset.card_univ, Fintype.card_fin] at h
    exact h
  by_cases h0 : 6 ≤ S0.card
  · obtain ⟨T, hTS0, hTcard⟩ := Finset.exists_subset_card_eq (s := S0) h0
    obtain ⟨P, hPT, hPcard⟩ := Finset.exists_subset_card_eq (s := T) (n := 3) (by omega)
    refine ⟨P, T \ P, hPcard, ?_, ?_, ?_, ?_⟩
    · rw [Finset.card_sdiff_of_subset hPT, hTcard, hPcard]
    · exact Finset.disjoint_left.mpr (fun x hxP hxTP => (Finset.mem_sdiff.mp hxTP).2 hxP)
    · exact ⟨0, fun i hi => (hmem0 i).mp (hTS0 (hPT hi))⟩
    · exact ⟨0, fun i hi => (hmem0 i).mp (hTS0 (Finset.mem_sdiff.mp hi).1)⟩
  · rw [not_le] at h0
    by_cases h1 : 6 ≤ S1.card
    · obtain ⟨T, hTS1, hTcard⟩ := Finset.exists_subset_card_eq (s := S1) h1
      obtain ⟨P, hPT, hPcard⟩ := Finset.exists_subset_card_eq (s := T) (n := 3) (by omega)
      refine ⟨P, T \ P, hPcard, ?_, ?_, ?_, ?_⟩
      · rw [Finset.card_sdiff_of_subset hPT, hTcard, hPcard]
      · exact Finset.disjoint_left.mpr (fun x hxP hxTP => (Finset.mem_sdiff.mp hxTP).2 hxP)
      · exact ⟨1, fun i hi => (hmem1 i).mp (hTS1 (hPT hi))⟩
      · exact ⟨1, fun i hi => (hmem1 i).mp (hTS1 (Finset.mem_sdiff.mp hi).1)⟩
    · rw [not_le] at h1
      have hS0c : 3 ≤ S0.card := by omega
      have hS1c : 3 ≤ S1.card := by omega
      obtain ⟨P, hPS0, hPcard⟩ := Finset.exists_subset_card_eq (s := S0) hS0c
      obtain ⟨Q, hQS1, hQcard⟩ := Finset.exists_subset_card_eq (s := S1) hS1c
      refine ⟨P, Q, hPcard, hQcard, ?_, ?_, ?_⟩
      · apply Finset.disjoint_left.mpr
        intro x hxP hxQ
        have hx0 : f x = 0 := (hmem0 x).mp (hPS0 hxP)
        have hx1 : f x = 1 := (hmem1 x).mp (hQS1 hxQ)
        exact zero_ne_one (hx0.symm.trans hx1)
      · exact ⟨0, fun i hi => (hmem0 i).mp (hPS0 hi)⟩
      · exact ⟨1, fun i hi => (hmem1 i).mp (hQS1 hi)⟩

private theorem s16t3_exists_two_triples {n : ℕ} (hn : 8 ≤ n) (f : Fin n → ZMod 2) :
    ∃ p₁ p₂ p₃ q₁ q₂ q₃ : Fin n,
      p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₂ ≠ p₃ ∧ q₁ ≠ q₂ ∧ q₁ ≠ q₃ ∧ q₂ ≠ q₃ ∧
      Disjoint ({p₁, p₂, p₃} : Finset (Fin n)) ({q₁, q₂, q₃} : Finset (Fin n)) ∧
      f p₁ = f p₂ ∧ f p₁ = f p₃ ∧ f q₁ = f q₂ ∧ f q₁ = f q₃ := by
  obtain ⟨P, Q, hPcard, hQcard, hPQ, ⟨cP, hcP⟩, ⟨cQ, hcQ⟩⟩ := s16t3_two_triplet_finsets hn f
  obtain ⟨p₁, p₂, p₃, hp12, hp13, hp23, hPeq⟩ := Finset.card_eq_three.mp hPcard
  obtain ⟨q₁, q₂, q₃, hq12, hq13, hq23, hQeq⟩ := Finset.card_eq_three.mp hQcard
  refine ⟨p₁, p₂, p₃, q₁, q₂, q₃, hp12, hp13, hp23, hq12, hq13, hq23, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hPeq, ← hQeq]
    exact hPQ
  · have h1 := hcP p₁ (by rw [hPeq]; simp)
    have h2 := hcP p₂ (by rw [hPeq]; simp)
    rw [h1, h2]
  · have h1 := hcP p₁ (by rw [hPeq]; simp)
    have h2 := hcP p₃ (by rw [hPeq]; simp)
    rw [h1, h2]
  · have h1 := hcQ q₁ (by rw [hQeq]; simp)
    have h2 := hcQ q₂ (by rw [hQeq]; simp)
    rw [h1, h2]
  · have h1 := hcQ q₁ (by rw [hQeq]; simp)
    have h2 := hcQ q₃ (by rw [hQeq]; simp)
    rw [h1, h2]

private theorem s16t3_permAct_swap_mul_swap {n : ℕ} {x : G6.PermMod n} {a b c : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hb : Multiplicative.toAdd x a = Multiplicative.toAdd x b)
    (hc : Multiplicative.toAdd x a = Multiplicative.toAdd x c) :
    G6.permAct n (Equiv.swap a b * Equiv.swap a c) x = x := by
  apply Multiplicative.toAdd.injective
  funext i
  set σ : Equiv.Perm (Fin n) := Equiv.swap a b * Equiv.swap a c with hσ
  rw [G6.permAct_apply]
  show Multiplicative.toAdd x (σ⁻¹ i) = Multiplicative.toAdd x i
  have hout : ∀ y, ¬ (y = a ∨ y = b ∨ y = c) → σ y = y := by
    intro y hy
    have hya : y ≠ a := fun h => hy (Or.inl h)
    have hyb : y ≠ b := fun h => hy (Or.inr (Or.inl h))
    have hyc : y ≠ c := fun h => hy (Or.inr (Or.inr h))
    rw [hσ, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hya hyc,
      Equiv.swap_apply_of_ne_of_ne hya hyb]
  have hfT : ∀ y, (y = a ∨ y = b ∨ y = c) →
      Multiplicative.toAdd x y = Multiplicative.toAdd x a := by
    rintro y (rfl | rfl | rfl)
    · rfl
    · exact hb.symm
    · exact hc.symm
  by_cases hi : i = a ∨ i = b ∨ i = c
  · have hin : σ⁻¹ i = a ∨ σ⁻¹ i = b ∨ σ⁻¹ i = c := by
      by_contra h
      have h1 : σ (σ⁻¹ i) = σ⁻¹ i := hout (σ⁻¹ i) h
      have h2 : σ (σ⁻¹ i) = i := by simp
      rw [h2] at h1
      exact h (by rw [← h1]; exact hi)
    rw [hfT _ hin, hfT _ hi]
  · have hfix : σ⁻¹ i = i := by
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact (hout i hi).symm
    rw [hfix]

private theorem s16t3_permAct_closure_fixes {n : ℕ} {x : G6.PermMod n}
    {a b : ↥(alternatingGroup (Fin n))}
    (ha : G6.permAct n (a : Equiv.Perm (Fin n)) x = x)
    (hb : G6.permAct n (b : Equiv.Perm (Fin n)) x = x) :
    ∀ γ ∈ Subgroup.closure ({a, b} : Set ↥(alternatingGroup (Fin n))),
      G6.permAct n (γ : Equiv.Perm (Fin n)) x = x := by
  intro γ hγ
  induction hγ using Subgroup.closure_induction with
  | mem y hy =>
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact ha
      · exact hb
  | one => simp
  | mul y z hy hz ihy ihz =>
      rw [Subgroup.coe_mul, map_mul, MulAut.mul_apply, ihz, ihy]
  | inv y hy ihy =>
      rw [Subgroup.coe_inv, map_inv, MulAut.inv_apply]
      exact (MulEquiv.symm_apply_eq (G6.permAct n (y : Equiv.Perm (Fin n)))).mpr ihy.symm

theorem s16t3_good_alt_dn {n : ℕ} (hn : 8 ≤ n) (m : ↥(FFModel.altDn n).sec) :
    ∃ F : Subgroup ↥(alternatingGroup (Fin n)), IsPGroup 3 ↥F ∧ ¬ IsCyclic ↥F ∧
      ∀ γ ∈ F, (FFModel.altDn n).act γ (m : (FFModel.altDn n).Amb) * (m : (FFModel.altDn n).Amb)⁻¹ ∈
        (FFModel.altDn n).ker := by
  classical
  let mv : (FFModel.altDn n).Amb := (m : (FFModel.altDn n).Amb)
  let f : Fin n → ZMod 2 := Multiplicative.toAdd mv
  obtain ⟨p₁, p₂, p₃, q₁, q₂, q₃, hp12, hp13, hp23, hq12, hq13, hq23, hPQ, hp, hp', hq, hq'⟩ :=
    s16t3_exists_two_triples hn f
  set σ₁ : Equiv.Perm (Fin n) := Equiv.swap p₁ p₂ * Equiv.swap p₁ p₃ with hσ₁
  set σ₂ : Equiv.Perm (Fin n) := Equiv.swap q₁ q₂ * Equiv.swap q₁ q₃ with hσ₂
  have h3₁ : σ₁.IsThreeCycle := Equiv.Perm.isThreeCycle_swap_mul_swap_same hp12 hp13 hp23
  have h3₂ : σ₂.IsThreeCycle := Equiv.Perm.isThreeCycle_swap_mul_swap_same hq12 hq13 hq23
  have hfix1 : G6.permAct n σ₁ mv = mv :=
    s16t3_permAct_swap_mul_swap (x := mv) hp12 hp13 hp23 hp hp'
  have hfix2 : G6.permAct n σ₂ mv = mv :=
    s16t3_permAct_swap_mul_swap (x := mv) hq12 hq13 hq23 hq hq'
  let a : ↥(alternatingGroup (Fin n)) := ⟨σ₁, h3₁.mem_alternatingGroup⟩
  let b : ↥(alternatingGroup (Fin n)) := ⟨σ₂, h3₂.mem_alternatingGroup⟩
  have ha3 : a ^ 3 = 1 := by
    apply Subtype.ext
    show σ₁ ^ 3 = 1
    rw [← h3₁.orderOf]
    exact pow_orderOf_eq_one σ₁
  have hb3 : b ^ 3 = 1 := by
    apply Subtype.ext
    show σ₂ ^ 3 = 1
    rw [← h3₂.orderOf]
    exact pow_orderOf_eq_one σ₂
  have ha1 : a ≠ 1 := by
    intro h
    exact h3₁.ne_one (Subtype.ext_iff.mp h)
  have hb1 : b ≠ 1 := by
    intro h
    exact h3₂.ne_one (Subtype.ext_iff.mp h)
  have hout1 : ∀ y, ¬ (y = p₁ ∨ y = p₂ ∨ y = p₃) → σ₁ y = y := by
    intro y hy
    have hy1 : y ≠ p₁ := fun h => hy (Or.inl h)
    have hy2 : y ≠ p₂ := fun h => hy (Or.inr (Or.inl h))
    have hy3 : y ≠ p₃ := fun h => hy (Or.inr (Or.inr h))
    rw [hσ₁, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hy1 hy3,
      Equiv.swap_apply_of_ne_of_ne hy1 hy2]
  have hout2 : ∀ y, ¬ (y = q₁ ∨ y = q₂ ∨ y = q₃) → σ₂ y = y := by
    intro y hy
    have hy1 : y ≠ q₁ := fun h => hy (Or.inl h)
    have hy2 : y ≠ q₂ := fun h => hy (Or.inr (Or.inl h))
    have hy3 : y ≠ q₃ := fun h => hy (Or.inr (Or.inr h))
    rw [hσ₂, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hy1 hy3,
      Equiv.swap_apply_of_ne_of_ne hy1 hy2]
  have hq1_fix1 : σ₁ q₁ = q₁ := by
    apply hout1
    have hq1Q : q₁ ∈ ({q₁, q₂, q₃} : Finset (Fin n)) := by simp
    have hnotP : q₁ ∉ ({p₁, p₂, p₃} : Finset (Fin n)) :=
      Finset.disjoint_right.mp hPQ hq1Q
    simpa using hnotP
  have hq1_move2 : σ₂ q₁ = q₃ := by
    rw [hσ₂, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hq13.symm hq23.symm]
  have hdisj : Equiv.Perm.Disjoint σ₁ σ₂ := by
    intro y
    by_cases hy : y = p₁ ∨ y = p₂ ∨ y = p₃
    · right
      have hyP : y ∈ ({p₁, p₂, p₃} : Finset (Fin n)) := by simpa using hy
      have hnotQ : y ∉ ({q₁, q₂, q₃} : Finset (Fin n)) :=
        Finset.disjoint_left.mp hPQ hyP
      exact hout2 y (by simpa using hnotQ)
    · left
      exact hout1 y hy
  have hba : b ≠ a := by
    intro h
    have hval : σ₂ = σ₁ := congrArg Subtype.val h
    have hq : σ₂ q₁ = σ₁ q₁ := by rw [hval]
    rw [hq1_move2, hq1_fix1] at hq
    exact hq13 hq.symm
  have hq1_fix_pow2 : (σ₁ ^ 2) q₁ = q₁ := by
    rw [pow_two, Equiv.Perm.mul_apply, hq1_fix1, hq1_fix1]
  have hba2 : b ≠ a ^ 2 := by
    intro h
    have hval : σ₂ = σ₁ ^ 2 := by
      have h' := congrArg Subtype.val h
      rw [Subgroup.coe_pow] at h'
      exact h'
    have hq : σ₂ q₁ = (σ₁ ^ 2) q₁ := by rw [hval]
    rw [hq1_move2, hq1_fix_pow2] at hq
    exact hq13 hq.symm
  have hcomm : a * b = b * a := by
    apply Subtype.ext
    show σ₁ * σ₂ = σ₂ * σ₁
    exact (Equiv.Perm.Disjoint.commute hdisj).eq
  obtain ⟨hpg, hnc⟩ := s16c1g_closure_pair ha3 hb3 hcomm ha1 hb1 hba hba2
  refine ⟨Subgroup.closure ({a, b} : Set ↥(alternatingGroup (Fin n))), hpg, hnc, ?_⟩
  intro γ hγ
  have hfixγ : G6.permAct n (γ : Equiv.Perm (Fin n)) mv = mv :=
    s16t3_permAct_closure_fixes (x := mv) hfix1 hfix2 γ hγ
  have hact : (FFModel.altDn n).act γ (m : (FFModel.altDn n).Amb) =
      (m : (FFModel.altDn n).Amb) := hfixγ
  rw [hact, mul_inv_cancel]
  exact Subgroup.one_mem _

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
