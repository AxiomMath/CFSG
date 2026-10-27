module

public import CFSG.Milestones.ASVolI.I1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.ASVolI.ChIJK Equiv

@[expose] def evenPair (n : ℕ) (a b : Fin n) : evenWeight n :=
  ⟨Pi.single a 1 + Pi.single b 1, by
    show ∑ i, ((Pi.single a 1 : Fin n → ZMod 2) i + (Pi.single b 1 : Fin n → ZMod 2) i) = 0
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_pi_single', Finset.mem_univ, if_true]
    decide⟩

private lemma coe_evenWeightRep_apply (n : ℕ) (σ : Perm (Fin n)) (x : evenWeight n) (i : Fin n) :
    ((evenWeightRep n σ x : evenWeight n) : Fin n → ZMod 2) i =
      (x : Fin n → ZMod 2) (σ⁻¹ i) := by
  simp [evenWeightRep, permRepF2, Representation.subrepresentation, LinearMap.funLeft,
    Equiv.Perm.inv_def]

private lemma evenPair_self (n : ℕ) (a : Fin n) : evenPair n a a = 0 := by
  apply Subtype.ext
  funext k
  show (Pi.single a 1 + Pi.single a 1 : Fin n → ZMod 2) k = 0
  simp only [Pi.add_apply, Pi.single_apply]
  by_cases hk : k = a
  · rw [if_pos hk]
    decide
  · rw [if_neg hk]
    simp

private lemma zmod2_sub_eq_add (a b : ZMod 2) : a - b = a + b := by
  revert a b
  decide

private lemma zmod2_add_eq_one_of_ne {a b : ZMod 2} (h : a ≠ b) : a + b = 1 := by
  revert a b
  decide

private lemma exists_ne_of_notMem_constInEven {n : ℕ} (hn : 1 ≤ n) {x : evenWeight n}
    (hx : x ∉ constInEven n) :
    ∃ i j : Fin n, (x : Fin n → ZMod 2) i ≠ (x : Fin n → ZMod 2) j := by
  by_contra hc
  push Not at hc
  let i0 : Fin n := ⟨0, by omega⟩
  have hxspan : (x : Fin n → ZMod 2) ∈
      Submodule.span (ZMod 2) {fun _ : Fin n => (1 : ZMod 2)} := by
    rw [Submodule.mem_span_singleton]
    refine ⟨(x : Fin n → ZMod 2) i0, ?_⟩
    funext i
    simp only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    exact (hc i i0).symm
  exact hx (by simpa [constInEven] using hxspan)

theorem evenWeightRep_evenPair {n : ℕ} (σ : Perm (Fin n)) (a b : Fin n) :
    evenWeightRep n σ (evenPair n a b) = evenPair n (σ a) (σ b) := by
  apply Subtype.ext
  funext i
  rw [coe_evenWeightRep_apply]
  simp only [evenPair, Submodule.coe_mk, Pi.add_apply, Pi.single_apply,
    Equiv.Perm.inv_eq_iff_eq]

theorem evenWeightRep_swap_sub_self {n : ℕ} (i j : Fin n) (x : evenWeight n) :
    evenWeightRep n (swap i j) x - x =
      ((x : Fin n → ZMod 2) i + (x : Fin n → ZMod 2) j) • evenPair n i j := by
  apply Subtype.ext
  funext k
  have hL : ((evenWeightRep n (swap i j) x - x : evenWeight n) : Fin n → ZMod 2) k =
      (x : Fin n → ZMod 2) (swap i j k) - (x : Fin n → ZMod 2) k := by
    rw [Submodule.coe_sub, Pi.sub_apply, coe_evenWeightRep_apply, Equiv.swap_inv]
  have hR : ((((x : Fin n → ZMod 2) i + (x : Fin n → ZMod 2) j) • evenPair n i j :
      evenWeight n) : Fin n → ZMod 2) k =
      ((x : Fin n → ZMod 2) i + (x : Fin n → ZMod 2) j) *
        ((Pi.single i 1 + Pi.single j 1 : Fin n → ZMod 2) k) := by
    rw [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    rfl
  rw [hL, hR]
  by_cases hij : i = j
  · subst hij
    simp only [Equiv.swap_self, Equiv.refl_apply, Pi.add_apply, Pi.single_apply]
    rw [zmod2_sub_eq_add, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, zero_mul]
  · by_cases hki : k = i
    · subst hki
      rw [Equiv.swap_apply_left, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij]
      rw [add_zero, mul_one, zmod2_sub_eq_add]
      ac_rfl
    · by_cases hkj : k = j
      · subst hkj
        rw [Equiv.swap_apply_right, Pi.add_apply, Pi.single_eq_of_ne (Ne.symm hij),
          Pi.single_eq_same]
        rw [zero_add, mul_one, zmod2_sub_eq_add]
      · rw [Equiv.swap_apply_of_ne_of_ne hki hkj, Pi.add_apply, Pi.single_eq_of_ne hki,
          Pi.single_eq_of_ne hkj]
        rw [add_zero, mul_zero, zmod2_sub_eq_add, CharTwo.add_self_eq_zero]

theorem span_evenPair_eq_top {n : ℕ} (hn : 1 ≤ n) :
    Submodule.span (ZMod 2) (Set.range fun p : Fin n × Fin n => evenPair n p.1 p.2) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  let z : Fin n := ⟨0, by omega⟩
  have hx : x = ∑ i : Fin n, (x : Fin n → ZMod 2) i • evenPair n i z := by
    apply Subtype.ext
    funext k
    rw [Submodule.coe_sum, Finset.sum_apply]
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, evenPair, Submodule.coe_mk,
      Pi.add_apply, Pi.single_apply, mul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, x.2, zero_mul, add_zero]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]
    simp
  rw [hx]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨(i, z), rfl⟩

theorem exists_perm_apply_two {n : ℕ} {a b i j : Fin n} (hab : a ≠ b) (hij : i ≠ j) :
    ∃ σ : Perm (Fin n), σ a = i ∧ σ b = j := by
  have hne : swap a i b ≠ i := by
    rintro h
    by_cases hbi : b = i
    · subst hbi
      rw [Equiv.swap_apply_right] at h
      exact hab h
    · have hba : b ≠ a := fun h' => hab h'.symm
      rw [Equiv.swap_apply_of_ne_of_ne hba hbi] at h
      exact hbi h
  refine ⟨swap (swap a i b) j * swap a i, ?_, ?_⟩
  · simp only [Perm.mul_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hne) hij
  · simp only [Perm.mul_apply]
    exact Equiv.swap_apply_left _ _

theorem exists_perm_apply_three {n : ℕ} {a b d i j k : Fin n} (hab : a ≠ b) (had : a ≠ d)
    (hbd : b ≠ d) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ σ : Perm (Fin n), σ a = i ∧ σ b = j ∧ σ d = k := by
  obtain ⟨σ', hσ'a, hσ'b⟩ := exists_perm_apply_two hab hij
  have hd'i : σ' d ≠ i := fun h => had (σ'.injective (by rw [hσ'a, h]))
  have hd'j : σ' d ≠ j := fun h => hbd (σ'.injective (by rw [hσ'b, h]))
  refine ⟨swap (σ' d) k * σ', ?_, ?_, ?_⟩
  · simp only [Perm.mul_apply, hσ'a]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hd'i) hik
  · simp only [Perm.mul_apply, hσ'b]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hd'j) hjk
  · simp only [Perm.mul_apply]
    exact Equiv.swap_apply_left _ _

theorem eq_top_of_not_le_constInEven {n : ℕ} (hn : 3 ≤ n) (N : Submodule (ZMod 2) (evenWeight n))
    (hN : ∀ (σ : Perm (Fin n)) (x : evenWeight n), x ∈ N → evenWeightRep n σ x ∈ N)
    (hnc : ¬ N ≤ constInEven n) : N = ⊤ := by
  have hnc' : ∃ x : evenWeight n, x ∈ N ∧ x ∉ constInEven n := by
    by_contra h
    push Not at h
    exact hnc fun y hy => h y hy
  obtain ⟨x, hxN, hxc⟩ := hnc'
  obtain ⟨i, j, hij⟩ := exists_ne_of_notMem_constInEven (by omega) hxc
  have hij_ne : i ≠ j := fun h => hij (by rw [h])
  have hsum : (x : Fin n → ZMod 2) i + (x : Fin n → ZMod 2) j = 1 :=
    zmod2_add_eq_one_of_ne hij
  have heven : evenPair n i j ∈ N := by
    have h1 : evenWeightRep n (swap i j) x - x ∈ N := N.sub_mem (hN (swap i j) x hxN) hxN
    rw [evenWeightRep_swap_sub_self, hsum, one_smul] at h1
    exact h1
  have hall : ∀ k l : Fin n, evenPair n k l ∈ N := by
    intro k l
    by_cases hkl : k = l
    · subst hkl
      rw [evenPair_self]
      exact N.zero_mem
    · obtain ⟨σ, hσk, hσl⟩ := exists_perm_apply_two hij_ne hkl
      have hσ : evenWeightRep n σ (evenPair n i j) ∈ N := hN σ _ heven
      rw [evenWeightRep_evenPair, hσk, hσl] at hσ
      exact hσ
  have hn1 : 1 ≤ n := by omega
  refine eq_top_iff.mpr ?_
  rw [← span_evenPair_eq_top hn1]
  apply Submodule.span_le.mpr
  rintro y ⟨⟨k, l⟩, rfl⟩
  exact hall k l

theorem mem_closure_isSwap_fixing_two {n : ℕ} {a b : Fin n} {σ : Perm (Fin n)} (ha : σ a = a)
    (hb : σ b = b) :
    σ ∈ Subgroup.closure {τ : Perm (Fin n) | τ.IsSwap ∧ τ a = a ∧ τ b = b} := by
  classical
  let p : Fin n → Prop := fun x => x ≠ a ∧ x ≠ b
  have hp : ∀ x, p (σ x) ↔ p x := by
    intro x
    show (σ x ≠ a ∧ σ x ≠ b) ↔ (x ≠ a ∧ x ≠ b)
    refine and_congr ?_ ?_
    · constructor
      · intro h hx; exact h (by rw [hx, ha])
      · intro h hx; exact h (σ.injective (by rw [hx, ha]))
    · constructor
      · intro h hx; exact h (by rw [hx, hb])
      · intro h hx; exact h (σ.injective (by rw [hx, hb]))
  have hmem : ∀ π : Perm (Subtype p), Equiv.Perm.ofSubtype π ∈
      Subgroup.closure {τ : Perm (Fin n) | τ.IsSwap ∧ τ a = a ∧ τ b = b} := by
    intro π
    refine Equiv.Perm.swap_induction_on π ?_ ?_
    · rw [map_one]
      exact Subgroup.one_mem _
    · intro f x y hxy ih
      rw [map_mul, Equiv.Perm.ofSubtype_swap_eq]
      refine Subgroup.mul_mem _ (Subgroup.subset_closure ?_) ih
      refine ⟨⟨↑x, ↑y, fun h => hxy (Subtype.ext h), rfl⟩, ?_, ?_⟩
      · exact Equiv.swap_apply_of_ne_of_ne (Ne.symm x.2.1) (Ne.symm y.2.1)
      · exact Equiv.swap_apply_of_ne_of_ne (Ne.symm x.2.2) (Ne.symm y.2.2)
  have hσ' : σ = Equiv.Perm.ofSubtype (σ.subtypePerm hp) := by
    rw [Equiv.Perm.ofSubtype_subtypePerm hp]
    intro x hx
    exact ⟨fun h => hx (by rw [h, ha]), fun h => hx (by rw [h, hb])⟩
  rw [hσ']
  exact hmem _

end CFSG.LocalAnalysis.WeakClosure81
