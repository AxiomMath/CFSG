module

public import CFSG.Quasithin.SteinbergCBTwoNaturalCentralizer
public import Std.Tactic.BVDecide.Normalize.Prop

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SteinbergCB

open Module Subgroup

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem zmod_two_module_add_self (v : V) : v + v = 0 := by
  have h : (1 + 1 : ZMod 2) = 0 := by decide
  rw [← one_smul (ZMod 2) v, ← add_smul, h, zero_smul]

theorem exists_linearEquiv_apply_eq_pair [FiniteDimensional (ZMod 2) V] {v w v' w' : V}
    (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v ≠ w) (hv' : v' ≠ 0) (hw' : w' ≠ 0) (hvw' : v' ≠ w') :
    ∃ g : V ≃ₗ[ZMod 2] V, g v = v' ∧ g w = w' := by
  have hind : ∀ {x y : V}, x ≠ 0 → y ≠ 0 → x ≠ y → LinearIndependent (ZMod 2) ![x, y] := by
    intro x y hx hy hxy
    refine LinearIndependent.pair_iff.2 fun s t hst => ?_
    have hs : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    rcases hs s with rfl | rfl <;> rcases hs t with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · simp at hst
      exact absurd hst hy
    · simp at hst
      exact absurd hst hx
    · simp only [one_smul] at hst
      refine absurd ?_ hxy
      calc x = x + (y + y) := by rw [zmod_two_module_add_self, add_zero]
        _ = x + y + y := (add_assoc _ _ _).symm
        _ = y := by rw [hst, zero_add]
  have hD := hind hv hw hvw
  have hE := hind hv' hw' hvw'
  have : FiniteDimensional (ZMod 2) (Submodule.span (ZMod 2) (Set.range ![v, w])) :=
    FiniteDimensional.span_of_finite (ZMod 2) (Set.finite_range _)
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq
    (hD.linearCombinationEquiv.symm.trans hE.linearCombinationEquiv)
  have key : ∀ i : Fin 2, g (![v, w] i) = ![v', w'] i := by
    intro i
    have hmem : ![v, w] i ∈ Submodule.span (ZMod 2) (Set.range ![v, w]) :=
      Submodule.subset_span ⟨i, rfl⟩
    have h1 : hD.linearCombinationEquiv.symm ⟨![v, w] i, hmem⟩ = Finsupp.single i 1 := by
      rw [LinearEquiv.symm_apply_eq]
      apply Subtype.ext
      rw [LinearIndependent.linearCombinationEquiv_apply_coe, Finsupp.linearCombination_single,
        one_smul]
    have h2 := hg ⟨![v, w] i, hmem⟩
    rw [← h2]
    change ((hE.linearCombinationEquiv (hD.linearCombinationEquiv.symm ⟨![v, w] i, hmem⟩) :
      Submodule.span (ZMod 2) (Set.range ![v', w'])) : V) = _
    rw [h1, LinearIndependent.linearCombinationEquiv_apply_coe, Finsupp.linearCombination_single,
      one_smul]
  exact ⟨g, key 0, key 1⟩

open Classical in
noncomputable def pairClass (x : V × V) : Fin 5 :=
  if x.1 = 0 then (if x.2 = 0 then 0 else 2)
  else if x.2 = 0 then 1 else if x.1 = x.2 then 3 else 4

theorem pairClass_diag (g : V ≃ₗ[ZMod 2] V) (x : V × V) :
    pairClass (diagHom g x) = pairClass x := by
  classical
  simp only [pairClass, diagHom_apply, LinearEquiv.map_eq_zero_iff, g.injective.eq_iff]

omit [Module (ZMod 2) V] in
theorem pairClass_eq_zero {x : V × V} : pairClass x = 0 ↔ x.1 = 0 ∧ x.2 = 0 := by
  unfold pairClass
  split_ifs <;> simp_all

omit [Module (ZMod 2) V] in
theorem pairClass_eq_one {x : V × V} : pairClass x = 1 ↔ x.1 ≠ 0 ∧ x.2 = 0 := by
  unfold pairClass
  split_ifs <;> simp_all

omit [Module (ZMod 2) V] in
theorem pairClass_eq_two {x : V × V} : pairClass x = 2 ↔ x.1 = 0 ∧ x.2 ≠ 0 := by
  unfold pairClass
  split_ifs <;> simp_all

omit [Module (ZMod 2) V] in
theorem pairClass_eq_three {x : V × V} : pairClass x = 3 ↔ x.1 ≠ 0 ∧ x.2 ≠ 0 ∧ x.1 = x.2 := by
  unfold pairClass
  split_ifs <;> simp_all

omit [Module (ZMod 2) V] in
theorem pairClass_eq_four {x : V × V} : pairClass x = 4 ↔ x.1 ≠ 0 ∧ x.2 ≠ 0 ∧ x.1 ≠ x.2 := by
  unfold pairClass
  split_ifs <;> simp_all

theorem exists_diag_of_pairClass_eq [FiniteDimensional (ZMod 2) V] {x y : V × V}
    (h : pairClass x = pairClass y) : ∃ g : V ≃ₗ[ZMod 2] V, diagHom g x = y := by
  obtain ⟨i, hi⟩ : ∃ i, pairClass x = i := ⟨_, rfl⟩
  have hj : pairClass y = i := h ▸ hi
  fin_cases i
  · obtain ⟨h1, h2⟩ := pairClass_eq_zero.1 hi
    obtain ⟨h1', h2'⟩ := pairClass_eq_zero.1 hj
    exact ⟨1, Prod.ext (by simp [h1, h1']) (by simp [h2, h2'])⟩
  · obtain ⟨h1, h2⟩ := pairClass_eq_one.1 hi
    obtain ⟨h1', h2'⟩ := pairClass_eq_one.1 hj
    obtain ⟨g, hg⟩ := exists_linearEquiv_apply_eq h1 h1'
    exact ⟨g, Prod.ext (by simp [diagHom_apply, hg]) (by simp [diagHom_apply, h2, h2'])⟩
  · obtain ⟨h1, h2⟩ := pairClass_eq_two.1 hi
    obtain ⟨h1', h2'⟩ := pairClass_eq_two.1 hj
    obtain ⟨g, hg⟩ := exists_linearEquiv_apply_eq h2 h2'
    exact ⟨g, Prod.ext (by simp [diagHom_apply, h1, h1']) (by simp [diagHom_apply, hg])⟩
  · obtain ⟨h1, -, h3⟩ := pairClass_eq_three.1 hi
    obtain ⟨h1', -, h3'⟩ := pairClass_eq_three.1 hj
    obtain ⟨g, hg⟩ := exists_linearEquiv_apply_eq h1 h1'
    exact ⟨g, Prod.ext (by simp [diagHom_apply, hg]) (by simp [diagHom_apply, ← h3, ← h3', hg])⟩
  · obtain ⟨h1, h2, h3⟩ := pairClass_eq_four.1 hi
    obtain ⟨h1', h2', h3'⟩ := pairClass_eq_four.1 hj
    obtain ⟨g, hg1, hg2⟩ := exists_linearEquiv_apply_eq_pair h1 h2 h3 h1' h2' h3'
    exact ⟨g, Prod.ext (by simp [diagHom_apply, hg1]) (by simp [diagHom_apply, hg2])⟩

omit [Module (ZMod 2) V] in
theorem card_subtype_ne_zero [Fintype V] [DecidableEq V] :
    Fintype.card {v : V // v ≠ 0} = Fintype.card V - 1 := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]

omit [Module (ZMod 2) V] in
theorem card_pairClass_zero [Fintype V] [DecidableEq V] :
    Fintype.card {x : V × V // pairClass x = 0} = 1 := by
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨0, pairClass_eq_zero.2 ⟨rfl, rfl⟩⟩, fun y => Subtype.ext ?_⟩
  obtain ⟨h1, h2⟩ := pairClass_eq_zero.1 y.2
  exact Prod.ext h1 h2

omit [Module (ZMod 2) V] in
theorem card_pairClass_one [Fintype V] [DecidableEq V] :
    Fintype.card {x : V × V // pairClass x = 1} = Fintype.card V - 1 := by
  rw [← card_subtype_ne_zero]
  refine Fintype.card_congr
    { toFun := fun x => ⟨x.1.1, (pairClass_eq_one.1 x.2).1⟩
      invFun := fun v => ⟨(v.1, 0), pairClass_eq_one.2 ⟨v.2, rfl⟩⟩
      left_inv := fun x => Subtype.ext (Prod.ext rfl (pairClass_eq_one.1 x.2).2.symm)
      right_inv := fun v => rfl }

omit [Module (ZMod 2) V] in
theorem card_pairClass_two [Fintype V] [DecidableEq V] :
    Fintype.card {x : V × V // pairClass x = 2} = Fintype.card V - 1 := by
  rw [← card_subtype_ne_zero]
  refine Fintype.card_congr
    { toFun := fun x => ⟨x.1.2, (pairClass_eq_two.1 x.2).2⟩
      invFun := fun v => ⟨(0, v.1), pairClass_eq_two.2 ⟨rfl, v.2⟩⟩
      left_inv := fun x => Subtype.ext (Prod.ext (pairClass_eq_two.1 x.2).1.symm rfl)
      right_inv := fun v => rfl }

omit [Module (ZMod 2) V] in
theorem card_pairClass_three [Fintype V] [DecidableEq V] :
    Fintype.card {x : V × V // pairClass x = 3} = Fintype.card V - 1 := by
  rw [← card_subtype_ne_zero]
  refine Fintype.card_congr
    { toFun := fun x => ⟨x.1.1, (pairClass_eq_three.1 x.2).1⟩
      invFun := fun v => ⟨(v.1, v.1), pairClass_eq_three.2 ⟨v.2, v.2, rfl⟩⟩
      left_inv := fun x => Subtype.ext (Prod.ext rfl (pairClass_eq_three.1 x.2).2.2)
      right_inv := fun v => rfl }

omit [Module (ZMod 2) V] in
theorem card_pairClass_sum [Fintype V] [DecidableEq V] :
    ∑ i : Fin 5, Fintype.card {x : V × V // pairClass x = i} =
      Fintype.card V * Fintype.card V := by
  rw [← Fintype.card_prod, ← Finset.card_univ,
    Finset.card_eq_sum_card_fiberwise (f := pairClass) (t := Finset.univ)
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))]
  exact Finset.sum_congr rfl fun i _ => Fintype.card_subtype _

theorem card_pairClass_le_of_mem_normalizer [FiniteDimensional (ZMod 2) V] [Fintype V]
    [DecidableEq V] {h : (V × V) ≃ₗ[ZMod 2] (V × V)}
    (hh : h ∈ normalizer ((diagHom (V := V)).range : Set ((V × V) ≃ₗ[ZMod 2] (V × V))))
    (z : V × V) : Fintype.card {x : V × V // pairClass x = pairClass z} ≤
      Fintype.card {x : V × V // pairClass x = pairClass (h z)} := by
  refine Fintype.card_le_of_injective (fun y => ⟨h y.1, ?_⟩) fun a b hab => ?_
  · obtain ⟨g, hg⟩ := exists_diag_of_pairClass_eq y.2.symm
    obtain ⟨g', hg'⟩ : h * diagHom g * h⁻¹ ∈ (diagHom (V := V)).range :=
      (mem_normalizer_iff.1 hh _).1 ⟨g, rfl⟩
    have : h y.1 = diagHom g' (h z) := by
      rw [hg', ← hg]
      change h (diagHom g z) = h (diagHom g (h⁻¹ (h z)))
      rw [show h⁻¹ (h z) = z from h.symm_apply_apply z]
    rw [this, pairClass_diag]
  · exact Subtype.ext (h.injective (congrArg Subtype.val hab))

theorem nq_two_natural_three_space_normalizer_orbits [FiniteDimensional (ZMod 2) V]
    (hV : finrank (ZMod 2) V = 3) {H : Subgroup ((V × V) ≃ₗ[ZMod 2] (V × V))}
    (hSH : (diagHom (V := V)).range ≤ H)
    (hHN : H ≤ normalizer ((diagHom (V := V)).range : Set ((V × V) ≃ₗ[ZMod 2] (V × V))))
    (x : V × V) :
    Nat.card (MulAction.orbit H x) ∈ ({1, 7, 14, 21, 42} : Finset ℕ) ∧
      ¬ 4 ∣ Nat.card (MulAction.orbit H x) := by
  classical
  have : Finite V := Module.finite_of_finite (ZMod 2)
  let _ : Fintype V := Fintype.ofFinite V
  have hcardV : Fintype.card V = 8 := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, hV]
    norm_num
  set c : Fin 5 → ℕ := fun i => Fintype.card {y : V × V // pairClass y = i} with hc
  have hc0 : c 0 = 1 := card_pairClass_zero
  have hc1 : c 1 = 7 := by
    change Fintype.card {y : V × V // pairClass y = 1} = 7
    rw [card_pairClass_one, hcardV]
  have hc2 : c 2 = 7 := by
    change Fintype.card {y : V × V // pairClass y = 2} = 7
    rw [card_pairClass_two, hcardV]
  have hc3 : c 3 = 7 := by
    change Fintype.card {y : V × V // pairClass y = 3} = 7
    rw [card_pairClass_three, hcardV]
  have hc4 : c 4 = 42 := by
    have h := card_pairClass_sum (V := V)
    rw [Fin.sum_univ_five, hcardV] at h
    change c 0 + c 1 + c 2 + c 3 + c 4 = 8 * 8 at h
    omega
  set O : Finset (V × V) := Finset.univ.filter fun y => ∃ k ∈ H, k x = y with hO
  have hmemO : ∀ y, y ∈ O ↔ ∃ k ∈ H, k x = y := fun y => by simp [hO]
  have hcardO : Nat.card (MulAction.orbit H x) = O.card := by
    rw [← Fintype.card_coe O, ← Nat.card_eq_fintype_card]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
    rw [MulAction.mem_orbit_iff, hmemO]
    constructor
    · rintro ⟨⟨k, hk⟩, rfl⟩
      exact ⟨k, hk, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
  have hsize : ∀ y ∈ O, c (pairClass y) = c (pairClass x) := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := (hmemO y).1 hy
    refine le_antisymm ?_ (card_pairClass_le_of_mem_normalizer (hHN hk) x)
    have h := card_pairClass_le_of_mem_normalizer (inv_mem (hHN hk)) (k x)
    rwa [show k⁻¹ (k x) = x from k.symm_apply_apply x] at h
  set t : Fin 5 → ℕ := fun i => (O.filter fun y => pairClass y = i).card with ht
  have htfib : ∀ i, t i = 0 ∨ (t i = c i ∧ c i = c (pairClass x)) := by
    intro i
    by_cases hne : ∃ y ∈ O, pairClass y = i
    · right
      obtain ⟨y₀, hy₀, hy₀i⟩ := hne
      refine ⟨?_, hy₀i ▸ hsize y₀ hy₀⟩
      have hfilt : (O.filter fun y => pairClass y = i) =
          Finset.univ.filter fun y => pairClass y = i := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · exact fun h => h.2
        · intro hyi
          refine ⟨?_, hyi⟩
          obtain ⟨g, hg⟩ := exists_diag_of_pairClass_eq (hy₀i.trans hyi.symm)
          obtain ⟨k, hk, hkx⟩ := (hmemO y₀).1 hy₀
          exact (hmemO y).2 ⟨diagHom g * k, H.mul_mem (hSH ⟨g, rfl⟩) hk, by
            rw [LinearEquiv.mul_apply, hkx, hg]⟩
      change (O.filter fun y => pairClass y = i).card = Fintype.card {y // pairClass y = i}
      rw [hfilt, Fintype.card_subtype]
    · left
      rw [ht]
      simp only
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro y hy hyi
      exact hne ⟨y, hy, hyi⟩
  have htx : t (pairClass x) = c (pairClass x) := by
    rcases htfib (pairClass x) with h | h
    · exfalso
      rw [ht] at h
      simp only at h
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
      exact h ((hmemO x).2 ⟨1, H.one_mem, rfl⟩) rfl
    · exact h.1
  have hsum : O.card = t 0 + t 1 + t 2 + t 3 + t 4 := by
    rw [← Fin.sum_univ_five, Finset.card_eq_sum_card_fiberwise (f := pairClass)
      (t := Finset.univ) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))]
  rw [hcardO, hsum]
  have h0 := htfib 0
  have h1 := htfib 1
  have h2 := htfib 2
  have h3 := htfib 3
  have h4 := htfib 4
  rw [hc0] at h0
  rw [hc1] at h1
  rw [hc2] at h2
  rw [hc3] at h3
  rw [hc4] at h4
  have hcases : pairClass x = 0 ∨ pairClass x = 1 ∨ pairClass x = 2 ∨ pairClass x = 3 ∨
      pairClass x = 4 := by
    generalize pairClass x = i
    fin_cases i <;> simp
  rcases hcases with hx | hx | hx | hx | hx <;> rw [hx] at h0 h1 h2 h3 h4 htx <;>
    simp only [hc0, hc1, hc2, hc3, hc4] at h0 h1 h2 h3 h4 htx ⊢ <;>
    simp only [Finset.mem_insert, Finset.mem_singleton] <;> omega

end CFSG.Quasithin.SteinbergCB
