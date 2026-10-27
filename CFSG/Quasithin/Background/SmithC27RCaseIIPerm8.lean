module

public import CFSG.Quasithin.Background.SmithC27RCaseIIKlein
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_26ClaimPerm

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.QuasithinUnique Equiv Equiv.Perm MulAction

section Generic

variable {α : Type} [Fintype α] [DecidableEq α]

omit [Fintype α] in
theorem IsRadSig.swap_mem_of_invariant {P : Subgroup (Perm α)} (hrad : IsRadSig P) {e f : α}
    (hef : e ≠ f) (hN : ∀ m ∈ Subgroup.normalizer (P : Set (Perm α)), ∀ x,
      m x ∈ ({e, f} : Set α) ↔ x ∈ ({e, f} : Set α)) :
    swap e f ∈ P := by
  refine hrad.swap_mem fun m hm => ?_
  have he : m e = e ∨ m e = f := (hN m hm e).2 (Or.inl rfl)
  have hf : m f = e ∨ m f = f := (hN m hm f).2 (Or.inr rfl)
  have hne : m e ≠ m f := fun h => hef (m.injective h)
  rcases he with h1 | h1 <;> rcases hf with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hne

omit [Fintype α] in
theorem eq_one_or_eq_swap {g : Perm α} {e f : α} (hef : e ≠ f)
    (hg : ∀ x, x ≠ e → x ≠ f → g x = x) : g = 1 ∨ g = swap e f := by
  have hmem : ∀ y, y = e ∨ y = f → g y = e ∨ g y = f := by
    intro y hy
    by_contra h
    push Not at h
    have h2 : g y = y := g.injective (hg (g y) h.1 h.2)
    rcases hy with rfl | rfl
    · exact h.1 h2
    · exact h.2 h2
  rcases hmem e (Or.inl rfl) with h1 | h1
  · left
    have h2 : g f = f := by
      rcases hmem f (Or.inr rfl) with h2 | h2
      · exact absurd (g.injective (h2.trans h1.symm)) hef.symm
      · exact h2
    refine Equiv.ext fun x => ?_
    rw [Perm.one_apply]
    by_cases hxe : x = e
    · rw [hxe, h1]
    by_cases hxf : x = f
    · rw [hxf, h2]
    exact hg x hxe hxf
  · right
    have h2 : g f = e := by
      rcases hmem f (Or.inr rfl) with h2 | h2
      · exact h2
      · exact absurd (g.injective (h2.trans h1.symm)) hef.symm
    refine Equiv.ext fun x => ?_
    by_cases hxe : x = e
    · rw [hxe, h1, swap_apply_left]
    by_cases hxf : x = f
    · rw [hxf, h2, swap_apply_right]
    rw [hg x hxe hxf, swap_apply_of_ne_of_ne hxe hxf]

omit [Fintype α] in
theorem mem_orbit_of_kleinOf_le {P : Subgroup (Perm α)} {a b c d : α} (hab : a ≠ b)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hle : kleinOf ({a, b, c, d} : Set α) ≤ P) :
    b ∈ orbit ↥P a ∧ c ∈ orbit ↥P a ∧ d ∈ orbit ↥P a := by
  have hset2 : ({a, c, b, d} : Set α) = {a, b, c, d} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hset3 : ({a, d, b, c} : Set α) = {a, b, c, d} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have h1 := swap_mul_swap_mem_kleinGens hab hac had hbc hbd hcd
  have h2 := swap_mul_swap_mem_kleinGens hac hab had hbc.symm hcd hbd
  have h3 := swap_mul_swap_mem_kleinGens had hab hac hbd.symm hcd.symm hbc
  rw [hset2] at h2
  rw [hset3] at h3
  exact ⟨mem_orbit_subgroup_iff.2 ⟨_, hle (Subgroup.subset_closure h1),
      (swap_mul_swap_apply hac had hbc hbd).1⟩,
    mem_orbit_subgroup_iff.2 ⟨_, hle (Subgroup.subset_closure h2),
      (swap_mul_swap_apply hab had hbc.symm hcd).1⟩,
    mem_orbit_subgroup_iff.2 ⟨_, hle (Subgroup.subset_closure h3),
      (swap_mul_swap_apply hab hac hbd.symm hcd.symm).1⟩⟩

omit [Fintype α] [DecidableEq α] in
theorem mem_normalizer_of_map_conj_eq {H : Subgroup (Perm α)} {m : Perm α}
    (h : H.map (MulAut.conj m).toMonoidHom = H) :
    m ∈ Subgroup.normalizer (H : Set (Perm α)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    rw [← h]
    exact ⟨g, hg, rfl⟩
  · intro hg
    rw [← h] at hg
    obtain ⟨g', hg', hgg'⟩ := hg
    have : g' = g := by
      have h2 : m * g' * m⁻¹ = m * g * m⁻¹ := hgg'
      exact mul_left_cancel (mul_right_cancel h2)
    rw [← this]
    exact hg'

omit [Fintype α] [DecidableEq α] in
theorem map_conj_kleinOf_sup (A B : Set α) (m : Perm α) :
    (kleinOf A ⊔ kleinOf B).map (MulAut.conj m).toMonoidHom =
      kleinOf ((m : α → α) '' A) ⊔ kleinOf ((m : α → α) '' B) := by
  rw [Subgroup.map_sup, map_conj_kleinOf, map_conj_kleinOf]

omit [Fintype α] [DecidableEq α] in
theorem apply_mem_orbit_of_mem {P : Subgroup (Perm α)} {g : Perm α} (hg : g ∈ P) (x y : α) :
    g y ∈ orbit ↥P x ↔ y ∈ orbit ↥P x := by
  rw [mem_orbit_subgroup_iff, mem_orbit_subgroup_iff]
  constructor
  · rintro ⟨g', hg', hg'y⟩
    exact ⟨g⁻¹ * g', P.mul_mem (P.inv_mem hg) hg', by rw [Perm.mul_apply, hg'y]; simp⟩
  · rintro ⟨g', hg', rfl⟩
    exact ⟨g * g', P.mul_mem hg hg', rfl⟩

omit [Fintype α] [DecidableEq α] in
theorem exists_eq_quad_of_ncard_eq_four [Finite α] {Γ : Set α} (h : Γ.ncard = 4) :
    ∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧ Γ = {a, b, c, d} := by
  obtain ⟨a, t, hat, rfl, ht⟩ := (Set.ncard_eq_succ (Set.toFinite _)).1 h
  obtain ⟨b, c, d, hbc, hbd, hcd, rfl⟩ := Set.ncard_eq_three.1 ht
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hat
  exact ⟨a, b, c, d, hat.1, hat.2.1, hat.2.2, hbc, hbd, hcd, rfl⟩

omit [Fintype α] [DecidableEq α] in
theorem eq_one_of_mem_center_of_apply_eq {P : Subgroup (Perm α)}
    (htr : ∀ x y : α, ∃ g ∈ P, g x = y) {c : Perm α} (hc : ∀ g ∈ P, g * c = c * g) {x : α}
    (hx : c x = x) : c = 1 := by
  refine Equiv.ext fun y => ?_
  obtain ⟨g, hg, rfl⟩ := htr x y
  have h1 := congrArg (fun p : Perm α => p x) (hc g hg)
  simp only [Perm.mul_apply, hx] at h1
  rw [Perm.one_apply, ← h1]

end Generic

theorem card_perm_fin_eight : Nat.card (Perm (Fin 8)) = 40320 := by
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem exists_sylow_le_normalizer_of_sixtyFour_le {P : Subgroup (Perm (Fin 8))}
    (hP : IsPGroup 2 P) (h : 64 ≤ Nat.card P) :
    ∃ T : Subgroup (Perm (Fin 8)), IsSylowTwoOf T ⊤ ∧
      T ≤ Subgroup.normalizer (P : Set (Perm (Fin 8))) :=
  exists_sylow_le_normalizer_of_card hP (k := 7) (by rw [card_perm_fin_eight]; norm_num)
    (by rw [card_perm_fin_eight]; norm_num) (by omega)

theorem V8_eq_kleinOf_sup :
    Claim2526.V8 = kleinOf {x : Fin 8 | (x : ℕ) < 4} ⊔ kleinOf {x : Fin 8 | (x : ℕ) < 4}ᶜ := by
  have hL : {x : Fin 8 | (x : ℕ) < 4} = {0, 1, 2, 3} := by
    ext x
    fin_cases x <;> simp
  have hU : {x : Fin 8 | (x : ℕ) < 4}ᶜ = {4, 5, 6, 7} := by
    ext x
    fin_cases x <;> simp
  have hL2 : ({0, 2, 1, 3} : Set (Fin 8)) = {0, 1, 2, 3} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hU2 : ({4, 6, 5, 7} : Set (Fin 8)) = {4, 5, 6, 7} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have m1 : Claim2526.v8g1 ∈ Claim2526.V8 :=
    Subgroup.subset_closure (show Claim2526.v8g1 ∈ Claim2526.v8Gens by decide)
  have m2 : Claim2526.v8g2 ∈ Claim2526.V8 :=
    Subgroup.subset_closure (show Claim2526.v8g2 ∈ Claim2526.v8Gens by decide)
  have m3 : Claim2526.v8g3 ∈ Claim2526.V8 :=
    Subgroup.subset_closure (show Claim2526.v8g3 ∈ Claim2526.v8Gens by decide)
  have m4 : Claim2526.v8g4 ∈ Claim2526.V8 :=
    Subgroup.subset_closure (show Claim2526.v8g4 ∈ Claim2526.v8Gens by decide)
  rw [hU, hL]
  apply le_antisymm
  · rw [Claim2526.V8, Subgroup.closure_le]
    intro g hg
    have hg' : g ∈ Claim2526.v8Gens := hg
    simp only [Claim2526.v8Gens, List.mem_cons, List.mem_nil_iff, or_false] at hg'
    rcases hg' with rfl | rfl | rfl | rfl
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (swap_mul_swap_mem_kleinGens
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)))
    · have h := swap_mul_swap_mem_kleinGens (a := (0 : Fin 8)) (b := 2) (c := 1) (d := 3)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      rw [hL2] at h
      exact Subgroup.mem_sup_left (Subgroup.subset_closure h)
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (swap_mul_swap_mem_kleinGens
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)))
    · have h := swap_mul_swap_mem_kleinGens (a := (4 : Fin 8)) (b := 6) (c := 5) (d := 7)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      rw [hU2] at h
      exact Subgroup.mem_sup_right (Subgroup.subset_closure h)
  · refine sup_le ((Subgroup.closure_le _).2 fun g hg => ?_)
      ((Subgroup.closure_le _).2 fun g hg => ?_)
    · rcases mem_kleinGens_quad (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) hg with rfl | rfl | rfl
      · exact m1
      · exact m2
      · rw [show swap (0 : Fin 8) 3 * swap 1 2 = Claim2526.v8g1 * Claim2526.v8g2 by decide]
        exact Claim2526.V8.mul_mem m1 m2
    · rcases mem_kleinGens_quad (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) hg with rfl | rfl | rfl
      · exact m3
      · exact m4
      · rw [show swap (4 : Fin 8) 7 * swap 5 6 = Claim2526.v8g3 * Claim2526.v8g4 by decide]
        exact Claim2526.V8.mul_mem m3 m4

theorem fix_cases_eight {P : Subgroup (Perm (Fin 8))} (hP : IsPGroup 2 P) (hrad : IsRadSig P)
    (hodd : ¬ P ≤ alternatingGroup (Fin 8)) :
    (∀ x : Fin 8, ∃ g ∈ P, g x ≠ x) ∨ ∃ a b : Fin 8, a ≠ b ∧ P = Subgroup.zpowers (swap a b) := by
  classical
  obtain ⟨F, hF⟩ : ∃ F : Set (Fin 8), fixedPoints ↥P (Fin 8) = F := ⟨_, rfl⟩
  have hmemF : ∀ x, x ∈ F ↔ ∀ g ∈ P, g x = x := fun x => by
    rw [← hF, mem_fixedPoints_subgroup_iff]
  have hFN : ∀ m ∈ Subgroup.normalizer (P : Set (Perm (Fin 8))), ∀ x, m x ∈ F ↔ x ∈ F :=
    fun m hm x => by rw [← hF]; exact apply_mem_fixedPoints_iff hm
  have hmod := hP.card_modEq_card_fixedPoints (Fin 8)
  rw [hF, Nat.card_eq_fintype_card, Fintype.card_fin, Nat.card_coe_set_eq] at hmod
  have hle : F.ncard ≤ 8 := (Set.ncard_le_card _).trans (by simp)
  have heven : F.ncard % 2 = 0 := by
    unfold Nat.ModEq at hmod
    omega
  have hcF : Fᶜ.ncard = 8 - F.ncard := by
    rw [Set.ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  rcases (by omega : F.ncard = 0 ∨ F.ncard = 2 ∨ F.ncard = 4 ∨ F.ncard = 6 ∨ F.ncard = 8)
    with h | h | h | h | h
  ·
    left
    intro x
    have hx : x ∉ F := by
      rw [(Set.ncard_eq_zero (Set.toFinite _)).1 h]
      exact Set.notMem_empty x
    rw [hmemF] at hx
    push Not at hx
    exact hx
  ·
    exfalso
    obtain ⟨e, f, hef, hEF⟩ := Set.ncard_eq_two.1 h
    have hsw : swap e f ∈ P := hrad.swap_mem_of_invariant hef fun m hm x => by
      rw [← hEF]
      exact hFN m hm x
    have he : e ∈ F := by
      rw [hEF]
      exact Or.inl rfl
    have h1 := (hmemF e).1 he _ hsw
    rw [swap_apply_left] at h1
    exact hef h1.symm
  ·
    exfalso
    obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, habcd⟩ := exists_eq_quad_of_ncard_eq_four h
    have hK : kleinOf F ≤ P := by
      refine hrad.kleinOf_le ?_ hFN
      rw [habcd]
      exact isPGroup_kleinOf_quad hab hac had hbc hbd hcd
    rw [habcd] at hK
    have ha : a ∈ F := by
      rw [habcd]
      exact Or.inl rfl
    have h1 := (hmemF a).1 ha _ (hK (Subgroup.subset_closure
      (swap_mul_swap_mem_kleinGens hab hac had hbc hbd hcd)))
    rw [(swap_mul_swap_apply hac had hbc hbd).1] at h1
    exact hab h1.symm
  ·
    right
    obtain ⟨e, f, hef, hEF⟩ := Set.ncard_eq_two.1 (by rw [hcF, h] : Fᶜ.ncard = 2)
    have hsw : swap e f ∈ P := hrad.swap_mem_of_invariant hef fun m hm x => by
      rw [← hEF]
      exact not_congr (hFN m hm x)
    refine ⟨e, f, hef, le_antisymm (fun g hg => ?_) (Subgroup.zpowers_le.2 hsw)⟩
    have hfix : ∀ x, x ≠ e → x ≠ f → g x = x := by
      intro x hxe hxf
      have hx : x ∈ F := by
        by_contra hx
        have hx' : x ∈ Fᶜ := hx
        rw [hEF] at hx'
        rcases hx' with h1 | h1
        · exact hxe h1
        · exact hxf h1
      exact (hmemF x).1 hx g hg
    rcases eq_one_or_eq_swap hef hfix with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  ·
    exfalso
    apply hodd
    have hc : Fᶜ = ∅ := (Set.ncard_eq_zero (Set.toFinite _)).1 (by rw [hcF, h])
    intro g hg
    have hg1 : g = 1 := Equiv.ext fun x => by
      have hx : x ∈ F := by
        by_contra hx
        have hx' : x ∈ Fᶜ := hx
        rw [hc] at hx'
        exact hx'
      exact (hmemF x).1 hx g hg
    rw [hg1]
    exact Subgroup.one_mem _

theorem card_orbit_cases_eight {P : Subgroup (Perm (Fin 8))} (hP : IsPGroup 2 P)
    (hfree : ∀ x : Fin 8, ∃ g ∈ P, g x ≠ x) (x : Fin 8) :
    Nat.card (orbit ↥P x) = 2 ∨ Nat.card (orbit ↥P x) = 4 ∨ Nat.card (orbit ↥P x) = 8 := by
  obtain ⟨k, hk⟩ := hP.card_orbit x
  have h8 : Nat.card (orbit ↥P x) ≤ 8 := by
    rw [Nat.card_coe_set_eq]
    exact (Set.ncard_le_card _).trans (by simp)
  have h1 : Nat.card (orbit ↥P x) ≠ 1 := by
    intro h1
    obtain ⟨g, hg, hgx⟩ := hfree x
    rw [Nat.card_coe_set_eq] at h1
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 h1
    have hx : x ∈ orbit ↥P x := mem_orbit_self (M := ↥P) x
    have hgx' : g x ∈ orbit ↥P x := mem_orbit_subgroup_iff.2 ⟨g, hg, rfl⟩
    rw [ha, Set.mem_singleton_iff] at hx hgx'
    exact hgx (hgx'.trans hx.symm)
  rw [hk] at h8 h1 ⊢
  have hk3 : k ≤ 3 := by
    by_contra hk3
    have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases k <;> simp_all

theorem forall_exists_apply_eq_of_card_orbit {P : Subgroup (Perm (Fin 8))} {x : Fin 8}
    (hx : Nat.card (orbit ↥P x) = 8) : ∀ y z : Fin 8, ∃ g ∈ P, g y = z := by
  have huniv : orbit ↥P x = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
    rw [Set.ncard_univ, ← Nat.card_coe_set_eq, hx]
    simp
  have hmem : ∀ y, ∃ g ∈ P, g x = y := fun y =>
    mem_orbit_subgroup_iff.1 (huniv ▸ Set.mem_univ y)
  intro y z
  obtain ⟨g, hg, rfl⟩ := hmem y
  obtain ⟨g', hg', rfl⟩ := hmem z
  exact ⟨g' * g⁻¹, P.mul_mem hg' (P.inv_mem hg), by simp [Perm.mul_apply]⟩

theorem pairs_eight {P : Subgroup (Perm (Fin 8))} (hrad : IsRadSig P)
    (h2 : ∀ x : Fin 8, Nat.card (orbit ↥P x) = 2) :
    ∃ T : Subgroup (Perm (Fin 8)), IsSylowTwoOf T ⊤ ∧
      T ≤ Subgroup.normalizer (P : Set (Perm (Fin 8))) := by
  classical
  obtain ⟨z, hz, hfz, hPz, hNz⟩ := exists_pairing h2
  have hPeq : P = swapGroupOf z hz := le_antisymm (fun g hg => hPz g hg)
    (hrad _ (isPGroup_swapGroupOf hz) (by rw [normalizer_swapGroupOf]; exact hNz))
  rw [hPeq, normalizer_swapGroupOf]
  apply exists_sylow_le_of_not_two_dvd_index
  have key : Nat.card (Subgroup.centralizer {z}) * (Subgroup.centralizer {z}).index = 40320 := by
    rw [Subgroup.card_mul_index, card_perm_fin_eight]
  have hs : z.support.card = 8 := by
    rw [Finset.eq_univ_of_forall fun x => Perm.mem_support.2 (hfz x), Finset.card_univ,
      Fintype.card_fin]
  rw [card_centralizer_of_mul_self hz, Fintype.card_fin, hs] at key
  generalize (Subgroup.centralizer {z}).index = i at key ⊢
  norm_num [Nat.factorial] at key
  omega

end CFSG.Quasithin.SmithC27
