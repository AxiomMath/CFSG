module

public import CFSG.Quasithin.Background.SmithC27Perm
public import CFSG.Quasithin.Background.B4Statement

public section

set_option maxRecDepth 100000

namespace CFSG.Quasithin.SmithC27

open Equiv Equiv.Perm
open scoped Pointwise

section SwapGroup

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
private theorem inv_app' (f : Perm α) (x : α) : f⁻¹ (f x) = x := f.symm_apply_apply x

omit [DecidableEq α] in
private theorem app_inv' (f : Perm α) (x : α) : f (f⁻¹ x) = x := f.apply_symm_apply x

theorem normalizer_eq_centralizer_of_mem_iff {z : Perm α} (hz : ∀ x, z (z x) = x)
    {J : Subgroup (Perm α)} (hJ : ∀ g, g ∈ J ↔ ∀ x, g x = x ∨ g x = z x) :
    Subgroup.normalizer (J : Set (Perm α)) = Subgroup.centralizer {z} := by
  ext h
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hh
    have key : ∀ h ∈ Subgroup.normalizer (J : Set (Perm α)), ∀ x, z x ≠ x →
        h (z x) = z (h x) := by
      intro h hh x hx
      have hs : swap x (z x) ∈ J := by
        rw [hJ]
        intro y
        by_cases hy : y = x
        · subst hy
          right
          rw [swap_apply_left]
        · by_cases hy' : y = z x
          · subst hy'
            right
            rw [swap_apply_right, hz]
          · left
            exact swap_apply_of_ne_of_ne hy hy'
      have hc := (Subgroup.mem_normalizer_iff.mp hh _).mp hs
      rw [← swap_apply_apply, hJ] at hc
      have hne : h x ≠ h (z x) := fun e => hx (h.injective e).symm
      rcases hc (h x) with e | e <;> rw [swap_apply_left] at e
      · exact absurd e.symm hne
      · exact e
    have hall : ∀ y, h (z y) = z (h y) := by
      intro y
      by_cases hy : z y = y
      · rw [hy]
        by_contra hne
        have := key h⁻¹ (Subgroup.inv_mem _ hh) (h y) (Ne.symm hne)
        rw [inv_app', hy] at this
        apply hne
        have h2 := congrArg h this
        rw [app_inv'] at h2
        exact h2.symm
      · exact key h hh y hy
    ext y
    simp only [Perm.mul_apply]
    exact hall y
  · intro hh
    have hconj : ∀ k : Perm α, k * z = z * k → ∀ g ∈ J, k * g * k⁻¹ ∈ J := by
      intro k hk g hg
      have hk' : ∀ y, k (z y) = z (k y) := fun y => by
        have := congrArg (· y) hk
        simpa only [Perm.mul_apply] using this
      rw [hJ] at hg ⊢
      intro x
      simp only [Perm.mul_apply]
      rcases hg (k⁻¹ x) with e | e <;> rw [e]
      · left
        exact app_inv' k x
      · right
        rw [hk', app_inv']
    have hinv : h⁻¹ * z = z * h⁻¹ := (Commute.inv_left (show Commute h z from hh)).eq
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨hconj h hh g, fun hg => ?_⟩
    have := hconj h⁻¹ hinv _ hg
    simpa [mul_assoc] using this

theorem mem_normalizer_closure_of' {G : Type*} [Group G] {S : Set G} {g : G}
    (h₁ : ∀ s ∈ S, g * s * g⁻¹ ∈ Subgroup.closure S)
    (h₂ : ∀ s ∈ S, g⁻¹ * s * g ∈ Subgroup.closure S) :
    g ∈ Subgroup.normalizer ((Subgroup.closure S : Subgroup G) : Set G) := by
  have key : ∀ x : G, (∀ s ∈ S, x * s * x⁻¹ ∈ Subgroup.closure S) →
      ∀ y ∈ Subgroup.closure S, x * y * x⁻¹ ∈ Subgroup.closure S := by
    intro x hx y hy
    have hle : Subgroup.closure S ≤ (Subgroup.closure S).comap (MulAut.conj x).toMonoidHom := by
      rw [Subgroup.closure_le]
      intro s hs
      exact hx s hs
    exact hle hy
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key g h₁ y, fun hy => ?_⟩
  have := key g⁻¹ (by simpa using h₂) _ hy
  simpa [mul_assoc] using this

end SwapGroup

theorem alt_inf_normalizer_eq_kJ_stdT2 {n : ℕ} [NeZero n] (hn : n = 5 ∨ n = 7)
    {J : Subgroup (Perm (Fin n))} (hJ : ∀ g, g ∈ J ↔ ∀ x, g x = x ∨ g x = z2 n x) :
    alternatingGroup (Fin n) ⊓ Subgroup.normalizer (J : Set (Perm (Fin n))) = kJ (stdT2 n) := by
  rcases hn with rfl | rfl
  · rw [normalizer_eq_centralizer_of_mem_iff z2_invol_five hJ, kJ_stdT2_five]
  · rw [normalizer_eq_centralizer_of_mem_iff z2_invol_seven hJ, kJ_stdT2_seven]

theorem alt_inf_normalizer_eq_kJ_stdT3 {J : Subgroup (Perm (Fin 7))}
    (hJ : ∀ g, g ∈ J ↔ ∀ x, g x = x ∨ g x = z3 7 x) :
    alternatingGroup (Fin 7) ⊓ Subgroup.normalizer (J : Set (Perm (Fin 7))) = kJ (stdT3 7) := by
  rw [normalizer_eq_centralizer_of_mem_iff z3_invol hJ, kJ_stdT3]

section VFour

variable (n : ℕ) [NeZero n]

@[expose] def V4 : Subgroup (Perm (Fin n)) :=
  Subgroup.closure {swap 0 1 * swap 2 3, swap 0 2 * swap 1 3}

end VFour

private theorem dbl_5 : ∀ p q r s : Fin 5, [p, q, r, s].Nodup →
    (p ∈ quad 5 ∧ q ∈ quad 5 ∧ r ∈ quad 5 ∧ s ∈ quad 5) →
    swap p q * swap r s = swap 0 1 * swap 2 3 ∨ swap p q * swap r s = swap 0 2 * swap 1 3 ∨
      swap p q * swap r s = swap 0 1 * swap 2 3 * (swap 0 2 * swap 1 3) := by
  decide +kernel

private theorem genfix_5 : ∀ i : Fin 5, i ∉ quad 5 →
    (swap 0 1 * swap 2 3 : Perm (Fin 5)) i = i ∧ (swap 0 2 * swap 1 3 : Perm (Fin 5)) i = i := by
  decide +kernel

private theorem afix_5 :
    ∀ i : Fin 5, (swap 0 1 * swap 2 3 : Perm (Fin 5)) i = i → i ∉ quad 5 := by
  decide +kernel

private theorem lits_5 : ((0 : Fin 5) ∈ quad 5 ∧ (1 : Fin 5) ∈ quad 5 ∧ (2 : Fin 5) ∈ quad 5 ∧
    (3 : Fin 5) ∈ quad 5) ∧ ([0, 1, 2, 3] : List (Fin 5)).Nodup ∧
    ([0, 2, 1, 3] : List (Fin 5)).Nodup := by
  decide +kernel

private theorem dbl_7 : ∀ p q r s : Fin 7, [p, q, r, s].Nodup →
    (p ∈ quad 7 ∧ q ∈ quad 7 ∧ r ∈ quad 7 ∧ s ∈ quad 7) →
    swap p q * swap r s = swap 0 1 * swap 2 3 ∨ swap p q * swap r s = swap 0 2 * swap 1 3 ∨
      swap p q * swap r s = swap 0 1 * swap 2 3 * (swap 0 2 * swap 1 3) := by
  decide +kernel

private theorem genfix_7 : ∀ i : Fin 7, i ∉ quad 7 →
    (swap 0 1 * swap 2 3 : Perm (Fin 7)) i = i ∧ (swap 0 2 * swap 1 3 : Perm (Fin 7)) i = i := by
  decide +kernel

private theorem afix_7 :
    ∀ i : Fin 7, (swap 0 1 * swap 2 3 : Perm (Fin 7)) i = i → i ∉ quad 7 := by
  decide +kernel

private theorem lits_7 : ((0 : Fin 7) ∈ quad 7 ∧ (1 : Fin 7) ∈ quad 7 ∧ (2 : Fin 7) ∈ quad 7 ∧
    (3 : Fin 7) ∈ quad 7) ∧ ([0, 1, 2, 3] : List (Fin 7)).Nodup ∧
    ([0, 2, 1, 3] : List (Fin 7)).Nodup := by
  decide +kernel

private theorem v4_facts {n : ℕ} [NeZero n] (hn : n = 5 ∨ n = 7) :
    (∀ p q r s : Fin n, [p, q, r, s].Nodup →
      (p ∈ quad n ∧ q ∈ quad n ∧ r ∈ quad n ∧ s ∈ quad n) →
      swap p q * swap r s = swap 0 1 * swap 2 3 ∨ swap p q * swap r s = swap 0 2 * swap 1 3 ∨
        swap p q * swap r s = swap 0 1 * swap 2 3 * (swap 0 2 * swap 1 3)) ∧
    (∀ i : Fin n, i ∉ quad n → (swap 0 1 * swap 2 3 : Perm (Fin n)) i = i ∧
      (swap 0 2 * swap 1 3 : Perm (Fin n)) i = i) ∧
    (∀ i : Fin n, (swap 0 1 * swap 2 3 : Perm (Fin n)) i = i → i ∉ quad n) ∧
    ((0 : Fin n) ∈ quad n ∧ (1 : Fin n) ∈ quad n ∧ (2 : Fin n) ∈ quad n ∧ (3 : Fin n) ∈ quad n) ∧
    ([0, 1, 2, 3] : List (Fin n)).Nodup ∧ ([0, 2, 1, 3] : List (Fin n)).Nodup := by
  rcases hn with rfl | rfl
  · exact ⟨dbl_5, genfix_5, afix_5, lits_5⟩
  · exact ⟨dbl_7, genfix_7, afix_7, lits_7⟩

theorem swap01_23_mem_V4 (n : ℕ) [NeZero n] : (swap 0 1 * swap 2 3 : Perm (Fin n)) ∈ V4 n :=
  Subgroup.subset_closure (Set.mem_insert _ _)

theorem swap02_13_mem_V4 (n : ℕ) [NeZero n] : (swap 0 2 * swap 1 3 : Perm (Fin n)) ∈ V4 n :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem quadStab_le_normalizer_V4 {n : ℕ} [NeZero n] (hn : n = 5 ∨ n = 7) :
    quadStab n ≤ Subgroup.normalizer ((V4 n : Subgroup (Perm (Fin n))) : Set (Perm (Fin n))) := by
  obtain ⟨hdbl, -, -, ⟨hq0, hq1, hq2, hq3⟩, hnd1, hnd2⟩ := v4_facts hn
  have hmem : ∀ {p q r t : Fin n}, [p, q, r, t].Nodup →
      (p ∈ quad n ∧ q ∈ quad n ∧ r ∈ quad n ∧ t ∈ quad n) → swap p q * swap r t ∈ V4 n := by
    intro p q r t hnd hq
    rcases hdbl p q r t hnd hq with e | e | e <;> rw [e]
    · exact swap01_23_mem_V4 n
    · exact swap02_13_mem_V4 n
    · exact Subgroup.mul_mem _ (swap01_23_mem_V4 n) (swap02_13_mem_V4 n)
  have key : ∀ k : Perm (Fin n), (∀ x, k x ∈ quad n ↔ x ∈ quad n) →
      ∀ s ∈ ({swap 0 1 * swap 2 3, swap 0 2 * swap 1 3} : Set (Perm (Fin n))),
        k * s * k⁻¹ ∈ V4 n := by
    intro k hk s hs
    have hk0 := (hk 0).mpr hq0
    have hk1 := (hk 1).mpr hq1
    have hk2 := (hk 2).mpr hq2
    have hk3 := (hk 3).mpr hq3
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · rw [show k * (swap 0 1 * swap 2 3) * k⁻¹ = (k * swap 0 1 * k⁻¹) * (k * swap 2 3 * k⁻¹) by
        group, ← swap_apply_apply, ← swap_apply_apply]
      exact hmem (hnd1.map k.injective) ⟨hk0, hk1, hk2, hk3⟩
    · rw [show k * (swap 0 2 * swap 1 3) * k⁻¹ = (k * swap 0 2 * k⁻¹) * (k * swap 1 3 * k⁻¹) by
        group, ← swap_apply_apply, ← swap_apply_apply]
      exact hmem (hnd2.map k.injective) ⟨hk0, hk2, hk1, hk3⟩
  intro g hg
  rw [quadStab, mem_alt_inf_stabilizer_iff] at hg
  have hgi : ∀ x, g⁻¹ x ∈ quad n ↔ x ∈ quad n := fun x => by
    rw [← hg.2 (g⁻¹ x), app_inv']
  exact mem_normalizer_closure_of' (key g hg.2) (key g⁻¹ hgi)

theorem V4_fix {n : ℕ} [NeZero n] (hn : n = 5 ∨ n = 7) {g : Perm (Fin n)} (hg : g ∈ V4 n)
    {i : Fin n} (hi : i ∉ quad n) : g i = i := by
  obtain ⟨-, hgen, -⟩ := v4_facts hn
  have hle : V4 n ≤ fixingSubgroup (Perm (Fin n)) ((quad n : Set (Fin n))ᶜ) := by
    rw [V4, Subgroup.closure_le]
    intro s hs
    rw [SetLike.mem_coe, mem_fixingSubgroup_iff]
    intro y hy
    rw [Set.mem_compl_iff, Finset.mem_coe] at hy
    rw [Perm.smul_def]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact (hgen y hy).1
    · exact (hgen y hy).2
  have := (mem_fixingSubgroup_iff _).mp (hle hg) i (by simpa using hi)
  rwa [Perm.smul_def] at this

theorem mem_quadStab_of_normalizer_V4 {n : ℕ} [NeZero n] (hn : n = 5 ∨ n = 7) {g : Perm (Fin n)}
    (hgA : g ∈ alternatingGroup (Fin n))
    (hg : g ∈ Subgroup.normalizer ((V4 n : Subgroup (Perm (Fin n))) : Set (Perm (Fin n)))) :
    g ∈ quadStab n := by
  obtain ⟨-, -, hfix, -⟩ := v4_facts hn
  rw [quadStab, mem_alt_inf_stabilizer_iff]
  refine ⟨Perm.mem_alternatingGroup.mp hgA, ?_⟩
  have hconj : g * (swap 0 1 * swap 2 3) * g⁻¹ ∈ V4 n :=
    (Subgroup.mem_normalizer_iff.mp hg _).mp (swap01_23_mem_V4 n)
  have hout : ∀ i, i ∉ quad n → g⁻¹ i ∉ quad n := by
    intro i hi
    have h1 : (g * (swap 0 1 * swap 2 3) * g⁻¹ : Perm (Fin n)) i = i := V4_fix hn hconj hi
    simp only [Perm.mul_apply] at h1
    have h2 : (swap 0 1 * swap 2 3 : Perm (Fin n)) (g⁻¹ i) = g⁻¹ i := by
      have := congrArg (fun y => g⁻¹ y) h1
      simp only [inv_app'] at this
      exact this
    exact hfix _ h2
  have hst : g⁻¹ ∈ MulAction.stabilizer (Perm (Fin n))
      (((quad n)ᶜ : Finset (Fin n)) : Set (Fin n)) := by
    by_contra hcon
    obtain ⟨x, hx, hgx⟩ := exists_mem_apply_not_mem hcon
    rw [Finset.mem_compl] at hx hgx
    exact hgx (hout x hx)
  rw [mem_stabilizer_coe_finset_iff] at hst
  intro x
  have := hst (g x)
  rw [inv_app', Finset.mem_compl, Finset.mem_compl] at this
  exact (not_iff_not.mp this).symm

theorem quadStab_eq_normalizer_V4 {n : ℕ} [NeZero n] (hn : n = 5 ∨ n = 7) :
    quadStab n = alternatingGroup (Fin n) ⊓
      Subgroup.normalizer ((V4 n : Subgroup (Perm (Fin n))) : Set (Perm (Fin n))) :=
  le_antisymm (le_inf (fun _ hg => (Subgroup.mem_inf.mp hg).1) (quadStab_le_normalizer_V4 hn))
    fun _ hg => mem_quadStab_of_normalizer_V4 hn (Subgroup.mem_inf.mp hg).1
      (Subgroup.mem_inf.mp hg).2

theorem alt_inf_normalizer_kleinRegular7 :
    alternatingGroup (Fin 7) ⊓ Subgroup.normalizer
      ((CFSG.Quasithin.kleinRegular7 : Subgroup (Perm (Fin 7))) : Set (Perm (Fin 7))) =
      quadStab 7 :=
  (quadStab_eq_normalizer_V4 (Or.inr rfl)).symm

theorem V4_le_kJ_stdT2_five : V4 5 ≤ kJ (stdT2 5) := by
  rw [V4, Subgroup.closure_le]
  intro s hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl <;> exact mem_kJ_stdT2_five (by decide +kernel)

theorem V4_le_kJ_stdT2_seven : V4 7 ≤ kJ (stdT2 7) := by
  rw [V4, Subgroup.closure_le]
  intro s hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl <;> exact mem_kJ_stdT2_seven (by decide +kernel)

theorem V4_le_kJ_stdT2 {n : ℕ} [NeZero n] (hn : n = 5 ∨ n = 7) : V4 n ≤ kJ (stdT2 n) := by
  rcases hn with rfl | rfl
  · exact V4_le_kJ_stdT2_five
  · exact V4_le_kJ_stdT2_seven

theorem kJ_stdT2_le_normalizer_V4 {n : ℕ} [NeZero n] (hn : n = 5 ∨ n = 7) :
    kJ (stdT2 n) ≤ Subgroup.normalizer ((V4 n : Subgroup (Perm (Fin n))) : Set (Perm (Fin n))) := by
  refine le_trans ?_ (quadStab_le_normalizer_V4 hn)
  rcases hn with rfl | rfl
  · exact kJ_stdT2_le_quadStab_five
  · exact kJ_stdT2_le_quadStab_seven

theorem V4_five_eq_kJ : V4 5 = kJ (stdT2 5) := by
  refine Subgroup.eq_of_le_of_card_ge (V4_le_kJ_stdT2 (Or.inl rfl)) ?_
  rw [card_kJ_stdT2_five]
  have hsub : (({1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 1 * swap 2 3 *
      (swap 0 2 * swap 1 3)} : Finset (Perm (Fin 5))) : Set (Perm (Fin 5))) ⊆ V4 5 := by
    intro g hg
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact swap01_23_mem_V4 5
    · exact swap02_13_mem_V4 5
    · exact Subgroup.mul_mem _ (swap01_23_mem_V4 5) (swap02_13_mem_V4 5)
  have hcard := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset] at hcard
  have h4 : ({1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 1 * swap 2 3 *
      (swap 0 2 * swap 1 3)} : Finset (Perm (Fin 5))).card = 4 := by decide +kernel
  rw [h4, ← Nat.card_coe_set_eq] at hcard
  exact hcard

theorem card_V4_five : Nat.card (V4 5) = 4 := by
  rw [V4_five_eq_kJ, card_kJ_stdT2_five]

theorem isSylowTwoOf_V4_five :
    CFSG.QuasithinUnique.IsSylowTwoOf (V4 5) (alternatingGroup (Fin 5)) := by
  have hle : V4 5 ≤ alternatingGroup (Fin 5) :=
    (V4_le_kJ_stdT2 (Or.inl rfl)).trans inf_le_left
  refine ⟨hle, IsPGroup.of_card (n := 2) (by rw [card_V4_five]; norm_num), ?_⟩
  have h := relIndex_mul_card_of_le hle
  rw [card_V4_five, card_alt_five] at h
  change ¬ 2 ∣ (V4 5).relIndex (alternatingGroup (Fin 5))
  have h15 : (V4 5).relIndex (alternatingGroup (Fin 5)) = 15 := by omega
  rw [h15]
  decide

theorem isBorelIn_quadStab_five : IsBorelIn (alternatingGroup (Fin 5)) (quadStab 5) :=
  ⟨V4 5, isSylowTwoOf_V4_five, quadStab_eq_normalizer_V4 (Or.inl rfl)⟩

section ConjClosure

abbrev conjSwapClosure (Y : Subgroup (Perm (Fin 7))) : Subgroup (Perm (Fin 7)) :=
  Subgroup.closure {x | ∃ y ∈ Y, x = y * swap 0 1 * y⁻¹}

theorem swap_mem_conjSwapClosure {Y : Subgroup (Perm (Fin 7))} {y : Perm (Fin 7)} (hy : y ∈ Y) :
    swap (y 0) (y 1) ∈ conjSwapClosure Y :=
  Subgroup.subset_closure ⟨y, hy, (swap_apply_apply y 0 1)⟩

theorem mem_closure_swaps_of_fix {α : Type*} [DecidableEq α] [Fintype α] (p : α → Prop)
    [DecidablePred p] {g : Perm α} (hg : ∀ x, ¬ p x → g x = x) :
    g ∈ Subgroup.closure {s | ∃ a b, p a ∧ p b ∧ a ≠ b ∧ s = swap a b} := by
  have h₁ : ∀ x, p (g x) ↔ p x := by
    intro x
    by_cases hx : p x
    · refine ⟨fun _ => hx, fun _ => ?_⟩
      by_contra hgx
      have := hg (g x) hgx
      exact hgx (by rw [g.injective this]; exact hx)
    · rw [hg x hx]
  have hsup : ∀ x, g x ≠ x → p x := fun x h => by
    by_contra hx
    exact h (hg x hx)
  rw [← Perm.ofSubtype_subtypePerm h₁ hsup]
  have hmem : g.subtypePerm h₁ ∈ Subgroup.closure {σ : Perm (Subtype p) | σ.IsSwap} := by
    rw [Perm.closure_isSwap]
    exact Subgroup.mem_top _
  have hmap := Subgroup.mem_map_of_mem (Perm.ofSubtype : Perm (Subtype p) →* Perm α) hmem
  rw [MonoidHom.map_closure] at hmap
  refine Subgroup.closure_mono ?_ hmap
  rintro _ ⟨σ, ⟨a, b, hab, rfl⟩, rfl⟩
  exact ⟨a, b, a.2, b.2, fun e => hab (Subtype.ext e), Perm.ofSubtype_swap_eq a b⟩

theorem card_stabilizer_six : Nat.card (MulAction.stabilizer (Perm (Fin 7)) (6 : Fin 7)) = 720 := by
  have h := card_stabilizer_coe_finset ({6} : Finset (Fin 7))
  rw [Finset.coe_singleton, MulAction.stabilizer_singleton] at h
  rw [h]
  decide +kernel

@[expose] def pairWit (a b : Fin 7) : Perm (Fin 7) :=
  if sign (swap 0 a * swap 1 (swap 0 a b)) = 1 then swap 0 a * swap 1 (swap 0 a b)
  else swap 0 a * swap 1 (swap 0 a b) * swap 2 3

private theorem pairWit_spec : ∀ a b : Fin 7, a ≠ b → a ≠ 6 → b ≠ 6 →
    sign (pairWit a b) = 1 ∧ pairWit a b 6 = 6 ∧ pairWit a b 0 = a ∧ pairWit a b 1 = b := by
  decide +kernel

theorem stabilizer_six_le_conjSwapClosure :
    MulAction.stabilizer (Perm (Fin 7)) (6 : Fin 7) ≤ conjSwapClosure pointStab := by
  intro g hg
  rw [MulAction.mem_stabilizer_iff, Perm.smul_def] at hg
  have hfix : ∀ x, ¬ x ≠ 6 → g x = x := fun x hx => by
    rw [not_not.mp hx]
    exact hg
  refine (Subgroup.closure_le _).mpr ?_ (mem_closure_swaps_of_fix (fun x => x ≠ 6) hfix)
  rintro _ ⟨a, b, ha, hb, hab, rfl⟩
  obtain ⟨hs, h6, h0, h1⟩ := pairWit_spec a b hab ha hb
  have hmem : pairWit a b ∈ pointStab := mem_pointStab_iff.mpr ⟨hs, h6⟩
  have := swap_mem_conjSwapClosure hmem
  rwa [h0, h1] at this

private theorem one_reach : ∀ x : Fin 7, x ≠ 6 → ∃ e ∈ kJ (stdT3 7), e 1 = x ∧ e 6 = 6 := by
  have hq : ∀ y : Fin 7, y ≠ 6 → y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 := by decide
  intro x hx
  rcases hq x hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨swap 0 1 * swap 2 3, mem_kJ_stdT3 (by decide +kernel), by decide, by decide⟩
  · exact ⟨1, Subgroup.one_mem _, rfl, rfl⟩
  · exact ⟨swap 0 3 * swap 1 2, mem_kJ_stdT3 (by decide +kernel), by decide, by decide⟩
  · exact ⟨swap 0 2 * swap 1 3, mem_kJ_stdT3 (by decide +kernel), by decide, by decide⟩
  · exact ⟨swap 0 5 * swap 1 4, mem_kJ_stdT3 (by decide +kernel), by decide, by decide⟩
  · exact ⟨swap 0 4 * swap 1 5, mem_kJ_stdT3 (by decide +kernel), by decide, by decide⟩

private theorem conjSwapClosure_eq_top {Y : Subgroup (Perm (Fin 7))} (hY : kJ (stdT3 7) ≤ Y)
    {τ : Perm (Fin 7)} (hτ : τ ∈ Y) (hτ0 : τ 0 = 6) (hτ1 : τ 1 = 1) :
    conjSwapClosure Y = ⊤ := by
  have h6 : ∀ x : Fin 7, x ≠ 6 → swap x 6 ∈ conjSwapClosure Y := by
    intro x hx
    obtain ⟨e, he, he1, he6⟩ := one_reach x hx
    have := swap_mem_conjSwapClosure (Y.mul_mem (hY he) hτ)
    rwa [Perm.mul_apply, Perm.mul_apply, hτ0, hτ1, he6, he1, swap_comm] at this
  have hall : ∀ a b : Fin 7, a ≠ b → swap a b ∈ conjSwapClosure Y := by
    intro a b hab
    by_cases ha : a = 6
    · subst ha
      rw [swap_comm]
      exact h6 b (Ne.symm hab)
    by_cases hb : b = 6
    · subst hb
      exact h6 a hab
    have he : swap a b = swap a 6 * swap b 6 * swap a 6 := by
      have h := swap_apply_apply (swap a 6) b 6
      rw [swap_apply_of_ne_of_ne (Ne.symm hab) hb, swap_apply_right, swap_inv] at h
      calc swap a b = swap b a := swap_comm a b
        _ = swap a 6 * swap b 6 * swap a 6 := h
    rw [he]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (h6 a ha) (h6 b hb)) (h6 a ha)
  rw [eq_top_iff, ← Perm.closure_isSwap, Subgroup.closure_le]
  rintro _ ⟨a, b, hab, rfl⟩
  exact hall a b hab

theorem conjSwapClosure_fanoStabEven : conjSwapClosure fanoStabEven = ⊤ :=
  conjSwapClosure_eq_top kJ_stdT3_le_fanoStabEven
    (Subgroup.mem_inf.mpr ⟨Perm.mem_alternatingGroup.mpr (by decide +kernel),
      MulAction.mem_stabilizer_iff.mpr (by decide +kernel)⟩)
    (show (swap 0 6 * swap 3 4 : Perm (Fin 7)) 0 = 6 by decide)
    (show (swap 0 6 * swap 3 4 : Perm (Fin 7)) 1 = 1 by decide)

theorem conjSwapClosure_fanoStabOdd : conjSwapClosure fanoStabOdd = ⊤ :=
  conjSwapClosure_eq_top kJ_stdT3_le_fanoStabOdd
    (Subgroup.mem_inf.mpr ⟨Perm.mem_alternatingGroup.mpr (by decide +kernel),
      MulAction.mem_stabilizer_iff.mpr (by decide +kernel)⟩)
    (show (swap 0 6 * swap 3 5 : Perm (Fin 7)) 0 = 6 by decide)
    (show (swap 0 6 * swap 3 5 : Perm (Fin 7)) 1 = 1 by decide)

theorem sixteen_dvd_card_closure_conj {Y : Subgroup (Perm (Fin 7))}
    (hY : Y = pointStab ∨ Y = fanoStabEven ∨ Y = fanoStabOdd) :
    16 ∣ Nat.card (Subgroup.closure {x | ∃ y ∈ Y, x = y * swap 0 1 * y⁻¹}) := by
  rcases hY with rfl | rfl | rfl
  · have h := Subgroup.card_dvd_of_le stabilizer_six_le_conjSwapClosure
    rw [card_stabilizer_six] at h
    exact dvd_trans (by norm_num) h
  · change 16 ∣ Nat.card (conjSwapClosure fanoStabEven)
    rw [conjSwapClosure_fanoStabEven, Subgroup.card_top, Nat.card_perm, Nat.card_fin]
    decide
  · change 16 ∣ Nat.card (conjSwapClosure fanoStabOdd)
    rw [conjSwapClosure_fanoStabOdd, Subgroup.card_top, Nat.card_perm, Nat.card_fin]
    decide

end ConjClosure

section Module

open CFSG.Quasithin.G6

theorem toAdd_coreAct {n : ℕ} (σ : Perm (Fin n)) (x : ↥(coreMod n)) (i : Fin n) :
    Multiplicative.toAdd ((coreAct n σ x : ↥(coreMod n)) : PermMod n) i =
      Multiplicative.toAdd (x : PermMod n) (σ⁻¹ i) := rfl

theorem coreMod_ext {n : ℕ} {x y : ↥(coreMod n)}
    (h : ∀ i, Multiplicative.toAdd (x : PermMod n) i = Multiplicative.toAdd (y : PermMod n) i) :
    x = y :=
  Subtype.ext (Multiplicative.toAdd.injective (funext h))

theorem toAdd_coreMod_mul {n : ℕ} (x y : ↥(coreMod n)) (i : Fin n) :
    Multiplicative.toAdd ((x * y : ↥(coreMod n)) : PermMod n) i =
      Multiplicative.toAdd (x : PermMod n) i + Multiplicative.toAdd (y : PermMod n) i := rfl

private theorem zmod2_add_self : ∀ a : ZMod 2, a + a = 0 := by decide

theorem toAdd_mul_coreAct_of_fix {n : ℕ} (v : ↥(coreMod n)) {w : Perm (Fin n)} {i : Fin n}
    (hw : w i = i) :
    Multiplicative.toAdd ((v * coreAct n w v : ↥(coreMod n)) : PermMod n) i = 0 := by
  rw [toAdd_coreMod_mul, toAdd_coreAct]
  have : w⁻¹ i = i := by
    rw [Perm.inv_eq_iff_eq]
    exact hw.symm
  rw [this]
  exact zmod2_add_self _

theorem threeCycle01_facts {n : ℕ} [NeZero n] (h01 : (0 : Fin n) ≠ 1) {e : Fin n}
    (he0 : e ≠ 0) (he1 : e ≠ 1) :
    (∀ i, i ≠ 0 → i ≠ 1 → i ≠ e → (swap 0 e * swap 0 1 : Perm (Fin n)) i = i) ∧
      (swap 0 e * swap 0 1 : Perm (Fin n)).IsThreeCycle ∧
      (swap 0 e * swap 0 1 : Perm (Fin n)) ∈ alternatingGroup (Fin n) ∧
      (swap 0 e * swap 0 1 : Perm (Fin n)) * swap 0 1 ≠ swap 0 1 * (swap 0 e * swap 0 1) := by
  have h3 : (swap 0 e * swap 0 1 : Perm (Fin n)).IsThreeCycle :=
    isThreeCycle_swap_mul_swap_same he0.symm h01 he1
  refine ⟨fun i hi0 hi1 hie => ?_, h3, h3.mem_alternatingGroup, fun h => ?_⟩
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne hi0 hi1, swap_apply_of_ne_of_ne hi0 hie]
  · have := congrArg (· 0) h
    simp only [Perm.mul_apply, swap_apply_left, swap_apply_right,
      swap_apply_of_ne_of_ne h01.symm he1.symm] at this
    exact he0 this

private theorem v4mod_lits_five : (swap 0 1 * swap 2 3 : Perm (Fin 5))⁻¹ 2 = 3 ∧
    (swap 0 2 * swap 1 3 : Perm (Fin 5))⁻¹ 0 = 2 ∧ (swap 0 2 * swap 1 3 : Perm (Fin 5))⁻¹ 1 = 3 ∧
    (3 : Fin 5) ≠ 0 ∧ (3 : Fin 5) ≠ 1 ∧ (3 : Fin 5) ≠ 2 := by
  decide +kernel

private theorem v4mod_lits_seven : (swap 0 1 * swap 2 3 : Perm (Fin 7))⁻¹ 2 = 3 ∧
    (swap 0 2 * swap 1 3 : Perm (Fin 7))⁻¹ 0 = 2 ∧ (swap 0 2 * swap 1 3 : Perm (Fin 7))⁻¹ 1 = 3 ∧
    (3 : Fin 7) ≠ 0 ∧ (3 : Fin 7) ≠ 1 ∧ (3 : Fin 7) ≠ 2 := by
  decide +kernel

theorem eq_one_of_coreFix_V4 {n : ℕ} [NeZero n] (hn : n = 5 ∨ n = 7) {x y : ↥(coreMod n)}
    {c : Perm (Fin n)} (hc : ∀ i, i ≠ 0 → i ≠ 1 → i ≠ 2 → c i = i)
    (hxy : x = y * coreAct n c y) (h1 : coreAct n (swap 0 1 * swap 2 3) x = x)
    (h2 : coreAct n (swap 0 2 * swap 1 3) x = x) : x = 1 := by
  obtain ⟨l1, l2, l3, h30, h31, h32⟩ : (swap 0 1 * swap 2 3 : Perm (Fin n))⁻¹ 2 = 3 ∧
      (swap 0 2 * swap 1 3 : Perm (Fin n))⁻¹ 0 = 2 ∧
      (swap 0 2 * swap 1 3 : Perm (Fin n))⁻¹ 1 = 3 ∧
      (3 : Fin n) ≠ 0 ∧ (3 : Fin n) ≠ 1 ∧ (3 : Fin n) ≠ 2 := by
    rcases hn with rfl | rfl
    · exact v4mod_lits_five
    · exact v4mod_lits_seven
  have hout : ∀ i, i ≠ 0 → i ≠ 1 → i ≠ 2 → Multiplicative.toAdd (x : PermMod n) i = 0 := by
    intro i hi0 hi1 hi2
    rw [hxy]
    exact toAdd_mul_coreAct_of_fix y (hc i hi0 hi1 hi2)
  have hx3 := hout 3 h30 h31 h32
  have hx2 : Multiplicative.toAdd (x : PermMod n) 2 = 0 := by
    have := congrArg (fun z : ↥(coreMod n) => Multiplicative.toAdd (z : PermMod n) 2) h1
    simp only [toAdd_coreAct, l1] at this
    rw [← this, hx3]
  have hx0 : Multiplicative.toAdd (x : PermMod n) 0 = 0 := by
    have := congrArg (fun z : ↥(coreMod n) => Multiplicative.toAdd (z : PermMod n) 0) h2
    simp only [toAdd_coreAct, l2] at this
    rw [← this, hx2]
  have hx1 : Multiplicative.toAdd (x : PermMod n) 1 = 0 := by
    have := congrArg (fun z : ↥(coreMod n) => Multiplicative.toAdd (z : PermMod n) 1) h2
    simp only [toAdd_coreAct, l3] at this
    rw [← this, hx3]
  apply coreMod_ext
  intro i
  show Multiplicative.toAdd (x : PermMod n) i = 0
  by_cases hi0 : i = 0
  · rw [hi0, hx0]
  by_cases hi1 : i = 1
  · rw [hi1, hx1]
  by_cases hi2 : i = 2
  · rw [hi2, hx2]
  exact hout i hi0 hi1 hi2

end Module

end CFSG.Quasithin.SmithC27
