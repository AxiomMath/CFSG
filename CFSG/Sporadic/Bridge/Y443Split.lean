module

public import CFSG.Sporadic.Bridge.Y322Words
public import CFSG.Blueprint.NativeSporadic
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all CFSG.Sporadic.Bridge.Y322Words

public section

namespace CFSG.Sporadic.Bridge.Y443

open CFSG.Blueprint.NativeSporadic CFSG.Certificates
open scoped commutatorElement

noncomputable abbrev x (i : Fin 12) : Y443 := PresentedGroup.of i

theorem adjacent_iff (i j : Fin 12) : y443Adjacent i j ↔
    ((i.val = 0 ∧ (j.val = 1 ∨ j.val = 5 ∨ j.val = 9)) ∨
      (j.val = 0 ∧ (i.val = 1 ∨ i.val = 5 ∨ i.val = 9)) ∨
      (i.val + 1 = j.val ∧ (i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 5 ∨ i.val = 6 ∨
        i.val = 7 ∨ i.val = 9 ∨ i.val = 10)) ∨
      (j.val + 1 = i.val ∧ (j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 5 ∨ j.val = 6 ∨
        j.val = 7 ∨ j.val = 9 ∨ j.val = 10))) := by
  simp only [y443Adjacent, Set.mem_insert_iff, Set.mem_singleton_iff]

@[expose] def adjList : List (ℕ × ℕ) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (0, 5), (5, 6), (6, 7), (7, 8), (0, 9), (9, 10), (10, 11)]

@[expose] def adjB (i j : Fin 12) : Bool :=
  adjList.contains (i.val, j.val) || adjList.contains (j.val, i.val)

theorem adjacent_iff_adjB (i j : Fin 12) : y443Adjacent i j ↔ adjB i j = true := by
  rw [adjacent_iff]
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  simp only
  interval_cases i <;> interval_cases j <;> simp [adjB, adjList]

theorem mem_rels_sq (i : Fin 12) : FreeGroup.of i ^ 2 ∈ y443Relations := by
  unfold y443Relations
  exact Or.inl (Or.inl ⟨i, rfl⟩)

theorem mem_rels_adj {i j : Fin 12} (h : i.val < j.val) (hadj : y443Adjacent i j) :
    (FreeGroup.of i * FreeGroup.of j) ^ 3 ∈ y443Relations := by
  unfold y443Relations
  exact Or.inl (Or.inr ⟨i, j, h, by rw [ite_eq_left hadj]⟩)

theorem mem_rels_nadj {i j : Fin 12} (h : i.val < j.val) (hadj : ¬ y443Adjacent i j) :
    (FreeGroup.of i * FreeGroup.of j) ^ 2 ∈ y443Relations := by
  unfold y443Relations
  exact Or.inl (Or.inr ⟨i, j, h, by rw [ite_eq_right hadj]⟩)

@[expose] def spiderBase : FreeGroup (Fin 12) :=
  FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 2 * FreeGroup.of 0 * FreeGroup.of 5 *
    FreeGroup.of 6 * FreeGroup.of 0 * FreeGroup.of 9 * FreeGroup.of 10

theorem mem_rels_spider : spiderBase ^ 10 ∈ y443Relations := by
  unfold y443Relations spiderBase
  exact Or.inr rfl

theorem x_mul_self (i : Fin 12) : x i * x i = 1 := by
  rw [← pow_two]
  exact PresentedGroup.one_of_mem (mem_rels_sq i)

theorem x_inv (i : Fin 12) : (x i)⁻¹ = x i := inv_eq_of_mul_eq_one_right (x_mul_self i)

theorem pow_swap {i j : Fin 12} {k : ℕ} (h : (x i * x j) ^ k = 1) : (x j * x i) ^ k = 1 := by
  have e : x j * x i = (x i * x j)⁻¹ := by rw [mul_inv_rev, x_inv, x_inv]
  rw [e, inv_pow, h, inv_one]

theorem x_adj {i j : Fin 12} (hne : i ≠ j) (hadj : y443Adjacent i j) : (x i * x j) ^ 3 = 1 := by
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
  · exact PresentedGroup.one_of_mem (mem_rels_adj h hadj)
  · apply pow_swap
    refine PresentedGroup.one_of_mem (mem_rels_adj h ?_)
    rw [adjacent_iff] at hadj ⊢
    omega

theorem x_nadj {i j : Fin 12} (hne : i ≠ j) (hadj : ¬ y443Adjacent i j) :
    (x i * x j) ^ 2 = 1 := by
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
  · exact PresentedGroup.one_of_mem (mem_rels_nadj h hadj)
  · apply pow_swap
    refine PresentedGroup.one_of_mem (mem_rels_nadj h ?_)
    rw [adjacent_iff] at hadj ⊢
    omega

theorem commute_nadj {i j : Fin 12} (hne : i ≠ j) (hadj : ¬ y443Adjacent i j) :
    Commute (x i) (x j) := by
  have h := x_nadj hne hadj
  rw [pow_two] at h
  have e : x i * x j = (x i * x j)⁻¹ := eq_inv_of_mul_eq_one_left h
  rw [mul_inv_rev, x_inv, x_inv] at e
  exact e

theorem spider : (x 0 * x 1 * x 2 * x 0 * x 5 * x 6 * x 0 * x 9 * x 10) ^ 10 = 1 :=
  PresentedGroup.one_of_mem mem_rels_spider

@[expose] def m : Fin 8 → Fin 12 := ![0, 9, 10, 11, 1, 2, 5, 6]

theorem m_injective : Function.Injective m := by decide

noncomputable abbrev s (i : Fin 8) : Y443 := x (m i)

theorem exponent_cases_b : ∀ i j : Fin 8, i ≠ j →
    (Y322.exponent i j = 3 ∧ adjB (m i) (m j) = true) ∨
      (Y322.exponent i j = 2 ∧ adjB (m i) (m j) = false) := by
  decide

theorem exponent_cases (i j : Fin 8) (h : i ≠ j) :
    (Y322.exponent i j = 3 ∧ y443Adjacent (m i) (m j)) ∨
      (Y322.exponent i j = 2 ∧ ¬ y443Adjacent (m i) (m j)) := by
  rw [adjacent_iff_adjB]
  rcases exponent_cases_b i j h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, by rw [h2]; decide⟩

theorem s_eq : s 0 = x 0 ∧ s 1 = x 9 ∧ s 2 = x 10 ∧ s 3 = x 11 ∧ s 4 = x 1 ∧ s 5 = x 2 ∧
    s 6 = x 5 ∧ s 7 = x 6 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem spider322 : (s 0 * s 1 * s 2 * s 0 * s 4 * s 5 * s 0 * s 6 * s 7) ^ 10 = 1 := by
  obtain ⟨h0, h1, h2, -, h4, h5, h6, h7⟩ := s_eq
  have e : s 0 * s 1 * s 2 * s 0 * s 4 * s 5 * s 0 * s 6 * s 7 =
      ((x 0 * x 1 * x 2) * (x 0 * x 5 * x 6))⁻¹ *
        (x 0 * x 1 * x 2 * x 0 * x 5 * x 6 * x 0 * x 9 * x 10) *
        ((x 0 * x 1 * x 2) * (x 0 * x 5 * x 6))⁻¹⁻¹ := by
    rw [h0, h1, h2, h4, h5, h6, h7, inv_inv]
    group
  rw [e, conj_pow, spider, mul_one, mul_inv_cancel]

theorem s_relations : ∀ w ∈ Y322.words, signedProd s w = 1 := by
  rw [Y322.relations_iff]
  refine ⟨fun i => x_mul_self _, fun i j hij => ?_, spider322⟩
  have hne : m i ≠ m j := m_injective.ne (ne_of_lt hij)
  rcases exponent_cases i j (ne_of_lt hij) with ⟨he, ha⟩ | ⟨he, ha⟩
  · rw [he]; exact x_adj hne ha
  · rw [he]; exact x_nadj hne ha

noncomputable abbrev z : Y443 := (x 0 * x 9 * x 10 * x 11 * x 1 * x 2 * x 5) ^ 9

theorem f1_eq : signedProd s Y322.f1Word = z := by
  rw [Y322.signedProd_f1Word]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, -⟩ := s_eq
  rw [h0, h1, h2, h3, h4, h5, h6]

theorem f2_eq : signedProd s Y322.f2Word = (x 0 * x 9 * x 10 * x 11 * x 5 * x 6 * x 1) ^ 9 := by
  rw [Y322.signedProd_f2Word]
  obtain ⟨h0, h1, h2, h3, h4, -, h6, h7⟩ := s_eq
  rw [h0, h1, h2, h3, h6, h7, h4]

theorem commute_word {g : Y443} {l : List (Fin 12)} (h : ∀ k ∈ l, Commute g (x k)) :
    Commute g (l.map x).prod := by
  induction l with
  | nil => exact Commute.one_right g
  | cons k l ih =>
    rw [List.map_cons, List.prod_cons]
    exact (h k List.mem_cons_self).mul_right (ih fun k' hk' => h k' (List.mem_cons_of_mem _ hk'))

theorem commute_nadj' (i j : Fin 12) (h : i ≠ j ∧ ¬ y443Adjacent i j) : Commute (x i) (x j) :=
  commute_nadj h.1 h.2

section Central

variable (hcw : Y322.CentralWord)
include hcw

theorem z_sq : z ^ 2 = 1 := by
  rw [← f1_eq]; exact (hcw s s_relations).2.1

theorem z_eq_f2 : z = (x 0 * x 9 * x 10 * x 11 * x 5 * x 6 * x 1) ^ 9 := by
  rw [← f1_eq, ← f2_eq]; exact (hcw s s_relations).1

theorem commute_s_z (i : Fin 8) : Commute (s i) z := by
  rw [← f1_eq]; exact (hcw s s_relations).2.2 i

end Central

structure ZFacts : Prop where
  sq : z ^ 2 = 1
  eq_f2 : z = (x 0 * x 9 * x 10 * x 11 * x 5 * x 6 * x 1) ^ 9
  comm : ∀ i : Fin 8, Commute (s i) z

theorem zFacts_of_centralWord (hcw : Y322.CentralWord) : ZFacts :=
  ⟨z_sq hcw, z_eq_f2 hcw, commute_s_z hcw⟩

section Central

variable (hz : ZFacts)
include hz

theorem z_central (i : Fin 12) : Commute (x i) z := by
  have hz1 : z = ([0, 9, 10, 11, 1, 2, 5].map x).prod ^ 9 := by
    simp only [z, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  have hz2 : z = ([0, 9, 10, 11, 5, 6, 1].map x).prod ^ 9 := by
    rw [hz.eq_f2]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  fin_cases i
  · exact hz.comm 0
  · exact hz.comm 4
  · exact hz.comm 5
  · rw [hz2]
    refine (commute_word fun k hk => commute_nadj' _ _ ?_).pow_right 9
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rw [adjacent_iff_adjB]
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [hz2]
    refine (commute_word fun k hk => commute_nadj' _ _ ?_).pow_right 9
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rw [adjacent_iff_adjB]
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · exact hz.comm 6
  · exact hz.comm 7
  · rw [hz1]
    refine (commute_word fun k hk => commute_nadj' _ _ ?_).pow_right 9
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rw [adjacent_iff_adjB]
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [hz1]
    refine (commute_word fun k hk => commute_nadj' _ _ ?_).pow_right 9
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rw [adjacent_iff_adjB]
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · exact hz.comm 1
  · exact hz.comm 2
  · exact hz.comm 3

end Central

noncomputable def sgn : Y443 →* Multiplicative (ZMod 2) :=
  PresentedGroup.toGroup (f := fun _ => Multiplicative.ofAdd 1) (by
    unfold y443Relations
    rintro r ((⟨i, rfl⟩ | ⟨i, j, -, rfl⟩) | rfl)
    · simp only [map_pow, FreeGroup.lift_apply_of]; decide
    · simp only [map_pow, map_mul, FreeGroup.lift_apply_of]
      split <;> decide
    · simp only [map_pow, map_mul, FreeGroup.lift_apply_of]; decide)

theorem sgn_x (i : Fin 12) : sgn (x i) = Multiplicative.ofAdd 1 := PresentedGroup.toGroup.of _

theorem sgn_z : sgn z = Multiplicative.ofAdd 1 := by
  simp only [z, map_pow, map_mul, sgn_x]; decide

theorem commutator_le_ker_sgn : commutator Y443 ≤ sgn.ker :=
  Abelianization.commutator_subset_ker sgn

theorem conj_eq {i j : Fin 12} (h3 : (x i * x j) ^ 3 = 1) :
    (x i * x j) * x i * (x i * x j)⁻¹ = x j := by
  have e1 : (x i * x j) * x i * (x i * x j)⁻¹ = x i * x j * x i * x j * x i := by
    rw [mul_inv_rev, x_inv, x_inv]; group
  have e2 : x i * x j * x i * x j * x i = (x i * x j) ^ 3 * x j := by
    rw [show (x i * x j) ^ 3 * x j = x i * x j * x i * x j * x i * (x j * x j) by
      rw [pow_succ, pow_two]; simp only [mul_assoc], x_mul_self, mul_one]
  rw [e1, e2, h3, one_mul]

theorem inv_mul_mem_commutator {i j : Fin 12} (hne : i ≠ j) (hadj : y443Adjacent i j) :
    (x i)⁻¹ * x j ∈ commutator Y443 := by
  have e := conj_eq (x_adj hne hadj)
  have : (x i)⁻¹ * x j = ⁅(x i)⁻¹, x i * x j⁆ := by
    rw [commutatorElement_def, inv_inv]
    conv_lhs => rw [← e]
    group
  rw [this]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem inv_mul_trans {i j k : Fin 12} (h1 : (x i)⁻¹ * x j ∈ commutator Y443)
    (h2 : (x j)⁻¹ * x k ∈ commutator Y443) : (x i)⁻¹ * x k ∈ commutator Y443 := by
  have := Subgroup.mul_mem _ h1 h2
  rwa [show (x i)⁻¹ * x j * ((x j)⁻¹ * x k) = (x i)⁻¹ * x k by group] at this

theorem adj_of_adjB {i j : Fin 12} (h : adjB i j = true) : y443Adjacent i j :=
  (adjacent_iff_adjB i j).2 h

theorem x0_inv_mul_mem (k : Fin 12) : (x 0)⁻¹ * x k ∈ commutator Y443 := by
  have step : ∀ i j : Fin 12, adjB i j = true → (x i)⁻¹ * x j ∈ commutator Y443 :=
    fun i j h => inv_mul_mem_commutator (by rintro rfl; revert h; revert i; decide)
      (adj_of_adjB h)
  have h01 := step 0 1 (by decide)
  have h12 := step 1 2 (by decide)
  have h23 := step 2 3 (by decide)
  have h34 := step 3 4 (by decide)
  have h05 := step 0 5 (by decide)
  have h56 := step 5 6 (by decide)
  have h67 := step 6 7 (by decide)
  have h78 := step 7 8 (by decide)
  have h09 := step 0 9 (by decide)
  have h910 := step 9 10 (by decide)
  have h1011 := step 10 11 (by decide)
  fin_cases k
  · simp only [Fin.zero_eta, inv_mul_cancel]; exact Subgroup.one_mem _
  · exact h01
  · exact inv_mul_trans h01 h12
  · exact inv_mul_trans (inv_mul_trans h01 h12) h23
  · exact inv_mul_trans (inv_mul_trans (inv_mul_trans h01 h12) h23) h34
  · exact h05
  · exact inv_mul_trans h05 h56
  · exact inv_mul_trans (inv_mul_trans h05 h56) h67
  · exact inv_mul_trans (inv_mul_trans (inv_mul_trans h05 h56) h67) h78
  · exact h09
  · exact inv_mul_trans h09 h910
  · exact inv_mul_trans (inv_mul_trans h09 h910) h1011

theorem top_le_sup : (⊤ : Subgroup Y443) ≤ commutator Y443 ⊔ Subgroup.zpowers (x 0) := by
  rw [← PresentedGroup.closure_range_of, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_sup_of_normal_left]
  refine ⟨x k * (x 0)⁻¹, ?_, x 0, Subgroup.mem_zpowers _, by group⟩
  have hN : (commutator Y443).Normal := inferInstance
  have h := hN.conj_mem _ (x0_inv_mul_mem k) (x 0)
  rwa [show x 0 * ((x 0)⁻¹ * x k) * (x 0)⁻¹ = x k * (x 0)⁻¹ by group] at h

theorem commutator_eq_ker_sgn : commutator Y443 = sgn.ker := by
  refine le_antisymm commutator_le_ker_sgn fun g hg => ?_
  obtain ⟨c, hc, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 (top_le_sup (Subgroup.mem_top g))
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  have hx2 : x 0 ^ 2 = 1 := by rw [pow_two, x_mul_self]
  rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [zpow_mul, zpow_two, ← pow_two, hx2, one_zpow, mul_one]
    exact hc
  · exfalso
    rw [MonoidHom.mem_ker, map_mul, commutator_le_ker_sgn hc, one_mul, zpow_add, zpow_mul,
      zpow_two, ← pow_two, hx2, one_zpow, one_mul, zpow_one, sgn_x] at hg
    exact absurd hg (by decide)

open TauCeti.Sporadic.Monster in
abbrev TCG : Type :=
  PresentedGroup (coxeterMatrix.relationsSet ∪ TauCeti.Relator.relatorSet adjoinedRelators)

theorem edges_iff : ∀ i j : Fin 12,
    ((i, j) ∈ TauCeti.Sporadic.Monster.edges ∨ (j, i) ∈ TauCeti.Sporadic.Monster.edges) ↔
      adjB i j = true := by
  rw [TauCeti.Sporadic.Monster.edges_def]
  decide

theorem coxeter_eq (i j : Fin 12) (h : i ≠ j) :
    TauCeti.Sporadic.Monster.coxeterMatrix i j = if adjB i j then 3 else 2 := by
  rw [TauCeti.Sporadic.Monster.coxeterMatrix_apply, ite_eq_right h]
  by_cases hb : adjB i j = true
  · rw [ite_eq_left ((edges_iff i j).2 hb), ite_eq_left hb]
  · rw [ite_eq_right (fun h' => hb ((edges_iff i j).1 h')), ite_eq_right hb]

theorem coxeter_self (i : Fin 12) : TauCeti.Sporadic.Monster.coxeterMatrix i i = 1 := by
  rw [TauCeti.Sporadic.Monster.coxeterMatrix_apply, ite_eq_left rfl]

theorem spider_toFreeGroup :
    TauCeti.Sporadic.Monster.spiderRelator.toFreeGroup = spiderBase ^ 10 := by
  simp [TauCeti.Sporadic.Monster.spiderRelator_def, spiderBase]

@[expose] def centralBase : FreeGroup (Fin 12) :=
  FreeGroup.of 0 * FreeGroup.of 9 * FreeGroup.of 10 * FreeGroup.of 11 * FreeGroup.of 1 *
    FreeGroup.of 2 * FreeGroup.of 5

theorem central_toFreeGroup :
    TauCeti.Sporadic.Monster.centralInvolutionRelator.toFreeGroup = centralBase ^ 9 := by
  simp [TauCeti.Sporadic.Monster.centralInvolutionRelator_def, centralBase]

theorem mapsTo_rels : Set.MapsTo (MonoidHom.id (FreeGroup (Fin 12))) y443Relations
    (TauCeti.Sporadic.Monster.coxeterMatrix.relationsSet ∪
      TauCeti.Relator.relatorSet TauCeti.Sporadic.Monster.adjoinedRelators) := by
  unfold y443Relations
  rintro r ((⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩) | rfl)
  · refine Or.inl ⟨(i, i), ?_⟩
    simp [CoxeterMatrix.relation, pow_two]
  · refine Or.inl ⟨(i, j), ?_⟩
    have hne : i ≠ j := fun h => by rw [h] at hij; exact lt_irrefl _ hij
    simp only [Function.uncurry_apply_pair, CoxeterMatrix.relation, coxeter_eq i j hne,
      MonoidHom.id_apply]
    by_cases hb : adjB i j = true
    · rw [ite_eq_left hb, ite_eq_left ((adjacent_iff_adjB i j).2 hb)]
    · rw [ite_eq_right hb, ite_eq_right (fun h => hb ((adjacent_iff_adjB i j).1 h))]
  · refine Or.inr (TauCeti.Relator.mem_relatorSet.2
      ⟨TauCeti.Sporadic.Monster.spiderRelator, by simp, ?_⟩)
    rw [spider_toFreeGroup]
    rfl

theorem lift_of_eq_mk {rels : Set (FreeGroup (Fin 12))} (r : FreeGroup (Fin 12)) :
    FreeGroup.lift (PresentedGroup.of (rels := rels)) r = PresentedGroup.mk rels r := by
  have : FreeGroup.lift (PresentedGroup.of (rels := rels)) = PresentedGroup.mk rels :=
    FreeGroup.ext_hom _ _ fun i => by rw [FreeGroup.lift_apply_of]; rfl
  rw [this]

noncomputable def σ : Y443 →* TCG :=
  PresentedGroup.toGroup (f := PresentedGroup.of) fun r hr => by
    rw [lift_of_eq_mk]
    exact PresentedGroup.one_of_mem (mapsTo_rels hr)

theorem σ_x (i : Fin 12) : σ (x i) = PresentedGroup.of i := PresentedGroup.toGroup.of _

theorem σ_z : σ z = 1 := by
  have h : σ z = PresentedGroup.mk _ (centralBase ^ 9) := by
    simp only [z, map_pow, map_mul, σ_x, centralBase]
    rfl
  rw [h]
  refine PresentedGroup.one_of_mem (Or.inr (TauCeti.Relator.mem_relatorSet.2
    ⟨TauCeti.Sporadic.Monster.centralInvolutionRelator, by simp, ?_⟩))
  rw [central_toFreeGroup]

theorem mult_cases (u : Multiplicative (ZMod 2)) : u = 1 ∨ u = Multiplicative.ofAdd 1 := by
  revert u; decide

@[expose] noncomputable def ε (u : Multiplicative (ZMod 2)) : Y443 := if u = 1 then 1 else z

theorem ε_one : ε 1 = 1 := by simp [ε]

theorem ε_ofAdd : ε (Multiplicative.ofAdd 1) = z := by
  rw [ε, ite_eq_right (by decide)]

private theorem presentation_eq :
    TauCeti.SporadicName.M.presentation = TauCeti.Sporadic.Monster.presentation := rfl

section Central2

variable (hz : ZFacts)
include hz

theorem z_mul_z : z * z = 1 := by rw [← pow_two, hz.sq]

theorem prod_mul_z (l : List (Fin 12)) :
    (l.map fun i => x i * z).prod = (l.map x).prod * z ^ l.length := by
  induction l with
  | nil => simp
  | cons k l ih =>
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons, List.length_cons,
      pow_succ]
    have hc : Commute z (l.map x).prod := (commute_word fun k' _ => (z_central hz k').symm)
    calc x k * z * ((l.map x).prod * z ^ l.length)
        = x k * (z * (l.map x).prod) * z ^ l.length := by group
      _ = x k * ((l.map x).prod * z) * z ^ l.length := by rw [hc.eq]
      _ = x k * (l.map x).prod * (z ^ l.length * z) := by
          rw [(Commute.pow_left (Commute.refl z) l.length).eq]; group

theorem z_pow_even (n : ℕ) : z ^ (2 * n) = 1 := by rw [pow_mul, hz.sq, one_pow]

noncomputable def ρ : TCG →* Y443 :=
  PresentedGroup.toGroup (f := fun i => x i * z) (by
    rintro r (⟨⟨i, j⟩, rfl⟩ | hr)
    · simp only [Function.uncurry_apply_pair, CoxeterMatrix.relation, map_pow, map_mul,
        FreeGroup.lift_apply_of]
      have e : x i * z * (x j * z) = x i * x j := by
        rw [mul_assoc, ← mul_assoc z, ← (z_central hz j).eq, mul_assoc, z_mul_z hz, mul_one]
      rw [e]
      by_cases hij : i = j
      · subst hij; rw [coxeter_self, pow_one, x_mul_self]
      · rw [coxeter_eq i j hij]
        by_cases hb : adjB i j = true
        · rw [ite_eq_left hb]; exact x_adj hij ((adjacent_iff_adjB i j).2 hb)
        · rw [ite_eq_right hb]; exact x_nadj hij (fun h => hb ((adjacent_iff_adjB i j).1 h))
    · obtain ⟨t, ht, rfl⟩ := TauCeti.Relator.mem_relatorSet.1 hr
      simp only [TauCeti.Sporadic.Monster.adjoinedRelators_def, List.mem_cons,
        List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · rw [spider_toFreeGroup]
        simp only [spiderBase, map_pow, map_mul, FreeGroup.lift_apply_of]
        have hc : Commute (([0, 1, 2, 0, 5, 6, 0, 9, 10] : List (Fin 12)).map x).prod (z ^ 9) :=
          ((commute_word fun k _ => (z_central hz k).symm).symm).pow_right 9
        have e := prod_mul_z hz [0, 1, 2, 0, 5, 6, 0, 9, 10]
        rw [List.length_cons, List.length_cons, List.length_cons, List.length_cons,
          List.length_cons, List.length_cons, List.length_cons, List.length_cons,
          List.length_cons, List.length_nil] at e
        have hL : x 0 * z * (x 1 * z) * (x 2 * z) * (x 0 * z) * (x 5 * z) * (x 6 * z) *
            (x 0 * z) * (x 9 * z) * (x 10 * z) =
            ((([0, 1, 2, 0, 5, 6, 0, 9, 10] : List (Fin 12)).map fun i => x i * z).prod) := by
          simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
            mul_assoc]
        have hS : (([0, 1, 2, 0, 5, 6, 0, 9, 10] : List (Fin 12)).map x).prod =
            x 0 * x 1 * x 2 * x 0 * x 5 * x 6 * x 0 * x 9 * x 10 := by
          simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
            mul_assoc]
        rw [hL, e, hc.mul_pow, hS, spider, one_mul, ← pow_mul]
        exact z_pow_even hz 45
      · rw [central_toFreeGroup]
        simp only [centralBase, map_pow, map_mul, FreeGroup.lift_apply_of]
        have hc : Commute (([0, 9, 10, 11, 1, 2, 5] : List (Fin 12)).map x).prod (z ^ 7) :=
          ((commute_word fun k _ => (z_central hz k).symm).symm).pow_right 7
        have e := prod_mul_z hz [0, 9, 10, 11, 1, 2, 5]
        rw [List.length_cons, List.length_cons, List.length_cons, List.length_cons,
          List.length_cons, List.length_cons, List.length_cons, List.length_nil] at e
        have hL : x 0 * z * (x 9 * z) * (x 10 * z) * (x 11 * z) * (x 1 * z) * (x 2 * z) *
            (x 5 * z) =
            ((([0, 9, 10, 11, 1, 2, 5] : List (Fin 12)).map fun i => x i * z).prod) := by
          simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
            mul_assoc]
        have hS : (([0, 9, 10, 11, 1, 2, 5] : List (Fin 12)).map x).prod =
            x 0 * x 9 * x 10 * x 11 * x 1 * x 2 * x 5 := by
          simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
            mul_assoc]
        rw [hL, e, hc.mul_pow, hS, ← pow_mul]
        show z * z ^ (7 * 9) = 1
        rw [← pow_succ', show 7 * 9 + 1 = 2 * 32 by norm_num, z_pow_even hz])

theorem ρ_of (i : Fin 12) : ρ hz (PresentedGroup.of i) = x i * z := PresentedGroup.toGroup.of _

theorem σ_ρ : (σ.comp (ρ hz)) = MonoidHom.id TCG := by
  ext i
  simp only [MonoidHom.comp_apply, ρ_of, map_mul, σ_x, σ_z, mul_one, MonoidHom.id_apply]

theorem sgn_ρ (h : TCG) : sgn (ρ hz h) = 1 := by
  have : sgn.comp (ρ hz) = 1 := by
    refine PresentedGroup.ext fun i => ?_
    simp only [MonoidHom.comp_apply, ρ_of, map_mul, sgn_x, sgn_z, MonoidHom.one_apply]
    decide
  exact DFunLike.congr_fun this h

theorem ρ_mem (h : TCG) : ρ hz h ∈ commutator Y443 := by
  rw [commutator_eq_ker_sgn, MonoidHom.mem_ker]
  exact sgn_ρ hz h

theorem ε_mul (u v : Multiplicative (ZMod 2)) : ε (u * v) = ε u * ε v := by
  rcases mult_cases u with rfl | rfl <;> rcases mult_cases v with rfl | rfl
  · simp [ε_one]
  · simp [ε_one]
  · simp [ε_one]
  · rw [show Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 = 1 by decide, ε_one,
      ε_ofAdd, z_mul_z hz]

theorem ε_inv (u : Multiplicative (ZMod 2)) : ε u⁻¹ = (ε u)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← ε_mul hz, show u⁻¹ * u = 1 from inv_mul_cancel u, ε_one])

theorem commute_z (g : Y443) : Commute g z := by
  have : g ∈ Subgroup.centralizer {z} := PresentedGroup.generated_by _ _ (fun j =>
    Subgroup.mem_centralizer_singleton_iff.2 (z_central hz j).eq) g
  exact Subgroup.mem_centralizer_singleton_iff.1 this

theorem commute_ε (g : Y443) (u : Multiplicative (ZMod 2)) : Commute g (ε u) := by
  unfold ε; split
  · exact Commute.one_right g
  · exact commute_z hz g

noncomputable def goodSub : Subgroup Y443 where
  carrier := {g | ρ hz (σ g) = g * ε (sgn g)}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [map_mul, map_mul, ha, hb, map_mul, ε_mul hz, mul_assoc, ← mul_assoc (ε _) b,
      (commute_ε hz b _).eq.symm, mul_assoc, mul_assoc]
  one_mem' := by simp [ε_one]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at *
    rw [map_inv, map_inv, ha, map_inv, ε_inv hz, mul_inv_rev]
    exact ((commute_ε hz a⁻¹ (sgn a)).inv_right).eq.symm

theorem ρσ_eq (g : Y443) : ρ hz (σ g) = g * ε (sgn g) := by
  have : g ∈ goodSub hz := PresentedGroup.generated_by _ _ (fun j => by
    show ρ hz (σ (x j)) = x j * ε (sgn (x j))
    rw [σ_x, ρ_of, sgn_x, ε_ofAdd]) g
  exact this

theorem ρσ_of_mem {g : Y443} (hg : g ∈ commutator Y443) : ρ hz (σ g) = g := by
  rw [ρσ_eq hz, commutator_le_ker_sgn hg, ε_one, mul_one]

noncomputable def mulEquivTCG : commutator Y443 ≃* TCG where
  toFun g := σ (g : Y443)
  invFun h := ⟨ρ hz h, ρ_mem hz h⟩
  left_inv g := Subtype.ext (ρσ_of_mem hz g.2)
  right_inv h := DFunLike.congr_fun (σ_ρ hz) h
  map_mul' g h := map_mul σ (g : Y443) (h : Y443)

end Central2

theorem nonempty_mulEquiv_of_centralWord (hcw : Y322.CentralWord) :
    Nonempty (Blueprint.NativeSporadic.Carrier .M ≃* TauCeti.SporadicName.M.Group) := by
  show Nonempty (↥(commutator Y443) ≃* TauCeti.SporadicName.M.presentation.Group)
  rw [presentation_eq]
  exact ⟨(mulEquivTCG (zFacts_of_centralWord hcw)).trans
    TauCeti.Sporadic.Monster.mulEquivPresentedGroupCoxeterAppend.symm⟩


end CFSG.Sporadic.Bridge.Y443
