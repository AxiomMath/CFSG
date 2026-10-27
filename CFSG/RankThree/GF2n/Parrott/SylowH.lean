module

public import CFSG.RankThree.GF2n.Parrott.LocalData
public import CFSG.RankThree.GF2n.Parrott.LiftOrderThree
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

public section

namespace CFSG.RankThree.GF2n.Parrott

open scoped Pointwise
open CFSG.ComponentClassification.CatFactsSmall.PSp43

local notation "P45" => Equiv.Perm (Fin 45)

namespace SylowHAux

private theorem card_sup_zpowers_of_sq_mem {G : Type*} [Group G] [Finite G] {N : Subgroup G}
    {g : G} (hn : g ∈ Subgroup.normalizer (N : Set G)) (hsq : g * g ∈ N) (hg : g ∉ N) :
    Nat.card ↥(N ⊔ Subgroup.zpowers g) = 2 * Nat.card ↥N := by
  set M := N ⊔ Subgroup.zpowers g with hM
  have hgM : g ∈ M := Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
  have hmul : (↑M : Set G) = (N : Set G) * (Subgroup.zpowers g : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left N _ (Subgroup.zpowers_le.mpr hn)
  have hsq' : g ^ 2 ∈ N := by simpa [sq] using hsq
  have key : ∀ x ∈ M, x ∈ N ∨ x * g ∈ N := by
    intro x hx
    rw [← SetLike.mem_coe, hmul] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    beta_reduce
    have hk : g ^ k = (g ^ 2) ^ (k / 2) * g ^ (k % 2) := by
      rw [← zpow_natCast, ← zpow_mul, ← zpow_add]
      congr 1
      push_cast
      omega
    have hN2 : (g ^ 2) ^ (k / 2) ∈ N := Subgroup.zpow_mem _ hsq' _
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left
      rw [hk, h0, zpow_zero, mul_one]
      exact N.mul_mem ha hN2
    · right
      have : a * g ^ k * g = a * (g ^ 2) ^ (k / 2) * g ^ 2 := by
        rw [hk, h1, zpow_one]
        simp only [sq, mul_assoc]
      rw [this]
      exact N.mul_mem (N.mul_mem ha hN2) hsq'
  have h2 : N.relIndex M = 2 := by
    rw [Subgroup.relIndex_eq_two_iff]
    refine ⟨g, hgM, fun b hb => ?_⟩
    rcases key b hb with h | h
    · right
      exact ⟨h, fun hbg => hg (by simpa using N.mul_mem (N.inv_mem h) hbg)⟩
    · left
      exact ⟨h, fun hbN => hg (by simpa using N.mul_mem (N.inv_mem hbN) h)⟩
  have h3 := Subgroup.relIndex_mul_card N M
  rw [inf_eq_left.mpr le_sup_left, h2] at h3
  exact h3.symm

private theorem mem_normalizer_closure {G : Type*} [Group G] [Finite G] {s : Set G} {g : G}
    (h : ∀ x ∈ s, g * x * g⁻¹ ∈ Subgroup.closure s) :
    g ∈ Subgroup.normalizer ((Subgroup.closure s : Subgroup G) : Set G) := by
  have hle : (Subgroup.closure s).map (MulAut.conj g).toMonoidHom ≤ Subgroup.closure s := by
    rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    intro x hx
    exact h x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge

private theorem closure_cons {G : Type*} [Group G] (g : G) (l : List G) :
    Subgroup.closure {x | x ∈ g :: l} =
      Subgroup.zpowers g ⊔ Subgroup.closure {x | x ∈ l} := by
  have : {x | x ∈ g :: l} = {g} ∪ {x | x ∈ l} := by
    ext x
    simp
  rw [this, Subgroup.closure_union, Subgroup.zpowers_eq_closure]

private theorem card_closure_cons {G : Type*} [Group G] [Finite G] {g : G} {l : List G}
    (hn : ∀ x ∈ l, g * x * g⁻¹ ∈ Subgroup.closure {x | x ∈ l})
    (hsq : g * g ∈ Subgroup.closure {x | x ∈ l}) (hg : g ∉ Subgroup.closure {x | x ∈ l}) :
    Nat.card ↥(Subgroup.closure {x | x ∈ g :: l}) =
      2 * Nat.card ↥(Subgroup.closure {x | x ∈ l}) := by
  rw [closure_cons, sup_comm]
  exact card_sup_zpowers_of_sq_mem (mem_normalizer_closure hn) hsq hg

private theorem not_mem_closure_of_invariant {α : Type*} [DecidableEq α]
    (l : List (Equiv.Perm α)) (O : List α)
    (h : (l.all fun g => O.all fun x => decide (g x ∈ O)) = true)
    (h' : (l.all fun g => O.all fun x => decide (g⁻¹ x ∈ O)) = true) {p : α} (hp : p ∈ O)
    {y : Equiv.Perm α} (hy : y p ∉ O) : y ∉ Subgroup.closure {g | g ∈ l} := by
  simp only [List.all_eq_true, decide_eq_true_eq] at h h'
  intro hmem
  have key : ∀ x ∈ Subgroup.closure {g | g ∈ l}, ∀ q ∈ O, x q ∈ O ∧ x⁻¹ q ∈ O := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact fun q hq => ⟨h x hx q hq, h' x hx q hq⟩
    | one => intro q hq; simpa using hq
    | mul x y _ _ ihx ihy =>
      intro q hq
      refine ⟨?_, ?_⟩
      · simpa using (ihx _ (ihy q hq).1).1
      · simpa using (ihy _ (ihx q hq).2).2
    | inv x _ ih => exact fun q hq => ⟨(ih q hq).2, by simpa using (ih q hq).1⟩
  exact hy (key y hmem p hp).1

private theorem gen_mem {l : List P45} {x : P45} (h : x ∈ l) :
    x ∈ Subgroup.closure {y | y ∈ l} := Subgroup.subset_closure h

private theorem c_beta1_alpha1 : beta1 * alpha1 * beta1⁻¹ = alpha1⁻¹ := by decide +kernel
private theorem c_alpha2_alpha1 : alpha2 * alpha1 * alpha2⁻¹ = alpha1 := by decide +kernel
private theorem c_alpha2_beta1 : alpha2 * beta1 * alpha2⁻¹ = beta1 := by decide +kernel
private theorem c_beta2_alpha1 : beta2 * alpha1 * beta2⁻¹ = alpha1 := by decide +kernel
private theorem c_beta2_beta1 : beta2 * beta1 * beta2⁻¹ = beta1 := by decide +kernel
private theorem c_beta2_alpha2 : beta2 * alpha2 * beta2⁻¹ = alpha2⁻¹ := by decide +kernel
private theorem c_u_alpha1 : u * alpha1 * u⁻¹ = alpha2 := by decide +kernel
private theorem c_u_beta1 : u * beta1 * u⁻¹ = beta2 := by decide +kernel
private theorem c_u_alpha2 : u * alpha2 * u⁻¹ = alpha1 := by decide +kernel
private theorem c_u_beta2 : u * beta2 * u⁻¹ = beta1 := by decide +kernel
private theorem c_v_alpha1 : v * alpha1 * v⁻¹ = alpha1⁻¹ := by decide +kernel
private theorem c_v_beta1 : v * beta1 * v⁻¹ = alpha1 * beta1 := by decide +kernel
private theorem c_v_alpha2 : v * alpha2 * v⁻¹ = alpha2⁻¹ := by decide +kernel
private theorem c_v_beta2 : v * beta2 * v⁻¹ = alpha2 * beta2 := by decide +kernel
private theorem c_v_u : v * u * v⁻¹ = u := by decide +kernel

private theorem sq_beta1 : beta1 * beta1 = alpha1 * alpha1 := by decide +kernel
private theorem sq_alpha2 : alpha2 * alpha2 = alpha1 * alpha1 := by decide +kernel
private theorem sq_beta2 : beta2 * beta2 = alpha1 * alpha1 := by decide +kernel
private theorem sq_u : u * u = 1 := by decide +kernel
private theorem sq_v : v * v = 1 := by decide +kernel
private theorem sq_alpha1_ne_one : ¬ alpha1 ^ 2 = 1 := by decide +kernel
private theorem pow4_alpha1 : alpha1 ^ 4 = 1 := by decide +kernel

private theorem card_cl_alpha1 :
    Nat.card ↥(Subgroup.closure {x | x ∈ [alpha1]}) = 4 := by
  have h : {x | x ∈ [alpha1]} = ({alpha1} : Set P45) := by
    ext x
    simp
  rw [h, ← Subgroup.zpowers_eq_closure, Nat.card_zpowers]
  have h4 : orderOf alpha1 = 2 ^ (1 + 1) :=
    orderOf_eq_prime_pow (p := 2) (n := 1) (x := alpha1)
      sq_alpha1_ne_one (by simpa using pow4_alpha1)
  simpa using h4

private def O1 : List (Fin 45) := [1, 2, 9, 12]

private theorem orb1_fwd : ([alpha1].all fun g => O1.all fun x => decide (g x ∈ O1)) = true := by
  decide +kernel

private theorem orb1_bwd :
    ([alpha1].all fun g => O1.all fun x => decide (g⁻¹ x ∈ O1)) = true := by
  decide +kernel

private theorem orb1_sep : beta1 1 ∉ O1 := by decide +kernel

private theorem card_cl_beta1 :
    Nat.card ↥(Subgroup.closure {x | x ∈ [beta1, alpha1]}) = 8 := by
  have h := card_closure_cons (g := beta1) (l := [alpha1]) ?_ ?_ ?_
  · rw [h, card_cl_alpha1]
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    rw [c_beta1_alpha1]
    exact Subgroup.inv_mem _ (gen_mem (by simp))
  · rw [sq_beta1]
    exact Subgroup.mul_mem _ (gen_mem (by simp)) (gen_mem (by simp))
  · exact not_mem_closure_of_invariant [alpha1] O1 orb1_fwd orb1_bwd (p := 1) (by decide)
      orb1_sep

private def O2 : List (Fin 45) := [1, 2, 9, 10, 11, 12, 13, 14]

private theorem orb2_fwd :
    ([beta1, alpha1].all fun g => O2.all fun x => decide (g x ∈ O2)) = true := by
  decide +kernel

private theorem orb2_bwd :
    ([beta1, alpha1].all fun g => O2.all fun x => decide (g⁻¹ x ∈ O2)) = true := by
  decide +kernel

private theorem orb2_sep : alpha2 1 ∉ O2 := by decide +kernel

private theorem card_cl_alpha2 :
    Nat.card ↥(Subgroup.closure {x | x ∈ [alpha2, beta1, alpha1]}) = 16 := by
  have h := card_closure_cons (g := alpha2) (l := [beta1, alpha1]) ?_ ?_ ?_
  · rw [h, card_cl_beta1]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · rw [c_alpha2_beta1]
      exact gen_mem (by simp)
    · rw [c_alpha2_alpha1]
      exact gen_mem (by simp)
  · rw [sq_alpha2]
    exact Subgroup.mul_mem _ (gen_mem (by simp)) (gen_mem (by simp))
  · exact not_mem_closure_of_invariant [beta1, alpha1] O2 orb2_fwd orb2_bwd (p := 1)
      (by decide) orb2_sep

private def O3 : List (Fin 45) := [1, 2, 3, 6, 9, 10, 11, 12, 13, 14, 21, 23, 28, 32, 37, 39]

private theorem orb3_fwd :
    ([alpha2, beta1, alpha1].all fun g => O3.all fun x => decide (g x ∈ O3)) = true := by
  decide +kernel

private theorem orb3_bwd :
    ([alpha2, beta1, alpha1].all fun g => O3.all fun x => decide (g⁻¹ x ∈ O3)) = true := by
  decide +kernel

private theorem orb3_sep : beta2 1 ∉ O3 := by decide +kernel

private theorem card_cl_beta2 :
    Nat.card ↥(Subgroup.closure {x | x ∈ [beta2, alpha2, beta1, alpha1]}) = 32 := by
  have h := card_closure_cons (g := beta2) (l := [alpha2, beta1, alpha1]) ?_ ?_ ?_
  · rw [h, card_cl_alpha2]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [c_beta2_alpha2]
      exact Subgroup.inv_mem _ (gen_mem (by simp))
    · rw [c_beta2_beta1]
      exact gen_mem (by simp)
    · rw [c_beta2_alpha1]
      exact gen_mem (by simp)
  · rw [sq_beta2]
    exact Subgroup.mul_mem _ (gen_mem (by simp)) (gen_mem (by simp))
  · exact not_mem_closure_of_invariant [alpha2, beta1, alpha1] O3 orb3_fwd orb3_bwd (p := 1)
      (by decide) orb3_sep

private def O4 : List (Fin 45) := [25, 26, 30, 34]

private theorem orb4_fwd :
    ([beta2, alpha2, beta1, alpha1].all fun g => O4.all fun x => decide (g x ∈ O4)) = true := by
  decide +kernel

private theorem orb4_bwd :
    ([beta2, alpha2, beta1, alpha1].all fun g => O4.all fun x => decide (g⁻¹ x ∈ O4)) = true := by
  decide +kernel

private theorem orb4_sep : u 25 ∉ O4 := by decide +kernel

private theorem card_cl_u :
    Nat.card ↥(Subgroup.closure {x | x ∈ [u, beta2, alpha2, beta1, alpha1]}) = 64 := by
  have h := card_closure_cons (g := u) (l := [beta2, alpha2, beta1, alpha1]) ?_ ?_ ?_
  · rw [h, card_cl_beta2]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · rw [c_u_beta2]
      exact gen_mem (by simp)
    · rw [c_u_alpha2]
      exact gen_mem (by simp)
    · rw [c_u_beta1]
      exact gen_mem (by simp)
    · rw [c_u_alpha1]
      exact gen_mem (by simp)
  · rw [sq_u]
    exact Subgroup.one_mem _
  · exact not_mem_closure_of_invariant [beta2, alpha2, beta1, alpha1] O4 orb4_fwd orb4_bwd
      (p := 25) (by decide) orb4_sep

section Certified

private theorem card_cl_v :
    Nat.card ↥(Subgroup.closure {x | x ∈ [v, u, beta2, alpha2, beta1, alpha1]}) = 128 := by
  have h := card_closure_cons (g := v) (l := [u, beta2, alpha2, beta1, alpha1]) ?_ ?_ ?_
  · rw [h, card_cl_u]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · rw [c_v_u]
      exact gen_mem (by simp)
    · rw [c_v_beta2]
      exact Subgroup.mul_mem _ (gen_mem (by simp)) (gen_mem (by simp))
    · rw [c_v_alpha2]
      exact Subgroup.inv_mem _ (gen_mem (by simp))
    · rw [c_v_beta1]
      exact Subgroup.mul_mem _ (gen_mem (by simp)) (gen_mem (by simp))
    · rw [c_v_alpha1]
      exact Subgroup.inv_mem _ (gen_mem (by simp))
  · rw [sq_v]
    exact Subgroup.one_mem _
  · intro hv
    refine v_not_mem_Q ((Subgroup.closure_le (K := QP45.originalSubgroup)).mpr ?_ hv)
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact u_mem_Q
    · exact beta2_mem_Q
    · exact alpha2_mem_Q
    · exact beta1_mem_Q
    · exact alpha1_mem_Q

end Certified

private theorem card_comap_eq {G A : Type*} [Group G] [Group A] (f : G →* A)
    (hf : Function.Surjective f) (S : Subgroup A) :
    Nat.card ↥(S.comap f) = Nat.card ↥f.ker * Nat.card ↥S := by
  have hsurj := MonoidHom.subgroupComap_surjective f S hf
  have h1 := Subgroup.card_ker_mul_card_of_surjective hsurj
  have hle : f.ker ≤ S.comap f := fun x hx => by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
    exact S.one_mem
  have hker : (f.subgroupComap S).ker = f.ker.subgroupOf (S.comap f) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact ⟨fun hx => congrArg Subtype.val hx, fun hx => Subtype.ext hx⟩
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h1
  exact h1.symm

end SylowHAux

open SylowHAux

section Model

@[expose] noncomputable def sylowTwoQA45 : Subgroup ↥QA45.originalSubgroup :=
  Subgroup.closure {⟨u, u_mem_A⟩, ⟨v, v_mem_A⟩, ⟨alpha1, alpha1_mem_A⟩, ⟨beta1, beta1_mem_A⟩,
    ⟨alpha2, alpha2_mem_A⟩, ⟨beta2, beta2_mem_A⟩}

private theorem image_gens_eq :
    QA45.originalSubgroup.subtype '' ({⟨u, u_mem_A⟩, ⟨v, v_mem_A⟩, ⟨alpha1, alpha1_mem_A⟩,
      ⟨beta1, beta1_mem_A⟩, ⟨alpha2, alpha2_mem_A⟩, ⟨beta2, beta2_mem_A⟩} :
        Set ↥QA45.originalSubgroup) = {x | x ∈ [v, u, beta2, alpha2, beta1, alpha1]} := by
  ext x
  simp only [Set.image_insert_eq, Set.image_singleton, Subgroup.coe_subtype, Set.mem_insert_iff,
    Set.mem_singleton_iff, List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq]
  constructor
  · rintro (h | h | h | h | h | h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inl h))
  · rintro (h | h | h | h | h | h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inl h))

theorem card_sylowTwoQA45 : Nat.card ↥sylowTwoQA45 = 2 ^ 7 := by
  have hmap : sylowTwoQA45.map QA45.originalSubgroup.subtype =
      Subgroup.closure {x | x ∈ [v, u, beta2, alpha2, beta1, alpha1]} := by
    rw [sylowTwoQA45, MonoidHom.map_closure, image_gens_eq]
  have h1 := Subgroup.card_map_of_injective (K := sylowTwoQA45)
    (f := QA45.originalSubgroup.subtype) (Subgroup.subtype_injective _)
  rw [hmap, card_cl_v] at h1
  rw [← h1]
  norm_num

theorem index_sylowTwoQA45 : sylowTwoQA45.index = 3 ^ 4 * 5 := by
  rw [Subgroup.index_eq_card_div, card_QA45, card_sylowTwoQA45]
  norm_num

theorem isPGroup_sylowTwoQA45 : IsPGroup 2 sylowTwoQA45 :=
  IsPGroup.of_card card_sylowTwoQA45

theorem isSylow_sylowTwoQA45 :
    ∃ P : Sylow 2 ↥QA45.originalSubgroup,
      (P : Subgroup ↥QA45.originalSubgroup) = sylowTwoQA45 :=
  ⟨isPGroup_sylowTwoQA45.toSylow (by rw [index_sylowTwoQA45]; norm_num),
    IsPGroup.toSylow_coe _ _⟩

end Model

section Lifted

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

@[expose] noncomputable def sylowTwoH : Subgroup ↥(H z) :=
  (J z).subgroupOf (H z) ⊔ Subgroup.closure {uH D, vH D, a1H D, b1H D, a2H D, b2H D}

theorem sylowTwoH_eq_comap : sylowTwoH D = sylowTwoQA45.comap (qH D) := by
  have hmap : (Subgroup.closure {uH D, vH D, a1H D, b1H D, a2H D, b2H D}).map (qH D) =
      sylowTwoQA45 := by
    rw [MonoidHom.map_closure, sylowTwoQA45]
    simp only [Set.image_insert_eq, Set.image_singleton, qH_uH, qH_vH, qH_a1H, qH_b1H, qH_a2H,
      qH_b2H]
  rw [sylowTwoH, ← hmap, Subgroup.comap_map_eq, ker_qH, sup_comm]

theorem index_sylowTwoH : (sylowTwoH D).index = 3 ^ 4 * 5 := by
  rw [sylowTwoH_eq_comap, Subgroup.index_comap_of_surjective _ (qH_surjective D),
    index_sylowTwoQA45]

theorem card_sylowTwoH (h : Tim79a.ParrottHyp z) : Nat.card ↥(sylowTwoH D) = 2 ^ 17 := by
  have hJ : Nat.card ↥(qH D).ker = 2 ^ 10 := by
    rw [ker_qH, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (J_le_H (z := z))).toEquiv,
      card_J h]
  rw [sylowTwoH_eq_comap, card_comap_eq _ (qH_surjective D), hJ, card_sylowTwoQA45]
  norm_num

theorem isPGroup_sylowTwoH (h : Tim79a.ParrottHyp z) : IsPGroup 2 (sylowTwoH D) :=
  IsPGroup.of_card (card_sylowTwoH D h)

theorem isSylow_sylowTwoH (h : Tim79a.ParrottHyp z) :
    ∃ S : Sylow 2 ↥(H z), (S : Subgroup ↥(H z)) = sylowTwoH D :=
  ⟨(isPGroup_sylowTwoH D h).toSylow (by rw [index_sylowTwoH]; norm_num),
    IsPGroup.toSylow_coe _ _⟩

end Lifted

end CFSG.RankThree.GF2n.Parrott
