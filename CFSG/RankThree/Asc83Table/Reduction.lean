module

public import CFSG.RankThree.Asc83Table.E9
public import CFSG.RankThree.Asc83Table.Extraspecial
public import CFSG.Foundations.Basic
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.Asc83Table

open Subgroup CFSG.SectionRank.LocalWitness
open scoped commutatorElement

variable {L : Type*} [Group L]

theorem isElementaryAbelian_iff {p : ℕ} {A : Subgroup L} :
    IsElementaryAbelian p A ↔ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ ∀ a ∈ A, a ^ p = 1 := by
  constructor
  · intro h
    refine ⟨fun a ha b hb => ?_, fun a ha => elemPow_eq_one_of_isElementaryAbelian a ha⟩
    have := mul_comm' (⟨a, ha⟩ : A) ⟨b, hb⟩
    exact congrArg Subtype.val this
  · rintro ⟨h₁, h₂⟩
    exact
      { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (h₁ a a.2 b b.2)⟩⟩
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
          Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact h₂ a a.2) }

theorem IsElementaryAbelian.map_hom {L' : Type*} [Group L'] (f : L →* L') {p : ℕ}
    {A : Subgroup L} (h : IsElementaryAbelian p A) : IsElementaryAbelian p (A.map f) :=
  CFSG.IsElementaryAbelian.subgroup_map h _

theorem isPGroup_of_isElementaryAbelian {p : ℕ} [Fact p.Prime] {A : Subgroup L}
    (h : IsElementaryAbelian p A) : IsPGroup p A :=
  IsElementaryAbelian.isPGroup p A

theorem pRank_eq {p k : ℕ} (hp : 1 < p) {E : Subgroup L} (hE : IsElementaryAbelian p E)
    (hEk : Nat.card E = p ^ k)
    (hle : ∀ A : Subgroup L, IsElementaryAbelian p A → Nat.card A ≤ p ^ k) :
    CFSG.pRank p L = k := by
  have hbound : ∀ r ∈ {r : ℕ | ∃ A : Subgroup L, IsElementaryAbelian p A ∧ Nat.card A = p ^ r},
      r ≤ k := by
    rintro r ⟨A, hA, hAr⟩
    have h := hle A hA
    rw [hAr] at h
    exact (Nat.pow_le_pow_iff_right hp).mp h
  have hmem : k ∈ {r : ℕ | ∃ A : Subgroup L, IsElementaryAbelian p A ∧ Nat.card A = p ^ r} :=
    ⟨E, hE, hEk⟩
  exact le_antisymm (csSup_le ⟨k, hmem⟩ hbound) (le_csSup ⟨k, hbound⟩ hmem)

theorem exists_map_conj_le [Finite L] {p : ℕ} [Fact p.Prime] {P : Subgroup L}
    (hP : Nat.card P = p ^ (Nat.card L).factorization p) {B : Subgroup L} (hB : IsPGroup p B) :
    ∃ g : L, B.map (MulAut.conj g).toMonoidHom ≤ P := by
  obtain ⟨Q, hBQ⟩ := hB.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L Q (Sylow.ofCard P hP)
  refine ⟨g, ?_⟩
  have h : ((g • Q : Sylow p L) : Subgroup L) = P := by rw [hg]; rfl
  have h' : ((g • Q : Sylow p L) : Subgroup L) =
      (Q : Subgroup L).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul]
    rfl
  rw [← h, h']
  exact Subgroup.map_mono hBQ

theorem card_map_conj (g : L) (B : Subgroup L) :
    Nat.card (B.map (MulAut.conj g).toMonoidHom) = Nat.card B :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

@[expose] def automizerOfEq {B₁ B₂ : Subgroup L} (h : B₁ = B₂) : Automizer B₁ ≃* Automizer B₂ :=
  h ▸ MulEquiv.refl _

theorem exists_sylow_eq_map [Finite L] {p : ℕ} [Fact p.Prime] {P : Subgroup L}
    (hP : Nat.card P = p ^ (Nat.card L).factorization p) (Q : Sylow p L) :
    ∃ g : L, (Q : Subgroup L) = P.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L (Sylow.ofCard P hP) Q
  refine ⟨g, ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul]
  rfl

section E9

variable [Finite L]

omit [Finite L] in
theorem E9Basis.isElementaryAbelian (E : E9Basis L) : IsElementaryAbelian 3 E.sub := by
  rw [isElementaryAbelian_iff]
  have hcomm : IsMulCommutative E.sub := isMulCommutative_closure (by
    rintro u (rfl | rfl) v (rfl | rfl) -
    · exact Commute.refl _
    · exact E.hab
    · exact E.hab.symm
    · exact Commute.refl _)
  refine ⟨fun a ha b hb => congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : E.sub) ⟨b, hb⟩), ?_⟩
  intro a ha
  rw [← E.closure_range] at ha
  obtain ⟨v, hv⟩ := basisHom_surjective E.vec_pow E.vec_comm ⟨a, ha⟩
  have := congrArg Subtype.val hv
  rw [coe_basisHom, E.basisProd_vec] at this
  change _ = a at this
  rw [← this, (E.hab.pow_pow _ _).mul_pow, ← pow_mul, ← pow_mul, mul_comm, pow_mul, E.ha, one_pow,
    one_mul, mul_comm, pow_mul, E.hb, one_pow]

omit [Finite L] in
theorem e9_card_sylow (E : E9Basis L) (hL : (Nat.card L).factorization 3 = 2) :
    Nat.card E.sub = 3 ^ (Nat.card L).factorization 3 := by
  rw [hL, E.card]
  norm_num

theorem e9_sylow (E : E9Basis L) (hL : (Nat.card L).factorization 3 = 2) (P : Sylow 3 L) :
    IsElementaryAbelian 3 (P : Subgroup L) ∧ Nat.card P = 9 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨g, hg⟩ := exists_sylow_eq_map (e9_card_sylow E hL) P
  refine ⟨hg ▸ IsElementaryAbelian.map_hom _ E.isElementaryAbelian, ?_⟩
  rw [Sylow.card_eq_multiplicity, hL]
  norm_num

theorem e9_pRank (E : E9Basis L) (hL : (Nat.card L).factorization 3 = 2) :
    CFSG.pRank 3 L = 2 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  refine pRank_eq (by norm_num) E.isElementaryAbelian (by rw [E.card]; norm_num) fun A hA => ?_
  obtain ⟨g, hg⟩ := exists_map_conj_le (e9_card_sylow E hL) (isPGroup_of_isElementaryAbelian hA)
  have := Subgroup.card_le_of_le hg
  rw [card_map_conj, E.card] at this
  norm_num
  exact this

theorem e9_automizer (E : E9Basis L) (hL : (Nat.card L).factorization 3 = 2) (B : Subgroup L)
    (hB : Nat.card B = 9) :
    Nonempty (Automizer B ≃* Automizer E.sub) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hp : IsPGroup 3 B := IsPGroup.of_card (n := 2) (by rw [hB]; norm_num)
  obtain ⟨g, hg⟩ := exists_map_conj_le (e9_card_sylow E hL) hp
  have heq : B.map (MulAut.conj g).toMonoidHom = E.sub :=
    Subgroup.eq_of_le_of_card_ge hg (by rw [card_map_conj, hB, E.card])
  exact ⟨(automizerCongr (MulAut.conj g) B).trans (automizerOfEq heq)⟩

end E9

section Ex27

variable [Finite L] {x y : L} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hzx : Commute ⁅x, y⁆ x)
  (hzy : Commute ⁅x, y⁆ y) (hz1 : ⁅x, y⁆ ≠ 1)
include hx hy hzx hzy hz1

theorem ex27_card : Nat.card (closure ({x, y} : Set L)) = 27 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set P := closure ({x, y} : Set L)
  have hp : IsPGroup 3 P := by
    intro g
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact pow_three_eq_one_of_mem hx hzx hzy hy g.2
  obtain ⟨m, hm⟩ := hp.exists_card_eq
  have hle : Nat.card P ≤ 27 := by
    have hxP : x ∈ P := subset_closure (by simp)
    have hyP : y ∈ P := subset_closure (by simp)
    have hzP : ⁅x, y⁆ ∈ P := by
      rw [commutatorElement_def]
      exact P.mul_mem (P.mul_mem (P.mul_mem hxP hyP) (P.inv_mem hxP)) (P.inv_mem hyP)
    let F : Fin 3 × Fin 3 × Fin 3 → P := fun t =>
      ⟨x ^ (t.1 : ℕ) * y ^ (t.2.1 : ℕ) * ⁅x, y⁆ ^ (t.2.2 : ℕ),
        P.mul_mem (P.mul_mem (P.pow_mem hxP _) (P.pow_mem hyP _)) (P.pow_mem hzP _)⟩
    have hF : Function.Surjective F := fun g => by
      obtain ⟨i, j, k, hi, hj, hk, hg⟩ := mem_closure_normalForm (by norm_num) hx hy hzx hzy g.2
      exact ⟨(⟨i, hi⟩, ⟨j, hj⟩, ⟨k, hk⟩), Subtype.ext hg.symm⟩
    have := Nat.card_le_card_of_surjective F hF
    simpa using this
  have hm3 : m ≤ 3 := by
    by_contra h
    push Not at h
    have : 3 ^ 4 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) h
    rw [← hm] at this
    omega
  have hxP : x ∈ P := subset_closure (by simp)
  have hyP : y ∈ P := subset_closure (by simp)
  have key : m ≤ 2 → (⟨x, hxP⟩ : P) * ⟨y, hyP⟩ = ⟨y, hyP⟩ * ⟨x, hxP⟩ := by
    intro h2
    interval_cases m
    · have : Subsingleton P := by
        rw [pow_zero] at hm
        exact (Nat.card_eq_one_iff_unique.mp hm).1
      exact Subsingleton.elim _ _
    · have : IsCyclic P := isCyclic_of_prime_card (p := 3) (by rw [hm]; norm_num)
      let _ := IsCyclic.commGroup (α := P)
      exact mul_comm _ _
    · have := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hm
      exact mul_comm' _ _
  rw [hm]
  by_contra hne
  have h2 : m ≤ 2 := by
    rcases Nat.lt_or_ge m 3 with h | h
    · omega
    · exact absurd (by rw [show m = 3 by omega]; norm_num) hne
  apply hz1
  rw [commutatorElement_eq_one_iff_mul_comm]
  exact congrArg Subtype.val (key h2)

@[expose] def ex27Rep (x y : L) (i : Fin 4) : L := ![x, y, x * y, x * y ^ 2] i

omit [Finite L] hx hy hzx hzy hz1 in
theorem ex27Rep_eq (i : Fin 4) : ∃ a b : ℕ, a < 3 ∧ b < 3 ∧ ¬ (a = 0 ∧ b = 0) ∧
    ex27Rep x y i = x ^ a * y ^ b := by
  fin_cases i
  · exact ⟨1, 0, by norm_num, by norm_num, by simp, by simp [ex27Rep]⟩
  · exact ⟨0, 1, by norm_num, by norm_num, by simp, by simp [ex27Rep]⟩
  · exact ⟨1, 1, by norm_num, by norm_num, by simp, by simp [ex27Rep]⟩
  · exact ⟨1, 2, by norm_num, by norm_num, by simp, by simp [ex27Rep]⟩

theorem ex27_card_rep (i : Fin 4) :
    Nat.card (closure ({⁅x, y⁆, ex27Rep x y i} : Set L)) = 9 := by
  obtain ⟨a, b, ha, hb, hab, hw⟩ := ex27Rep_eq (x := x) (y := y) i
  rw [hw]
  have hcard := ex27_card hx hy hzx hzy hz1
  refine card_closure_pair_eq_nine (commutator_pow_three hx hzx)
    (cube_x_pow_mul_y_pow_eq_one hx hzx hzy hy a b)
    ((hzx.pow_right a).mul_right (hzy.pow_right b)) hz1 fun hmem => hab ?_
  exact eq_zero_of_mem_zpowers hx hy hzx hzy hcard ha hb hmem

@[expose] noncomputable def ex27Basis (i : Fin 4) : E9Basis L where
  a := ⁅x, y⁆
  b := ex27Rep x y i
  ha := commutator_pow_three hx hzx
  hb := by
    obtain ⟨a, b, -, -, -, hw⟩ := ex27Rep_eq (x := x) (y := y) i
    rw [hw]
    exact cube_x_pow_mul_y_pow_eq_one hx hzx hzy hy a b
  hab := by
    obtain ⟨a, b, -, -, -, hw⟩ := ex27Rep_eq (x := x) (y := y) i
    rw [hw]
    exact (hzx.pow_right a).mul_right (hzy.pow_right b)
  card := ex27_card_rep hx hy hzx hzy hz1 i

variable (hL : (Nat.card L).factorization 3 = 3)
include hL

theorem ex27_card_sylow :
    Nat.card (closure ({x, y} : Set L)) = 3 ^ (Nat.card L).factorization 3 := by
  rw [hL, ex27_card hx hy hzx hzy hz1]
  norm_num

omit hx hy hzx hzy hz1 in
theorem ex27_sylow (P : Sylow 3 L) : Nat.card P = 27 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [Sylow.card_eq_multiplicity, hL]
  norm_num

theorem ex27_pRank : CFSG.pRank 3 L = 2 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set E := ex27Basis hx hy hzx hzy hz1 0
  refine pRank_eq (by norm_num) E.isElementaryAbelian (by rw [E.card]; norm_num) fun A hA => ?_
  obtain ⟨g, hg⟩ := exists_map_conj_le (ex27_card_sylow hx hy hzx hzy hz1 hL)
    (isPGroup_of_isElementaryAbelian hA)
  have hdvd := Subgroup.card_dvd_of_le hg
  rw [card_map_conj, ex27_card hx hy hzx hzy hz1] at hdvd
  have hmem : Nat.card A ∈ Nat.divisors 27 := Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩
  rw [show Nat.divisors 27 = {1, 3, 9, 27} by decide] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h
  · rw [h]; norm_num
  · rw [h]; norm_num
  · rw [h]; norm_num
  · exfalso
    have heq : A.map (MulAut.conj g).toMonoidHom = closure {x, y} :=
      Subgroup.eq_of_le_of_card_ge hg (by rw [card_map_conj, h, ex27_card hx hy hzx hzy hz1])
    have hAc := (isElementaryAbelian_iff.1 (IsElementaryAbelian.map_hom
      (MulAut.conj g).toMonoidHom hA)).1
    rw [heq] at hAc
    apply hz1
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact hAc x (subset_closure (by simp)) y (subset_closure (by simp))

theorem ex27_automizer (B : Subgroup L) (h9 : Nat.card B = 9) :
    ∃ i : Fin 4, Nonempty (Automizer B ≃* Automizer (ex27Basis hx hy hzx hzy hz1 i).sub) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hp : IsPGroup 3 B := IsPGroup.of_card (n := 2) (by rw [h9]; norm_num)
  obtain ⟨g, hg⟩ := exists_map_conj_le (ex27_card_sylow hx hy hzx hzy hz1 hL) hp
  have h9' : Nat.card (B.map (MulAut.conj g).toMonoidHom) = 9 := by rw [card_map_conj, h9]
  have hcases := eq_of_le_of_card_eq_nine hx hy hzx hzy (ex27_card hx hy hzx hzy hz1) hg h9'
  have key : ∀ i : Fin 4, B.map (MulAut.conj g).toMonoidHom =
      closure {⁅x, y⁆, ex27Rep x y i} →
      Nonempty (Automizer B ≃* Automizer (ex27Basis hx hy hzx hzy hz1 i).sub) := by
    intro i hi
    exact ⟨(automizerCongr (MulAut.conj g) B).trans (automizerOfEq hi)⟩
  rcases hcases with h | h | h | h
  · exact ⟨0, key 0 h⟩
  · exact ⟨1, key 1 h⟩
  · exact ⟨2, key 2 h⟩
  · exact ⟨3, key 3 h⟩

end Ex27

theorem factorization_eq_of_eq {n m k p : ℕ} (hp : p.Prime) (h : n = p ^ k * m) (hm : ¬ p ∣ m) :
    n.factorization p = k := by
  have hm0 : m ≠ 0 := fun h0 => hm (h0 ▸ dvd_zero p)
  subst h
  rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hm0, Finsupp.add_apply,
    hp.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hm,
    add_zero]

section TransportE9

variable {N : Type*} [Group N] [Finite N] (E : E9Basis N)
  (hN : (Nat.card N).factorization 3 = 2) {L : Type*} [Group L]
include hN

theorem e9_transport (e : L ≃* N) :
    (∀ P : Sylow 3 L, IsElementaryAbelian 3 (P : Subgroup L) ∧ Nat.card P = 9) ∧
      CFSG.pRank 3 L = 2 ∧
      ∀ B : Subgroup L, Nat.card B = 9 → Nonempty (Automizer B ≃* Automizer E.sub) := by
  have : Finite L := Finite.of_equiv _ e.symm.toEquiv
  have hL : (Nat.card L).factorization 3 = 2 := by rw [Nat.card_congr e.toEquiv, hN]
  set E' := E.map e.symm.toMonoidHom e.symm.injective
  refine ⟨e9_sylow E' hL, e9_pRank E' hL, fun B hB => ?_⟩
  obtain ⟨f⟩ := e9_automizer E' hL B hB
  have hsub : E.sub.map e.symm.toMonoidHom = E'.sub := (E.map_sub _ _).symm
  exact ⟨f.trans ((automizerCongr e.symm E.sub).trans (automizerOfEq hsub)).symm⟩

end TransportE9

section TransportEx27

variable {N : Type*} [Group N] [Finite N] {x y : N} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
  (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y) (hz1 : ⁅x, y⁆ ≠ 1)
  (hN : (Nat.card N).factorization 3 = 3) {L : Type*} [Group L]
include hx hy hzx hzy hz1 hN

theorem ex27_transport (e : L ≃* N) :
    (∀ P : Sylow 3 L, Nat.card P = 27) ∧ CFSG.pRank 3 L = 2 ∧
      ∀ B : Subgroup L, Nat.card B = 9 →
        ∃ i : Fin 4, Nonempty (Automizer B ≃* Automizer (ex27Basis hx hy hzx hzy hz1 i).sub) := by
  have : Finite L := Finite.of_equiv _ e.symm.toEquiv
  have hL : (Nat.card L).factorization 3 = 3 := by rw [Nat.card_congr e.toEquiv, hN]
  set f := e.symm.toMonoidHom
  have hf : Function.Injective f := e.symm.injective
  have hx' : f x ^ 3 = 1 := by rw [← map_pow, hx, map_one]
  have hy' : f y ^ 3 = 1 := by rw [← map_pow, hy, map_one]
  have hzx' : Commute ⁅f x, f y⁆ (f x) := by rw [← map_commutatorElement]; exact hzx.map f
  have hzy' : Commute ⁅f x, f y⁆ (f y) := by rw [← map_commutatorElement]; exact hzy.map f
  have hz1' : ⁅f x, f y⁆ ≠ 1 := by
    rw [← map_commutatorElement]
    exact fun h => hz1 (hf (h.trans (map_one f).symm))
  refine ⟨ex27_sylow hL, ex27_pRank hx' hy' hzx' hzy' hz1' hL, fun B hB => ?_⟩
  obtain ⟨i, ⟨g⟩⟩ := ex27_automizer hx' hy' hzx' hzy' hz1' hL B hB
  refine ⟨i, ⟨g.trans ?_⟩⟩
  have hsub : (ex27Basis hx hy hzx hzy hz1 i).sub.map f =
      (ex27Basis hx' hy' hzx' hzy' hz1' i).sub := by
    change (closure {⁅x, y⁆, ex27Rep x y i}).map f = closure {⁅f x, f y⁆, ex27Rep (f x) (f y) i}
    rw [MonoidHom.map_closure, Set.image_pair, map_commutatorElement]
    congr 3
    fin_cases i <;> simp [ex27Rep]
  exact ((automizerCongr e.symm _).trans (automizerOfEq hsub)).symm

end TransportEx27

end CFSG.RankThree.Asc83Table
