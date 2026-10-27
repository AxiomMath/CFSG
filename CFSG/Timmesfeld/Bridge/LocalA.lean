module

public import CFSG.Timmesfeld.Closure.Reduction
public import CFSG.Timmesfeld.Moufang.Criterion

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Closure

variable {G : Type*} [Group G] {D : Set G}

theorem commute_of_mem_rootSet_pair (hD : IsRootInvolutionSet D) {d a b : G} (hd : d ∈ D)
    (ha : a ∈ rootSet D d) (hb : b ∈ rootSet D d) :
    Commute a b ∧ a * b * (a * b) = 1 := by
  have hab : Commute a b := (ha.2 b hb.1).2 ((hb.2 d hd).2 (Commute.refl d)).symm
  refine ⟨hab, ?_⟩
  calc a * b * (a * b) = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [hab.eq]
    _ = (a * a) * (b * b) := by group
    _ = 1 := by rw [hD.mul_self_eq_one ha.1, hD.mul_self_eq_one hb.1, one_mul]

theorem mem_rootSet_of_mem_rootSet_pair {d a b : G} (ha : a ∈ rootSet D d)
    (hb : b ∈ rootSet D d) : b ∈ rootSet D a := by
  rw [rootSet_eq_of_mem ha]
  exact hb

theorem not_opposite_of_commute_mul (hD : IsRootInvolutionSet D) {d a b : G} (hd : d ∈ D)
    (ha : a ∈ rootSet D d) (hb : b ∈ rootSet D d) (hab : a ≠ b) {e : G} (he : e ∈ D)
    (heu : Commute e (a * b)) : ¬ (¬ Commute d e ∧ Odd (orderOf (d * e))) := by
  rintro ⟨hnc, ho⟩
  obtain ⟨hoa, -⟩ := odd_orderOf_mul_of_mem_rootSet hD hd he ha (mem_rootSet_self he) ho hnc
  obtain ⟨hob, -⟩ := odd_orderOf_mul_of_mem_rootSet hD hd he hb (mem_rootSet_self he) ho hnc
  rw [orderOf_mul_comm_eq] at hoa hob
  exact hab (eq_of_commute_mul_of_odd (hD.mul_self_eq_one ha.1) (hD.mul_self_eq_one hb.1)
    (hD.mul_self_eq_one he) hoa hob heu)

theorem opposite_of_mem_rootSet_pair (hD : IsRootInvolutionSet D) {d a c : G} (hd : d ∈ D)
    (ha : a ∈ rootSet D d) (hc : c ∈ D) (hdc : ¬ Commute d c) (hodd : Odd (orderOf (d * c))) :
    ¬ Commute a c ∧ Odd (orderOf (a * c)) := by
  obtain ⟨h1, h2⟩ := odd_orderOf_mul_of_mem_rootSet hD hd hc ha (mem_rootSet_self hc) hodd hdc
  exact ⟨h2, h1⟩

theorem mul_conj_eq_sq (hD : IsRootInvolutionSet D) {d a b : G} (hd : d ∈ D) (ha : a ∈ rootSet D d)
    (hb : b ∈ rootSet D d) (c : G) :
    c * (a * b * c * (a * b)⁻¹) = (c * (a * b)) ^ 2 := by
  rw [inv_eq_of_mul_eq_one_right (commute_of_mem_rootSet_pair hD hd ha hb).2, pow_two]
  group

theorem orderOf_mul_cases (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {d a b c : G} (hd : d ∈ D) (ha : a ∈ rootSet D d)
    (hb : b ∈ rootSet D d) (hc : c ∈ D) :
    (Odd (orderOf (c * (a * b))) ∨ ∃ m, Odd m ∧ orderOf (c * (a * b)) = 2 * m) ∨
      orderOf (c * (a * b)) = 4 ∨ orderOf (c * (a * b)) = 8 := by
  have hc' : a * b * c * (a * b)⁻¹ ∈ D := conj_mem_of_isClass hclass (a * b) hc
  have hrel := hD.orderOf_mul hc hc'
  rw [mul_conj_eq_sq hD hd ha hb c, orderOf_pow' _ two_ne_zero] at hrel
  rcases Nat.even_or_odd (orderOf (c * (a * b))) with ⟨k, hk⟩ | h
  · rw [hk] at hrel ⊢
    have hgcd : Nat.gcd (k + k) 2 = 2 := by
      rw [← two_mul]
      exact Nat.gcd_mul_right_left k 2
    rw [hgcd, ← two_mul, Nat.mul_div_cancel_left _ two_pos] at hrel
    rcases hrel with h | h | h
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr (by omega))
    · exact Or.inl (Or.inr ⟨k, h, by omega⟩)
  · exact Or.inl (Or.inl h)

theorem mem_of_twoOdd (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D)
    {d a b c : G} (hd : d ∈ D) (ha : a ∈ rootSet D d) (hb : b ∈ rootSet D d) (hc : c ∈ D)
    (hab : a ≠ b) {m : ℕ} (hm : Odd m) (hcu : orderOf (c * (a * b)) = 2 * m) :
    a * b * (c * (a * b)) ^ m ∈ D ∧ Commute (a * b * (c * (a * b)) ^ m) (a * b) ∧
      ¬ (¬ Commute d (a * b * (c * (a * b)) ^ m) ∧
        Odd (orderOf (d * (a * b * (c * (a * b)) ^ m)))) := by
  have hu2 := (commute_of_mem_rootSet_pair hD hd ha hb).2
  obtain ⟨-, hzu, h, -, hh⟩ := third_kind (hD.mul_self_eq_one hc) hu2 hm hcu
  have heD : a * b * (c * (a * b)) ^ m ∈ D := by
    rw [← hh]
    exact conj_mem_of_isClass hclass h hc
  have heu : Commute (a * b * (c * (a * b)) ^ m) (a * b) := (Commute.refl _).mul_left hzu
  exact ⟨heD, heu, not_opposite_of_commute_mul hD hd ha hb hab heD heu⟩

theorem special_config (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D)
    {d a b c : G} (hd : d ∈ D) (ha : a ∈ rootSet D d) (hb : b ∈ rootSet D d) (hc : c ∈ D)
    (hdc : ¬ Commute d c) (hodd : Odd (orderOf (d * c))) (hab : a ≠ b) {w : G} (hw : w ∈ D)
    (hcw : Commute c w) (hcwD : c * w ∈ D) (hwu : Commute w (a * b)) :
    orderOf (w * a) = 4 ∧ orderOf (w * b) = 4 ∧ (w * a) ^ 2 = (w * b) ^ 2 ∧
      (w * a) ^ 2 ∈ D ∧ Commute ((w * a) ^ 2) a ∧ Commute ((w * a) ^ 2) b ∧
        Commute ((w * a) ^ 2) w ∧ orderOf ((w * a) ^ 2 * c) = 4 := by
  have ha' := ha.1
  have hb' := hb.1
  have ha2 := hD.mul_self_eq_one ha'
  have hb2 := hD.mul_self_eq_one hb'
  have hw2 := hD.mul_self_eq_one hw
  have hbA := mem_rootSet_of_mem_rootSet_pair ha hb
  obtain ⟨hac, hoac⟩ := opposite_of_mem_rootSet_pair hD hd ha hc hdc hodd
  have hoca : Odd (orderOf (c * a)) := by rwa [orderOf_mul_comm_eq]
  have haw : ¬ Commute a w := fun h => by
    have h1 := Moufang.eq_of_collinear_of_odd hD hw hcw hcwD ha' h hoac
    have : a = c := (mul_eq_one_iff_eq_inv.1 h1).trans (hD.inv_eq hc)
    exact hac (this ▸ Commute.refl a)
  have h4 : orderOf (w * a) = 4 := by
    rcases hD.orderOf_mul hw ha' with h | h | h
    · exfalso
      apply haw
      exact ((commute_iff_mul_sq_eq_one hw2 ha2).2 (by rw [← h, pow_orderOf_eq_one])).symm
    · exact h
    · exfalso
      have hwb : Odd (orderOf (w * b)) := by
        rw [orderOf_mul_comm_eq] at h ⊢
        exact (odd_orderOf_mul_iff_of_mem_rootSet hD ha' hbA hw haw).2 h
      exact hab (eq_of_commute_mul_of_odd ha2 hb2 hw2 h hwb hwu)
  have h4b : orderOf (w * b) = 4 := by
    rw [orderOf_mul_comm_eq] at h4 ⊢
    exact (orderOf_mul_eq_four_iff_of_mem_rootSet hD ha' hbA hw).2 h4
  have hsq : (w * a) ^ 2 = (w * b) ^ 2 := by
    have hmul := commutatorElement_mul_of_mem_rootGroup hclass hD hw ha' h4 (mem_rootSet_self hw)
      (rootSet_subset_rootGroup D a (mem_rootSet_self ha'))
      (rootSet_subset_rootGroup D a hbA)
    rw [commutatorElement_eq_one_iff_mul_comm.2 hwu.eq,
      Special.commutatorElement_eq_mul_sq hw2 ha2,
      Special.commutatorElement_eq_mul_sq hw2 hb2] at hmul
    have hinv : ((w * b) ^ 2)⁻¹ = (w * b) ^ 2 := by
      rw [inv_eq_iff_mul_eq_one, ← pow_add, show 2 + 2 = 4 from rfl, ← h4b, pow_orderOf_eq_one]
    rw [← hinv]
    exact eq_inv_of_mul_eq_one_left hmul.symm
  obtain ⟨hpD, hwp, hap, hawa⟩ := sq_mem_of_orderOf_eq_four hD hw ha' h4
  obtain ⟨-, -, hbp, -⟩ := sq_mem_of_orderOf_eq_four hD hw hb' h4b
  rw [← hsq] at hbp
  set p := (w * a) ^ 2 with hp
  have hap' : a * p ∈ D := by
    have h4' : orderOf (a * w) = 4 := by rwa [orderOf_mul_comm_eq]
    obtain ⟨-, -, -, hwaw⟩ := sq_mem_of_orderOf_eq_four hD ha' hw h4'
    have hsq' : (a * w) ^ 2 = p := by
      have hinv : a * w = (w * a)⁻¹ := by rw [mul_inv_rev, hD.inv_eq ha', hD.inv_eq hw]
      rw [hinv, inv_pow, hp]
      exact inv_eq_of_mul_eq_one_right (by
        rw [← pow_add, show 2 + 2 = 4 from rfl, ← h4, pow_orderOf_eq_one])
    rw [← hsq', ← hwaw]
    have := conj_mem_of_isClass hclass w ha'
    rwa [hD.inv_eq hw] at this
  have hwpD : p * w ∈ D := by
    rw [← hwp.eq, ← hawa]
    have := conj_mem_of_isClass hclass a hw
    rwa [hD.inv_eq ha'] at this
  have hpc : ¬ Commute c p := fun h => by
    have h1 := Moufang.eq_of_collinear_of_odd hD hpD hap hap' hc h hoca
    have : c = a := (mul_eq_one_iff_eq_inv.1 h1).trans (hD.inv_eq ha')
    exact hac (this ▸ Commute.refl c)
  have hpc' : ¬ Odd (orderOf (c * p)) := fun h => by
    have h1 := Moufang.eq_of_collinear_of_odd hD hw hwp.symm hwpD hc hcw h
    have : c = p := (mul_eq_one_iff_eq_inv.1 h1).trans (hD.inv_eq hpD)
    exact hpc (this ▸ Commute.refl c)
  refine ⟨h4, h4b, hsq, hpD, hap.symm, hbp.symm, hwp.symm, ?_⟩
  rcases hD.orderOf_mul hpD hc with h | h | h
  · exfalso
    exact hpc ((commute_iff_mul_sq_eq_one (hD.mul_self_eq_one hpD) (hD.mul_self_eq_one hc)).2
      (by rw [← h, pow_orderOf_eq_one])).symm
  · exact h
  · exact absurd (by rwa [orderOf_mul_comm_eq] at h) hpc'

theorem special_config_of_eight (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {d a b c : G} (hd : d ∈ D) (ha : a ∈ rootSet D d)
    (hb : b ∈ rootSet D d) (hc : c ∈ D) (h8 : orderOf (c * (a * b)) = 8) :
    (c * (a * b)) ^ 4 ∈ D ∧ Commute c ((c * (a * b)) ^ 4) ∧ c * (c * (a * b)) ^ 4 ∈ D ∧
      Commute ((c * (a * b)) ^ 4) (a * b) := by
  have hc' : a * b * c * (a * b)⁻¹ ∈ D := conj_mem_of_isClass hclass (a * b) hc
  have hcc := mul_conj_eq_sq hD hd ha hb c
  have h4 : orderOf (c * (a * b * c * (a * b)⁻¹)) = 4 := by
    rw [hcc, orderOf_pow' _ two_ne_zero, h8]
    rfl
  obtain ⟨hwD, hcw, -, hcc'⟩ := sq_mem_of_orderOf_eq_four hD hc hc' h4
  have hw : (c * (a * b * c * (a * b)⁻¹)) ^ 2 = (c * (a * b)) ^ 4 := by
    rw [hcc, ← pow_mul]
  rw [hw] at hwD hcw hcc'
  have hc'2 : (a * b * c * (a * b)⁻¹) * (a * b * c * (a * b)⁻¹) = 1 := by
    calc (a * b * c * (a * b)⁻¹) * (a * b * c * (a * b)⁻¹) = a * b * (c * c) * (a * b)⁻¹ := by
          group
      _ = 1 := by rw [hD.mul_self_eq_one hc, mul_one, mul_inv_cancel]
  refine ⟨hwD, hcw, ?_, ?_⟩
  · rw [← hcc']
    have := conj_mem_of_isClass hclass (a * b * c * (a * b)⁻¹) hc
    rwa [inv_eq_of_mul_eq_one_right hc'2] at this
  · have h1 : Commute ((c * (a * b)) ^ 4) (c * (a * b)) := (Commute.self_pow _ 4).symm
    have hu : c * (c * (a * b)) = a * b := by rw [← mul_assoc, hD.mul_self_eq_one hc, one_mul]
    have h2 := hcw.symm.mul_right h1
    rwa [hu] at h2

end CFSG.Timmesfeld.Bridge
