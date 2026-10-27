module

public import CFSG.Timmesfeld.Bridge.RootStructBasic
public import CFSG.Timmesfeld.Bridge.RootStructQD

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G] {D : Set G}

theorem exists_opposite_special_of_mem_twoCore (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hsing : ∀ x ∈ D, rootSet D x = {x})
    (hOD : OppositeDetermines D) {d p : G} (hd : d ∈ D) (hp : p ∈ D)
    (hpQ : p ∈ Moufang.twoCore d) (hpd : p ≠ d) :
    ∃ c ∈ D, ¬ Commute p c ∧ Odd (orderOf (p * c)) ∧ orderOf (c * d) = 4 := by
  set A : G → Set G := fun y => {x | x ∈ D ∧ ¬ Commute y x ∧ Odd (orderOf (y * x))}
  obtain ⟨c, ⟨hc, hpc, hodd⟩, hcd⟩ : ∃ c ∈ A p, c ∉ A d := by
    by_contra! hsub
    obtain ⟨g, rfl⟩ := isConj_iff.mp (isConj_of_isClass hclass hd hp)
    have himage : A (g * d * g⁻¹) = (fun x => g * x * g⁻¹) '' A d := by
      ext y
      constructor
      · rintro ⟨hy, hny, hoy⟩
        refine ⟨g⁻¹ * y * g, ⟨by simpa using conj_mem_of_isClass hclass g⁻¹ hy, ?_, ?_⟩,
          by group⟩
        · rwa [← Commute.conj_iff g, show g * (g⁻¹ * y * g) * g⁻¹ = y by group]
        · rwa [← orderOf_conj_eq g,
            show g * (d * (g⁻¹ * y * g)) * g⁻¹ = g * d * g⁻¹ * y by group]
      · rintro ⟨x, ⟨hx, hnx, hox⟩, rfl⟩
        refine ⟨conj_mem_of_isClass hclass g hx, by rwa [Commute.conj_iff], ?_⟩
        rwa [show g * d * g⁻¹ * (g * x * g⁻¹) = g * (d * x) * g⁻¹ by group, orderOf_conj_eq]
    have hinj : Function.Injective (fun x => g * x * g⁻¹) := fun x y hxy => by simpa using hxy
    have heq : A (g * d * g⁻¹) = A d := Set.eq_of_subset_of_ncard_le hsub
      (by rw [himage, Set.ncard_image_of_injective _ hinj]) (Set.toFinite _)
    have hmem : g * d * g⁻¹ ∈ rootSet D d := hOD d hd _ hp fun x hx => by
      have h := Set.ext_iff.mp heq x
      exact ⟨fun h' => (h.2 ⟨hx, h'⟩).2, fun h' => (h.1 ⟨hx, h'⟩).2⟩
    rw [hsing d hd] at hmem
    exact hpd hmem
  refine ⟨c, hc, hpc, hodd, ?_⟩
  have hcd' : ¬ Commute d c := fun h =>
    not_opposite_of_mem_twoCore_of_commute hD hpQ hc h.symm ⟨hpc, hodd⟩
  rcases commute_or_orderOf_mul_eq_four_or_odd hD hd hc with h | h | ⟨h, h'⟩
  · exact absurd h hcd'
  · rwa [orderOf_mul_comm_eq]
  · exact absurd ⟨hc, h', h⟩ hcd

theorem eq_of_mem_nCore_of_forall_commute (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hsing : ∀ x ∈ D, rootSet D x = {x})
    (hOD : OppositeDetermines D) {d e : G} (hd : d ∈ D) (he : e ∈ D) (heN : e ∈ nCore D d)
    (hcomm : ∀ s ∈ D, s ∈ Moufang.twoCore d → Commute e s) : e = d := by
  by_contra hed
  have heQ := mem_twoCore_of_mem_nCore heN
  obtain ⟨c, hc, hec, hodd, h4⟩ :=
    exists_opposite_special_of_mem_twoCore hclass hD hsing hOD hd he heQ hed
  have hwD : c * d * c ∈ D := by simpa [hD.inv_eq hc] using conj_mem_of_isClass hclass c hd
  exact not_commute_conj_of_odd_special hD he hc hd hec hodd h4
    (Moufang.commute_of_mem_twoCore heQ)
    (hcomm _ hwD (conj_mem_twoCore_of_orderOf_eq_four hclass hD hc hd h4))

theorem eq_of_mem_center_nCore (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hsing : ∀ x ∈ D, rootSet D x = {x})
    (hOD : OppositeDetermines D) {d e : G} (hd : d ∈ D) (he : e ∈ D) (heN : e ∈ nCore D d)
    (hZ : (⟨e, heN⟩ : nCore D d) ∈ Subgroup.center (nCore D d)) : e = d :=
  eq_of_mem_nCore_of_forall_commute hclass hD hsing hOD hd he heN
    ((mem_center_nCore_iff heN).1 hZ)

theorem conj_eq_or_of_mem_Z2 (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hsing : ∀ x ∈ D, rootSet D x = {x})
    (hOD : OppositeDetermines D) {d f s : G} (hd : d ∈ D) (hf : f ∈ D) (hfN : f ∈ nCore D d)
    (hfZ : (⟨f, hfN⟩ : nCore D d) ∈ Subgroup.upperCentralSeries (nCore D d) 2) (hs : s ∈ D)
    (hsQ : s ∈ Moufang.twoCore d) : f * s * f⁻¹ = s ∨ f * s * f⁻¹ = s * d := by
  have hsN := mem_nCore_of_mem_twoCore hs hsQ
  have hfQ := mem_twoCore_of_mem_nCore hfN
  have hZ : ⁅(⟨f, hfN⟩ : nCore D d), (⟨s, hsN⟩ : nCore D d)⁆ ∈ Subgroup.center (nCore D d) := by
    rw [← Subgroup.upperCentralSeries_one]
    exact Subgroup.mem_upperCentralSeries_succ_iff.1 hfZ _
  have hsq : f * s * f⁻¹ * s⁻¹ = (f * s) ^ 2 := by
    rw [hD.inv_eq hf, hD.inv_eq hs, sq, ← mul_assoc]
  by_cases h1 : (f * s) ^ 2 = 1
  · exact Or.inl (mul_inv_eq_one.1 (hsq.trans h1))
  right
  have h4 : orderOf (f * s) = 4 := by
    rcases hD.orderOf_mul hf hs with h | h | h
    · exact absurd (by rw [← h]; exact pow_orderOf_eq_one _) h1
    · exact h
    · exact absurd (Special.eq_one_of_mem_of_isPGroup (Moufang.isPGroup_twoCore d)
        ((Moufang.twoCore d).pow_mem ((Moufang.twoCore d).mul_mem hfQ hsQ) 2)
        (Odd.of_dvd_nat h (orderOf_pow_dvd 2))) h1
  have hsqN : (f * s) ^ 2 ∈ nCore D d := (nCore D d).pow_mem ((nCore D d).mul_mem hfN hsN) 2
  have heq : (⟨(f * s) ^ 2, hsqN⟩ : nCore D d) = ⁅(⟨f, hfN⟩ : nCore D d), ⟨s, hsN⟩⁆ :=
    Subtype.ext (by rw [commutatorElement_def]; exact hsq.symm)
  have hd' := eq_of_mem_center_nCore hclass hD hsing hOD hd (hD.sq_mem hf hs h4) hsqN
    (heq ▸ hZ)
  rw [mul_inv_eq_iff_eq_mul.1 (hsq.trans hd')]
  exact (Moufang.commute_of_mem_twoCore hsQ).symm.eq

theorem mul_mem_of_mem_Z2 (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hsing : ∀ x ∈ D, rootSet D x = {x})
    (hOD : OppositeDetermines D) {d f : G} (hd : d ∈ D) (hf : f ∈ D) (hfN : f ∈ nCore D d)
    (hfZ : (⟨f, hfN⟩ : nCore D d) ∈ Subgroup.upperCentralSeries (nCore D d) 2) (hfd : f ≠ d) :
    f * d ∈ D := by
  obtain ⟨s, hs, hsQ, hfs⟩ : ∃ s ∈ D, s ∈ Moufang.twoCore d ∧ ¬ Commute f s := by
    by_contra! h
    exact hfd (eq_of_mem_nCore_of_forall_commute hclass hD hsing hOD hd hf hfN h)
  rcases conj_eq_or_of_mem_Z2 hclass hD hsing hOD hd hf hfN hfZ hs hsQ with h | h
  · exact absurd (mul_inv_eq_iff_eq_mul.1 h) hfs
  have h' : f * s = s * d * f := mul_inv_eq_iff_eq_mul.1 h
  have hfd' : f * d = s * f * s⁻¹ := by
    rw [hD.inv_eq hs, mul_assoc s f s, h', ← mul_assoc, ← mul_assoc, hD.mul_self_eq_one hs,
      one_mul]
    exact (commute_of_mem_nCore hfN).eq
  rw [hfd']
  exact conj_mem_of_isClass hclass s hf

theorem orderOf_mul_eq_three_of_mem_Z2 (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hsing : ∀ x ∈ D, rootSet D x = {x})
    (hOD : OppositeDetermines D) {d f z : G} (hd : d ∈ D) (hf : f ∈ D) (hfN : f ∈ nCore D d)
    (hfZ : (⟨f, hfN⟩ : nCore D d) ∈ Subgroup.upperCentralSeries (nCore D d) 2) (hz : z ∈ D)
    (hfz : ¬ Commute f z) (hodd : Odd (orderOf (f * z))) (h4 : orderOf (z * d) = 4) :
    f * (z * d * z) * f⁻¹ = z * d * z * d ∧ orderOf (f * z) = 3 := by
  have hfQ := mem_twoCore_of_mem_nCore hfN
  have hfd : Commute f d := Moufang.commute_of_mem_twoCore hfQ
  have hwD : z * d * z ∈ D := by simpa [hD.inv_eq hz] using conj_mem_of_isClass hclass z hd
  have h1 : f * (z * d * z) * f⁻¹ = z * d * z * d := by
    rcases conj_eq_or_of_mem_Z2 hclass hD hsing hOD hd hf hfN hfZ hwD
        (conj_mem_twoCore_of_orderOf_eq_four hclass hD hz hd h4) with h | h
    · exact absurd (mul_inv_eq_iff_eq_mul.1 h)
        (not_commute_conj_of_odd_special hD hf hz hd hfz hodd h4 hfd)
    · exact h
  refine ⟨h1, ?_⟩
  have hf2 := hD.mul_self_eq_one hf
  have hz2 := hD.mul_self_eq_one hz
  have hdd : ∀ y : G, d * (d * y) = y := fun y => by
    rw [← mul_assoc, hD.mul_self_eq_one hd, one_mul]
  have hzt : Commute z (z * d * z * d) := by
    have := (sq_mem_of_orderOf_eq_four hD hz hd h4).2.1
    rwa [sq, ← mul_assoc] at this
  have h1' : f * (z * d * z) = z * d * z * d * f := mul_inv_eq_iff_eq_mul.1 h1
  have e1 : SemiconjBy (f * z) d (z * d * z * d) := by
    show f * z * d = z * d * z * d * (f * z)
    rw [← mul_assoc, ← h1']
    simp only [mul_assoc, hz2, mul_one]
  have e2 : SemiconjBy (f * z) (z * d * z * d) (z * d * z) := by
    show f * z * (z * d * z * d) = z * d * z * (f * z)
    calc f * z * (z * d * z * d) = f * (z * d * z) * d * z := by
          rw [mul_assoc f z, hzt.eq]
          simp only [mul_assoc]
      _ = z * d * z * (f * z) := by
          rw [h1', mul_assoc _ f d, hfd.eq]
          simp only [mul_assoc, hdd]
  have e3 : SemiconjBy (f * z) (z * d * z) d := by
    show f * z * (z * d * z) = d * (f * z)
    rw [show f * z * (z * d * z) = f * (z * z) * d * z by simp only [mul_assoc], hz2, mul_one,
      hfd.eq, mul_assoc]
  have hσ3 : Commute ((f * z) ^ 3) d := by
    rw [pow_three]
    exact e3.mul_left (e2.mul_left e1)
  have hinv : SemiconjBy f (f * z) (f * z)⁻¹ := by
    show f * (f * z) = (f * z)⁻¹ * f
    rw [mul_inv_rev, hD.inv_eq hz, hD.inv_eq hf, ← mul_assoc, hf2, one_mul, mul_assoc, hf2,
      mul_one]
  have hinv3 : f * (f * z) ^ 3 * f⁻¹ = ((f * z) ^ 3)⁻¹ := by
    rw [(hinv.pow_right 3).eq, mul_inv_cancel_right, inv_pow]
  have h3 := eq_one_of_mem_twoCore_of_inv hfQ hσ3 hinv3 (Odd.of_dvd_nat hodd (orderOf_pow_dvd 3))
  rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one h3) with h | h
  · refine absurd ?_ hfz
    rw [eq_inv_of_mul_eq_one_right (orderOf_eq_one_iff.1 h)]
    exact (Commute.refl f).inv_right
  · exact h

end CFSG.Timmesfeld.Bridge
