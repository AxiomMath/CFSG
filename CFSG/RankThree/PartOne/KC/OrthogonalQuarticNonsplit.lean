module

public import CFSG.RankThree.PartOne.KC.OrthogonalFactorization
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourSplitCoordinates

public section

universe u v

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module Polynomial CFSG.RankThree.PartOne.KCPrimary CFSG.LocalAnalysis.ComponentInitial

section Counting

theorem card_fiber_eq_card_ker {G H : Type*} [Group G] [Group H] [Finite G] (φ : G →* H)
    (hφ : Function.Surjective φ) (h : H) :
    Nat.card {g : G // φ g = h} = Nat.card φ.ker := by
  classical
  have := Fintype.ofFinite G
  have h1 := MonoidHom.card_fiber_eq_of_mem_range φ (x := h) (y := 1) (hφ h) ⟨1, map_one φ⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, h1, ← Fintype.card_subtype,
    ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => (MonoidHom.mem_ker).symm)

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Finite K] [Finite E] {d : ℕ}

theorem card_fiber_unitaryNorm (hd : finrank K E = 2 * d) (t : fixedSubfield K E d)
    (ht : t ≠ 0) : Nat.card {z : E // unitaryNorm hd z = t} = Nat.card K ^ d + 1 := by
  obtain ⟨ℓ, f, hU, hq, hbar⟩ := exists_unitaryFieldData K E hd
  obtain ⟨hker, hsurj⟩ := hU.card_ker_normUnits_and_surjective
  have htmem : (t : E) ∈ hU.fixedField := by
    rw [UnitaryFieldData.mem_fixedField, hbar]
    exact (mem_fixedSubfield K E d _).mp t.2
  let tU : hU.fixedField := ⟨(t : E), htmem⟩
  have htU : tU ≠ 0 := fun h => ht (Subtype.ext (by simpa [tU] using congrArg Subtype.val h))
  let uU : hU.fixedFieldˣ := Units.mk0 tU htU
  have hfib := card_fiber_eq_card_ker (Units.map hU.normHom) hsurj uU
  rw [hker] at hfib
  have hqd : ℓ ^ (f * d) = Nat.card K ^ d := by rw [hq, ← pow_mul]
  rw [hqd] at hfib
  rw [← hfib]
  have hnorm : ∀ z : E, hU.norm z = z * z ^ (Nat.card K ^ d) := fun z => by
    rw [UnitaryFieldData.norm, hbar]
  have hunorm : ∀ z : E, ((unitaryNorm hd z : fixedSubfield K E d) : E) =
      z * z ^ (Nat.card K ^ d) := fun z => by
    rw [coe_unitaryNorm, frobPow_apply]
  refine Nat.card_congr
    { toFun := fun z => ⟨Units.mk0 z.1 (fun h0 => ht (by
        have := z.2
        rw [h0] at this
        rw [← this]
        apply Subtype.ext
        rw [hunorm]
        simp)), ?_⟩
      invFun := fun u => ⟨(u.1 : E), ?_⟩
      left_inv := fun z => rfl
      right_inv := fun u => Subtype.ext (Units.ext rfl) }
  · apply Units.ext
    apply Subtype.ext
    have h1 := congrArg Subtype.val z.2
    rw [hunorm] at h1
    show hU.norm z.1 = (t : E)
    rw [hnorm, h1]
  · apply Subtype.ext
    have h1 := congrArg Subtype.val (congrArg Units.val u.2)
    change hU.norm (u.1 : E) = (t : E) at h1
    rw [hnorm] at h1
    rw [hunorm, h1]

theorem card_trace_ker (hd : finrank K E = 2 * d) (hd0 : 0 < d) :
    Nat.card {t : fixedSubfield K E d // Algebra.trace K (fixedSubfield K E d) t = 0} =
      Nat.card K ^ (d - 1) := by
  classical
  have : Finite (fixedSubfield K E d) := inferInstance
  have : FiniteDimensional K (fixedSubfield K E d) := inferInstance
  have : Algebra.IsSeparable K (fixedSubfield K E d) := inferInstance
  have hsurj := Algebra.trace_surjective K (fixedSubfield K E d)
  let f : fixedSubfield K E d →+ K := (Algebra.trace K (fixedSubfield K E d)).toAddMonoidHom
  have h1 := AddSubgroup.card_ker_mul_card_of_surjective (f := f) hsurj
  rw [card_fixedSubfield K E hd] at h1
  have hk : Nat.card {t : fixedSubfield K E d // Algebra.trace K (fixedSubfield K E d) t = 0} =
      Nat.card f.ker := Nat.card_congr (Equiv.subtypeEquivRight fun t => by
        rw [AddMonoidHom.mem_ker]; rfl)
  rw [hk]
  have hqpos : 0 < Nat.card K := Nat.card_pos
  have hd' : Nat.card K ^ d = Nat.card K ^ (d - 1) * Nat.card K := by
    rw [← pow_succ]; congr 1; omega
  rw [hd'] at h1
  exact Nat.eq_of_mul_eq_mul_right hqpos h1

theorem unitaryNorm_ne_zero (hd : finrank K E = 2 * d) {z : E} (hz : z ≠ 0) :
    unitaryNorm hd z ≠ 0 := by
  intro h
  have h1 := congrArg Subtype.val h
  rw [coe_unitaryNorm] at h1
  have h2 : z * frobPow K E d z = 0 := h1
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact hz h3
  · exact hz ((map_eq_zero_iff _ (frobPow K E d).injective).mp h3)

theorem card_nonzero_singular_hermitian (hd : finrank K E = 2 * d) (hd0 : 0 < d) :
    Nat.card {z : E // z ≠ 0 ∧ hermitianForm hd z = 0} =
      (Nat.card K ^ (d - 1) - 1) * (Nat.card K ^ d + 1) := by
  classical
  have := Fintype.ofFinite E
  have := Fintype.ofFinite (fixedSubfield K E d)
  let S : Finset E := Finset.univ.filter fun z =>
    z ≠ 0 ∧ Algebra.trace K (fixedSubfield K E d) (unitaryNorm hd z) = 0
  let T₀ : Finset (fixedSubfield K E d) := Finset.univ.filter fun t =>
    t ≠ 0 ∧ Algebra.trace K (fixedSubfield K E d) t = 0
  have hS : S.card = ∑ t ∈ T₀, (S.filter fun z => unitaryNorm hd z = t).card :=
    Finset.card_eq_sum_card_fiberwise (f := fun z => unitaryNorm hd z) (s := S) (t := T₀)
      fun z hz => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        unitaryNorm_ne_zero hd (Finset.mem_filter.mp hz).2.1, (Finset.mem_filter.mp hz).2.2⟩
  have hfib : ∀ t ∈ T₀, (S.filter fun z => unitaryNorm hd z = t).card =
      Nat.card K ^ d + 1 := by
    intro t ht
    simp only [T₀, Finset.mem_filter, Finset.mem_univ, true_and] at ht
    have h1 := card_fiber_unitaryNorm hd t ht.1
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h1
    rw [← h1]
    congr 1
    ext z
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨⟨fun hz0 => ht.1 ?_, ?_⟩, h⟩
      · rw [← h, hz0]
        apply Subtype.ext
        rw [coe_unitaryNorm]
        simp
      · rw [h]; exact ht.2
  have hT : T₀.card = Nat.card K ^ (d - 1) - 1 := by
    have h1 := card_trace_ker hd hd0
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h1
    have hT0 : T₀ = (Finset.univ.filter fun t : fixedSubfield K E d =>
        Algebra.trace K (fixedSubfield K E d) t = 0).erase 0 := by
      ext t
      simp only [T₀, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    rw [hT0, Finset.card_erase_of_mem (by simp), h1]
  have hcard : Nat.card {z : E // z ≠ 0 ∧ hermitianForm hd z = 0} = S.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
  rw [hcard, hS, Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, hT]

end Counting

section Matrices

open Matrix

theorem card_det_ne_zero (K : Type*) [Field K] [Fintype K] :
    Nat.card {X : Matrix (Fin 2) (Fin 2) K // X.det ≠ 0} =
      (Fintype.card K ^ 2 - 1) * (Fintype.card K ^ 2 - Fintype.card K) := by
  classical
  have e : GL (Fin 2) K ≃ {X : Matrix (Fin 2) (Fin 2) K // X.det ≠ 0} :=
    { toFun := fun A => ⟨A.1, GeneralLinearGroup.det_ne_zero A⟩
      invFun := fun X => GeneralLinearGroup.mkOfDetNeZero X.1 X.2
      left_inv := fun A => by ext i j; rfl
      right_inv := fun X => rfl }
  rw [← Nat.card_congr e, Matrix.card_GL_field]
  simp [Fin.prod_univ_two]

theorem card_nonzero_singular_matrix (K : Type*) [Field K] [Finite K] :
    Nat.card {X : Matrix (Fin 2) (Fin 2) K // X ≠ 0 ∧ X.det = 0} =
      (Nat.card K - 1) * (Nat.card K + 1) ^ 2 := by
  classical
  have := Fintype.ofFinite K
  have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have hq' : Nat.card K = Fintype.card K := Nat.card_eq_fintype_card
  rw [hq']
  have h1 := card_det_ne_zero K
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h1
  have h2 : Fintype.card (Matrix (Fin 2) (Fin 2) K) = Fintype.card K ^ 4 := by
    rw [← Nat.card_eq_fintype_card, Matrix.card_matrix, Nat.card_eq_fintype_card]; simp
  have a1 := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Matrix (Fin 2) (Fin 2) K))) (fun X => X.det ≠ 0)
  have a2 := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Matrix (Fin 2) (Fin 2) K)).filter (fun X => ¬ X.det ≠ 0))
    (fun X => X = 0)
  have hs : ((Finset.univ : Finset (Matrix (Fin 2) (Fin 2) K)).filter
      (fun X => ¬ X.det ≠ 0)).filter (fun X => X = 0) = {0} := by
    ext X
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not, Finset.mem_singleton]
    constructor
    · exact fun h => h.2
    · rintro rfl; exact ⟨by simp, rfl⟩
  have hs2 : ((Finset.univ : Finset (Matrix (Fin 2) (Fin 2) K)).filter
      (fun X => ¬ X.det ≠ 0)).filter (fun X => ¬ X = 0) =
      (Finset.univ : Finset (Matrix (Fin 2) (Fin 2) K)).filter (fun X => X ≠ 0 ∧ X.det = 0) := by
    ext X
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
    tauto
  rw [hs, hs2, Finset.card_singleton] at a2
  rw [Finset.card_univ, h2] at a1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h4 : (Fintype.card K ^ 2 - 1) * (Fintype.card K ^ 2 - Fintype.card K) +
      (Fintype.card K - 1) * (Fintype.card K + 1) ^ 2 + 1 = Fintype.card K ^ 4 := by
    obtain ⟨r, hr⟩ : ∃ r, Fintype.card K = r + 2 := ⟨Fintype.card K - 2, by omega⟩
    rw [hr]
    have e1 : (r + 2) ^ 2 - 1 = r ^ 2 + 4 * r + 3 := by
      have : (r + 2) ^ 2 = r ^ 2 + 4 * r + 4 := by ring
      omega
    have e2 : (r + 2) ^ 2 - (r + 2) = r ^ 2 + 3 * r + 2 := by
      have : (r + 2) ^ 2 = (r ^ 2 + 3 * r + 2) + (r + 2) := by ring
      omega
    rw [e1, e2]
    have e3 : r + 2 - 1 = r + 1 := by omega
    rw [e3]
    ring
  omega

end Matrices

section Lines

variable {K W : Type*} [Field K] [Finite K] [AddCommGroup W] [Module K W] [Finite W]

omit [Finite K] in
theorem card_nonzero_singular_eq_mul_card_lines (Q : QuadraticForm K W) :
    Nat.card {w : W // w ≠ 0 ∧ Q w = 0} =
      (Nat.card K - 1) *
        Nat.card {L : Submodule K W // finrank K L = 1 ∧ ∀ w ∈ L, Q w = 0} := by
  classical
  have := Fintype.ofFinite W
  have hfinL : Finite (Submodule K W) :=
    Finite.of_injective (fun L : Submodule K W => (L : Set W)) SetLike.coe_injective
  have := Fintype.ofFinite (Submodule K W)
  let A : Finset W := Finset.univ.filter fun w => w ≠ 0 ∧ Q w = 0
  let Lset : Finset (Submodule K W) := Finset.univ.filter fun L =>
    finrank K L = 1 ∧ ∀ w ∈ L, Q w = 0
  have hmapsto : ∀ w ∈ A, (K ∙ w) ∈ Lset := by
    intro w hw
    have hw' := Finset.mem_filter.mp hw
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, finrank_span_singleton hw'.2.1, ?_⟩
    intro v hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [QuadraticMap.map_smul, hw'.2.2, smul_zero]
  have hA : A.card = ∑ L ∈ Lset, (A.filter fun w => (K ∙ w) = L).card :=
    Finset.card_eq_sum_card_fiberwise (f := fun w => K ∙ w) (s := A) (t := Lset) hmapsto
  have hfib : ∀ L ∈ Lset, (A.filter fun w => (K ∙ w) = L).card = Nat.card K - 1 := by
    intro L hL
    have hL' := Finset.mem_filter.mp hL
    have hfilt : A.filter (fun w => (K ∙ w) = L) =
        (Finset.univ.filter fun w : W => w ∈ L).erase 0 := by
      ext w
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      constructor
      · rintro ⟨⟨hw0, -⟩, hwL⟩
        exact ⟨hw0, hwL ▸ Submodule.mem_span_singleton_self w⟩
      · rintro ⟨hw0, hwL⟩
        refine ⟨⟨hw0, hL'.2.2 w hwL⟩, ?_⟩
        refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
        · exact (Submodule.span_singleton_le_iff_mem w L).mpr hwL
        · rw [finrank_span_singleton hw0, hL'.2.1]
    have hLcard : (Finset.univ.filter fun w : W => w ∈ L).card = Nat.card K := by
      have h1 : Nat.card L = Nat.card K ^ finrank K L := Module.natCard_eq_pow_finrank
      rw [hL'.2.1, pow_one] at h1
      rw [← h1, Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hfilt, Finset.card_erase_of_mem (by simp), hLcard]
  have e1 : Nat.card {w : W // w ≠ 0 ∧ Q w = 0} = A.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have e2 : Nat.card {L : Submodule K W // finrank K L = 1 ∧ ∀ w ∈ L, Q w = 0} = Lset.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [e1, e2, hA, Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, mul_comm]

end Lines

section Structure

variable {K : Type u} {W : Type v} [Field K] [Finite K] [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] {Q : QuadraticForm K W} {p : ℕ} {x : W ≃ₗ[K] W}

omit [Finite K] in
theorem OddOrderIsometry.X_sub_one_not_mem (hx : OddOrderIsometry Q p x)
    (hx1 : ∀ w, x w = w → w = 0) : (X - 1 : K[X]) ∉ primaryFactors x.toLinearMap := by
  intro hmem
  apply primaryComponent_ne_bot hx.squarefree_minpoly hmem
  rw [← fixedSpace_eq_primaryComponent, eq_bot_iff]
  intro w hw
  exact (Submodule.mem_bot K).mpr (hx1 w (mem_fixedSpace.mp hw))

theorem OddOrderIsometry.dvd_natDegree_of_orderOf (hx : OddOrderIsometry Q p x) (hp : p.Prime)
    {n : ℕ} (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = n) (hx1 : ∀ w, x w = w → w = 0)
    {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap) : n ∣ h.natDegree := by
  have hirr := irreducible_of_mem_primaryFactors hh
  have : Fact (Irreducible h) := ⟨hirr⟩
  have hne1 : h ≠ X - 1 := fun e => hx.X_sub_one_not_mem hx1 (e ▸ hh)
  obtain ⟨hlam0, hord'⟩ := hx.orderOf_root hp hh hne1
  have hdvd : p ∣ Nat.card (AdjoinRoot h) - 1 := by
    rw [← Nat.card_units, ← hord']
    exact orderOf_dvd_natCard _
  have hfin : finrank K (AdjoinRoot h) = h.natDegree := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim]
  have hcard : Nat.card (AdjoinRoot h) = Nat.card K ^ h.natDegree := by
    rw [Module.natCard_eq_pow_finrank (K := K), hfin]
  rw [hcard] at hdvd
  have h1 : 1 ≤ Nat.card K ^ h.natDegree := Nat.one_le_pow _ _ Nat.card_pos
  have h2 : (((Nat.card K ^ h.natDegree - 1 : ℕ)) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
  rw [Nat.cast_sub h1, Nat.cast_pow, Nat.cast_one, sub_eq_zero] at h2
  rw [← hord]
  exact orderOf_dvd_of_pow_eq_one h2

theorem OddOrderIsometry.exists_unique_quartic_factor (hx : OddOrderIsometry Q p x)
    (hp : p.Prime) (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 4) (hW : finrank K W = 4)
    (hx1 : ∀ w, x w = w → w = 0) :
    ∃ h : K[X], primaryFactors x.toLinearMap = {h} ∧ h.natDegree = 4 ∧
      primaryMultiplicity x.toLinearMap h = 1 := by
  classical
  have hsum := finrank_eq_sum_degree_mul_multiplicity hx.squarefree_minpoly
  rw [hW, Finset.sum_coe_sort (primaryFactors x.toLinearMap)
    (fun a => a.natDegree * primaryMultiplicity x.toLinearMap a)] at hsum
  have hdeg4 : ∀ a ∈ primaryFactors x.toLinearMap, 4 ≤ a.natDegree := fun a ha =>
    Nat.le_of_dvd (irreducible_of_mem_primaryFactors ha).natDegree_pos
      (hx.dvd_natDegree_of_orderOf hp hord hx1 ha)
  have hge : ∀ a ∈ primaryFactors x.toLinearMap,
      4 ≤ a.natDegree * primaryMultiplicity x.toLinearMap a := by
    intro a ha
    have : Fact (Irreducible a) := ⟨irreducible_of_mem_primaryFactors ha⟩
    have hm := hx.primaryMultiplicity_pos ha
    exact (hdeg4 a ha).trans (Nat.le_mul_of_pos_right _ hm)
  have hcard := Finset.card_nsmul_le_sum (primaryFactors x.toLinearMap)
    (fun a => a.natDegree * primaryMultiplicity x.toLinearMap a) 4 hge
  rw [← hsum, smul_eq_mul] at hcard
  have hne : (primaryFactors x.toLinearMap).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp] at hsum
    simp at hsum
  have hc1 : (primaryFactors x.toLinearMap).card = 1 := by
    have := hne.card_pos
    omega
  obtain ⟨h, hs⟩ := Finset.card_eq_one.mp hc1
  refine ⟨h, hs, ?_⟩
  have hhmem : h ∈ primaryFactors x.toLinearMap := hs ▸ Finset.mem_singleton_self h
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hhmem⟩
  have hm := hx.primaryMultiplicity_pos hhmem
  have hprod : h.natDegree * primaryMultiplicity x.toLinearMap h = 4 := by
    rw [hs, Finset.sum_singleton] at hsum
    exact hsum.symm
  have hd4 := hdeg4 h hhmem
  have hm1 : primaryMultiplicity x.toLinearMap h = 1 := by
    by_contra hne1
    have h2 : 2 ≤ primaryMultiplicity x.toLinearMap h := by omega
    nlinarith
  rw [hm1] at hprod
  exact ⟨by omega, hm1⟩

theorem OddOrderIsometry.exists_quartic_model (hx : OddOrderIsometry Q p x) (hp : p.Prime)
    (hp2 : Odd p) (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 4)
    (hW : finrank K W = 4) (hx1 : ∀ w, x w = w → w = 0) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra K E) (_ : Finite E) (hd : finrank K E = 2 * 2)
      (e : W ≃ₗ[K] E), ∀ w, Q w = hermitianForm hd (e w) := by
  classical
  obtain ⟨h, hs, hdeg, hm⟩ := hx.exists_unique_quartic_factor hp hord hW hx1
  have hh : h ∈ primaryFactors x.toLinearMap := hs ▸ Finset.mem_singleton_self h
  have hirr := irreducible_of_mem_primaryFactors hh
  have : Fact (Irreducible h) := ⟨hirr⟩
  have hne1 : h ≠ X - 1 := fun e => hx.X_sub_one_not_mem hx1 (e ▸ hh)
  have hself : h = reciprocalPolynomial h := by
    have := hx.reciprocalPolynomial_mem hh
    rw [hs, Finset.mem_singleton] at this
    exact this.symm
  obtain ⟨d, hdegd, -, -, -, -, -, ι, hinj, -, hQι, -⟩ := hx.selfDualModel hp2 hh hne1 hself
  have hd2 : d = 2 := by omega
  subst hd2
  have hfin : finrank K (AdjoinRoot h) = 2 * 2 := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim]
    omega
  have hm0 : 0 < primaryMultiplicity x.toLinearMap h := hx.primaryMultiplicity_pos hh
  let i₀ : Fin (primaryMultiplicity x.toLinearMap h) := ⟨0, hm0⟩
  let ι' : AdjoinRoot h →ₗ[K] W :=
    ι ∘ₗ LinearMap.single K (fun _ : Fin (primaryMultiplicity x.toLinearMap h) => AdjoinRoot h) i₀
  have hι' : ∀ z, ι' z = ι (Pi.single i₀ z) := fun z => rfl
  have hinj' : Function.Injective ι' := fun a b hab =>
    Pi.single_injective i₀ (hinj (by rw [← hι', ← hι']; exact hab))
  have hbij : Function.Bijective ι' :=
    ⟨hinj', (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [hfin, hW])).mp hinj'⟩
  let e : W ≃ₗ[K] AdjoinRoot h := (LinearEquiv.ofBijective ι' hbij).symm
  refine ⟨AdjoinRoot h, inferInstance, inferInstance, inferInstance, hfin, e, fun w => ?_⟩
  have hw : w = ι (Pi.single i₀ (e w)) := by
    rw [← hι']
    exact ((LinearEquiv.ofBijective ι' hbij).apply_symm_apply w).symm
  obtain ⟨hmem, hQ⟩ := hQι (Pi.single i₀ (e w))
  have hN : 0 < Nat.card K ^ 2 := pow_pos Nat.card_pos 2
  have hsumz : ∑ i, (Pi.single i₀ (e w) : Fin (primaryMultiplicity x.toLinearMap h) →
      AdjoinRoot h) i * (Pi.single i₀ (e w) : Fin (primaryMultiplicity x.toLinearMap h) →
        AdjoinRoot h) i ^ Nat.card K ^ 2 = e w * e w ^ Nat.card K ^ 2 := by
    rw [Finset.sum_eq_single i₀]
    · simp
    · intro i _ hi
      simp [Pi.single_eq_of_ne hi, zero_pow hN.ne']
    · simp
  rw [congrArg Q hw, hQ, hermitianForm_apply]
  congr 1
  apply Subtype.ext
  rw [coe_unitaryNorm, frobPow_apply]
  exact hsumz

end Structure

end CFSG.RankThree.PartOne.KCOrthogonal

namespace CFSG.RankThree.PartOne

open Module CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
  CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit

theorem quartic_prime_orthogonal_four_space_is_nonsplit
    {ℓ p f : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime) (hp3 : 3 < p) (hpℓ : p ≠ ℓ) (hf : 1 ≤ f)
    {K : Type u} [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 4)
    {W : Type v} [AddCommGroup W] [Module K W] (hW : finrank K W = 4) (Q : QuadraticForm K W)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {x : W ≃ₗ[K] W}
    (hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hxp : orderOf x = p)
    (hx1 : LinearMap.ker (x.toLinearMap - 1) = ⊥) :
    Nat.card {L : Submodule K W // finrank K L = 1 ∧ ∀ w ∈ L, Q w = 0} = Nat.card K ^ 2 + 1 ∧
    (¬ ∃ U : Submodule K W, finrank K U = 2 ∧ ∀ u ∈ U, Q u = 0) ∧
    ∃ (E : Type u) (_ : Field E) (_ : Algebra K E) (F : IntermediateField K E),
      Nat.card F = Nat.card K ^ 2 ∧ Nat.card E = Nat.card K ^ 4 ∧
      (∀ z : E, z ∈ F ↔ z ^ (Nat.card K ^ 2) = z) ∧
      ∃ e : W ≃ₗ[K] E, ∀ w, ∃ hmem : e w * e w ^ (Nat.card K ^ 2) ∈ F,
        Q w = Algebra.trace K F ⟨e w * e w ^ (Nat.card K ^ 2), hmem⟩ := by
  classical
  have hp2 : p ≠ 2 := by omega
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hcharP : CharP K ℓ := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hK)
  have hchar : ringChar K = ℓ := ringChar.eq K ℓ
  have hcast : (p : K) ≠ 0 := by
    intro h0
    have h1 := (ringChar.spec K p).mp h0
    rw [hchar] at h1
    rcases (Nat.dvd_prime hp).mp h1 with h2 | h2
    · exact hℓ.one_lt.ne' h2
    · exact hpℓ h2.symm
  have : FiniteDimensional K W := Module.finite_of_finrank_pos (by omega)
  have : Finite W := Module.finite_of_finite K
  have hx : OddOrderIsometry Q p x :=
    ⟨hxO, by rw [← hxp]; exact pow_orderOf_eq_one x, hcast, fun v hv =>
      hQ.1 v fun w => by simpa using hv w⟩
  have hx1' : ∀ w, x w = w → w = 0 := fun w hw => by
    have : w ∈ LinearMap.ker (x.toLinearMap - 1) := by
      rw [LinearMap.mem_ker]; simp [hw]
    rw [hx1] at this
    exact (Submodule.mem_bot K).mp this
  obtain ⟨E, _, _, hfinE, hd, e, he⟩ :=
    hx.exists_quartic_model hp (hp.odd_of_ne_two hp2) hord hW hx1'
  have hcount : Nat.card {w : W // w ≠ 0 ∧ Q w = 0} =
      (Nat.card K - 1) * (Nat.card K ^ 2 + 1) := by
    have h1 := card_nonzero_singular_hermitian (K := K) (E := E) hd (by norm_num)
    rw [show (2 - 1 : ℕ) = 1 from rfl, pow_one] at h1
    rw [← h1]
    exact Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun w => by
      simp only [LinearEquiv.coe_toEquiv, ne_eq, map_eq_zero_iff _ e.injective, he w])
  have hq2 : 2 ≤ Nat.card K := by
    rw [hK]
    calc 2 ≤ ℓ := hℓ.two_le
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hf
  refine ⟨?_, ?_, ?_⟩
  · have h1 := card_nonzero_singular_eq_mul_card_lines Q
    rw [hcount] at h1
    have : 0 < Nat.card K - 1 := by omega
    exact (Nat.eq_of_mul_eq_mul_left this h1).symm
  · rintro ⟨S, hS2, hSQ⟩
    obtain ⟨psi, -, hpsi, -, -⟩ := split_four_determinant_form_isometry Q hQ hW S hS2 hSQ
    have h1 : Nat.card {w : W // w ≠ 0 ∧ Q w = 0} =
        Nat.card {X : Matrix (Fin 2) (Fin 2) K // X ≠ 0 ∧ X.det = 0} :=
      Nat.card_congr (Equiv.subtypeEquiv psi.toEquiv fun w => by
        simp only [LinearEquiv.coe_toEquiv, ne_eq, map_eq_zero_iff _ psi.injective, hpsi w])
    rw [hcount, card_nonzero_singular_matrix] at h1
    have h2 : 0 < Nat.card K - 1 := by omega
    have h3 := Nat.eq_of_mul_eq_mul_left h2 h1
    have h4 : (Nat.card K + 1) ^ 2 = Nat.card K ^ 2 + 2 * Nat.card K + 1 := by ring
    omega
  · have hfin4 : finrank K E = 4 := by omega
    refine ⟨E, inferInstance, inferInstance, fixedSubfield K E 2, card_fixedSubfield K E hd, ?_,
      fun z => ?_, e, fun w => ?_⟩
    · rw [Module.natCard_eq_pow_finrank (K := K), hfin4]
    · rw [mem_fixedSubfield]
    · have hmem : e w * e w ^ (Nat.card K ^ 2) ∈ fixedSubfield K E 2 := by
        simpa [frobPow_apply] using mul_frobPow_mem_fixedSubfield hd (e w)
      refine ⟨hmem, ?_⟩
      rw [he w, hermitianForm_apply]
      congr 1
      apply Subtype.ext
      rw [coe_unitaryNorm, frobPow_apply]

end CFSG.RankThree.PartOne
