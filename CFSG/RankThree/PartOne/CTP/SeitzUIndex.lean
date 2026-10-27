module

public import CFSG.RankThree.PartOne.CTP.SeitzUFrame
public import CFSG.RankThree.PartOne.CTP.SeitzUSplit
public import CFSG.RankThree.PartOne.CTP.SeitzLift
public import CFSG.RankThree.PartOne.CTP.SeitzTransfer
public import CFSG.RankThree.PartOne.CTP.SeitzThree
public import CFSG.RankThree.PartTwo.Census.OddClassical.UnitaryWitness
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryPlane

variable {ℓ f p : ℕ} {K : Type} [Field K]

theorem not_dvd_gcd_six {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (q : ℕ) : ¬ p ∣ Nat.gcd 6 q := by
  intro hd
  have h3 : p ∣ 6 := hd.trans (Nat.gcd_dvd_left _ _)
  have h4 := Nat.le_of_dvd (by norm_num) h3
  interval_cases p
  · exact absurd h3 (by norm_num)
  · exact absurd hp (by norm_num)

theorem closure_centralizers_statedProj_unitary_of_lift {m : ℕ}
    (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hm : 1 ≤ m)
    (hker : ¬ p ∣ Nat.gcd m (ℓ ^ f + 1))
    (E : Subgroup (StatedProj (StatedSU m (ℓ ^ f) K))) [CFSG.IsElementaryAbelian p E]
    (hcard : Nat.card E = p ^ 2)
    (hG : ∀ E' : Subgroup (unitarySU ℓ f K m), (∀ x ∈ E', ∀ y ∈ E', x * y = y * x) →
      (∀ x ∈ E', x ^ p = 1) → Nat.card E' = p ^ 2 →
      Subgroup.closure {g : unitarySU ℓ f K m | ∃ x ∈ E', x ≠ 1 ∧ g * x = x * g} = ⊤) :
    Subgroup.closure {k : StatedProj (StatedSU m (ℓ ^ f) K) |
      ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  classical
  have hfin := h.finite
  have : Fact p.Prime := ⟨hp⟩
  let π : unitarySU ℓ f K m →* StatedProj (StatedSU m (ℓ ^ f) K) :=
    QuotientGroup.mk' ((StatedScalars (Fin m) K).subgroupOf (unitarySU ℓ f K m))
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hkerπ : π.ker = unitaryScalars h m := by
    rw [QuotientGroup.ker_mk', unitaryScalars_eq h hm]
  have hker' : ¬ p ∣ Nat.card π.ker := by
    rw [hkerπ, card_unitaryScalars h hm]
    exact hker
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨x, hx⟩ : E) ⟨y, hy⟩)
  have hexp : ∀ x ∈ E, x ^ p = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  exact closure_centralizers_of_lift π hπ hker' E hcomm hexp fun E' hc he hcd _ =>
    hG E' hc he (hcd.trans hcard)

theorem closure_centralizers_statedProj_su_three (h : UnitaryFieldData ℓ f K) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpℓ : p ≠ ℓ) (E : Subgroup (StatedProj (StatedSU 3 (ℓ ^ f) K)))
    [CFSG.IsElementaryAbelian p E] (hcard : Nat.card E = p ^ 2) :
    Subgroup.closure {k : StatedProj (StatedSU 3 (ℓ ^ f) K) |
      ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  refine closure_centralizers_statedProj_unitary_of_lift h hp (by norm_num) ?_ E hcard ?_
  · intro hd
    have := Nat.le_of_dvd (by norm_num) (hd.trans (Nat.gcd_dvd_left _ _))
    omega
  · intro E' hc he hcd
    have h2 := two_mul_ordNegQ_le h hp hpℓ E' he hcd
    have hpos := pos_ordNegQ (f := f) hp hpℓ h.prime
    have hpq : p ∣ ℓ ^ f + 1 := (ordNegQ_eq_one_iff hp).mp (by omega)
    have hq : ℓ ^ f ≠ 2 := by
      intro h2'
      rw [h2'] at hpq
      have := Nat.le_of_dvd (by norm_num) hpq
      omega
    exact closure_centralizers_unitarySU_of_dvd_add_one (n := 2) h hp hpq hq E' hc he hcd

theorem closure_centralizers_statedProj_su_six_two (h : UnitaryFieldData ℓ f K)
    (hq : ℓ ^ f = 2) (hp : p.Prime) (hp5 : 5 ≤ p) (hpℓ : p ≠ ℓ)
    (E : Subgroup (StatedProj (StatedSU 6 (ℓ ^ f) K))) [CFSG.IsElementaryAbelian p E]
    (hcard : Nat.card E = p ^ 2) :
    Subgroup.closure {k : StatedProj (StatedSU 6 (ℓ ^ f) K) |
      ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  refine closure_centralizers_statedProj_unitary_of_lift h hp (by norm_num) ?_ E hcard ?_
  · exact not_dvd_gcd_six hp hp5 _
  · intro E' hc he hcd
    exfalso
    have h2 := two_mul_ordNegQ_le h hp hpℓ E' he hcd
    have h4 := four_le_ordNegQ_of_two hp (by omega) hpℓ h.prime hq
    omega

theorem extSeitzAtInner_twistedA_two (q : TauCeti.PrimePower) :
    ExtSeitzAtInner (.twistedA 2 q) := by
  intro K _ _ _ hnab ⟨hv, ⟨e0⟩⟩ p hp hp5 hpd E hE hcard hinner
  have : Fact p.Prime := ⟨hp⟩
  left
  have hU := CFSG.RankThree.PartTwo.Census.unitaryFieldData_galoisField
    (TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩)
    (TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩)
    (TauCeti.ValidLieTypeIndex.fieldExponent_pos ⟨.twistedA 2 q, hv⟩)
  have e1 := e0.trans (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 2 q hv)
  refine closure_fixUnion_eq_top_of_inner_equiv hnab e1 (p := p) ?_ E hcard hinner
  intro E₁ hE₁ hcard₁
  exact closure_centralizers_statedProj_su_three hU hp hp5 hpd E₁ hcard₁

theorem extSeitzAtInner_twistedA_five {q : TauCeti.PrimePower} (hq : q.p = 2)
    (he : q.exponent = 1) : ExtSeitzAtInner (.twistedA 5 q) := by
  intro K _ _ _ hnab ⟨hv, ⟨e0⟩⟩ p hp hp5 hpd E hE hcard hinner
  have : Fact p.Prime := ⟨hp⟩
  left
  have hU := CFSG.RankThree.PartTwo.Census.unitaryFieldData_galoisField
    (TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 5 q, hv⟩)
    (TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 5 q, hv⟩)
    (TauCeti.ValidLieTypeIndex.fieldExponent_pos ⟨.twistedA 5 q, hv⟩)
  have hq2 : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 5 q, hv⟩ ^
      TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 5 q, hv⟩ = 2 := by
    simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent, hq,
      he]
  have e1 := e0.trans (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 5 q hv)
  refine closure_fixUnion_eq_top_of_inner_equiv hnab e1 (p := p) ?_ E hcard hinner
  intro E₁ hE₁ hcard₁
  exact closure_centralizers_statedProj_su_six_two hU hq2 hp hp5 hpd E₁ hcard₁

theorem closure_centralizers_unitarySU_four_five (h : UnitaryFieldData ℓ f K) {n : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpℓ : p ≠ ℓ) (hn : n + 1 = 4 ∨ n + 1 = 5)
    (E : Subgroup (unitarySU ℓ f K (n + 1))) (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (he : ∀ x ∈ E, x ^ p = 1) (hcd : Nat.card E = p ^ 2) :
    Subgroup.closure {g : unitarySU ℓ f K (n + 1) | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g} = ⊤ := by
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  have h2 := two_mul_ordNegQ_le h hp hpℓ E he hcd
  have hpos := pos_ordNegQ (f := f) hp hpℓ h.prime
  rcases (show ordNegQ ℓ f p = 1 ∨ ordNegQ ℓ f p = 2 by omega) with he1 | he2
  · have hpq : p ∣ ℓ ^ f + 1 := (ordNegQ_eq_one_iff hp).mp he1
    have hq : ℓ ^ f ≠ 2 := by
      intro h2'
      rw [h2'] at hpq
      have := Nat.le_of_dvd (by norm_num) hpq
      omega
    exact closure_centralizers_unitarySU_of_dvd_add_one h hp hpq hq E hc he hcd
  · have hpq := (ordNegQ_eq_two hp (by omega) h.prime he2 h.one_le).1
    obtain ⟨P, hP, hdiag⟩ := exists_frame_of_dvd_sub_one h hp hp5 hpℓ hpq hn E hc he hcd
    exact closure_centralizers_unitarySU_of_frame h hp (by omega) hpq (by omega) E he hcd P hP hdiag

theorem closure_centralizers_statedProj_su_four (h : UnitaryFieldData ℓ f K) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpℓ : p ≠ ℓ) (E : Subgroup (StatedProj (StatedSU 4 (ℓ ^ f) K)))
    [CFSG.IsElementaryAbelian p E] (hcard : Nat.card E = p ^ 2) :
    Subgroup.closure {k : StatedProj (StatedSU 4 (ℓ ^ f) K) |
      ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  refine closure_centralizers_statedProj_unitary_of_lift h hp (by norm_num) ?_ E hcard ?_
  · intro hd
    have := Nat.le_of_dvd (by norm_num) (hd.trans (Nat.gcd_dvd_left _ _))
    omega
  · intro E' hc he hcd
    exact closure_centralizers_unitarySU_four_five (n := 3) h hp hp5 hpℓ (Or.inl rfl) E' hc he hcd

theorem closure_centralizers_statedProj_su_five (h : UnitaryFieldData ℓ f K) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpℓ : p ≠ ℓ) (hq : ¬ 5 ∣ ℓ ^ f + 1)
    (E : Subgroup (StatedProj (StatedSU 5 (ℓ ^ f) K))) [CFSG.IsElementaryAbelian p E]
    (hcard : Nat.card E = p ^ 2) :
    Subgroup.closure {k : StatedProj (StatedSU 5 (ℓ ^ f) K) |
      ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  refine closure_centralizers_statedProj_unitary_of_lift h hp (by norm_num) ?_ E hcard ?_
  · intro hd
    have h5 : p ∣ 5 := hd.trans (Nat.gcd_dvd_left _ _)
    have hp5' : p = 5 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h5
    subst hp5'
    exact hq (hd.trans (Nat.gcd_dvd_right _ _))
  · intro E' hc he hcd
    exact closure_centralizers_unitarySU_four_five (n := 4) h hp hp5 hpℓ (Or.inr rfl) E' hc he hcd

theorem extSeitzAtInner_twistedA_three (q : TauCeti.PrimePower) :
    ExtSeitzAtInner (.twistedA 3 q) := by
  intro K _ _ _ hnab ⟨hv, ⟨e0⟩⟩ p hp hp5 hpd E hE hcard hinner
  have : Fact p.Prime := ⟨hp⟩
  left
  have hU := CFSG.RankThree.PartTwo.Census.unitaryFieldData_galoisField
    (TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv⟩)
    (TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 q, hv⟩)
    (TauCeti.ValidLieTypeIndex.fieldExponent_pos ⟨.twistedA 3 q, hv⟩)
  have e1 := e0.trans (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 3 q hv)
  refine closure_fixUnion_eq_top_of_inner_equiv hnab e1 (p := p) ?_ E hcard hinner
  intro E₁ hE₁ hcard₁
  exact closure_centralizers_statedProj_su_four hU hp hp5 hpd E₁ hcard₁

theorem extSeitzAtInner_twistedA_four_of_not_dvd {q : TauCeti.PrimePower}
    (hq : ¬ 5 ∣ q.p ^ q.exponent + 1) : ExtSeitzAtInner (.twistedA 4 q) := by
  intro K _ _ _ hnab ⟨hv, ⟨e0⟩⟩ p hp hp5 hpd E hE hcard hinner
  have : Fact p.Prime := ⟨hp⟩
  left
  have hU := CFSG.RankThree.PartTwo.Census.unitaryFieldData_galoisField
    (TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 4 q, hv⟩)
    (TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 4 q, hv⟩)
    (TauCeti.ValidLieTypeIndex.fieldExponent_pos ⟨.twistedA 4 q, hv⟩)
  have hq' : ¬ 5 ∣ TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 4 q, hv⟩ ^
      TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 4 q, hv⟩ + 1 := by
    simpa [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
      using hq
  have e1 := e0.trans (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 4 q hv)
  refine closure_fixUnion_eq_top_of_inner_equiv hnab e1 (p := p) ?_ E hcard hinner
  intro E₁ hE₁ hcard₁
  exact closure_centralizers_statedProj_su_five hU hp hp5 hpd hq' E₁ hcard₁

end CFSG.RankThree.PartOne.CTP
