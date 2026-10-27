module

public import CFSG.LieType.Chevalley.OrdinaryRootCentralizerGeneration
public import CFSG.Adapters.TauCetiExceptional.EvenB1
public import CFSG.LieType.Chevalley.ExactG2FiniteOrder
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
public import CFSG.RankThree.PartOne.CTP.SeitzFineDefs

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree TauCeti
  CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.RankThree.PartOne.Census3 (IsoLie)

section Arith

theorem not_dvd_g2_index_aux {p a : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (ha : p ∣ a) :
    ¬ p ∣ (a + 2) ^ 2 * (a ^ 2 + 3 * a + 3) * (a ^ 2 + a + 1) := by
  intro h
  have : Fact p.Prime := ⟨hp⟩
  have h' : (((a + 2) ^ 2 * (a ^ 2 + 3 * a + 3) * (a ^ 2 + a + 1) : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr h
  have ha' : (a : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr ha
  push_cast at h'
  rw [ha'] at h'
  norm_num at h'
  have h12 : ((12 : ℕ) : ZMod p) = 0 := by
    exact_mod_cast (by linear_combination h' : (12 : ZMod p) = 0)
  have h12' : p ∣ 12 := (ZMod.natCast_eq_zero_iff _ _).mp h12
  have := Nat.le_of_dvd (by norm_num) h12'
  interval_cases p <;> first | omega | (exfalso; revert hp; decide)


theorem closure_centralizers_of_iSup_eq {G : Type*} [Group G] (C : Subgroup G) (E₁ : Subgroup C)
    (h : (⨆ a ∈ E₁.map C.subtype, ⨆ (_ : a ≠ 1), C ⊓ Subgroup.centralizer ({a} : Set G)) = C) :
    Subgroup.closure {k' : C | ∃ x ∈ E₁, x ≠ 1 ∧ k' * x = x * k'} = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hg : (g : G) ∈ ⨆ a ∈ E₁.map C.subtype, ⨆ (_ : a ≠ 1), C ⊓
      Subgroup.centralizer ({a} : Set G) := by
    rw [h]
    exact g.2
  have hle : (⨆ a ∈ E₁.map C.subtype, ⨆ (_ : a ≠ 1), C ⊓ Subgroup.centralizer ({a} : Set G)) ≤
      (Subgroup.closure {k' : C | ∃ x ∈ E₁, x ≠ 1 ∧ k' * x = x * k'}).map C.subtype := by
    refine iSup₂_le fun a ha => iSup_le fun ha1 => ?_
    obtain ⟨x, hx, rfl⟩ := ha
    have hx1 : x ≠ 1 := fun h => ha1 (by rw [h]; rfl)
    intro c hc
    obtain ⟨hcC, hcc⟩ := Subgroup.mem_inf.1 hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hcc
    exact ⟨⟨c, hcC⟩, Subgroup.subset_closure ⟨x, hx, hx1, Subtype.ext hcc⟩, rfl⟩
  obtain ⟨s, hs, hsg⟩ := hle hg
  have hsg' : s = g := Subtype.ext hsg
  rw [← hsg']
  exact hs

end Arith

section Split


theorem closure_centralizers_adjoint_of_conj_borel (τ : Tag) (k : Type) [Field k] [Finite k]
    (r p : ℕ) [Fact r.Prime] [Fact p.Prime] [CharP k r] (hrp : r ≠ p)
    [IsSimpleGroup (adjointGroup τ k)]
    (A : Subgroup (ModGL τ k)) (hAC : A ≤ adjointGroup τ k) [IsElementaryAbelian p A]
    (hcard : p ^ 2 ≤ Nat.card A) (hU : posUnipotent τ k ≠ ⊥)
    (hidx : ¬ p ∣ ((borelGroup τ k).subgroupOf (adjointGroup τ k)).index) :
    (⨆ a ∈ A, ⨆ (_ : a ≠ 1), adjointGroup τ k ⊓
        Subgroup.centralizer ({a} : Set (ModGL τ k))) = adjointGroup τ k := by
  have := finite_modGL (τ := τ) (K := k)
  have hBC : borelGroup τ k ≤ adjointGroup τ k := borelGroup_le_adjointGroup'
  obtain ⟨y, hyC, hyA⟩ := exists_conj_le_of_not_dvd_index hAC
    (IsElementaryAbelian.isPGroup p A) hidx
  have hA'C : A.map (MulAut.conj y).toMonoidHom ≤ adjointGroup τ k := by
    rintro _ ⟨a, ha, rfl⟩
    exact mul_mem (mul_mem hyC (hAC ha)) (inv_mem hyC)
  have : IsElementaryAbelian p (A.map (MulAut.conj y).toMonoidHom) := IsElementaryAbelian.map _
  have hcard' : p ^ 2 ≤ Nat.card (A.map (MulAut.conj y).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj y).injective]
    exact hcard
  have hUr : IsPGroup r (posUnipotent τ k) := by
    have : Fintype k := Fintype.ofFinite k
    obtain ⟨n, -, hn⟩ := FiniteField.card k r
    refine IsPGroup.of_card (n := n * {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard) ?_
    rw [card_posUnipotent, Nat.card_eq_fintype_card, hn, ← pow_mul]
  have hAR : A.map (MulAut.conj y).toMonoidHom ≤
      Subgroup.normalizer (posUnipotent τ k : Set _) := by
    have hnorm := ((triangular_borel_structure.{0, 0} τ k).2.2.2.2.2.2.2.2.1)
    have h1 : borelGroup τ k ≤ Subgroup.normalizer (posUnipotent τ k : Set _) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).1 hnorm
    exact hyA.trans h1
  have hmain := ordinary_root_invariant_prime_subgroup_centralizer_generation τ k r p hrp
    (A.map (MulAut.conj y).toMonoidHom) hA'C hcard' (posUnipotent τ k)
    (posUnipotent_le_adjointGroup) hUr hU hAR
  refine le_antisymm (iSup₂_le fun a _ => iSup_le fun _ => inf_le_left) ?_
  exact le_iSup_inf_centralizer_of_map_conj hyC hmain.ge


theorem not_dvd_index_borel_G2 (X : Type) [Field X] [Finite X] (p : ℕ) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card X - 1) :
    ¬ p ∣ ((borelGroup .G2 X).subgroupOf (adjointGroup .G2 X)).index := by
  have hq2 : 2 ≤ Nat.card X := Finite.one_lt_card
  obtain ⟨m, hm⟩ := hpq
  have hq : Nat.card X = p * m + 1 := by omega
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0] at hm; omega
    · exact h0
  obtain ⟨hC, -⟩ := CFSG.LieType.Chevalley.exact_G2_finite_order X rfl
  have hB : Nat.card (borelGroup .G2 X) = (Nat.card X - 1) ^ 2 * Nat.card X ^ 6 := by
    rw [card_borelGroup, CFSG.Timmesfeld.ExceptionalOrders.card_torusGroup_G2, card_posUnipotent,
      CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_G2]
  have h1 := Subgroup.index_mul_card ((borelGroup .G2 X).subgroupOf (adjointGroup .G2 X))
  rw [card_subgroupOf_of_le borelGroup_le_adjointGroup', hB, hC] at h1
  have e1 : (p * m + 1) ^ 2 - 1 = (p * m) * (p * m + 2) := by
    apply Nat.sub_eq_of_eq_add; ring
  have e2 : (p * m + 1) ^ 2 - (p * m + 1) + 1 = (p * m) ^ 2 + p * m + 1 := by
    have : (p * m + 1) ^ 2 = ((p * m) ^ 2 + p * m + 1) + p * m := by ring
    omega
  rw [hq, Nat.add_sub_cancel, e1, e2] at h1
  have hK : 0 < (p * m) ^ 2 * (p * m + 1) ^ 6 := by positivity
  intro hdiv
  have hind : ((borelGroup .G2 X).subgroupOf (adjointGroup .G2 X)).index =
      (p * m + 2) ^ 2 * ((p * m) ^ 2 + 3 * (p * m) + 3) * ((p * m) ^ 2 + p * m + 1) := by
    apply Nat.eq_of_mul_eq_mul_right hK
    calc _ = _ := h1
      _ = _ := by ring
  rw [hind] at hdiv
  exact not_dvd_g2_index_aux hp hp5 (dvd_mul_right p m) hdiv

theorem closure_centralizers_adjoint_G2_split (X : Type) [Field X] [Finite X] (r p : ℕ)
    [Fact r.Prime] [Fact p.Prime] [CharP X r] (hrp : r ≠ p) (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card X - 1) [IsSimpleGroup (adjointGroup .G2 X)]
    (E₁ : Subgroup (adjointGroup .G2 X)) [IsElementaryAbelian p E₁] (hcard : Nat.card E₁ = p ^ 2) :
    Subgroup.closure {k' : adjointGroup .G2 X | ∃ x ∈ E₁, x ≠ 1 ∧ k' * x = x * k'} = ⊤ := by
  have hq2 : 2 ≤ Nat.card X := Finite.one_lt_card
  let C : Subgroup (ModGL .G2 X) := adjointGroup .G2 X
  let A : Subgroup (ModGL .G2 X) := E₁.map C.subtype
  have hAC : A ≤ C := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have : IsElementaryAbelian p A := IsElementaryAbelian.map _
  have hcardA : p ^ 2 ≤ Nat.card A := by
    rw [Subgroup.card_map_of_injective C.subtype_injective, hcard]
  have hU : posUnipotent .G2 X ≠ ⊥ := by
    intro h
    have h1 := card_posUnipotent (τ := .G2) (K := X)
    rw [h, CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_G2, Subgroup.card_bot] at h1
    have : 1 < Nat.card X ^ 6 := Nat.one_lt_pow (by norm_num) hq2
    omega
  have hmain := closure_centralizers_adjoint_of_conj_borel .G2 X r p hrp A hAC hcardA hU
    (not_dvd_index_borel_G2 X p Fact.out hp5 hpq)
  exact closure_centralizers_of_iSup_eq C E₁ hmain

end Split

section Models


theorem exists_adjointG2_model {q : TauCeti.PrimePower} {K : Type} [Group K]
    (hiso : IsoLie K (.G2 q)) :
    ∃ (X : Type) (_ : Field X) (_ : Finite X), Nat.card X = q.p ^ q.exponent ∧
      Nonempty (K ≃* adjointGroup .G2 X) := by
  obtain ⟨hv, ⟨e0⟩⟩ := hiso
  by_cases hq : q.p = 2
  · have hmodel := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
      CFSG.TauCetiBridge.Even.chevalleyBridgesEven.g2 q hv hq e0
    obtain ⟨X, _, _, hX, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hmodel
    exact ⟨X, inferInstance, inferInstance, hX, ⟨e⟩⟩
  · have hmodel := CFSG.TauCetiBridge.untwistedModel_of_bridge
      CFSG.TauCetiBridge.chevalleyBridges.g2 q hv hq e0
    obtain ⟨X, _, _, hX, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hmodel
    exact ⟨X, inferInstance, inferInstance, hX, ⟨e⟩⟩

theorem extSeitzAtInnerFor_G2_split {q : TauCeti.PrimePower} :
    ExtSeitzAtInnerFor (.G2 q) fun p => p ∣ q.card - 1 := by
  intro K _ _ _ hnab hiso p hp hp5 hpd hpq E hE hcard hinner
  left
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨X, _, _, hX, ⟨e⟩⟩ := exists_adjointG2_model hiso
  have hXq : Nat.card X = q.card := by rw [hX, PrimePower.card_def]
  have : IsSimpleGroup (adjointGroup .G2 X) := MulEquiv.isSimpleGroup e.symm
  have : CharP X q.p := finite_field_prime_power_characteristic q.prime_p q.exponent_pos hX
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  refine closure_fixUnion_eq_top_of_inner_equiv hnab e (p := p) ?_ E hcard hinner
  intro E₁ hE₁ hcard₁
  have := hE₁
  exact closure_centralizers_adjoint_G2_split X q.p p (by simpa using hpd.symm) hp5
    (by rw [hXq]; exact hpq) E₁ hcard₁

end Models

end CFSG.RankThree.PartOne.CTP
