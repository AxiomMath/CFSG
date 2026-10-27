module

public import CFSG.RankThree.PartOne.CTP.SeitzMaxAbstract
public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldFixed
public import CFSG.RankThree.PartOne.S11d.PSpGood
public import CFSG.RankThree.PartOne.KC.LinearSubfieldInclusion
public import CFSG.RankThree.PartOne.CTP.SeitzSpIndex

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.RankThree.PartOne.KCSpComm CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.RankThree.PartOne (card_semilinearFixedSubfield)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)
open TauCeti

section Defs

variable {r : ℕ} {K : Type} [Field K]

@[expose] def spSub (r : ℕ) {K : Type} [Field K] (k : Subfield K) : Subgroup (StatedSp r K) :=
  (subfieldSpHom r k).range

@[expose] def SubfieldPairSp (r : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Finite K], CharP K 2 → ∀ (k : Subfield K) (p : ℕ), p.Prime → 5 ≤ p →
    Nat.card K = Nat.card k ^ p → ∀ A : gsp r K,
      (spSub r k).map (conjSp r K A).toMonoidHom ≠ spSub r k →
      Subgroup.closure ((spSub r k : Set (StatedSp r K)) ∪
        ((spSub r k).map (conjSp r K A).toMonoidHom : Set (StatedSp r K))) = ⊤

end Defs

section Fixed

variable {r : ℕ} {K : Type} [Field K]

theorem range_subfieldProj_eq_map (σ : K ≃+* K) :
    (subfieldProj (r := r) σ).range = (spSub r (descentField σ)).map (proj r K) := by
  rw [subfieldProj, MonoidHom.range_comp]
  rfl

theorem map_conjAut_map_proj (k : Subfield K) (A : gsp r K) :
    ((spSub r k).map (proj r K)).map
        (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.conjAut r K A).toMonoidHom =
      ((spSub r k).map (conjSp r K A).toMonoidHom).map (proj r K) := by
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl

theorem fixedSubgroup_fieldAut_eq_range_sp [NeZero r] {p : ℕ} (hp : Odd p) {σ : K ≃+* K}
    (hσp : σ ^ p = 1) :
    fixedSubgroup (fieldAut r K σ) = (subfieldProj σ).range := by
  have h := spFixedGroup_fieldAut_eq_range (r := r) hp hσp
  ext x
  exact Iff.of_eq (congrArg (x ∈ ·) h)

theorem eq_one_of_central_statedSp [NeZero r] {k : Type} [Field k] [CharP k 2]
    {g : StatedSp r k} (hg : g ∈ Subgroup.center (StatedSp r k)) : g = 1 := by
  rw [CFSG.LieType.Universal.Symplectic.center_eq] at hg
  obtain ⟨c, hc⟩ := hg
  have hc' : (g : GL (Fin r ⊕ Fin r) k) = GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c := hc.symm
  have hc2 : c ^ 2 = 1 := by
    have hmem : (g : GL (Fin r ⊕ Fin r) k) ∈ StatedSp r k := g.2
    rw [hc'] at hmem
    exact (CFSG.LieType.Classical.scalar_mem_statedSp_iff NeZero.one_le c).mp hmem
  have hc1 : c = 1 := by
    have h1 : (c : k) ^ 2 = 1 := by simpa using congrArg Units.val hc2
    have h2 : ((c : k) + 1) ^ 2 = 0 := by
      rw [CharTwo.add_sq, one_pow, h1, CharTwo.add_self_eq_zero]
    have h3 : (c : k) + 1 = 0 := (pow_eq_zero_iff two_ne_zero).mp h2
    exact Units.ext (by
      calc (c : k) = -1 := eq_neg_of_add_eq_zero_left h3
        _ = 1 := CharTwo.neg_eq 1
        _ = ((1 : kˣ) : k) := rfl)
  refine Subtype.ext ?_
  rw [hc', hc1, map_one]
  rfl

end Fixed

section Main

variable {r : ℕ}

theorem fieldAutData_projectiveSp (hr : 2 ≤ r) (hpair : SubfieldPairSp r) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {K : Type} [Field K] [Finite K]
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) :
    FieldAutData (StatedProj (StatedSp r K)) p := by
  classical
  have : CharP K 2 := charP_two_of_card hK
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero r := ⟨by omega⟩
  have hp2 : p ≠ 2 := by omega
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hcyc : IsCyclic (K ≃+* K) := isCyclic_ringEquiv_of_card Nat.prime_two hf hK
  have O : SpOuter 2 f r K := spOuter Nat.prime_two hf hr hK
  have hinj : Function.Injective (proj r K) := proj_injective_sp hK hf (by omega)
  refine fieldAutData_of_standard (spLinearAutGroup r K)
    {g | ∃ σ : K ≃+* K, orderOf σ = p ∧ g = fieldAut r K σ} ?_ ?_ ?_ ?_ ?_
  ·
    intro E hE hEc
    by_cases hEH : E ≤ inner (StatedProj (StatedSp r K))
    · obtain ⟨a, haE, ha1⟩ : ∃ a ∈ E, a ≠ 1 := by
        by_contra hcon
        push Not at hcon
        have hbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).2 hcon
        rw [hbot, Subgroup.card_bot] at hEc
        have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
        omega
      obtain ⟨g, rfl⟩ := hEH haE
      refine ⟨g, ?_, haE⟩
      rintro rfl
      exact ha1 (map_one _)
    · have hcard := card_inf_inner_eq_prime O hr hp hp2 hcyc hEc hEH
      have h1 : (E ⊓ inner (StatedProj (StatedSp r K)) :
          Subgroup (MulAut (StatedProj (StatedSp r K)))) ≠ ⊥ := by
        rw [← Subgroup.one_lt_card_iff_ne_bot, hcard]
        exact hp.one_lt
      obtain ⟨⟨a, haE, haI⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h1
      obtain ⟨g, rfl⟩ := haI
      refine ⟨g, ?_, haE⟩
      rintro rfl
      exact ha1 (Subtype.ext (map_one _))
  ·
    intro α hα
    obtain ⟨hord, hout⟩ := hα
    have hαp : α ^ p = 1 := hord ▸ pow_orderOf_eq_one α
    have hαE : α ∈ spSemilinearAutGroup r K :=
      mem_of_odd_orderOf_of_index_dvd_two _ O.index_dvd (hord ▸ hpodd)
    have hαD : α ∉ spLinearAutGroup r K := fun hD => by
      have := inner_normal (StatedProj (StatedSp r K))
      obtain ⟨g, hg⟩ := mem_of_pow_eq_one_of_relIndex_dvd_two
        (O.relIndex_dvd.trans (Nat.gcd_dvd_left 2 _)) hp hp2 hD hαp
      exact hout g hg.symm
    obtain ⟨-, σ, hσord, h, hhD, hαh⟩ := O.descent p hp α hαE hαD hord
    exact ⟨h, hhD, fieldAut r K σ, ⟨σ, hσord, rfl⟩, hαh⟩
  ·
    rintro _ ⟨σ, hσ, rfl⟩ _ ⟨τ, hτ, rfl⟩
    have hσp : σ ^ p = 1 := hσ ▸ pow_orderOf_eq_one σ
    have hτp : τ ^ p = 1 := hτ ▸ pow_orderOf_eq_one τ
    have hfield : descentField σ = descentField τ :=
      fixedField_eq_of_orderOf Nat.prime_two hf hK hσ hτ
    rw [fixedSubgroup_fieldAut_eq_range_sp hpodd hσp, fixedSubgroup_fieldAut_eq_range_sp hpodd hτp,
      range_subfieldProj_eq_map, range_subfieldProj_eq_map, hfield]
  ·
    rintro _ ⟨σ, hσ, rfl⟩ _ x hx hcomm
    have hσp : σ ^ p = 1 := hσ ▸ pow_orderOf_eq_one σ
    rw [fixedSubgroup_fieldAut_eq_range_sp hpodd hσp] at hx hcomm
    obtain ⟨g₀, rfl⟩ := hx
    have hcard : Nat.card (descentField σ) = 2 ^ (f / p) :=
      (card_semilinearFixedSubfield Nat.prime_two hf hK hσ).2
    have : CharP (descentField σ) 2 := inferInstance
    have hcen : g₀ ∈ Subgroup.center (StatedSp r (descentField σ)) := by
      rw [Subgroup.mem_center_iff]
      intro h₀
      have h1 := hcomm (subfieldProj σ h₀) ⟨h₀, rfl⟩
      apply subfieldSpHom_injective (descentField σ)
      apply hinj
      rw [map_mul, map_mul, map_mul, map_mul]
      exact h1.symm
    rw [eq_one_of_central_statedSp hcen, map_one]
  ·
    rintro _ ⟨σ, hσ, rfl⟩ d hd hne
    left
    obtain ⟨A, rfl⟩ := mem_spLinearAutGroup_iff.mp hd
    have hσp : σ ^ p = 1 := hσ ▸ pow_orderOf_eq_one σ
    rw [fixedSubgroup_fieldAut_eq_range_sp hpodd hσp, range_subfieldProj_eq_map] at hne ⊢
    set k := descentField σ with hk
    have hpf : p ∣ f ∧ Nat.card k = 2 ^ (f / p) :=
      card_semilinearFixedSubfield Nat.prime_two hf hK hσ
    have hcardK : Nat.card K = Nat.card k ^ p := by
      rw [hK, hpf.2, ← pow_mul, Nat.div_mul_cancel hpf.1]
    have hne' : (spSub r k).map (conjSp r K A).toMonoidHom ≠ spSub r k := by
      intro h
      apply hne
      rw [map_conjAut_map_proj, h]
    have hgen := hpair K inferInstance k p hp hp5 hcardK A hne'
    have h4 := congrArg (Subgroup.map (proj r K)) hgen
    rw [map_closure_union, Subgroup.map_top_of_surjective _ proj_surjective] at h4
    rw [map_conjAut_map_proj]
    exact h4

theorem extSeitzAtOuter_B_of_pair {r : ℕ} (hr2 : 2 ≤ r) (hr3 : r ≤ 3)
    (hpair : SubfieldPairSp r) {q : PrimePower} (hq2 : q.p = 2) :
    ExtSeitzAtOuter (.B r q) := by
  intro K _ _ _ hnab ⟨hv, ⟨e0⟩⟩ p hp hp5 hpd E hE hc hout
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : Fact p.Prime := ⟨hp⟩
  have hF := card_fixedField_B r q hv
  have : Finite ↥(ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) :=
    Nat.finite_of_card_ne_zero (by rw [hF]; exact pow_ne_zero _ q.prime_p.ne_zero)
  have hF2 : Nat.card ↥(ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) = 2 ^ q.exponent := by
    rw [hF, hq2]
  obtain ⟨e⟩ : Nonempty
      (K ≃* StatedProj (StatedSp r ↥(ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩))) := by
    rcases Nat.lt_or_ge r 3 with h2 | h3
    · obtain rfl : r = 2 := by omega
      exact ⟨e0.trans (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv)⟩
    · obtain rfl : r = 3 := by omega
      exact ⟨e0.trans (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj 3 q hv
        hq2 h3)⟩
  have hd : FieldAutData K p :=
    (fieldAutData_projectiveSp hr2 hpair hp hp5 q.exponent_pos hF2).of_mulEquiv e hp
  left
  exact closure_fixUnion_eq_top_of_fieldAutData hnab hp hd E hc hout

end Main

end CFSG.RankThree.PartOne.CTP
