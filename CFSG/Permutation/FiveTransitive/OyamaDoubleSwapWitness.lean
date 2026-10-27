module

public import CFSG.Permutation.FiveTransitive.SixDoubleSwapNormalizerRepresentative
public import CFSG.Permutation.FiveTransitive.OyamaOrderFourWitness

public section

namespace CFSG

namespace FiveTransitive.OyamaDoubleSwapWitness

open MulAction Equiv CyclePatternRoots

theorem exists_witness
    (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hX : 10 ≤ Fintype.card X) (h4 : IsMultiplyPretransitive G X 4)
    (e : Fin 4 ↪ X) (S : Sylow 2 (fixingSubgroup G (Set.range e))) [Nontrivial S]
    (hfree : ∀ (q : S) (x : X), x ∉ fixedPoints S X → q • x = x → q = 1)
    (hcard : (fixedPoints S X).ncard = 6)
    (himage : let Q := (S : Subgroup (fixingSubgroup G (Set.range e))).map (fixingSubgroup G (Set.range e)).subtype
      letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (OyamaSixElementary.fixedHom G X Q).range = alternatingGroup (fixedPoints Q X))
    (hS : Nat.card S = 16) :
    ∃ a : G, orderOf a = 4 ∧
      (∀ i, a • e i = e (CyclePatternFinite.doubleTwo i)) ∧
      fixedBy X (a ^ 2) = fixedPoints S X ∧
      fixedBy X a = fixedPoints S X \ Set.range e := by
  classical
  let s := Set.range e
  let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
  have hs : s.ncard = 4 := by
    simpa only [Nat.card_fin] using Set.ncard_range_of_injective e.injective
  obtain ⟨b,_,hb,_,_,_,_⟩ := OyamaOrderFourWitness.exists_order_four_normalizer
    G X hX h4 s hs S hfree hcard himage hS
  have htwo := (OyamaOrderFourShape.fixed_two_and_two_root_four
    G X hX h4 s hs S hfree hcard himage hS b hb).2
  change Nat.card (TwoRoot (toPermHom G X b)) = 4 at htwo
  have hF : fixedPoints Q X = fixedPoints S X :=
    OyamaSixElementary.fixedPoints_image G X (fixingSubgroup G s) S
  have hcQ : (fixedPoints Q X).ncard = 6 := by rw [hF,hcard]
  have heven := OyamaSixOrderUpper.even_of_alternating_image G X Q himage
  obtain ⟨a,_,E,hE,ha,heF,hsq,hfix⟩ := SixDoubleSwapNormalizerRepresentative.exists_conjugate
    G X h4 s S hcQ heven e rfl b hb (by omega)
  have hpat : ∀ i, a • e i = e (CyclePatternFinite.doubleTwo i) := by
    intro i
    have h := E.property i
    change a • E.val i = E.val (CyclePatternFinite.doubleTwo i) at h
    simpa only [hE] using h
  have ha2 : orderOf (a ^ 2) = 2 := by rw [orderOf_pow,ha]; norm_num
  have hcard2 := OyamaSixOrderSixteen.involution_fixed_six
    G X hX h4 s hs S hfree hcard himage hS (a ^ 2) ha2
  have hsub : fixedPoints Q X ⊆ fixedBy X (a ^ 2) := hsq
  have heq : fixedPoints Q X = fixedBy X (a ^ 2) :=
    Set.eq_of_subset_of_ncard_le hsub (by omega)
  have haF : fixedBy X a ⊆ fixedPoints Q X := by
    intro x hx
    rw [heq]
    change a ^ 2 • x = x
    change a • x = x at hx
    rw [pow_two,mul_smul,hx,hx]
  have hfixcard : (fixedBy X a).ncard = 2 := by
    rwa [Set.inter_eq_left.mpr haF] at hfix
  have hbase : s ⊆ fixedPoints Q X := by
    simpa only [hE] using heF
  have hne : ∀ i : Fin 4, CyclePatternFinite.doubleTwo i ≠ i := by decide
  have hfixsub : fixedBy X a ⊆ fixedPoints Q X \ s := by
    intro x hx
    refine ⟨haF hx,?_⟩
    rintro ⟨i,rfl⟩
    apply hne i
    apply e.injective
    exact (hpat i).symm.trans hx
  have hfixeq : fixedBy X a = fixedPoints Q X \ s :=
    Set.eq_of_subset_of_ncard_le hfixsub (by rw [Set.ncard_sdiff hbase,hcQ,hs,hfixcard])
  exact ⟨a,ha,hpat,heq.symm.trans hF,by simpa only [hF] using hfixeq⟩

end FiveTransitive.OyamaDoubleSwapWitness

end CFSG
