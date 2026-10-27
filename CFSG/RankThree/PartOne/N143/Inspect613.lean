module

public import CFSG.RankThree.PartOne.N143.SectionReduce
public import CFSG.RankThree.PartOne.Census3.Interface
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
import CFSG.Dihedral.DihedralFusionAutomorphisms
import CFSG.Dihedral.PerfectDihedralFourgroupAction
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalPSLTwoSections
import CFSG.Adapters.LinearCatalog

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly CFSG.RankThree.PartOne.Census3 TauCeti
open scoped commutatorElement

@[expose] def Item613At (X : Type) [Group X] : Prop :=
  ∀ p : ℕ, p.Prime → 7 ≤ p → ∀ E : Subgroup X, CFSG.IsElementaryAbelian p E → p ^ 2 ≤ Nat.card E →
    (∃ S : Subgroup X, S ≠ ⊥ ∧ IsPGroup 2 S ∧ E ≤ Subgroup.normalizer (S : Set X) ∧ ⁅S, E⁆ = S) →
    CFSG.Blueprint.EvenLieType X

@[expose] def ThmThreeCatalog : Prop :=
  ∀ (G : Type) [Group G] [Finite G], TheoremThreeHyp G → TheoremThreeList G

@[expose] def Item613List : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → TheoremThreeList X → Item613At X

theorem item613Simple_of_list (hT : ThmThreeCatalog) (hL : Item613List) : Item613Simple := by
  intro X _ _ hsimple hnonab hK he p hp hp7 E hE hcard hex
  have hhyp : TheoremThreeHyp X :=
    ⟨hsimple, hnonab, hK, by rw [← CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank]; exact he⟩
  exact hL X hsimple (hT X hhyp) p hp hp7 E hE hcard hex

@[expose] def Item613Item1 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → ThmThreeItem1 X → Item613At X
@[expose] def Item613Item2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → ThmThreeItem2 X → Item613At X
@[expose] def Item613Item3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → ThmThreeItem3 X → Item613At X
@[expose] def Item613Item4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → ThmThreeItem4 X → Item613At X
@[expose] def Item613Item5 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → ThmThreeItem5 X → Item613At X
@[expose] def Item613Item6 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → ThmThreeItem6 X → Item613At X
@[expose] def EvenListBridge : Prop :=
  ∀ (X : Type) [Group X] [Finite X], (ThmThreeItem7 X ∨ ThmThreeItem8 X ∨ ThmThreeItem9 X) →
    CFSG.Blueprint.EvenLieType X

theorem item613List_of_items (h1 : Item613Item1) (h2 : Item613Item2) (h3 : Item613Item3)
    (h4 : Item613Item4) (h5 : Item613Item5) (h6 : Item613Item6) (hE : EvenListBridge) :
    Item613List := by
  intro X _ _ hs h
  rcases h with h | h | h | h | h | h | h | h | h
  · exact h1 X hs h
  · exact h2 X hs h
  · exact h3 X hs h
  · exact h4 X hs h
  · exact h5 X hs h
  · exact h6 X hs h
  · exact fun _ _ _ _ _ _ _ => hE X (Or.inl h)
  · exact fun _ _ _ _ _ _ _ => hE X (Or.inr (Or.inl h))
  · exact fun _ _ _ _ _ _ _ => hE X (Or.inr (Or.inr h))

theorem not_sq_dvd_factorial_of_le_twelve {n p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hn : n ≤ 12) :
    ¬ p ^ 2 ∣ Nat.factorial n := by
  intro h
  have hpn : p ∣ Nat.factorial n := (dvd_pow_self p two_ne_zero).trans h
  have hp12 : p ≤ 12 := ((hp.dvd_factorial).1 hpn).trans hn
  have key : ∀ m ≤ 12, ¬ 7 ^ 2 ∣ Nat.factorial m ∧ ¬ 11 ^ 2 ∣ Nat.factorial m := by decide +kernel
  interval_cases p
  · exact (key n hn).1 h
  · exact absurd hp (by norm_num)
  · exact absurd hp (by norm_num)
  · exact absurd hp (by norm_num)
  · exact (key n hn).2 h
  · exact absurd hp (by norm_num)

theorem item613Item5 : Item613Item5 := by
  rintro X _ _ - ⟨n, hn5, hn12, ⟨e⟩⟩ p hp hp7 E hE hcard -
  exfalso
  have : Fact p.Prime := ⟨hp⟩
  have hEp : IsPGroup p E := by
    have := hE
    exact IsElementaryAbelian.isPGroup p E
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hEp
  have hk2 : 2 ≤ k := (Nat.pow_le_pow_iff_right hp.one_lt).1 (hk ▸ hcard)
  have hdvdE : p ^ 2 ∣ Nat.card E := by
    rw [hk]
    exact pow_dvd_pow p hk2
  have hdvd : p ^ 2 ∣ Nat.card X := hdvdE.trans (Subgroup.card_subgroup_dvd_card E)
  have hX : Nat.card X = Nat.factorial n / 2 := by
    have : Nontrivial (Fin n) := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
  rw [hX] at hdvd
  have h2n : 2 ∣ Nat.factorial n := Nat.dvd_factorial (by norm_num) (by omega)
  exact not_sq_dvd_factorial_of_le_twelve hp hp7 hn12 (hdvd.trans (Nat.div_dvd_of_dvd h2n))

theorem no_action_of_dihedral {X : Type} [Group X] [Finite X]
    (hd : GorensteinWalter.HasDihedralSylowTwo X) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {E S : Subgroup X} (hE : ∀ x ∈ E, x ^ p = 1) (hS : IsPGroup 2 S)
    (hN : E ≤ Subgroup.normalizer (S : Set X)) : E ≤ Subgroup.centralizer (S : Set X) := by
  classical
  obtain ⟨T, hST⟩ := hS.exists_le_sylow
  obtain ⟨m, hm, ⟨eT⟩⟩ := hd T
  let φ : E →* MulAut S := S.normalizerMonoidHom.comp (Subgroup.inclusion hN)
  have hφ : ∀ x : E, φ x = 1 := by
    intro x
    have hxp : x ^ p = 1 := Subtype.ext (hE x x.2)
    have hord : orderOf (φ x) ∣ p :=
      (orderOf_map_dvd φ x).trans (orderOf_dvd_of_pow_eq_one hxp)
    have hne : orderOf (φ x) ≠ p := by
      intro hop
      by_cases hk : IsKleinFour S
      · have h6 : Nat.card (MulAut S) = 6 := GorensteinWalter.kleinFourAut_card S
        have hdv : orderOf (φ x) ∣ 6 := h6 ▸ orderOf_dvd_natCard (φ x)
        rw [hop] at hdv
        have h23 : p ∣ 2 * 3 := by simpa using hdv
        rcases (Nat.Prime.dvd_mul hp).1 h23 with h2 | h3
        · have := Nat.le_of_dvd (by norm_num) h2
          omega
        · have := Nat.le_of_dvd (by norm_num) h3
          omega
      · have hM : IsPGroup 2 (MulAut S) :=
          GorensteinWalter.dihedral_subgroup_automorphism_isTwoGroup T hm eT S hST hk
        obtain ⟨j, hj⟩ := hM (φ x)
        have hdv : p ∣ 2 ^ j := hop ▸ orderOf_dvd_of_pow_eq_one hj
        have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow hdv)
        omega
    exact orderOf_eq_one_iff.1 ((Nat.dvd_prime hp).1 hord |>.resolve_right hne)
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have h1 : (φ ⟨x, hx⟩) ⟨s, hs⟩ = ⟨s, hs⟩ := by rw [hφ ⟨x, hx⟩]; rfl
  have h2 : x * s * x⁻¹ = s := congrArg Subtype.val h1
  calc s * x = (x * s * x⁻¹) * x := by rw [h2]
    _ = x * s := by group

theorem item613Item1 : Item613Item1 := by
  rintro X _ _ - ⟨q, hq2, -, hv, ⟨e⟩⟩ p hp hp7 E hE - ⟨S, hS1, hS2, hEN, hSE⟩
  exfalso
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hcard : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card q.p q.exponent q.exponent_pos.ne'
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField q.p q.exponent)) :=
    ⟨q.p, q.exponent, q.prime_p, q.prime_p.eq_two_or_odd'.resolve_left hq2, q.exponent_pos, hcard⟩
  let eP : X ≃* GorensteinWalter.PSL2 (GaloisField q.p q.exponent) :=
    e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv)
  have hd : GorensteinWalter.HasDihedralSylowTwo X :=
    CFSG.ComponentClassification.OutcomeLocal.hasDihedralSylowTwo_of_mulEquiv eP
      (GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model _ hodd)
  have hEp : ∀ x ∈ E, x ^ p = 1 := by
    intro x hx
    have := hE
    exact elemPow_eq_one_of_isElementaryAbelian x hx
  have hcent := no_action_of_dihedral hd hp (by omega) hEp hS2 hEN
  have hcomm : ⁅E, S⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hcent
  apply hS1
  rw [← hSE, Subgroup.commutator_comm]
  exact hcomm

theorem item613List_of_inspections (hE : EvenListBridge) (h2 : Item613Item2) (h3 : Item613Item3)
    (h4 : Item613Item4) (h6 : Item613Item6) : Item613List :=
  item613List_of_items item613Item1 h2 h3 h4 item613Item5 h6 hE

theorem item613_of_inspections (hB : ThetaQuotientBookkeeping) (hT : ThmThreeCatalog)
    (hE : EvenListBridge) (h2 : Item613Item2) (h3 : Item613Item3) (h4 : Item613Item4)
    (h6 : Item613Item6) : Item613 :=
  item613_of_simple hB (item613Simple_of_list hT (item613List_of_inspections hE h2 h3 h4 h6))

end CFSG.RankThree.PartOne.N143
