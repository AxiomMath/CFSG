module

public import CFSG.RankThree.PartTwo.Sec18.Notation
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.Sec18.SylowFiveOmega
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item1810Proof

open CFSG CFSG.RankThree.PartTwo
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

private theorem pow_three_eq_one_of_exponent {V : Subgroup G} (hV : Monoid.exponent V = 3)
    {v : G} (hv : v ∈ V) : v ^ 3 = 1 := by
  have h : (⟨v, hv⟩ : V) ^ 3 = 1 := by
    rw [← hV]
    exact Monoid.pow_exponent_eq_one _
  exact congrArg Subtype.val h

theorem card_and_pow_three_of_isZ3TimesHeis [Finite G] {X : Subgroup G}
    (hX : IsZ3TimesHeis X) : Nat.card X = 81 ∧ ∀ x ∈ X, x ^ 3 = 1 := by
  obtain ⟨U, V, hUV, hinf, hU3, hV, hUC⟩ := hX
  obtain ⟨-, hV27, hVexp⟩ := hV
  have hUN : U ≤ Subgroup.normalizer (V : Set G) :=
    hUC.trans (Subgroup.centralizer_le_normalizer _)
  have hcomm : ∀ u ∈ U, ∀ v ∈ V, Commute u v := fun u hu v hv =>
    ((Subgroup.mem_centralizer_iff.mp (hUC hu)) v hv).symm
  have hU3' : ∀ u ∈ U, u ^ 3 = 1 := by
    intro u hu
    have h : (⟨u, hu⟩ : U) ^ 3 = 1 := by
      rw [← hU3]
      exact pow_card_eq_one'
    exact congrArg Subtype.val h
  subst hUV
  have hcard : Nat.card (U ⊔ V : Subgroup G) = 81 := by
    have h1 := Sec6.card_sup_mul_card_inf hUN
    rw [hinf, Subgroup.card_bot, mul_one, hU3, hV27] at h1
    omega
  refine ⟨hcard, fun x hx => ?_⟩
  have hx' : x ∈ (U : Set G) * (V : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right U V hUN]
    exact hx
  obtain ⟨u, hu, v, hv, rfl⟩ := hx'
  rw [(hcomm u hu v hv).mul_pow 3, hU3' u hu, pow_three_eq_one_of_exponent hVexp hv, one_mul]

theorem le_normalizer_and_card_inf [Finite G] {X Y Z : Subgroup G} (hX : Nat.card X = 81)
    (hYX : Y ≤ X) (hZX : Z ≤ X) (hY : Nat.card Y = 27) (hZ : Nat.card Z = 27) (hYZ : Y ≠ Z) :
    Y ≤ Subgroup.normalizer (Z : Set G) ∧ Nat.card (Y ⊓ Z : Subgroup G) = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (IsPGroup 3 X) := ⟨IsPGroup.of_card (n := 4) (hX.trans (by norm_num))⟩
  have hidx : (Z.subgroupOf X).index = 3 := by
    have h1 := Subgroup.card_mul_index (Z.subgroupOf X)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZX).toEquiv, hZ, hX] at h1
    omega
  have hZn : (Z.subgroupOf X).Normal :=
    CFSG.coatom_normal_of_isPGroup (p := 3)
      (Subgroup.isCoatom_of_index_prime (by rw [hidx]; exact Nat.prime_three))
  have hYN : Y ≤ Subgroup.normalizer (Z : Set G) :=
    hYX.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hZX).mp hZn)
  refine ⟨hYN, ?_⟩
  have hdvd1 : Nat.card (Y ⊔ Z : Subgroup G) ∣ 81 := by
    have := Subgroup.card_dvd_of_le (sup_le hYX hZX)
    rwa [hX] at this
  have hdvd2 : 27 ∣ Nat.card (Y ⊔ Z : Subgroup G) := by
    have := Subgroup.card_dvd_of_le (le_sup_left : Y ≤ Y ⊔ Z)
    rwa [hY] at this
  have key : Nat.card (Y ⊔ Z : Subgroup G) = 27 ∨ Nat.card (Y ⊔ Z : Subgroup G) = 81 := by
    obtain ⟨k, hk⟩ := hdvd2
    rw [hk] at hdvd1 ⊢
    have hk3 : k ≤ 3 := by
      have := Nat.le_of_dvd (by norm_num) hdvd1
      omega
    interval_cases k
    · norm_num at hdvd1
    · left
      norm_num
    · norm_num at hdvd1 <;> omega
    · right
      norm_num
  have hS81 : Nat.card (Y ⊔ Z : Subgroup G) = 81 := by
    rcases key with h27 | h81
    · exfalso
      have hYS : Y = Y ⊔ Z := Subgroup.eq_of_le_of_card_ge le_sup_left (by omega)
      have hZS : Z = Y ⊔ Z := Subgroup.eq_of_le_of_card_ge le_sup_right (by omega)
      exact hYZ (hYS.trans hZS.symm)
    · exact h81
  have hprod := Sec6.card_sup_mul_card_inf hYN
  rw [hS81, hY, hZ] at hprod
  omega

theorem sup_zpowers_isElemAbelian [Finite G] {E : Subgroup G} {d : G}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hEd : E ≤ Subgroup.centralizer ({d} : Set G))
    (hd3 : d ^ 3 = 1) (hdE : d ∉ E) :
    CFSG.Assembly.IsElemAbelian 3 (E ⊔ Subgroup.zpowers d) ∧
      Nat.card (E ⊔ Subgroup.zpowers d : Subgroup G) = 3 * Nat.card E := by
  have hd1 : d ≠ 1 := fun h => hdE (h ▸ E.one_mem)
  have hcomm : ∀ a ∈ E, ∀ b ∈ Subgroup.zpowers d, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have had : Commute a d := Subgroup.mem_centralizer_singleton_iff.mp (hEd ha)
    exact (had.zpow_right k).eq
  have hdC : d ∈ Subgroup.centralizer (E : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun e he =>
      Subgroup.mem_centralizer_singleton_iff.mp (hEd he)
  have hzE : Subgroup.zpowers d ≤ Subgroup.normalizer (E : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hdC)
  refine ⟨CFSG.Open.IsElemAbelian.sup_of_commute hE (CFSG.Open.isElemAbelian_zpowers hd3) hcomm,
    ?_⟩
  have hz3 : Nat.card (Subgroup.zpowers d) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hd3 hd1]
  have h1 := Sec6.card_sup_mul_card_inf hzE
  rw [SylowFive.zpowers_inf_eq_bot hd3 hdE, Subgroup.card_bot, mul_one, hz3] at h1
  rw [sup_comm]
  exact h1

theorem omegaOneThree_map_conj (P : Subgroup G) (x : G) :
    omegaOneThree (P.map (MulAut.conj x).toMonoidHom) =
      (omegaOneThree P).map (MulAut.conj x).toMonoidHom := by
  unfold omegaOneThree
  rw [MonoidHom.map_closure]
  congr 1
  ext z
  constructor
  · rintro ⟨hzP, hz3⟩
    obtain ⟨y, hyP, rfl⟩ := Subgroup.mem_map.mp hzP
    refine ⟨y, ⟨hyP, ?_⟩, rfl⟩
    apply (MulAut.conj x).injective
    rw [map_pow, map_one]
    exact hz3
  · rintro ⟨y, ⟨hyP, hy3⟩, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem _ hyP, ?_⟩
    rw [← map_pow, hy3, map_one]

theorem le_omegaOneThree {E P : Subgroup G} (hEP : E ≤ P) (hE : ∀ e ∈ E, e ^ 3 = 1) :
    E ≤ omegaOneThree P := by
  intro e he
  exact Subgroup.subset_closure ⟨hEP he, hE e he⟩

theorem commutator_mem_frattini [Finite G] {p : ℕ} [Fact p.Prime] {X : Subgroup G}
    (hX : IsPGroup p X) {a e : G} (ha : a ∈ X) (he : e ∈ X) :
    a * e * a⁻¹ * e⁻¹ ∈ (frattini X).map X.subtype := by
  haveI : Fact (IsPGroup p X) := ⟨hX⟩
  have hmem : ⁅(⟨a, ha⟩ : X), (⟨e, he⟩ : X)⁆ ∈ _root_.commutator X :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hc : ⁅(⟨a, ha⟩ : X), (⟨e, he⟩ : X)⁆ ∈ frattini X :=
    CFSG.commutator_le_frattini_of_isPGroup (R := ↥X) (p := p) hmem
  have heq : X.subtype ⁅(⟨a, ha⟩ : X), (⟨e, he⟩ : X)⁆ = a * e * a⁻¹ * e⁻¹ := by
    simp [commutatorElement_def]
  rw [← heq]
  exact Subgroup.mem_map_of_mem X.subtype hc

end CFSG.RankThree.PartTwo.Sec18.Item1810Proof
