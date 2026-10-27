module

public import CFSG.LocalAnalysis.SignalizerFunctor.Maximality
public import CFSG.SignalizerFunctorTheorem.Coprime.CommutatorGeneration
public import CFSG.Assembly.Defs

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride

variable {G : Type*} [Group G]

theorem iSup_centralizer_cyclic_quotient [Finite G] {p : ℕ} (hp : p.Prime) {A X : Subgroup G}
    [IsMulCommutative A] (hA : IsPGroup p A) (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hX : Nat.Coprime p (Nat.card X)) :
    ⨆ (B : Subgroup G) (_ : B ≤ A) (_ : IsCyclic (A ⧸ B.subgroupOf A)),
      X ⊓ Subgroup.centralizer (B : Set G) = X := by
  let _actorCommGroup : CommGroup A := { A.toGroup with mul_comm := mul_comm' }
  let _action := CFSG.SignalizerFunctor.Helpers.conjugationAction A X hAX
  have generated :=
    CFSG.SignalizerFunctor.Helpers.coprime_cyclic_quotient_generation p hp A hA X hX
  apply le_antisymm
  · exact iSup_le fun B => iSup_le fun _ => iSup_le fun _ => inf_le_left
  · have target_generated :
        (⨆ (B' : Subgroup A) (_ : IsCyclic (A ⧸ B')), FixedPoints.subgroup B' X).map
          X.subtype = X := by
      rw [generated, ← MonoidHom.range_eq_map, X.subtype_range]
    conv_lhs => rw [← target_generated]
    rw [Subgroup.map_iSup]
    refine iSup_le fun B' => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hcyc => ?_
    set B : Subgroup G := B'.map A.subtype
    have hBA : B ≤ A := by
      rintro _ ⟨a, -, rfl⟩
      exact a.2
    have hsub : B.subgroupOf A = B' :=
      Subgroup.comap_map_eq_self_of_injective A.subtype_injective B'
    refine le_trans ?_ (le_iSup_of_le B (le_iSup_of_le hBA
      (le_iSup_of_le (hsub ▸ hcyc) le_rfl)))
    rintro element ⟨representative, fixed, rfl⟩
    refine ⟨representative.property, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro actorElement member
    obtain ⟨internalElement, internal_member, rfl⟩ := member
    have equality := congrArg (fun internalTarget : X => (internalTarget : G))
      (fixed (⟨internalElement, internal_member⟩ : B'))
    change internalElement.val * representative.val * internalElement.val⁻¹ =
      representative.val at equality
    exact mul_inv_eq_iff_eq_mul.mp equality

theorem isCyclic_quotient_iff_of_isElemAbelian [Finite G] {p : ℕ} (hp : p.Prime)
    {A B : Subgroup G} [IsMulCommutative A] (hA : IsElemAbelian p A) (hBA : B ≤ A) :
    IsCyclic (A ⧸ B.subgroupOf A) ↔ B = A ∨ B ∈ Coprime.hyperplanes p A := by
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card A = Nat.card B * (B.subgroupOf A).index := by
    rw [← Subgroup.card_mul_index (B.subgroupOf A),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBA).toEquiv]
  have hquot : Nat.card (A ⧸ B.subgroupOf A) = (B.subgroupOf A).index := rfl
  have hBpos : 0 < Nat.card B := Nat.card_pos
  constructor
  · intro hcyc
    obtain ⟨g, hg⟩ := hcyc
    have hord : orderOf g = Nat.card (A ⧸ B.subgroupOf A) :=
      orderOf_eq_card_of_forall_mem_zpowers hg
    have hgp : g ^ p = 1 := by
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective g
      have ha : a ^ p = 1 := Subtype.ext (hA.2 a a.2)
      rw [← QuotientGroup.mk_pow, ha]
      rfl
    have hdvd : (B.subgroupOf A).index ∣ p := hquot ▸ hord ▸ orderOf_dvd_of_pow_eq_one hgp
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · left
      exact le_antisymm hBA (Subgroup.subgroupOf_eq_top.mp (Subgroup.index_eq_one.mp h1))
    · right
      exact ⟨hBA, by rw [hcard, h1, mul_comm]⟩
  · rintro (hBA' | ⟨-, hcardB⟩)
    · refine isCyclic_of_card_dvd_prime (p := p) ?_
      rw [hquot, Subgroup.index_eq_one.mpr (Subgroup.subgroupOf_eq_top.mpr hBA'.ge)]
      exact one_dvd p
    · refine isCyclic_of_prime_card (p := p) ?_
      rw [hquot]
      exact Nat.eq_of_mul_eq_mul_left hBpos (by rw [← hcard, hcardB, mul_comm])

theorem iSup_centralizer_hyperplanes [Finite G] {p : ℕ} (hp : p.Prime) {A X : Subgroup G}
    (hA : IsElemAbelian p A) (hpA : p ≤ Nat.card A) (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hX : Nat.Coprime p (Nat.card X)) :
    ⨆ B ∈ Coprime.hyperplanes p A, X ⊓ Subgroup.centralizer (B : Set G) = X := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨r, hr⟩ :=
    (CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup p A hA).exists_card_eq
  have hr1 : r ≠ 0 := by
    rintro rfl
    rw [hr, pow_zero] at hpA
    exact hp.one_lt.not_ge hpA
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have hset : Coprime.hyperplanes p A = signalizerFunctorEk p s A := by
    ext B
    refine and_congr_right fun _ => ?_
    rw [hr, pow_succ, mul_comm]
    exact (Nat.mul_right_inj hp.ne_zero).trans eq_comm
  rw [hset]
  exact CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation p s hp A X hA
    hr.ge hAX hX

private theorem exists_zpowers_eq_of_mem_signalizerFunctorEk [Finite G] {p : ℕ} (hp : p.Prime)
    {A S : Subgroup G} (hS : S ∈ signalizerFunctorEk p 1 A) :
    ∃ a ∈ S, a ≠ 1 ∧ Subgroup.zpowers a = S := by
  have hScard : Nat.card S = p := by rw [hS.2, pow_one]
  obtain ⟨a, haS, ha1⟩ : ∃ a ∈ S, a ≠ 1 := by
    by_contra! h
    have hbot : S = ⊥ := (Subgroup.eq_bot_iff_forall S).mpr h
    rw [hbot, Subgroup.card_bot] at hScard
    exact hp.one_lt.ne hScard
  refine ⟨a, haS, ha1, Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haS) ?_⟩
  rw [hScard, Nat.card_zpowers]
  have hdvd : orderOf a ∣ p := hScard ▸ Subgroup.orderOf_dvd_natCard S haS
  rcases (Nat.dvd_prime hp).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) ha1
  · exact h.ge

theorem iSup_centralizer_nonidentity [Finite G] {p : ℕ} (hp : p.Prime) {A X : Subgroup G}
    (hA : IsElemAbelian p A) (hrank : p ^ 2 ≤ Nat.card A)
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hX : Nat.Coprime p (Nat.card X)) :
    ⨆ (a : G) (_ : a ∈ A) (_ : a ≠ 1), X ⊓ Subgroup.centralizer ({a} : Set G) = X := by
  apply le_antisymm
  · exact iSup_le fun a => iSup_le fun _ => iSup_le fun _ => inf_le_left
  · conv_lhs =>
      rw [← CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation p 1 hp A X
        hA hrank hAX hX]
    refine iSup₂_le fun S hS => ?_
    obtain ⟨a, haS, ha1, hSa⟩ := exists_zpowers_eq_of_mem_signalizerFunctorEk hp hS
    refine le_iSup_of_le a (le_iSup_of_le (hS.1 haS) (le_iSup_of_le ha1 ?_))
    rw [← hSa, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

end CFSG.SignalizerFunctorTheorem.McBride
