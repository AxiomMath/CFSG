module

public import CFSG.Permutation.FiveTransitive.HighDegreeRegularFourSeed
public import CFSG.Permutation.FiveTransitive.PGroupConjugateIntoPreimageSylow
public import CFSG.Permutation.FiveTransitive.PairFixedExceptionTransport
public import CFSG.Permutation.FiveTransitive.ThreeSwapTwoGroup
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction

public section

namespace CFSG

open scoped Pointwise Classical

namespace FiveTransitive.HighDegreeFullSylowExceptionContradiction

open MulAction FixedNormalizerAction Research.HallRegularOrbits

theorem contradiction
    {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (hcard : 28 ≤ Fintype.card X) (h5 : IsMultiplyPretransitive G X 5)
    (hmax : ∀ t : G, orderOf t = 2 → (fixedBy X t).ncard ≤ 7)
    (Q : Subgroup G) (hQ : Nat.card Q = 2)
    (A : Sylow 2 (Normalizer Q))
    (a : Q) (ha : orderOf a.val = 2) (x : Normalizer Q)
    (hx : orderOf x.val = 2) (hxQ : x.val ∉ Q) (hax : Commute a.val x.val)
    (O : Set X)
    (hO : ∀ y ∈ O, y ∉ fixedPoints Q X ∧
      (x.val • y = y ∨ (a.val * x.val) • y = y))
    (hsemifree : ∀ b : A, ∀ y : X,
      y ∉ fixedPoints Q X → y ∉ O → b.val.val • y = y → b = 1) : False := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hane : a ≠ 1 := by
    intro he
    have he' := congrArg Subtype.val he
    simp only [he', OneMemClass.coe_one, orderOf_one] at ha
    omega
  have hall (q : Q) : q = 1 ∨ q = a := by
    obtain ⟨b, _, hb⟩ := (Nat.card_eq_two_iff' (1 : Q)).mp hQ
    by_cases hq : q = 1
    · exact Or.inl hq
    · exact Or.inr ((hb q hq).trans (hb a hane).symm)
  have hnorm (g : G) (hg : Commute a.val g) : g ∈ Normalizer Q := by
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    rcases hall ⟨q,hq⟩ with h | h
    · have he : q = 1 := congrArg Subtype.val h
      rw [he, one_mul, mul_one]
    · have he : q = a.val := congrArg Subtype.val h
      rw [he]
      exact hg.eq
  have hne : a.val ≠ x.val := fun he => hxQ (he ▸ a.property)
  obtain ⟨z, u, _, hzout, _, _, huorder, huz, hua, hux⟩ :=
    HighDegreeRegularFourSeed.exists_fixing_regular_four hcard h5 hmax a.val x.val ha hx hax hne
  let aN : Normalizer Q := ⟨a.val, Q.le_normalizer a.property⟩
  let uN : Normalizer Q := ⟨u, hnorm u hua.symm⟩
  have ha2 : aN ^ 2 = 1 := Subtype.ext (ha ▸ pow_orderOf_eq_one a.val)
  have hx2 : x ^ 2 = 1 := Subtype.ext (hx ▸ pow_orderOf_eq_one x.val)
  have hu2 : uN ^ 2 = 1 := Subtype.ext (huorder ▸ pow_orderOf_eq_one u)
  have haxN : Commute aN x := Subtype.ext hax.eq
  have huaN : Commute uN aN := Subtype.ext hua.eq
  have huxN : Commute uN x := Subtype.ext hux.eq
  let H := Subgroup.closure ({aN, x, uN} : Set (Normalizer Q))
  have hHp : IsPGroup 2 H := by
    apply (ThreeSwapTwoGroup.closure_two_group _ ?_ ?_).1
    · intro b hb c hc hbc
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb hc
      rcases hb with rfl | rfl | rfl <;> rcases hc with rfl | rfl | rfl
      all_goals first | exact Commute.refl _ | exact haxN | exact haxN.symm | exact huaN | exact huaN.symm | exact huxN | exact huxN.symm
    · intro b hb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
      rcases hb with rfl | rfl | rfl <;> assumption
  obtain ⟨c, hc⟩ := PGroupConjugateIntoPreimageSylow.into_sylow A H hHp
  let C : Subgroup G := (A : Subgroup (Normalizer Q)).map (Normalizer Q).subtype
  have hcC (g : Normalizer Q) (hg : g ∈ H) : c.val * g.val * c.val⁻¹ ∈ C :=
    ⟨c * g * c⁻¹, hc ⟨g,hg⟩, rfl⟩
  have hsemiC : ∀ b : C, ∀ y : X,
      y ∉ fixedPoints Q X → y ∉ O → b.val • y = y → b = 1 := by
    intro b y hyF hyO hb
    obtain ⟨v,hv,he⟩ := b.property
    change v.val = b.val at he
    have hvone := hsemifree ⟨v,hv⟩ y hyF hyO (by rw [he]; exact hb)
    exact Subtype.ext (he.symm.trans (congrArg (fun b : A => b.val.val) hvone))
  have hcF : ∀ y : X, y ∈ fixedPoints Q X ↔ c.val • y ∈ fixedPoints Q X := by
    intro y
    constructor
    · intro hy
      have hh := (c • (⟨y,by simpa only [fixed_eq Q] using hy⟩ : Fixed (X := X) Q)).property
      change c.val • y ∈ Fixed (X := X) Q at hh
      rwa [fixed_eq Q] at hh
    · intro hy
      have hh := (c⁻¹ • (⟨c.val • y,by simpa only [fixed_eq Q] using hy⟩ : Fixed (X := X) Q)).property
      change c.val⁻¹ • (c.val • y) ∈ Fixed (X := X) Q at hh
      simpa only [fixed_eq Q, inv_smul_smul] using hh
  have hzS : z ∈ regularFourSet a.val x.val z := by
    simp only [regularFourSet, Set.mem_insert_iff, true_or]
  have hzF : z ∉ fixedPoints Q X := fun hz => hzout hzS (Or.inl (Or.inl (hz a)))
  have hzO : z ∉ O := by
    intro hz
    rcases (hO z hz).2 with h | h
    · exact hzout hzS (Or.inl (Or.inr h))
    · exact hzout hzS (Or.inr h)
  have hxne : x.val ≠ 1 := by intro he; rw [he,orderOf_one] at hx; omega
  have hune : u ≠ 1 := by intro he; rw [he,orderOf_one] at huorder; omega
  have haxne : a.val * x.val ≠ 1 := by
    intro he
    have hxa : x.val = a.val⁻¹ := by
      calc
        x.val = a.val⁻¹ * (a.val * x.val) := by group
        _ = a.val⁻¹ := by rw [he,mul_one]
    exact hxQ (hxa ▸ Q.inv_mem a.property)
  exact PairFixedExceptionTransport.contradiction C (fixedPoints Q X) O a.val x.val u c.val z
    hsemiC hO hxne haxne hune hzF hzO (huz z hzS) hcF
    (hcC aN (Subgroup.subset_closure (by simp)))
    (hcC x (Subgroup.subset_closure (by simp)))
    (hcC uN (Subgroup.subset_closure (by simp)))

end FiveTransitive.HighDegreeFullSylowExceptionContradiction

end CFSG
