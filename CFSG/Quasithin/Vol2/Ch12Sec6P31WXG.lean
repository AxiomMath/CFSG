module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31e
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXLie

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.P31X

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits S126 S126P31 Equiv
open scoped IsMulCommutative

structure StarProps {Q : Type*} [Group Q] (X : Subgroup Q) : Prop where
  simple : IsSimpleGroup ↥X
  nonab : ¬ ∀ a b : ↥X, a * b = b * a
  three : 3 ∣ Nat.card ↥X

theorem StarProps.of_equiv {Q : Type*} [Group Q] {X X' : Subgroup Q} (e : ↥X ≃* ↥X')
    (h : StarProps X') : StarProps X := by
  haveI := h.simple
  refine ⟨e.isSimpleGroup, fun hc => h.nonab fun a b => ?_, ?_⟩
  · have := hc (e.symm a) (e.symm b)
    have h2 := congrArg e this
    simpa using h2
  · rw [Nat.card_congr e.toEquiv]
    exact h.three

theorem exists_card_three_of_dvd {Q : Type*} [Group Q] [Finite Q] {X : Subgroup Q}
    (h : 3 ∣ Nat.card ↥X) : ∃ A : Subgroup Q, A ≤ X ∧ Nat.card A = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 3 h
  refine ⟨(Subgroup.zpowers c).map X.subtype, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · rw [Subgroup.card_map_of_injective X.subtype_injective, Nat.card_zpowers, hc]

theorem starProps_of_isPSL {Y : Type} [Group Y] [Finite Y] (hL : L2BorelFacts) {m : ℕ} (hm : 2 ≤ m)
    {X : Subgroup Y} (h : IsPSL 2 2 m ↥X) : StarProps X := by
  obtain ⟨U, hU⟩ := exists_isSylowTwoOf X
  obtain ⟨hcX, -⟩ := hL m hm Y X U h hU
  haveI hs : IsSimpleGroup ↥X := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 2 m h).2
  have h4 : 16 ≤ 4 ^ m := calc 16 = 4 ^ 2 := by norm_num
    _ ≤ 4 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have h2 : 4 ≤ 2 ^ m := calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  refine ⟨hs, S126P31.not_comm_of_simple_card ?_, ?_⟩
  · rw [hcX]
    exact Nat.not_prime_mul (by omega) (by omega)
  · have h4m : 4 ^ m % 3 = 1 := by rw [Nat.pow_mod]; norm_num
    rw [hcX]
    exact Dvd.dvd.mul_left (by omega) _

section G

variable {G : Type} [Group G] [Finite G] {T L V V₁ Vp H K : Subgroup G}

noncomputable def starConjEquiv {g : G} (hg : g ∈ H) :
    ↥(star H (conjSub g K)) ≃* ↥(star H K) :=
  (MulEquiv.subgroupCongr (L1233.star_conjSub hg)).trans
    (((star H K).equivMapOfInjective _ (MulAut.conj _).injective).symm)

theorem starProps_conjSub (hP : StarProps (star H K)) {g : G} (hg : g ∈ H) :
    StarProps (star H (conjSub g K)) :=
  hP.of_equiv (starConjEquiv hg)

end G

end CFSG.Quasithin.H13.P31X
