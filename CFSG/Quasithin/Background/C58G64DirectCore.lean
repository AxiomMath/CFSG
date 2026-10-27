module

public import CFSG.Quasithin.Background.G11Defs

public section

namespace CFSG.Quasithin.C58.G64D

open CFSG.QuasithinUnique CFSG.Quasithin.G11

private instance instFiniteGLVCore {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] :
    Finite (GLV V) :=
  Finite.of_injective (fun g : GLV V => (g : V → V)) (fun a b h => LinearEquiv.ext (congrFun h))

theorem closure_pair_core {G : Type*} [Group G] {x y : G} (hxy : Commute x y)
    (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) :
    (∀ e ∈ Subgroup.closure ({x, y} : Set G), ∀ e' ∈ Subgroup.closure ({x, y} : Set G),
      e * e' = e' * e) ∧ ∀ e ∈ Subgroup.closure ({x, y} : Set G), e ^ 3 = 1 := by
  have hS : Subgroup.closure ({x, y} : Set G) ≤ Subgroup.centralizer ({x, y} : Set G) := by
    refine (Subgroup.closure_le _).2 fun g hg => ?_
    show g ∈ Subgroup.centralizer ({x, y} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rcases hg with rfl | rfl <;> rcases hh with rfl | rfl <;>
      (first | rfl | exact hxy.eq.symm | exact hxy.eq)
  have hS2 : Subgroup.closure ({x, y} : Set G) ≤
      Subgroup.centralizer (Subgroup.closure ({x, y} : Set G) : Set G) := by
    refine (Subgroup.closure_le _).2 fun g hg => ?_
    show g ∈ Subgroup.centralizer (Subgroup.closure ({x, y} : Set G) : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (Subgroup.mem_centralizer_iff.1 (hS hh) g hg).symm
  have hcomm : ∀ e ∈ Subgroup.closure ({x, y} : Set G), ∀ e' ∈ Subgroup.closure ({x, y} : Set G),
      e * e' = e' * e := fun e he e' he' => Subgroup.mem_centralizer_iff.1 (hS2 he') e he
  have hpow : ∀ e ∈ Subgroup.closure ({x, y} : Set G), e ^ 3 = 1 := by
    intro e he
    refine Subgroup.closure_induction (p := fun e _ => e ^ 3 = 1) ?_ ?_ ?_ ?_ he
    · rintro z (rfl | rfl)
      · exact hx3
      · exact hy3
    · exact one_pow 3
    · intro a b ha hb hpa hpb
      have hpa' : a ^ 3 = 1 := hpa
      have hpb' : b ^ 3 = 1 := hpb
      have hc : Commute a b := hcomm a ha b hb
      show (a * b) ^ 3 = 1
      rw [hc.mul_pow 3, hpa', hpb', mul_one]
    · intro a ha hpa
      have hpa' : a ^ 3 = 1 := hpa
      show a⁻¹ ^ 3 = 1
      rw [inv_pow, hpa', inv_one]
  exact ⟨hcomm, hpow⟩

theorem not_isCyclic_core {G : Type*} [Group G] [Finite G] {E : Subgroup G}
    (hE3 : ∀ e ∈ E, e ^ 3 = 1) {x y : G} (hxE : x ∈ E) (hyE : y ∈ E)
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    (hne : Subgroup.zpowers x ≠ Subgroup.zpowers y) : ¬ IsCyclic ↥E := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hc
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥E)
  have hg3 : g ^ 3 = 1 := Subtype.ext (by simpa using hE3 g.1 g.2)
  have hdvd : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hg3
  rw [hg] at hdvd
  have hxle : Subgroup.zpowers x ≤ E := Subgroup.zpowers_le.2 hxE
  have hyle : Subgroup.zpowers y ≤ E := Subgroup.zpowers_le.2 hyE
  have hxc : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1]
  have hyc : Nat.card (Subgroup.zpowers y) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hy3 hy1]
  have hEc : Nat.card E = 3 := by
    have h1 := Subgroup.card_le_of_le hxle
    have h2 : Nat.card E ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  apply hne
  have h1 : Subgroup.zpowers x = E :=
    Subgroup.eq_of_le_of_card_ge hxle (hEc.trans hxc.symm).le
  have h2 : Subgroup.zpowers y = E :=
    Subgroup.eq_of_le_of_card_ge hyle (hEc.trans hyc.symm).le
  rw [h1, h2]

end CFSG.Quasithin.C58.G64D
