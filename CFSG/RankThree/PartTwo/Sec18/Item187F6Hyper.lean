module

public import CFSG.RankThree.PartTwo.Sec18.Item187F6HyperAux

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

open scoped commutatorElement Pointwise

variable {V : Type} [Group V] [Finite V]

theorem abelian_case_sixtyfour (hV : ∀ v : V, v * v = 1) {K D : Subgroup (MulAut V)}
    (hK5 : IsPGroup 5 K) (hKab : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) (hKnc : ¬ IsCyclic K)
    {e : MulAut V} (he : e * e = 1) (hinv : ∀ y ∈ K, e * y * e⁻¹ = y⁻¹)
    (hDK : D ≤ Subgroup.normalizer (K : Set (MulAut V))) (heD : e ∈ ⁅D, D⁆)
    (hD : ∀ D₀ : Subgroup (MulAut V), D₀ ≤ D → D₀.relIndex D ≤ 2 → D₀ = D) :
    2 ^ 12 ≤ (Fix (Subgroup.zpowers e)).index ^ 2 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Finite (MulAut V) :=
    Finite.of_injective (fun f : MulAut V => (f : V ≃ V))
      (fun f g h => MulEquiv.ext fun v => congrArg (fun e : V ≃ V => e v) h)
  let Ω : Subgroup (MulAut V) :=
    { carrier := {x | x ∈ K ∧ x ^ 5 = 1}
      mul_mem' := fun {a b} ha hb => ⟨K.mul_mem ha.1 hb.1, by
        rw [(show Commute a b from hKab a ha.1 b hb.1).mul_pow, ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨K.one_mem, one_pow 5⟩
      inv_mem' := fun {a} ha => ⟨K.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hΩmem : ∀ x, x ∈ Ω ↔ x ∈ K ∧ x ^ 5 = 1 := fun x => Iff.rfl
  have hΩK : ∀ x ∈ Ω, x ∈ K := fun x hx => ((hΩmem x).mp hx).1
  have hΩ5 : ∀ x ∈ Ω, x ^ 5 = 1 := fun x hx => ((hΩmem x).mp hx).2
  have hΩab : ∀ x ∈ Ω, ∀ y ∈ Ω, x * y = y * x := fun x hx y hy =>
    hKab x (hΩK x hx) y (hΩK y hy)
  have hΩinv : ∀ y ∈ Ω, e * y * e⁻¹ = y⁻¹ := fun y hy => hinv y (hΩK y hy)
  have hfwd : ∀ d ∈ D, ∀ n ∈ Ω, d * n * d⁻¹ ∈ Ω := by
    intro d hd n hn
    refine (hΩmem _).mpr ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hDK hd) n).mp (hΩK n hn)
    · rw [conj_pow, hΩ5 n hn, mul_one, mul_inv_cancel]
  have hDΩ : D ≤ Subgroup.normalizer (Ω : Set (MulAut V)) := by
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · exact hfwd d hd n
    · intro h
      have h' := hfwd d⁻¹ (D.inv_mem hd) _ h
      have e1 : d⁻¹ * (d * n * d⁻¹) * d⁻¹⁻¹ = n := by group
      rw [e1] at h'
      exact h'
  have hΩne : Ω ≠ ⊥ := by
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := K) 5
      (dvd_trans (by norm_num) (twentyfive_dvd_card_of_not_isCyclic hK5 hKnc))
    have hg5 : (g : MulAut V) ^ 5 = 1 := by
      have h := pow_orderOf_eq_one g
      rw [hg] at h
      simpa using congrArg Subtype.val h
    intro hbot
    have hgΩ : (g : MulAut V) ∈ Ω := (hΩmem _).mpr ⟨g.2, hg5⟩
    rw [hbot, Subgroup.mem_bot] at hgΩ
    have hg1 : g = 1 := Subtype.ext (by simpa using hgΩ)
    rw [hg1, orderOf_one] at hg
    norm_num at hg
  obtain ⟨y, hyΩ, hy⟩ := exists_two_pow_twelve_core hV hΩ5 hΩab hΩne hDΩ heD hΩinv hD
  have hodd : Odd (orderOf y) :=
    Odd.of_dvd_nat ⟨2, by norm_num⟩ (orderOf_dvd_of_pow_eq_one (hΩ5 y hyΩ))
  exact le_trans hy (index_fix_zpowers_le_sq he (hinv y (hΩK y hyΩ)) hodd)

end CFSG.RankThree.PartTwo.Sec18.Item187Proof
