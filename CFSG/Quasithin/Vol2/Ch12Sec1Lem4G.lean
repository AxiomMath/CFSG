module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Vol2.Ch12Sec1Swap

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.E3

namespace Sec1214

variable {G : Type} [Group G] [Finite G]

theorem orderOf_eq_one_or_three {X : Subgroup G} (hcube : ∀ x ∈ X, x ^ 3 ∈ pCoreOf 2 X)
    {x : G} (hx : x ∈ X) (ho : Odd (orderOf x)) : orderOf x = 1 ∨ orderOf x = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 : x ^ 3 = 1 := by
    obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X) ⟨_, hcube x hx⟩
    have hn' : (x ^ 3) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hd : orderOf (x ^ 3) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn'
    have hodd : Odd (orderOf (x ^ 3)) :=
      Odd.of_dvd_nat ho (orderOf_pow_dvd (x := x) 3)
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    have hm0 : m = 0 := by
      rcases m with _ | m
      · rfl
      · exfalso
        rw [hm, pow_succ] at hodd
        exact (Nat.not_even_iff_odd.mpr hodd) (even_two.mul_left _)
    rw [hm0, pow_zero, orderOf_eq_one_iff] at hm
    exact hm
  have hd3 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  rcases (Nat.dvd_prime Nat.prime_three).mp hd3 with h | h
  · exact Or.inl h
  · exact Or.inr h

theorem mem_normalizer_of_three {X : Subgroup G} (hXo : X = oTwoUpper X)
    (hcube : ∀ x ∈ X, x ^ 3 ∈ pCoreOf 2 X) {g : G}
    (hg : ∀ x ∈ X, orderOf x = 3 → g * x * g⁻¹ ∈ X) :
    g ∈ Subgroup.normalizer (X : Set G) := by
  refine Sec121Swap.mem_normalizer_of_conj_mem fun a ha => ?_
  have hle : (oTwoUpper X).map (MulAut.conj g).toMonoidHom ≤ X := by
    rw [oTwoUpper, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, ⟨hx, ho⟩, rfl⟩
    rcases orderOf_eq_one_or_three hcube hx ho with h1 | h3
    · rw [orderOf_eq_one_iff] at h1
      subst h1
      simp
    · exact hg x hx h3
  have ha' : a ∈ oTwoUpper X := hXo ▸ ha
  exact hle ⟨a, ha', rfl⟩

end Sec1214

end CFSG.Quasithin.H13
