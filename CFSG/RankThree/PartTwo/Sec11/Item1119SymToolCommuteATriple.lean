module

public import CFSG.RankThree.PartTwo.Sec11.Item1119SymToolRForm

public section

namespace CFSG.RankThree.PartTwo.Sec11.Item1119Sym

theorem commute_a_triple_form {G : Type*} [Group G] (u x c a d : G) (m : ℤ)
    (hcu : c * u = u * c) (hcx : c * x = x * c) (hca : c * a = a * c)
    (hux : u * x * u⁻¹ ∈ Subgroup.zpowers x) (hux' : u⁻¹ * x * u ∈ Subgroup.zpowers x)
    (hua : u * a = a * u)
    (hxa : x * a * x⁻¹ = d ^ m * a) (hxd : x * d = d * x) (had : a * d = d * a)
    (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) (hm : ¬ (3 : ℤ) ∣ m)
    {p : G} (hp : p ∈ Subgroup.closure ({u, x, c} : Set G)) (hpa : p * a = a * p) :
    ∃ j i l : ℤ, p = u ^ j * (x ^ 3) ^ i * c ^ l := by
  obtain ⟨j, i, l, rfl⟩ := mem_closure_triple_form u x c hcu hcx hux hux' hp
  have hAa : u ^ j * a = a * u ^ j := ((show Commute u a from hua).zpow_left j).eq
  have hCa : c ^ l * a = a * c ^ l := ((show Commute c a from hca).zpow_left l).eq
  have key : (u ^ j)⁻¹ * (a * (u ^ j * x ^ i * c ^ l))
      = (u ^ j)⁻¹ * (u ^ j * x ^ i * c ^ l * a) := by
    rw [hpa]
  have step1 : (u ^ j)⁻¹ * (a * (u ^ j * x ^ i * c ^ l)) = a * x ^ i * c ^ l := by
    calc (u ^ j)⁻¹ * (a * (u ^ j * x ^ i * c ^ l))
        = (u ^ j)⁻¹ * (a * u ^ j) * x ^ i * c ^ l := by group
      _ = (u ^ j)⁻¹ * (u ^ j * a) * x ^ i * c ^ l := by rw [hAa]
      _ = a * x ^ i * c ^ l := by group
  have step2 : (u ^ j)⁻¹ * (u ^ j * x ^ i * c ^ l * a) = x ^ i * a * c ^ l := by
    calc (u ^ j)⁻¹ * (u ^ j * x ^ i * c ^ l * a)
        = x ^ i * (c ^ l * a) := by group
      _ = x ^ i * (a * c ^ l) := by rw [hCa]
      _ = x ^ i * a * c ^ l := by group
  have h3 : a * x ^ i * c ^ l = x ^ i * a * c ^ l := step1.symm.trans (key.trans step2)
  have h4 : a * x ^ i = x ^ i * a := mul_right_cancel h3
  have hconj : x ^ i * a * (x ^ i)⁻¹ = a := by
    rw [← h4, mul_inv_cancel_right]
  have hd : d ^ (i * m) * a = a :=
    (zpow_conj_of_comm x a d m hxa hxd had i).symm.trans hconj
  have hdpow : d ^ (i * m) = 1 := mul_right_cancel (hd.trans (one_mul a).symm)
  have hord : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have h3dvd : (3 : ℤ) ∣ i * m := by
    have h := orderOf_dvd_iff_zpow_eq_one.mpr hdpow
    rw [hord] at h
    exact_mod_cast h
  have h3i : (3 : ℤ) ∣ i := by
    rcases Int.prime_three.dvd_or_dvd h3dvd with h | h
    · exact h
    · exact absurd h hm
  obtain ⟨i', rfl⟩ := h3i
  refine ⟨j, i', l, ?_⟩
  have hx3 : x ^ (3 * i') = (x ^ 3) ^ i' := by
    rw [zpow_mul]
    simp
  rw [hx3]

end CFSG.RankThree.PartTwo.Sec11.Item1119Sym

end
