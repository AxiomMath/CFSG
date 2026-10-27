module

public import CFSG.Quasithin.EmptyFaithful.S153Q3Ab

public section

namespace CFSG.Quasithin

namespace S153Q

namespace Q3A

open scoped Pointwise

variable {W : Type} [CommGroup W] {z : MulAut W}

theorem isPt_smul {o : Subgroup W} (ho : IsPt z o) {g : MulAut W} (hg : g * z = z * g) :
    IsPt z (g • o) := by
  refine ⟨?_, fun w hw => ?_⟩
  · rw [card_smul]
    exact ho.1
  · rw [mem_smul_iff] at hw ⊢
    have hc : Commute g⁻¹ z := (show Commute g z from hg).inv_left
    have h : g⁻¹ (z w) = z (g⁻¹ w) := apply_comm (g := g⁻¹) hc w
    rw [h]
    exact ho.2 _ hw

theorem exists_orbit_six [Finite W] {Ah : Subgroup (MulAut W)} (hWc : Nat.card W = 2 ^ 6) (hz3 : z ^ 3 = 1)
    (hfpf : ∀ w : W, z w = w → w = 1) (hzA : z ∈ Ah) (hcent : ∀ g ∈ Ah, g * z = z * g)
    (hperf : Ah ≤ ⁅Ah, Ah⁆) (hcard : Nat.card ↥Ah = 1080) :
    ∃ o₀ : Subgroup W, IsPt z o₀ ∧ (MulAction.orbit Ah o₀).ncard = 6 ∧
      ∃ g ∈ Ah, ∃ u ∈ o₀, g u ∉ o₀ := by
  classical
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Finite ↥Ah := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥Ah) 5 (by rw [hcard]; norm_num)
  set x : MulAut W := (x₀ : MulAut W) with hxdef
  have hxord : orderOf x = 5 := by rw [hxdef, Subgroup.orderOf_coe, hx₀]
  have hx : x ^ 5 = 1 := by rw [← hxord]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hxord; omega
  have hxz : x * z = z * x := hcent x x₀.2
  set o₀ : Subgroup W := fixSub x with ho₀
  have hpt : IsPt z o₀ := ⟨card_fixSub hWc hx hx1, fun w hw => z_mem_fixSub hxz hw⟩
  have hnst : ∃ g ∈ Ah, ∃ u ∈ o₀, g u ∉ o₀ := exists_not_stab hperf hzA hcent hz3 hfpf hpt
  have hpts : ∀ O ∈ MulAction.orbit Ah o₀, IsPt z O := by
    rintro O ⟨g, rfl⟩
    exact isPt_smul hpt (hcent g g.2)
  have hcard4 : ∀ O ∈ MulAction.orbit Ah o₀, Nat.card ↥O = 4 := fun O hO => (hpts O hO).1
  let xL : Ah := x₀
  have hxL5 : xL ^ 5 = 1 := Subtype.ext (by simpa using hx)
  let f : MulAction.orbit Ah o₀ → MulAction.orbit Ah o₀ := fun O => xL • O
  have hfiter : ∀ n : ℕ, ∀ O, f^[n] O = (xL ^ n) • O := by
    intro n
    induction n with
    | zero => intro O; simp
    | succ n ih =>
      intro O
      rw [Function.iterate_succ_apply, ih, ← mul_smul, ← pow_succ]
  have hf5 : f^[5] = id := by
    funext O
    rw [hfiter, hxL5, one_smul]
    rfl
  have hmod := card_modEq_fixed f hf5
  have hfix : Nat.card {O : MulAction.orbit Ah o₀ // f O = O} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    have hxo : ∀ w ∈ o₀, x w ∈ o₀ := fun w hw => by
      have h : x w = w := hw
      rw [h]
      exact hw
    have hbase : f ⟨o₀, MulAction.mem_orbit_self o₀⟩ = ⟨o₀, MulAction.mem_orbit_self o₀⟩ :=
      Subtype.ext (smul_eq_of_le hxo)
    refine ⟨⟨fun a b => ?_⟩, ⟨⟨_, hbase⟩⟩⟩
    have key : ∀ c : {O : MulAction.orbit Ah o₀ // f O = O}, (c.1 : Subgroup W) = o₀ := by
      intro c
      have hc : (x : MulAut W) • (c.1 : Subgroup W) = (c.1 : Subgroup W) :=
        congrArg Subtype.val c.2
      have hle : (c.1 : Subgroup W) ≤ fixSub x :=
        le_fixSub_of_inv hx (hcard4 _ c.1.2) (fun w hw => by
          have h1 : x • w ∈ x • (c.1 : Subgroup W) := Subgroup.smul_mem_pointwise_smul w x _ hw
          rw [hc] at h1
          exact h1)
      exact (Subgroup.eq_of_le_of_card_ge hle (le_of_eq (hpt.1.trans (hcard4 _ c.1.2).symm)))
    exact Subtype.ext (Subtype.ext ((key a).trans (key b).symm))
  have hn : (MulAction.orbit Ah o₀).ncard % 5 = 1 := by
    have h := hmod
    rw [hfix, Nat.card_coe_set_eq] at h
    exact h
  have hdvd : (MulAction.orbit Ah o₀).ncard ∣ 1080 := by
    have h1 := MulAction.index_stabilizer Ah o₀
    have h2 := Subgroup.index_dvd_card (MulAction.stabilizer Ah o₀)
    rw [h1, hcard] at h2
    exact h2
  have hle : (MulAction.orbit Ah o₀).ncard ≤ 21 := ncard_pts_le hWc hz3 hfpf hpts
  have hcases : ∀ n : ℕ, n ≤ 21 → n ∣ 1080 → n % 5 = 1 → n = 1 ∨ n = 6 := by decide
  refine ⟨o₀, hpt, ?_, hnst⟩
  rcases hcases _ hle hdvd hn with h1 | h6
  · exfalso
    obtain ⟨g, hg, u, hu, hgu⟩ := hnst
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h1
    have e1 : ((⟨g, hg⟩ : Ah) • o₀ : Subgroup W) ∈ MulAction.orbit Ah o₀ :=
      MulAction.mem_orbit o₀ (⟨g, hg⟩ : Ah)
    have e2 : o₀ ∈ MulAction.orbit Ah o₀ := MulAction.mem_orbit_self o₀
    rw [ha, Set.mem_singleton_iff] at e1 e2
    have e3 : ((⟨g, hg⟩ : Ah) • o₀ : Subgroup W) = o₀ := e1.trans e2.symm
    apply hgu
    rw [← e3]
    exact Subgroup.smul_mem_pointwise_smul u g o₀ hu
  · exact h6

end Q3A

end S153Q

end CFSG.Quasithin
