module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.F112Crit

section Aux

private theorem sum_comp_inv_smul {Ω G : Type*} [Fintype Ω] [Group G] [MulAction G Ω] (g : G)
    (f : Ω → ZMod 2) : ∑ α, f (g⁻¹ • α) = ∑ α, f α :=
  Equiv.sum_comp (MulAction.toPerm g⁻¹) f

private theorem exists_smul_eq_self_ne_zero {K V : Type*} [Group K] [MulAction K V]
    [AddCommGroup V] [Finite V] (hK : IsPGroup 2 K) (h2 : ∀ a : V, a + a = 0) (A : AddSubgroup V)
    (hA : ∀ g : K, ∀ a ∈ A, g • a ∈ A) (h0 : ∀ g : K, g • (0 : V) = 0) {a₀ : V}
    (ha₀ : a₀ ∈ A) (ha₀' : a₀ ≠ 0) : ∃ a ∈ A, a ≠ 0 ∧ ∀ g : K, g • a = a := by
  let S : SubMulAction K V := ⟨(A : Set V), fun g a ha => hA g a ha⟩
  have hdvd : 2 ∣ Nat.card S := by
    have h1 : addOrderOf (⟨a₀, ha₀⟩ : A) = 2 := by
      rw [AddSubgroup.addOrderOf_mk]
      exact addOrderOf_eq_prime (by rw [two_nsmul]; exact h2 a₀) ha₀'
    have h3 : Nat.card S = Nat.card A := Nat.card_congr (Equiv.refl _)
    rw [h3, ← h1]
    exact addOrderOf_dvd_natCard _
  have hfix0 : (⟨0, A.zero_mem⟩ : S) ∈ MulAction.fixedPoints K S := fun g =>
    Subtype.ext (h0 g)
  obtain ⟨b, hb, hne⟩ := hK.exists_fixed_point_of_prime_dvd_card_of_fixed_point S hdvd hfix0
  refine ⟨b.1, b.2, fun h => hne (Subtype.ext h.symm), fun g => ?_⟩
  exact congrArg Subtype.val (hb g)

private theorem exists_sub_translate {Ω G : Type*} [Fintype Ω] [Group G] [MulAction G Ω]
    (htrans : ∀ α β : Ω, ∃ g : G, g • α = β) {f : Ω → ZMod 2} {α₀ β₀ : Ω}
    (hne : f α₀ ≠ f β₀) :
    ∃ g : G, f - (fun α => f (g⁻¹ • α)) ≠ 0 ∧ ∑ α, (f - (fun α => f (g⁻¹ • α))) α = 0 := by
  obtain ⟨g, hg⟩ : ∃ g : G, (fun α => f (g⁻¹ • α)) ≠ f := by
    by_contra hcon
    push Not at hcon
    obtain ⟨k, hk⟩ := htrans β₀ α₀
    apply hne
    have h := congrFun (hcon k⁻¹) β₀
    simp only [inv_inv, hk] at h
    exact h
  refine ⟨g, sub_ne_zero.mpr hg.symm, ?_⟩
  simp only [Pi.sub_apply, Finset.sum_sub_distrib, sum_comp_inv_smul, sub_self]

private theorem eq_ite_of_fixed {Ω G : Type*} [Fintype Ω] [DecidableEq Ω] [Group G]
    [MulAction G Ω] (hodd : Odd (Fintype.card Ω)) {ω : Ω} {U : Subgroup G}
    (hUtr : ∀ α β : Ω, α ≠ ω → β ≠ ω → ∃ u ∈ U, u • α = β) {g : Ω → ZMod 2} (hg0 : g ≠ 0)
    (hgs : ∑ α, g α = 0) (hgfix : ∀ u ∈ U, ∀ α, g (u • α) = g α) (α : Ω) :
    g α = if α = ω then 0 else 1 := by
  have hconst : ∀ μ ν : Ω, μ ≠ ω → ν ≠ ω → g μ = g ν := by
    intro μ ν hμ hν
    obtain ⟨u, hu, hμν⟩ := hUtr μ ν hμ hν
    rw [← hμν, hgfix u hu μ]
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ZMod 2, ∀ ν, ν ≠ ω → g ν = c₁ := by
    by_cases h : ∃ μ, μ ≠ ω
    · obtain ⟨μ, hμ⟩ := h
      exact ⟨g μ, fun ν hν => hconst ν μ hν hμ⟩
    · exact ⟨0, fun ν hν => (h ⟨ν, hν⟩).elim⟩
  have hsum0 : ∑ ν ∈ Finset.univ.erase ω, g ν = 0 := by
    rw [Finset.sum_congr rfl fun ν hν => hc₁ ν (Finset.ne_of_mem_erase hν), Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    obtain ⟨k, hk⟩ := hodd
    have : Fintype.card Ω - 1 = 2 * k := by omega
    rw [this, mul_nsmul, two_nsmul, CharTwo.add_self_eq_zero, nsmul_zero]
  have hgω : g ω = 0 := by
    have := Finset.add_sum_erase Finset.univ g (Finset.mem_univ ω)
    rw [hsum0, hgs, add_zero] at this
    exact this
  by_cases hα : α = ω
  · rw [if_pos hα, hα, hgω]
  · rw [if_neg hα]
    obtain ⟨ν₀, hν₀⟩ := Function.ne_iff.mp hg0
    have hν₀' : ν₀ ≠ ω := fun h => hν₀ (by rw [h, hgω]; rfl)
    have hc1 : c₁ = 1 := by
      have : c₁ ≠ 0 := by rw [← hc₁ ν₀ hν₀']; exact hν₀
      revert this
      generalize c₁ = x
      revert x
      decide
    rw [hc₁ α hα, hc1]

private theorem const_sub_single_mem {Ω G : Type*} [Fintype Ω] [DecidableEq Ω] [Group G]
    [MulAction G Ω] (hodd : Odd (Fintype.card Ω)) (htrans : ∀ α β : Ω, ∃ g : G, g • α = β)
    {ω : Ω} {U : Subgroup G} (hU : IsPGroup 2 U)
    (hUtr : ∀ α β : Ω, α ≠ ω → β ≠ ω → ∃ u ∈ U, u • α = β)
    {M : AddSubgroup (Ω → ZMod 2)}
    (hM : ∀ (g : G) (f : Ω → ZMod 2), f ∈ M → (fun α => f (g⁻¹ • α)) ∈ M)
    {f : Ω → ZMod 2} (hf : f ∈ M) {α₀ β₀ : Ω} (hne : f α₀ ≠ f β₀) (γ : Ω) :
    (fun α => if α = γ then (0 : ZMod 2) else 1) ∈ M := by
  obtain ⟨g₀, hd0, hds⟩ := exists_sub_translate htrans hne
  let A : AddSubgroup (Ω → ZMod 2) :=
    { carrier := {h | h ∈ M ∧ ∑ α, h α = 0}
      zero_mem' := ⟨M.zero_mem, by simp⟩
      add_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        exact ⟨M.add_mem ha1 hb1, by simp [Finset.sum_add_distrib, ha2, hb2]⟩
      neg_mem' := by
        rintro a ⟨ha1, ha2⟩
        exact ⟨M.neg_mem ha1, by simp [Finset.sum_neg_distrib, ha2]⟩ }
  letI : MulAction U (Ω → ZMod 2) := arrowAction
  obtain ⟨g, ⟨hgM, hgs⟩, hg0, hgfix⟩ := exists_smul_eq_self_ne_zero (K := U) (V := Ω → ZMod 2) hU
    (fun a => funext fun α => CharTwo.add_self_eq_zero (a α)) A
    (fun u a ha => ⟨hM u a ha.1, (sum_comp_inv_smul (u : G) a).trans ha.2⟩) (fun u => rfl)
    (a₀ := f - (fun α => f (g₀⁻¹ • α))) ⟨M.sub_mem hf (hM g₀ f hf), hds⟩ hd0
  have hgc : ∀ u ∈ U, ∀ ν, g (u • ν) = g ν := by
    intro u hu ν
    have h := congrFun (hgfix (⟨u, hu⟩ : U)⁻¹) ν
    change g (((⟨u, hu⟩ : U)⁻¹)⁻¹ • ν) = g ν at h
    rwa [inv_inv] at h
  have hgeq : g = fun α => if α = ω then (0 : ZMod 2) else 1 :=
    funext (eq_ite_of_fixed hodd hUtr hg0 hgs hgc)
  have hω : (fun α => if α = ω then (0 : ZMod 2) else 1) ∈ M := by
    rw [← hgeq]
    exact hgM
  obtain ⟨k, hk⟩ := htrans ω γ
  convert hM k _ hω using 1
  funext α
  have hiff : k⁻¹ • α = ω ↔ α = γ := by rw [inv_smul_eq_iff, hk]
  simp only [hiff]

end Aux

theorem single_add_single_mem_of_nonconst {Ω G : Type*} [Fintype Ω] [DecidableEq Ω] [Group G]
    [MulAction G Ω] (hodd : Odd (Fintype.card Ω)) (htrans : ∀ α β : Ω, ∃ g : G, g • α = β)
    {ω : Ω} {U : Subgroup G} [Finite U] (hU : IsPGroup 2 U) (hUω : ∀ u ∈ U, u • ω = ω)
    (hUtr : ∀ α β : Ω, α ≠ ω → β ≠ ω → ∃ u ∈ U, u • α = β)
    {M : AddSubgroup (Ω → ZMod 2)}
    (hM : ∀ (g : G) (f : Ω → ZMod 2), f ∈ M → (fun α => f (g⁻¹ • α)) ∈ M)
    {f : Ω → ZMod 2} (hf : f ∈ M) {α₀ β₀ : Ω} (hne : f α₀ ≠ f β₀) (α β : Ω) :
    Pi.single α 1 + Pi.single β 1 ∈ M := by
  have key : (Pi.single α 1 + Pi.single β 1 : Ω → ZMod 2) =
      (fun x => if x = α then (0 : ZMod 2) else 1) +
        (fun x => if x = β then (0 : ZMod 2) else 1) := by
    funext x
    simp only [Pi.add_apply, Pi.single_apply]
    split_ifs <;> decide
  rw [key]
  exact M.add_mem (const_sub_single_mem hodd htrans hU hUtr hM hf hne α)
    (const_sub_single_mem hodd htrans hU hUtr hM hf hne β)

end CFSG.Quasithin.F112Crit

end
