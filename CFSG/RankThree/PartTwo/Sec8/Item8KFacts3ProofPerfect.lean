module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item8KFacts3

open Equiv Equiv.Perm Subgroup

theorem fixes_of_isPerfect {G X : Type*} [Group G] (ρ : G →* Perm X) {H : Subgroup G}
    (hH : Group.IsPerfect H) {Y : Set X} [Finite Y] (hY : Nat.card Y ≤ 4)
    (hHY : ∀ h ∈ H, ∀ y ∈ Y, ρ h y ∈ Y) : ∀ h ∈ H, ∀ y ∈ Y, ρ h y = y := by
  have hiff : ∀ h : H, ∀ x, ρ h x ∈ Y ↔ x ∈ Y := by
    intro h x
    refine ⟨fun hx => ?_, fun hx => hHY h h.2 x hx⟩
    have h1 := hHY (h : G)⁻¹ (inv_mem h.2) _ hx
    rwa [← Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one, Perm.one_apply] at h1
  let ψ : H →* Perm Y :=
    { toFun := fun h => (ρ h).subtypePerm (hiff h)
      map_one' := by
        ext y
        simp
      map_mul' := fun g h => by
        ext y
        simp only [Subgroup.coe_mul, map_mul]
        rfl }
  have hsolv : Group.IsSolvable (Perm Y) := Equiv.Perm.isSolvable hY
  have hrange : ψ.range = ⊥ := by
    by_contra hne
    have : Nontrivial ψ.range := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    have : Group.IsPerfect ψ.range := Group.IsPerfect.range ψ
    exact Group.IsPerfect.not_isSolvable ψ.range inferInstance
  intro h hh y hy
  have h1 : ψ ⟨h, hh⟩ = 1 := by
    have h2 : ψ ⟨h, hh⟩ ∈ ψ.range := ⟨_, rfl⟩
    rw [hrange] at h2
    exact h2
  have h2 := congrArg (fun σ : Perm Y => (σ ⟨y, hy⟩ : X)) h1
  simpa [ψ] using h2

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem card_support_of_mem_cycleFactorsFinset {u : Perm α} (hu : u ^ 3 = 1) {c : Perm α}
    (hc : c ∈ u.cycleFactorsFinset) : c.support.card = 3 := by
  have hcyc := (mem_cycleFactorsFinset_iff.mp hc).1
  obtain ⟨a, ha⟩ := hcyc.nonempty_support
  have hca : c = u.cycleOf a := cycle_is_cycleOf ha hc
  have hdvd : orderOf c ∣ 3 := by
    rw [hca]
    exact (orderOf_cycleOf_dvd_orderOf u a).trans (orderOf_dvd_of_pow_eq_one hu)
  rw [hcyc.orderOf] at hdvd
  have h2 := hcyc.two_le_card_support
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h <;> omega

theorem card_cycleFactorsFinset_le_four (hα : Fintype.card α ≤ 12) {u : Perm α}
    (hu : u ^ 3 = 1) : u.cycleFactorsFinset.card ≤ 4 := by
  have hsum : (u.cycleFactorsFinset.val.map (Finset.card ∘ support)).sum = u.support.card := by
    rw [← cycleType_def, sum_cycleType]
  have hmap : u.cycleFactorsFinset.val.map (Finset.card ∘ support) =
      Multiset.replicate u.cycleFactorsFinset.card 3 := by
    rw [Multiset.eq_replicate]
    refine ⟨by simp, fun n hn => ?_⟩
    obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.mp hn
    exact card_support_of_mem_cycleFactorsFinset hu hc
  rw [hmap, Multiset.sum_replicate, smul_eq_mul] at hsum
  have hle : u.support.card ≤ 12 := (Finset.card_le_univ _).trans hα
  omega

theorem commute_of_mem_cycleFactorsFinset (hα : Fintype.card α ≤ 12) {u : Perm α}
    (hu : u ^ 3 = 1) {H : Subgroup (Perm α)} (hH : Group.IsPerfect H)
    (hHu : H ≤ Subgroup.centralizer {u}) {c : Perm α} (hc : c ∈ u.cycleFactorsFinset) :
    ∀ h ∈ H, h * c * h⁻¹ = c := by
  set Y : Set (Perm α) := (u.cycleFactorsFinset : Set (Perm α)) with hYdef
  have hY : Nat.card Y ≤ 4 := by
    rw [hYdef, Nat.card_coe_set_eq, Set.ncard_coe_finset]
    exact card_cycleFactorsFinset_le_four hα hu
  have hHY : ∀ h ∈ H, ∀ y ∈ Y, ((MulAut.toPerm (Perm α)).comp MulAut.conj) h y ∈ Y := by
    intro h hh y hy
    have h1 := OnCycleFactors.Subgroup.Centralizer.toConjAct_smul_mem_cycleFactorsFinset
      (hHu hh) (Finset.mem_coe.mp hy)
    rw [ConjAct.toConjAct_smul] at h1
    exact Finset.mem_coe.mpr h1
  intro h hh
  exact fixes_of_isPerfect ((MulAut.toPerm (Perm α)).comp MulAut.conj) hH hY hHY h hh c
    (Finset.mem_coe.mpr hc)

theorem fixes_support_of_isPerfect (hα : Fintype.card α ≤ 12) {u : Perm α} (hu : u ^ 3 = 1)
    {H : Subgroup (Perm α)} (hH : Group.IsPerfect H) (hHu : H ≤ Subgroup.centralizer {u}) :
    ∀ h ∈ H, ∀ x ∈ u.support, h x = x := by
  intro h hh x hx
  set c := u.cycleOf x with hcdef
  have hc : c ∈ u.cycleFactorsFinset := cycleOf_mem_cycleFactorsFinset_iff.mpr hx
  have hcomm := commute_of_mem_cycleFactorsFinset hα hu hH hHu hc
  set Y : Set α := (c.support : Set α) with hYdef
  have hY : Nat.card Y ≤ 4 := by
    rw [hYdef, Nat.card_coe_set_eq, Set.ncard_coe_finset,
      card_support_of_mem_cycleFactorsFinset hu hc]
    norm_num
  have hHY : ∀ g ∈ H, ∀ y ∈ Y, (MonoidHom.id (Perm α)) g y ∈ Y := by
    intro g hg y hy
    rw [MonoidHom.id_apply, hYdef, Finset.mem_coe, mem_support]
    rw [hYdef, Finset.mem_coe, mem_support] at hy
    intro hgy
    apply hy
    have h1 := hcomm g hg
    have h2 : c (g y) = g (c y) := by
      rw [← Perm.mul_apply, ← Perm.mul_apply]
      conv_lhs => rw [← h1]
      simp [mul_assoc]
    rw [hgy] at h2
    exact (g.injective h2).symm
  have hxY : x ∈ Y := by
    rw [hYdef, Finset.mem_coe, hcdef, mem_support_cycleOf_iff]
    exact ⟨SameCycle.refl _ _, hx⟩
  exact fixes_of_isPerfect (MonoidHom.id (Perm α)) hH hY hHY h hh x hxY

end CFSG.RankThree.PartTwo.Sec8.Item8KFacts3
