module

public import CFSG.LocalAnalysis.WeakClosure81.TwelveEight
public import CFSG.LocalAnalysis.WeakClosure81.TwelveSevenA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem exists_fixed_add_commSub_of_odd {t : LGL 2 V} (ht : Odd (orderOf t))
    {H : Subgroup (LGL 2 V)} (htH : t ∈ H) {U : Submodule (ZMod 2) V}
    (hU : ∀ u ∈ U, t u ∈ U) {u : V} (hu : u ∈ U) :
    ∃ u₁ ∈ U, ∃ u₂ ∈ U, u = u₁ + u₂ ∧ t u₁ = u₁ ∧ u₂ ∈ commSub H := by
  have hpow : ∀ k : ℕ, ∀ w ∈ U, (t ^ k) w ∈ U := by
    intro k
    induction k with
    | zero =>
      intro w hw
      simpa using hw
    | succ k ih =>
      intro w hw
      rw [pow_succ]
      exact ih _ (hU w hw)
  set m := orderOf t with hm
  let u₁ : V := ∑ i ∈ Finset.range m, (t ^ i) u
  have hu₁ : u₁ ∈ U := Submodule.sum_mem _ fun i _ => hpow i u hu
  have htu₁ : t u₁ = u₁ := by
    have h1 : t u₁ = ∑ i ∈ Finset.range m, (t ^ (i + 1)) u := by
      simp only [u₁, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_succ']
      rfl
    have h2 := Finset.sum_range_succ' (fun i => (t ^ i) u) m
    have h3 := Finset.sum_range_succ (fun i => (t ^ i) u) m
    have h4 : (t ^ m) u = (t ^ 0) u := by
      rw [hm, pow_orderOf_eq_one, pow_zero]
    have h5 : ∑ i ∈ Finset.range m, (t ^ (i + 1)) u + (t ^ 0) u =
        ∑ i ∈ Finset.range m, (t ^ i) u + (t ^ m) u := by
      rw [← h2, ← h3]
    rw [h4] at h5
    rw [h1]
    exact add_right_cancel h5
  have hmu : m • u = u := by
    have h1 : ((m : ℕ) : ZMod 2) = 1 := ZMod.natCast_eq_one_iff_odd.mpr ht
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2) m u, h1, one_smul]
  have hsum : u - u₁ = ∑ i ∈ Finset.range m, (u - (t ^ i) u) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, hmu]
  refine ⟨u₁, hu₁, u - u₁, U.sub_mem hu hu₁, by abel, htu₁, ?_⟩
  rw [hsum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have h1 := sub_mem_commSub (A := H) (H.pow_mem htH i) u
  have h2 := (commSub H).neg_mem h1
  rwa [neg_sub] at h2

section PartTwo

variable {G : Type} [Group G] [Finite G] {A M : Subgroup G} {n : ℕ}

theorem Setting12Two.exists_odd_mem_fix (h : Setting12Two A M n)
    (hA : IsElemAbelian 2 A) (ρ : G →* LGL 2 V) (hq : RepQuad ρ A) :
    ∃ x : G, x ∈ M ∧ Odd (orderOf x) ∧
      fixMod (cE ρ.range) (ρ x) ⊓ commSub ρ.range ≤ cE ρ.range := by
  obtain ⟨u, v, hu, hv, huv1, huv, hmem⟩ := h.exists_cartan_pair
  obtain ⟨y, hyodd, hy, hfix⟩ := Setting12Two.exists_odd_fix h hA ρ hq hu hv huv huv1
  refine ⟨y, ?_, hyodd, hfix⟩
  rw [b12_TwelveBar_mem_map_iff h, hy]
  exact hmem

theorem Setting12Two.eq_inf_fixSub_sup_inf_commSub
    (h : Setting12Two A M n) (hA : IsElemAbelian 2 A) (ρ : G →* LGL 2 V) (hq : RepQuad ρ A)
    {U : Submodule (ZMod 2) V} (hUA : U ≤ fixSub (A.map ρ))
    (hMU : ∀ g ∈ M, ∀ u ∈ U, ρ g u ∈ U) :
    U = (U ⊓ fixSub ρ.range) ⊔ (U ⊓ commSub (A.map ρ)) := by
  obtain ⟨x, hxM, hxodd, hxfix⟩ := h.exists_odd_mem_fix hA ρ hq
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  intro u hu
  have hodd : Odd (orderOf (ρ x)) := Odd.of_dvd_nat hxodd (orderOf_map_dvd ρ x)
  have hxr : ρ x ∈ ρ.range := MonoidHom.mem_range.mpr ⟨x, rfl⟩
  obtain ⟨u₁, hu₁U, u₂, hu₂U, hsum, hxu₁, hu₂⟩ :=
    exists_fixed_add_commSub_of_odd (H := ρ.range) hodd hxr
      (fun w hw => hMU x hxM w hw) hu
  have hu₂A : u₂ ∈ commSub (A.map ρ) := by
    rw [← Setting12Two.fixSub_inf_commSub h ρ hq]
    exact ⟨hUA hu₂U, hu₂⟩
  obtain ⟨w, hw, c, hc, hwc⟩ := Submodule.mem_sup.mp
    (Setting12Two.fixSub_le_commSub_sup_fixSub h hA ρ hq (hUA hu₁U))
  have hxc : ρ x c = c := hc (ρ x) hxr
  have hxw : ρ x w = w := by
    have h1 : ρ x (w + c) = w + c := by
      rw [hwc]
      exact hxu₁
    rw [map_add, hxc] at h1
    exact add_right_cancel h1
  have hwE : w ∈ commSub ρ.range :=
    commSub_mono (A.map ρ) ρ.range (Subgroup.map_le_range ρ A) hw
  have hwcE : w ∈ cE ρ.range := by
    apply hxfix
    refine ⟨?_, hwE⟩
    show ρ x w - w ∈ cE ρ.range
    rw [hxw, sub_self]
    exact Submodule.zero_mem _
  have hu₁G : u₁ ∈ fixSub ρ.range := by
    rw [← hwc]
    exact Submodule.add_mem _ (cE_le_fixSub ρ.range hwcE) hc
  rw [hsum]
  exact Submodule.add_mem_sup (⟨hu₁U, hu₁G⟩ : u₁ ∈ U ⊓ fixSub ρ.range)
    (⟨hu₂U, hu₂A⟩ : u₂ ∈ U ⊓ commSub (A.map ρ))

end PartTwo

end CFSG.LocalAnalysis.WeakClosure81
