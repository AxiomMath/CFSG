module

public import CFSG.Certificates.Kernel.CentGenHKSound

public section

namespace CFSG.KC.CentGenK

open CFSG.KS.Raw.Orb
open scoped commutatorElement

variable {n w : Nat}

theorem cg_facts {A B : Nat} {a b : Equiv.Perm (Fin n)} (hA : PRep n w A a) (hB : PRep n w B b)
    {D : CGK} (h : cgK n w A B D = true) :
    ∃ e f s₁ s₂ : Equiv.Perm (Fin n),
      Subgroup.closure {s₁, s₂} = Subgroup.closure {a, b} ∧
      e ∈ Subgroup.closure {a, b} ∧ f ∈ Subgroup.closure {a, b} ∧
      e ^ D.p = 1 ∧ f ^ D.p = 1 ∧ e * f = f * e ∧ e ≠ 1 ∧ (∀ k < D.p, f ≠ e ^ k) ∧
      s₁ * e = e * s₁ ∧ s₂ * f = f * s₂ := by
  obtain ⟨e, f, s₁, s₂, h₁, h₂, he, hf, hep, hfp, hef, he1, hfe, hs₁, hs₂, ha, hb⟩ :=
    cgK_spec hA hB h
  refine ⟨e, f, s₁, s₂, le_antisymm ?_ ?_, he, hf, hep, hfp, hef, he1, hfe, hs₁, hs₂⟩
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    exacts [h₁, h₂]
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    exacts [ha, hb]

theorem hp_facts {A B : Nat} {a b : Equiv.Perm (Fin n)} (hA : PRep n w A a) (hB : PRep n w B b)
    {D : HPK} (h : hpK n w A B D = true) :
    ∃ x y s₁ s₂ : Equiv.Perm (Fin n),
      Subgroup.closure {s₁, s₂} = Subgroup.closure {a, b} ∧
      x ∈ Subgroup.closure {a, b} ∧ y ∈ Subgroup.closure {a, b} ∧
      x ^ D.p = 1 ∧ y ^ D.p = 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
      (∀ k < D.p, ⁅x, y⁆ ≠ x ^ k) ∧ (∀ k < D.p, ⁅x, y⁆ ≠ y ^ k) ∧
      s₁ * x = x * s₁ ∧ s₂ * y = y * s₂ := by
  obtain ⟨s₁, s₂, hs, -, hx, hy, hzx, hzy, hnx, hny⟩ := hpK_spec hA hB h
  refine ⟨s₁ ^ D.ke, s₂ ^ D.kf, s₁, s₂, hs, ?_, ?_, hx, hy, hzx, hzy, hnx, hny,
    (Commute.self_pow s₁ D.ke).eq, (Commute.self_pow s₂ D.kf).eq⟩
  · rw [← hs]
    exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_insert _ _)) _
  · rw [← hs]
    exact Subgroup.pow_mem _
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton s₂))) _

end CFSG.KC.CentGenK

end
