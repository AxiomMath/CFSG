
module

public import CFSG.Sporadic.Th.KernelCosetBase

public import CFSG.Sporadic.Th.KernelOrder

public section

namespace CFSG.Sporadic.Th.Kernel

open CFSG.Sporadic.Bridge TauCeti Pointwise MulAction

section Orbits

variable {v : Fin 11 → P} (hv0 : v 0 = 1)
  (hcov : ∀ g : P, ∃ D, ∃ k ∈ K, ∃ k' ∈ K, g = k * v D * k')
  (hstab : ∀ D, mD D ≤ Nat.card (stabK (v D))) (hK : Nat.card K ≤ 634023936)

end Orbits

theorem isPreprimitive_Om (h : KernelFacts) :
    have := h.finite
    IsPreprimitive P Om ∧ Nat.card Om = 143127000 ∧ Nat.card K = 634023936 := by
  intro
  classical
  have hP := card_P_eq h
  obtain ⟨v, hv0, hcov, hstab, -, hK, -⟩ := h.dce hP
  obtain ⟨hOm, hKc, hc, hsz, hlab⟩ := orbitData hP hv0 hcov hstab hK
  refine ⟨?_, hOm, hKc⟩
  have : Fintype Om := Fintype.ofFinite Om
  have hbase : lab v hc (pt 1) = 0 := by
    rw [← hlab, hv0]
    exact MulAction.mem_orbit_self _
  apply isPreprimitive_of_suborbit_labels (pt 1) K (fun k hk => by
      rw [smul_pt, pt_eq_pt]; simpa using hk) (lab v hc)
  · intro k hk p
    have h1 := (hlab p _).2 rfl
    exact ((hlab _ _).1 (by
      obtain ⟨q, hq⟩ := h1
      refine ⟨⟨k, hk⟩ * q, ?_⟩
      change (⟨k, hk⟩ * q : K) • pt (v (lab v hc p)) = k • p
      rw [mul_smul]
      change (⟨k, hk⟩ : K) • (q • pt (v (lab v hc p))) = k • p
      have hq' : q • pt (v (lab v hc p)) = p := hq
      rw [hq']
      rfl))
  · intro p q hpq
    obtain ⟨x, hx⟩ := (hlab p _).2 rfl
    obtain ⟨y, hy⟩ := (hlab q _).2 hpq.symm
    refine ⟨((y * x⁻¹ : K) : P), (y * x⁻¹).2, ?_⟩
    rw [← hx, ← hy]
    change ((y * x⁻¹ : K) : P) • ((x : P) • pt (v (lab v hc p))) = (y : P) • pt (v (lab v hc p))
    rw [smul_smul]
    simp
  · intro S hS hdvd
    have hcard : ∀ i, (Finset.univ.filter fun p => lab v hc p = i).card = subSizes i := by
      intro i
      rw [← hsz i, Set.ncard_eq_toFinset_card']
      congr 1
      ext p
      simp [hlab]
    simp only [hcard] at hdvd
    rw [Fintype.card_eq_nat_card, hOm] at hdvd
    rw [hbase] at hS ⊢
    exact subSizes_blocks S hS hdvd

end CFSG.Sporadic.Th.Kernel
