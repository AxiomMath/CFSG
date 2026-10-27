module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP2That

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin U42F431
open CFSG.Quasithin.H13.F431.U42 (Y P45 L0S x45 y45 sT repL_sT sT_mem sT_zero sT_injective gP
  gen_conj zero_mem_L0S sY sY_mem_T)
open CFSG.ComponentClassification.CatFactsSmall.PSp43 (QA45 QP45 f45)
open scoped Pointwise

theorem conj_mem_closure_of {H : Type*} [Group H] {S : Set H} {g : H}
    (hS : ∀ s ∈ S, g * s * g⁻¹ ∈ Subgroup.closure S) {h : H} (hh : h ∈ Subgroup.closure S) :
    g * h * g⁻¹ ∈ Subgroup.closure S := by
  refine Subgroup.closure_induction (p := fun x _ => g * x * g⁻¹ ∈ Subgroup.closure S)
    hS ?_ ?_ ?_ hh
  · simp only [mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  · intro x y _ _ hx hy
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by
      simp only [mul_assoc, inv_mul_cancel_left]
    rw [this]
    exact Subgroup.mul_mem _ hx hy
  · intro x _ hx
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by
      simp only [mul_inv_rev, inv_inv, mul_assoc]
    rw [this]
    exact Subgroup.inv_mem _ hx

theorem tpL_check : ∀ i < 45, comp (comp f45L (tpL i)) f45L = tpL (f45L.getD i 0) := by
  decide +kernel

theorem f45_conj (i : Fin 45) : f45 * sT i * f45⁻¹ = sT (f45 i) := by
  rw [f45_inv]
  have hlt : f45L.getD i 0 < 45 := by
    rw [repL_f45.2 i]
    exact (f45 i).2
  refine eq_of_repL (l := comp (comp f45L (tpL i)) f45L)
    (repL_mul (repL_mul repL_f45 (repL_sT i)) repL_f45) ?_
  rw [tpL_check i i.2]
  have h := repL_sT (f45 i)
  rwa [← repL_f45.2 i] at h

theorem tau_conj_A {g : P45} (hg : g ∈ QA45.originalSubgroup)
    (i : Fin 45) : g * sT i * g⁻¹ = sT (g i) := by
  have step : ∀ p s : P45, (∀ i : Fin 45, p * sT i * p⁻¹ = sT (p i)) →
      (∀ i : Fin 45, s * sT i * s⁻¹ = sT (s i)) →
      ∀ i : Fin 45, (p * s) * sT i * (p * s)⁻¹ = sT ((p * s) i) := by
    intro p s hp hs i
    calc p * s * sT i * (p * s)⁻¹ = p * (s * sT i * s⁻¹) * p⁻¹ := by group
      _ = p * sT (s i) * p⁻¹ := by rw [hs i]
      _ = sT (p (s i)) := hp (s i)
      _ = sT ((p * s) i) := rfl
  have key : ((QA45.originalSubgroup : Subgroup P45) : Set P45) ⊆
      {g : P45 | ∀ i : Fin 45, g * sT i * g⁻¹ = sT (g i)} := by
    rw [QA45_closure_eq]
    refine closure_subset_of_right_closed (S := ({x45, y45, f45} : Set P45)) ?_ ?_ ?_
    · intro s _
      obtain ⟨n, hn, h⟩ := (isOfFinOrder_of_finite s).exists_pow_eq_one
      exact ⟨n, hn, h⟩
    · intro i
      simp
    · intro p hp s hs
      rcases hs with rfl | rfl | rfl
      · exact step p _ hp (fun i => by simpa [gP] using gen_conj 0 i)
      · exact step p _ hp (fun i => by simpa [gP] using gen_conj 1 i)
      · exact step p _ hp f45_conj
  exact key hg i

theorem mem_centralizer_xA_iff {g : P45}
    (hg : g ∈ QA45.originalSubgroup) : g * x45 = x45 * g ↔ g 0 = 0 := by
  have h := tau_conj_A hg 0
  rw [sT_zero] at h
  constructor
  · intro hc
    have : sT (g 0) = sT 0 := by
      rw [← h, sT_zero, hc]
      group
    exact sT_injective this
  · intro h0
    rw [h0, sT_zero] at h
    calc g * x45 = g * x45 * g⁻¹ * g := by group
      _ = x45 * g := by rw [h]

theorem mul_xA_comm_iff (g : Ah) :
    g * xA = xA * g ↔ g ∈ P1h := by
  rw [mem_P1h_iff]
  constructor
  · intro h
    exact (mem_centralizer_xA_iff g.2).1 (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext ((mem_centralizer_xA_iff g.2).2 h)

theorem sT_mem_A (i : Fin 45) : sT i ∈ QA45.originalSubgroup := Xs_le_A (sT_mem i)

@[expose] def sA (i : Fin 45) : Ah := ⟨sT i, sT_mem_A i⟩

theorem sA_conj (g : Ah) (p : Fin 45) :
    g * sA p * g⁻¹ = sA ((g : P45) p) := Subtype.ext (tau_conj_A g.2 p)

theorem sA_zero : sA 0 = xA := Subtype.ext sT_zero

theorem sA_eq_incl (p : Fin 45) : sA p = incl (sY p) := rfl

@[expose] def VA : Subgroup Ah := Subgroup.closure {g | ∃ p : Fin 45, p ∈ L0S ∧ g = sA p}

theorem VA_le_That : VA ≤ That := by
  rw [VA, Subgroup.closure_le]
  rintro _ ⟨p, hp, rfl⟩
  rw [sA_eq_incl]
  exact map_T_le_That (Subgroup.mem_map_of_mem _ (sY_mem_T hp))

theorem xA_mem_VA : xA ∈ VA := by
  rw [← sA_zero]
  exact Subgroup.subset_closure ⟨0, zero_mem_L0S, rfl⟩

theorem VA_ne_bot : VA ≠ ⊥ := fun h => by
  have := xA_mem_VA
  rw [h, Subgroup.mem_bot] at this
  exact xA_ne_one this

theorem VA_isPGroup :
    IsPGroup 2 VA :=
  (isSylowTwoOf_That_Bh.2.1).to_le VA_le_That

theorem P2h_conj_VA {g : Ah} (hg : g ∈ P2h) {h : Ah}
    (hh : h ∈ VA) : g * h * g⁻¹ ∈ VA := by
  refine conj_mem_closure_of (S := {g | ∃ p : Fin 45, p ∈ L0S ∧ g = sA p}) ?_ hh
  rintro _ ⟨p, hp, rfl⟩
  rw [sA_conj]
  refine Subgroup.subset_closure ⟨(g : P45) p, ?_, rfl⟩
  have h2 := (mem_P2h_iff g).1 hg
  rw [← h2]
  exact ⟨p, hp, rfl⟩

end CFSG.Quasithin.H13.F431.U42Aut
