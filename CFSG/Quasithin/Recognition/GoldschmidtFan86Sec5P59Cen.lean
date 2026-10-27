module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P59Gen
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Z2Loc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P55Core
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P57Mech
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P58Loc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PRev
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5Stmt

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P59

section Kernels

variable (F : FanTree Γ G) (ℓ : Line Γ) {z z1 : G} {a tL tR : ℤ}

include F

theorem mul_mem_kernels (hz2 : z * z = 1) (hz12 : z1 * z1 = 1)
    (hfz : ∀ i, i ∈ ℓ.fixIdx z ↔ tL ≤ i ∧ i ≤ tR) (hfz1 : ∀ i, i ∈ ℓ.fixIdx z1 ↔ tL ≤ i ∧ i ≤ tR)
    (h1 : tL + 1 ≤ tR) :
    z * z1 ∈ nbrStab Γ G (ℓ.vert tL) ∧ z * z1 ∈ nbrStab Γ G (ℓ.vert tR) := by
  have fz : ∀ i, tL ≤ i → i ≤ tR → z • ℓ.vert i = ℓ.vert i := fun i h1 h2 => (hfz i).2 ⟨h1, h2⟩
  have fz1 : ∀ i, tL ≤ i → i ≤ tR → z1 • ℓ.vert i = ℓ.vert i := fun i h1 h2 =>
    (hfz1 i).2 ⟨h1, h2⟩
  have mz : ∀ i, (i < tL ∨ tR < i) → z • ℓ.vert i ≠ ℓ.vert i := fun i hi h => by
    have := (hfz i).1 h
    omega
  have mz1 : ∀ i, (i < tL ∨ tR < i) → z1 • ℓ.vert i ≠ ℓ.vert i := fun i hi h => by
    have := (hfz1 i).1 h
    omega
  constructor
  · refine F.mul_mem_nbrStab_of_sq_eq_one (ℓ.adj tL) ⟨?_, ?_⟩ ⟨?_, ?_⟩ hz2 hz12 ?_ ?_
    · exact MulAction.mem_stabilizer_iff.2 (fz _ le_rfl (by omega))
    · exact MulAction.mem_stabilizer_iff.2 (fz _ (by omega) (by omega))
    · exact MulAction.mem_stabilizer_iff.2 (fz1 _ le_rfl (by omega))
    · exact MulAction.mem_stabilizer_iff.2 (fz1 _ (by omega) (by omega))
    · exact fun h => mz (tL - 1) (Or.inl (by omega)) (mem_nbrStab.1 h _ (ℓ.adj_pred tL))
    · exact fun h => mz1 (tL - 1) (Or.inl (by omega)) (mem_nbrStab.1 h _ (ℓ.adj_pred tL))
  · refine F.mul_mem_nbrStab_of_sq_eq_one (ℓ.adj_pred tR) ⟨?_, ?_⟩ ⟨?_, ?_⟩ hz2 hz12 ?_ ?_
    · exact MulAction.mem_stabilizer_iff.2 (fz _ (by omega) le_rfl)
    · exact MulAction.mem_stabilizer_iff.2 (fz _ (by omega) (by omega))
    · exact MulAction.mem_stabilizer_iff.2 (fz1 _ (by omega) le_rfl)
    · exact MulAction.mem_stabilizer_iff.2 (fz1 _ (by omega) (by omega))
    · exact fun h => mz (tR + 1) (Or.inr (by omega)) (mem_nbrStab.1 h _ (ℓ.adj tR))
    · exact fun h => mz1 (tR + 1) (Or.inr (by omega)) (mem_nbrStab.1 h _ (ℓ.adj tR))

theorem comm_kernel (hcz : z ∈ Cen (ℓ.edgeStab (G := G) a : Set G))
    (hcz1 : z1 ∈ Cen (ℓ.edgeStab (G := G) (a - 1) : Set G)) {s : G}
    (hs : s ∈ nbrStab Γ G (ℓ.vert a)) : s * (z * z1) = (z * z1) * s := by
  have hsa : s • ℓ.vert a = ℓ.vert a :=
    MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer _ hs)
  have h1 : s ∈ ℓ.edgeStab (G := G) a :=
    ⟨MulAction.mem_stabilizer_iff.2 hsa,
      MulAction.mem_stabilizer_iff.2 (mem_nbrStab.1 hs _ (ℓ.adj a))⟩
  have h2 : s ∈ ℓ.edgeStab (G := G) (a - 1) := by
    refine ⟨MulAction.mem_stabilizer_iff.2 (mem_nbrStab.1 hs _ (ℓ.adj_pred a)), ?_⟩
    rw [sub_add_cancel]
    exact MulAction.mem_stabilizer_iff.2 hsa
  calc s * (z * z1) = (s * z) * z1 := by group
    _ = (z * s) * z1 := by rw [hcz.2 s h1]
    _ = z * (s * z1) := by group
    _ = z * (z1 * s) := by rw [hcz1.2 s h2]
    _ = (z * z1) * s := by group

omit F in
theorem comm_kernel_conj (F : FanTree Γ G) {u g : G} {v : V} (hug : u * g = g * u)
    (hk : ∀ s ∈ nbrStab Γ G v, s * u = u * s) {s : G} (hs : s ∈ nbrStab Γ G (g • v)) :
    s * u = u * s := by
  have hk' := hk (g⁻¹ * s * g) ((F.mem_nbrStab_smul_iff g v).1 hs)
  have c1 : Commute (g⁻¹ * s * g) u := hk'
  have c2 : Commute g u := hug.symm
  have h : Commute (g * (g⁻¹ * s * g) * g⁻¹) u := (c2.mul_left c1).mul_left c2.inv_left
  have e : g * (g⁻¹ * s * g) * g⁻¹ = s := by group
  rw [e] at h
  exact h.eq

end Kernels

end P59

end CFSG.Quasithin.Fan86
