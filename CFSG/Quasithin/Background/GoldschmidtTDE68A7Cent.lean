module

public import CFSG.Quasithin.Background.GoldschmidtTDE68A7Dat

public section

namespace CFSG.Quasithin.E6.Alt.A7

open Equiv Equiv.Perm

set_option maxRecDepth 100000 in
theorem cent_S7 : ∀ σ : Perm (Fin 7), (∀ i, σ (g1 i) = g1 (σ i)) → (∀ i, σ (g2 i) = g2 (σ i)) →
    (∀ i, σ i = i) ∨ (∀ i, σ i = pa i) ∨ (∀ i, σ i = pb i) ∨ (∀ i, σ i = pa (pb i)) := by
  decide +kernel

theorem toT_g1 : toT g1 = [1, 2, 3, 0, 5, 4, 6] := by decide +kernel

theorem toT_g2 : toT g2 = [1, 0, 3, 2, 4, 5, 6] := by decide +kernel

theorem toT_pa : toT pa = [2, 3, 0, 1, 4, 5, 6] := by decide +kernel

theorem toT_pb : toT pb = [0, 1, 2, 3, 5, 4, 6] := by decide +kernel

theorem g1_mem : g1 ∈ D7 := by
  rw [mem_D7, toT_g1]
  decide +kernel

theorem g2_mem : g2 ∈ D7 := by
  rw [mem_D7, toT_g2]
  decide +kernel

theorem cent_D7 (σ : Perm (Fin 7)) (h : ∀ d ∈ D7, σ * d = d * σ) :
    σ = 1 ∨ σ = pa ∨ σ = pb ∨ σ = pa * pb := by
  have h1 : ∀ i, σ (g1 i) = g1 (σ i) := fun i => by
    have := congrArg (fun τ : Perm (Fin 7) => τ i) (h g1 g1_mem)
    exact this
  have h2 : ∀ i, σ (g2 i) = g2 (σ i) := fun i => by
    have := congrArg (fun τ : Perm (Fin 7) => τ i) (h g2 g2_mem)
    exact this
  rcases cent_S7 σ h1 h2 with h | h | h | h
  · exact Or.inl (Equiv.ext h)
  · exact Or.inr (Or.inl (Equiv.ext h))
  · exact Or.inr (Or.inr (Or.inl (Equiv.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Equiv.ext h)))

theorem comm_dtabs_pa :
    ∀ t ∈ dtabs, compT [2, 3, 0, 1, 4, 5, 6] t = compT t [2, 3, 0, 1, 4, 5, 6] := by
  decide +kernel

theorem comm_dtabs_pb :
    ∀ t ∈ dtabs, compT [0, 1, 2, 3, 5, 4, 6] t = compT t [0, 1, 2, 3, 5, 4, 6] := by
  decide +kernel

theorem pa_comm (d : Perm (Fin 7)) (hd : d ∈ D7) : pa * d = d * pa := by
  refine toT_injective ?_
  rw [toT_mul, toT_mul, toT_pa]
  exact comm_dtabs_pa _ hd

theorem pb_comm (d : Perm (Fin 7)) (hd : d ∈ D7) : pb * d = d * pb := by
  refine toT_injective ?_
  rw [toT_mul, toT_mul, toT_pb]
  exact comm_dtabs_pb _ hd

end CFSG.Quasithin.E6.Alt.A7
