module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBase

public section

namespace CFSG.Quasithin.A312M23

open CFSG.QuasithinUnique.K1.SporadicPerm
open scoped Pointwise

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)]

@[expose] def blkSet (n : ℕ) (b : List ℕ) : Set (Fin n) := {p | p.val ∈ b}

theorem mem_blkSet {b : List ℕ} {p : Fin n} : p ∈ blkSet n b ↔ p.val ∈ b := Iff.rfl

theorem smul_blkSet (g : Γ) {b : List ℕ} (hb : ∀ p ∈ b, p < n) :
    g • blkSet n b = blkSet n (b.map (act n g)) := by
  ext x
  rw [Set.mem_smul_set, mem_blkSet, List.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.val, hy, act_eq g y⟩
  · rintro ⟨p, hp, hpx⟩
    refine ⟨⟨p, hb p hp⟩, hp, Fin.ext ?_⟩
    rw [← hpx]
    exact (act_eq g ⟨p, hb p hp⟩).symm

end CFSG.Quasithin.A312M23
