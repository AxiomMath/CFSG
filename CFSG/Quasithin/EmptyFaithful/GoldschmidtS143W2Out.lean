module

public import CFSG.Quasithin.EmptyFaithful.Insp7NumA

public section

namespace CFSG.Quasithin

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

namespace S143

namespace InspW2

section Out

variable {L : Type} [Group L] {Gc : Type} [Group Gc]

theorem index_comap_conj_dvd_outer (ρ : Gc →* MulAut L) :
    ((MulAut.conj : L →* MulAut L).range.comap ρ).index ∣ Nat.card (Outer L) := by
  let ψ : Gc →* Outer L :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner L)).comp ρ
  have hker : ψ.ker = (MulAut.conj : L →* MulAut L).range.comap ρ := by
    ext g
    exact QuotientGroup.eq_one_iff (N := CFSG.ComponentClassification.OuterAutomorphisms.inner L)
      (ρ g)
  rw [← hker, Subgroup.index_ker]
  exact Subgroup.card_subgroup_dvd_card ψ.range

theorem card_outer_le_of_card_aut [Finite L] (hZ : Subgroup.center L = ⊥) {k : ℕ}
    (h : Nat.card (MulAut L) ≤ k * Nat.card L) : Nat.card (Outer L) ≤ k := by
  have h1 := Subgroup.card_mul_index (CFSG.ComponentClassification.OuterAutomorphisms.inner L)
  have h2 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner L) =
      Nat.card (L ⧸ Subgroup.center L) := by
    unfold CFSG.ComponentClassification.OuterAutomorphisms.inner
    rw [← Insp7.ker_conj_eq_center]
    exact (Nat.card_congr
      (QuotientGroup.quotientKerEquivRange (MulAut.conj : L →* MulAut L)).toEquiv).symm
  have h2' : Nat.card (L ⧸ Subgroup.center L) = Nat.card L := by
    rw [hZ]
    exact Nat.card_congr (QuotientGroup.quotientBot (G := L)).toEquiv
  rw [h2'] at h2
  have h4 : (CFSG.ComponentClassification.OuterAutomorphisms.inner L).index =
      Nat.card (Outer L) := rfl
  rw [h2, h4] at h1
  have hpos : 0 < Nat.card L := Nat.card_pos
  rw [← h1] at h
  exact Nat.le_of_mul_le_mul_left (by linarith) hpos

theorem mem_conj_range_of_odd_index [Finite L] (ρ : Gc →* MulAut L) (hO : Nat.card (Outer L) ≤ 2)
    (hodd : ¬ 2 ∣ ((MulAut.conj : L →* MulAut L).range.comap ρ).index) (g : Gc) :
    ρ g ∈ (MulAut.conj : L →* MulAut L).range := by
  have hd := index_comap_conj_dvd_outer ρ
  have hle : ((MulAut.conj : L →* MulAut L).range.comap ρ).index ≤ 2 :=
    (Nat.le_of_dvd Nat.card_pos hd).trans hO
  have hpos : 0 < ((MulAut.conj : L →* MulAut L).range.comap ρ).index := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    rw [h0] at hd
    exact absurd (Nat.eq_zero_of_zero_dvd hd) (Nat.card_pos).ne'
  have h1 : ((MulAut.conj : L →* MulAut L).range.comap ρ).index = 1 := by omega
  rw [Subgroup.index_eq_one] at h1
  have : g ∈ (MulAut.conj : L →* MulAut L).range.comap ρ := h1 ▸ Subgroup.mem_top g
  exact this

end Out

end InspW2

end S143

end CFSG.Quasithin
