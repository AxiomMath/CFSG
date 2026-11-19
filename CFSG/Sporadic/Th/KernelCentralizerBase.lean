
module

public import CFSG.Sporadic.Th.KernelCosetBase
public import CFSG.GroupTheory.FixedPointCount

@[expose] public section

namespace CFSG.Sporadic.Th.Kernel

open CFSG.Sporadic.Bridge CFSG.Sporadic.Th.Max3 TauCeti Pointwise MulAction

theorem card_centralizer_mul_ncard {G : Type*} [Group G] (t : G) :
    Nat.card (Subgroup.centralizer ({t} : Set G)) * (conjugatesOf t).ncard = Nat.card G := by
  rw [← Subgroup.index_centralizer_eq_ncard]
  exact Subgroup.card_mul_index _

noncomputable def aK : K := ⟨gen 0, Subgroup.subset_closure ⟨0, rfl⟩⟩

theorem fix_orb_le [Finite P] (v : P) (t : K) {m n c : ℕ} (hm : m ≤ Nat.card (stabK v))
    (hn : Nat.card {k : P // k ∈ stabK v ∧ ∃ g ∈ K, g * t * g⁻¹ = k} ≤ n)
    (hc : Nat.card (Subgroup.centralizer ({t} : Set K)) ≤ c) :
    Nat.card {p : orb v // t • p = p} * m ≤ c * n := by
  have := CFSG.GroupAction.card_fix_mul_card_stabilizer (G := K) (X := orb v)
    ⟨pt v, mem_orbit_self _⟩ t
  have hs : stabilizer K (⟨pt v, mem_orbit_self _⟩ : orb v) = stabilizer K (pt v) := by
    ext k
    rw [mem_stabilizer_iff, mem_stabilizer_iff, Subtype.ext_iff]
    rfl
  have hmap : ∀ x : {h : K // h ∈ stabilizer K (⟨pt v, mem_orbit_self _⟩ : orb v) ∧ IsConj t h},
      (x.1 : P) ∈ stabK v ∧ ∃ g ∈ K, g * t * g⁻¹ = x.1 := by
    intro x
    obtain ⟨hst, hc⟩ := x.2
    have hst' : ((x.1 : K) : P) • pt v = pt v := congrArg Subtype.val (mem_stabilizer_iff.1 hst)
    obtain ⟨g, hg⟩ := isConj_iff.1 hc
    refine ⟨mem_stabK.2 ⟨x.1.2, hst'⟩, g, g.2, ?_⟩
    rw [← hg]
    rfl
  have hconj : Nat.card {h : K // h ∈ stabilizer K (⟨pt v, mem_orbit_self _⟩ : orb v) ∧
      IsConj t h} ≤ n := by
    refine le_trans (Nat.card_le_card_of_injective (fun x => ⟨(x.1 : P), hmap x⟩) ?_) hn
    intro x y hxy
    simp only [Subtype.mk.injEq] at hxy
    exact Subtype.ext (Subtype.ext hxy)
  calc Nat.card {p : orb v // t • p = p} * m
      ≤ Nat.card {p : orb v // t • p = p} * Nat.card (stabK v) := Nat.mul_le_mul_left _ hm
    _ = Nat.card {p : orb v // t • p = p} *
        Nat.card (stabilizer K (⟨pt v, mem_orbit_self _⟩ : orb v)) := by
      rw [hs, card_stabilizer]
    _ = _ := this
    _ ≤ c * n := Nat.mul_le_mul hc hconj

def fD : Fin 11 → ℕ := ![1, 0, 0, 0, 0, 0, 0, 1064, 8064, 0, 1071]

theorem fD_spec : ∀ D : Fin 11, D ≠ 0 → fD D = 774144 * nD D / mD D := by decide

theorem sum_fD : ∑ D, fD D = 10200 := by simp [Fin.sum_univ_succ, fD]


end CFSG.Sporadic.Th.Kernel
