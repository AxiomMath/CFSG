module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAutomorphisms
public import CFSG.GH74.Uniqueness.Bender.AutFixed
import CFSG.GroupTheory.CommuteOfSqEqOne

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6.L34

open Subgroup CFSG.ComponentClassification.PSL3Four CFSG.GH74.Uniqueness.Bender

theorem center_eq_bot : center S = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hc : (z : Equiv.Perm (Fin 42)) ∈
      Subgroup.centralizer (S : Set (Equiv.Perm (Fin 42))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h := Subgroup.mem_center_iff.1 hz ⟨s, hs⟩
    simpa only [Subgroup.coe_mul] using congrArg (fun t : S => (t : Equiv.Perm (Fin 42))) h
  have h1 : (z : Equiv.Perm (Fin 42)) ∈
      Subgroup.centralizer (S : Set (Equiv.Perm (Fin 42))) ⊓ R := ⟨hc, S_le_R z.2⟩
  rw [centralizer_S_inf_R, Subgroup.mem_bot] at h1
  exact Subtype.ext h1

theorem conjAutS_mk (s : S) :
    conjAutS ⟨s, S_le_R s.2⟩ = MulAut.conj s :=
  MulEquiv.ext fun _ => Subtype.ext rfl

theorem mem_autFixed_conjAutS {r : R} {s : S} :
    s ∈ autFixed (conjAutS r) ↔
      (r : Equiv.Perm (Fin 42)) * s = (s : Equiv.Perm (Fin 42)) * r := by
  rw [mem_autFixed_iff]
  constructor
  · intro h
    have hv : (r : Equiv.Perm (Fin 42)) * s * (r : Equiv.Perm (Fin 42))⁻¹ =
        (s : Equiv.Perm (Fin 42)) := by
      simpa only [conjAutS_apply] using congrArg (fun t : S => (t : Equiv.Perm (Fin 42))) h
    exact mul_inv_eq_iff_eq_mul.mp hv
  · intro h
    apply Subtype.ext
    rw [conjAutS_apply]
    exact mul_inv_eq_iff_eq_mul.mpr h

theorem mul_self_of_mem {B : Subgroup (MulAut S)}
    (hB2 : ∀ b ∈ B, b * b = 1) {r : R} (h : conjAutS r ∈ B) :
    (r : Equiv.Perm (Fin 42)) * r = 1 := by
  have h2 : conjAutS r * conjAutS r = 1 := hB2 _ h
  have h1 : conjAutS (r * r) = conjAutS 1 := by rw [map_mul, h2, map_one]
  have hrr : r * r = 1 := conjAutS_injective h1
  simpa using congrArg (fun t : R => (t : Equiv.Perm (Fin 42))) hrr

theorem commute_of_mem {B : Subgroup (MulAut S)}
    (hB2 : ∀ b ∈ B, b * b = 1) {r r' : R} (h : conjAutS r ∈ B) (h' : conjAutS r' ∈ B) :
    (r : Equiv.Perm (Fin 42)) * r' = r' * r := by
  have h1 : conjAutS r ^ 2 = 1 := by rw [pow_two]; exact hB2 _ h
  have h2 : conjAutS r' ^ 2 = 1 := by rw [pow_two]; exact hB2 _ h'
  have h3 : (conjAutS r * conjAutS r') ^ 2 = 1 := by
    rw [pow_two]
    exact hB2 _ (B.mul_mem h h')
  have hc : conjAutS r * conjAutS r' = conjAutS r' * conjAutS r :=
    CFSG.commute_of_sq_eq_one h1 h2 h3
  have hmap : conjAutS (r * r') = conjAutS (r' * r) := by rw [map_mul, map_mul, hc]
  have heq : r * r' = r' * r := conjAutS_injective hmap
  simpa using congrArg (fun t : R => (t : Equiv.Perm (Fin 42))) heq

theorem eq_top_of_mem {H : Subgroup S} (h₁ : (⟨g₁, g₁_mem_S⟩ : S) ∈ H)
    (h₂ : (⟨g₂, g₂_mem_S⟩ : S) ∈ H) (h₃ : (⟨g₃, g₃_mem_S⟩ : S) ∈ H) : H = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro s
  have hmap : S ≤ H.map S.subtype := by
    change Subgroup.closure {g₁, g₂, g₃} ≤ H.map S.subtype
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact Subgroup.mem_map_of_mem S.subtype h₁
    · exact Subgroup.mem_map_of_mem S.subtype h₂
    · exact Subgroup.mem_map_of_mem S.subtype h₃
  obtain ⟨t, ht, hts⟩ := Subgroup.mem_map.mp (hmap s.2)
  have hts' : t = s := Subtype.ext hts
  rw [← hts']
  exact ht

end CFSG.LocalAnalysis.WeakClosure81.Asch6.L34

end
