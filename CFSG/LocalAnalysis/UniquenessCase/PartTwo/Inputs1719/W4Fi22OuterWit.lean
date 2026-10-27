module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Fi22OuterGen
public import CFSG.Sporadic.FischerOddCore.Fi22ExtCover

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore

private theorem fi22ow_conj_mem {r p : Equiv.Perm (Fin 3510)}
    (hr : r ∈ Subgroup.normalizer (fi22P : Set (Equiv.Perm (Fin 3510))))
    (hp : p ∈ fi22P) : r * p * r⁻¹ ∈ fi22P :=
  (Subgroup.mem_set_normalizer_iff.1 hr p).1 hp

private theorem fi22ow_inv_conj_mem {r p : Equiv.Perm (Fin 3510)}
    (hr : r ∈ Subgroup.normalizer (fi22P : Set (Equiv.Perm (Fin 3510))))
    (hp : p ∈ fi22P) : r⁻¹ * p * r ∈ fi22P := by
  have h := (Subgroup.mem_set_normalizer_iff.1 (Subgroup.inv_mem _ hr) p).1 hp
  simpa using h

private theorem fi22ow_dih_transfer {r t τ : Equiv.Perm (Fin 3510)}
    (hr : r ∈ Subgroup.normalizer (fi22P : Set (Equiv.Perm (Fin 3510))))
    (hτ : τ = r⁻¹ * t * r) {c : Equiv.Perm (Fin 3510)} (hcP : c ∈ fi22P)
    (hc : orderOf (t * (c * t * c⁻¹)) = 11) :
    ∃ c' ∈ fi22P, orderOf (τ * (c' * τ * c'⁻¹)) = 11 := by
  rw [hτ]
  refine ⟨r⁻¹ * c * r, fi22ow_inv_conj_mem hr hcP, ?_⟩
  have h1 : (r⁻¹ * t * r) * ((r⁻¹ * c * r) * (r⁻¹ * t * r) * (r⁻¹ * c * r)⁻¹) =
      MulAut.conj r⁻¹ (t * (c * t * c⁻¹)) := by
    rw [MulAut.conj_apply]
    group
  rw [h1]
  exact (MulEquiv.orderOf_eq (MulAut.conj r⁻¹) (t * (c * t * c⁻¹))).trans hc

private theorem fi22ow_gen4_transfer {r t τ : Equiv.Perm (Fin 3510)}
    (hr : r ∈ Subgroup.normalizer (fi22P : Set (Equiv.Perm (Fin 3510))))
    (hτ : τ = r⁻¹ * t * r)
    (h : ∃ cs : List (Equiv.Perm (Fin 3510)), cs.length = 4 ∧ (∀ c ∈ cs, c ∈ fi22P) ∧
      fi22P ≤ Subgroup.closure {x | ∃ c ∈ cs, x = c * t * c⁻¹}) :
    ∃ cs : List (Equiv.Perm (Fin 3510)), cs.length = 4 ∧ (∀ c ∈ cs, c ∈ fi22P) ∧
      fi22P ≤ Subgroup.closure {x | ∃ c ∈ cs, x = c * τ * c⁻¹} := by
  rw [hτ]
  obtain ⟨cs, hlen, hcs, hgen⟩ := h
  let S : Set (Equiv.Perm (Fin 3510)) := {x | ∃ c ∈ cs, x = c * t * c⁻¹}
  have hPmap : Subgroup.map (MulAut.conj r⁻¹).toMonoidHom fi22P = fi22P := by
    apply le_antisymm
    · intro p hp
      rw [Subgroup.mem_map] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
        fi22ow_inv_conj_mem hr hq
    · intro p hp
      rw [Subgroup.mem_map]
      refine ⟨r * p * r⁻¹, fi22ow_conj_mem hr hp, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hset : {x : Equiv.Perm (Fin 3510) |
        ∃ c ∈ cs.map (fun c => r⁻¹ * c * r), x = c * (r⁻¹ * t * r) * c⁻¹} =
      (MulAut.conj r⁻¹).toMonoidHom '' S := by
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
      exact ⟨c₀ * t * c₀⁻¹, ⟨c₀, hc₀, rfl⟩, by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group⟩
    · rintro ⟨y, ⟨c₀, hc₀, rfl⟩, rfl⟩
      exact ⟨r⁻¹ * c₀ * r, List.mem_map.2 ⟨c₀, hc₀, rfl⟩, by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group⟩
  refine ⟨cs.map (fun c => r⁻¹ * c * r), by simp [hlen], ?_, ?_⟩
  · intro c hc
    obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    exact fi22ow_inv_conj_mem hr (hcs c₀ hc₀)
  · rw [hset]
    calc fi22P = Subgroup.map (MulAut.conj r⁻¹).toMonoidHom fi22P := hPmap.symm
      _ ≤ Subgroup.map (MulAut.conj r⁻¹).toMonoidHom (Subgroup.closure S) :=
            Subgroup.map_mono hgen
      _ = Subgroup.closure ((MulAut.conj r⁻¹).toMonoidHom '' S) :=
            MonoidHom.map_closure (MulAut.conj r⁻¹).toMonoidHom S

theorem fi22_outerWitness
    {τ : Equiv.Perm (Fin 3510)} (hτR : τ ∈ fi22R)
    (hτ2 : orderOf τ = 2) (hτP : τ ∉ fi22P) :
    (∃ c ∈ fi22P, orderOf (τ * (c * τ * c⁻¹)) = 11) ∨
      ∃ cs : List (Equiv.Perm (Fin 3510)), cs.length = 4 ∧ (∀ c ∈ cs, c ∈ fi22P) ∧
        fi22P ≤ Subgroup.closure {x | ∃ c ∈ cs, x = c * τ * c⁻¹} := by
  obtain ⟨k, hk, r, hr, hrτ⟩ := fi22R_involution_conj hτR hτ2
  have hrn : r ∈ Subgroup.normalizer (fi22P : Set (Equiv.Perm (Fin 3510))) :=
    fi22R_le_normalizer hr
  have hτeq : τ = r⁻¹ * fi22ExtRep k * r := by
    rw [← hrτ]
    group
  have hk3 : 3 ≤ k := by
    by_contra h
    have hklt : k < 3 := by omega
    have hkP : fi22ExtRep k ∈ fi22P :=
      CTUC_Fi22_all_extension_involutions_covered.1 k hklt
    have hmem : r⁻¹ * fi22ExtRep k * r ∈ fi22P := fi22ow_inv_conj_mem hrn hkP
    rw [← hτeq] at hmem
    exact hτP hmem
  have hkcases : k = 3 ∨ k = 4 ∨ k = 5 := by omega
  rcases hkcases with rfl | rfl | rfl
  · obtain ⟨c, hcP, hc⟩ := fi22_ext_dihedral.2.1
    exact Or.inl (fi22ow_dih_transfer hrn hτeq hcP hc)
  · obtain ⟨cs, hlen, hcs, hgen⟩ := fi22_outerGen_t4
    exact Or.inr (fi22ow_gen4_transfer hrn hτeq ⟨cs, hlen, hcs, hgen⟩)
  · obtain ⟨c, hcP, hc⟩ := fi22_ext_dihedral.2.2
    exact Or.inl (fi22ow_dih_transfer hrn hτeq hcP hc)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
