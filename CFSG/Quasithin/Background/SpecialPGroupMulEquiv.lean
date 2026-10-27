module

public import CFSG.Quasithin.Background.F1Lemma10

public section

namespace CFSG.Quasithin

theorem IsSpecialPGroup.of_mulEquiv {P Q : Type*} [Group P] [Group Q] {p : ℕ}
    (e : P ≃* Q) (h : IsSpecialPGroup p P) : IsSpecialPGroup p Q := by
  refine ⟨h.1.of_equiv e, ?_⟩
  rcases h.2 with ⟨hc, hexp⟩ | ⟨hcomm, hfr, hcenter⟩
  · left
    refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
    · intro x y
      obtain ⟨x, rfl⟩ := e.surjective x
      obtain ⟨y, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, hc.is_comm.comm x y]
    · intro x
      obtain ⟨x, rfl⟩ := e.surjective x
      rw [← map_pow, hexp x, map_one]
  · right
    refine ⟨?_, ?_, ?_⟩
    · have hmap : (commutator P).map e.toMonoidHom = commutator Q := by
        rw [map_commutator_eq, MonoidHom.range_eq_top_of_surjective e.toMonoidHom e.surjective]
        rfl
      calc commutator Q = (commutator P).map e.toMonoidHom := hmap.symm
        _ = (Subgroup.center P).map e.toMonoidHom := by rw [hcomm]
        _ = Subgroup.center Q := Subgroup.map_center_eq e
    · have hmap : frattini Q = (frattini P).map e.toMonoidHom := by
        refine le_antisymm ?_ ?_
        · intro x hx
          have hx' : e.symm x ∈ frattini P := by
            have h := frattini_le_comap_frattini_of_surjective
              (φ := e.symm.toMonoidHom) e.symm.surjective hx
            simpa using h
          exact Subgroup.mem_map.mpr ⟨e.symm x, hx', by simp⟩
        · rintro _ ⟨y, hy, rfl⟩
          exact frattini_le_comap_frattini_of_surjective e.surjective hy
      calc frattini Q = (frattini P).map e.toMonoidHom := hmap
        _ = (Subgroup.center P).map e.toMonoidHom := by rw [hfr]
        _ = Subgroup.center Q := Subgroup.map_center_eq e
    · intro z hz
      have hz' : e.symm z ∈ Subgroup.center P := by
        have hmap : (Subgroup.center Q).map e.symm.toMonoidHom = Subgroup.center P :=
          Subgroup.map_center_eq e.symm
        rw [← hmap]
        exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
      rw [← e.apply_symm_apply z, ← map_pow, hcenter _ hz', map_one]

end CFSG.Quasithin
