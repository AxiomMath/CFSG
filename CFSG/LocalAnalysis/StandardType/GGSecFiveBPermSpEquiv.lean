module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpFrameDefs

public section

namespace CFSG.StandardType

section Equivariance

variable {G : Type} [Group G] {p n : ℕ} {Bs : Subgroup G}
  {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {φ : MulAut ↥Bs} {g : G}

theorem ggBs_map_conj (hφ : ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = g * b * g⁻¹) :
    Bs.map (MulAut.conj g).toMonoidHom = Bs := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨b, hb, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hφ ⟨b, hb⟩]
    exact (φ ⟨b, hb⟩).2
  · intro c hc
    refine ⟨((φ.symm ⟨c, hc⟩ : ↥Bs) : G), (φ.symm ⟨c, hc⟩).2, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hφ (φ.symm ⟨c, hc⟩),
      MulEquiv.apply_symm_apply]

theorem ggBsCoordEq_map_conj (hφ : ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = g * b * g⁻¹)
    {w : Equiv.Perm (Fin n)} (hw : ∀ (b : ↥Bs) (i : Fin n), eta (φ b) (w i) = eta b i)
    (i j : Fin n) :
    (ggBsCoordEq Bs eta i j).map (MulAut.conj g).toMonoidHom = ggBsCoordEq Bs eta (w i) (w j) := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨b, hb, rfl⟩ := hx
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hbBs : b ∈ Bs := ggBsCoordEq_le (Bs := Bs) (eta := eta) i j hb
    have hbs : g * b * g⁻¹ ∈ Bs := by
      rw [← hφ ⟨b, hbBs⟩]
      exact (φ ⟨b, hbBs⟩).2
    refine (mem_ggBsCoordEq (Bs := Bs) (eta := eta) (g := g * b * g⁻¹)).mpr
      ⟨hbs, ?_⟩
    have hsub : (⟨g * b * g⁻¹, hbs⟩ : ↥Bs) = φ ⟨b, hbBs⟩ :=
      Subtype.ext (hφ ⟨b, hbBs⟩).symm
    have hb' : eta ⟨b, hbBs⟩ i = eta ⟨b, hbBs⟩ j :=
      (coe_mem_ggBsCoordEq (Bs := Bs) (eta := eta) (i := i) (j := j)
        (b := ⟨b, hbBs⟩)).mp hb
    rw [hsub, hw ⟨b, hbBs⟩ i, hw ⟨b, hbBs⟩ j, hb']
  · intro hx
    rw [Subgroup.mem_map]
    rw [mem_ggBsCoordEq] at hx
    obtain ⟨hbs, heq⟩ := hx
    refine ⟨((φ.symm ⟨x, hbs⟩ : ↥Bs) : G), ?_, ?_⟩
    · rw [coe_mem_ggBsCoordEq]
      have h1 := hw (φ.symm ⟨x, hbs⟩) i
      have h2 := hw (φ.symm ⟨x, hbs⟩) j
      rw [MulEquiv.apply_symm_apply] at h1 h2
      rw [← h1, ← h2]
      exact heq
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hφ (φ.symm ⟨x, hbs⟩),
        MulEquiv.apply_symm_apply]

theorem ggBsCoordZero_map_conj (hφ : ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = g * b * g⁻¹)
    {w : Equiv.Perm (Fin n)} (hw : ∀ (b : ↥Bs) (i : Fin n), eta (φ b) (w i) = eta b i)
    (j : Fin n) :
    (ggBsCoordZero Bs eta j).map (MulAut.conj g).toMonoidHom = ggBsCoordZero Bs eta (w j) := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨b, hb, rfl⟩ := hx
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hbBs : b ∈ Bs := ggBsCoordZero_le (Bs := Bs) (eta := eta) j hb
    have hbs : g * b * g⁻¹ ∈ Bs := by
      rw [← hφ ⟨b, hbBs⟩]
      exact (φ ⟨b, hbBs⟩).2
    refine (mem_ggBsCoordZero (Bs := Bs) (eta := eta) (g := g * b * g⁻¹)).mpr
      ⟨hbs, ?_⟩
    have hsub : (⟨g * b * g⁻¹, hbs⟩ : ↥Bs) = φ ⟨b, hbBs⟩ :=
      Subtype.ext (hφ ⟨b, hbBs⟩).symm
    have hb' : eta ⟨b, hbBs⟩ j = 1 :=
      (coe_mem_ggBsCoordZero (Bs := Bs) (eta := eta) (j := j) (b := ⟨b, hbBs⟩)).mp hb
    rw [hsub, hw ⟨b, hbBs⟩ j, hb']
  · intro hx
    rw [Subgroup.mem_map]
    rw [mem_ggBsCoordZero] at hx
    obtain ⟨hbs, heq⟩ := hx
    refine ⟨((φ.symm ⟨x, hbs⟩ : ↥Bs) : G), ?_, ?_⟩
    · rw [coe_mem_ggBsCoordZero]
      have h1 := hw (φ.symm ⟨x, hbs⟩) j
      rw [MulEquiv.apply_symm_apply] at h1
      rw [← h1]
      exact heq
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hφ (φ.symm ⟨x, hbs⟩),
        MulEquiv.apply_symm_apply]

theorem ggReflComm_map_conj (hφ : ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = g * b * g⁻¹)
    {w : Equiv.Perm (Fin n)} (hw : ∀ (b : ↥Bs) (i : Fin n), eta (φ b) (w i) = eta b i)
    (i j : Fin n) :
    (⁅Subgroup.centralizer (ggBsCoordEq Bs eta i j : Set G), Bs⁆).map
        (MulAut.conj g).toMonoidHom =
      ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (w i) (w j) : Set G), Bs⁆ := by
  rw [Subgroup.map_commutator, CFSG.Glauberman.map_centralizer_eq_of_equiv (MulAut.conj g),
    ggBsCoordEq_map_conj hφ hw i j, ggBs_map_conj hφ]

theorem ggSingletonComm_map_conj (hφ : ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = g * b * g⁻¹)
    {w : Equiv.Perm (Fin n)} (hw : ∀ (b : ↥Bs) (i : Fin n), eta (φ b) (w i) = eta b i)
    (j : Fin n) :
    (⁅Subgroup.centralizer (ggBsCoordZero Bs eta j : Set G), Bs⁆).map
        (MulAut.conj g).toMonoidHom =
      ⁅Subgroup.centralizer (ggBsCoordZero Bs eta (w j) : Set G), Bs⁆ := by
  rw [Subgroup.map_commutator, CFSG.Glauberman.map_centralizer_eq_of_equiv (MulAut.conj g),
    ggBsCoordZero_map_conj hφ hw j, ggBs_map_conj hφ]

end Equivariance

end CFSG.StandardType

end
