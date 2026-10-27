module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBDenseDefs
import CFSG.LocalAnalysis.StandardType.GGSignedCoordConj
import CFSG.LocalAnalysis.StandardType.GGTBRowSignedFrameAux
import CFSG.Walter.Bender1970.S3.Basic

public section

namespace CFSG.StandardType

theorem map_conj_permAut_bCoordinateBlock {n p : ℕ} (σ : Equiv.Perm (Fin n))
    (j : Fin n) :
    (bCoordinateBlock n p j).map
        (MulAut.conj (SpCoord.permAut (p := p) σ)).toMonoidHom =
      bCoordinateBlock n p (σ j) := by
  apply le_antisymm
  · rw [bCoordinateBlock, MonoidHom.map_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro r ⟨g, (⟨i, hi, rfl⟩ | ⟨a, b, hab, ha, hb, rfl⟩), rfl⟩
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        ggSpSigned_conj_permAut_sgnAut]
      exact Subgroup.subset_closure (Or.inl ⟨σ i, fun h => hi (σ.injective h), rfl⟩)
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, permAut_conj_swap]
      exact Subgroup.subset_closure (Or.inr ⟨σ a, σ b, fun h => hab (σ.injective h),
        fun h => ha (σ.injective h), fun h => hb (σ.injective h), rfl⟩)
  · refine (Subgroup.closure_le _).mpr ?_
    rintro r (⟨c, hc, rfl⟩ | ⟨c, d, hcd, hc, hd, rfl⟩)
    · refine Subgroup.mem_map.mpr ⟨SpCoord.sgnAut (σ⁻¹ c), ?_, ?_⟩
      · exact Subgroup.subset_closure
          (Or.inl ⟨σ⁻¹ c, fun h => hc (by rw [← h]; simp), rfl⟩)
      · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          ggSpSigned_conj_permAut_sgnAut]
        simp
    · refine Subgroup.mem_map.mpr
        ⟨SpCoord.permAut (Equiv.swap (σ⁻¹ c) (σ⁻¹ d)), ?_, ?_⟩
      · refine Subgroup.subset_closure (Or.inr ⟨σ⁻¹ c, σ⁻¹ d, ?_, ?_, ?_, rfl⟩)
        · exact fun h => hcd ((σ⁻¹).injective h)
        · exact fun h => hc (by rw [← h]; simp)
        · exact fun h => hd (by rw [← h]; simp)
      · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, permAut_conj_swap]
        simp

theorem exists_coords_of_map_eq_conj_aPermutationFull {X : Type*} [Group X] {n p : ℕ}
    (eta : X ≃* (Fin n → Multiplicative (ZMod p))) {A𝒦 AL AK : Subgroup (MulAut X)} {i0 : Fin n}
    (h𝒦 : A𝒦.map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hL : AL.map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    {δ : MulAut (Fin n → Multiplicative (ZMod p))} (hδ : δ ∈ bSignedFull n p)
    (hK : AK.map (MulAut.congr eta).toMonoidHom =
      (aPermutationFull n p).map (MulAut.conj δ).toMonoidHom) :
    ∃ eta' : X ≃* (Fin n → Multiplicative (ZMod p)),
      A𝒦.map (MulAut.congr eta').toMonoidHom = bSignedFull n p ∧
      AL.map (MulAut.congr eta').toMonoidHom = bCoordinateBlock n p i0 ∧
      AK.map (MulAut.congr eta').toMonoidHom = aPermutationFull n p := by
  obtain ⟨j', hj'⟩ := exists_map_conj_bCoordinateBlock (δ := δ⁻¹)
    (Subgroup.inv_mem _ hδ) i0
  let τ : MulAut (Fin n → Multiplicative (ZMod p)) :=
    SpCoord.permAut (Equiv.swap j' i0)
  let θ : MulAut (Fin n → Multiplicative (ZMod p)) := τ * δ⁻¹
  have hcongr : (MulAut.congr (eta.trans θ)).toMonoidHom =
      (MulAut.conj θ).toMonoidHom.comp (MulAut.congr eta).toMonoidHom := by
    refine MonoidHom.ext fun φ => MulEquiv.ext fun x => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
      MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.trans_apply,
      MulEquiv.symm_trans_apply]
  have hmap_eq : ∀ H : Subgroup (MulAut X),
      H.map (MulAut.congr (eta.trans θ)).toMonoidHom =
        (H.map (MulAut.congr eta).toMonoidHom).map (MulAut.conj θ).toMonoidHom := by
    intro H; rw [hcongr, ← Subgroup.map_map]
  have hconj_mul : ∀ (S : Subgroup (MulAut (Fin n → Multiplicative (ZMod p))))
      (g h : MulAut (Fin n → Multiplicative (ZMod p))),
      (S.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
        S.map (MulAut.conj (g * h)).toMonoidHom := by
    intro S g h
    rw [Subgroup.map_map]
    congr 1
  have hτ_one : j' = i0 → τ = 1 := by
    intro h
    dsimp only [τ]
    refine MulEquiv.ext fun f => ?_
    rw [SpCoord.permAut_apply, h, Equiv.swap_self]
    rfl
  have hτ_signed : τ ∈ bSignedFull n p := by
    by_cases h : j' = i0
    · rw [hτ_one h]
      exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (Or.inr ⟨j', i0, h, rfl⟩)
  have hτ_perm : τ ∈ aPermutationFull n p := by
    by_cases h : j' = i0
    · rw [hτ_one h]
      exact Subgroup.one_mem _
    · exact Subgroup.subset_closure ⟨j', i0, h, rfl⟩
  have hθ : θ ∈ bSignedFull n p := by
    dsimp only [θ]
    exact Subgroup.mul_mem _ hτ_signed (Subgroup.inv_mem _ hδ)
  refine ⟨eta.trans θ, ?_, ?_, ?_⟩
  · have h1 := hmap_eq A𝒦
    rw [h1, h𝒦]
    exact CFSG.Walter.map_conj_eq_self_of_mem hθ
  · have h1 := hmap_eq AL
    rw [h1, hL, (hconj_mul _ τ δ⁻¹).symm, hj']
    dsimp only [τ]
    rw [map_conj_permAut_bCoordinateBlock]
    simp
  · have h1 := hmap_eq AK
    rw [h1, hK, hconj_mul _ θ δ]
    have hθδ : θ * δ = τ := by dsimp only [θ]; group
    rw [hθδ]
    exact CFSG.Walter.map_conj_eq_self_of_mem hτ_perm

theorem GGSecFiveBCoordBDenseNbr.exists_coords {G : Type} [Group G] {p n : ℕ}
    {Bs L : Subgroup G} {𝒦 : Finset (Subgroup G)} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {i0 : Fin n} {K : Subgroup G}
    (h𝒦 : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    (hK : GGSecFiveBCoordBDenseNbr p Bs 𝒦 n eta K) :
    ∃ eta' : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)),
      (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta').toMonoidHom = bSignedFull n p ∧
      (ggAutomizer L Bs).map (MulAut.congr eta').toMonoidHom = bCoordinateBlock n p i0 ∧
      (ggAutomizer K Bs).map (MulAut.congr eta').toMonoidHom = aPermutationFull n p := by
  obtain ⟨-, δ, hδ, hKδ⟩ := hK
  exact exists_coords_of_map_eq_conj_aPermutationFull (eta := eta)
    (A𝒦 := ggAutomizerJoin L Bs 𝒦) (AL := ggAutomizer L Bs)
    (AK := ggAutomizer K Bs) h𝒦 hL hδ hKδ

end CFSG.StandardType

end
