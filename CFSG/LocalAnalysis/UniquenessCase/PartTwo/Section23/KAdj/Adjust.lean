module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.ReduceLine

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.Quasithin

open scoped Pointwise

theorem exists_mulEquiv_map_sylow_eq {G₁ G₂ : Type*} [Group G₁] [Group G₂] [Finite G₁]
    {p : ℕ} [Fact p.Prime] (φ₀ : G₁ ≃* G₂) {Q : Subgroup G₁} (U : Sylow p G₁)
    (hU : (U : Subgroup G₁) ≤ Q) (S : Sylow p G₂)
    (hS : (S : Subgroup G₂) ≤ Q.map φ₀.toMonoidHom) :
    ∃ φ : G₁ ≃* G₂, (U : Subgroup G₁).map φ.toMonoidHom = S ∧
      Q.map φ.toMonoidHom = Q.map φ₀.toMonoidHom := by
  haveI : Finite G₂ := Finite.of_surjective φ₀ φ₀.surjective
  let V : Sylow p G₁ :=
    S.mapSurjective (f := φ₀.symm.toMonoidHom) φ₀.symm.surjective
  have hVcoe : (V : Subgroup G₁) = S.map φ₀.symm.toMonoidHom := rfl
  have hVle : (V : Subgroup G₁) ≤ Q := by
    rw [hVcoe, Subgroup.map_le_iff_le_comap,
      Subgroup.comap_equiv_eq_map_symm' φ₀.symm Q]
    simpa using hS
  haveI : Finite (Sylow p Q) := Sylow.finite_of_finiteIndex (U.subtype hU)
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq Q (U.subtype hU) (V.subtype hVle)
  rw [Sylow.smul_subtype] at hy
  have hUV : (y : G₁) • U = V := Sylow.subtype_injective hy
  have hUs : (U : Subgroup G₁).map (MulAut.conj (y : G₁)).toMonoidHom =
      (((y : G₁) • U : Sylow p G₁) : Subgroup G₁) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] <;> rfl
  have hconj : Q.map (MulAut.conj (y : G₁)).toMonoidHom = Q :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer y.2)
  have htrans : ((MulAut.conj (y : G₁)).trans φ₀).toMonoidHom =
      φ₀.toMonoidHom.comp (MulAut.conj (y : G₁)).toMonoidHom :=
    MulEquiv.toMonoidHom_trans _ _
  have hsymm : φ₀.toMonoidHom.comp φ₀.symm.toMonoidHom = MonoidHom.id G₂ :=
    MulEquiv.toMonoidHom_comp_toMonoidHom_symm φ₀
  refine ⟨(MulAut.conj (y : G₁)).trans φ₀, ?_, ?_⟩
  · calc (U : Subgroup G₁).map ((MulAut.conj (y : G₁)).trans φ₀).toMonoidHom
        = ((U : Subgroup G₁).map (MulAut.conj (y : G₁)).toMonoidHom).map φ₀.toMonoidHom := by
          rw [htrans, ← Subgroup.map_map]
      _ = (((y : G₁) • U : Sylow p G₁) : Subgroup G₁).map φ₀.toMonoidHom := by rw [hUs]
      _ = (V : Subgroup G₁).map φ₀.toMonoidHom := by rw [hUV]
      _ = S := by
          rw [hVcoe, Subgroup.map_map, hsymm, Subgroup.map_id]
  · rw [htrans, ← Subgroup.map_map, hconj]

theorem sylow_le_pointStab {W : Type} [CommGroup W] (H : Subgroup (MulAut W)) (S : Sylow 2 ↥H) :
    (S : Subgroup ↥H) ≤ KTabD.pointStab H S := by
  intro s hs
  letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
  letI : MulAction ↥H W := MulAction.compHom W H.subtype
  letI : MulAction ↥H (Set W) := Set.mulActionSet
  letI : MulDistribMulAction ↥S W :=
    MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
  show s ∈ MulAction.stabilizer ↥H
    ((CFSG.fixedPointSubgroup ↥S W : Subgroup W) : Set W)
  rw [MulAction.mem_stabilizer_set]
  intro b
  have hmem : ∀ x : W, x ∈ (CFSG.fixedPointSubgroup ↥S W : Subgroup W) ↔
      ∀ z : ↥S, z • x = x := fun x => by
    rw [FixedPoints.mem_subgroup]
  simp only [SetLike.mem_coe, hmem]
  have hsb : s • b = (⟨s, hs⟩ : ↥S) • b := rfl
  constructor
  · intro h
    have h1 := h (⟨s, hs⟩ : ↥S)⁻¹
    have h2 : (⟨s, hs⟩ : ↥S)⁻¹ • (s • b) = b := by
      rw [hsb, smul_smul, inv_mul_cancel, one_smul]
    have hb : b = s • b := h2.symm.trans h1
    intro z
    calc z • b = z • (s • b) := congrArg (fun t => z • t) hb
      _ = s • b := h z
      _ = b := hb.symm
  · intro h z
    rw [hsb, smul_smul]
    exact (h (z * ⟨s, hs⟩)).trans (h ⟨s, hs⟩).symm

theorem exists_mulEquiv_pointStab_eq_map_sylow {W : Type} [CommGroup W] [Finite W]
    {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K] {Γ : Subgroup (GL ι K)}
    {H : Subgroup (MulAut W)} (hreal : (FFModel.nat Γ).Realizes H ⊤ ⊥) {e₀ : ι → K}
    (hline : KTabC.SylowFixedLine Γ e₀) (U : Sylow 2 ↥Γ)
    (hU : (U : Subgroup ↥Γ) ≤ KTabD.lineStab Γ e₀) (S : Sylow 2 ↥H) :
    ∃ φ : ↥Γ ≃* ↥H, (U : Subgroup ↥Γ).map φ.toMonoidHom = S ∧
      KTabD.pointStab H S = (KTabD.lineStab Γ e₀).map φ.toMonoidHom := by
  obtain ⟨φ₀, hφ₀⟩ := KTabD.exists_mulEquiv_pointStab_eq_map hreal hline S
  have hS : (S : Subgroup ↥H) ≤ (KTabD.lineStab Γ e₀).map φ₀.toMonoidHom := by
    rw [← hφ₀]
    exact sylow_le_pointStab H S
  obtain ⟨φ, hφU, hφQ⟩ :=
    exists_mulEquiv_map_sylow_eq (Q := KTabD.lineStab Γ e₀) φ₀ U hU S hS
  exact ⟨φ, hφU, by rw [hφQ]; exact hφ₀⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
