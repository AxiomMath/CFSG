module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2ModelData
public import CFSG.GH74.GLS.Stage4.HexModelG2
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsG2Data

public noncomputable section

namespace CFSG.Quasithin.H13.F431.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.GH74.GLS.Stage4.Hex CFSG.QuasithinUnique

section Generic

theorem isSylowTwoOf_map_equiv {G H : Type} [Group G] [Group H] [Finite G] (e : G ≃* H)
    {U : Subgroup G} (hU : IsSylowTwoOf U ⊤) : IsSylowTwoOf (U.map e.toMonoidHom) ⊤ := by
  have : Finite H := Finite.of_equiv G e.toEquiv
  have h := CFSG.QuasithinUnique.Setup.X6.isSylowOf_map_injective (p := 2) e.toMonoidHom
    e.injective (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.1 hU)
  rw [Subgroup.map_top_of_surjective _ e.surjective] at h
  exact CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.2 h

end Generic

section Plain

variable {K : Type} [Field K]

@[expose] def proj (K : Type) [Field K] : ↥(adjointGroup .G2 K) →* AdjointQuotient .G2 K :=
  hexProj ↥(adjointGroup .G2 K)

theorem proj_injective [Finite K] : Function.Injective (proj K) := by
  rw [← MonoidHom.ker_eq_bot_iff, proj, ker_hexProj]
  exact center_adjointGroup_eq_bot

@[expose] def mk (K : Type) [Field K] [Finite K] :
    ↥(adjointGroup .G2 K) ≃* AdjointQuotient .G2 K :=
  MulEquiv.ofBijective (proj K) ⟨proj_injective, hexProj_surjective⟩

theorem mk_toMonoidHom [Finite K] : (mk K).toMonoidHom = proj K := rfl

theorem g2_quot_data {D : Type} [Group D] {f : ℕ} (hD : LieModel D .G2 0 2 f) :
    2 ≤ f ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (_ : 3 ≤ Nat.card K),
      Nat.card K = 2 ^ f ∧ Nonempty (AdjointQuotient .G2 K ≃* D) := by
  obtain ⟨hf, K, hF, hFin, hcp, hK, ⟨e⟩⟩ := g2_model_data hD
  have h3 : 3 ≤ Nat.card K := by
    rw [hK]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  exact ⟨hf, K, hF, hFin, hcp, h3, hK, ⟨(mk K).symm.trans e.symm⟩⟩

end Plain

section Hex

variable {K : Type} [Field K]

theorem isSimpleGroup_adjointQuotient (hK : 3 ≤ Nat.card K) :
    IsSimpleGroup (AdjointQuotient .G2 K) :=
  isSimpleGroup_g2Model hK

theorem isSimpleGroup_adjointGroup [Finite K] (hK : 3 ≤ Nat.card K) :
    IsSimpleGroup ↥(adjointGroup .G2 K) :=
  haveI := isSimpleGroup_adjointQuotient hK
  (mk K).isSimpleGroup

theorem posUnipotentSub_eq : posUnipotentSub .G2 K = posUnipotent (g2Datum K) := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    have hle : posUnipotent Tag.G2 K ≤
        (posUnipotent (g2Datum K)).map (adjointGroup Tag.G2 K).subtype := by
      refine iSup₂_le fun α hα => ?_
      have hroot : IsRoot Tag.G2 α := hα.1
      have h1 : rootGroup (rootOperatorFamily Tag.G2) K α ≤ posUnipotent (g2Datum K) :=
        rootGroup_le_posUnipotent (mem_adjDatum_roots.2 hroot) hα.2
      have h2 : rootGroup (rootOperatorFamily Tag.G2) K α =
          (rootSubgroup Tag.G2 K α).subgroupOf (adjointGroup Tag.G2 K) := by
        rw [rootGroup_of_isRoot hroot,
          ← (rootOperatorFamily Tag.G2).subgroupOf_rootSubgroup_eq K ⟨α, hroot⟩]
      calc rootSubgroup Tag.G2 K α
          = ((rootSubgroup Tag.G2 K α).subgroupOf (adjointGroup Tag.G2 K)).map
              (adjointGroup Tag.G2 K).subtype :=
            (Subgroup.map_subgroupOf_eq_of_le (rootSubgroup_le_adjointGroup α)).symm
        _ ≤ _ := Subgroup.map_mono (h2 ▸ h1)
    obtain ⟨y, hy, hyx⟩ := hle hx
    exact (Subtype.ext hyx : y = x) ▸ hy
  · refine iSup₂_le fun γ hγ => ?_
    have hroot : IsRoot Tag.G2 γ := mem_adjDatum_roots.1 hγ.1
    change rootGroup (rootOperatorFamily Tag.G2) K γ ≤ _
    rw [rootGroup_of_isRoot hroot,
      ← (rootOperatorFamily Tag.G2).subgroupOf_rootSubgroup_eq K ⟨γ, hroot⟩]
    exact Subgroup.comap_mono (le_iSup₂_of_le (f := fun α (_ : α ∈ {α | IsRoot Tag.G2 α ∧
      0 < height α}) => rootSubgroup Tag.G2 K α) γ ⟨hroot, hγ.2⟩ le_rfl)

theorem map_posUnipotentSub [Finite K] (hK : 3 ≤ Nat.card K) :
    (posUnipotentSub .G2 K).map (mk K).toMonoidHom = (g2ModelSystem K hK).U := by
  rw [posUnipotentSub_eq]
  rfl

theorem isSylowTwoOf_modelU [Finite K] [CharP K 2] (hK : 3 ≤ Nat.card K) :
    IsSylowTwoOf (g2ModelSystem K hK).U ⊤ := by
  rw [← map_posUnipotentSub hK]
  exact isSylowTwoOf_map_equiv (mk K) CFSG.Quasithin.H13.Sec53F.G2.g2_sylow

end Hex

end CFSG.Quasithin.H13.F431.G2
