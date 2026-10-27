module

public import CFSG.Quasithin.Background.G6Basic

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G]

theorem map_pCore_two_normal {K : Subgroup G} [hK : K.Normal] :
    ((pCore 2 K).map K.subtype).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hn
  let e : K ≃* K :=
    { toFun := fun x => ⟨g * x * g⁻¹, hK.conj_mem x x.2 g⟩
      invFun := fun x => ⟨g⁻¹ * x * g⁻¹⁻¹, hK.conj_mem x x.2 g⁻¹⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  have hmap : (pCore 2 K).map e.toMonoidHom ≤ pCore 2 K := by
    refine le_sSup ⟨?_, ?_⟩
    · exact Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
    · exact IsPGroup.map (pCore_isPGroup (p := 2) (G := K)) e.toMonoidHom
  have hk' : e k ∈ pCore 2 K := hmap (Subgroup.mem_map_of_mem _ hk)
  exact Subgroup.mem_map.mpr ⟨e k, hk', rfl⟩

theorem pCore_two_residual_eq_bot [Finite G] (ho : pCore 2 G = ⊥) :
    pCore 2 ↥(pResidual 2 G) = ⊥ := by
  haveI : (pResidual 2 G).Normal := G6.pResidual_normal_aux 2
  have hR := map_pCore_two_normal (K := pResidual 2 G)
  have hle : (pCore 2 ↥(pResidual 2 G)).map (pResidual 2 G).subtype ≤ pCore 2 G :=
    le_sSup ⟨hR, IsPGroup.map (pCore_isPGroup (p := 2) (G := ↥(pResidual 2 G)))
      (pResidual 2 G).subtype⟩
  rw [ho, le_bot_iff] at hle
  rw [eq_bot_iff]
  intro x hx
  have hxG : (x : G) ∈ Subgroup.map (pResidual 2 G).subtype (pCore 2 ↥(pResidual 2 G)) :=
    Subgroup.mem_map_of_mem _ hx
  rw [hle, Subgroup.mem_bot] at hxG
  rw [Subgroup.mem_bot]
  exact Subtype.ext hxG

end CFSG.RankThree.GF2n.Tim79a
