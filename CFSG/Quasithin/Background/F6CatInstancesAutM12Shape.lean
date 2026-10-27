module

public import CFSG.Quasithin.Background.F6CatShapeAutM12
public import CFSG.Quasithin.Recognition.M12AmalAutJMain

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.M12AmalAut

namespace F6

theorem autM12AmalgamShapeFact_holds
    : AutM12AmalgamShapeFact := by
  intro W _ _ K₁ K₂ hW hTL _ hQ₂ _ _ hZ₁ hO₂
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eW⟩ := hW
  obtain ⟨m⟩ := autM12PermModel
  let ε : W ≃* AutG := eW.trans m.symm
  obtain ⟨hK₁, hK₂, hne, S, hS⟩ := hTL
  have hS' : IsSylowTwoOf (K₁.map ε.toMonoidHom ⊓ K₂.map ε.toMonoidHom) ⊤ := by
    rw [← Subgroup.map_inf _ _ _ ε.injective, ← hS]
    exact isSylowTwoOf_top_map ε (isSylowTwoOf_top_of_sylow S)
  obtain ⟨φ, hφ⟩ := AutShape.exists_conj (isMaximalTwoLocal_map ε hK₁)
    (isMaximalTwoLocal_map ε hK₂) (fun h => hne (Subgroup.map_injective ε.injective h)) hS'
  have hmap : ∀ K : Subgroup W,
      K.map (ε.trans φ).toMonoidHom = (K.map ε.toMonoidHom).map φ.toMonoidHom := fun K => by
    rw [Subgroup.map_map]
    rfl
  rcases hφ with ⟨hA, hB⟩ | ⟨hB, hA⟩
  ·
    obtain ⟨eK₂⟩ := mulEquiv_of_map_eq (ε.trans φ) ((hmap K₂).trans hB)
    have hinf : (K₁ ⊓ K₂).map (ε.trans φ).toMonoidHom = autData.T := by
      rw [Subgroup.map_inf _ _ _ (ε.trans φ).injective, hmap, hmap, hA, hB, autData.inf_AB]
    obtain ⟨eT⟩ := mulEquiv_of_map_eq (ε.trans φ) hinf
    have hB384 : Nat.card ↥autData.B = 384 := by
      rw [← Nat.card_congr eK₂.toEquiv]
      obtain ⟨e₂⟩ := hQ₂
      have := CFSG.LieType.BorelTits.pCore_normal (G := ↥K₂) 2
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Open.pCore 2 ↥K₂)
      have h3 : Nat.card ↥(Open.pCore 2 ↥K₂) = 2 ^ 6 := by
        rw [← hO₂]
        exact Nat.card_congr ((Open.pCore 2 ↥K₂).equivMapOfInjective _
          K₂.subtype_injective).toEquiv
      rw [h1, Nat.card_congr e₂.toEquiv, h3, Nat.card_perm, Nat.card_fin]
      rfl
    exact ⟨isExtensionOf_of_mulEquiv eT AutShape.T_shape,
      isExtensionOf₃_of_mulEquiv eK₂
        (AutShape.B_shape hB384 (quotientPCoreIsL22_of_mulEquiv eK₂ hQ₂))⟩
  ·
    exfalso
    obtain ⟨eK₁⟩ := mulEquiv_of_map_eq (ε.trans φ) ((hmap K₁).trans hB)
    exact aut_card_center_B_ne_two ((card_centerOf_eq (pCoreOfCongr eK₁)).symm.trans hZ₁)

end F6

end CFSG.Quasithin
