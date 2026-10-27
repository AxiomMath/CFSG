module

public import CFSG.LocalAnalysis.StandardType.GGTwE6TorusIndexAux2

public section

namespace CFSG.StandardType.TwE6Tori

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.LangTorus

theorem twE6_image_le_torus_index
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ 2)
    (D : LangDatum TwistTag.E6.tag L) (hΦ : D.Φ = twistHom TwistTag.E6 L Fr)
    (ω : List (Fin Tag.E6.rank))
    (hn : D.n = canonicalRep (coxeterSystem Tag.E6) L ((coxeterSystem Tag.E6).wordProd ω)) :
    twE6Image Fr ω ≤ D.torus ∧ Nat.card (twE6Image Fr ω) * 3 = Nat.card D.torus := by
  have htor : D.torus =
      (l10mp2a_AFix Fr ((coxeterSystem Tag.E6).wordProd ω)).map (rootDiagUnitHom Tag.E6 L) := by
    rw [LangDatum.torus, hΦ, hn]
    exact l10mp2a_torus_eq Fr ((coxeterSystem Tag.E6).wordProd ω)
  constructor
  · rw [htor]
    rintro x ⟨c, hc, rfl⟩
    exact Subgroup.mem_map.2 ⟨twE6Cartan c,
      l10mp2a_image_le Fr ω (Subgroup.mem_map.2 ⟨c, hc, rfl⟩), rfl⟩
  · have htor' : D.torus =
        (l10mp2a_AFix Fr ((coxeterSystem Tag.E6).wordProd ω)).map
          (rootDiagUnitHom TwistTag.E6.tag L) := by
      rw [LangDatum.torus, hΦ, hn]
      exact l10mp2a_torus_eq Fr ((coxeterSystem Tag.E6).wordProd ω)
    rw [htor']
    have hmap : twE6Image Fr ω =
        ((twE6Pfix Fr ω).map twE6Cartan).map (rootDiagUnitHom Tag.E6 L) := by
      rw [twE6Image, ← Subgroup.map_map]
    have hB : Nat.card (twE6Image Fr ω) = Nat.card ((twE6Pfix Fr ω).map twE6Cartan) := by
      rw [hmap]
      exact Subgroup.card_map_of_injective CFSG.LieType.Chevalley.rootDiagUnit_injective
    have hA : Nat.card ((l10mp2a_AFix Fr ((coxeterSystem Tag.E6).wordProd ω)).map
        (rootDiagUnitHom TwistTag.E6.tag L)) =
        Nat.card (l10mp2a_AFix Fr ((coxeterSystem Tag.E6).wordProd ω)) :=
      Subgroup.card_map_of_injective CFSG.LieType.Chevalley.rootDiagUnit_injective
    rw [hB, hA]
    exact l10mp2a_card_image Fr hFr ω

end CFSG.StandardType.TwE6Tori

end
