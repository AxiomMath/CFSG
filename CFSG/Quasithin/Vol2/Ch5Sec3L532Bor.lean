module

public import CFSG.Quasithin.Vol2.GoldschmidtF431SpBorel
public import CFSG.Quasithin.Recognition.CertTwoLocal

public section

namespace CFSG.Quasithin.H13.L532

open CFSG.Quasithin CFSG.QuasithinUnique

theorem inf_le_normalizer_of_borelData {X : Type} [Group X] [Finite X] {U R₁ R₂ : Subgroup X}
    (hB : Borel252.BorelData X U R₁ R₂)
    (hO2 : ∀ P : Subgroup X, P.Normal → IsPGroup 2 P → P = ⊥)
    {Y : Type} [Group Y] (e : Y ≃* X) {TY P₁ P₂ : Subgroup Y} (hY : IsYAmalgamPair TY P₁ P₂) :
    P₁ ⊓ P₂ ≤ Subgroup.normalizer (TY : Set Y) := by
  have hy1 := IsYAmalgamPair.map e hY
  obtain ⟨c, -, hc⟩ := IsSylowTwoOf.exists_conj hy1.1 hB.sylow
  let E : Y ≃* X := e.trans (MulAut.conj c)
  have hEmap : ∀ Q : Subgroup Y,
      Q.map E.toMonoidHom = (Q.map e.toMonoidHom).map (MulAut.conj c).toMonoidHom := fun Q => by
    rw [Subgroup.map_map]
    rfl
  have hTE : TY.map E.toMonoidHom = U := by rw [hEmap, ← hc]
  have hy2 : IsYAmalgamPair U (P₁.map E.toMonoidHom) (P₂.map E.toMonoidHom) := by
    have := IsYAmalgamPair.map E hY
    rwa [hTE] at this
  have hinf : (P₁ ⊓ P₂).map E.toMonoidHom = Subgroup.normalizer (U : Set X) := by
    rw [Subgroup.map_inf _ _ _ E.injective, ← hB.inf_norm]
    rcases hB.yam_cases hO2 hy2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, inf_comm]
  have hN : (Subgroup.normalizer (TY : Set Y)).map E.toMonoidHom =
      Subgroup.normalizer (U : Set X) := by
    rw [Subgroup.map_equiv_normalizer_eq, hTE]
  rw [← Subgroup.map_le_map_iff_of_injective (f := E.toMonoidHom) E.injective, hinf, hN]

end CFSG.Quasithin.H13.L532
