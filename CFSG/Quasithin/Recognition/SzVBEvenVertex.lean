module

public import CFSG.Quasithin.Recognition.SzVBEvenBasic
public import CFSG.Quasithin.Recognition.SzVBConj

public section

namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T V : Subgroup G} {z : G}

omit [Finite G] in
theorem conjSub_zpowers_eq (g x : G) :
    conjSub g (Subgroup.zpowers x) = Subgroup.zpowers (g * x * g⁻¹) := by
  unfold conjSub
  rw [MonoidHom.map_zpowers]
  rfl

omit [Finite G] in
theorem exists_vertexData (hC : EvenCtx G₀ G₁ G₂ T V z) {x : CosetGeom G₀ G₁ G₂}
    (hx : vtype x = true) :
    ∃ (P S V' : Subgroup G) (z' : G), stab x = P ∧ Vv V x = conjClosure V' P ∧
      Zv z x = Subgroup.zpowers z' ∧ KleinData P V' z' ∧ BenderLocalFacts P S V' := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₁ hx
  refine ⟨conjSub (g : G) G₂, conjSub (g : G) T, conjSub (g : G) V, (g : G) * z * (g : G)⁻¹,
    ?_, ?_, ?_, hC.klein.conj _, hC.bender.conj _⟩
  · rw [stab_smul, stab_γ₁ hC.hyp.le₂]
  · rw [Vv_smul hC.hyp.normalizes, Vv_γ₁ hC.hyp.le₂ hC.hyp.normalizes, conjSub_conjClosure]
  · rw [Zv_smul_γ₁ (G₂_le_normalizer_zpowers hC.toGeoCtx), conjSub_zpowers_eq]

end CFSG.Quasithin.SzVB
