module

public import CFSG.LocalAnalysis.StandardType.GGExcCompFieldInput
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.StandardType.A6Red

open CFSG.Assembly CFSG.StandardType

theorem a6glue_isComponentOf_map_mulEquiv {G G' : Type*} [Group G] [Group G']
    (e : G ≃* G') {L K : Subgroup G} (h : IsComponentOf L K) :
    IsComponentOf (L.map e.toMonoidHom) (K.map e.toMonoidHom) :=
  ⟨Subgroup.map_mono h.1,
   CFSG.Assembly.IsSubnormal.map e.toMonoidHom h.2.1,
   CFSG.Assembly.IsQuasisimple.of_mulEquiv
     (Subgroup.equivMapOfInjective L e.toMonoidHom e.injective).symm h.2.2⟩

theorem a6glue_map_centralizer {G : Type*} [Group G] (e : G ≃* G) (A : Subgroup G) :
    (Subgroup.centralizer (A : Set G)).map e.toMonoidHom =
      Subgroup.centralizer (A.map e.toMonoidHom : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp ha
    have hy' : b * y = y * b := hy b hb
    rw [← map_mul, ← map_mul, hy']
  · intro hx
    refine Subgroup.mem_map.mpr ⟨e.symm x, ?_, by simp⟩
    intro a ha
    have h := hx (e a) (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩)
    have h2 := congrArg (⇑e.symm) h
    simpa using h2

theorem a6glue_ggCompFieldAt_congr {G H : Type} [Group G] [Group H]
    {X : Subgroup G} {Y : Subgroup H} {Q : ℕ}
    (h : GGCompFieldAt Q X) (θ : ↥X ≃* ↥Y) : GGCompFieldAt Q Y := by
  obtain ⟨lab, hlab, hchar, hdeg, h1, h2, h3, hhas, R, instR, hR, ⟨φ⟩⟩ := h
  let : Group R := instR
  have hq : (↥X ⧸ Subgroup.center ↥X) ≃* (↥Y ⧸ Subgroup.center ↥Y) :=
    QuotientGroup.congr _ _ θ (Subgroup.map_center_eq θ)
  have hhas' : GGHasLabel lab (↥Y ⧸ Subgroup.center ↥Y) := by
    unfold GGHasLabel at hhas ⊢
    refine largeEvenRawDatum_mono ?_ hhas
    rintro R' _ I F ⟨ψ⟩
    exact ⟨hq.symm.trans ψ⟩
  exact ⟨lab, hlab, hchar, hdeg, h1, h2, h3, hhas', R, instR, hR, ⟨hq.symm.trans φ⟩⟩

end CFSG.StandardType.A6Red
