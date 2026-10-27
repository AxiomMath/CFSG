module

public import CFSG.Quasithin.H13.L32ACSkPfH

public section

namespace CFSG.Quasithin.H13.L32A.C.SkPf

open CFSG.Quasithin

theorem n3At_of_n4At {M : Type} [Group M] {U : Subgroup M} (h : N4At M U) : N3At M U := by
  intro α β hα hβ hαU _ hinv hαc _
  rcases h α hα hαU hαc with ⟨x, rfl⟩ | hL
  · refine Or.inl ⟨x * β x⁻¹, ?_⟩
    have h1 : MulAut.conj (β x⁻¹) = β * (MulAut.conj x)⁻¹ * β⁻¹ := by
      rw [← mul_conj_mul_inv, map_inv]
    rw [map_mul, h1, show MulAut.conj x * (β * (MulAut.conj x)⁻¹ * β⁻¹) =
      MulAut.conj x * β * (MulAut.conj x)⁻¹ * β⁻¹ by group, hinv]
    calc β⁻¹ * β⁻¹ = β⁻¹ * β⁻¹ * β ^ 3 := by rw [hβ, mul_one]
      _ = β := by group
  · exact Or.inr hL

theorem n3Model_of_n4Model {M : Type} [Group M] (h : N4Model M) : N3Model M :=
  fun U hU => n3At_of_n4At (h U hU)

theorem lieBorelThreeInner_holds :
    LieBorelThreeInner :=
  lieBorelThreeInner_of fun _ _ _ _ hn _ hL =>
    n3Model_of_n4Model (n2Model_n4Model_of_isLieChar2 hn hL).2

end CFSG.Quasithin.H13.L32A.C.SkPf
