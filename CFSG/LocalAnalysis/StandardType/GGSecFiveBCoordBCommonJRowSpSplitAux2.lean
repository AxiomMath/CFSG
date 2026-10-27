module

public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticDiag
public import CFSG.LocalAnalysis.StandardType.GGTableBRank

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.Open (StatedSp)

theorem ggCommonJSpSplit_conj {K : Type} [Field K] [Finite K] {p r : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0) {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    (E : Subgroup (StatedSp r K)) (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ r) :
    ∃ P : StatedSp r K,
      E = (TableBSymp.spTorusSp (m := r) hζ).range.map (MulAut.conj P).toMonoidHom := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let S := StatedSp r K
  let τ : (Fin r → Multiplicative (ZMod p)) →* S := TableBSymp.spTorusSp (m := r) hζ
  let E' : Subgroup (GL (Fin r ⊕ Fin r) K) := E.map S.subtype
  have hE'ab : IsElemAbelian p E' := TableB.isElemAbelian_map hE S.subtype
  have hE'Sp : E' ≤ LargeEvenSpGroup K r := Subgroup.map_subtype_le E
  have hcard' : p ^ r ≤ Nat.card E' := by
    rw [show Nat.card E' = Nat.card E from
      Subgroup.card_map_of_injective S.subtype_injective, hcard]
  obtain ⟨P, hP, hPE⟩ := TableBSymp.exists_conj_eq_range_spTorusGL (m := r) (E := E')
    hp2 hpK hζo hζ hE'Sp hE'ab hcard'
  let P₀ : S := ⟨P, hP⟩
  have hTor : (TableBSymp.spTorusGL (m := r) hζ).range = τ.range.map S.subtype := by
    ext x
    simp [τ, TableBSymp.spTorusSp]
  have hE'_eq : E' = (TableBSymp.spTorusGL (m := r) hζ).range.map
      (MulAut.conj P).toMonoidHom := by
    refine Subgroup.map_injective (f := (MulAut.conj P⁻¹).toMonoidHom)
      (MulAut.conj P⁻¹).injective ?_
    rw [hPE, Subgroup.map_map]
    have hcomp : (MulAut.conj P⁻¹).toMonoidHom.comp (MulAut.conj P).toMonoidHom =
        MonoidHom.id (GL (Fin r ⊕ Fin r) K) := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
    rw [hcomp, Subgroup.map_id]
  have hcomp : (MulAut.conj P).toMonoidHom.comp S.subtype =
      S.subtype.comp (MulAut.conj P₀).toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_subtype, P₀]
  have hfin : E' = (τ.range.map (MulAut.conj P₀).toMonoidHom).map S.subtype := by
    rw [hE'_eq, hTor, Subgroup.map_map, hcomp, ← Subgroup.map_map]
  refine ⟨P₀, ?_⟩
  refine Subgroup.map_injective (f := S.subtype) S.subtype_injective ?_
  simpa only [E'] using hfin
end CFSG.StandardType

end
