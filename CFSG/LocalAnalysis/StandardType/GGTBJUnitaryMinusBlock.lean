module

public import CFSG.LocalAnalysis.StandardType.GGTBJUnitaryMinusDefs
public import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenWeyl
public import CFSG.LocalAnalysis.StandardType.GGRealKGCoverComp
public import CFSG.LocalAnalysis.StandardType.GGTBJUnitaryMinusBlockAuxCover
import CFSG.LocalAnalysis.StandardType.GGTBJUnitaryMinusBlockAuxRot

public section

namespace CFSG.StandardType.SuSplitRootGen

open CFSG CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.CALinearPlane

theorem exists_alignedBlock_of_isComponentOf_centralizer
    {F : Type} [Field F] [Finite F] {f m ε p : ℕ} [Fact p.Prime]
    (h : UnitaryFieldData 2 f F) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f - 1) (hε : ε ≤ 1)
    {ζ : F} (hζ : IsPrimitiveRoot ζ p) (hζb : h.bar ζ = ζ)
    {τ : Multiplicative (Fin m → ZMod p) →* hypSU h m ε} (hτ : IsSplitTorus h ζ τ)
    (E : Set (Multiplicative (Fin m → ZMod p))) {J : Subgroup (hypSU h m ε)}
    (hJ : IsComponentOf J (Subgroup.centralizer (τ '' E))) :
    (∃ S : Finset (Fin m), S.Nonempty ∧ J = hypBlock h (zeroCoords S)) ∨
      ∃ (S : Finset (Fin m)) (s : Fin m → ZMod p) (w : hypSU h m ε),
        (∀ i, s i = 1 ∨ s i = -1) ∧
        (∀ t : Fin m → ZMod p,
          w * τ (Multiplicative.ofAdd t) * w⁻¹ =
            τ (Multiplicative.ofAdd fun i => s i * t i)) ∧
        2 ≤ S.card ∧
        J = (coordBlockSL F S).map ((MulAut.conj w).toMonoidHom.comp (leviSU h ε)) := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨a, hJle⟩ :=
    exists_le_weightPairBlock_of_isComponentOf (h := h) (ε := ε) hp hp2 hε hζ hζb hτ
      (E := E) hJ
  by_cases hz : ∃ t : Fin m → ZMod p,
      Multiplicative.ofAdd t ∈ E ∧ splitWeight (ε := ε) a t ≠ 0
  · obtain ⟨S, s, w, hs, hw, hcard, hJeq⟩ :=
      exists_eq_map_coordBlockSL_of_ne_zero_weight (h := h) (ε := ε) hp hp2 hpq hζ hτ
        (E := E) hJ (a := a) hJle hz
    exact Or.inr ⟨S, s, w, hs, hw, hcard, hJeq⟩
  · left
    have hz0 : ∀ t : Fin m → ZMod p,
        Multiplicative.ofAdd t ∈ E → splitWeight (ε := ε) a t = 0 := by
      intro t ht
      by_contra hne
      exact hz ⟨t, ht, hne⟩
    have hJle' : J ≤ Subgroup.centralizer (τ '' E) ⊓
        hypBlock h (weightClass E a ∪ weightClassPartner E a) := by
      simpa only [weightPairBlock] using hJle
    obtain ⟨S, hS, hJeq⟩ :=
      exists_eq_zeroBlock_of_isComponentOf (h := h) (ε := ε) hp hpq hε hτ
        (E := E) hJ (a := a) hJle' hz0
    refine ⟨S, hS, ?_⟩
    rw [hJeq]
    rw [show (MulAut.conj (1 : hypSU h m ε)).toMonoidHom = MonoidHom.id _ from by
      ext x
      simp, Subgroup.map_id]

theorem exists_alignedBlock_of_isComponentOf
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] {f m ε p : ℕ}
    [Fact p.Prime] (h : UnitaryFieldData 2 f F) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f - 1)
    (hε : ε ≤ 1) {ζ : F} (hζ : IsPrimitiveRoot ζ p) (hζb : h.bar ζ = ζ)
    {τ : Multiplicative (Fin m → ZMod p) →* hypSU h m ε} (hτ : IsSplitTorus h ζ τ)
    {φ : hypSU h m ε →* G} (hker : φ.ker ≤ Subgroup.center (hypSU h m ε))
    (hkp : ∀ z ∈ φ.ker, z ^ p = 1 → z = 1) {C : Set G}
    (hC : ∀ c ∈ C, ∃ v, ∀ g ∈ φ.range, c * g * c⁻¹ = hypFrame φ τ v * g * (hypFrame φ τ v)⁻¹)
    {J : Subgroup G} (hJ : IsComponentOf J (φ.range ⊓ Subgroup.centralizer C)) :
    (∃ S : Finset (Fin m), S.Nonempty ∧ J = (hypBlock h (zeroCoords S)).map φ) ∨
      ∃ (S : Finset (Fin m)) (s : Fin m → ZMod p) (w : hypSU h m ε),
        (∀ i, s i = 1 ∨ s i = -1) ∧
        (∀ t : Fin m → ZMod p,
          w * τ (Multiplicative.ofAdd t) * w⁻¹ =
            τ (Multiplicative.ofAdd fun i => s i * t i)) ∧
        2 ≤ S.card ∧
        J = (coordBlockSL F S).map ((φ.comp (MulAut.conj w).toMonoidHom).comp (leviSU h ε)) :=
  exists_alignedBlock_of_isComponentOf_of_centralizer
    (hmain := fun E _K hK =>
      exists_alignedBlock_of_isComponentOf_centralizer h hp2 hpq hε hζ hζb hτ E hK)
    hker hkp hC hJ

end CFSG.StandardType.SuSplitRootGen

end
