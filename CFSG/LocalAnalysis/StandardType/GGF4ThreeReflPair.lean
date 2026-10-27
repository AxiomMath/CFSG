module

public import CFSG.LocalAnalysis.StandardType.GGF4AutWeylTableB
public import CFSG.LocalAnalysis.StandardType.GGF4NbrAutReflKGReduce
public import CFSG.LocalAnalysis.StandardType.GGF4ThreeNbrInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LieType.SeitzGeneration
open CFSG.Open (IsElemAbelian)

namespace F4AutWeyl

theorem exists_reflPair_of_card
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup (adjointGroup .F4 K)} (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 4) :
    ∃ r ∈ ggInduced ⊤ E, ∃ r' ∈ ggInduced ⊤ E, GGIsReflection p r ∧ GGIsReflection p r' ∧
      4 ∣ orderOf (r * r') := by
  classical
  have hq2 : p ∣ Nat.card K ^ 2 - 1 := dvd_card_sq_sub_one_of_card_F4 hp hp2 hE hcard
  let L := FiniteField.Extension K 2 2
  have hLK : Nat.card L = Nat.card K ^ 2 := FiniteField.natCard_extension K 2 2
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have hpL : p ∣ Nat.card L - 1 := hLK ▸ hq2
  obtain ⟨ψ, hψinj, hEV, hcos⟩ := exists_descent_F4 hp hp2 hE hcard
  have hW : ∀ w : WeylGroup .F4, ∃ h ∈ (⊤ : Subgroup (adjointGroup .F4 K)).map ψ,
      ∃ t ∈ torusGroup .F4 L, (h : ModGL .F4 L) = t * canonicalRep (coxeterSystem .F4) L w := by
    intro w
    obtain ⟨k, t, ht, hkt⟩ := hcos w
    exact ⟨ψ k, ⟨k, Subgroup.mem_top k, rfl⟩, t, ht, hkt⟩
  have hA := ggAutomizer_torusPow_eq_range hp hp2 hpL hW
  rw [ggAutomizer_map_eq hψinj ⊤ E hEV] at hA
  set e := (E.equivMapOfInjective ψ hψinj).trans (MulEquiv.subgroupCongr hEV) with he
  have hpre : ∀ w, ∃ r ∈ ggAutomizer ⊤ E, MulAut.congr e r = weylTorusAut L p w := by
    intro w
    have hw : weylTorusAut L p w ∈ (ggAutomizer ⊤ E).map (MulAut.congr e).toMonoidHom := by
      rw [hA]; exact ⟨w, rfl⟩
    obtain ⟨r, hr, hrw⟩ := hw
    exact ⟨r, hr, hrw⟩
  set i₁ : Fin Tag.F4.rank := ⟨1, by decide⟩
  set i₂ : Fin Tag.F4.rank := ⟨2, by decide⟩
  have hM : orderOf (simple .F4 i₁ * simple .F4 i₂) = 4 := by
    have hc : Tag.F4.cartan i₁ i₂ * Tag.F4.cartan i₂ i₁ = 2 := by decide
    rw [orderOf_simple_mul_simple_eq, hc, TauCeti.coxeterOrder_two]
  obtain ⟨r, hr, hcr⟩ := hpre (simple .F4 i₁)
  obtain ⟨r', hr', hcr'⟩ := hpre (simple .F4 i₂)
  refine ⟨r, mem_ggAutomizer_iff.1 hr, r', mem_ggAutomizer_iff.1 hr',
    (F4AutRefl.ggIsReflection_congr_iff e r).1 ?_,
    (F4AutRefl.ggIsReflection_congr_iff e r').1 ?_, ?_⟩
  · rw [hcr]; exact isReflection_weylTorusAut_simple hp hp2 hpL i₁
  · rw [hcr']; exact isReflection_weylTorusAut_simple hp hp2 hpL i₂
  · have hw : orderOf (weylTorusAut L p (simple .F4 i₁ * simple .F4 i₂)) = 4 :=
      (orderOf_injective (weylTorusAut L p) (weylTorusAut_injective hp hp2 hpL) _).trans hM
    have hmul : MulAut.congr e (r * r') = weylTorusAut L p (simple .F4 i₁ * simple .F4 i₂) := by
      rw [map_mul, hcr, hcr']
      exact (map_mul (weylTorusAut L p) _ _).symm
    have h4 : orderOf (r * r') = 4 := by
      rw [← orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective (r * r')]
      exact (congrArg orderOf hmul).trans hw
    rw [h4]

end F4AutWeyl

end CFSG.StandardType
