module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4CBA3AAAA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Cfg
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_sl4_cba3_E9_le_two_components
    {D : Data G} {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 2)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L) :
    ∃ E : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)),
      E ≤ lBar ⊥ V h.hyp151.isElemAbelian L ⊔
        barSub ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x) ∧
      IsElemAbelian 3 E ∧ 9 ≤ Nat.card ↥E := by
  have hV := h.hyp151.isElemAbelian
  set lB : Subgroup (MulAut (Vtil ⊥ V hV)) := lBar ⊥ V hV L with hlB
  set lBx : Subgroup (MulAut (Vtil ⊥ V hV)) := barSub ⊥ V hV (conjSubgroup L x) with hlBx
  have hxstab : x ∈ stabTil ⊥ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
      h.hyp151.hyp125.pairFacts.le_normalizer₀ hxM
  have hlBx_eq : lBx = lB.map (MulAut.conj (actTil ⊥ V hV ⟨x, hxstab⟩)⁻¹).toMonoidHom := by
    rw [hlBx, hlB]
    exact s15_Infra_barSub_conjSubgroup ⊥ V hV hxstab L
  have hB : IsSLn ↥lBx 2 2 := by
    obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hrow.1
    refine ⟨K, hKf, hKfin, hKcard, ⟨?_⟩⟩
    have hf : Function.Injective
        (MulAut.conj (actTil ⊥ V hV ⟨x, hxstab⟩)⁻¹).toMonoidHom :=
      (MulAut.conj _).injective
    have hiso : ↥lB ≃* ↥lBx :=
      hlBx_eq.symm ▸ Subgroup.equivMapOfInjective lB _ hf
    exact hiso.symm.trans e
  have hcomm : ∀ a ∈ lB, ∀ b ∈ lBx, a * b = b * a := by
    intro a ha b hb
    have hc := (h.hyp151.commute x hxM hxn).1
    have hle : lB ≤ Subgroup.centralizer (lBx : Set (MulAut (Vtil ⊥ V hV))) := by
      simpa only [hlB, hlBx, lBar] using
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
    exact (Subgroup.mem_centralizer_iff.mp (hle ha) b hb).symm
  obtain ⟨E, hEsup, hEab, hEcard⟩ :=
    s16h_e9_of_commuting_isSLn_two (A := lB) (B := lBx) hrow.1 hB hcomm
  exact ⟨E, hEsup, hEab, hEcard⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
