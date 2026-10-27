module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Assembly
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenTwenty

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def K_Omega6Minus_sumOfTwo_aParam : Prop :=
  ∀ {W : Type} [CommGroup W] [Finite W] (X N : Subgroup (MulAut W)) (n : ℕ),
    SumOfNat (fun H U Z => NatOmegaMinus H U Z 6 n) X ⊤ ⊥ 2 →
      N ≤ Subgroup.normalizer (X : Set (MulAut W)) → E3.aParam N ≤ 2 * n

theorem Mbar_le_normalizer_barSub_conjClosure {D : Data G} {V₀ V : Subgroup G} {p : ℕ}
    {L : Subgroup G} (h : Hyp18 D V₀ V p L) :
    Mbar D.M V₀ V h.hyp125.isElemAbelian ≤
      Subgroup.normalizer (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L) :
        Set (MulAut (Vtil V₀ V h.hyp125.isElemAbelian))) := by
  have hV : IsElemAbelian 2 V := h.hyp125.isElemAbelian
  intro φ hφ
  obtain ⟨g, hg, rfl⟩ := (mem_barSub V₀ V hV D.M φ).1 hφ
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hgN : (g : G) ∈ Subgroup.normalizer (UC22.conjClosure D.M L : Set G) :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThree.le_normalizer_conjClosure
      D.M L hg
  have hXmap : (UC22.conjClosure D.M L).map (MulAut.conj (g : G)).toMonoidHom =
      UC22.conjClosure D.M L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 hgN
  have h := CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16c7_barSub_map_conj V₀ V hV g.2
    (UC22.conjClosure D.M L)
  rw [hXmap] at h
  exact h.symm

section Certified


theorem nOf_eq_of_isOmegaMinus_barSub {D : Data G} {V₀ V : Subgroup G} {p : ℕ}
    {L : Subgroup G} (h : Hyp18 D V₀ V p L) {f : ℕ}
    (hO : IsOmegaMinus ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) 6 f) :
    S17.nOf L = f := by
  have hV : IsElemAbelian 2 V := h.hyp125.isElemAbelian
  have hU : IsU4 ↥(barSub V₀ V hV (UC22.conjClosure D.M L)) f := isU4_of_isOmegaMinus hO
  have hs : IsSimpleGroup ↥(barSub V₀ V hV (UC22.conjClosure D.M L)) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU
  obtain ⟨hXL, ⟨e⟩⟩ := conjClosure_eq_and_bar2_equiv_of_hyp18 h hs
  rw [hXL] at hU
  exact S17.nOf_eq_of_isU4 (CFSG.Blueprint.LieModel.of_mulEquiv e.symm hU)

theorem gap_18_20_aBar (hK : K_Omega6Minus_sumOfTwo_aParam) {D : Data G} {V₀ V : Subgroup G}
    {p : ℕ} {L : Subgroup G} (h : Hyp18 D V₀ V p L) :
    Gap_18_20_aBar D V₀ V p L h := by
  intro s hs hs2
  have hV : IsElemAbelian 2 V := h.hyp125.isElemAbelian
  obtain ⟨-, -, f, hO, hSum⟩ := hs
  have hSum2 : SumOfNat (fun H U Z => NatOmegaMinus H U Z 6 f)
      (barSub V₀ V hV (UC22.conjClosure D.M L)) ⊤ ⊥ 2 := hs2 ▸ hSum
  have hN := Mbar_le_normalizer_barSub_conjClosure h
  have hle : E3.aParam (Mbar D.M V₀ V hV) ≤ 2 * f :=
    hK (barSub V₀ V hV (UC22.conjClosure D.M L)) (Mbar D.M V₀ V hV) f hSum2 hN
  have hf : S17.nOf L = f := nOf_eq_of_isOmegaMinus_barSub h hO
  rw [hf]
  exact hle

theorem eighteen_twenty_of_K (hK : K_Omega6Minus_sumOfTwo_aParam) (D : Data G)
    (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G) (h : Hyp18 D V₀ V p L)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h126 : R126 D) (h66 : UC6.R6_6 D)
    (h127 : R127 D) (h1114 : R1114 D) (h111 : W3Thm111 G) (h183 : W3Thm183 G)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (h16 : R18_16_2At D V₀ V p L h) (h17 : R18_17_2At D V₀ V p L h)
    (h18 : R18_18bAt D V₀ V p L h) (h1742 : S17.R17_42 D) :
    R18_20At D V₀ V p L h :=
  eighteen_twenty D V₀ V p L h hx h61 h126 h66 h127 h1114 h111 h183 h1669 h16 h17 h18
    (gap_18_20_aBar hK h)
    (fun f hO => ⟨(r18_fieldOmega D h1742 V₀ V p L h f hO).1,
      (r18_fieldOmega D h1742 V₀ V p L h f hO).2.1⟩)

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
