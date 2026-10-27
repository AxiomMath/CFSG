module

public import CFSG.LocalAnalysis.StandardType.GGHLAutomizer
public import CFSG.LocalAnalysis.StandardType.GGTBTorDatum

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggAutomizerLift_of_torData {G : Type} [Group G] [Finite G] {p m N : ℕ} [Fact p.Prime]
    {Bs L : Subgroup G} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs)
    (hSdef : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hom : Odd m) (hpm : p ∣ m)
    (hTor : GGTorusTorData m N C M ↥L (ggGamma L hN).range) : GGAutomizerLift L Bs hN := by
  obtain ⟨w, hw⟩ := hTor
  obtain ⟨hnk, -, -, -, -, -, -, -⟩ := ggTD_core hom hpm hBs hSdef hN w hw
  let φ₁ : Fin N → MulAut ↥Bs := fun k => ggTDρB L Bs (ggTDnH w hnk k)
  let ψ₁ : Fin N → MulAut ↥(ggGamma L hN).range :=
    fun k => ggConjAut (ggGamma L hN).range (w.hn k)
  have hcompat₁ : ∀ i (b : ↥Bs), ψ₁ i ((ggGamma L hN).rangeRestrict b) =
      (ggGamma L hN).rangeRestrict (φ₁ i b) := by
    intro i b
    have hgb : (w.n i : G) * b * (w.n i : G)⁻¹ ∈ Bs :=
      (Subgroup.mem_normalizer_iff.mp (hnk i) b).mp b.2
    have hconj : MulAut.conj (w.n i) =
        L.normalizerMonoidHom ⟨(w.n i : G), Subgroup.le_normalizer (w.n i).2⟩ := by
      ext l
      rfl
    apply Subtype.ext
    rw [show ψ₁ i = ggConjAut (ggGamma L hN).range (w.hn i) from rfl, ggConjAut_apply,
      MonoidHom.coe_rangeRestrict, MonoidHom.coe_rangeRestrict, hconj]
    rw [show φ₁ i b = (⟨(w.n i : G) * b * (w.n i : G)⁻¹, hgb⟩ : ↥Bs) from
      Subtype.ext (ggTDρB_apply (X := L) (Bs := Bs) (ggTDnH w hnk i) b)]
    exact ggGamma_conj_normalizer L hN
      ⟨(w.n i : G), Subgroup.le_normalizer (w.n i).2⟩ b hgb
  have hA₁ : ggAutomizer (MulAut.conj : L →* MulAut L).range (ggGamma L hN).range =
      Subgroup.closure (Set.range ψ₁) := by
    simpa only [ψ₁] using hw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hgen₁ : ggAutomizer L Bs = Subgroup.closure (Set.range φ₁) :=
    ggTD_closure hN hw hp2 hBs hnk
  exact ggAutomizerLift_of_system hN φ₁ ψ₁ hcompat₁ hA₁ hgen₁

end CFSG.StandardType

end
