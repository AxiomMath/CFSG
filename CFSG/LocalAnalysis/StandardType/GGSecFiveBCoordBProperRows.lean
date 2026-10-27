module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCornerDenseDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveDataSpSpTwo
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCornerCharts
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCornerRowOneLevi

public section

namespace CFSG.StandardType

open CFSG.Open

variable {G : Type} [Group G]

section Inputs


theorem GGSecFiveRouteCfg.ggSecFiveData_of_corner [Finite G] (hX : GGResXDichotomyInput)
    (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput) (hTPn : GGNbrTablePNbrInputNarrow)
    (hA8 : GGForkA8NotReflInput) (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hFC : GGResNbrFixCentralizesInput) (hAbs : GGSecFiveBCoordBCornerAbsorbInput)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) (hne : B ≠ Bs) {s : ℕ} (hs : 2 ≤ s)
    {eta : ↥Bs ≃* (Fin (s + 3) → Multiplicative (ZMod 3))}
    (hEta : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull (s + 3) 3)
    (hNbr : ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K →
      ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hG0 : ggG0 3 B x L D J = L ⊔ ⨆ K ∈ 𝒦, K) {π : Fin (s + 3) ≃ Fin (s + 3)}
    {κ : StatedSp (s + 2) (GaloisField 2 1) →* G}
    {ζ : Multiplicative (ZMod 3) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1)}
    (hκ : GGSecFiveBPermSpPlaneFrame Bs L eta π κ ζ)
    (hb : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock (s + 3) 3 (π 0))
    (hdense : ∀ (g : G) (hg : g ∈ Subgroup.normalizer (Bs : Set G)), g ∈ ggG0 3 B x L D J →
      MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut (Equiv.swap (π 0) (π 1)) →
      ∀ K : Subgroup G, GGSecFiveBCoordBDenseNbr 3 Bs 𝒦 (s + 3) eta K →
        K ≤ L ⊔ L.map (MulAut.conj g).toMonoidHom) :
    GGSecFiveData 3 B x L D J := by
  have h01 : π 0 ≠ π 1 := π.injective.ne (Fin.ne_of_val_ne (by simp))
  have h03 : π 0 ≠ π 3 := π.injective.ne (Fin.ne_of_val_ne (by
    rw [Fin.val_zero]
    show 0 ≠ 3 % (s + 1 + 2)
    rw [Nat.mod_eq_of_lt (by omega)]
    omega))
  obtain ⟨g, hgG, hg, hgη⟩ := exists_swap_lift_of_bSignedFull hEta h01
  obtain ⟨w, -, hw, hwη⟩ := exists_swap_lift_of_bSignedFull hEta h03
  have hgG' : g ∈ ggG0 3 B x L D J := by
    rw [hG0]
    exact hgG
  have habs : ∀ K ∈ 𝒦, K ≤ L ⊔ L.map (MulAut.conj g).toMonoidHom := by
    intro K hK
    rcases hAbs hX hTCJ hRig hTPn hA8 hraw hiso hFC G B Bs x L D J 𝒦 hR hne (s + 3)
      (s + 1) (by omega) eta hEta hNbr π κ ζ hκ hb g hg hgη K hK with h | h
    · exact h
    · exact hdense g hg hgG' hgη K h
  exact hR.ggSecFiveData_of_corner_charts hs hκ hg hgη hw hwη hG0 hgG' habs

theorem ggSecFiveBCoordBProperRowsInput_of_leaves (hMp : GGInnerDiagMpInput)
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput) (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) (hFC : GGResNbrFixCentralizesInput)
    (hLJ : GGSecFivePermNbrLabelOfJInput) (hU62 : GGU62OuterDiagInput)
    (hFrame : GGSecFiveBCoordBCornerPlaneFrameInput) (hAbs : GGSecFiveBCoordBCornerAbsorbInput)
    (hDense : GGSecFiveBCoordBCornerDenseInput) : GGSecFiveBCoordBProperRowsInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 n e hpres h4 eta i0 hEta hb hlab hne hBeq hrows hNbr
    hG0
  obtain ⟨-, -, -, -, -, -, -, -, ⟨-, hn5, -, -, hp⟩, -⟩ := largeEvenMarking_exists' hlab
  subst hp
  obtain ⟨s, rfl⟩ : ∃ s, n = s + 3 := ⟨n - 3, by omega⟩
  have hM' : GGInnerDiagOnLabel (fun _ lab => (lab.tag = .B ∨ lab.tag = .C) ∧
      lab.rank = s + 2 ∧ lab.n = 1) 3 Bs L :=
    hlab.mono_label fun _ hl => by
      obtain ⟨ht, hr, hn1⟩ := GGSecFiveBCoordBLabel.corner_tag_rank hl
      exact ⟨ht, by omega, hn1⟩
  obtain ⟨π, hπ0, κ, ζ, hκ⟩ := hFrame hMp G B Bs x L D J 𝒦 hR s (by omega) eta i0 hb hM'
  subst hπ0
  exact GGSecFiveRouteCfg.ggSecFiveData_of_corner hX hTCJ hRig hTPn hA8 hraw hiso hFC hAbs
    hR hne (by omega) hEta hNbr hG0 hκ hb (fun g hg hgG hgη K hK =>
      hDense hMp hX hTCJ hRig hTPn hA8 hraw hiso hFC hLJ hU62 G 3 B Bs x L D J 𝒦 hR hT1 (s + 3)
        e hpres h4 eta (π 0) hEta hb hlab hne hBeq hrows hNbr hG0 (s + 1) π κ ζ rfl hκ g hg hgG
        hgη K hK)

end Inputs

end CFSG.StandardType

end
