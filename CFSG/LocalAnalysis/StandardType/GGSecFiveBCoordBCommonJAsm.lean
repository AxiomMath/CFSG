module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRow
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJSmall

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace CommonJ

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

theorem ggCommonJ_core_of_rowData (hcfg : GGConfig p B Bs x L D J) (hB : B = Bs) {m : ℕ}
    (hm : 3 ≤ m) (eta : ↥Bs ≃* (Fin (m + 1) → Multiplicative (ZMod p))) (i0 : Fin (m + 1))
    (hA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock (m + 1) p i0)
    {lab : LargeEvenLabel} {R : Type} [Group R] (hRs : IsSimpleGroup R)
    (hRnc : ∃ a b : R, a * b ≠ b * a) {I : Set (MulAut R)} (hI : I ⊆ Set.range MulAut.conj)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hind : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    {SD SS : LargeEvenLabel → Prop} (hrow : GGSecFiveBNativeRow R p m SD SS)
    (hSD : ∀ labJ, SD labJ → GGSecFiveBCoordBJDenseLabel (m + 1) p lab labJ ∨
      ((lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D) ∧ m + 1 = 5 ∧ lab.n = 1 ∧
        labJ = ⟨.twA, 3, 1⟩ ∧ p = 3))
    (hSS : ∀ labJ, SS labJ → GGSecFiveBCoordBJSparseLabel (m + 1) p lab labJ)
    (hsp : (lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D) → m + 1 = 5 → lab.n = 1 → p = 3 →
      GGSecFiveBNativeSparseRow R p m) :
    (GGSecFiveBCoordDense eta i0 D ∧ LargeEvenMarking J
        (fun labJ _ _ _ _ _ => GGSecFiveBCoordBJDenseLabelCore L (m + 1) p lab labJ)) ∨
      (GGSecFiveBCoordSparse eta i0 D ∧ LargeEvenMarking J
        (fun labJ _ _ _ _ _ => GGSecFiveBCoordBJSparseLabel (m + 1) p lab labJ)) := by
  haveI : IsSimpleGroup R := hRs
  have hR : Subgroup.center R = ⊥ := by
    obtain ⟨a, b, hab⟩ := hRnc
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center R) with h | h
    · exact h
    · refine absurd ?_ hab
      have hb : b ∈ Subgroup.center R := by rw [h]; exact Subgroup.mem_top b
      exact Subgroup.mem_center_iff.mp hb a
  have hinn : ∀ b ∈ Bs, ∃ h : R, ∀ l l' : ↥L, (l' : G) = b * l * b⁻¹ →
      ggQuotHom θ l' = h * ggQuotHom θ l * h⁻¹ := by
    intro b hb
    obtain ⟨φ, hφI, hφ⟩ := hind b⁻¹ (Bs.inv_mem hb)
    obtain ⟨h, rfl⟩ := hI hφI
    refine ⟨h, ?_⟩
    intro l l' hl'
    have h' := hφ l l' (by simpa only [inv_inv] using hl')
    simpa only [MulAut.conj_apply, ggQuotHom_apply] using h'.symm
  obtain ⟨γ, hγ⟩ := exists_gammaHat θ hR hBsN hinn
  rcases ggCommonJ_marking_of_nativeRow hcfg hB hBsN hR hγ hm eta i0 hA
      (MulEquiv.refl R) hrow with ⟨hD, hM⟩ | ⟨hS, hM⟩
  · refine Or.inl ⟨hD, ?_⟩
    refine largeEvenMarking_mono ?_ hM
    intro labJ R' _ I F θJ hθJ
    obtain ⟨hSDlab, hSU⟩ := hθJ
    rcases hSD labJ hSDlab with h | ⟨htag, hm5, hn1, hlabJ, hp3⟩
    · exact Or.inl h
    · refine Or.inr ⟨htag, hm5, hn1, hlabJ, fun hZ => ?_⟩
      exact not_largeEvenSmall_J hcfg hB hBsN hR hγ hm eta i0 hA (MulEquiv.refl R)
        (hsp htag hm5 hn1 hp3) hp3 (hSU hlabJ hZ)
  · refine Or.inr ⟨hS, ?_⟩
    exact largeEvenMarking_mono (fun labJ _ _ _ _ _ hθJ => hSS labJ hθJ) hM

end CommonJ

end CFSG.StandardType

end
