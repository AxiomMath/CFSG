module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatOm4mA.Holds
public import CFSG.LocalAnalysis.WeakClosure81.SevenEightCoreBar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeBasics
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem aBar_congr_subgroup {M V₀ V V' : Subgroup G} (h : V = V')
    (hV : IsElemAbelian 2 V) (hV' : IsElemAbelian 2 V') :
    aBar M V₀ V hV = aBar M V₀ V' hV' := by
  subst h
  rfl

theorem aBar_le_of_omegaMinus {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {A : Subgroup G} (hA : IsElemAbelian 2 A) {k : ℕ}
    (hOm : IsOmegaMinus ↥(barSub ⊥ A hA c.L0) 4 k)
    (hNat : NatOmegaMinus (barSub ⊥ A hA c.L0) ⊤ ⊥ 4 k) :
    aBar (c.L0 ⊔ D.T) ⊥ A hA ≤ k := by
  have hHX : barSub (⊥ : Subgroup G) A hA c.L0 ≤ barSub (⊥ : Subgroup G) A hA (c.L0 ⊔ D.T) :=
    barSub_mono ⊥ A hA le_sup_left
  have hXN : barSub (⊥ : Subgroup G) A hA (c.L0 ⊔ D.T) ≤
      Subgroup.normalizer (barSub (⊥ : Subgroup G) A hA c.L0 : Set (MulAut (Vtil ⊥ A hA))) :=
    CFSG.LocalAnalysis.WeakClosure81.barSub_le_normalizer_barSub (actTil (⊥ : Subgroup G) A hA)
      (sup_le Subgroup.le_normalizer c.hL0.1.1)
  exact kNatOm4mA_holds (Vtil ⊥ A hA) (barSub (⊥ : Subgroup G) A hA c.L0)
    (barSub (⊥ : Subgroup G) A hA (c.L0 ⊔ D.T)) k hOm hNat hHX hXN

theorem aBar_le_of_omegaMinus_of_barSub_eq {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {A : Subgroup G} (hA : IsElemAbelian 2 A) {k : ℕ}
    (hL : barSub (⊥ : Subgroup G) A hA c.L0 = barSub (⊥ : Subgroup G) A hA c.L)
    (hOm : IsOmegaMinus ↥(barSub ⊥ A hA c.L) 4 k)
    (hNat : NatOmegaMinus (barSub ⊥ A hA c.L) ⊤ ⊥ 4 k) :
    aBar (c.L0 ⊔ D.T) ⊥ A hA ≤ k :=
  aBar_le_of_omegaMinus c hA (by rw [hL]; exact hOm) (by rw [hL]; exact hNat)

private theorem conj_eq_of_actTil_eq {A : Subgroup G} (hA : IsElemAbelian 2 A)
    {g g' : G} (hg : g ∈ stabTil (⊥ : Subgroup G) A) (hg' : g' ∈ stabTil (⊥ : Subgroup G) A)
    (h : actTil (⊥ : Subgroup G) A hA ⟨g, hg⟩ = actTil (⊥ : Subgroup G) A hA ⟨g', hg'⟩)
    {a : G} (ha : a ∈ A) : g * a * g⁻¹ = g' * a * g'⁻¹ := by
  have h2 : actTil (⊥ : Subgroup G) A hA ⟨g, hg⟩ (mkTil ⊥ A hA (IntMod.mk hA ⟨a, ha⟩)) =
      actTil (⊥ : Subgroup G) A hA ⟨g', hg'⟩ (mkTil ⊥ A hA (IntMod.mk hA ⟨a, ha⟩)) := by
    rw [h]
  rw [actTil_mk, actTil_mk, mkTil_eq_iff, Subgroup.mem_bot] at h2
  rw [actStab_apply_val, actStab_apply_val] at h2
  exact mul_inv_eq_one.mp h2

private theorem conjClosure_eq_iSup (H S : Subgroup G) :
    conjClosure H S = ⨆ l ∈ H, S.map (MulAut.conj l).toMonoidHom := by
  refine le_antisymm (iSup₂_le fun K hK => ?_) (iSup₂_le fun l hl => ?_)
  · obtain ⟨l, hl, rfl⟩ := hK
    exact le_iSup₂_of_le l hl le_rfl
  · exact le_iSup₂_of_le _ ⟨l, hl, rfl⟩ le_rfl

private theorem map_conj_le_conjClosure {A S H H' : Subgroup G} (hA : IsElemAbelian 2 A)
    (hSA : S ≤ A) (hH : H ≤ Subgroup.normalizer (A : Set G))
    (hL : barSub (⊥ : Subgroup G) A hA H = barSub (⊥ : Subgroup G) A hA H')
    {l : G} (hl : l ∈ H) : S.map (MulAut.conj l).toMonoidHom ≤ conjClosure H' S := by
  have hst : l ∈ stabTil (⊥ : Subgroup G) A :=
    Subgroup.mem_inf.mpr ⟨hH hl, by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top l⟩
  have hmem : actTil (⊥ : Subgroup G) A hA ⟨l, hst⟩ ∈ barSub (⊥ : Subgroup G) A hA H :=
    actTil_mem_barSub ⊥ A hA hl hst
  rw [hL] at hmem
  obtain ⟨l', hl', hl'eq⟩ := (mem_barSub (⊥ : Subgroup G) A hA H' _).1 hmem
  have hconj : ∀ s ∈ S, l * s * l⁻¹ = (l' : G) * s * (l' : G)⁻¹ := fun s hs =>
    conj_eq_of_actTil_eq hA hst l'.2 hl'eq.symm (hSA hs)
  rintro _ ⟨s, hs, rfl⟩
  show l * s * l⁻¹ ∈ conjClosure H' S
  rw [hconj s hs]
  exact Subgroup.mem_iSup_of_mem (S.map (MulAut.conj (l' : G)).toMonoidHom)
    (Subgroup.mem_iSup_of_mem ⟨(l' : G), hl', rfl⟩ (Subgroup.mem_map_of_mem _ hs))

private theorem conjClosure_eq_of_barSub_eq {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) {A S : Subgroup G} (hA : IsElemAbelian 2 A)
    (hSA : S ≤ A) (hAL : c.L ≤ Subgroup.normalizer (A : Set G))
    (hAL0 : c.L0 ≤ Subgroup.normalizer (A : Set G))
    (hL : barSub (⊥ : Subgroup G) A hA c.L0 = barSub (⊥ : Subgroup G) A hA c.L) :
    conjClosure c.L0 S = conjClosure c.L S := by
  have key : ∀ (l : G), l ∈ c.L → S.map (MulAut.conj l).toMonoidHom ≤ conjClosure c.L0 S :=
    fun l hl => map_conj_le_conjClosure hA hSA hAL hL.symm hl
  have key' : ∀ (l : G), l ∈ c.L0 → S.map (MulAut.conj l).toMonoidHom ≤ conjClosure c.L S :=
    fun l hl => map_conj_le_conjClosure hA hSA hAL0 hL hl
  refine le_antisymm ?_ ?_
  · conv_lhs => rw [conjClosure_eq_iSup]
    exact iSup₂_le key'
  · conv_lhs => rw [conjClosure_eq_iSup]
    exact iSup₂_le key

theorem A_le_W23_1 {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch) {A : Subgroup G}
    (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
    (hT : D.T ≤ Subgroup.normalizer (A : Set G))
    (hAL : c.L ≤ Subgroup.normalizer (A : Set G))
    (hAL0 : c.L0 ≤ Subgroup.normalizer (A : Set G))
    (hirr : IrrOn c.L A)
    (hL : barSub (⊥ : Subgroup G) A hA c.L0 = barSub (⊥ : Subgroup G) A hA c.L) :
    A ≤ W23_1 c := by
  have hinf : A ⊓ D.Z ≠ ⊥ := Ctx23L.inf_Z_ne_bot c hAV hAne hT
  have hAle : conjClosure c.L (A ⊓ D.Z) ≤ A := by
    rw [conjClosure_eq_iSup]
    refine iSup₂_le fun l hl => ?_
    refine Subgroup.map_le_iff_le_comap.mpr fun s hs => ?_
    exact (Subgroup.mem_normalizer_iff.mp (hAL hl) s).1 (Subgroup.mem_inf.mp hs).1
  have hne : conjClosure c.L (A ⊓ D.Z) ≠ ⊥ := fun h =>
    hinf (le_bot_iff.mp (h ▸ TwelveTwentyThree.le_conjClosure c.L (A ⊓ D.Z)))
  have hNL : c.L ≤ Subgroup.normalizer (conjClosure c.L (A ⊓ D.Z) : Set G) :=
    TwelveTwentyThree.le_normalizer_conjClosure c.L (A ⊓ D.Z)
  have heq : conjClosure c.L (A ⊓ D.Z) = A := by
    rcases hirr _ hAle hNL with h | h
    · exact absurd h hne
    · exact h
  rw [← heq, ← conjClosure_eq_of_barSub_eq c hA inf_le_left hAL hAL0 hL]
  exact iSup₂_le fun K hK => by
    obtain ⟨l, hl, rfl⟩ := hK
    exact (Subgroup.map_mono (show A ⊓ D.Z ≤ D.Z from inf_le_right)).trans
      (le_iSup₂_of_le (f := fun K (_ : K ∈ conjSetOf c.L0 D.Z) => K) _
        ⟨l, hl, rfl⟩ le_rfl)

theorem mBar_V_le_of_omegaMinus {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h1A : S23_1A D Ch) (h1930 : H1930 D) (hVne : c.V ≠ ⊥)
    {hV : IsElemAbelian 2 c.V} {k : ℕ} {hW : IsElemAbelian 2 (W23_1 c)}
    (haW : aBar (c.L0 ⊔ D.T) ⊥ (W23_1 c) hW ≤ k) :
    mBar c.N ⊥ c.V hV ≤ k + 1 := by
  have hZleV : D.Z ≤ c.V := uc22p22v_le_conjClosure c.N D.Z
  have heq : c.V = conjClosure c.N (c.V ⊓ D.Z) := by
    rw [inf_eq_right.mpr hZleV]
    rfl
  obtain ⟨hW', h1, -⟩ := h1A h1930 c c.V hV le_rfl heq hVne
  have hWe : conjClosure c.L0 (c.V ⊓ D.Z) = W23_1 c := by
    rw [inf_eq_right.mpr hZleV]
    rfl
  have hle : aBar (c.L0 ⊔ D.T) ⊥ (conjClosure c.L0 (c.V ⊓ D.Z)) hW' ≤ k := by
    rw [aBar_congr_subgroup hWe hW' hW]
    exact haW
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
