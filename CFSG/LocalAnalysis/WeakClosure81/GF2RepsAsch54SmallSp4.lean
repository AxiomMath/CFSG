module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SmallNarrow
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SmallSp4Irr

import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SmallSp4Cover
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SmallSp4Red
import CFSG.LocalAnalysis.WeakClosure81.W18ASNineCF
import CFSG.Quasithin.Vol2.Ch8Sec2L829LN1
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CalL0

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Quasithin
open CFSG.Open (StatedSp StatedProj StatedScalars)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)


theorem sectionalTwoRankLE_of_isCompositionFactor_of_lt_sp4 {r : ℕ} [Fact r.Prime]
    (hr2 : r ≠ 2) {G : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod r))} (hGS : G ≤ StatedSp 2 (ZMod r))
    (hGt : G ≠ StatedSp 2 (ZMod r)) {L : Type} [Group L] (hL : E1.IsCompositionFactor G L)
    (hnab : ∃ a b : L, a * b ≠ b * a) : CFSG.GH74.SectionalTwoRankLE L 2 := by
  obtain ⟨H, ψ, hHG, hψ, hperf, hnil, hsimp⟩ := exists_perfect_cover_of_isCompositionFactor hL hnab
  have hHS : H ≤ StatedSp 2 (ZMod r) := hHG.trans hGS
  have hHt : H ≠ StatedSp 2 (ZMod r) := fun h => hGt (le_antisymm hGS (h ▸ hHG))
  let eψ : H ⧸ ψ.ker ≃* L := QuotientGroup.quotientKerEquivOfSurjective ψ hψ
  by_cases hirr : CFSG.RankThree.SubgroupLists.IsIrreducibleOn H
  · have hs : IsSimpleGroup (H ⧸ ψ.ker) := eψ.isSimpleGroup
    exact (sectionalTwoRankLE_quotient_of_irreducible hr2 hHS hHt hirr ψ.ker inferInstance
      hs).of_mulEquiv eψ
  · let ψ' : (⊤ : Subgroup H) →* L :=
      ψ.comp (Subgroup.topEquiv : (⊤ : Subgroup H) ≃* H).toMonoidHom
    have hψ' : Function.Surjective ψ' := fun l => by
      obtain ⟨h, rfl⟩ := hψ l
      exact ⟨Subgroup.topEquiv.symm h, by simp [ψ']⟩
    have hLH : E1.IsCompositionFactor H L :=
      CFSG.Quasithin.H13.L829N.isCompositionFactor_of_subnormal_surjection
        Subgroup.IsSubnormal.top hsimp ψ' hψ'
    exact sectionalTwoRankLE_of_isCompositionFactor_of_not_irreducible hr2 hHS hirr hLH hnab


theorem k_Asch511SylowOvergroupsPSp4_holds : K_Asch511SylowOvergroupsPSp4 := by
  intro X _ _ r hr hr2 hX _ Y _ hY ⟨L, _, hcf, hL0⟩
  have : Fact r.Prime := ⟨hr⟩
  have : Finite L := isCompositionFactor_finite hcf
  obtain ⟨hnab, hnsle⟩ := isCalL0_nonabelian_not_sectionalTwoRankLE L hL0
  refine hnsle ?_
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX.statedClassicalModel (by decide)
  let : Fintype K := Fintype.ofFinite K
  have hKr : Fintype.card K = r := by rw [← Nat.card_eq_fintype_card, hK, pow_one]
  let σ : K ≃+* ZMod r := (ZMod.ringEquivOfPrime K hr hKr).symm
  set S : Subgroup (GL (Fin 2 ⊕ Fin 2) K) := StatedSp 2 K with hS
  let π : S →* StatedProj S := QuotientGroup.mk' _
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  set Y' : Subgroup (StatedProj S) := Y.map e.toMonoidHom with hY'
  have hY't : Y' ≠ ⊤ := fun h => hY.ne (by
    rw [← Subgroup.comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective Y]
    change Y'.comap e.toMonoidHom = ⊤
    rw [h, Subgroup.comap_top])
  have hcf' : E1.IsCompositionFactor Y' L :=
    (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr
      (Y.equivMapOfInjective e.toMonoidHom e.injective)).1 hcf
  set Yh : Subgroup S := Y'.comap π with hYh
  have hYht : Yh ≠ ⊤ := fun h => hY't (by
    rw [← Subgroup.map_comap_eq_self_of_surjective hπ Y', ← hYh, h,
      ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hπ])
  have hcfh : E1.IsCompositionFactor Yh L :=
    CFSG.Quasithin.H13.L829N.isCompositionFactor_of_surjective (π.subgroupComap Y')
      (MonoidHom.subgroupComap_surjective π Y' hπ) hcf'
  set GK : Subgroup (GL (Fin 2 ⊕ Fin 2) K) := Yh.map S.subtype with hGK
  have hGKS : GK ≤ S := Subgroup.map_subtype_le Yh
  have hcfK : E1.IsCompositionFactor GK L :=
    (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr
      (Yh.equivMapOfInjective S.subtype S.subtype_injective)).1 hcfh
  have hcardK : Nat.card GK < Nat.card S := by
    rw [hGK, Subgroup.card_map_of_injective S.subtype_injective]
    refine lt_of_le_of_ne (Subgroup.card_le_card_group Yh) fun h => hYht ?_
    exact Subgroup.card_eq_iff_eq_top Yh |>.mp h
  let Ψ : GL (Fin 2 ⊕ Fin 2) K →* GL (Fin 2 ⊕ Fin 2) (ZMod r) :=
    Matrix.GeneralLinearGroup.map (σ : K →+* ZMod r)
  have hΨ : Function.Injective Ψ := by
    intro a b h
    ext i j
    have h' := congrArg (fun g : GL (Fin 2 ⊕ Fin 2) (ZMod r) => g i j) h
    simp only [Ψ, Matrix.GeneralLinearGroup.map_apply] at h'
    exact σ.injective h'
  have hΨS : ∀ g ∈ S, Ψ g ∈ StatedSp 2 (ZMod r) := fun g hg =>
    CFSG.Open.StatedAPI.map_mem_statedSp (σ : K →+* ZMod r) hg
  set G : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod r)) := GK.map Ψ with hG
  have hGS : G ≤ StatedSp 2 (ZMod r) := by
    rintro _ ⟨g, hg, rfl⟩
    exact hΨS g (hGKS hg)
  have hGt : G ≠ StatedSp 2 (ZMod r) := by
    intro h
    have h1 : Nat.card S ≤ Nat.card (StatedSp 2 (ZMod r)) := by
      rw [← Subgroup.card_map_of_injective hΨ (K := S)]
      exact Subgroup.card_le_of_le fun _ ⟨g, hg, hgx⟩ => hgx ▸ hΨS g hg
    have h2 : Nat.card G = Nat.card GK := Subgroup.card_map_of_injective hΨ
    rw [h] at h2
    omega
  have hcfG : E1.IsCompositionFactor G L :=
    (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr
      (GK.equivMapOfInjective Ψ hΨ)).1 hcfK
  exact sectionalTwoRankLE_of_isCompositionFactor_of_lt_sp4 hr2 hGS hGt hcfG hnab

end CFSG.LocalAnalysis.WeakClosure81

end
