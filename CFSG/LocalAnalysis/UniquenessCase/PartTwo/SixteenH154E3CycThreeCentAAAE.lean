module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenCore
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16h_e3_CycThreeCentAAAE_conjSubs_eq_range
    (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (h : Setting16 D V₀ V L) :
    conjSubs (Mbar D.M V₀ V hV) (wTil V₀ V hV L) =
      Set.range fun m : D.M => wTil V₀ V hV (conjSubgroup L (m : G)) := by
  ext X
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    obtain ⟨g, hgM, hgφ⟩ := (mem_barSub V₀ V hV D.M φ).1 hφ
    have hgs : (g : G)⁻¹ ∈ stabTil V₀ V := (stabTil V₀ V).inv_mem g.2
    refine ⟨⟨(g : G)⁻¹, D.M.inv_mem hgM⟩, ?_⟩
    change wTil V₀ V hV (conjSubgroup L ((g : G)⁻¹)) =
      (wTil V₀ V hV L).map φ.toMonoidHom
    rw [s15_Infra_wTil_conjSubgroup V₀ V L hV hgs]
    congr 1
    rw [show (⟨(g : G)⁻¹, hgs⟩ : stabTil V₀ V) =
        (⟨(g : G), g.2⟩ : stabTil V₀ V)⁻¹ from Subtype.ext rfl, map_inv, inv_inv, hgφ]
  · rintro ⟨m, rfl⟩
    have hm : (m : G) ∈ stabTil V₀ V :=
      le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
        h.hyp151.hyp125.pairFacts.le_normalizer₀ m.2
    refine ⟨(actTil V₀ V hV ⟨(m : G), hm⟩)⁻¹, ?_, ?_⟩
    · exact Subgroup.inv_mem _ (actTil_mem_barSub V₀ V hV m.2 hm)
    · change wTil V₀ V hV (conjSubgroup L (m : G)) =
        (wTil V₀ V hV L).map ((actTil V₀ V hV ⟨(m : G), hm⟩)⁻¹).toMonoidHom
      rw [s15_Infra_wTil_conjSubgroup V₀ V L hV hm]

theorem s16h_e3_cyc_conjSubs_ncard
    (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (h : Setting16 D V₀ V L)
    (hc : Conc4_136 D V₀ V hV L)
    {p : ℕ} (hp : p.Prime) (hLp : IsCyclicOrd ↥(lBar V₀ V hV L) p) :
    (conjSubs (Mbar D.M V₀ V hV) (wTil V₀ V hV L)).ncard = s15 D.M V₀ V hV L := by
  have hL : barSub V₀ V hV L ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥(lBar V₀ V hV L) = 1 := by
      change Nat.card ↥(barSub V₀ V hV L) = 1
      rw [hbot]
      simp
    exact hp.ne_one (hLp.2.symm.trans h1)
  rw [s16h_e3_CycThreeCentAAAE_conjSubs_eq_range D hV h]
  rw [s15_Core_ncard_range_eq
    (f := fun m : D.M => wTil V₀ V hV (conjSubgroup L (m : G)))
    (g := fun m : D.M => barSub V₀ V hV (conjSubgroup L (m : G)))
    (fun a b => s15_Core_wTil_conj_eq_iff h.hyp151 hL a.2 b.2)]
  exact (s15_Core_s15_eq_ncard_range h.hyp151).symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
