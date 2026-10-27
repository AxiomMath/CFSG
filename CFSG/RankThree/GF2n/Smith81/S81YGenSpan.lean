module

public import CFSG.RankThree.GF2n.Smith81.S81YGenDef
public import CFSG.RankThree.GF2n.Smith81.S81RRoot
public import CFSG.RankThree.GF2n.Smith81.S81TBridge

public section

namespace CFSG.RankThree.GF2n.Smith81.RootGen

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.E3LBridge CFSG.RankThree.GF2n.Smith81.E3LCond
  CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.MinuscT
open scoped commutatorElement

variable {G : Type} [Group G]

theorem caseII_of_spanC [Finite G] {M Q Z B : Subgroup G} {K : Type}
    [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {V : Type}
    [AddCommGroup V] [Module K V] {ψ : M₀.E ≃ₗ[K] V} {φ : Lgen M (LB M Q B) →* (V ≃ₗ[K] V)}
    {Γ : Subgroup (V ≃ₗ[K] V)} {p₀ : V} {U₀ : Subgroup (V ≃ₗ[K] V)} {X : Subgroup G} {x : G}
    (d : EUniData M Q Z B M₀ ψ φ Γ p₀ U₀) (hD : GlobalModelData M Q Z γ M₀)
    (Hs : StrothHyp M Q Z) (hs : Sit M Q Z X x) (hxL : x ∈ Lgen M (LB M Q B))
    {t : V ≃ₗ[K] V} (hφ : φ ⟨x, hxL⟩ = t)
    (hspan : ∀ c : V, t c = c →
      c ∈ Submodule.span K {v : V | t v = v ∧ (v = 0 ∨ IsPurePt Γ p₀ v)})
    (hNF : ∀ w ∈ Z, w ≠ 1 → ¬ IsConj x (x * w)) : CaseII Q Z x := by
  have h12 := smith_1_12 hs
  obtain ⟨Tx⟩ := exists_xact hD hs.memM (hs.x_cent h12)
  refine E3LRoot.caseII_of_nf hD hs Tx ?_ hNF
  intro e he
  have hψe : t (ψ e) = ψ e := (MinuscT.mem_Cs_iff_E d hxL Tx hφ).mp he
  have h1 := hspan (ψ e) hψe
  have h2 := Submodule.mem_map_of_mem (f := (ψ.symm : V →ₗ[K] M₀.E)) h1
  rw [Submodule.map_span] at h2
  have h3 : e ∈ Submodule.span K ((ψ.symm : V →ₗ[K] M₀.E) ''
      {v : V | t v = v ∧ (v = 0 ∨ IsPurePt Γ p₀ v)}) := by
    simpa only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using h2
  refine Submodule.span_mono ?_ h3
  rintro _ ⟨v, ⟨hvt, hv⟩, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [MinuscT.mem_Cs_iff_E d hxL Tx hφ, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    exact hvt
  · by_cases hv0 : v = 0
    · left
      simp [hv0]
    · rcases hv with h0 | ⟨g, hg, c, -, hc⟩
      · exact absurd h0 hv0
      · exact MinuscT.rootPt_of_orbit d Hs hv0 ⟨g, hg, c, hc⟩

end CFSG.RankThree.GF2n.Smith81.RootGen
