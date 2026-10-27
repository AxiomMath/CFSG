module

public import CFSG.LocalAnalysis.StandardType.FF81.PropTwoDict
public import CFSG.RankThree.PartTwo.Sec21.FF81P51Mon
import CFSG.RankThree.PartTwo.Sec21.FF81P51Pat

@[expose] public section

namespace CFSG.StandardType.FF81

open Matrix
open CFSG.RankThree.PartTwo.Sec21.FF81.P51 (V Mat GL4 e Sig01 GM cfgOf mA mem_GM mon_mem_GM
  e_mem_Om coe_mem_GM mulVec_mem_Om mulVec_inj sig01_of_mA mem_Om_of_mA)
open CFSG.StandardType.FrameRoute.FS81 (spMat spMat_mulVec)

private theorem spMat_mulVec_e (σ : Equiv.Perm (Fin 4)) (ε : Fin 4 → ZMod 3) (i : Fin 4) :
    spMat σ ε *ᵥ e i = ε i • e (σ i) := by
  rw [spMat_mulVec]
  ext j
  simp only [e, Pi.smul_apply, smul_eq_mul]
  by_cases hj : j = σ i
  · subst hj; simp
  · have : σ.symm j ≠ i := fun h => hj (by rw [← h]; simp)
    simp [hj, this]

theorem containsMonomial_of_sig01 {G : Type} [Group G]
    {K : Subgroup G} {b : G} {z : Fin 3 → K} {Γ : Subgroup GL4} {cv : G → V}
    (hM : BCoordModel b z Γ cv) (hs : Sig01 ∈ GM Γ) : ContainsMonomial b z := by
  intro σ ε hε
  obtain ⟨g, hg, hgA⟩ := mem_GM.1 (mon_mem_GM hM.hyp hs σ ε hε)
  obtain ⟨n, hn, hcol⟩ := hM.to_nor g hg
  refine ⟨n, hn, fun i => ?_⟩
  have hnx : n * xs b z i * n⁻¹ ∈ GGFF.Bt b z :=
    (Subgroup.mem_normalizer_iff.mp hn _).mp (xs_mem_Bt b z i)
  refine hM.inj _ hnx _ ((GGFF.Bt b z).pow_mem (xs_mem_Bt b z _) _) ?_
  rw [← hcol i, hgA, spMat_mulVec_e, hM.cv_xs_pow, ZMod.natCast_zmod_val]

theorem isMonomial_of_mA {G : Type} [Group G]
    {K : Subgroup G} {b : G} {z : Fin 3 → K} {Γ : Subgroup GL4} {cv : G → V}
    (hM : BCoordModel b z Γ cv) (hA : (cfgOf Γ).1 = mA) : IsMonomial b z := by
  refine ⟨containsMonomial_of_sig01 hM (sig01_of_mA hM.hyp hA), fun n hn => ?_⟩
  obtain ⟨g, hg, hcol⟩ := hM.of_nor n hn
  have hcol' : ∀ i, ∃ j, ∃ c : ZMod 3, c ≠ 0 ∧ (g : Mat) *ᵥ e i = c • e j := fun i =>
    (mem_Om_of_mA hM.hyp hA _).1 (mulVec_mem_Om (coe_mem_GM hg) (e_mem_Om hM.hyp hA i))
  choose j c hc hgj using hcol'
  have hinj : Function.Injective j := by
    intro i i' hii'
    by_contra hne
    have h1 : (g : Mat) *ᵥ (c i' • e i) = (g : Mat) *ᵥ (c i • e i') := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul, hgj i, hgj i', hii', smul_comm]
    have h2 := congrFun (mulVec_inj g h1) i
    simp [e, hne] at h2
    exact hc i' h2
  refine ⟨Equiv.ofBijective j (Finite.injective_iff_bijective.mp hinj), c, hc, fun i => ?_⟩
  have hnx : n * xs b z i * n⁻¹ ∈ GGFF.Bt b z :=
    (Subgroup.mem_normalizer_iff.mp hn _).mp (xs_mem_Bt b z i)
  refine hM.inj _ hnx _ ((GGFF.Bt b z).pow_mem (xs_mem_Bt b z _) _) ?_
  rw [← hcol i, hgj i, Equiv.ofBijective_apply, hM.cv_xs_pow, ZMod.natCast_zmod_val]

end CFSG.StandardType.FF81

end
