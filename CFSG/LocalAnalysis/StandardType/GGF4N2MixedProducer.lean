module

public import CFSG.LocalAnalysis.StandardType.GGF4N2MixedMarkedL
public import CFSG.LocalAnalysis.StandardType.GGF4N2ActualH0
public import CFSG.LocalAnalysis.StandardType.GGCentralImageE6Quotient
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestGen
import CFSG.LocalAnalysis.StandardType.GGF4N2NoPSL216
import CFSG.LocalAnalysis.StandardType.GGF4N2MarkedSylow
import CFSG.LocalAnalysis.StandardType.GGNbrBalanceSchreier
import CFSG.RankThree.PartOne.TCB.SchreierFinal

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.ClassicalInvolution.WeakCT CFSG.LocalAnalysis.GLTheoremA


theorem ggF4N2_mixed_centralImage_of_marked {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K) (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K)
    (hF4 : GGWeylOfType 5 CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
    ∃ ψ₁ ψ₂ : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2) →* G, ∃ g ∈ L, ∃ v : G,
      ψ₁.ker ≤ Subgroup.center _ ∧ ψ₁.range = K ∧
      (ψ₁.comp (blockSL (GaloisField 2 2) 6 4 0 (by norm_num))).range = J ∧
      g ∈ Subgroup.normalizer (Bs : Set G) ∧ (∀ b ∈ Bs ⊓ L, g * b * g⁻¹ = b⁻¹) ∧ g * x * g⁻¹ = x ∧
      ψ₂.ker ≤ Subgroup.center _ ∧ ψ₂.range = K.map (MulAut.conj g).toMonoidHom ∧
      ψ₂.comp (blockSL (GaloisField 2 2) 6 4 0 (by norm_num)) =
        ψ₁.comp (blockSL (GaloisField 2 2) 6 4 0 (by norm_num)) ∧
      (∃ rho : Bs →* Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2),
        rho.range = N2KCoordinate.coordinateTorus ∧ rho.ker = (Subgroup.zpowers y).subgroupOf Bs ∧
        (∀ hx : x ∈ Bs, rho ⟨x, hx⟩ ∈ N2KCoordinate.coordT45) ∧ (∀ b : Bs, rho b ^ 5 = 1) ∧
        (∀ (b : Bs) (k : G), k ∈ K → ψ₁ (rho b) * k * (ψ₁ (rho b))⁻¹ = b * k * b⁻¹) ∧
        Nat.card rho.range = 5 ^ 3 ∧ (ψ₁.comp rho).range = Bs ⊓ K) ∧
      v ∈ D ⊓ K ∧ orderOf v = 5 ∧ D = Subgroup.zpowers y ⊔ Subgroup.zpowers v ∧
      g * y * g⁻¹ ∈ Subgroup.zpowers v ∧
      v ∈ (blockSL (GaloisField 2 2) 6 3 3 (by norm_num)).range.map ψ₁ ∧
      y ∈ (blockSL (GaloisField 2 2) 6 3 3 (by norm_num)).range.map ψ₂ ∧
      (((∀ a ∈ (blockSL (GaloisField 2 2) 6 3 3 (by norm_num)).range.map ψ₁,
            ∀ b ∈ (blockSL (GaloisField 2 2) 6 3 3 (by norm_num)).range.map ψ₂, a * b = b * a) →
          ∃ a ∈ ψ₁.range ⊔ (blockSL2 (GaloisField 2 2) 5 3).range.map ψ₂,
            a ∈ Subgroup.centralizer (K : Set G) ∧ orderOf a = 5 ∧
            ∀ c ∈ ggG0 5 B x L D J ⊓ Subgroup.centralizer (K : Set G),
              Subgroup.zpowers (c * a * c⁻¹) = Subgroup.zpowers y →
              Bs ≤ (ψ₁.range ⊔ (blockSL2 (GaloisField 2 2) 5 3).range.map ψ₂).map
                (MulAut.conj c).toMonoidHom →
              LabelOf ((ψ₁.range ⊔ (blockSL2 (GaloisField 2 2) 5 3).range.map ψ₂).map
                (MulAut.conj c).toMonoidHom) ⟨.E6, 0, 2⟩ →
              (K.map (MulAut.conj g).toMonoidHom ≤
                  (ψ₁.range ⊔ (blockSL2 (GaloisField 2 2) 5 3).range.map ψ₂).map
                    (MulAut.conj c).toMonoidHom ∨
                ∃ I₂ : Subgroup G, CFSG.Open.IsComponentOf I₂
                  ((ψ₁.range ⊔ (blockSL2 (GaloisField 2 2) 5 3).range.map ψ₂).map
                    (MulAut.conj c).toMonoidHom ⊓ Subgroup.centralizer ({g * y * g⁻¹} : Set G)) ∧
                CFSG.Blueprint.LieModel (↥I₂ ⧸ Subgroup.center ↥I₂) .PSL 6 2 2) ∧
              (K.map (MulAut.conj g).toMonoidHom ≤
                  (ψ₁.range ⊔ (blockSL2 (GaloisField 2 2) 5 3).range.map ψ₂).map
                    (MulAut.conj c).toMonoidHom →
                ∃ I : Subgroup G, CFSG.Open.IsComponentOf I
                    ((ψ₁.range ⊔ (blockSL2 (GaloisField 2 2) 5 3).range.map ψ₂).map
                      (MulAut.conj c).toMonoidHom ⊓ Subgroup.centralizer ({x} : Set G)) ∧
                  CFSG.Blueprint.LieModel (↥I ⧸ Subgroup.center ↥I) .POmegaMinus 4 2 2)) →
        GGCentralImage .E6 0 2 (ggG0 5 B x L D J)) := by
  have hLB : GGLBalanceInput :=
    ggLBalanceInput_of_catalogueSchreier CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds
  obtain ⟨ψ₁, ψ₂, g, hgL, h₁, hK₁, hJ₁, hgN, hinv, hxg, h₂, hK₂, hblock, hrho, hle, -, hfin⟩ :=
    ggF4N2_mixed_E6_reduction hLB hR hNbr hL hK hF4
  obtain ⟨v, hvDK, hvo, hDyv, hgy, hvM₁, hyM₂, -, -, -, -, -, -, -⟩ :=
    ggF4N2_mixed_slices_of_charts hR hNbr hL hK hF4 hgL hgN hinv hxg h₁ hK₁ hJ₁ h₂ hK₂ hblock
  refine ⟨ψ₁, ψ₂, g, hgL, v, h₁, hK₁, hJ₁, hgN, hinv, hxg, h₂, hK₂, hblock, hrho, hvDK, hvo, hDyv,
    hgy, hvM₁, hyM₂, fun hDict => ?_⟩
  have hM := ggF4N2_mixed_hM hR hNbr hL hK hF4 hgL hgN hinv hxg h₁ hK₁ hJ₁ h₂ hK₂ hblock
  obtain ⟨a, haX, haK, ha5, hI⟩ := hDict hM
  have hyg : y ∈ K.map (MulAut.conj g).toMonoidHom := by
    rw [← hK₂]
    exact Subgroup.map_le_range ψ₂ _ hyM₂
  have hKX₀ : K ≤ ψ₁.range ⊔ (blockSL2 (GaloisField 2 2) 5 3).range.map ψ₂ := by
    rw [← hK₁]
    exact le_sup_left
  obtain ⟨c, hc, hca, -, -, hKX, hBsX, -⟩ :=
    ggF4N2_mixed_exists_marking_conj hR hNbr hL hK hle hKX₀ hgL hyg haX haK ha5
  have hX₀ := ggCentralImage_E6_of_twoSL6Charts (le_refl 2) ψ₁ ψ₂ h₁ h₂ hblock.symm hM
  obtain ⟨hKg, hpair⟩ :=
    hI c hc hca hBsX (ggCentralImage_E6_four_labelOf (ggCentralImage_map_conj hX₀ c))
  obtain ⟨I, hIc, hIL⟩ := hpair (hKg.elim id fun ⟨_, hI₂c, hI₂L⟩ =>
    ggF4N2_mixed_Kg_le_of_component_lieModel hR hNbr hL hK hgN hI₂c hI₂L)
  exact hfin hM c hc.1 (ggF4N2_mixed_L_le_of_component_lieModel hR hNbr hL hIc hIL) hKX

end CFSG.StandardType

end
