module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIE6Prime
public import CFSG.LocalAnalysis.StandardType.GGE6TwoThreeComp
public import CFSG.LocalAnalysis.StandardType.GGCompListMarked
import CFSG.LocalAnalysis.StandardType.GGK0MarkedArithmetic
import CFSG.LocalAnalysis.StandardType.GGLieOddCover
import CFSG.LocalAnalysis.StandardType.GGReverseMarking
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldE6
import CFSG.LocalAnalysis.StandardType.GGSixFieldFiveTagsRank
import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab
import CFSG.LocalAnalysis.StandardType.GGTPNDefs

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType


theorem exists_ggU_cover_of_lieModel_two {X : Type} [Group X] [Finite X] {K : Subgroup X}
    (hperf : commutator ↥K = ⊤) (hodd : Odd (Nat.card (Subgroup.center ↥K)))
    {t : CFSG.Open.StatedLieTag} {m f : ℕ} (ht : S2MathFi1035Pos.GGPosTag t)
    (hM : LieModel (↥K ⧸ Subgroup.center ↥K) t m 2 f) :
    ∃ φ : (ggU t m f).K →* X, φ.range = K ∧ φ.ker ≤ Subgroup.center (ggU t m f).K := by
  obtain ⟨φ, hφ, hker⟩ :=
    LieOddCover.ggLieOddCover_holds.1 t m f ht hM.admissible K hperf hodd hM
  refine ⟨K.subtype.comp φ, ?_, ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hφ, Subgroup.map_top,
      Subgroup.range_subtype]
  · rw [MonoidHom.ker_comp_of_injective φ K.subtype K.subtype_injective]
    exact hker

theorem e6_two_compConfig_has_three_component_label
    {X : Type} [Group X] [Finite X] {n p : ℕ}
    {ψ : (ggU .E6 n 1).K →* X} {G₀ A B₁ D J L K : Subgroup X} {e : X}
    (hcfg : RCKRP.RCKCompConfig .E6 n 1 ψ p G₀ A B₁ D J L K e) :
    ∃ labK : LargeEvenLabel,
      labK ∈ [⟨.A, 5, 1⟩, ⟨.twD, 4, 1⟩, ⟨.A, 2, 2⟩] ∧
      GGHasLabel labK (↥K ⧸ Subgroup.center ↥K) := by
  have hp3 := prime_eq_three_of_e6_two_compConfig hcfg
  subst p
  have hdiag := RCKRP.rckRPConfigInnerDiag_holds X .E6 n 1 ψ 3 G₀ A B₁ D J L K e hcfg
  obtain ⟨hGG, -, -, -, hA, hBA, hDB, -, hAN, -, -, -, -, -, -, hfaith,
    -, -, -, -, -, -, -, -, -, heD, hene, hKcomp, -, -⟩ := hcfg
  have hn : n = 0 := hGG.1.1.2.2
  subst n
  have heA : e ∈ A := hBA (hDB heD)
  have heN : e ∈ Subgroup.normalizer (G₀ : Set X) := hAN heA
  let α : MulAut G₀ := G₀.normalizerMonoidHom ⟨e, heN⟩
  have hα3 : α ^ 3 = 1 := by
    have he3 : (⟨e, heN⟩ : Subgroup.normalizer (G₀ : Set X)) ^ 3 = 1 :=
      Subtype.ext (hA.2 e heA)
    change (G₀.normalizerMonoidHom ⟨e, heN⟩) ^ 3 = 1
    rw [← map_pow, he3, map_one]
  have hα1 : α ≠ 1 := by
    intro h1
    have heC : e ∈ Subgroup.centralizer (G₀ : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h := congrArg (fun β : MulAut G₀ => ((β ⟨x, hx⟩ : G₀) : X)) h1
      change e * x * e⁻¹ = x at h
      exact (mul_inv_eq_iff_eq_mul.mp h).symm
    have heInf : e ∈ A ⊓ Subgroup.centralizer (G₀ : Set X) := ⟨heA, heC⟩
    rw [hfaith, Subgroup.mem_bot] at heInf
    exact hene heInf
  have hfield : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero, pow_one]
  let ψE : ↥(CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup
      (GaloisField 2 1)) →* X := ψ
  have hrangeE : ψE.range = G₀ := hGG.2.1.1
  have hkerE : ψE.ker ≤ Subgroup.center ↥(CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup
      (GaloisField 2 1)) := hGG.2.1.2
  obtain ⟨g, hg, hecg⟩ := exists_mem_centralizer_E6_two hfield ψE hkerE (hdiag e heA)
  have hg0 : g ∈ G₀ := hrangeE ▸ hg
  have hecg0 : e * g ∈ Subgroup.centralizer (G₀ : Set X) := hrangeE ▸ hecg
  let g₀ : G₀ := ⟨g⁻¹, G₀.inv_mem hg0⟩
  have hαinner : α = MulAut.conj g₀ := by
    ext x
    change e * (x : X) * e⁻¹ = g⁻¹ * (x : X) * (g⁻¹)⁻¹
    rw [inv_inv]
    have hz : g⁻¹ * (x : X) * g ∈ G₀ :=
      G₀.mul_mem (G₀.mul_mem (G₀.inv_mem hg0) x.2) hg0
    have hc := Subgroup.mem_centralizer_iff.mp hecg0 _ hz
    calc
      e * (x : X) * e⁻¹ = (e * g) * (g⁻¹ * (x : X) * g) * (e * g)⁻¹ := by group
      _ = g⁻¹ * (x : X) * g := by
        rw [mul_inv_eq_iff_eq_mul]
        exact hc.symm
  obtain ⟨hperf, lab, hΛ, hraw⟩ :=
    largeEvenMarking_of_lieModel_centerQuot hGG.2.2.1 hGG.2.2.2
  have hfirst := largeEvenRawDatum_exists hraw
  obtain ⟨R, _, I, F, -, -, θ, htag, -, -, hdeg⟩ := hfirst
  have hlab : lab = ⟨.E6, 0, 1⟩ := by
    rcases lab with ⟨tag, rank, exponent⟩
    cases tag <;> simp_all [markTag, markDeg, LargeEvenInLambda2]
    all_goals split_ifs at htag
  subst lab
  have hrawI := ggRawInnFieldOn_E6 3 (by decide) (by decide) ⟨.E6, 0, 1⟩ hΛ rfl _ hraw
  have hmarked : LargeEvenRawDatum (⟨.E6, 0, 1⟩ : LargeEvenLabel) fun R _ I _ =>
      ∃ θ : ↥G₀ ⧸ Subgroup.center ↥G₀ ≃* R, ∃ β ∈ I,
        LargeEvenInduces θ (fun x y => y = α x) β := by
    apply largeEvenRawDatum_mono _ hrawI
    rintro R _ I F ⟨⟨hsimple, hnab, θ, -, -, -, -⟩, hI⟩
    let β : MulAut R := MulAut.conj (θ (QuotientGroup.mk g₀))
    refine ⟨θ, β, (hI hsimple hnab).2.2.1 _, ?_⟩
    intro x y hy
    subst y
    simp [β, hαinner]
  have hKle : K ≤ G₀ := hKcomp.1.trans inf_le_left
  obtain ⟨labK, hmem, hlabel⟩ := GGCompList.of_rawMarking E6TwoThree.ggE6TwoThreeComp_holds
    hperf hα3 hα1 hmarked (isComponentOf_subgroupOf_ggAutFixed heN hKle hKcomp)
  exact ⟨labK, hmem,
    ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKle) hlabel⟩

theorem e6_two_compConfig_exists_native_cover
    {X : Type} [Group X] [Finite X] {n p : ℕ}
    {ψ : (ggU .E6 n 1).K →* X} {G₀ A B₁ D J L K : Subgroup X} {e : X}
    (hcfg : RCKRP.RCKCompConfig .E6 n 1 ψ p G₀ A B₁ D J L K e) :
    (GGHasLabel ⟨.A, 5, 1⟩ (↥K ⧸ Subgroup.center ↥K) ∧
      ∃ φ : (ggU .PSL 6 1).K →* X,
        φ.range = K ∧ φ.ker ≤ Subgroup.center (ggU .PSL 6 1).K) ∨
    (GGHasLabel ⟨.twD, 4, 1⟩ (↥K ⧸ Subgroup.center ↥K) ∧
      ∃ φ : (ggU .POmegaMinus 4 1).K →* X,
        φ.range = K ∧ φ.ker ≤ Subgroup.center (ggU .POmegaMinus 4 1).K) ∨
    (GGHasLabel ⟨.A, 2, 2⟩ (↥K ⧸ Subgroup.center ↥K) ∧
      ∃ φ : (ggU .PSL 3 2).K →* X,
        φ.range = K ∧ φ.ker ≤ Subgroup.center (ggU .PSL 3 2).K) := by
  obtain ⟨labK, hmem, hlabel⟩ := e6_two_compConfig_has_three_component_label hcfg
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hKcomp, -, hOddK⟩ := hcfg
  have hnab : ∃ a b : ↥K ⧸ Subgroup.center ↥K, a * b ≠ b * a :=
    exists_mul_ne_mul_centerQuot_of_perfect hKcomp.2.2.1 hKcomp.2.2.2.toNontrivial
  have hcover {t : CFSG.Open.StatedLieTag} {m f : ℕ} (ht : S2MathFi1035Pos.GGPosTag t)
      (hM : LieModel (↥K ⧸ Subgroup.center ↥K) t m 2 f) :=
    exists_ggU_cover_of_lieModel_two hKcomp.2.2.1 hOddK ht hM
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl
  · have hM := GGK0MarkedArithmetic.markedModel_of_label (by simp [LargeEvenInLambda2]) hnab hlabel
    exact Or.inl ⟨hlabel, hcover (by simp [S2MathFi1035Pos.GGPosTag]) (by
      simpa [MarkedModel, markTag, markRank, markChar, markDeg] using hM)⟩
  · have hM := GGK0MarkedArithmetic.markedModel_of_label (by simp [LargeEvenInLambda2]) hnab hlabel
    exact Or.inr (Or.inl ⟨hlabel, hcover (by simp [S2MathFi1035Pos.GGPosTag]) (by
      simpa [MarkedModel, markTag, markRank, markChar, markDeg] using hM)⟩)
  · have hM := GGK0MarkedArithmetic.markedModel_of_label (by simp [LargeEvenInLambda2]) hnab hlabel
    exact Or.inr (Or.inr ⟨hlabel, hcover (by simp [S2MathFi1035Pos.GGPosTag]) (by
      simpa [MarkedModel, markTag, markRank, markChar, markDeg] using hM)⟩)

end CFSG.StandardType.RCKC1
