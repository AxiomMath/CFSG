module

public import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619Contracts
public import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
public import CFSG.RankThree.PartTwo.Sec4.RonanK423G2
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonTriCentHolds
import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619ClassicalGlue
import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619CoverDescentHolds
import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherExcFixG2
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census423Three.LocalGen

public section

namespace S2MathAs3_1619Final
open CFSG CFSG.Assembly CFSG.StandardType CFSG.Open
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement Pointwise




theorem g2_inner_on_component {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) {z : adjointGroup .G2 K}
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) {C : Subgroup (adjointGroup .G2 K)}
    (hC : CFSG.Assembly.IsComponentOf C
      (Subgroup.centralizer ({z} : Set (adjointGroup .G2 K))))
    {x : adjointGroup .G2 K} (hx : x ∈ Subgroup.centralizer ({z} : Set (adjointGroup .G2 K))) :
    ∃ s ∈ C, ∀ c ∈ C, x * c * x⁻¹ = s * c * s⁻¹ := by
  obtain ⟨hq, _, A, hA, hAR, hH⟩ :=
    CFSG.RankThree.PartTwo.Sec4.RonanK423.G2.layerData_of_cube hn hK hz3 hz1
  let H : Subgroup (adjointGroup .G2 K) := Subgroup.centralizer ({z} : Set (adjointGroup .G2 K))
  let R : Subgroup (adjointGroup .G2 K) := ⁅H, H⁆
  have hRC : R ≤ H := Subgroup.commutator_le_self H
  have hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b * a⁻¹ * b⁻¹ ∈ R := by
    intro a ha b hb
    simpa only [commutatorElement_def] using Subgroup.commutator_mem_commutator ha hb
  have hCR : C = R := CFSG.LocalAnalysis.GLTheoremA.tcent_component_eq hC hRC hcomm hq
  have hnorm : R ≤ Subgroup.normalizer (A : Set (adjointGroup .G2 K)) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    exact fun a ha => hAR a ha r hr
  have hprod : x ∈ (R : Set (adjointGroup .G2 K)) * (A : Set (adjointGroup .G2 K)) := by
    have hxSup : x ∈ R ⊔ A := hH hx
    change x ∈ ((R ⊔ A : Subgroup (adjointGroup .G2 K)) : Set (adjointGroup .G2 K)) at hxSup
    rwa [Subgroup.coe_mul_of_left_le_normalizer_right R A hnorm] at hxSup
  obtain ⟨s, hs, a, ha, hsa⟩ := hprod
  refine ⟨s, by rwa [hCR], fun c hc => ?_⟩
  have hcR : c ∈ R := hCR ▸ hc
  rw [← hsa]
  calc (s * a) * c * (s * a)⁻¹ = s * (a * c) * a⁻¹ * s⁻¹ := by group
    _ = s * (c * a) * a⁻¹ * s⁻¹ := by rw [hAR a ha c hcR]
    _ = s * c * s⁻¹ := by group
theorem g2_classicalModelAction {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) : ClassicalModelAction (adjointGroup .G2 K) := by
  intro z hz1 hz3 C hC _ x hzx _
  have hx : x ∈ Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hzx.symm
  obtain ⟨s, hs, heq⟩ := g2_inner_on_component hn hK hz3 hz1 hC hx
  refine ⟨QuotientGroup.mk ⟨s, hs⟩, ?_⟩
  intro c c' hcc
  have hval : (c' : adjointGroup .G2 K) = s * c * s⁻¹ := by
    rw [← hcc, MulAut.conj_apply]
    exact heq c c.2
  have hinside : (⟨s, hs⟩ * c * ⟨s, hs⟩⁻¹ : C) = c' := Subtype.ext hval.symm
  calc (c' : C ⧸ Subgroup.center C) = QuotientGroup.mk (⟨s, hs⟩ * c * ⟨s, hs⟩⁻¹) := by
          rw [hinside]
    _ = _ := by rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]

theorem g2_rawActionAt {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) :
    RawActionAt (TableBExc.RecipeGroup .G2 K) (TableBExc.RecipeID .G2 K) := by
  let θ := TableBExc.recipeEquiv .G2 K
  have hI : ∀ β ∈ TableBExc.RecipeID .G2 K, ∃ y : adjointGroup .G2 K,
      ∀ r : TableBExc.RecipeGroup .G2 K, θ (β r) = y * θ r * y⁻¹ := by
    intro β hβ
    obtain ⟨y, rfl⟩ := chevG2_idImage_subset_inn K hβ
    exact ⟨θ y, fun r => by simp only [MulAut.conj_apply, map_mul, map_inv]⟩
  refine rawActionAt_of_model θ hI (g2_classicalModelAction hn hK) ?_
  intro z hz
  have hzC : z ∈ Subgroup.center (adjointGroup .G2 K) := by
    rw [Subgroup.mem_center_iff]
    exact fun y => (hz y).symm
  rwa [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hzC

theorem noSetupG2_holds : NoSetupG2 := by
  intro lab htag hlab Q hQ
  rcases lab with ⟨tag, rank, n⟩
  dsimp only at htag
  subst tag
  dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, hField, hFinite, hK, hQ⟩ := hQ
  let : Field K := hField
  let : Finite K := hFinite
  refine ⟨K, hField, hFinite, hK, hQ, ?_⟩
  exact coverDescent_holds (TableBExc.RecipeGroup .G2 K) (TableBExc.RecipeID .G2 K)
    (g2_rawActionAt (by simpa using hlab.2.2) hK)

end S2MathAs3_1619Final
