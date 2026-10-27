module

public import CFSG.LocalAnalysis.StandardType.KGLangS1EBridgeFix
public import CFSG.LocalAnalysis.StandardType.KGLangS1ECover
public import CFSG.LocalAnalysis.StandardType.KGLangS1ENormalFormTwE6Diag
public import CFSG.LocalAnalysis.StandardType.GGL45NtDefs
import CFSG.LocalAnalysis.StandardType.KGLangS1EModelDerived
import CFSG.LieType.Chevalley.GraphFixedFinitePerfect
import CFSG.LieType.Chevalley.TrialityFullAmbientFixedGroup
import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Dvd
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.C14Exc
open scoped commutatorElement

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley in
private theorem kgLangS1EModelTwE6OddAux_twInndiag_comm_le
    {k : Type} [Field k] [Finite k] {e : ℕ} (he : 1 ≤ e)
    (hk : Nat.card k = (2 ^ e) ^ 2) {σ : k ≃+* k} (hσ : ∀ c, σ c = c ^ 2 ^ e) :
    ⁅RecipeExcLang.twInndiagGroup k σ, RecipeExcLang.twInndiagGroup k σ⁆ ≤
      graphFixedRootGroup TwistTag.E6 k σ.toRingHom := by
  have : CharP k 2 := charP_two_of_card (m := e * 2) (by rw [hk, pow_mul])
  have : CharP (AlgebraicClosure k) 2 :=
    charP_of_injective_algebraMap (algebraMap k (AlgebraicClosure k)).injective 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFr : ∀ c : AlgebraicClosure k,
      iterateFrobenius (AlgebraicClosure k) 2 e c = c ^ (2 ^ e) := fun c => by
    rw [iterateFrobenius_def]
  set Γ := RecipeExcLang.twInndiagGroup k σ
  set C₀ := graphFixedRootGroup TwistTag.E6 k σ.toRingHom
  have hconj : ∀ w ∈ Γ, ∀ c ∈ C₀, w * c * w⁻¹ ∈ C₀ := fun w hw c hc =>
    RecipeExcLang.conj_mem_C0_of_mem_twInndiag he hk hσ hFr hw hc
  have hle : C₀ ≤ Γ := RecipeExcLang.graphFixedRootGroup_le_twInndiag σ
  rw [Subgroup.commutator_le]
  intro w hw w' hw'
  obtain ⟨b, -, c, hc, rfl⟩ := RecipeExcLang.exists_decomp_of_mem_twInndiag he hk hσ hFr hw
  obtain ⟨b', -, c', hc', rfl⟩ := RecipeExcLang.exists_decomp_of_mem_twInndiag he hk hσ hFr hw'
  have hdd : rootDiagUnit TwistTag.E6.tag b * rootDiagUnit TwistTag.E6.tag b' =
      rootDiagUnit TwistTag.E6.tag b' * rootDiagUnit TwistTag.E6.tag b := by
    rw [← CFSG.LieType.Chevalley.rootDiagUnit_mul, ← CFSG.LieType.Chevalley.rootDiagUnit_mul,
      mul_comm]
  generalize rootDiagUnit TwistTag.E6.tag b = d at hw hdd ⊢
  generalize rootDiagUnit TwistTag.E6.tag b' = d' at hw' hdd ⊢
  have hd : d ∈ Γ := by simpa using Γ.mul_mem hw (Γ.inv_mem (hle hc))
  have hd' : d' ∈ Γ := by simpa using Γ.mul_mem hw' (Γ.inv_mem (hle hc'))
  have hX : d * c * d⁻¹ ∈ C₀ := hconj d hd c hc
  have hY : d' * c' * d'⁻¹ ∈ C₀ := hconj d' hd' c' hc'
  have hkey : (d * d')⁻¹ * (d' * d) = 1 := by rw [hdd, inv_mul_cancel]
  have hid : ⁅d * c, d' * c'⁆ = d * c * d⁻¹ * (d * (d' * c' * d'⁻¹) * d⁻¹) *
      (d' * (d * c * d⁻¹)⁻¹ * d'⁻¹) * (d' * c' * d'⁻¹)⁻¹ := by
    calc ⁅d * c, d' * c'⁆ = d * c * d' * c' * 1 * c⁻¹ * d⁻¹ * c'⁻¹ * d'⁻¹ := by
          rw [commutatorElement_def]; group
      _ = d * c * d' * c' * ((d * d')⁻¹ * (d' * d)) * c⁻¹ * d⁻¹ * c'⁻¹ * d'⁻¹ := by
          rw [hkey]
      _ = _ := by group
  rw [hid]
  exact C₀.mul_mem (C₀.mul_mem (C₀.mul_mem hX (hconj d hd _ hY))
    (hconj d' hd' _ (C₀.inv_mem hX))) (C₀.inv_mem hY)

theorem kgLangS1E_J0_model_twE6_odd
    {n : ℕ} (hn : 1 ≤ n) (hodd : Odd n) {K₁ : Type} [Field K₁] [Finite K₁]
    (hK₁ : Nat.card K₁ = (2 ^ n) ^ 2)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {e : ℕ} (he : 1 ≤ e) (hen : e * 3 = n)
    (ρ : LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K₁ LargeEvenRhoE6 n) →*
      ModGL TwistTag.E6.tag L)
    (Θ : ratPts TwistTag.E6.tag L
        (endPow (frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L)) 3) →*
      MulAut (LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K₁ LargeEvenRhoE6 n)))
    (hρ : Function.Injective ρ)
    (hρG : ∀ r, ρ r ∈ ratPts TwistTag.E6.tag L
      (endPow (frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L)) 3))
    (hΘ : Function.Injective Θ)
    (hI : ∀ φ, φ ∈ LargeEvenChevIDImage (LargeEvenCartanE 6) K₁
        (LargeEvenTwistedH (LargeEvenCartanE 6) K₁ LargeEvenRhoE6 n) ↔ ∃ g, Θ g = φ)
    (hconjΘ : ∀ g r, ρ (Θ g r) = (g : ModGL TwistTag.E6.tag L) * ρ r *
      (g : ModGL TwistTag.E6.tag L)⁻¹)
    (hFj : ∀ f ∈ LargeEvenChevFieldImage (LargeEvenCartanE 6) K₁
        (LargeEvenTwistedH (LargeEvenCartanE 6) K₁ LargeEvenRhoE6 n), orderOf f = 3 →
      ∃ j : ℕ, ¬ 3 ∣ j ∧ ∀ r, ρ (f r) =
        (endPow (frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L)) j) (ρ r))
    {K : Type} [Group K] [Finite K]
    (θ : K ⧸ Subgroup.center K ≃*
      LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K₁ LargeEvenRhoE6 n))
    (hcomm : commutator K = ⊤) (A : Subgroup (MulAut K)) (hA : IsElemAbelian 3 A)
    (hAI : ∀ α ∈ A, ∃ u ∈ LargeEvenChevIDImage (LargeEvenCartanE 6) K₁
        (LargeEvenTwistedH (LargeEvenCartanE 6) K₁ LargeEvenRhoE6 n),
      ∃ f ∈ Subgroup.closure (LargeEvenChevFieldImage (LargeEvenCartanE 6) K₁
        (LargeEvenTwistedH (LargeEvenCartanE 6) K₁ LargeEvenRhoE6 n)), kgInducedAut θ α = u * f)
    {ξ : MulAut K} (hξ : ξ ∈ A)
    (hξI : kgInducedAut θ ξ ∉ LargeEvenChevIDImage (LargeEvenCartanE 6) K₁
      (LargeEvenTwistedH (LargeEvenCartanE 6) K₁ LargeEvenRhoE6 n))
    {J₀ : Subgroup K} (hJ₀ : IsComponentOf J₀ (ggFixSub ξ)) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (σ : k ≃+* k) (ι : k →+* L)
      (g : ModGL TwistTag.E6.tag L),
      Nat.card k = (2 ^ e) ^ 2 ∧ (∀ c, σ c = c ^ 2 ^ e) ∧ g ∈ adjointGroup TwistTag.E6.tag L ∧
      ∃ ψ : (↥J₀ ⧸ Subgroup.center ↥J₀) ≃* ↥(graphFixedRootGroup TwistTag.E6 k σ.toRingHom),
        ∀ x ∈ {x : ModGL TwistTag.E6.tag L | x ∈ ratPts TwistTag.E6.tag L
            (endPow (frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L)) 3) ∧
          ∃ α ∈ A, kgInducedAut θ α ∈ LargeEvenChevIDImage (LargeEvenCartanE 6) K₁
            (LargeEvenTwistedH (LargeEvenCartanE 6) K₁ LargeEvenRhoE6 n) ∧
          ∀ r, ρ (kgInducedAut θ α r) = x * ρ r * x⁻¹},
          ∃ y ∈ RecipeExcLang.twInndiagGroup k σ,
            baseChangeGL (τ := TwistTag.E6.tag) ι y = g⁻¹ * x * g ∧
            ∃ α ∈ A, ∀ j : ↥J₀, ∃ j' : ↥J₀, (j' : K) = α j ∧
              (ψ (QuotientGroup.mk j') : ModGL TwistTag.E6.tag k) =
                y * ψ (QuotientGroup.mk j) * y⁻¹ := by
  classical
  let R := LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K₁ LargeEvenRhoE6 n)
  let _ : Group R := QuotientGroup.Quotient.group
    (Subgroup.center (↥(LargeEvenTwistedH (LargeEvenCartanE 6) K₁ LargeEvenRhoE6 n)))
  let I : Set (MulAut R) := LargeEvenChevIDImage (LargeEvenCartanE 6) K₁
    (LargeEvenTwistedH (LargeEvenCartanE 6) K₁ LargeEvenRhoE6 n)
  let F : Set (MulAut R) := LargeEvenChevFieldImage (LargeEvenCartanE 6) K₁
    (LargeEvenTwistedH (LargeEvenCartanE 6) K₁ LargeEvenRhoE6 n)
  let F₀ : ModGL TwistTag.E6.tag L →* ModGL TwistTag.E6.tag L :=
    frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L)
  have hstab : ∀ g ∈ adjointGroup TwistTag.E6.tag L, F₀ g ∈ adjointGroup TwistTag.E6.tag L := by
    intro g hg
    show frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L) g ∈
      adjointGroup TwistTag.E6.tag L
    simpa [pow_one] using
      frobTwistGL_diagramMap_pow_mem_adjointGroup (k := L) (p := 2) (e := e) (ε := 1) hg
  obtain ⟨hRsimple, hRnab⟩ := TwE6Dvd.isSimpleGroup_recipeR hn hK₁
  have hconj : GGRawFieldConj 3 R I F :=
    RecipeExcLang.ggRawFieldConj_twE6 (K := K₁) hn hK₁ (p := 3) Nat.prime_three (by norm_num)
  have hρG' : ∀ r, ρ r ∈ ratPts TwistTag.E6.tag L (endPow F₀ 3) := hρG
  have hFj' : ∀ f ∈ F, orderOf f = 3 → ∃ j : ℕ, ¬ 3 ∣ j ∧
      ∀ r, ρ (f r) = (endPow F₀ j) (ρ r) := hFj
  have hcommI : ∀ φ₁ ∈ I, ∀ φ₂ ∈ I,
      φ₁ * φ₂ * φ₁⁻¹ * φ₂⁻¹ ∈ (MulAut.conj : R →* MulAut R).range := by
    intro φ₁ h₁ φ₂ h₂
    exact chevIDImage_commutator_mem_inn (A := LargeEvenCartanE 6) (K := K₁)
      (H := LargeEvenTwistedH (LargeEvenCartanE 6) K₁ LargeEvenRhoE6 n)
      (show φ₁ ∈ LargeEvenChevIDImage (LargeEvenCartanE 6) K₁
        (LargeEvenTwistedH (LargeEvenCartanE 6) K₁ LargeEvenRhoE6 n) from h₁)
      (show φ₂ ∈ LargeEvenChevIDImage (LargeEvenCartanE 6) K₁
        (LargeEvenTwistedH (LargeEvenCartanE 6) K₁ LargeEvenRhoE6 n) from h₂)
  obtain ⟨k, hkfield, hkfin, σ, ι, hkcard, hσ, hfix⟩ :=
    kgLangS1E_ratPts_frob_twE6_inndiag (L := L) he
  have hTΓ : graphFixedRootGroup TwistTag.E6 k σ.toRingHom ≤
      RecipeExcLang.twInndiagGroup k σ :=
    RecipeExcLang.graphFixedRootGroup_le_twInndiag σ
  have hΓT : ⁅RecipeExcLang.twInndiagGroup k σ,
      RecipeExcLang.twInndiagGroup k σ⁆ ≤ graphFixedRootGroup TwistTag.E6 k σ.toRingHom :=
    kgLangS1EModelTwE6OddAux_twInndiag_comm_le he hkcard hσ
  have hTperf : ⁅graphFixedRootGroup TwistTag.E6 k σ.toRingHom,
      graphFixedRootGroup TwistTag.E6 k σ.toRingHom⁆ =
      graphFixedRootGroup TwistTag.E6 k σ.toRingHom :=
    (finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two he k hkcard σ.toRingHom hσ).1
  obtain ⟨hTs, hTna⟩ := isSimpleGroup_graphFixedRootGroup_of_perfect TwistTag.E6 k σ hTperf
  obtain ⟨g, hgadj, ψ, hψ⟩ :=
    kgLangS1E_J0_model_derived (p := 3) Nat.prime_three hcommI hconj hRsimple hRnab hstab
      ρ Θ hρ hρG' hΘ hI hconjΘ hFj' ι (RecipeExcLang.twInndiagGroup k σ)
      (graphFixedRootGroup TwistTag.E6 k σ.toRingHom) hfix hTΓ hΓT hTperf hTs hTna
      θ A hA hAI hξ hξI hJ₀
  exact ⟨k, hkfield, hkfin, σ, ι, g, hkcard, hσ, hgadj, ψ, hψ⟩

end CFSG.StandardType
