module

public import CFSG.LocalAnalysis.StandardType.KGLangS1EBridgeFix
public import CFSG.LocalAnalysis.StandardType.KGLangS1ECover
public import CFSG.LocalAnalysis.StandardType.KGLangS1ENormalFormE6Diag
public import CFSG.LocalAnalysis.StandardType.GGL45NtDefs
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

import CFSG.LocalAnalysis.StandardType.KGLangS1EModelDerived

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.C14Exc

private theorem kgLangS1EModelE6EvenAux_nonabelian {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : ∃ a b : A, a * b ≠ b * a) : ∃ a b : B, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h
  exact ⟨e a, e b, fun h' => hab (e.injective (by rw [map_mul, map_mul, h']))⟩

theorem kgLangS1E_J0_model_E6_even
    {n : ℕ} (hn : 1 ≤ n) {K₁ : Type} [Field K₁] [Finite K₁] (hK₁ : Nat.card K₁ = 2 ^ n)
    (heven : Even n)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {e : ℕ} (he : 1 ≤ e) (hen : e * 3 = n)
    (ρ : LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K₁ false) →* ModGL .E6 L)
    (Θ : ratPts .E6 L (endPow (frobTwistGL .E6 L 2 e 1) 3) →*
      MulAut (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K₁ false)))
    (hρ : Function.Injective ρ) (hρG : ∀ r, ρ r ∈ ratPts .E6 L (endPow (frobTwistGL .E6 L 2 e 1) 3))
    (hΘ : Function.Injective Θ)
    (hI : ∀ φ, φ ∈ LargeEvenChevIDImage (LargeEvenCartanE 6) K₁
      (LargeEvenChevH (LargeEvenCartanE 6) K₁ false) ↔ ∃ g, Θ g = φ)
    (hconjΘ : ∀ g r, ρ (Θ g r) = (g : ModGL .E6 L) * ρ r * (g : ModGL .E6 L)⁻¹)
    (hFj : ∀ f ∈ LargeEvenChevFieldImage (LargeEvenCartanE 6) K₁
        (LargeEvenChevH (LargeEvenCartanE 6) K₁ false), orderOf f = 3 →
      ∃ j : ℕ, ¬ 3 ∣ j ∧ ∀ r, ρ (f r) = (endPow (frobTwistGL .E6 L 2 e 1) j) (ρ r))
    {K : Type} [Group K] [Finite K]
    (θ : K ⧸ Subgroup.center K ≃*
      LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K₁ false))
    (hcomm : commutator K = ⊤) (A : Subgroup (MulAut K)) (hA : IsElemAbelian 3 A)
    (hAI : ∀ α ∈ A, ∃ u ∈ LargeEvenChevIDImage (LargeEvenCartanE 6) K₁
        (LargeEvenChevH (LargeEvenCartanE 6) K₁ false),
      ∃ f ∈ Subgroup.closure (LargeEvenChevFieldImage (LargeEvenCartanE 6) K₁
        (LargeEvenChevH (LargeEvenCartanE 6) K₁ false)), kgInducedAut θ α = u * f)
    {ξ : MulAut K} (hξ : ξ ∈ A)
    (hξI : kgInducedAut θ ξ ∉ LargeEvenChevIDImage (LargeEvenCartanE 6) K₁
      (LargeEvenChevH (LargeEvenCartanE 6) K₁ false))
    {J₀ : Subgroup K} (hJ₀ : IsComponentOf J₀ (ggFixSub ξ)) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (ι : k →+* L) (g : ModGL .E6 L),
      Nat.card k = 2 ^ e ∧ g ∈ adjointGroup .E6 L ∧
      ∃ ψ : (↥J₀ ⧸ Subgroup.center ↥J₀) ≃* ↥(adjointGroup .E6 k),
        ∀ x ∈ {x : ModGL .E6 L | x ∈ ratPts .E6 L (endPow (frobTwistGL .E6 L 2 e 1) 3) ∧
            ∃ α ∈ A, kgInducedAut θ α ∈ LargeEvenChevIDImage (LargeEvenCartanE 6) K₁
              (LargeEvenChevH (LargeEvenCartanE 6) K₁ false) ∧
            ∀ r, ρ (kgInducedAut θ α r) = x * ρ r * x⁻¹},
          ∃ y ∈ RecipeExcLang.inndiagGroup .E6 k, baseChangeGL (τ := .E6) ι y = g⁻¹ * x * g ∧
            ∃ α ∈ A, ∀ j : ↥J₀, ∃ j' : ↥J₀, (j' : K) = α j ∧
              (ψ (QuotientGroup.mk j') : ModGL .E6 k) = y * ψ (QuotientGroup.mk j) * y⁻¹ := by
  classical
  let R := LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K₁ false)
  let : Group R := QuotientGroup.Quotient.group
    (Subgroup.center (↥(LargeEvenChevH (LargeEvenCartanE 6) K₁ false)))
  let I : Set (MulAut R) := LargeEvenChevIDImage (LargeEvenCartanE 6) K₁
    (LargeEvenChevH (LargeEvenCartanE 6) K₁ false)
  let F : Set (MulAut R) := LargeEvenChevFieldImage (LargeEvenCartanE 6) K₁
    (LargeEvenChevH (LargeEvenCartanE 6) K₁ false)
  let F₀ : ModGL .E6 L →* ModGL .E6 L := frobTwistGL .E6 L 2 e 1
  have hcharK : CharP K₁ 2 := charP_two_of_card hK₁
  have hstab : ∀ g ∈ adjointGroup .E6 L, F₀ g ∈ adjointGroup .E6 L := by
    intro g hg
    show frobTwistGL .E6 L 2 e 1 g ∈ adjointGroup .E6 L
    rw [frobTwistGL_apply]
    simpa using (entrywiseFrobGL_mem (p := 2) (e := e) hg)
  have hq₁ : CFSG.IsQuasisimple ↥(adjointGroup .E6 K₁) :=
    CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 K₁
  obtain ⟨eQ⟩ := centerQuot_chevGroup_equiv K₁ .E6
  have hRsimple : IsSimpleGroup R := by
    have : IsSimpleGroup (CFSG.Blueprint.AdjointQuotient .E6 K₁) := hq₁.2.1
    exact eQ.isSimpleGroup
  have hRnab : ∃ a b : R, a * b ≠ b * a :=
    kgLangS1EModelE6EvenAux_nonabelian eQ.symm hq₁.2.2
  have hinner : RecipeExcLang.InnerFieldTrivial .E6 K₁ :=
    RecipeExcLang.innerFieldTrivial_E6
  have hconj : GGRawFieldConj 3 R I F :=
    RecipeExcLang.ggRawFieldConj_chev_two (K := K₁) (n := n) (p := 3) hn hK₁
      (by norm_num) hinner
  have hρG' : ∀ r, ρ r ∈ ratPts .E6 L (endPow F₀ 3) := hρG
  have hFj' : ∀ f ∈ F, orderOf f = 3 → ∃ j : ℕ, ¬ 3 ∣ j ∧
      ∀ r, ρ (f r) = (endPow F₀ j) (ρ r) := hFj
  have hcommI : ∀ φ₁ ∈ I, ∀ φ₂ ∈ I,
      φ₁ * φ₂ * φ₁⁻¹ * φ₂⁻¹ ∈ (MulAut.conj : R →* MulAut R).range := by
    intro φ₁ h₁ φ₂ h₂
    exact chevIDImage_commutator_mem_inn (A := LargeEvenCartanE 6) (K := K₁)
      (H := LargeEvenChevH (LargeEvenCartanE 6) K₁ false)
      (show φ₁ ∈ LargeEvenChevIDImage (LargeEvenCartanE 6) K₁
        (LargeEvenChevH (LargeEvenCartanE 6) K₁ false) from h₁)
      (show φ₂ ∈ LargeEvenChevIDImage (LargeEvenCartanE 6) K₁
        (LargeEvenChevH (LargeEvenCartanE 6) K₁ false) from h₂)
  obtain ⟨k, hkfield, hkfin, ι, hkcard, hfix⟩ :=
    kgLangS1E_ratPts_frob_E6_inndiag (L := L) he
  have hfix' : ratPts .E6 L F₀ =
      (RecipeExcLang.inndiagGroup .E6 k).map (baseChangeGL ι) := hfix
  have hTΓ : (adjointGroup .E6 k) ≤ (RecipeExcLang.inndiagGroup .E6 k) :=
    RecipeExcLang.adjointGroup_le_inndiagGroup (τ := .E6) (K := k)
  have hΓT : ⁅(RecipeExcLang.inndiagGroup .E6 k),
      (RecipeExcLang.inndiagGroup .E6 k)⁆ ≤ (adjointGroup .E6 k) := by
    rw [Subgroup.commutator_le]
    intro w hw w' hw'
    obtain ⟨b, j, hj, rfl⟩ :=
      (RecipeExcLang.mem_inndiagGroup (τ := .E6) (K := k)).mp
        (show w ∈ RecipeExcLang.inndiagGroup .E6 k from hw)
    obtain ⟨b', j', hj', rfl⟩ :=
      (RecipeExcLang.mem_inndiagGroup (τ := .E6) (K := k)).mp
        (show w' ∈ RecipeExcLang.inndiagGroup .E6 k from hw')
    simp only [commutatorElement_def]
    set d : ModGL .E6 k :=
      CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit .E6 b with hd
    set d' : ModGL .E6 k :=
      CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit .E6 b' with hd'
    have hdΓ : d ∈ RecipeExcLang.inndiagGroup .E6 k := by
      rw [hd]
      exact RecipeExcLang.rootDiagUnit_mem_inndiagGroup b
    have hd'Γ : d' ∈ RecipeExcLang.inndiagGroup .E6 k := by
      rw [hd']
      exact RecipeExcLang.rootDiagUnit_mem_inndiagGroup b'
    have hdd : d * d' = d' * d := by
      rw [hd, hd', ← rootDiagUnit_mul, ← rootDiagUnit_mul]
      exact congrArg _ (mul_comm b b')
    have e₁ : (d * j) * (d' * j') * (d * j)⁻¹ * (d' * j')⁻¹ =
        d * (j * (d' * j') * j⁻¹ * (d' * j')⁻¹) * d⁻¹ *
          (d * (d' * j') * d⁻¹ * (d' * j')⁻¹) := by group
    have e₂ : d * (d' * j') * d⁻¹ * (d' * j')⁻¹ =
        (d * d' * d⁻¹ * d'⁻¹) * (d' * (d * j' * d⁻¹ * j'⁻¹) * d'⁻¹) := by group
    have h₁ : j * (d' * j') * j⁻¹ * (d' * j')⁻¹ ∈ adjointGroup .E6 k := by
      have hconj : (d' * j') * j⁻¹ * (d' * j')⁻¹ ∈ adjointGroup .E6 k :=
        RecipeExcLang.conj_mem_adjointGroup_of_mem_inndiag (τ := .E6) (K := k)
          (mul_mem hd'Γ
            (RecipeExcLang.adjointGroup_le_inndiagGroup (τ := .E6) (K := k) hj'))
          (inv_mem hj)
      rw [show j * (d' * j') * j⁻¹ * (d' * j')⁻¹ =
        j * ((d' * j') * j⁻¹ * (d' * j')⁻¹) by group]
      exact mul_mem hj hconj
    have h₂ : d * j' * d⁻¹ * j'⁻¹ ∈ adjointGroup .E6 k := by
      have hconj : d * j' * d⁻¹ ∈ adjointGroup .E6 k :=
        RecipeExcLang.conj_mem_adjointGroup_of_mem_inndiag (τ := .E6) (K := k) hdΓ hj'
      rw [show d * j' * d⁻¹ * j'⁻¹ = (d * j' * d⁻¹) * j'⁻¹ by group]
      exact mul_mem hconj (inv_mem hj')
    have hcomm_dd' : d * d' * d⁻¹ * d'⁻¹ = 1 := by
      rw [hdd]
      group
    rw [e₁, e₂, hcomm_dd', one_mul]
    have hX : d * (j * (d' * j') * j⁻¹ * (d' * j')⁻¹) * d⁻¹ ∈ adjointGroup .E6 k :=
      RecipeExcLang.conj_mem_adjointGroup_of_mem_inndiag (τ := .E6) (K := k) hdΓ h₁
    have hY : d' * (d * j' * d⁻¹ * j'⁻¹) * d'⁻¹ ∈ adjointGroup .E6 k :=
      RecipeExcLang.conj_mem_adjointGroup_of_mem_inndiag (τ := .E6) (K := k) hd'Γ h₂
    exact mul_mem hX hY
  have hq_k : CFSG.IsQuasisimple ↥(adjointGroup .E6 k) :=
    CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 k
  let ebot : (↥(adjointGroup .E6 k) ⧸ Subgroup.center ↥(adjointGroup .E6 k)) ≃*
      ↥(adjointGroup .E6 k) :=
    (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .E6) (K := k))).trans
      QuotientGroup.quotientBot
  have hTperf : ⁅(adjointGroup .E6 k), (adjointGroup .E6 k)⁆ = (adjointGroup .E6 k) := by
    have hperf : commutator ↥(adjointGroup .E6 k) = ⊤ := hq_k.1.commutator_eq_top
    rw [← Subgroup.map_subtype_commutator (adjointGroup .E6 k), hperf, Subgroup.map_top]
    exact Subgroup.range_subtype (adjointGroup .E6 k)
  have hTs : IsSimpleGroup ↥(adjointGroup .E6 k) := by
    have : IsSimpleGroup
        (↥(adjointGroup .E6 k) ⧸ Subgroup.center ↥(adjointGroup .E6 k)) := hq_k.2.1
    exact ebot.symm.isSimpleGroup
  have hTna : ∃ a b : ↥(adjointGroup .E6 k), a * b ≠ b * a :=
    kgLangS1EModelE6EvenAux_nonabelian ebot hq_k.2.2
  obtain ⟨g, hgadj, ψ, hψ⟩ :=
    kgLangS1E_J0_model_derived (p := 3) Nat.prime_three hcommI hconj hRsimple hRnab hstab
      ρ Θ hρ hρG' hΘ hI hconjΘ hFj' ι (RecipeExcLang.inndiagGroup .E6 k)
      (adjointGroup .E6 k) hfix' hTΓ hΓT hTperf hTs hTna θ A hA hAI hξ hξI hJ₀
  exact ⟨k, hkfield, hkfin, ι, g, hkcard, hgadj, ψ, hψ⟩

end CFSG.StandardType
