module

public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenFourE
public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenThreeD
public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenInit

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.QuasithinUnique.Setup.Campbell
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem b15_prime_isSylowIn_of_le_of_le {p : ℕ} {P A B : Subgroup G}
    (hP : IsSylowIn p P B) (hPA : P ≤ A) (hAB : A ≤ B) : IsSylowIn p P A := by
  refine ⟨hPA, hP.isPGroup, fun hdvd => hP.not_dvd_relIndex ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex P A B hPA hAB]
  exact hdvd.mul_right _

private theorem b15_prime_exists_minimal {F : Subgroup G → Prop} {H₁ : Subgroup G} (hF : F H₁) :
    ∃ H₀ : Subgroup G, H₀ ≤ H₁ ∧ F H₀ ∧ ∀ H' : Subgroup G, H' ≤ H₀ → F H' → H' = H₀ := by
  obtain ⟨H₀, ⟨hH₀, hF₀⟩, hmin⟩ :=
    WellFounded.has_min wellFounded_lt {H : Subgroup G | H ≤ H₁ ∧ F H} ⟨H₁, le_rfl, hF⟩
  refine ⟨H₀, hH₀, hF₀, fun H' hle hF' => ?_⟩
  by_contra hne
  exact hmin H' ⟨hle.trans hH₀, hF'⟩ (lt_of_le_of_ne hle hne)

private theorem b15_prime_zOmega15_comm (Q : Subgroup G) :
    ∀ x ∈ zOmega15 Q, ∀ y ∈ zOmega15 Q, x * y = y * x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx y hy
  have hE : CFSG.IsElementaryAbelian 2 (elemCenterIn 2 Q) := elemCenterIn_isElementaryAbelian 2 Q
  have := hE.toIsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
  exact congrArg Subtype.val this

section Certified


theorem Cex15.false_of_inputs {M V₀ V U S : Subgroup G}
    (hI : NamedInputs15 G) (hW : W15Eight1 G) (h2b : W15Ten2b G)
    (hD : W15Eleven3Dich G) (hS4 : W15Eleven3S4 G) (h4 : W15Eleven4Bar G)
    (hS : Std15 G) (h : Cex15 M V₀ V U S) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨H₀, hH₀C, hF₀, hmin₀⟩ :=
    b15_prime_exists_minimal (F := Fam15 V₀ V U S) (h.centralizer_mem_fam hI hS)
  have hS₀ : IsSylowIn 2 S H₀ :=
    b15_prime_isSylowIn_of_le_of_le h.isSylowIn_centralizer hF₀.S_le hH₀C
  have hP₀ : Hyp1510 V₀ V U S H₀ S :=
    ⟨hF₀, hS₀, h.V₀_le_S, le_rfl, fun H' hle _ hF' => hmin₀ H' hle hF'⟩
  obtain ⟨Q₀, p, c⟩ := Cfg1511.exists_of_inputs hI hW h2b hS h hP₀
  obtain ⟨X, v, hX⟩ := c.exists_xData
  obtain ⟨R, hR, hSR⟩ := exists_isSylowIn_ge 2 c.S_le_cTilde c.cex.sylow.isPGroup
  obtain ⟨hUZ, hRZ⟩ := c.three hD hS4 hX hR (inf_le_left.trans hSR)
  have hHZ := c.H_le_normalizer_zOmega15 hD hS4 hX
  have hH₁Z : H₀ ⊔ R ≤ normalizer (zOmega15 (qSub15 M V₀ V U H₀ S) : Set G) := sup_le hHZ hRZ
  have hfam₁ : Fam15 V₀ V U S (H₀ ⊔ R) := by
    refine ⟨hF₀.S_le.trans le_sup_left, fun hV => ?_, fun x hx y hy => ?_⟩
    · have hH₀N : H₀ ≤ normalizer ((pCoreOf 2 (H₀ ⊔ R) ⊓ H₀ : Subgroup G) : Set G) :=
        (le_inf (le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (H₀ ⊔ R)))
          Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf
      have hN : pCoreOf 2 (H₀ ⊔ R) ⊓ H₀ ≤ pCoreOf 2 H₀ :=
        CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hH₀N
          ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (H₀ ⊔ R)).to_le inf_le_left)
      exact Fam15.not_V₀_le_pCoreOf h hF₀ fun w hw =>
        hN ⟨hV (c.cex.hyp.h6.le hw), c.hyp.V₀_le_H hw⟩
    · have hle : zSub15 V₀ U (H₀ ⊔ R) ≤ zOmega15 (qSub15 M V₀ V U H₀ S) := by
        refine conjClosure_le fun k hk z hz => ?_
        exact (Subgroup.mem_normalizer_iff.1 (hH₁Z hk) z).1 (hUZ hz)
      exact b15_prime_zOmega15_comm _ x (hle hx) y (hle hy)
  obtain ⟨P₁, hP₁, hRP₁⟩ := exists_isSylowIn_ge 2 (le_sup_right : R ≤ H₀ ⊔ R) hR.isPGroup
  obtain ⟨H₂, hH₂H₁, ⟨hP₁H₂, hF₂⟩, hmin₂⟩ :=
    b15_prime_exists_minimal (F := fun H' => P₁ ≤ H' ∧ Fam15 V₀ V U S H')
      (⟨hP₁.le, hfam₁⟩ : P₁ ≤ H₀ ⊔ R ∧ Fam15 V₀ V U S (H₀ ⊔ R))
  have hSP₁ : S ≤ P₁ := hSR.trans hRP₁
  have hP₂ : Hyp1510 V₀ V U S H₂ P₁ :=
    ⟨hF₂, b15_prime_isSylowIn_of_le_of_le hP₁ hP₁H₂ hH₂H₁, h.V₀_le_S.trans hSP₁, hSP₁,
      fun H' hle hP hF' => hmin₂ H' hle ⟨hP, hF'⟩⟩
  obtain ⟨Q₁, p₁, c₁⟩ := Cfg1511.exists_of_inputs hI hW h2b hS h hP₂
  obtain ⟨X₁, v₁, hX₁⟩ := c₁.exists_xData
  exact c₁.not_le_P h4 hX₁ hR hRP₁

end Certified

end CFSG.LocalAnalysis.WeakClosure81
