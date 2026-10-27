module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylUnitaryCover
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUModelCoprime

public section

namespace CFSG.StandardType.FrameRoute

open Matrix CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.StandardType.LineU

variable {L : Type} [Group L] [Finite L] {F : Type} [Field F] [Finite F] {m : ℕ}

theorem P9_U3a_exists_diagModel (hF : Nat.card F = 4) (hm : 5 ≤ m) (hm6 : m ≠ 6)
    {ψ : L →* LargeEvenProj (unitarySU 2 1 F m)} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L) (hperf : commutator L = ⊤)
    {A : Subgroup (MulAut L)} (hA : CFSG.Open.IsElemAbelian 3 A)
    (hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 F m))
        (LargeEvenGUSet (Fin m) F (2 ^ 1)), ∀ l : L, x (ψ l) = ψ (a l))
    (hcard : 3 ∣ m → 3 ^ (m / 3 + 2) ≤ Nat.card A) :
    ∃ φ : ↥(unitarySU 2 1 F m) →* L, Function.Surjective φ ∧
      (∀ g : ↥(unitarySU 2 1 F m), φ g = 1 →
        ∃ c : F, ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = diagonal (fun _ => c)) ∧
      ∀ a ∈ A, ∃ t : Fin m → F, ActsDiagU φ a t := by
  have hK4 : Nat.card F = (2 ^ 1) ^ 2 := by rw [hF]; norm_num
  have hcov : UnitaryCoverAt 1 m F := unitaryCoverAt hK4 (by omega) (by rintro ⟨h, -⟩; omega)
  by_cases h3 : 3 ∣ m
  · exact exists_diagModel hK4 le_rfl (by omega) Nat.prime_three (by norm_num) h3 hcov hψ hker
      hperf hA hAI (hcard h3)
  · exact exists_diagModel_coprime hK4 le_rfl (by omega) Nat.prime_three (by norm_num) h3 hcov
      hψ hker hperf hA hAI

theorem P9_U3a_exists_diagModel_of_card (hF : Nat.card F = 4) (hm : 5 ≤ m) (hm6 : m ≠ 6)
    {r : ℕ} (hmr : m ≤ r + 3)
    {ψ : L →* LargeEvenProj (unitarySU 2 1 F m)} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L) (hperf : commutator L = ⊤)
    {A : Subgroup (MulAut L)} (hA : CFSG.Open.IsElemAbelian 3 A)
    (hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 F m))
        (LargeEvenGUSet (Fin m) F (2 ^ 1)), ∀ l : L, x (ψ l) = ψ (a l))
    (hcard : 3 ^ r ≤ Nat.card A) :
    ∃ φ : ↥(unitarySU 2 1 F m) →* L, Function.Surjective φ ∧
      (∀ g : ↥(unitarySU 2 1 F m), φ g = 1 →
        ∃ c : F, ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = diagonal (fun _ => c)) ∧
      ∀ a ∈ A, ∃ t : Fin m → F, ActsDiagU φ a t := by
  refine P9_U3a_exists_diagModel hF hm hm6 hψ hker hperf hA hAI fun h3 => ?_
  exact (Nat.pow_le_pow_right (by norm_num) (by omega)).trans hcard

end CFSG.StandardType.FrameRoute

end
