module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplitR
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeRComp
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeRAct
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeRCentre
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

theorem leafR_holds :
    ∀ (X : Type) [Group X] [Finite X], commutator X = ⊤ →
      ∀ (R : Type) [Group R] (θ : X ⧸ Subgroup.center X ≃* R) (A : Subgroup (MulAut X))
        (δ : MulAut X) (J : Subgroup X), GGKLocal A δ J →
        (∀ Q : Subgroup X, IsComponentOf Q (ggAutFixedSubgroup δ) → Q = J) → 3 ^ 3 ≤ Nat.card A →
        ∃ (Ā : Subgroup (MulAut R)) (δ' : MulAut R) (J' : Subgroup R), RDatum Ā δ' J' ∧
          Nat.card Ā = Nat.card A ∧ ggInducedAut θ δ = δ' ∧ (∀ a ∈ A, ggInducedAut θ a ∈ Ā) ∧
          J' = J.map (proj θ) ∧
          (Subgroup.center J = ⊥ → Subgroup.center J' = ⊥ ∧ J ⊓ Subgroup.center X = ⊥) ∧
          (Subgroup.center J ≠ ⊥ → Subgroup.center J' ≠ ⊥ ∨ J ⊓ Subgroup.center X ≠ ⊥) := by
  intro X _ _ hX R _ θ A δ J hkl huniq hcard
  have hinj : Function.Injective (ggInducedAut θ) :=
    ggInducedAut_injective_of_perfect hX θ
  have hcomp := leafRComp_holds X hX R θ δ
  have hJperf : commutator J = ⊤ := hkl.1.2.2.2.1.2.2.1
  have hact := leafRAct_holds X R θ J hJperf
  have hcentre := leafRCentre_holds X R θ J
  refine ⟨A.map (ggInducedAut θ), ggInducedAut θ δ, J.map (proj θ),
    ?_, ?_, rfl, ?_, rfl, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact CFSG.Open.IsElemAbelian.map hkl.1.1 (ggInducedAut θ)
    · exact ⟨δ, hkl.1.2.1, rfl⟩
    · intro h
      exact hkl.1.2.2.1 (hinj (by simpa using h))
    · exact hcomp.1 J hkl.1.2.2.2.1
    · intro Q hQ
      obtain ⟨J₀, hJ₀, hJ₀map⟩ := hcomp.2 Q hQ
      rw [← hJ₀map, huniq J₀ hJ₀]
    · intro a ha j hj
      obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
      exact hact.1 a₀ (hkl.1.2.2.2.2 a₀ ha₀) j hj
    · intro a ha hfix
      obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
      have hz : a₀ ∈ Subgroup.zpowers δ := hkl.2 a₀ ha₀ (hact.2 a₀ hfix)
      have hmem : ggInducedAut θ a₀ ∈ (Subgroup.zpowers δ).map (ggInducedAut θ) :=
        ⟨a₀, hz, rfl⟩
      rw [MonoidHom.map_zpowers] at hmem
      exact hmem
    · rw [Subgroup.card_map_of_injective hinj]
      exact hcard
  · exact Subgroup.card_map_of_injective hinj
  · intro a ha
    exact ⟨a, ha, rfl⟩
  · intro h
    exact hcentre.1 h
  · intro h
    exact hcentre.2 h

end CFSG.StandardType.TablePThreeKG

end
