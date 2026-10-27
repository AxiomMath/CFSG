module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {G : Type} [Group G]

theorem GGInnerDiagOnLabel.subgroupOf {S : ℕ → LargeEvenLabel → Prop} {p : ℕ} {Bs K : Subgroup G}
    (h : GGInnerDiagOnLabel S p Bs K) :
    GGInnerDiagOnLabel S p (Bs.subgroupOf K) (⊤ : Subgroup ↥K) := by
  refine largeEvenMarking_congr (Subgroup.topEquiv (G := ↥K)) ?_ h
  intro lab R _ I F θ hθ
  obtain ⟨hS, -, hb⟩ := hθ
  refine ⟨hS, Subgroup.le_normalizer_of_normal, ?_⟩
  intro b hbK
  obtain ⟨φ, hφ, hind⟩ := hb ((b : ↥K) : G) (Subgroup.mem_subgroupOf.1 hbK)
  refine ⟨φ, hφ, (largeEvenInduces_congr_equiv (Subgroup.topEquiv (G := ↥K)) θ
    (fun l l' : ↥(⊤ : Subgroup ↥K) => (l' : ↥K) = b⁻¹ * l * b)
    (fun y y' : ↥K => (y' : G) = (((b : ↥K) : G))⁻¹ * y * (((b : ↥K) : G)))
    (fun x x' => ?_) φ).2 hind⟩
  rw [Subtype.ext_iff]
  rfl

end CFSG.StandardType

end
