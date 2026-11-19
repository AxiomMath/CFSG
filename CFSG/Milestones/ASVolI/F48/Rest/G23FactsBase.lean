
module

public import Certificates.Certificate7762
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

@[expose] public section

namespace CFSG.ASVolI

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.Certificates

attribute [local irreducible] burnsideF48t_g23LArr burnsideF48t_g23Tau burnsideF48t_g23GensArr
  burnsideF48t_g23PtsStr

theorem burnsideF48t_g23_P1Arr : burnsideF48t_g23P1Arr.size = 3 ∧
    burnsideF48t_g23P1Arr[0]! = burnsideF48t_g23LArr[0]! ∧
    burnsideF48t_g23P1Arr[1]! = burnsideF48t_g23LArr[1]! ∧
    burnsideF48t_g23P1Arr[2]! = burnsideF48t_g23LArr[2]! :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem burnsideF48t_g23_P2Arr : burnsideF48t_g23P2Arr.size = 3 ∧
    burnsideF48t_g23P2Arr[0]! = burnsideF48t_g23LArr[0]! ∧
    burnsideF48t_g23P2Arr[1]! = burnsideF48t_g23LArr[1]! ∧
    burnsideF48t_g23P2Arr[2]! = burnsideF48t_g23LArr[3]! :=
  ⟨rfl, rfl, rfl, rfl⟩

def burnsideF48t_g23P1Idx (k : ℕ) : ℕ := k

def burnsideF48t_g23P2Idx (k : ℕ) : ℕ := k + k / 2

section Letters

theorem burnsideF48t_g23_X_eq : burnsideF48t_g23X =
    Subgroup.closure (Set.range fun k : Fin 4 => burnsideF48t_g23γ k) :=
  Certificates.certificate7762.1

theorem burnsideF48t_g23_γ_mem {i : ℕ} (hi : i < 4) : burnsideF48t_g23γ i ∈ burnsideF48t_g23X := by
  rw [burnsideF48t_g23_X_eq]
  exact Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩

theorem burnsideF48t_g23_σ_mem {i : ℕ} (hi : i < 4) :
    burnsideF48t_g23σ i ∈ burnsideF48t_g23X :=
  Certificates.certificate7762.2.2.2.2.1 i hi

theorem burnsideF48t_g23_P1'_eq_closure : burnsideF48t_g23P1' =
    Subgroup.closure (Set.range fun k : Fin burnsideF48t_g23P1Arr.size =>
      burnsideF48t_g23σ (burnsideF48t_g23P1Idx k)) := by
  rw [Certificates.certificate7762.2.1]
  congr 1
  ext g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
  constructor
  · rintro (rfl | rfl | rfl)
    exacts [⟨⟨0, by decide⟩, rfl⟩, ⟨⟨1, by decide⟩, rfl⟩, ⟨⟨2, by decide⟩, rfl⟩]
  · rintro ⟨⟨k, hk⟩, rfl⟩
    have hk3 : k < 3 := hk
    interval_cases k
    exacts [Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)]

theorem burnsideF48t_g23_P2'_eq_closure : burnsideF48t_g23P2' =
    Subgroup.closure (Set.range fun k : Fin burnsideF48t_g23P2Arr.size =>
      burnsideF48t_g23σ (burnsideF48t_g23P2Idx k)) := by
  rw [Certificates.certificate7762.2.2.1]
  congr 1
  ext g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
  constructor
  · rintro (rfl | rfl | rfl)
    exacts [⟨⟨0, by decide⟩, rfl⟩, ⟨⟨1, by decide⟩, rfl⟩, ⟨⟨2, by decide⟩, rfl⟩]
  · rintro ⟨⟨k, hk⟩, rfl⟩
    have hk3 : k < 3 := hk
    interval_cases k
    · exact Or.inl (congrArg burnsideF48t_g23σ (by simp [burnsideF48t_g23P2Idx]))
    · exact Or.inr (Or.inl (congrArg burnsideF48t_g23σ (by simp [burnsideF48t_g23P2Idx])))
    · exact Or.inr (Or.inr (congrArg burnsideF48t_g23σ (by simp [burnsideF48t_g23P2Idx])))

end Letters

end CFSG.ASVolI
