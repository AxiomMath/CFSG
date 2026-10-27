module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2TData
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2TShape
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLarge
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2TSpecial
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2TSubC

public section

universe u

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL2S

namespace F6

namespace GoldAmL2T

variable {D : Type*} [Group D]

@[expose] def subA (A B V : Subgroup D) (y : D) : Subgroup D :=
  (yGrp A B V ⊔ Subgroup.zpowers y) ⊔ conjClosure V B

@[expose] def subB (A B V : Subgroup D) (x : D) : Subgroup D :=
  (conjClosure V B ⊔ Subgroup.zpowers x) ⊔ yGrp A B V

theorem b2Card64Input_holds : GoldAmLarge.B2Card64Input.{u} := by
  intro D _ _ A B z V hgold hn hb hA hT
  have h32 : 32 ≤ Nat.card ↥(A ⊓ B) := by omega
  obtain ⟨x, a, a₁, a₂, g⟩ := (Hyp2.of_critDist_two hgold h32 hn hb hA).exists_gen
  obtain ⟨y, hyA, hy3⟩ := hgold.vertex_left.exists_order_three
  have dA := subDataA g hT hyA hy3
  have dB := subDataB g hT
  have hT' : subA A B V y ⊓ subB A B V x = yGrp A B V ⊔ conjClosure V B := by
    apply le_antisymm
    · rintro u ⟨huA', huB'⟩
      have hu : u ∈ ((yGrp A B V ⊔ Subgroup.zpowers y) ⊔ conjClosure V B) ⊓ (A ⊓ B) :=
        ⟨huA', dA.H'_le_H huA', dB.H'_le_H huB'⟩
      rw [dA.H'_inf_T] at hu
      exact hu
    · refine le_inf dA.T'_le_H' ?_
      rw [sup_comm]
      exact dB.T'_le_H'
  refine ⟨subA A B V y, subB A B V x, dA.H'_le_H, dB.H'_le_H, dA.relIndex_H', dB.relIndex_H',
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hT']
    exact dA.vertex_H'
  · rw [hT', sup_comm]
    exact dB.vertex_H'
  · have hpc : pCoreOf 2 (subA A B V y) = yGrp A B V := dA.pCoreOf_H'
    obtain ⟨e⟩ := nonempty_yGrp_mulEquiv g hT
    rw [hpc]
    exact ⟨e⟩
  · have hpc : pCoreOf 2 (subB A B V x) = conjClosure V B := dB.pCoreOf_H'
    rw [hpc]
    exact isCentralProduct₂_conjClosure_c g
  · exact isSpecialTwoOnePlusFour_pCoreOf_right g hT

end GoldAmL2T

end F6

end CFSG.Quasithin
