module

public import CFSG.Monster.B.Gen.Max2AssemblyBase
public import CFSG.Monster.B.Gen.Generation


public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.VisQuot

theorem Jbar_le_of_max2
    (G : Subgroup Cbar) {a b : Cbar} (haG : a ∈ G) (hbG : b ∈ G)
    (haJ : a ∈ Jbar) (hbJ : b ∈ Jbar) (e : Fin 22 → Cbar) (he : ∀ i, e i ∈ Ebar)
    (hind : LinearIndependent (ZMod 2) fun i => Multiplicative.toAdd (psiBar ⟨e i, he i⟩))
    (hR1 : ∀ i, psiBar ⟨a⁻¹ * e i * a, conj_mem_Ebar haJ (he i)⟩ =
      Multiplicative.ofAdd (∑ j, ((Max2.R1u : GL (Fin 22) (ZMod 2)) : Matrix (Fin 22) (Fin 22) (ZMod 2)) i j •
        Multiplicative.toAdd (psiBar ⟨e j, he j⟩)))
    (hR2 : ∀ i, psiBar ⟨b⁻¹ * e i * b, conj_mem_Ebar hbJ (he i)⟩ =
      Multiplicative.ofAdd (∑ j, ((Max2.R2u : GL (Fin 22) (ZMod 2)) : Matrix (Fin 22) (Fin 22) (ZMod 2)) i j •
        Multiplicative.toAdd (psiBar ⟨e j, he j⟩)))
    (w : List (Bool × Bool)) (hw : wordIn Max2.R1u Max2.R2u w = 1) (hw1 : wordIn a b w ≠ 1)
    (hwx : wordIn a b w ≠ xbar) : Jbar ≤ G := by
  refine Jbar_le_of_generates G (jbarToKv_onto_of_max2 G haG hbG haJ hbJ e he hind hR1 hR2) ?_
  have hwE := wordIn_mem_Ebar haJ hbJ e he hind hR1 hR2 w hw
  refine ⟨⟨wordIn a b w, hwE⟩, wordIn_mem G haG hbG w, fun h1 => ?_⟩
  rcases (psiBar_eq_one_iff _).1 h1 with h | h
  · exact hw1 (congrArg Subtype.val h)
  · exact hwx (congrArg Subtype.val h)

theorem Jbar_le_of_max2_kernelWord
    (G : Subgroup Cbar) {a b : Cbar} (haG : a ∈ G) (hbG : b ∈ G)
    (haJ : a ∈ Jbar) (hbJ : b ∈ Jbar) (e : Fin 22 → Cbar) (he : ∀ i, e i ∈ Ebar)
    (hind : LinearIndependent (ZMod 2) fun i => Multiplicative.toAdd (psiBar ⟨e i, he i⟩))
    (hR1 : ∀ i, psiBar ⟨a⁻¹ * e i * a, conj_mem_Ebar haJ (he i)⟩ =
      Multiplicative.ofAdd (∑ j, ((Max2.R1u : GL (Fin 22) (ZMod 2)) : Matrix (Fin 22) (Fin 22) (ZMod 2)) i j •
        Multiplicative.toAdd (psiBar ⟨e j, he j⟩)))
    (hR2 : ∀ i, psiBar ⟨b⁻¹ * e i * b, conj_mem_Ebar hbJ (he i)⟩ =
      Multiplicative.ofAdd (∑ j, ((Max2.R2u : GL (Fin 22) (ZMod 2)) : Matrix (Fin 22) (Fin 22) (ZMod 2)) i j •
        Multiplicative.toAdd (psiBar ⟨e j, he j⟩)))
    (hw1 : wordIn a b kernelWord ≠ 1) (hwx : wordIn a b kernelWord ≠ xbar) : Jbar ≤ G :=
  Jbar_le_of_max2 G haG hbG haJ hbJ e he hind hR1 hR2 kernelWord wordIn_R_kernelWord hw1 hwx

theorem Jbar_le_of_max2_cert
    (G : Subgroup Cbar) {a b : Cbar} (haG : a ∈ G) (hbG : b ∈ G)
    (haJ : a ∈ Jbar) (hbJ : b ∈ Jbar) (e : Fin 22 → Cbar) (he : ∀ i, e i ∈ Ebar)
    (hG : ∀ i j : Fin 22, i < j → e i * e j = e j * e i * xbar ^ (Max2.decMat gramRows i j).val)
    (hR1 : ∀ i, psiBar ⟨a⁻¹ * e i * a, conj_mem_Ebar haJ (he i)⟩ =
      Multiplicative.ofAdd (∑ j, ((Max2.R1u : GL (Fin 22) (ZMod 2)) :
        Matrix (Fin 22) (Fin 22) (ZMod 2)) i j • Multiplicative.toAdd (psiBar ⟨e j, he j⟩)))
    (hR2 : ∀ i, psiBar ⟨b⁻¹ * e i * b, conj_mem_Ebar hbJ (he i)⟩ =
      Multiplicative.ofAdd (∑ j, ((Max2.R2u : GL (Fin 22) (ZMod 2)) :
        Matrix (Fin 22) (Fin 22) (ZMod 2)) i j • Multiplicative.toAdd (psiBar ⟨e j, he j⟩)))
    (hw1 : wordIn a b kernelWord ≠ 1) (hwx : wordIn a b kernelWord ≠ xbar) : Jbar ≤ G :=
  Jbar_le_of_max2_kernelWord G haG hbG haJ hbJ e he (linearIndependent_psi_of_cert e he hG) hR1 hR2
    hw1 hwx

end CFSG.Monster.B
