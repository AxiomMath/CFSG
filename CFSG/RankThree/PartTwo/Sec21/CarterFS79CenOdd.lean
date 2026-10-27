module

public import CFSG.RankThree.PartTwo.Sec21.CarterFS79Structure
public import CFSG.GroupTheory.ABGLocalTools.Basic

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79

variable {H : Type} [Group H] [Finite H]
variable {b t b₁ b₂ : H} {J : Subgroup H}

theorem FS79Hyp.odd_cenS_B (h : FS79Hyp b t b₁ b₂ J) :
    Odd (Nat.card (CenS (Subgroup.closure ({b, b₁, b₂} : Set H)))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B : Subgroup H := Subgroup.closure ({b, b₁, b₂} : Set H) with hB
  set C : Subgroup H := CenS B with hC
  by_contra hodd
  have hEven : Even (Nat.card C) := Nat.not_odd_iff_even.mp hodd
  have h2dvd : 2 ∣ Nat.card C := even_iff_two_dvd.mp hEven
  obtain ⟨R, hRsyl⟩ := CFSG.ABGLocalTools.exists_isSylowOf (p := 2) (K := C)
  have hR2 : IsPGroup 2 R := CFSG.ABGLocalTools.IsSylowOf.isPGroup hRsyl
  have hRle : R ≤ C := CFSG.ABGLocalTools.IsSylowOf.le hRsyl
  have hndvd : ¬ 2 ∣ R.relIndex C := (CFSG.ABGLocalTools.isSylowOf_iff.mp hRsyl).2.2
  have hBcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    have hE := h.isElemAb_B
    rw [← hB] at hE
    exact fun x hx y hy =>
      congrArg Subtype.val (hE.1.toIsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hBleC : B ≤ C := by
    rw [hC]
    intro x hx
    rw [CenS, Subgroup.mem_centralizer_iff]
    intro y hy
    exact hBcomm y hy x hx
  have hBcenR : B ≤ Subgroup.centralizer (R : Set H) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hrC : r ∈ C := hRle hr
    rw [hC, CenS] at hrC
    exact (Subgroup.mem_centralizer_iff.mp hrC x hx).symm
  have hBN : B ≤ Nor R := by
    intro x hx
    exact Subgroup.centralizer_le_normalizer (R : Set H) (hBcenR hx)
  have hRbot : R = ⊥ := h.no_two R hR2 (by simpa only [hB] using hBN)
  exact hndvd (by rw [hRbot, Subgroup.relIndex_bot_left]; exact h2dvd)

end CFSG.RankThree.PartTwo.Sec21.FF81
