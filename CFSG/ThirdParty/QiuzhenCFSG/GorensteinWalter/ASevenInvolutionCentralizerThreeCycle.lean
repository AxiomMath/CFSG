module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvolutionCentralizerOddPart
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenStructureFacts
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The odd part of the concrete involution centralizer in `A₇`

The normal subgroup `a7U = ⟨a7a⟩` is the unique Sylow `3`-subgroup of
`C_A₇(a7t)`.  Consequently every subgroup of that centralizer whose elements
all have odd order lies in `⟨a7a⟩`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

private theorem card_three_subgroup_centralizing_a7t_eq_a7U
    (U : Subgroup A7) (hUcard : Nat.card U = 3)
    (hUcent : U ≤ Subgroup.centralizer ({a7t} : Set A7)) :
    U = a7U := by
  have htS : a7t ∈ a7S := by
    change a7t = 1 ∨ a7t = a7v ∨ a7t = a7v ^ 2 ∨
      a7t = a7v ^ 3 ∨ a7t = a7s ∨ a7t = a7s * a7v ∨
      a7t = a7s * a7v ^ 2 ∨ a7t = a7s * a7v ^ 3
    decide
  have hvS : (a7v : A7) ∈ a7S := by
    change a7v = 1 ∨ a7v = a7v ∨ a7v = a7v ^ 2 ∨
      a7v = a7v ^ 3 ∨ a7v = a7s ∨ a7v = a7s * a7v ∨
      a7v = a7s * a7v ^ 2 ∨ a7v = a7s * a7v ^ 3
    exact Or.inr (Or.inl rfl)
  have hsS : a7s ∈ a7S := by
    change a7s = 1 ∨ a7s = a7v ∨ a7s = a7v ^ 2 ∨
      a7s = a7v ^ 3 ∨ a7s = a7s ∨ a7s = a7s * a7v ∨
      a7s = a7s * a7v ^ 2 ∨ a7s = a7s * a7v ^ 3
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have htCenter : a7t ∈ centerIn (G := A7) (a7S : Subgroup A7) := by
    refine ⟨htS, ?_⟩
    change a7t ∈ Subgroup.centralizer (a7S : Set A7)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    change y = 1 ∨ y = a7v ∨ y = a7v ^ 2 ∨ y = a7v ^ 3 ∨
      y = a7s ∨ y = a7s * a7v ∨ y = a7s * a7v ^ 2 ∨
      y = a7s * a7v ^ 3 at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  have hcenterCases : ∀ x : A7,
      x ∈ centerIn (G := A7) (a7S : Subgroup A7) →
        x = 1 ∨ x = a7t := by
    intro x hx
    have hxS : x ∈ a7S := hx.1
    change x = 1 ∨ x = a7v ∨ x = a7v ^ 2 ∨ x = a7v ^ 3 ∨
      x = a7s ∨ x = a7s * a7v ∨ x = a7s * a7v ^ 2 ∨
      x = a7s * a7v ^ 3 at hxS
    rcases hxS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exfalso
      have h := (Subgroup.mem_centralizer_iff.mp hx.2) a7s hsS
      exact (by decide : a7v * a7s ≠ a7s * a7v) h.symm
    · exact Or.inr (by decide)
    · exfalso
      have h := (Subgroup.mem_centralizer_iff.mp hx.2) a7s hsS
      exact (by decide : a7v ^ 3 * a7s ≠ a7s * a7v ^ 3) h.symm
    · exfalso
      have h := (Subgroup.mem_centralizer_iff.mp hx.2) a7v hvS
      exact (by decide : a7s * a7v ≠ a7v * a7s) h.symm
    · exfalso
      have h := (Subgroup.mem_centralizer_iff.mp hx.2) a7v hvS
      exact (by decide : (a7s * a7v) * a7v ≠
        a7v * (a7s * a7v)) h.symm
    · exfalso
      have h := (Subgroup.mem_centralizer_iff.mp hx.2) a7v hvS
      exact (by decide : (a7s * a7v ^ 2) * a7v ≠
        a7v * (a7s * a7v ^ 2)) h.symm
    · exfalso
      have h := (Subgroup.mem_centralizer_iff.mp hx.2) a7v hvS
      exact (by decide : (a7s * a7v ^ 3) * a7v ≠
        a7v * (a7s * a7v ^ 3)) h.symm
  have hcentEq :
      Subgroup.centralizer
          ((centerIn (G := A7) (a7S : Subgroup A7)) : Set A7) =
        Subgroup.centralizer ({a7t} : Set A7) := by
    ext x
    constructor
    · intro hx
      have hcomm := (Subgroup.mem_centralizer_iff.mp hx) a7t htCenter
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcomm.symm
    · intro hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rcases hcenterCases y hy with rfl | rfl
      · simp
      · exact (Subgroup.mem_centralizer_singleton_iff.mp hx).symm
  have hfact := aSeven_structure_fact_1_8_ii_centralizer
  let C : Subgroup A7 := Subgroup.centralizer ({a7t} : Set A7)
  have hCeq : C = a7US := by
    calc
      C = Subgroup.centralizer
          ((centerIn (G := A7) (a7S : Subgroup A7)) : Set A7) := hcentEq.symm
      _ = a7US := hfact.2.2.1
  have hUleC : a7U ≤ C := by
    intro x hx
    change x = 1 ∨ x = a7a ∨ x = a7a ^ 2 at hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases hx with rfl | rfl | rfl <;> decide
  have hUnormalC : IsNormalIn a7U C := by
    refine ⟨hUleC, ?_⟩
    intro z hz x hx
    have hzUS : z ∈ a7US := by rw [← hCeq]; exact hz
    have hxUS : x ∈ a7US := by
      rw [← hCeq]
      exact hUleC hx
    let zUS : a7US := ⟨z, hzUS⟩
    let xUS : a7US := ⟨x, hxUS⟩
    have hxSub : xUS ∈ a7U.subgroupOf a7US :=
      Subgroup.mem_subgroupOf.mpr hx
    have hconj := hfact.2.1.conj_mem xUS hxSub zUS
    simpa [xUS, zUS] using Subgroup.mem_subgroupOf.mp hconj
  have hUp : IsPGroup 3 a7U := by
    apply IsPGroup.of_card (n := 1)
    simpa [Nat.card_eq_fintype_card] using hfact.1
  have hUthree : IsPGroup 3 U := by
    apply IsPGroup.of_card (n := 1)
    simpa [Nat.card_eq_fintype_card] using hUcard
  have hUnormU : U ≤ Subgroup.normalizer (a7U : Set A7) := by
    intro u hu
    have huC : u ∈ C := hUcent hu
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hUnormalC.2 u huC x
    · intro hx
      have huInvC : u⁻¹ ∈ C := C.inv_mem huC
      have hback := hUnormalC.2 u⁻¹ huInvC (u * x * u⁻¹) hx
      have heq : u⁻¹ * (u * x * u⁻¹) * (u⁻¹)⁻¹ = x := by group
      rw [heq] at hback
      exact hback
  have hsupP : IsPGroup 3 (a7U ⊔ U : Subgroup A7) :=
    IsPGroup.to_sup_of_normal_left' hUp hUthree hUnormU
  have hsupOdd : Odd (Nat.card (a7U ⊔ U : Subgroup A7)) := by
    rcases hsupP.exists_card_eq with ⟨n, hn⟩
    rw [hn]
    exact Odd.pow (by decide)
  have hsupCent : a7U ⊔ U ≤
      Subgroup.centralizer ({a7t} : Set A7) := sup_le hUleC hUcent
  have hsupCardLe : Nat.card (a7U ⊔ U : Subgroup A7) ≤ 3 :=
    aSeven_odd_subgroup_centralizing_involution_card_le_three
      hsupOdd (by constructor <;> decide) hsupCent
  have hUle : U ≤ a7U := by
    have hsupEq : a7U = a7U ⊔ U := by
      apply Subgroup.eq_of_le_of_card_ge le_sup_left
      rw [hfact.1]
      exact hsupCardLe
    rw [hsupEq]
    exact le_sup_right
  apply Subgroup.eq_of_le_of_card_ge hUle
  rw [hUcard, hfact.1]

/-- Every subgroup of `C_A₇(a7t)` whose elements have odd order lies in the
distinguished three-cycle subgroup `⟨a7a⟩`.  The proof uses subgroup
cardinality and normality rather than enumerating all elements of `A₇`. -/
public theorem aSeven_odd_subgroup_centralizing_a7t_le_zpowers
    {X : Subgroup A7}
    (hXodd : ∀ x : A7, x ∈ X → Odd (orderOf x))
    (hXcent : X ≤ Subgroup.centralizer ({a7t} : Set A7)) :
    X ≤ Subgroup.zpowers a7a := by
  intro x hx
  by_cases hxone : x = 1
  · rw [hxone]
    exact Subgroup.one_mem _
  let P : Subgroup A7 := Subgroup.zpowers x
  have hPcent : P ≤ Subgroup.centralizer ({a7t} : Set A7) :=
    Subgroup.zpowers_le.mpr (hXcent hx)
  have hPodd : Odd (Nat.card P) := by
    rw [Nat.card_zpowers]
    exact hXodd x hx
  have hPcardLe : Nat.card P ≤ 3 :=
    aSeven_odd_subgroup_centralizing_involution_card_le_three
      hPodd (by constructor <;> decide) hPcent
  have horderLe : orderOf x ≤ 3 := by
    have hcard : Nat.card P = orderOf x := by
      dsimp [P]
      rw [Nat.card_zpowers]
    rwa [hcard] at hPcardLe
  have horderNeOne : orderOf x ≠ 1 := by
    intro h
    exact hxone (orderOf_eq_one_iff.mp h)
  have horderNeTwo : orderOf x ≠ 2 := by
    intro h
    have hodd := hXodd x hx
    rw [h] at hodd
    norm_num at hodd
  have horder : orderOf x = 3 := by
    have hpos : 0 < orderOf x := orderOf_pos x
    omega
  have hPcard : Nat.card P = 3 := by
    change Nat.card (Subgroup.zpowers x) = 3
    rw [Nat.card_zpowers, horder]
  have hPeq : P = a7U :=
    card_three_subgroup_centralizing_a7t_eq_a7U P hPcard hPcent
  have hxU : x ∈ a7U := by
    rw [← hPeq]
    exact Subgroup.mem_zpowers x
  change x = 1 ∨ x = a7a ∨ x = a7a ^ 2 at hxU
  rcases hxU with h1 | ha | ha2
  · rw [h1]
    exact Subgroup.one_mem _
  · rw [ha]
    exact Subgroup.mem_zpowers a7a
  · rw [ha2]
    exact Subgroup.pow_mem (Subgroup.zpowers a7a)
      (Subgroup.mem_zpowers a7a) 2

end CFSG.GorensteinWalter
