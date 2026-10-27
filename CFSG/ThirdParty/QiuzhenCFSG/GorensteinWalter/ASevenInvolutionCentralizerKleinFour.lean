module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenStructureFacts
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvolutionCentralizerOddPart
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourCentralizerTransport
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Klein four subgroups centralizing the three-part of an A7 involution centralizer
-/

noncomputable section

namespace CFSG.GorensteinWalter

/-- Every order-three subgroup in the centralizer of an involution of `A7`
is centralized by a Klein four subgroup that also centralizes the
involution. -/
public theorem
    aSeven_exists_kleinFour_centralizing_card_three_of_centralizes_involution
    (t : A7) (ht : IsInvolution t)
    (U : Subgroup A7) (hUcard : Nat.card U = 3)
    (hUcent : U ≤ Subgroup.centralizer ({t} : Set A7)) :
    ∃ V : Subgroup A7, IsKleinFour V ∧
      V ≤ Subgroup.centralizer (U : Set A7) ∧
      V ≤ Subgroup.centralizer ({t} : Set A7) := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hgt⟩ := aSeven_involutions_conjugate t a7t ht
    (by constructor <;> decide)
  let e : A7 ≃* A7 := MulAut.conj g
  let U0 : Subgroup A7 := U.map e.toMonoidHom
  have hU0card : Nat.card U0 = 3 := by
    rw [Subgroup.card_map_of_injective e.injective, hUcard]
  have hU0cent : U0 ≤ Subgroup.centralizer ({a7t} : Set A7) := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxcomm := Subgroup.mem_centralizer_singleton_iff.mp (hUcent hx)
    change (g * x * g⁻¹) * a7t = a7t * (g * x * g⁻¹)
    rw [← hgt]
    calc
      (g * x * g⁻¹) * (g * t * g⁻¹) = g * (x * t) * g⁻¹ := by group
      _ = g * (t * x) * g⁻¹ := by rw [hxcomm]
      _ = (g * t * g⁻¹) * (g * x * g⁻¹) := by group
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
  have hU0p : IsPGroup 3 U0 := by
    apply IsPGroup.of_card (n := 1)
    simpa [Nat.card_eq_fintype_card] using hU0card
  have hUp : IsPGroup 3 a7U := by
    apply IsPGroup.of_card (n := 1)
    simpa [Nat.card_eq_fintype_card] using hfact.1
  have hU0normU : U0 ≤ Subgroup.normalizer (a7U : Set A7) := by
    intro u hu
    have huC : u ∈ C := hU0cent hu
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
  have hsupP : IsPGroup 3 (a7U ⊔ U0 : Subgroup A7) :=
    IsPGroup.to_sup_of_normal_left' hUp hU0p hU0normU
  have hsupOdd : Odd (Nat.card (a7U ⊔ U0 : Subgroup A7)) := by
    rcases hsupP.exists_card_eq with ⟨n, hn⟩
    rw [hn]
    exact Odd.pow (by decide)
  have hsupCent : a7U ⊔ U0 ≤
      Subgroup.centralizer ({a7t} : Set A7) := sup_le hUleC hU0cent
  have hsupCardLe : Nat.card (a7U ⊔ U0 : Subgroup A7) ≤ 3 :=
    aSeven_odd_subgroup_centralizing_involution_card_le_three
      hsupOdd (by constructor <;> decide) hsupCent
  have hsupEq : a7U = a7U ⊔ U0 := by
    apply Subgroup.eq_of_le_of_card_ge le_sup_left
    rw [hfact.1]
    exact hsupCardLe
  have hU0le : U0 ≤ a7U := by
    rw [hsupEq]
    exact le_sup_right
  have hU0eq : U0 = a7U := by
    apply Subgroup.eq_of_le_of_card_ge hU0le
    rw [hU0card, hfact.1]
  have hVcentU : a7V ≤ Subgroup.centralizer (a7U : Set A7) := by
    intro v hv
    change v = 1 ∨ v = a7t ∨ v = a7u ∨ v = a7t * a7u at hv
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    change x = 1 ∨ x = a7a ∨ x = a7a ^ 2 at hx
    rcases hv with rfl | rfl | rfl | rfl <;>
      rcases hx with rfl | rfl | rfl <;> decide
  have hVcentA7t : a7V ≤ Subgroup.centralizer ({a7t} : Set A7) := by
    intro v hv
    change v = 1 ∨ v = a7t ∨ v = a7u ∨ v = a7t * a7u at hv
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases hv with rfl | rfl | rfl | rfl <;> decide
  let V : Subgroup A7 := a7V.map e.symm.toMonoidHom
  have hVK : IsKleinFour V :=
    isKleinFour_map_mulEquiv_cross a7V hfact.2.2.2 e.symm
  have hVcent := centralizer_map_le_of_mulEquiv e.symm a7U a7V hVcentU
  have hUback : a7U.map e.symm.toMonoidHom = U := by
    rw [← hU0eq]
    change (U.map e.toMonoidHom).map e.symm.toMonoidHom = U
    rw [Subgroup.map_map]
    have hid : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id A7 := by
      apply MonoidHom.ext
      intro x
      exact e.symm_apply_apply x
    rw [hid, Subgroup.map_id]
  rw [hUback] at hVcent
  have hVcentT : V ≤ Subgroup.centralizer ({t} : Set A7) := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨v, hv, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hvcomm :=
      Subgroup.mem_centralizer_singleton_iff.mp (hVcentA7t hv)
    apply e.injective
    rw [e.map_mul, e.map_mul]
    change e (e.symm v) * e t = e t * e (e.symm v)
    rw [e.apply_symm_apply]
    have het : e t = a7t := by
      change g * t * g⁻¹ = a7t
      exact hgt
    rw [het]
    exact hvcomm
  exact ⟨V, hVK, hVcent, hVcentT⟩

end CFSG.GorensteinWalter
