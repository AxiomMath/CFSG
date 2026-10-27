module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSix
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinDataComplete
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Basic
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The order-six intersection in restriction (6)

For an outside involution `y`, let `D = Ĥ ∩ Ĥ^y` and `N = D ∩ VU`.
The quotient injection from restriction (5) bounds `|I_Ĥ(y)|` by
`[D : N]`.  Since `VU` is normal in `Ĥ` and `Ĥ/VU ≃ D₆`, the latter index
divides six.  Thus the source hypothesis `|I_Ĥ(y)| ≥ 4` forces `[D : N] = 6`.
-/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-- In source restriction (6), the intersection `D/(D ∩ VU)` has order six
whenever the outside involution inverts at least four elements of `Ĥ`. -/
public theorem firstCase_klein_restrictionSix_index_eq
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {y : G} (hy : IsInvolution y) (hyH : y ∉ c.Hhat)
    (hn : 4 ≤ Nat.card {x : G // x ∈ invertedElements c.Hhat y}) :
    let D := c.Hhat ⊓ conjugateSubgroup c.Hhat y
    let N := D ⊓ (twoCoreOf c.Hhat ⊔ c.U)
    N.subgroupOf D |>.index = 6 := by
  classical
  let A : Subgroup G := c.Hhat
  let B : Subgroup G := twoCoreOf c.Hhat ⊔ c.U
  let D : Subgroup G := A ⊓ conjugateSubgroup A y
  let N : Subgroup G := D ⊓ B
  let B0 : Subgroup (↥A) := B.subgroupOf A
  have h26 := theorem_2_6 hmin c
  have hUeq : c.U = oddCoreOf c.Hhat := h26.1
  have hBleA : B ≤ A := by
    dsimp [A, B]
    apply sup_le
    · exact Subgroup.map_subtype_le (pCore 2 c.Hhat)
    · rw [hUeq]
      exact Subgroup.map_subtype_le (pPrimeCore 2 c.Hhat)
  have hBnorm : IsNormalIn B A :=
    firstCase_klein_VU_normal_in_Hhat hmin c
  have hB0norm : B0.Normal := by
    apply (Subgroup.normal_subgroupOf_iff hBleA).2
    intro a ha b hb
    exact hBnorm.2 ha hb a b
  let Bjoin : Subgroup (↥A) := pCore 2 A ⊔ pPrimeCore 2 A
  have hBjoinmap : Bjoin.map A.subtype = B := by
    dsimp [A, B, Bjoin]
    rw [Subgroup.map_sup]
    simp [twoCoreOf, oddCoreOf, hUeq]
  have hBjoin0 : Bjoin = B0 := by
    ext z
    constructor
    · intro hz
      apply (Subgroup.mem_subgroupOf).2
      rw [← hBjoinmap]
      exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
    · intro hz
      have hzB : (z : G) ∈ B := (Subgroup.mem_subgroupOf).1 hz
      rw [← hBjoinmap] at hzB
      rcases Subgroup.mem_map.mp hzB with ⟨w, hw, hwz⟩
      have hweq : w = z := by
        apply Subtype.ext
        simpa using hwz
      simpa [hweq] using hw
  have hqcard : Nat.card (A ⧸ B0) = 6 := by
    have hq := firstCase_klein_quotient_d6 hmin c hfirst hklein
    rcases hq with ⟨e⟩
    calc
      Nat.card (A ⧸ B0) = Nat.card (A ⧸ Bjoin) := by rw [hBjoin0]
      _ = Nat.card (DihedralGroup 3) := by
        simpa [A, Bjoin] using Nat.card_congr e.toEquiv
      _ = 6 := by rw [DihedralGroup.nat_card]
  let D0 : Subgroup (↥A) := D.subgroupOf A
  let fD : D0 →* (A ⧸ B0) := (QuotientGroup.mk' B0).comp D0.subtype
  let Q : Subgroup (A ⧸ B0) := fD.range
  have hker : fD.ker = B0.subgroupOf D0 := by
    ext z
    simpa [fD, Subgroup.mem_subgroupOf] using
      (QuotientGroup.eq_one_iff (N := B0) (D0.subtype z))
  have hidxQ : (B0.subgroupOf D0).index = Nat.card Q := by
    rw [← hker]
    simpa [Q] using Subgroup.index_ker fD
  have hQdvd : Nat.card Q ∣ Nat.card (A ⧸ B0) := Q.card_subgroup_dvd_card
  have hindexdvd0 : (B0.subgroupOf D0).index ∣ 6 := by
    have hQdvd' : Nat.card Q ∣ 6 := by simpa [hqcard] using hQdvd
    exact hidxQ ▸ hQdvd'
  have hNsubeq : B.subgroupOf D = N.subgroupOf D := by
    ext z
    change (z : G) ∈ B ↔ (z : G) ∈ D ∧ (z : G) ∈ B
    simp
  have hrel : (B0.subgroupOf D0).index = (N.subgroupOf D).index := by
    change (B.subgroupOf A).relIndex (D.subgroupOf A) = (N.subgroupOf D).index
    calc
      (B.subgroupOf A).relIndex (D.subgroupOf A) = B.relIndex D :=
        Subgroup.relIndex_subgroupOf (H := B) (K := D) (L := A)
          (by dsimp [D, A]; exact inf_le_left)
      _ = (N.subgroupOf D).index := by
        simpa [Subgroup.relIndex, hNsubeq]
  have hbound := firstCase_klein_restrictionSix_index_bound
    hmin c hfirst hklein hy hyH
  have hge : 4 ≤ (N.subgroupOf D).index := by
    have hbound' : Nat.card {x : G // x ∈ invertedElements A y} ≤
        (N.subgroupOf D).index := by
      simpa [A, B, D, N] using hbound
    exact le_trans hn hbound'
  have hdiv : (N.subgroupOf D).index ∣ 6 := by
    rw [← hrel]
    exact hindexdvd0
  have hidx : (N.subgroupOf D).index = 6 := by
    change 4 ≤ (N.subgroupOf D).index at hge
    change (N.subgroupOf D).index ∣ 6 at hdiv
    let i : ℕ := (N.subgroupOf D).index
    have hgei : 4 ≤ i := hge
    have hdivi : i ∣ 6 := hdiv
    have hlei : i ≤ 6 := Nat.le_of_dvd (by norm_num) hdivi
    have hi : i = 6 := by
      interval_cases i <;> simp_all
    exact hi
  simpa [A, B, D, N] using hidx

end CFSG.GorensteinWalter
