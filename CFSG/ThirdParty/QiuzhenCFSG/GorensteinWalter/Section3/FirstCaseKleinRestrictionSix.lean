module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionFive
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinCosetInvolution
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The quotient bound behind restriction (6)

For an outside involution `y`, put `D = Ĥ ∩ Ĥ^y` and
`N = D ∩ (VU)`.  The source's Fact 1.4 identifies collisions of inverted
elements modulo `N` with an inverted element of `VU`; restriction (5) then
forces the collision to be trivial.  Thus `I_Ĥ(y)` injects into `D/N`.
-/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-- The normal `VU` subgroup of `Ĥ` in the Klein-four branch. -/
public theorem firstCase_klein_VU_normal_in_Hhat
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) :
    IsNormalIn (twoCoreOf c.Hhat ⊔ c.U) c.Hhat := by
  let A : Subgroup G := c.Hhat
  let B : Subgroup G := twoCoreOf c.Hhat ⊔ c.U
  let B0 : Subgroup (↥A) := pCore 2 A ⊔ pPrimeCore 2 A
  have h26 := theorem_2_6 hmin c
  have hUeq : c.U = oddCoreOf c.Hhat := h26.1
  have hBmap : B0.map A.subtype = B := by
    dsimp [A, B, B0]
    rw [Subgroup.map_sup]
    simp [twoCoreOf, oddCoreOf, hUeq]
  have hBleA : B ≤ A := by
    dsimp [A, B]
    apply sup_le
    · exact Subgroup.map_subtype_le (pCore 2 c.Hhat)
    · rw [hUeq]
      exact Subgroup.map_subtype_le (pPrimeCore 2 c.Hhat)
  have hB0norm : B0.Normal := by
    dsimp [B0]
    infer_instance
  refine ⟨hBleA, ?_⟩
  intro a ha b hb
  have hbmap : b ∈ B0.map A.subtype := by
    rw [hBmap]
    exact hb
  rcases Subgroup.mem_map.mp hbmap with ⟨z, hz, hzb⟩
  have hzval : (z : G) = b := by simpa using hzb
  have hconj0 := hB0norm.conj_mem z hz ⟨a, ha⟩
  change a * b * a⁻¹ ∈ B
  rw [← hBmap]
  exact Subgroup.mem_map.mpr
    ⟨⟨a, ha⟩ * z * (⟨a, ha⟩ : ↥A)⁻¹, hconj0, by
      change a * (z : G) * a⁻¹ = a * b * a⁻¹
      rw [hzval]⟩

/-- The source inequality `|I_Ĥ(y)| ≤ |D : D ∩ VU|`, where
`D = Ĥ ∩ Ĥ^y`.  The `let`-bound form keeps the public statement independent
of a quotient-normality instance; the proof constructs that instance locally.
-/
public theorem firstCase_klein_restrictionSix_index_bound
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {y : G} (hy : IsInvolution y) (hyH : y ∉ c.Hhat) :
    Nat.card {x : G // x ∈ invertedElements c.Hhat y} ≤
      let D := c.Hhat ⊓ conjugateSubgroup c.Hhat y
      let N := D ⊓ (twoCoreOf c.Hhat ⊔ c.U)
      N.subgroupOf D |>.index := by
  classical
  let A : Subgroup G := c.Hhat
  let B : Subgroup G := twoCoreOf c.Hhat ⊔ c.U
  let D : Subgroup G := A ⊓ conjugateSubgroup A y
  let N : Subgroup G := D ⊓ B
  have h26 := theorem_2_6 hmin c
  have hUeq : c.U = oddCoreOf c.Hhat := h26.1
  have hBmap :
      (pCore 2 A ⊔ pPrimeCore 2 A).map A.subtype = B := by
    dsimp [A, B]
    rw [Subgroup.map_sup]
    simp [twoCoreOf, oddCoreOf, hUeq]
  have hBleA : B ≤ A := by
    dsimp [A, B]
    apply sup_le
    · exact Subgroup.map_subtype_le (pCore 2 c.Hhat)
    · rw [hUeq]
      exact Subgroup.map_subtype_le (pPrimeCore 2 c.Hhat)
  have hBnorm : IsNormalIn B A := by
    have hB0norm : (pCore 2 A ⊔ pPrimeCore 2 A).Normal := by infer_instance
    refine ⟨hBleA, ?_⟩
    intro a ha b hb
    have hbmap : b ∈ (pCore 2 A ⊔ pPrimeCore 2 A).map A.subtype := by
      rw [hBmap]
      exact hb
    rcases Subgroup.mem_map.mp hbmap with ⟨z, hz, hzb⟩
    have hzval : (z : G) = b := by simpa using hzb
    have hzeq : z = (⟨b, hBleA hb⟩ : ↥A) := by
      apply Subtype.ext
      exact hzval
    have hconj0 := hB0norm.conj_mem z hz ⟨a, ha⟩
    have hm : a * b * a⁻¹ ∈ B := by
      rw [← hBmap]
      exact Subgroup.mem_map.mpr
        ⟨⟨a, ha⟩ * z * (⟨a, ha⟩ : ↥A)⁻¹, hconj0, by
          change a * (z : G) * a⁻¹ = a * b * a⁻¹
          rw [hzval]⟩
    exact hm
  have hNnormD : D ≤ Subgroup.normalizer (N : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro d hd n hn
    have hdA : d ∈ A := (show D ≤ A from inf_le_left) hd
    have hnb : n ∈ B := (show N ≤ B from inf_le_right) hn
    have hconjB : d * n * d⁻¹ ∈ B := hBnorm.2 d hdA n hnb
    have hconjD : d * n * d⁻¹ ∈ D := by
      have hconjD0 : d * n * d⁻¹ ∈ D :=
        D.mul_mem (D.mul_mem hd ((show N ≤ D from inf_le_left) hn)) (D.inv_mem hd)
      exact ⟨(inf_le_left : D ≤ A) hconjD0,
        (inf_le_right : D ≤ conjugateSubgroup A y) hconjD0⟩
    exact ⟨hconjD, hconjB⟩
  let Nsub : Subgroup (↥D) := N.subgroupOf D
  let : Nsub.Normal := by
    dsimp [Nsub]
    exact Subgroup.normal_subgroupOf_of_le_normalizer hNnormD
  let q : D →* (D ⧸ Nsub) := QuotientGroup.mk' Nsub
  let f : {x : G // x ∈ invertedElements A y} → (D ⧸ Nsub) := fun x =>
    q ⟨x.1, by
      have hxA : x.1 ∈ A := x.2.1
      have hxconj : x.1 ∈ conjugateSubgroup A y := by
        change x.1 ∈ A.map (MulAut.conj y).toMonoidHom
        exact Subgroup.mem_map.mpr ⟨x.1⁻¹, A.inv_mem hxA, by
          change y * x.1⁻¹ * y⁻¹ = x.1
          calc
            y * x.1⁻¹ * y⁻¹ = (y * x.1 * y⁻¹)⁻¹ := by group
            _ = (x.1⁻¹)⁻¹ := by rw [x.2.2]
            _ = x.1 := by simp⟩
      exact ⟨hxA, hxconj⟩⟩
  have hf_inj : Function.Injective f := by
    intro x z hq
    apply Subtype.ext
    by_contra hne
    have hxD : x.1 ∈ D := by
      have hxA : x.1 ∈ A := x.2.1
      have hxconj : x.1 ∈ conjugateSubgroup A y := by
        change x.1 ∈ A.map (MulAut.conj y).toMonoidHom
        exact Subgroup.mem_map.mpr ⟨x.1⁻¹, A.inv_mem hxA, by
          change y * x.1⁻¹ * y⁻¹ = x.1
          calc
            y * x.1⁻¹ * y⁻¹ = (y * x.1 * y⁻¹)⁻¹ := by group
            _ = (x.1⁻¹)⁻¹ := by rw [x.2.2]
            _ = x.1 := by simp⟩
      exact ⟨hxA, hxconj⟩
    have hzD : z.1 ∈ D := by
      have hzA : z.1 ∈ A := z.2.1
      have hzconj : z.1 ∈ conjugateSubgroup A y := by
        change z.1 ∈ A.map (MulAut.conj y).toMonoidHom
        exact Subgroup.mem_map.mpr ⟨z.1⁻¹, A.inv_mem hzA, by
          change y * z.1⁻¹ * y⁻¹ = z.1
          calc
            y * z.1⁻¹ * y⁻¹ = (y * z.1 * y⁻¹)⁻¹ := by group
            _ = (z.1⁻¹)⁻¹ := by rw [z.2.2]
            _ = z.1 := by simp⟩
      exact ⟨hzA, hzconj⟩
    let xD : D := ⟨x.1, hxD⟩
    let zD : D := ⟨z.1, hzD⟩
    have hqone : q (xD * zD⁻¹) = 1 := by
      change q xD * (q zD)⁻¹ = 1
      rw [show q xD = f x by rfl, show q zD = f z by rfl, hq]
      simp
    have hmemNsub : xD * zD⁻¹ ∈ Nsub :=
      (QuotientGroup.eq_one_iff (xD * zD⁻¹)).mp hqone
    have hmemN : x.1 * z.1⁻¹ ∈ N := by
      exact hmemNsub
    have hmemB : x.1 * z.1⁻¹ ∈ B := (show N ≤ B from inf_le_right) hmemN
    have hxTop : x.1 ∈ invertedElements (⊤ : Subgroup G) y := by
      exact ⟨by simp, x.2.2⟩
    have hzTop : z.1 ∈ invertedElements (⊤ : Subgroup G) y := by
      exact ⟨by simp, z.2.2⟩
    have hInvProd := fact_1_4_inverted_mul_inv hy hxTop hzTop
    have hzyI : IsInvolution (z.1 * y) := by
      rw [fact_1_4_involution_mul hy]
      refine ⟨?_, ?_⟩
      · intro h
        apply hyH
        simpa [h] using z.2.1
      · have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right
          (by simpa [pow_two] using hy.2)
        simpa [invertedElements, hyinv] using z.2.2
    have hzyH : z.1 * y ∉ c.Hhat := by
      intro hmem
      apply hyH
      have hyEq : y = z.1⁻¹ * (z.1 * y) := by group
      rw [hyEq]
      exact c.Hhat.mul_mem (c.Hhat.inv_mem z.2.1) hmem
    have h5 := firstCase_klein_restrictionFive hmin c hfirst hklein
      (z.1 * y) hzyI hzyH
    have hone : (1 : G) ∈ invertedElements B (z.1 * y) := by
      exact ⟨B.one_mem, by simp⟩
    have hcarduniq := (Nat.card_eq_one_iff_exists).mp h5
    rcases hcarduniq with ⟨a0, ha0⟩
    have hprodsub : (⟨x.1 * z.1⁻¹, ⟨hmemB, hInvProd.2⟩⟩ :
        {w : G // w ∈ invertedElements B (z.1 * y)}) =
        (⟨1, hone⟩ : {w : G // w ∈ invertedElements B (z.1 * y)}) := by
      exact (ha0 _).trans (ha0 _).symm
    have hprod1 : x.1 * z.1⁻¹ = 1 := congrArg Subtype.val hprodsub
    exact hne (by
      calc
        x.1 = (x.1 * z.1⁻¹) * z.1 := by group
        _ = z.1 := by rw [hprod1]; simp)
  have hle : Nat.card {x : G // x ∈ invertedElements A y} ≤
      Nat.card (D ⧸ Nsub) := Nat.card_le_card_of_injective f hf_inj
  simpa [A, B, D, N, Nsub, Subgroup.index_eq_card] using hle

end CFSG.GorensteinWalter
