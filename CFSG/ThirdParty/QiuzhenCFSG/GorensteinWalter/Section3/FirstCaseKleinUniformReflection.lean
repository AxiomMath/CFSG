module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinReflectionExists
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Uniformity across the reflections outside `O₂(Ĥ)`
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

public theorem firstCase_klein_uniform_reflection_inverted
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    (r : G) (hr : c.IsReflection r)
    (hrV : r ∉ twoCoreOf c.Hhat) :
    ∃ K : Subgroup G,
      IsInvertedSubgroup K c.U r ∧ IsHallIn K c.FU ∧ K ≠ ⊥ ∧
        ∀ s : G, c.IsReflection s → s ∉ twoCoreOf c.Hhat →
          IsInvertedSubgroup K c.U s := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hKr, hKHall, hKne⟩ :=
    firstCase_klein_reflection_hall_nontrivial hmin c hfirst r hr hrV
  have h26 := theorem_2_6 hmin c
  have hS8 : Nat.card (c.S : Subgroup G) = 8 :=
    firstCase_klein_S_card hmin c hfirst hklein
  have hVleS : twoCoreOf c.Hhat ≤ (c.S : Subgroup G) := by
    rw [← h26.2.1]
    exact inf_le_left
  have hVcard : Nat.card (twoCoreOf c.Hhat) = 4 := by
    simpa using (firstCase_klein_V_klein c hklein).card_four
  have hVsubcard :
      Nat.card ((twoCoreOf c.Hhat).subgroupOf (c.S : Subgroup G)) =
        Nat.card (twoCoreOf c.Hhat) := by
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVleS).toEquiv
  have hVindex :
      ((twoCoreOf c.Hhat).subgroupOf (c.S : Subgroup G)).index = 2 := by
    have hmul :=
      ((twoCoreOf c.Hhat).subgroupOf (c.S : Subgroup G)).index_mul_card
    change ((twoCoreOf c.Hhat).subgroupOf (c.S : Subgroup G)).index *
        Nat.card ((twoCoreOf c.Hhat).subgroupOf (c.S : Subgroup G)) =
      Nat.card (c.S : Subgroup G) at hmul
    rw [hVsubcard, hVcard, hS8] at hmul
    omega
  have hrS : r ∈ (c.S : Subgroup G) := hr.1
  have hrInv : r⁻¹ = r := by
    exact inv_eq_of_mul_eq_one_right (by
      simpa [pow_two] using (centralizerSetup_reflection_isInvolution c hr).2)
  have hr2 : r * r = 1 := by
    simpa [pow_two] using (centralizerSetup_reflection_isInvolution c hr).2
  have hsInv_reflection : ∀ s : G, c.IsReflection s → s⁻¹ = s := by
    intro s hs
    exact inv_eq_of_mul_eq_one_right (by
      simpa [pow_two] using (centralizerSetup_reflection_isInvolution c hs).2)
  refine ⟨K, hKr, hKHall, hKne, ?_⟩
  intro s hs hsV
  have hs2 : s * s = 1 := by
    simpa [pow_two] using (centralizerSetup_reflection_isInvolution c hs).2
  have hsS : s ∈ (c.S : Subgroup G) := hs.1
  have hpV : r * s ∈ twoCoreOf c.Hhat := by
    have hiff := Subgroup.mul_mem_iff_of_index_two hVindex
      (a := (⟨r, hrS⟩ : c.S)) (b := (⟨s, hsS⟩ : c.S))
    have hrnot : (⟨r, hrS⟩ : c.S) ∉
        (twoCoreOf c.Hhat).subgroupOf (c.S : Subgroup G) := hrV
    have hsnot : (⟨s, hsS⟩ : c.S) ∉
        (twoCoreOf c.Hhat).subgroupOf (c.S : Subgroup G) := hsV
    have hprod : (⟨r * s, (c.S : Subgroup G).mul_mem hrS hsS⟩ : c.S) ∈
        (twoCoreOf c.Hhat).subgroupOf (c.S : Subgroup G) := by
      apply hiff.mpr
      exact iff_of_false hrnot hsnot
    exact hprod
  have hpS : r * s ∈ (c.S : Subgroup G) :=
    (c.S : Subgroup G).mul_mem hrS hsS
  have hpInf : r * s ∈
      (c.S : Subgroup G) ⊓ Subgroup.centralizer (c.U : Set G) := by
    rw [h26.2.1]
    exact hpV
  have hpFix : ∀ x : G, x ∈ c.U → (r * s) * x * (r * s)⁻¹ = x := by
    intro x hx
    have hcomm := (Subgroup.mem_centralizer_iff.mp hpInf.2 x hx)
    have hInvRS : (r * s)⁻¹ = s * r := by
      rw [mul_inv_rev, hrInv, hsInv_reflection s hs]
    rw [← hcomm]
    rw [hInvRS]
    calc
      x * (r * s) * (s * r) = x * (r * (s * s) * r) := by group
      _ = x := by simp [hs2, hr2]
  have hsEq : s = r * (r * s) := by
    calc
      s = (r * r) * s := by rw [show r * r = 1 by simpa [pow_two] using
        (centralizerSetup_reflection_isInvolution c hr).2]; simp
      _ = r * (r * s) := by group
  have hrInverted : (K : Set G) = invertedElements c.U r := by
    exact hKr
  have hset : invertedElements c.U r = invertedElements c.U s := by
    ext x
    constructor
    · intro hx
      refine ⟨hx.1, ?_⟩
      rw [hsEq]
      calc
        (r * (r * s)) * x * (r * (r * s))⁻¹ =
            r * ((r * s) * x * (r * s)⁻¹) * r⁻¹ := by group
        _ = r * x * r⁻¹ := by rw [hpFix x hx.1]
        _ = x⁻¹ := hx.2
    · intro hx
      refine ⟨hx.1, ?_⟩
      have hpInvFix : ∀ x : G, x ∈ c.U →
          (r * s)⁻¹ * x * ((r * s)⁻¹)⁻¹ = x := by
        intro y hy
        have hpinv : (r * s)⁻¹ ∈
            Subgroup.centralizer (c.U : Set G) :=
          (Subgroup.centralizer (c.U : Set G)).inv_mem hpInf.2
        have hcomm := (Subgroup.mem_centralizer_iff.mp hpinv y hy)
        have hInvRS : (r * s)⁻¹ = s * r := by
          rw [mul_inv_rev, hrInv, hsInv_reflection s hs]
        rw [← hcomm]
        rw [inv_inv]
        rw [hInvRS]
        calc
          y * (s * r) * (r * s) = y * ((s * r) * (r * s)) := by group
          _ = y * (s * (r * r) * s) := by group
          _ = y := by simp [hr2, hs2]
      have hrEq' : r = s * (r * s)⁻¹ := by
        have hsInv : s⁻¹ = s := by
          exact inv_eq_of_mul_eq_one_right (by
            simpa [pow_two] using (centralizerSetup_reflection_isInvolution c hs).2)
        have hs2 : s * s = 1 := by
          simpa [pow_two] using (centralizerSetup_reflection_isInvolution c hs).2
        calc
          r = (s * s) * r := by rw [hs2]; simp
          _ = s * (s * r) := by group
          _ = s * (r * s)⁻¹ := by rw [mul_inv_rev, hrInv, hsInv]
      calc
        r * x * r⁻¹ =
            (s * (r * s)⁻¹) * x * (s * (r * s)⁻¹)⁻¹ :=
              congrArg (fun z : G => z * x * z⁻¹) hrEq'
        _ =
            s * ((r * s)⁻¹ * x * ((r * s)⁻¹)⁻¹) * s⁻¹ := by group
        _ = s * x * s⁻¹ := by rw [hpInvFix x hx.1]
        _ = x⁻¹ := hx.2
  change (K : Set G) = invertedElements c.U s
  rw [hrInverted, hset]

end CFSG.GorensteinWalter
