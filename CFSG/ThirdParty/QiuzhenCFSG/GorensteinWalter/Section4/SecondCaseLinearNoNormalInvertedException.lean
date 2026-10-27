module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearS0CentralizesU
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma28
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Excluding the normal inverted-set exception after equation (9)

Once `S0` centralizes `U`, all reflections induce the same automorphism of
`U`.  Thus, if the inverted set for one reflection were a subgroup, the same
subgroup property would hold for every reflection.  Lemma 2.8 would then give
`[S0,U] ≠ 1`, contradicting the centralization.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private lemma reflection_product_mem_S0
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    {r s : G} (hrS : r ∈ (c.S : Subgroup G)) (hr0 : r ∉ c.S0)
    (hsS : s ∈ (c.S : Subgroup G)) (hs0 : s ∉ c.S0) :
    r * s ∈ c.S0 := by
  classical
  let K : Subgroup (c.S : Subgroup G) :=
    c.S0.subgroupOf (c.S : Subgroup G)
  have hmap : K.map (c.S : Subgroup G).subtype = c.S0 := by
    apply Subgroup.map_subgroupOf_eq_of_le c.S0_le_S
  have hcard := Subgroup.card_mul_index K
  have hKcard : Nat.card K = Nat.card c.S0 := by
    have h := Subgroup.card_subtype (c.S : Subgroup G) K
    rw [hmap] at h
    exact h.symm
  have hKindex : K.index = 2 := by
    rw [hKcard, c.S_index_two] at hcard
    exact Nat.mul_right_cancel (Nat.card_pos (α := c.S0))
      (by simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcard)
  have hiff := Subgroup.mul_mem_iff_of_index_two hKindex
    (G := (c.S : Subgroup G)) (H := K)
    (a := (⟨r, hrS⟩ : c.S)) (b := (⟨s, hsS⟩ : c.S))
  have hmem : (⟨r, hrS⟩ : c.S) * ⟨s, hsS⟩ ∈ K := by
    rw [hiff]
    dsimp [K]
    simp [Subgroup.mem_subgroupOf, hr0, hs0]
  exact Subgroup.mem_subgroupOf.mp hmem

/-- If `S0` centralizes `U`, the inverted set in `U` of any reflection cannot
be a subgroup.  In particular, the normal-subgroup exception in equation (8)
cannot occur. -/
public theorem secondCase_linear_no_normal_inverted_exception
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hS0centU : (c.S0 : Subgroup G) ≤
      Subgroup.centralizer (c.U : Set G))
    (s : G) (hsS : s ∈ (c.S : Subgroup G)) (hsS0 : s ∉ c.S0) :
    ¬ ∃ I : Subgroup G,
      IsInvertedSubgroup I c.U s ∧ IsNormalIn I c.Hhat := by
  rintro ⟨I, hI, _hInormal⟩
  have hsR : c.IsReflection s := ⟨hsS, hsS0⟩
  have hsI : IsInvolution s := centralizerSetup_reflection_isInvolution c hsR
  have hinverted : ∀ r : G, c.IsReflection r →
      ∃ J : Subgroup G, IsInvertedSubgroup J c.U r := by
    intro r hr
    refine ⟨I, ?_⟩
    have hrI : IsInvolution r := centralizerSetup_reflection_isInvolution c hr
    have hrsS0 : r * s ∈ c.S0 :=
      reflection_product_mem_S0 c hr.1 hr.2 hsS hsS0
    have haction : ∀ x : G, x ∈ c.U →
        r * x * r⁻¹ = s * x * s⁻¹ := by
      intro x hxU
      let w : G := r * s
      have hwS0 : w ∈ c.S0 := hrsS0
      have hsH : s ∈ c.H := centralizerSetup_S_le_H c hsS
      have hyU : s * x * s⁻¹ ∈ c.U :=
        (centralizerSetup_U_isNormalIn_H c).2 s hsH x hxU
      have hwy : (s * x * s⁻¹) * w = w * (s * x * s⁻¹) :=
        (Subgroup.mem_centralizer_iff.mp (hS0centU hwS0))
          (s * x * s⁻¹) hyU
      have hwfix : w * (s * x * s⁻¹) * w⁻¹ = s * x * s⁻¹ := by
        calc
          w * (s * x * s⁻¹) * w⁻¹ =
              (s * x * s⁻¹) * w * w⁻¹ := by rw [hwy]
          _ = s * x * s⁻¹ := by simp
      have hws : w * s = r := by
        simp only [w]
        calc
          (r * s) * s = r * (s * s) := by group
          _ = r := by simpa [pow_two] using congrArg (fun z : G => r * z) hsI.2
      calc
        r * x * r⁻¹ = (w * s) * x * (w * s)⁻¹ := by rw [hws]
        _ = w * (s * x * s⁻¹) * w⁻¹ := by group
        _ = s * x * s⁻¹ := hwfix
    calc
      (I : Set G) = invertedElements c.U s := hI
      _ = invertedElements c.U r := by
        ext x
        rw [invertedElements, invertedElements]
        constructor
        · rintro ⟨hxU, hxinv⟩
          exact ⟨hxU, (haction x hxU).trans hxinv⟩
        · rintro ⟨hxU, hxinv⟩
          exact ⟨hxU, (haction x hxU).symm.trans hxinv⟩
  have h28 := lemma_2_8 hmin c hinverted
  have hcommbot : ⁅c.S0, c.U⁆ = ⊥ :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hS0centU
  exact h28.1 hcommbot

end CFSG.GorensteinWalter
