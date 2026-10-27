module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinCosetInvolution
import all CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseCountData
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-!
If `s ∈ Ĥ`, then `s*y` represents the same right `Ĥ`-coset as `y`.
When `s` commutes with an outside involution `y`, this gives the exact
cardinality transport needed for the second alternative of restriction (6).
-/

public theorem firstCase_klein_coset_representative_card_eq
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    {s y : G} (hsH : s ∈ c.Hhat) (hy : IsInvolution y)
    (hsy : s * y = y * s) (hsI : IsInvolution s)
    (hyH : y ∉ c.Hhat) :
    firstCaseCosetInvolutions c (s * y) =
      firstCaseCosetInvolutions c y := by
  classical
  have hsyI : IsInvolution (s * y) := by
    refine ⟨?_, ?_⟩
    · intro h
      apply hyH
      have hyEq : y = s⁻¹ * (s * y) := by simp
      rw [hyEq, h]
      exact c.Hhat.mul_mem (c.Hhat.inv_mem hsH) (by simp)
    · have hs2 : s * s = 1 := by simpa [pow_two] using hsI.2
      have hy2 : y * y = 1 := by simpa [pow_two] using hy.2
      calc
        (s * y) ^ 2 = s * (y * s) * y := by simp [pow_two, mul_assoc]
        _ = s * (s * y) * y := by rw [hsy]
        _ = (s * s) * (y * y) := by group
        _ = 1 := by rw [hs2, hy2]; simp
  have hset : (c.Hhat : Set G) * ({s * y} : Set G) =
      (c.Hhat : Set G) * ({y} : Set G) := by
    ext z
    constructor
    · intro hz
      rcases Set.mem_mul.mp hz with ⟨a, ha, b, hb, hab⟩
      have hb' : b = s * y := by simpa using hb
      refine Set.mem_mul.mpr ⟨a * s, c.Hhat.mul_mem ha hsH, y, by simp, ?_⟩
      rw [← hab, hb']
      simp [mul_assoc]
    · intro hz
      rcases Set.mem_mul.mp hz with ⟨a, ha, b, hb, hab⟩
      have hb' : b = y := by simpa using hb
      refine Set.mem_mul.mpr ⟨a * s⁻¹, c.Hhat.mul_mem ha (c.Hhat.inv_mem hsH),
        s * y, by simp, ?_⟩
      rw [← hab, hb']
      group
  calc
    firstCaseCosetInvolutions c (s * y) =
        Nat.card {x : G // IsInvolution x ∧
          x ∈ (c.Hhat : Set G) * ({s * y} : Set G)} := rfl
    _ = Nat.card {x : G // IsInvolution x ∧
          x ∈ (c.Hhat : Set G) * ({y} : Set G)} := by rw [hset]
    _ = firstCaseCosetInvolutions c y := by
      rfl

public theorem firstCase_klein_coset_representative_mem_J
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    {s y : G} {n : ℕ} (hsH : s ∈ c.Hhat) (hyJ : y ∈ firstCaseJ c n)
    (hsy : s * y = y * s) (hsI : IsInvolution s) :
    s * y ∈ firstCaseJ c n := by
  rcases (show IsInvolution y ∧ y ∉ c.Hhat ∧
      firstCaseCosetInvolutions c y = n by simpa [firstCaseJ] using hyJ) with
    ⟨hy, hyH, hyn⟩
  have hcard := firstCase_klein_coset_representative_card_eq c hsH hy hsy hsI hyH
  refine (show IsInvolution (s * y) ∧ s * y ∉ c.Hhat ∧
      firstCaseCosetInvolutions c (s * y) = n by
    refine ⟨?_, ?_, ?_⟩
    · exact (by
        refine ⟨?_, ?_⟩
        · intro h
          apply hyH
          have hyEq : y = s⁻¹ * (s * y) := by simp
          rw [hyEq, h]
          exact c.Hhat.mul_mem (c.Hhat.inv_mem hsH) (by simp)
        · have hs2 : s * s = 1 := by simpa [pow_two] using hsI.2
          have hy2 : y * y = 1 := by simpa [pow_two] using hy.2
          calc
            (s * y) ^ 2 = s * (y * s) * y := by simp [pow_two, mul_assoc]
            _ = s * (s * y) * y := by rw [hsy]
            _ = (s * s) * (y * y) := by group
            _ = 1 := by rw [hs2, hy2]; simp)
    · intro h
      apply hyH
      have hyEq : y = s⁻¹ * (s * y) := by simp
      rw [hyEq]
      exact c.Hhat.mul_mem (c.Hhat.inv_mem hsH) h
    · calc
        firstCaseCosetInvolutions c (s * y) =
            firstCaseCosetInvolutions c y := hcard
        _ = n := hyn)

end CFSG.GorensteinWalter
