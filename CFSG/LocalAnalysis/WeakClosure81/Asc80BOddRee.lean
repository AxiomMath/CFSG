module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BOdd

import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Ree
import CFSG.Quasithin.Vol2.Ch11SecE3Sz

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Open
open CFSG.ComponentClassification.LiteratureLocal
  (ward_kleidman_small_Ree_involution_centralizer_maximal)

theorem seitzFour_ree :
    SeitzFour fun X _ => ∃ f : ℕ, CFSG.Models.LieModel X .twistedG2 0 3 f := by
  intro G _ _ L E hLn hLs hnab ⟨f, hf⟩ hC hE h4 _
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha, -, hR⟩ := exists_reeTitsModel_of_lieModel_twistedG2 hf
  obtain ⟨-, -, hcent, hmax, -, -, hodd⟩ :=
    ward_kleidman_small_Ree_involution_centralizer_maximal a ha ↥L hR
  have hEL : E ≤ L := fun e he =>
    CFSG.Quasithin.Vol2.Ch11.SecE3.mem_of_pow_two_pow_eq_one hC hodd (k := 1)
      (by simpa using hE.2 e he)
  have hEne : E ≠ ⊥ := fun hb => by rw [hb] at h4; simp at h4
  obtain ⟨⟨x, hxE⟩, hx1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hEne
  have hx1 : x ≠ 1 := fun h => hx1' (Subtype.ext h)
  obtain ⟨y, hyE, hy1, hyx⟩ := exists_mem_ne_one_ne_of_four_le_card (A := E) (by omega) x
  set x' : ↥L := ⟨x, hEL hxE⟩
  set y' : ↥L := ⟨y, hEL hyE⟩
  have hx2 : orderOf x' = 2 :=
    orderOf_eq_prime (Subtype.ext (by simpa [x'] using hE.2 x hxE))
      fun h => hx1 (congrArg Subtype.val h)
  have hy2 : orderOf y' = 2 :=
    orderOf_eq_prime (Subtype.ext (by simpa [y'] using hE.2 y hyE))
      fun h => hy1 (congrArg Subtype.val h)
  have hne : centralizer ({x'} : Set ↥L) ≠ centralizer {y'} := by
    intro heq
    obtain ⟨-, -, -, -, -, hzx⟩ := hcent x' hx2
    obtain ⟨-, -, -, -, -, hzy⟩ := hcent y' hy2
    rw [heq, hzy] at hzx
    have hyx' : y' ∈ zpowers x' := hzx ▸ mem_zpowers y'
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hyx'
    rw [← zpow_mod_orderOf, hx2] at hk
    have hk2 : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
    rcases hk2 with h0 | h1
    · rw [h0, zpow_zero] at hk
      rw [← hk, orderOf_one] at hy2
      exact absurd hy2 (by norm_num)
    · rw [h1, zpow_one] at hk
      exact hyx (congrArg Subtype.val hk).symm
  have hLsup := (hmax x' hx2).sup_eq_top_of_ne (hmax y' hy2) hne
  have hmapz : ∀ z : ↥L, (z : G) ∈ E → (z : G) ≠ 1 → (centralizer ({z} : Set ↥L)).map L.subtype ≤
      ⨆ e ∈ E, ⨆ (_ : e ≠ 1), L ⊓ centralizer ({e} : Set G) := by
    intro z hzE hz1
    refine le_trans ?_ (le_iSup₂_of_le (z : G) hzE (le_iSup_of_le hz1 le_rfl))
    rintro _ ⟨l, hl, rfl⟩
    refine ⟨l.2, ?_⟩
    have hl' : l * z = z * l := mem_centralizer_singleton_iff.1 hl
    show (l : G) ∈ centralizer ({(z : G)} : Set G)
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val hl'
  refine le_antisymm (iSup₂_le fun _ _ => iSup_le fun _ => inf_le_left) ?_
  intro l hl
  have h1 : (⟨l, hl⟩ : ↥L) ∈ centralizer ({x'} : Set ↥L) ⊔ centralizer {y'} :=
    hLsup ▸ mem_top _
  have h2 := mem_map_of_mem L.subtype h1
  rw [Subgroup.map_sup] at h2
  exact sup_le (hmapz x' hxE hx1) (hmapz y' hyE hy1) h2

end CFSG.LocalAnalysis.WeakClosure81

end
