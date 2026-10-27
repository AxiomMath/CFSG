module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardTwoCosetNormalizer
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The order-three centralizer in the order-two branch

Let `T = N_G(H) ∩ N_G(H)^u` for an involution `u` outside `N_G(H)`.  The
order-three subgroup `T` is self-normalizing inside `N_G(H)`.  A hypothetical
element of `C_G(T)` outside the normalizer would give a `T`-invariant right
coset of `H`; the unique involution in that coset would both centralize and
invert `T`, a contradiction.  Hence `C_G(T) = T`.
-/

open scoped Pointwise
open BenderSuzuki.PFchapter1section1
open BenderSuzuki.PFAppendixIII

namespace CFSG.GorensteinWalter

universe u

/-- In the `|K| = 2` branch, the order-three intersection attached to an
outside involution is self-centralizing in the ambient group. -/
public theorem
    BrauerSuzukiWallHypotheses.centralizer_inf_rightConjugate_eq_of_card_K_eq_two
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 2) {u : G}
    (huI : IsInvolution u)
    (huN : u ∉ Subgroup.normalizer (h.H : Set G)) :
    let N : Subgroup G := Subgroup.normalizer (h.H : Set G)
    let T : Subgroup G := N ⊓ rightConjugate N u
    Subgroup.centralizer (T : Set G) = T := by
  classical
  let N : Subgroup G := Subgroup.normalizer (h.H : Set G)
  let T : Subgroup G := N ⊓ rightConjugate N u
  obtain ⟨hTcard, _huNorm, _huInv⟩ :=
    h.normalizer_inf_rightConjugate_card_eq_three_and_inverted_of_card_K_eq_two
      hk huI huN
  have hNne : N ≠ ⊤ := by
    intro htop
    apply huN
    change u ∈ N
    rw [htop]
    trivial
  have hstrong : BenderSuzuki.IsStronglyEmbedded N :=
    h.normalizer_H_isStronglyEmbedded_of_card_K_eq_two hk hNne
  have hHleN : h.H ≤ N := Subgroup.le_normalizer
  have hTleN : T ≤ N := inf_le_left
  let TN : Subgroup N := T.subgroupOf N
  have hTNcard : Nat.card TN = 3 := by
    calc
      Nat.card TN = Nat.card T :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTleN).toEquiv
      _ = 3 := hTcard
  have hNiso : Nonempty (N ≃* alternatingGroup (Fin 4)) :=
    h.normalizer_mulEquiv_alternatingGroup_four_of_card_K_eq_two hk
  have hTNnorm : Subgroup.normalizer (TN : Set N) = TN :=
    normalizer_eq_self_of_card_eq_three_of_mulEquiv_alternatingGroup_four
      TN hTNcard hNiso
  have hcentralizer_inside_N :
      ∀ {c : G}, c ∈ Subgroup.centralizer (T : Set G) → c ∈ N → c ∈ T := by
    intro c hcC hcN
    have hcNorm : c ∈ Subgroup.normalizer (T : Set G) :=
      Subgroup.centralizer_le_normalizer (T : Set G) hcC
    let cN : N := ⟨c, hcN⟩
    have hcSub : cN ∈ (Subgroup.normalizer (T : Set G)).subgroupOf N :=
      hcNorm
    rw [Subgroup.subgroupOf_normalizer_eq hTleN] at hcSub
    have hcTN : cN ∈ TN := by
      rw [← hTNnorm]
      exact hcSub
    exact hcTN
  let : IsMulCommutative T :=
    (isCyclic_of_prime_card hTcard).isMulCommutative
  apply le_antisymm
  · intro c hcC
    by_cases hcN : c ∈ N
    · exact hcentralizer_inside_N hcC hcN
    · exfalso
      have htH : h.t ∈ h.H := by
        rw [h.H_eq_join]
        exact (show h.K ≤ h.K ⊔ Subgroup.zpowers h.s from le_sup_left)
          h.t_mem_K
      have htN : h.t ∈ N := hHleN htH
      have htIBS : BenderSuzuki.PFAppendixIII.IsInvolution h.t :=
        ⟨h.t_involution.1, h.t_involution.2⟩
      obtain ⟨v, hv, hvUnique⟩ :=
        hstrong.existsUnique_involution_in_centralizer_rightCoset
          htN htIBS hcN
      have hvCosetH : v * c⁻¹ ∈ h.H := by
        rw [h.H_eq_centralizer]
        exact hv.1
      have hvN : v ∉ N := by
        intro hvN
        apply hcN
        have hvcN : v * c⁻¹ ∈ N := hHleN hvCosetH
        have hcEq : c = (v * c⁻¹)⁻¹ * v := by group
        rw [hcEq]
        exact N.mul_mem (N.inv_mem hvcN) hvN
      have hvC : v ∈ Subgroup.centralizer (T : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hxT
        have hxc : x * c = c * x :=
          (Subgroup.mem_centralizer_iff.mp hcC) x hxT
        have hxcInv : x * c⁻¹ = c⁻¹ * x :=
          (show Commute x c from hxc).inv_right.eq
        have hxInvN : x⁻¹ ∈ N := N.inv_mem hxT.1
        have hconjH : x⁻¹ * (v * c⁻¹) * x ∈ h.H := by
          have hmem :=
            (Subgroup.mem_normalizer_iff.mp hxInvN (v * c⁻¹)).mp hvCosetH
          simpa using hmem
        have hcosetEq :
            rightConjugateElem v x * c⁻¹ =
              x⁻¹ * (v * c⁻¹) * x := by
          dsimp [rightConjugateElem]
          calc
            (x⁻¹ * v * x) * c⁻¹ =
                x⁻¹ * v * (x * c⁻¹) := by group
            _ = x⁻¹ * v * (c⁻¹ * x) := by rw [hxcInv]
            _ = x⁻¹ * (v * c⁻¹) * x := by group
        have hconjCoset :
            rightConjugateElem v x * c⁻¹ ∈
              Subgroup.centralizer ({h.t} : Set G) := by
          rw [← h.H_eq_centralizer, hcosetEq]
          exact hconjH
        have hconjEq : rightConjugateElem v x = v :=
          hvUnique _ ⟨hconjCoset,
            BenderSuzuki.PFAppendixIII.isInvolution_rightConjugateElem hv.2⟩
        have hmul := congrArg (fun z : G ↦ x * z) hconjEq
        have hvx : v * x = x * v := by
          simpa [rightConjugateElem, mul_assoc] using hmul
        exact hvx.symm
      have hvI : IsInvolution v := ⟨hv.2.1, hv.2.2⟩
      have hvv : v * v = 1 := by
        simpa [pow_two] using hvI.2
      have hvInvSelf : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
      let Tv : Subgroup G := N ⊓ rightConjugate N v
      obtain ⟨hTvcard0, _hvNormTv, hvInvTv0⟩ :=
        h.normalizer_inf_rightConjugate_card_eq_three_and_inverted_of_card_K_eq_two
          hk hvI (by simpa [N] using hvN)
      have hTvcard : Nat.card Tv = 3 := by
        simpa [Tv, N] using hTvcard0
      have hvInvTv :
          ∀ x : G, x ∈ Tv → v * x * v⁻¹ = x⁻¹ := by
        simpa [Tv, N] using hvInvTv0
      have hTleTv : T ≤ Tv := by
        intro x hxT
        refine ⟨hxT.1, ?_⟩
        have hmem :=
          BenderSuzuki.rightConjugateElem_mem_rightConjugate
            (M := N) (g := v) hxT.1
        have hxv : x * v = v * x :=
          (Subgroup.mem_centralizer_iff.mp hvC) x hxT
        have hfix : rightConjugateElem x v = x := by
          dsimp [rightConjugateElem]
          calc
            v⁻¹ * x * v = v * x * v := by rw [hvInvSelf]
            _ = (x * v) * v := by rw [← hxv]
            _ = x := by rw [mul_assoc, hvv]; simp
        rw [hfix] at hmem
        exact hmem
      have hTvEq : Tv = T :=
        (Subgroup.eq_of_le_of_card_ge hTleTv (by
          rw [hTvcard, hTcard])).symm
      have haH : c * v ∈ h.H := by
        have hinv := h.H.inv_mem hvCosetH
        simpa [mul_inv_rev, hvInvSelf] using hinv
      have hcNormT : c ∈ Subgroup.normalizer (T : Set G) :=
        Subgroup.centralizer_le_normalizer (T : Set G) hcC
      have hcNormTv : c ∈ Subgroup.normalizer (Tv : Set G) := by
        rw [hTvEq]
        exact hcNormT
      have havNormTv : (c * v) * v ∈ Subgroup.normalizer (Tv : Set G) := by
        simpa [mul_assoc, hvv] using hcNormTv
      have haOne : c * v = 1 :=
        h.eq_one_of_mem_H_mul_involution_mem_normalizer_inf_rightConjugate_of_card_K_eq_two
          hk hvI (by simpa [N] using hvN) haH (by
            simpa [Tv, N] using havNormTv)
      have hcEqv : c = v := by
        have hmul := congrArg (fun z : G ↦ z * v) haOne
        simpa [mul_assoc, hvv] using hmul
      subst c
      have hTne : T ≠ ⊥ := by
        intro hbot
        have hcardOne : Nat.card T = 1 := by simp [hbot]
        rw [hTcard] at hcardOne
        norm_num at hcardOne
      obtain ⟨xT, hxTne⟩ :=
        Subgroup.ne_bot_iff_exists_ne_one.mp hTne
      have hxne : (xT : G) ≠ 1 := by
        intro hx
        apply hxTne
        apply Subtype.ext
        exact hx
      have hxTv : (xT : G) ∈ Tv := by
        rw [hTvEq]
        exact xT.property
      have hvinv : v * (xT : G) * v⁻¹ = (xT : G)⁻¹ :=
        hvInvTv (xT : G) hxTv
      have hvfix : v * (xT : G) * v⁻¹ = (xT : G) := by
        have hxv : (xT : G) * v = v * (xT : G) :=
          (Subgroup.mem_centralizer_iff.mp hvC) (xT : G) xT.property
        calc
          v * (xT : G) * v⁻¹ =
              ((xT : G) * v) * v⁻¹ := by rw [← hxv]
          _ = (xT : G) := by simp
      have hxEqInv : (xT : G) = (xT : G)⁻¹ :=
        hvfix.symm.trans hvinv
      have hxSq : (xT : G) ^ 2 = 1 := by
        rw [pow_two]
        calc
          (xT : G) * (xT : G) = (xT : G)⁻¹ * (xT : G) :=
            congrArg (fun z : G ↦ z * (xT : G)) hxEqInv
          _ = 1 := by simp
      exact hstrong.inf_rightConjugate_involutionFree hvN (by
        simpa [Tv] using hxTv) ⟨hxne, hxSq⟩
  · intro x hxT
    rw [Subgroup.mem_centralizer_iff]
    intro y hyT
    exact congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := T)).comm
        (⟨y, hyT⟩ : T) (⟨x, hxT⟩ : T))

end CFSG.GorensteinWalter
