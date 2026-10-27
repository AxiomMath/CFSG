module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardTwoStrongEmbedding
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.StrongEmbeddingCounting
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Normalizer intersections in the order-two branch

For an involution `u` outside `N_G(H)`, strong embedding and the
centralizer-coset decomposition identify `N_G(H) ∩ N_G(H)^u` as a subgroup
of order three.  The involution normalizes this intersection and acts on it
by inversion.
-/

open scoped Pointwise
open BenderSuzuki.PFchapter1section1

namespace CFSG.GorensteinWalter

universe u

/-- In the `|K| = 2` branch, an involution outside `N_G(H)` normalizes and
inverts its order-three intersection with the corresponding conjugate of
`N_G(H)`. -/
public theorem
    BrauerSuzukiWallHypotheses.normalizer_inf_rightConjugate_card_eq_three_and_inverted_of_card_K_eq_two
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 2) {u : G}
    (huI : IsInvolution u)
    (huN : u ∉ Subgroup.normalizer (h.H : Set G)) :
    let N : Subgroup G := Subgroup.normalizer (h.H : Set G)
    let T : Subgroup G := N ⊓ rightConjugate N u
    Nat.card T = 3 ∧
      u ∈ Subgroup.normalizer (T : Set G) ∧
      ∀ x : G, x ∈ T → u * x * u⁻¹ = x⁻¹ := by
  classical
  let N : Subgroup G := Subgroup.normalizer (h.H : Set G)
  let T : Subgroup G := N ⊓ rightConjugate N u
  have hNne : N ≠ ⊤ := by
    intro htop
    apply huN
    rw [show Subgroup.normalizer (h.H : Set G) = N from rfl, htop]
    simp
  have hstrong : BenderSuzuki.IsStronglyEmbedded N :=
    h.normalizer_H_isStronglyEmbedded_of_card_K_eq_two hk hNne
  have huIBS : BenderSuzuki.PFAppendixIII.IsInvolution u :=
    ⟨huI.1, huI.2⟩
  have hKleH : h.K ≤ h.H := by
    rw [h.H_eq_join]
    exact le_sup_left
  have htH : h.t ∈ h.H := hKleH h.t_mem_K
  have htN : h.t ∈ N := Subgroup.le_normalizer htH
  have htIBS : BenderSuzuki.PFAppendixIII.IsInvolution h.t :=
    ⟨h.t_involution.1, h.t_involution.2⟩
  have hHleN : h.H ≤ N := Subgroup.le_normalizer
  let : IsKleinFour h.H := h.isKleinFour_H_of_card_K_eq_two hk
  have hTfree : ∀ {x : G}, x ∈ T →
      ¬ BenderSuzuki.PFAppendixIII.IsInvolution x := by
    intro x hxT hxI
    exact hstrong.inf_rightConjugate_involutionFree huN (by
      simpa [T] using hxT) hxI
  have hdisjoint : Disjoint h.H T := by
    rw [Subgroup.disjoint_def]
    intro x hxH hxT
    by_contra hxne
    have hxSqH := IsKleinFour.mul_self (⟨x, hxH⟩ : h.H)
    have hxSq : x ^ 2 = 1 := by
      simpa [pow_two] using congrArg Subtype.val hxSqH
    exact hTfree hxT ⟨hxne, hxSq⟩
  have hprod : (h.H : Set G) * (T : Set G) = (N : Set G) := by
    have hp := hstrong.centralizer_mul_inf_rightConjugate_eq
      htN htIBS huIBS huN
    simpa [T, h.H_eq_centralizer] using hp
  let toN : h.H × T → N := fun z =>
    ⟨(z.1 : G) * (z.2 : G), N.mul_mem (hHleN z.1.2) z.2.2.1⟩
  have htoNinj : Function.Injective toN := by
    intro a b hab
    apply Subgroup.mul_injective_of_disjoint hdisjoint
    exact congrArg Subtype.val hab
  have htoNsurj : Function.Surjective toN := by
    intro n
    have hnprod : (n : G) ∈ (h.H : Set G) * (T : Set G) := by
      rw [hprod]
      exact n.property
    rcases hnprod with ⟨a, haH, b, hbT, hab⟩
    exact ⟨(⟨a, haH⟩, ⟨b, hbT⟩), Subtype.ext hab⟩
  have hNcard : Nat.card N = 12 := by
    obtain ⟨e⟩ :=
      h.normalizer_mulEquiv_alternatingGroup_four_of_card_K_eq_two hk
    calc
      Nat.card N = Nat.card (alternatingGroup (Fin 4)) :=
        Nat.card_congr e.toEquiv
      _ = 12 := alternatingGroup.card_of_card_eq_four (by simp)
  have hTcard : Nat.card T = 3 := by
    have hcard :=
      Nat.card_congr (Equiv.ofBijective toN ⟨htoNinj, htoNsurj⟩)
    rw [Nat.card_prod, (h.isKleinFour_H_of_card_K_eq_two hk).card_four,
      hNcard] at hcard
    omega
  have huNorm : u ∈ Subgroup.normalizer (T : Set G) := by
    simpa [T] using
      BenderSuzuki.inf_rightConjugate_mem_normalizer_of_isInvolution N huIBS
  let C : Subgroup G := T ⊓ Subgroup.centralizer ({u} : Set G)
  have hTCt : T ⊓ Subgroup.centralizer ({h.t} : Set G) = ⊥ := by
    rw [← h.H_eq_centralizer]
    apply le_antisymm
    · exact hdisjoint.symm inf_le_left inf_le_right
    · exact bot_le
  have hCcard : Nat.card C = 1 := by
    have hc := hstrong.inf_rightConjugate_outside_inside_centralizer_card_eq
      htN htIBS huIBS huN
    change Nat.card
      (T ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) = 1
    calc
      Nat.card (T ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) =
          Nat.card
            (T ⊓ Subgroup.centralizer ({h.t} : Set G) : Subgroup G) := by
        simpa [T] using hc
      _ = 1 := by rw [hTCt]; simp
  have hfixed_one : ∀ {x : G}, x ∈ T → u * x * u⁻¹ = x → x = 1 := by
    intro x hxT hxfix
    have hxcomm : x * u = u * x := by
      calc
        x * u = (u * x * u⁻¹) * u := by rw [hxfix]
        _ = u * x := by group
    have hxC : x ∈ C := by
      refine ⟨hxT, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr hxcomm
    have hCsub : Subsingleton C :=
      (Nat.card_eq_one_iff_unique.mp hCcard).1
    have heq : (⟨x, hxC⟩ : C) = 1 := hCsub.elim _ _
    exact congrArg Subtype.val heq
  refine ⟨hTcard, huNorm, ?_⟩
  intro x hxT
  by_cases hxone : x = 1
  · simp [hxone]
  let xT : T := ⟨x, hxT⟩
  let y : G := u * x * u⁻¹
  have hyT : y ∈ T := by
    exact (Subgroup.mem_normalizer_iff.mp huNorm x).mp hxT
  let yT : T := ⟨y, hyT⟩
  have hyone : y ≠ 1 := by
    intro hy1
    apply hxone
    have hc := congrArg (fun z : G => u⁻¹ * z * u) hy1
    calc
      x = u⁻¹ * (u * x * u⁻¹) * u := by group
      _ = u⁻¹ * 1 * u := hc
      _ = 1 := by group
  have hyx : y ≠ x := by
    intro hyx
    exact hxone (hfixed_one hxT (by simpa [y] using hyx))
  have hxinvone : x⁻¹ ≠ 1 := by simpa using hxone
  have hxinvx : x⁻¹ ≠ x := by
    intro hinv
    have hxSq : x ^ 2 = 1 := by
      calc
        x ^ 2 = x * x := pow_two x
        _ = x⁻¹ * x := by rw [hinv]
        _ = 1 := by simp
    exact hTfree hxT ⟨hxone, hxSq⟩
  let : Fintype T := Fintype.ofFinite T
  let triple : Finset T := {1, xT, xT⁻¹}
  have hxTone : xT ≠ 1 := by
    intro hx
    exact hxone (congrArg Subtype.val hx)
  have hxTinvone : xT⁻¹ ≠ 1 := by
    intro hx
    exact hxinvone (congrArg Subtype.val hx)
  have hxTinvx : xT⁻¹ ≠ xT := by
    intro hx
    exact hxinvx (congrArg Subtype.val hx)
  have htripleCard : triple.card = 3 := by
    simp [triple, hxTone.symm, hxTinvone.symm, hxTinvx.symm]
  have htriple : triple = Finset.univ := by
    apply Finset.eq_univ_of_card
    calc
      triple.card = 3 := htripleCard
      _ = Fintype.card T := by
        simpa [Nat.card_eq_fintype_card] using hTcard.symm
  have hyMem : yT ∈ triple := by
    rw [htriple]
    exact Finset.mem_univ yT
  have hyCases : yT = 1 ∨ yT = xT ∨ yT = xT⁻¹ := by
    simpa [triple] using hyMem
  rcases hyCases with hy1 | hyx' | hyinv
  · exact (hyone (congrArg Subtype.val hy1)).elim
  · exact (hyx (congrArg Subtype.val hyx')).elim
  · exact congrArg Subtype.val hyinv

end CFSG.GorensteinWalter
