module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardTwoThreeNormalizerInvolutions
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Involutions normalizing a Sylow three-subgroup in the order-two branch

When the `A₄` normalizer is proper, every Sylow `3`-subgroup of it is
conjugate to an intersection attached to an outside involution.  Conjugation
therefore transports the cardinal-three normalizer fiber to every Sylow
`3`-subgroup.
-/

open scoped Pointwise
open BenderSuzuki.PFchapter1section1
open BenderSuzuki.PFAppendixIII

namespace CFSG.GorensteinWalter

universe u

/-- In the proper `|K| = 2` branch, exactly three ambient involutions
normalize the image of any Sylow `3`-subgroup of `N_G(H)`. -/
public theorem
    BrauerSuzukiWallHypotheses.involutions_normalizing_sylow_three_card_eq_three_of_card_K_eq_two
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 2)
    (hNne : Subgroup.normalizer (h.H : Set G) ≠ ⊤) :
    let N : Subgroup G := Subgroup.normalizer (h.H : Set G)
    ∀ P : Sylow 3 N,
      Nat.card {v : G // IsInvolution v ∧
        v ∈ Subgroup.normalizer
          (((P : Subgroup N).map N.subtype : Subgroup G) : Set G)} = 3 := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let N : Subgroup G := Subgroup.normalizer (h.H : Set G)
  change ∀ P : Sylow 3 N,
    Nat.card {v : G // IsInvolution v ∧
      v ∈ Subgroup.normalizer
        (((P : Subgroup N).map N.subtype : Subgroup G) : Set G)} = 3
  intro P
  have hstrong : BenderSuzuki.IsStronglyEmbedded N :=
    h.normalizer_H_isStronglyEmbedded_of_card_K_eq_two hk hNne
  have hHleN : h.H ≤ N := Subgroup.le_normalizer
  have htH : h.t ∈ h.H := by
    rw [h.H_eq_join]
    exact (show h.K ≤ h.K ⊔ Subgroup.zpowers h.s from le_sup_left)
      h.t_mem_K
  have htN : h.t ∈ N := hHleN htH
  have htIBS : BenderSuzuki.PFAppendixIII.IsInvolution h.t :=
    ⟨h.t_involution.1, h.t_involution.2⟩
  obtain ⟨g, _hgTop, hgN⟩ :=
    SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hNne)
  obtain ⟨u, ⟨huCoset, huIBS⟩, _huUnique⟩ :=
    hstrong.existsUnique_involution_in_centralizer_rightCoset
      htN htIBS hgN
  have huI : IsInvolution u := ⟨huIBS.1, huIBS.2⟩
  have huN : u ∉ N := by
    intro huN
    apply hgN
    have hugH : u * g⁻¹ ∈ h.H := by
      rw [h.H_eq_centralizer]
      exact huCoset
    have hugN : u * g⁻¹ ∈ N := hHleN hugH
    have hgEq : g = (u * g⁻¹)⁻¹ * u := by group
    rw [hgEq]
    exact N.mul_mem (N.inv_mem hugN) huN
  let T : Subgroup G := N ⊓ rightConjugate N u
  obtain ⟨hTcard0, _huNorm, _huInv⟩ :=
    h.normalizer_inf_rightConjugate_card_eq_three_and_inverted_of_card_K_eq_two
      hk huI (by simpa [N] using huN)
  have hTcard : Nat.card T = 3 := by
    simpa [T, N] using hTcard0
  have hTleN : T ≤ N := inf_le_left
  let TN : Subgroup N := T.subgroupOf N
  have hTNcard : Nat.card TN = 3 := by
    calc
      Nat.card TN = Nat.card T :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTleN).toEquiv
      _ = 3 := hTcard
  have hNiso : Nonempty (N ≃* alternatingGroup (Fin 4)) :=
    h.normalizer_mulEquiv_alternatingGroup_four_of_card_K_eq_two hk
  have hNcard : Nat.card N = 12 := by
    obtain ⟨e⟩ := hNiso
    calc
      Nat.card N = Nat.card (alternatingGroup (Fin 4)) :=
        Nat.card_congr e.toEquiv
      _ = 12 := alternatingGroup.card_of_card_eq_four (by simp)
  have hfac : (Nat.factorization 12) 3 = 1 := by
    rw [show 12 = 3 * 4 by norm_num,
      Nat.factorization_mul_apply_of_coprime (by norm_num : Nat.Coprime 3 4),
      Nat.prime_three.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 4)]
  have hTNpow : Nat.card TN = 3 ^ (Nat.card N).factorization 3 := by
    rw [hTNcard, hNcard, hfac]
    norm_num
  let P₀ : Sylow 3 N := Sylow.ofCard TN hTNpow
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N P₀ P
  let eG : G ≃* G := MulAut.conj (n : G)
  let PG : Subgroup G := (P : Subgroup N).map N.subtype
  have hnSub :
      (P₀ : Subgroup N).map (MulAut.conj n).toMonoidHom =
        (P : Subgroup N) := by
    have hn' := congrArg (fun Q : Sylow 3 N => (Q : Subgroup N)) hn
    exact hn'
  have hTNmap : TN.map N.subtype = T :=
    Subgroup.map_subgroupOf_eq_of_le hTleN
  have hcomp :
      eG.toMonoidHom.comp N.subtype =
        N.subtype.comp (MulAut.conj n).toMonoidHom := by
    ext x
    rfl
  have hMapT : T.map eG.toMonoidHom = PG := by
    calc
      T.map eG.toMonoidHom =
          (TN.map N.subtype).map eG.toMonoidHom := by rw [hTNmap]
      _ = TN.map (eG.toMonoidHom.comp N.subtype) := by
        rw [Subgroup.map_map]
      _ = TN.map (N.subtype.comp (MulAut.conj n).toMonoidHom) := by
        rw [hcomp]
      _ = (TN.map (MulAut.conj n).toMonoidHom).map N.subtype := by
        rw [Subgroup.map_map]
      _ = ((P₀ : Subgroup N).map
            (MulAut.conj n).toMonoidHom).map N.subtype := by rfl
      _ = (P : Subgroup N).map N.subtype := by rw [hnSub]
      _ = PG := rfl
  have hNormMap :
      (Subgroup.normalizer (T : Set G)).map eG.toMonoidHom =
        Subgroup.normalizer (PG : Set G) := by
    rw [Subgroup.map_equiv_normalizer_eq T eG, hMapT]
  have hInvIff : ∀ x : G, IsInvolution (eG x) ↔ IsInvolution x := by
    intro x
    constructor
    · rintro ⟨hxne, hxsq⟩
      constructor
      · intro hx
        apply hxne
        rw [hx, map_one]
      · apply eG.injective
        rw [map_pow, hxsq, map_one]
    · rintro ⟨hxne, hxsq⟩
      constructor
      · intro hex
        apply hxne
        apply eG.injective
        rw [hex, map_one]
      · rw [← map_pow, hxsq, map_one]
  have hNormIff : ∀ x : G,
      x ∈ Subgroup.normalizer (T : Set G) ↔
        eG x ∈ Subgroup.normalizer (PG : Set G) := by
    intro x
    rw [← hNormMap]
    simp
  let eInv :
      {v : G // IsInvolution v ∧
        v ∈ Subgroup.normalizer (T : Set G)} ≃
      {v : G // IsInvolution v ∧
        v ∈ Subgroup.normalizer (PG : Set G)} :=
    eG.toEquiv.subtypeEquiv (fun x =>
      and_congr (hInvIff x).symm (hNormIff x))
  have hTInvCard :
      Nat.card {v : G // IsInvolution v ∧
        v ∈ Subgroup.normalizer (T : Set G)} = 3 := by
    simpa [T, N] using
      h.involutions_normalizing_inf_rightConjugate_card_eq_three_of_card_K_eq_two
        hk huI (by simpa [N] using huN)
  change Nat.card {v : G // IsInvolution v ∧
    v ∈ Subgroup.normalizer (PG : Set G)} = 3
  calc
    Nat.card {v : G // IsInvolution v ∧
        v ∈ Subgroup.normalizer (PG : Set G)} =
        Nat.card {v : G // IsInvolution v ∧
          v ∈ Subgroup.normalizer (T : Set G)} :=
      (Nat.card_congr eInv).symm
    _ = 3 := hTInvCard

end CFSG.GorensteinWalter
