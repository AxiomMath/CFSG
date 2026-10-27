module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.AlternatingFourSylowThree
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardTwoSylowNormalizerInvolutions
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Outside involutions in the order-two branch

For a proper normalizer `N = N_G(H)`, associate to an outside involution `v`
the Sylow `3`-subgroup `N ∩ N^v`.  Conversely, an involution normalizing a
Sylow `3`-subgroup is outside `N`, and that subgroup is its associated
intersection.  This identifies the outside involutions with an incidence
sigma type having four fibers of cardinality three.
-/

open scoped Pointwise BigOperators
open BenderSuzuki.PFchapter1section1
open BenderSuzuki.PFAppendixIII

namespace CFSG.GorensteinWalter

universe u

/-- In the proper `|K| = 2` branch, there are exactly twelve involutions
outside `N_G(H)`. -/
public theorem
    BrauerSuzukiWallHypotheses.outside_involutions_card_eq_twelve_of_card_K_eq_two
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 2)
    (hNne : Subgroup.normalizer (h.H : Set G) ≠ ⊤) :
    let N : Subgroup G := Subgroup.normalizer (h.H : Set G)
    Nat.card {v : G // IsInvolution v ∧ v ∉ N} = 12 := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let N : Subgroup G := Subgroup.normalizer (h.H : Set G)
  change Nat.card {v : G // IsInvolution v ∧ v ∉ N} = 12
  let PG : Sylow 3 N → Subgroup G := fun P =>
    (P : Subgroup N).map N.subtype
  let InvNorm : Sylow 3 N → Type u := fun P =>
    {v : G // IsInvolution v ∧
      v ∈ Subgroup.normalizer (PG P : Set G)}
  let Pair := Σ P : Sylow 3 N, InvNorm P
  let OutInv := {v : G // IsInvolution v ∧ v ∉ N}
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
  have hPcard : ∀ P : Sylow 3 N, Nat.card P = 3 := by
    intro P
    rw [P.card_eq_multiplicity, hNcard, hfac]
    norm_num
  have hPGleN : ∀ P : Sylow 3 N, PG P ≤ N := by
    intro P x hx
    rcases hx with ⟨y, hyP, rfl⟩
    exact y.property
  have hPGsubgroup : ∀ P : Sylow 3 N,
      (PG P).subgroupOf N = (P : Subgroup N) := by
    intro P
    change ((P : Subgroup N).map N.subtype).comap N.subtype =
      (P : Subgroup N)
    exact Subgroup.comap_map_eq_self_of_injective N.subtype_injective P
  have hOutside : ∀ (P : Sylow 3 N) (v : InvNorm P), (v : G) ∉ N := by
    intro P v hvN
    have hvNorm : (v : G) ∈ Subgroup.normalizer (PG P : Set G) :=
      v.property.2
    let vN : N := ⟨(v : G), hvN⟩
    have hvSub : vN ∈
        (Subgroup.normalizer (PG P : Set G)).subgroupOf N :=
      hvNorm
    rw [Subgroup.subgroupOf_normalizer_eq (hPGleN P),
      hPGsubgroup P] at hvSub
    have hPnorm : Subgroup.normalizer ((P : Subgroup N) : Set N) =
        (P : Subgroup N) :=
      normalizer_eq_self_of_card_eq_three_of_mulEquiv_alternatingGroup_four
        P (hPcard P) hNiso
    have hvP : vN ∈ (P : Subgroup N) := by
      rw [← hPnorm]
      exact hvSub
    have hvNI : IsInvolution vN :=
      BenderSuzuki.IsInvolution.subtype v.property.1 hvN
    have hvOrder : orderOf vN = 2 :=
      orderOf_eq_prime hvNI.2 hvNI.1
    have hdvd : orderOf vN ∣ Nat.card P :=
      Subgroup.orderOf_dvd_natCard (P : Subgroup N) hvP
    rw [hvOrder, hPcard P] at hdvd
    norm_num at hdvd
  have hAssociated : ∀ (P : Sylow 3 N) (v : InvNorm P),
      PG P = N ⊓ rightConjugate N (v : G) := by
    intro P v
    have hvI : IsInvolution (v : G) := v.property.1
    have hvN : (v : G) ∉ N := hOutside P v
    have hvNorm : (v : G) ∈ Subgroup.normalizer (PG P : Set G) :=
      v.property.2
    let T : Subgroup G := N ⊓ rightConjugate N (v : G)
    obtain ⟨hTcard0, _hvNormT, _hvInvT⟩ :=
      h.normalizer_inf_rightConjugate_card_eq_three_and_inverted_of_card_K_eq_two
        hk hvI (by simpa [N] using hvN)
    have hTcard : Nat.card T = 3 := by
      simpa [T, N] using hTcard0
    have hPGcard : Nat.card (PG P) = 3 := by
      calc
        Nat.card (PG P) = Nat.card P :=
          Nat.card_congr
            (Subgroup.equivMapOfInjective (P : Subgroup N) N.subtype
              N.subtype_injective).toEquiv.symm
        _ = 3 := hPcard P
    have hPGleT : PG P ≤ T := by
      intro x hxPG
      have hxN : x ∈ N := hPGleN P hxPG
      refine ⟨hxN, ?_⟩
      have hconjPG :
          (v : G) * x * (v : G)⁻¹ ∈ PG P :=
        (Subgroup.mem_normalizer_iff.mp hvNorm x).mp hxPG
      have hconjN : (v : G) * x * (v : G)⁻¹ ∈ N :=
        hPGleN P hconjPG
      have hmem :=
        BenderSuzuki.rightConjugateElem_mem_rightConjugate
          (M := N) (g := (v : G)) hconjN
      simpa [rightConjugateElem, mul_assoc] using hmem
    have hEq : PG P = T :=
      Subgroup.eq_of_le_of_card_ge hPGleT (by rw [hPGcard, hTcard])
    simpa [T] using hEq
  let toFun : Pair → OutInv := fun z =>
    ⟨(z.2 : G), z.2.property.1, hOutside z.1 z.2⟩
  have htoFunInjective : Function.Injective toFun := by
    rintro ⟨P, v⟩ ⟨Q, w⟩ hvw
    have hvwG : (v : G) = (w : G) := congrArg Subtype.val hvw
    have hPAssoc := hAssociated P v
    have hQAssoc := hAssociated Q w
    have hPQmap : PG P = PG Q := by
      calc
        PG P = N ⊓ rightConjugate N (v : G) := hPAssoc
        _ = N ⊓ rightConjugate N (w : G) := by rw [hvwG]
        _ = PG Q := hQAssoc.symm
    have hPQsub : (P : Subgroup N) = (Q : Subgroup N) :=
      Subgroup.map_injective N.subtype_injective hPQmap
    have hPQ : P = Q := Sylow.ext hPQsub
    subst Q
    have hvw' : v = w := Subtype.ext hvwG
    subst w
    rfl
  have htoFunSurjective : Function.Surjective toFun := by
    intro v
    have hvI : IsInvolution (v : G) := v.property.1
    have hvN : (v : G) ∉ N := v.property.2
    let T : Subgroup G := N ⊓ rightConjugate N (v : G)
    obtain ⟨hTcard0, hvNorm0, _hvInv⟩ :=
      h.normalizer_inf_rightConjugate_card_eq_three_and_inverted_of_card_K_eq_two
        hk hvI (by simpa [N] using hvN)
    have hTcard : Nat.card T = 3 := by
      simpa [T, N] using hTcard0
    have hvNorm : (v : G) ∈ Subgroup.normalizer (T : Set G) := by
      simpa [T, N] using hvNorm0
    have hTleN : T ≤ N := inf_le_left
    let TN : Subgroup N := T.subgroupOf N
    have hTNcard : Nat.card TN = 3 := by
      calc
        Nat.card TN = Nat.card T :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTleN).toEquiv
        _ = 3 := hTcard
    have hTNpow : Nat.card TN = 3 ^ (Nat.card N).factorization 3 := by
      rw [hTNcard, hNcard, hfac]
      norm_num
    let P : Sylow 3 N := Sylow.ofCard TN hTNpow
    have hPG : PG P = T := by
      dsimp [PG, P]
      exact Subgroup.map_subgroupOf_eq_of_le hTleN
    let vP : InvNorm P :=
      ⟨(v : G), hvI, by rw [hPG]; exact hvNorm⟩
    refine ⟨⟨P, vP⟩, ?_⟩
    apply Subtype.ext
    rfl
  have hFiber : ∀ P : Sylow 3 N, Nat.card (InvNorm P) = 3 := by
    intro P
    simpa [InvNorm, PG, N] using
      h.involutions_normalizing_sylow_three_card_eq_three_of_card_K_eq_two
        hk hNne P
  have hSylow : Nat.card (Sylow 3 N) = 4 :=
    sylow_three_card_eq_four_of_mulEquiv_alternatingGroup_four hNiso
  let : Fintype (Sylow 3 N) := Fintype.ofFinite (Sylow 3 N)
  have hPairCard : Nat.card Pair = 12 := by
    calc
      Nat.card Pair = ∑ P : Sylow 3 N, Nat.card (InvNorm P) :=
        Nat.card_sigma
      _ = ∑ _P : Sylow 3 N, 3 := by
        apply Finset.sum_congr rfl
        intro P _hP
        exact hFiber P
      _ = Nat.card (Sylow 3 N) * 3 := by
        simp [Nat.card_eq_fintype_card]
      _ = 12 := by omega
  have hcard :=
    Nat.card_congr (Equiv.ofBijective toFun
      ⟨htoFunInjective, htoFunSurjective⟩)
  change Nat.card OutInv = 12
  calc
    Nat.card OutInv = Nat.card Pair := hcard.symm
    _ = 12 := hPairCard

end CFSG.GorensteinWalter
