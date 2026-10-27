module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerDefs
public import CFSG.Open.SplitBNPair
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.LocalAnalysis.UniquenessCase.UC22K108BN
import CFSG.GroupTheory.ConjNormalFaithful

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open Subgroup
open scoped commutatorElement

theorem le_of_commutator_eq_of_pGoodOut {X : Type*} [Group X] {L A B : Subgroup X} [L.Normal]
    (hcen : centralizer (L : Set X) = ⊥) {p : ℕ}
    (hgood : CFSG.AGLEmbedding.TwoGenInner.PGoodOut p ↥L) (hA : IsPGroup p A)
    (hAB : ⁅A, B⁆ = A) : A ≤ L := by
  classical
  obtain ⟨D, -, -, hDp, hcomm⟩ := hgood
  let psi : X →* MulAut ↥L := MulAut.conjNormal
  have hpowD : ∀ a ∈ A, ∃ k : ℕ, (psi a) ^ (p ^ k) ∈ D := by
    intro a ha
    obtain ⟨k, hk⟩ := hA ⟨a, ha⟩
    have hkX : a ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
    refine ⟨k, ?_⟩
    rw [← map_pow, hkX, map_one]
    exact D.one_mem
  have hAD : A ≤ D.comap psi := by
    rw [← hAB, Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_comap, map_commutatorElement]
    obtain ⟨k, hk⟩ := hpowD a ha
    have h1 : ⁅psi b, psi a⁆ ∈ D := hcomm (psi a) (psi b) ⟨k, hk⟩
    rw [← commutatorElement_inv]
    exact D.inv_mem h1
  intro x hx
  obtain ⟨k, hk⟩ := hA ⟨x, hx⟩
  have hkX : x ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hxpow : (psi x) ^ (p ^ k) = 1 := by rw [← map_pow, hkX, map_one]
  have hxI : psi x ∈ (MulAut.conj : ↥L →* MulAut ↥L).range :=
    hDp (psi x) (hAD hx) k (by rw [hxpow]; exact Subgroup.one_mem _)
  obtain ⟨l, hl⟩ := hxI
  have hxl : x = (l : X) :=
    Subgroup.conjNormal_injective_of_centralizer_eq_bot hcen (by
      change psi x = MulAut.conjNormal (l : X)
      rw [← hl, MulAut.conjNormal_val])
  rw [hxl]
  exact l.2

theorem isMulCommutative_of_le_normalizer_of_coprime {G : Type*} [Group G] {T H : Subgroup G}
    (hHN : H ≤ normalizer (T : Set G)) (hcop : Nat.Coprime (Nat.card T) (Nat.card H))
    (hab : IsMulCommutative (TauCeti.Subgroup.normalizerQuotient T)) :
    IsMulCommutative H := by
  have hTH : H ⊓ T = ⊥ := by
    rw [inf_comm]
    exact disjoint_iff.mp (disjoint_of_coprime_natCard hcop)
  let phi : H →* TauCeti.Subgroup.normalizerQuotient T :=
    (TauCeti.Subgroup.normalizerQuotientMk T).comp (Subgroup.inclusion hHN)
  have hphi : Function.Injective phi := by
    intro a b hab'
    have hab'' : TauCeti.Subgroup.normalizerQuotientMk T (Subgroup.inclusion hHN a) =
        TauCeti.Subgroup.normalizerQuotientMk T (Subgroup.inclusion hHN b) := hab'
    rw [TauCeti.Subgroup.normalizerQuotientMk_eq_iff_div_mem] at hab''
    have hdiv : (a : G) / (b : G) ∈ T := by simpa using hab''
    have hmem : (a : G) / (b : G) ∈ H ⊓ T := ⟨H.div_mem a.2 b.2, hdiv⟩
    rw [hTH, Subgroup.mem_bot] at hmem
    exact Subtype.ext (div_eq_one.mp hmem)
  have : IsMulCommutative (TauCeti.Subgroup.normalizerQuotient T) := hab
  refine IsMulCommutative.of_comm fun a b => hphi ?_
  rw [map_mul, map_mul]
  exact mul_comm' (phi a) (phi b)

theorem exists_abelian_le_sup_normalizer_of_splitBN {X : Type} [Group X] [Finite X]
    {L A S : Subgroup X} {B N : Subgroup ↥L} (hBN : CFSG.ASVolI.ChIJK.IsSplitBNPair 2 B N)
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S L)
    (hab : IsMulCommutative (TauCeti.Subgroup.normalizerQuotient (S.subgroupOf L)))
    (hAL : A ≤ L) (hA : Odd (Nat.card A)) (hAS : A ≤ normalizer (S : Set X)) :
    ∃ C : Subgroup X, IsMulCommutative C ∧ A ≤ C ∧ L ≤ S ⊔ (L ⊓ normalizer (C : Set X)) := by
  classical
  have : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
  have hSL : S ≤ L := hS.le
  obtain ⟨Q, hQ⟩ := hS.exists_sylow_eq_subgroupOf
  have hT : CFSG.QuasithinUnique.IsSylowTwoOf (S.subgroupOf L) ⊤ := by
    refine ⟨le_top, hS.isPGroup.comap_subtype, ?_⟩
    have hidx : ((S.subgroupOf L).subgroupOf (⊤ : Subgroup ↥L)).index =
        (S.subgroupOf L).index :=
      Subgroup.relIndex_top_right (H := S.subgroupOf L)
    rw [hidx, ← hQ]
    exact Q.not_dvd_index
  have hYT : (A.subgroupOf L) ≤ normalizer ((S.subgroupOf L) : Set ↥L) := by
    have h := Subgroup.subgroupOf_mono L hAS
    rwa [Subgroup.subgroupOf_normalizer_eq hSL] at h
  have hY : Odd (Nat.card (A.subgroupOf L)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv]
    exact hA
  obtain ⟨H, hYH, hHN, hHodd, hHgen⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22k108bn_exists_cartan hBN hT hYT hY
  have hcop : Nat.Coprime (Nat.card (S.subgroupOf L)) (Nat.card H) := by
    obtain ⟨n, hn⟩ := hT.2.1.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hHodd)
  have : IsMulCommutative H := isMulCommutative_of_le_normalizer_of_coprime hHN hcop hab
  refine ⟨H.map L.subtype, inferInstance, ?_, ?_⟩
  · have h1 := Subgroup.map_mono (f := L.subtype) hYH
    rwa [Subgroup.map_subgroupOf_eq_of_le hAL] at h1
  · have hnorm : (normalizer (H : Set ↥L)).map L.subtype ≤
        L ⊓ normalizer ((H.map L.subtype : Subgroup X) : Set X) := by
      refine le_inf (Subgroup.map_subtype_le (normalizer (H : Set ↥L))) ?_
      exact Subgroup.le_normalizer_map L.subtype
    have hmap := congrArg (fun K : Subgroup ↥L => K.map L.subtype) hHgen
    rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype,
      Subgroup.map_subgroupOf_eq_of_le hSL] at hmap
    calc L = S ⊔ (normalizer (H : Set ↥L)).map L.subtype := hmap.symm
      _ ≤ S ⊔ (L ⊓ normalizer ((H.map L.subtype : Subgroup X) : Set X)) :=
        sup_le_sup (le_refl S) hnorm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
