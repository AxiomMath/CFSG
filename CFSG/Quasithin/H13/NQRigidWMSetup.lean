module

public import CFSG.Quasithin.Background.FFStarOffenderMoving
public import CFSG.Quasithin.H13.NQBlockWitnessSingleton

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.InternalSec CFSG.QuasithinUnique
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL scalars)
open scoped IsMulCommutative commutatorElement

section PSL

variable {s : ℕ} [Fact s.Prime]

theorem card_scalars_two_zmod (hs : s ≠ 2) : Nat.card (scalars 2 (ZMod s)) = 2 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center,
    Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 2)).toEquiv,
    Fintype.card_fin]
  exact (IsPrimitiveRoot.neg_one s hs).card_rootsOfUnity

theorem card_projectiveSL_two_zmod (hs : s ≠ 2) :
    s * (s ^ 2 - 1) = 2 * Nat.card (projectiveSL 2 (ZMod s)) := by
  have h1 := (scalars 2 (ZMod s)).card_eq_card_quotient_mul_card_subgroup
  rw [card_scalars_two_zmod hs,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), Nat.card_zmod] at h1
  have hI : Finset.Icc 2 2 = {2} := rfl
  rw [hI, Finset.prod_singleton] at h1
  rw [mul_comm 2]
  simpa using h1

theorem isSimpleGroup_projectiveSL_two_zmod (hs : 5 ≤ s) :
    IsSimpleGroup (projectiveSL 2 (ZMod s)) := by
  have h4 : 4 ≤ Nat.card (ZMod s) := by
    rw [Nat.card_zmod]
    omega
  have := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  exact (QuotientGroup.quotientMulEquivOfEq
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 2 (ZMod s))).isSimpleGroup

end PSL

section Simple

theorem exists_noncomm_of_isSimpleGroup {X : Type*} [Group X] [Finite X] [IsSimpleGroup X]
    {s : ℕ} (hs : s.Prime) (hdvd : s ∣ Nat.card X) (hne : Nat.card X ≠ s) :
    ∃ a b : X, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  have : Fact s.Prime := ⟨hs⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' s hdvd
  have hn : (zpowers g).Normal :=
    ⟨fun n _ x => by rwa [hc x n, mul_inv_cancel_right]⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (zpowers g) with h | h
  · have : g = 1 := by
      have := mem_zpowers g
      rw [h, mem_bot] at this
      exact this
    rw [this, orderOf_one] at hg
    exact hs.one_lt.ne' hg.symm
  · apply hne
    rw [← hg, ← Nat.card_zpowers, h, card_top]

theorem isQuasisimple_of_simple_nonab {Y : Type*} [Group Y] [IsSimpleGroup Y]
    (hnc : ∃ a b : Y, a * b ≠ b * a) : CFSG.IsQuasisimple Y := by
  have hZ : center Y = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Y) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      exact hab ((mem_center_iff.mp (h ▸ mem_top b)) a)
  have hperf : Group.IsPerfect Y := by
    refine ⟨?_⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Y) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      have : ⁅a, b⁆ ∈ commutator Y := commutator_mem_commutator (mem_top a) (mem_top b)
      rw [h, mem_bot, commutatorElement_def] at this
      exact hab (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp this))
    · exact h
  let e : Y ⧸ center Y ≃* Y :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨hperf, e.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := hnc
  refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  have := congrArg e h
  simpa using this

theorem ne_bot_of_isSimpleGroup {Ω : Type*} [Group Ω] {K : Subgroup Ω} (hK : IsSimpleGroup ↥K) :
    K ≠ ⊥ := by
  intro h
  obtain ⟨x, y, hxy⟩ := hK.toNontrivial.exists_pair_ne
  apply hxy
  have hx : (x : Ω) = 1 := (eq_bot_iff_forall K).mp h (x : Ω) x.2
  have hy : (y : Ω) = 1 := (eq_bot_iff_forall K).mp h (y : Ω) y.2
  exact Subtype.ext (hx.trans hy.symm)

theorem commutator_eq_or_eq_bot_of_simple {Ω : Type*} [Group Ω] {K A : Subgroup Ω}
    (hK : IsSimpleGroup ↥K) (hA : A ≤ normalizer (K : Set Ω)) : ⁅K, A⁆ = K ∨ ⁅K, A⁆ = ⊥ :=
  CFSG.Quasithin.AutOn.commutator_eq_or_eq_bot_of_simple hK hA

end Simple

section Vc

variable {G : Type} [Group G] [Finite G]

theorem qtnqVc_isTwoReducedIn (M : Subgroup G) : IsTwoReducedIn M (qtnqVc M) := by
  refine isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 ⟨map_subtype_le _, ?_⟩
  have hsub : (qtnqVc M).subgroupOf M = primeReducedAggregate (↥M) 2 :=
    comap_map_eq_self_of_injective M.subtype_injective _
  rw [hsub]
  exact isPrimeReduced_primeReducedAggregate 2

instance qtnqVc_isMulCommutative (M : Subgroup G) : IsMulCommutative ↥(qtnqVc M) :=
  (qtnqVc_isTwoReducedIn M).2.2.1.1

variable {T L M : Subgroup G}

theorem sqtkGroup_of_qtnq (h : QTNQ T L M) : SQTKGroup ↥M := by
  have := h.simple
  exact sqtkGroup_of_localSQTK (qtkeCore_of_cat h.nonabelian h.qtke).1
    (NQBlock.pCoreOf_ne_bot_of_maxTwoLocal h.max_two_local)

end Vc

section AutOn

variable {G : Type} [Group G] {L W : Subgroup G}

theorem ker_autOnHom_eq (hLW : L ≤ normalizer (W : Set G))
    (hC : L ⊓ centralizer (W : Set G) = (CFSG.solvableRadical L).map L.subtype) :
    (autOnHom hLW).ker = CFSG.solvableRadical L := by
  ext x
  rw [mem_ker_autOnHom]
  constructor
  · intro hx
    have h1 : (x : G) ∈ L ⊓ centralizer (W : Set G) := ⟨x.2, hx⟩
    rw [hC] at h1
    obtain ⟨y, hy, hyx⟩ := h1
    have : y = x := Subtype.ext hyx
    rwa [← this]
  · intro hx
    have h1 : (x : G) ∈ L ⊓ centralizer (W : Set G) := by
      rw [hC]
      exact ⟨x, hx, rfl⟩
    exact h1.2

@[expose] noncomputable def radQuotEquivAutOn (hLW : L ≤ normalizer (W : Set G))
    (hC : L ⊓ centralizer (W : Set G) = (CFSG.solvableRadical L).map L.subtype) :
    (L ⧸ CFSG.solvableRadical L) ≃* autOn L W :=
  (QuotientGroup.quotientMulEquivOfEq (ker_autOnHom_eq hLW hC).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (autOnHom_surjective hLW))

end AutOn

section Offender

variable {G : Type} [Group G] [Finite G]

theorem exists_offender_of_thompson {T L Y W : Subgroup G} [IsMulCommutative ↥W]
    (hT : IsSylowTwoOf T Y) (hTL : T ≤ normalizer (L : Set G)) (hred : IsTwoReducedIn Y W)
    (hLW : L ≤ normalizer (W : Set G)) (hsimp : IsSimpleGroup ↥(autOn L W))
    (hJ : L = ⁅L, thompsonJ T⁆) :
    ∃ A : Subgroup G, IsMaxElemAbelian T A ∧
      IsFFStarOffender (autOn Y W) (autOn A W) ∧ ⁅autOn L W, autOn A W⁆ = autOn L W :=
  CFSG.Quasithin.AutOn.exists_isFFStarOffender_moving hT hTL hred hLW hsimp hJ

end Offender

end CFSG.Quasithin.H13.NQRigid
