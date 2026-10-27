module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_4Aux
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdGen
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.S152Stmts
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Blueprint
open CFSG.QuasithinUnique.Ch1
open scoped commutatorElement Pointwise

namespace S152U

@[expose] def HasSectionIso {G : Type} [Group G] (X : Subgroup G) (Y : Type) [Group Y] : Prop :=
  ∃ (A : Subgroup G) (N : Subgroup ↥A) (_ : N.Normal), A ≤ X ∧ Nonempty ((↥A ⧸ N) ≃* Y)

theorem HasSectionIso.mono {G : Type} [Group G] {X X' : Subgroup G} {Y : Type} [Group Y]
    (h : HasSectionIso X Y) (hXX' : X ≤ X') : HasSectionIso X' Y := by
  obtain ⟨A, N, hN, hAX, e⟩ := h
  exact ⟨A, N, hN, hAX.trans hXX', e⟩

theorem oPrimeResidualOf_mono_aux {G : Type} [Group G] (p : ℕ) {X Y : Subgroup G} (h : X ≤ Y) :
    oPrimeResidualOf p X ≤ oPrimeResidualOf p Y :=
  Subgroup.closure_mono fun _ hx => ⟨h hx.1, hx.2⟩

theorem centerOf_eq_pCoreOf_aux {G : Type} [Group G] [Finite G] {I K : Subgroup G}
    (hI : oddCoreIn I = ⊥) (hK : IsComponentIn K I) : centerOf K = pCoreOf 2 K := by
  have hq := BenderBranch.isQuasisimple_of_isComponentIn hK
  have hKK : IsComponentIn K K := Id2519.isComponentIn_self hq
  apply le_antisymm
  ·
    have h2 : IsPGroup 2 (centerOf K) := by
      intro x
      have hxK : (x : G) ∈ K := x.2.1
      have hxc : ∀ w ∈ K, w * (x : G) = (x : G) * w := fun w hw =>
        Subgroup.mem_centralizer_iff.mp x.2.2 w hw
      obtain ⟨k, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd
        (orderOf_pos (x : G)).ne'
      have hy : (x : G) ^ 2 ^ k ∈ oddCoreIn I := by
        refine Unc25G2.mem_oddCoreIn_of_central_odd hK (Subgroup.pow_mem K hxK _)
          (fun w hw => (Commute.pow_right (hxc w hw) _).eq) ?_
        have hdvd : orderOf ((x : G) ^ 2 ^ k) ∣ m := by
          refine orderOf_dvd_of_pow_eq_one ?_
          rw [← pow_mul, ← hord]
          exact pow_orderOf_eq_one _
        exact Odd.of_dvd_nat hm hdvd
      rw [hI, Subgroup.mem_bot] at hy
      exact ⟨k, Subtype.ext (by simpa using hy)⟩
    exact le_pCoreOf_of_le_normalizer 2 inf_le_left (fun g hg =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg,
        normalizer_le_normalizer_centralizer K (Subgroup.le_normalizer hg)⟩) h2
  · intro x hx
    have hcomm := Unc25G2.commutator_pCoreOf_eq_bot hKK
    have hle : K ≤ Subgroup.centralizer (pCoreOf 2 K : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    refine Subgroup.mem_inf.mpr ⟨pCoreOf_le 2 K hx, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (Subgroup.mem_centralizer_iff.mp (hle hw) x hx).symm

end S152U

variable {G : Type} [Group G] [Finite G]

structure Tail15215Cfg (I S Mi L L₀ K P : Subgroup G) (z : G) : Prop where
  sqtk : SQTKGroup ↥I
  odd : oddCoreIn I = ⊥
  sylow : IsSylowTwoOf S I
  zS : z ∈ S
  zC : z ∈ Subgroup.centralizer (S : Set G)
  z2 : z ^ 2 = 1
  z1 : z ≠ 1
  hMi : Mi = I ⊓ Subgroup.centralizer ({z} : Set G)
  Mi_ne : Mi ≠ I
  max : ∀ J : Subgroup G, Mi ≤ J → J ≤ I → J = Mi ∨ J = I
  comp : IsComponentIn L I
  center : centerOf L = pCoreOf 2 L
  L_not : ¬ L ≤ Mi
  comm : ⁅L, Subgroup.zpowers z⁆ = L
  cases : Lemma115Cases L z
  notLie : ¬ Lemma115LieCharTwo (↥L ⧸ Subgroup.center ↥L)
  L0 : L₀ = conjClosure L S
  L0n : (L₀.subgroupOf I).Normal
  I_eq : I = L₀ ⊔ Mi
  K_le : K ≤ Mi
  K_o2 : K = oTwoUpper K
  P_le : P ≤ K
  P_pgrp : IsPGroup 3 P
  P_card : Nat.card P = 9
  P_exp : ∀ x ∈ P, x ^ 3 = 1

@[expose] def Tail15215L2p : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I S Mi L L₀ K P : Subgroup G) (z : G),
    Tail15215Cfg I S Mi L L₀ K P z →
      (∃ p : ℕ, IsFermatOrMersennePrime p ∧ StatedClassicalModel L .PSL 2 p 1) →
        L ≤ Subgroup.centralizer (K : Set G)

@[expose] def Tail15215Rank : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I S Mi L L₀ K P : Subgroup G) (z : G),
    Tail15215Cfg I S Mi L L₀ K P z →
      ¬ (∃ p : ℕ, IsFermatOrMersennePrime p ∧ StatedClassicalModel L .PSL 2 p 1) →
        Nonempty (↥L ≃* NativeSporadic.Carrier .J4)

@[expose] def Tail15215J4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I S Mi L L₀ K P : Subgroup G) (z : G),
    Tail15215Cfg I S Mi L L₀ K P z → Nonempty (↥L ≃* NativeSporadic.Carrier .J4) →
      S152U.HasSectionIso (oPrimeResidualOf 3 (L ⊓ Subgroup.centralizer ({z} : Set G)))
        (NativeSporadic.Carrier .M22)

@[expose] def Tail15215Kc : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc K : Subgroup G), IsXi T K →
    (conjClosure K Mc = K ∨ Case15212ii T Mc (conjClosure K Mc) ∨
      Case15212iii T Mc (conjClosure K Mc) ∨ Case15212He T Mc (conjClosure K Mc)) →
      ¬ S152U.HasSectionIso (conjClosure K Mc) (NativeSporadic.Carrier .M22)

theorem normalizer_oTwoUpper_le_of_isUniqueM {H Mc : Subgroup G} (hU : IsUniqueM H Mc)
    (hchar : CharTwo H) (hK3 : 3 ∣ Nat.card ↥(oTwoUpper H)) :
    Subgroup.normalizer (oTwoUpper H : Set G) ≤ Mc := by
  have hHN : H ≤ Subgroup.normalizer (oTwoUpper H : Set G) := le_normalizer_oTwoUpper H
  have hcharK : CharTwo (oTwoUpper H) :=
    CharTwo.of_normal hchar (oTwoUpper_le H)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le H)).mpr hHN)
  have hKne : oTwoUpper H ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hK3
    exact absurd (Nat.le_of_dvd one_pos hK3) (by norm_num)
  have hO : pCoreOf 2 (oTwoUpper H) ≠ ⊥ := by
    intro hb
    have h1 : oTwoUpper H ⊓ Subgroup.centralizer (pCoreOf 2 (oTwoUpper H) : Set G) ≤
        pCoreOf 2 (oTwoUpper H) := hcharK
    rw [hb] at h1
    apply hKne
    rw [eq_bot_iff]
    intro x hx
    exact h1 ⟨hx, Subgroup.mem_centralizer_iff.2 fun y hy => by
      rw [show (y : G) = 1 from by simpa using hy, mul_one, one_mul]⟩
  have hHN' : H ≤ Subgroup.normalizer (pCoreOf 2 (oTwoUpper H) : Set G) :=
    hHN.trans (normalizer_le_normalizer_pCoreOf 2 _)
  have hCO : pCoreOf 2 (oTwoUpper H) ≤
      pCoreOf 2 (Subgroup.normalizer (pCoreOf 2 (oTwoUpper H) : Set G)) :=
    le_pCoreOf_of_le_normalizer Subgroup.le_normalizer le_rfl (pCoreOf_isPGroup 2 _)
  have hH' : InH H (Subgroup.normalizer (pCoreOf 2 (oTwoUpper H) : Set G)) :=
    ⟨hHN', fun hb => hO (le_bot_iff.mp (hb ▸ hCO))⟩
  obtain ⟨M', hM'⟩ := exists_inM_of_pCoreOf_ne_bot hH'.2
  have h1 : M' = Mc := hU.2 M' ⟨hM'.1, hH'.1.trans hM'.2⟩
  exact (normalizer_le_normalizer_pCoreOf 2 (oTwoUpper H)).trans (h1 ▸ hM'.2)

end CFSG.Quasithin
