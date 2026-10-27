module

public import CFSG.Quasithin.EmptyFaithful.S151CLJ4Def
public import CFSG.Quasithin.EmptyFaithful.S151CLJ4Hj
public import CFSG.Quasithin.EmptyFaithful.S151CLJ4Nrm
public import CFSG.Quasithin.EmptyFaithful.S151CLJ4Fix
public import Certificates.Kernel.J4Count.StarsBase2

public section

namespace CFSG.Quasithin.J4Local

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs
open CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem exists_local_of_isSporadic_j4
    {L R : Subgroup G}
    (hLq : CFSG.Open.IsQuasisimple ↥L) (hR2 : IsPGroup 2 ↥R)
    (hRN : R ≤ Subgroup.normalizer (L : Set G)) (hS : IsSylowTwoOf (R ⊓ L) L)
    (hne : ¬ L ≤ Subgroup.centralizer (centerOf (R ⊓ L) : Set G))
    (hJ4 : IsSporadic .J4 (↥L ⧸ CFSG.pCore 2 ↥L)) :
    ∃ K : Subgroup G, K ≤ L ∧ ⁅K, K⁆ = K ∧ R ≤ Subgroup.normalizer (K : Set G) ∧
      K ∈ cComp (K ⊔ R) ∧ ¬ 2 ∣ (R.subgroupOf (K ⊔ R)).index ∧ CharTwo K ∧
      IsSporadic .M24 (↥K ⧸ CFSG.pCore 2 ↥K) ∧
      K ⊔ (L ⊓ Subgroup.centralizer (centerOf (R ⊓ L) : Set G)) = L := by
  obtain ⟨e⟩ := hJ4
  have hM := j4Facts.mat
  have e1 : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥J := e.trans (seedEquiv hM)
  have hθ := @exists_hom_of_equiv ↥L ↥J _ _ (CFSG.pCore 2 ↥L) _ e1
  obtain ⟨θ0, hθ0, hker⟩ := hθ
  have hLperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.1 ⟨hLq.1⟩
  have hkerc : CFSG.pCore 2 ↥L ≤ Subgroup.center ↥L := pCore_le_center_of_quasisimple hLq
  have hN2 : IsPGroup 2 ↥((Eg uJ 11).subgroupOf Hj) :=
    A4.isPGroup_subgroupOf_of_le Eg_le_Hj (isPGroup_Eg (elem_uJ hM))
  have hmain := exists_local_of_canonical hLperf hRN hR2 hS hne θ0 hθ0 hker hkerc P0 Hj
    p0_isPGroup p0_index_odd P0_le_Hj hj_canonical hj_perfect goodLocal_Hj
    ((Eg uJ 11).subgroupOf Hj) hN2 isSimpleGroup_Hj_quotient (isCoatom_Hj j4Facts)
    fun W hW _ => hgen_J4 W hW
  obtain ⟨K, hKL, hKperf, hKR, hKc, hodd, hchar, ⟨e3⟩, hKC⟩ := hmain
  obtain ⟨e2⟩ := hjQuot_equiv
  exact ⟨K, hKL, hKperf, hKR, hKc, hodd, hchar, ⟨e3.trans e2⟩, hKC⟩

theorem pCoreOf_sup_ne_bot {K R : Subgroup G} (hK : K ≠ ⊥) (hc : CharTwo K)
    (hR : R ≤ Subgroup.normalizer (K : Set G)) : pCoreOf 2 (K ⊔ R) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : pCoreOf 2 K ≠ ⊥ := by
    intro h0
    apply hK
    have hc' : K ⊓ Subgroup.centralizer (pCoreOf 2 K : Set G) ≤ pCoreOf 2 K := hc
    rw [h0] at hc'
    rw [eq_bot_iff]
    intro k hk
    refine hc' ⟨hk, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    have : h = 1 := Subgroup.mem_bot.1 hh
    rw [this]
    simp
  intro h0
  apply hne
  rw [eq_bot_iff, ← h0]
  refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans le_sup_left) ?_
    (pCoreOf_isPGroup 2 K)
  exact sup_le (le_normalizer_pCoreOf 2 K) (hR.trans (normalizer_le_normalizer_pCoreOf 2 K))

end CFSG.Quasithin.J4Local

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem input15120J4Local_holds
    (h38 : A38ForSQTK) : Input15120J4Local := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp hJ4
  have hSyl : IsSylowTwoOf (s1516 T Z₁ ⊓ L) L := lemma_15_1_20_sylow hc.h18.four hc.hL
  have hfix : AutFixOn L (s1516 T Z₁ ⊓ L) := autFixOn_of_isSporadic_j4 hcomp.2.2 hSyl hJ4
  have hne := s151s_not_le_centralizer hc hcomp hfix
  have hSN : s1516 T Z₁ ≤ Subgroup.normalizer (L : Set G) :=
    (s1516_le_g1 T Z₁).trans (J4Excl.g1_le_normalizer_of_isSporadic_j4 h38 hc hcomp hJ4)
  have hR2 : IsPGroup 2 ↥(s1516 T Z₁) := hc.h18.four.2.1
  obtain ⟨K, hKL, -, hKR, hKc, hodd, hchar, hquot, hKC⟩ :=
    J4Local.exists_local_of_isSporadic_j4 hcomp.2.2 hR2 hSN hSyl hne hJ4
  exact ⟨K, ⟨hKL.trans hcomp.1, hR2, hKc, hodd,
    J4Local.pCoreOf_sup_ne_bot hKc.1 hchar hKR⟩, hchar, hquot, hKC⟩

end CFSG.Quasithin
