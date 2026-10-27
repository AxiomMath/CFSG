module

public import CFSG.Quasithin.EmptyFaithful.S151CLG2Lift
public import CFSG.Quasithin.EmptyFaithful.S151S4E
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtL2BlockType
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParGen
public import CFSG.Quasithin.Vol2.Ch12Sec8OneCComp

public section

namespace CFSG.Quasithin.CLG2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.QuasithinUnique.Vol2Native.L239

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G]

structure RankTwoPar (Y : Type) [Group Y] (U : Subgroup Y) (P : Fin 2 → Subgroup Y) : Prop where
  pkg : Rk2.Rank2Pkg Y U P
  inv : ∀ α : MulAut Y, U.map α.toMonoidHom = U → ∀ j, (P j).map α.toMonoidHom = P j
  good : ∀ j, GoodLocal (P j)

theorem no_two_power_quotient {K : Subgroup G} (hKp : ⁅K, K⁆ = K) (N : Subgroup ↥K) [N.Normal]
    (hN : IsPGroup 2 (↥K ⧸ N)) : N = ⊤ := by
  have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hKp
  have : Group.IsSolvable (↥K ⧸ N) := by
    have := hN.isNilpotent
    infer_instance
  have : Group.IsPerfect (↥K ⧸ N) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  have := CFSG.ComponentClassification.SolvableKernelContainment.perfect_solvable_subsingleton
    (G := ↥K ⧸ N)
  exact QuotientGroup.subsingleton_iff.mp this

theorem mem_lFamilyOf_of_normalized {T Mc M Z₁ Z₂ V₁ V₂ L K : Subgroup G}
    (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L) (hKL : K ≤ L) (hKp : ⁅K, K⁆ = K)
    (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hSK : s1516 T Z₁ ≤ Subgroup.normalizer (K : Set G)) :
    K ∈ lFamilyOf (g1_1516 Z₁) (s1516 T Z₁) := by
  have hKG : K ≤ g1_1516 Z₁ := hKL.trans hc.hL.mem.1
  have hS := s1516_le_g1 T Z₁
  have hKS : K ⊔ s1516 T Z₁ ≤ g1_1516 Z₁ := sup_le hKG hS
  have hXK : K ⊔ s1516 T Z₁ ≤ Subgroup.normalizer (K : Set G) :=
    sup_le Subgroup.le_normalizer hSK
  have hsyl : IsSylowTwoOf (s1516 T Z₁) (K ⊔ s1516 T Z₁) :=
    A4.isSylowTwoOf_mono hc.h18.four le_sup_right hKS
  have hcomp : K ∈ cComp (K ⊔ s1516 T Z₁) :=
    H13.mem_cComp_of_quasisimple_quotient (no_two_power_quotient hKp) hKq
      (A3.subnormal_of_normal le_sup_left
        ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hXK))
  have hpc : pCoreOf 2 (g1_1516 Z₁) ≠ ⊥ := hc.ctx.setting.pCore_g1_ne_bot hc.ctx.qtfe hc.ctx.mf
  refine ⟨hKG, hc.h18.four.2.1, hcomp, hsyl.2.2, ?_⟩
  intro h
  apply hpc
  have h1 : pCoreOf 2 (g1_1516 Z₁) ≤ s1516 T Z₁ := pCoreOf_le_of_isSylowTwoOf hc.h18.four
  have h2 : pCoreOf 2 (g1_1516 Z₁) ≤ pCoreOf 2 (K ⊔ s1516 T Z₁) :=
    le_pCoreOf_of_le_normalizer 2 (h1.trans le_sup_right)
      (hKS.trans (le_normalizer_pCoreOf 2 (g1_1516 Z₁))) (pCoreOf_isPGroup 2 (g1_1516 Z₁))
  rw [h] at h2
  exact le_bot_iff.mp h2

theorem le_mZ_of_not_chi0 (h118 : TheoremC118) (h126 : TheoremC126) (h42 : AsB42)
    (hLJ : Input15120LJ) (h1416 : StageLemma1416) (h15 : StageLemma1515CE)
    {T Mc M Z₁ Z₂ V₁ V₂ L K X : Subgroup G} (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L)
    (hK : K ∈ lFamilyOf (g1_1516 Z₁) (s1516 T Z₁))
    (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) (hKchar : CharTwo K)
    (hKn : ∃ m : ℕ, 2 ≤ m ∧ IsPSL 2 2 m (↥K ⧸ CFSG.pCore 2 ↥K))
    (hSK : s1516 T Z₁ ≤ Subgroup.normalizer (K : Set G))
    (hKX : K ≤ X) (hKXn : (K.subgroupOf X).Normal) (hnX : ¬ HasChi0Block X) :
    K ≤ mZ1516 Mc Z₁ := by
  by_contra hKM
  have hq := hc.ctx.qtfe
  have hcK : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ K := ⟨hc.ctx, hc.h17, hc.h18, hc.h19, ⟨hK, hKq, hKM⟩⟩
  have hKnotM : ¬ K ≤ M :=
    lemma_15_1_20_one (h1416 G T Mc hq).1 hc.ctx.mf (h15 G T Mc M hq hc.ctx.mf hc.ctx.ce) hcK.hL
  obtain ⟨m, hm, hKm⟩ := hKn
  have hblock := S151S4.l2_isBlock_of_baum h118 h126 hcK hKnotM hKchar hm hKm
    ((C1GN.baum_le (s1516 T Z₁)).trans hSK)
  have htype := input15120L2BlockType_holds h42 hLJ G T Mc M Z₁ Z₂ V₁ V₂ K hcK hKchar
    ⟨m, hm, hKm⟩ hblock
  apply hnX
  refine ⟨K, ⟨hblock.1, hKX, ?_⟩, ?_⟩
  · exact (isSubnormal_iff_subgroupOf hKX).mp (A3.subnormal_of_normal hKX hKXn)
  · rcases htype with h5 | h2
    · exact Or.inr (Or.inr h5)
    · exact Or.inl h2

theorem false_of_rankTwoPar (h118 : TheoremC118) (h126 : TheoremC126) (h42 : AsB42)
    (hLJ : Input15120LJ) (h1416 : StageLemma1416) (h15 : StageLemma1515CE)
    {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G} (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L)
    (hSN : s1516 T Z₁ ≤ Subgroup.normalizer (L : Set G))
    {P : Fin 2 → Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)}
    (hP : RankTwoPar (↥L ⧸ CFSG.pCore 2 ↥L)
      (((s1516 T Z₁ ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) P) :
    False := by
  have hsyl : IsSylowTwoOf (s1516 T Z₁ ⊓ L) L := lemma_15_1_20_sylow hc.h18.four hc.hL
  have hSM : s1516 T Z₁ ≤ mZ1516 Mc Z₁ := s1516_le_mZ1516 hc.h18
  have hle : ∀ j, perfectCore (liftQ L (P j)) ≤ mZ1516 Mc Z₁ := by
    intro j
    obtain ⟨hchar2, hnochi⟩ := goodLocal_liftQ (hP.good j)
    have hSX : s1516 T Z₁ ≤ Subgroup.normalizer (liftQ L (P j) : Set G) :=
      normalizes_liftQ hSN (fun α hα => hP.inv α hα j)
    have hSK : s1516 T Z₁ ≤ Subgroup.normalizer (perfectCore (liftQ L (P j)) : Set G) :=
      hSX.trans (normalizer_le_normalizer_perfectCore _)
    obtain ⟨m, hm, hKm, hKq⟩ := perfectCore_liftQ_levi (L := L) (hP.pkg.levi j)
    have hmem := mem_lFamilyOf_of_normalized hc
      ((perfectCore_le _).trans (liftQ_le L _)) (perfectCore_perfect _) hKq hSK
    exact le_mZ_of_not_chi0 h118 h126 h42 hLJ h1416 h15 hc hmem hKq
      (CharTwo.of_normal hchar2 (perfectCore_le _) (perfectCore_normal _)) ⟨m, hm, hKm⟩ hSK
      (perfectCore_le _) (perfectCore_normal _) hnochi
  have hgen := le_sup_perfectCore_liftQ (L := L) (R := s1516 T Z₁) (A₀ := P 0) (A₁ := P 1)
    hP.pkg.sup_perfectCore_eq_top ((pCoreOf_le_of_isSylowTwoOf hsyl).trans inf_le_left)
  exact hc.hL.not_le (hgen.trans (sup_le (sup_le (hle 0) (hle 1)) (inf_le_left.trans hSM)))

end CFSG.Quasithin.CLG2
