module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBMExcl
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBU0
public import CFSG.Quasithin.Background.C48PfB
public import CFSG.Quasithin.Background.C48Asm

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.CosetGraph
open scoped commutatorElement Pointwise

abbrev uBig {G : Type} [Group G] (I K : Subgroup G) : Subgroup G :=
  omegaOneCenterOf (pCoreOf 2 (K ⊔ pCoreOf 2 I))

theorem two_pow_nine_le_card_vV {G : Type} [Group G] [Finite G]
    {T M L Mm I H K : Subgroup G} {m k : ℕ} (hd : NoSumBigData G T M L Mm I H K m k) :
    2 ^ 9 ≤ Nat.card ↥(vV T L) := by
  obtain ⟨-, -, -, hm, hmk, -, -, hs⟩ := hd
  have hc := C48.card_of_isSumOfNaturalModules_bot hs
  rw [ZMod.card, Fintype.card_fin] at hc
  have h3 : 3 ≤ m := by omega
  have h9 : 9 ≤ m * k := by nlinarith
  exact hc ▸ Nat.pow_le_pow_right (by norm_num) h9

theorem exists_directSum_of_nsb (hN31 : NotC31)
    (h22 : ∀ (G : Type) [Group G] [Finite G], ASC22Three G)
    (h27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (h51 : AsB51) (hI16 : AsI16Cover) (hA8 : AsI16CoverA8)
    {G : Type} [Group G] [Finite G] {T M L Mm I H K : Subgroup G} {m k : ℕ}
    (hd : NoSumBigData G T M L Mm I H K m k) :
    ∃ hU : IsElemAbelian 2 (uBig I K), ∃ n' j : ℕ, (n' = 4 ∨ n' = 5) ∧ 1 ≤ j ∧ j ≤ n' - 1 ∧
      @DirectSumOfCopies ↥(uBig I K) (commGroupOfElemAbelian hU) (autOn K (uBig I K))
        (@commV ↥(uBig I K) (commGroupOfElemAbelian hU) (autOn K (uBig I K))) ⊥
        (FFModel.nat (StatedSL n' (ZMod 2))) j := by
  have hc : Conf4212 G T M L I H K := hd.2.2.1
  rcases hc.described with ⟨hcomp, h31'⟩ | ⟨hKc, hCT, hqs, hKM, h41'⟩
  · exact (hN31 G T M L Mm I H K m k hd hcomp h31').elim
  · have h4 := c41Case4_of_conclusion hd h41'
    obtain ⟨hU, halt⟩ :=
      C48Pf.alt15127_autOn (h27 G) h51 hI16 hA8 hc.hypC28 hKc hCT hqs hKM h41' h4
    refine ⟨hU, ?_⟩
    have hred := C48Pf.isTwoReducedIn_U (h27 G) hc.hypC28 hKc hCT hqs hKM h41'
    have hKU : K ≤ Subgroup.normalizer ((uBig I K : Subgroup G) : Set G) :=
      le_sup_left.trans hred.2.1
    have hle := C48Pf.inf_centralizer_le (h27 G) hc.hypC28 hKc hCT hqs hKM h41' h4
    obtain ⟨hVUK, hVO⟩ := C48Pf.le_commutator (h22 G) (h27 G) hc.hypC28 hKc hCT hqs hKM h41' h4
    have hcc : conjClosure (perfectCore (L ⊓ H)) (H ⊓ M) = perfectCore (L ⊓ H) :=
      conjClosure_eq_self hc.LH_normal
    rw [hcc] at hVO
    have hVcomm : ⁅vV T L, perfectCore (L ⊓ H)⁆ = vV T L := by
      have := hc.hypC28.V_comm
      rwa [hcc] at this
    have hVU : vV T L ≤ uBig I K :=
      hVUK.trans (C48Pf.FMod.commutator_le_of_le_normalizer hKU)
    have hVL : (vV T L).subgroupOf (uBig I K) ≤
        @commV ↥(uBig I K) (commGroupOfElemAbelian hU) (autOn K (uBig I K)) := by
      have : IsMulCommutative ↥(uBig I K) := hU.1
      rw [commV_autOn_eq1527d hKU]
      intro v hv
      exact Subgroup.mem_subgroupOf.2 (hVUK (Subgroup.mem_subgroupOf.1 hv))
    have hPK : H ⊓ M ⊓ K ≠ K := fun hPK => hKM (by rw [← hPK]; exact inf_le_left)
    have hP₀P : perfectCore (L ⊓ H) ≤ H ⊓ M ⊓ K :=
      le_inf (le_of_mem_cComp hc.LH_mem) hc.LH_le
    have hPN : H ⊓ M ⊓ K ≤ Subgroup.normalizer (perfectCore (L ⊓ H) : Set G) :=
      inf_le_left.trans hc.LH_normal
    have hperf : ⁅perfectCore (L ⊓ H), perfectCore (L ⊓ H)⁆ = perfectCore (L ⊓ H) :=
      perfectCore_perfect _
    have hcard := two_pow_nine_le_card_vV hd
    have hsmall := fun h => C48Pf.FMod.card_le_of_alt123 (K := K) (U := uBig I K)
      (P := H ⊓ M ⊓ K) (P₀ := perfectCore (L ⊓ H)) (V := vV T L) hU hKU hle h4.2.1 hPK hP₀P hPN
      hperf hd.2.2.2.1 hd.2.2.2.2.2.2.1 hc.hypC28.V_ne hVU hVO hVcomm hVL h
    rcases halt with h | h | h | ⟨n', hn', j, hj1, hjn, hds⟩
    · have := hsmall (Or.inl h)
      omega
    · have := hsmall (Or.inr (Or.inl h))
      omega
    · have := hsmall (Or.inr (Or.inr h))
      omega
    · exact ⟨n', j, hn', hj1, hjn, hds⟩

end CFSG.Quasithin.H13.Ch4.NSB
