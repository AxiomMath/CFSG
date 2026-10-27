module

public import CFSG.Quasithin.Recognition.St84.TransferSetup
public import CFSG.Quasithin.Recognition.GoldschmidtF112FA5Alt
public import CFSG.Quasithin.Recognition.F112J2Act
public import CFSG.GroupTheory.AlternatingFive.AutFixSylow
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.CoprimeHall
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Lemmas
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112SliceDefs
import CFSG.Quasithin.Recognition.St84.Gen.TransferL2Torus
import Mathlib.Tactic.Group
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.CharacterTheory.Blocks.Defs
public import CFSG.CharacterTheory.Wreathed.BrauerWongSylowCentralizer
public import CFSG.CharacterTheory.Wreathed.OddKernelSylowQuotient
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.GroupTheory.QuasiDihedralFusion.InvolutionCentralizer
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.Background.F6SolvableQuotient
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.Recognition.F112J2Reduce
public import CFSG.Quasithin.Recognition.F112RGold
public import CFSG.Quasithin.Recognition.ModelBridges
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped Pointwise commutatorElement

variable {H : Type} [Group H] [Finite H]

theorem f112saK_comm (L1 L2 S : Subgroup H) :
    f112saK L2 L1 S = f112saK L1 L2 S := by
  simp only [f112saK, f112saX1, f112saX2, bigB_comm]
  exact sup_comm _ _

theorem f112_commutator_zpow_mem_T_of_normal_left
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S)
    (hn : (S.subgroupOf (S ⊔ borelOf L1 S)).Normal)
    {k : H} (hkB : k ∈ borelOf L1 S) (hkK : k ∈ f112saK L1 L2 S)
    {s : H} (hs : s ∈ S) (i : ℤ) :
    ⁅s, k ^ i⁆ ∈ S ⊓ f112saK L1 L2 S := by
  have hSN : S ⊔ borelOf L1 S ≤ Subgroup.normalizer (S : Set H) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mp hn
  have hkN : k ^ i ∈ Subgroup.normalizer (S : Set H) :=
    (Subgroup.normalizer (S : Set H)).zpow_mem (hSN (Subgroup.mem_sup_right hkB)) i
  have hkKi : k ^ i ∈ f112saK L1 L2 S := (f112saK L1 L2 S).zpow_mem hkK i
  have hKnorm : s ∈ Subgroup.normalizer (f112saK L1 L2 S : Set H) :=
    f112sa_bigB_le_normalizer_K hF ((le_sup_right : S ≤ bigB L1 L2 S) hs)
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have hconj : k ^ i * s⁻¹ * (k ^ i)⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp hkN s⁻¹).mp (S.inv_mem hs)
    have heq : ⁅s, k ^ i⁆ = s * (k ^ i * s⁻¹ * (k ^ i)⁻¹) := by
      rw [commutatorElement_def]
      simp only [mul_assoc]
    rw [heq]
    exact S.mul_mem hs hconj
  · have hconj : s * k ^ i * s⁻¹ ∈ f112saK L1 L2 S :=
      (Subgroup.mem_normalizer_iff.mp hKnorm (k ^ i)).mp hkKi
    have heq : ⁅s, k ^ i⁆ = (s * k ^ i * s⁻¹) * (k ^ i)⁻¹ := by
      rw [commutatorElement_def]
    rw [heq]
    exact Subgroup.mul_mem _ hconj (Subgroup.inv_mem _ hkKi)

theorem f112_commutator_mem_T_of_normal_left
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S)
    (hn : (S.subgroupOf (S ⊔ borelOf L1 S)).Normal)
    {k : H} (hkB : k ∈ borelOf L1 S) (hkK : k ∈ f112saK L1 L2 S)
    {s : H} (hs : s ∈ S) :
    ⁅s, k⁆ ∈ S ⊓ f112saK L1 L2 S := by
  simpa using
    f112_commutator_zpow_mem_T_of_normal_left (i := (1 : ℤ)) hF hn hkB hkK hs

theorem f112sa_orderOf_mk_pCore_eq_three {L : Subgroup H} {k : H} (hkL : k ∈ L)
    (hk3 : orderOf k = 3) :
    orderOf (QuotientGroup.mk (s := CFSG.Open.pCore 2 ↥L) ⟨k, hkL⟩) = 3 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set x : ↥L := ⟨k, hkL⟩ with hx
  have hord : orderOf x = 3 := by
    rw [hx, Subgroup.orderOf_mk, hk3]
  have hdiv : orderOf (QuotientGroup.mk (s := CFSG.Open.pCore 2 ↥L) x) ∣ 3 := by
    rw [← hord]
    exact orderOf_map_dvd (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L)) x
  rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with h | h
  · exfalso
    rw [orderOf_eq_one_iff] at h
    have hmem : x ∈ CFSG.Open.pCore 2 ↥L := (QuotientGroup.eq_one_iff x).mp h
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_orderOf_dvd_pow
      (⟨x, hmem⟩ : ↥(CFSG.Open.pCore 2 ↥L))
    have hx3 : orderOf (⟨x, hmem⟩ : ↥(CFSG.Open.pCore 2 ↥L)) = 3 := by
      rw [Subgroup.orderOf_mk]
      exact hord
    rw [hx3] at hn
    have h32 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hn
    norm_num at h32
  · exact h

theorem f112_exists_torus_X1 {L1 L2 S : Subgroup H} {m : ℕ} (hF : F112HypW L1 L2 S)
    (hm : 1 ≤ m) (h1 : IsL2Quot m (oTwoQuot ↥L1)) :
    ∃ D : Subgroup H, D ≤ f112saX1 L1 L2 S ⊓ borelOf L1 S ∧ Nat.card D = 2 ^ m - 1 := by
  classical
  obtain ⟨D, hDB, hDcard⟩ :=
    exists_le_normalizer_card_eq_of_isL2Quot (L := L1) (T := S ⊓ L1) hm h1 hF.1.h1.sylow
  have hDB1 : D ≤ borelOf L1 S := by simpa [borelOf] using hDB
  have hodd : Odd (2 ^ m - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow
      (Even.pow_of_ne_zero (a := (2 : ℕ)) even_two (by omega)) odd_one
  have hoddD : Odd (Nat.card D) := by rwa [hDcard]
  have hDo2 : D ≤ oTwoRes L1 := by
    intro d hd
    have hdL1 : d ∈ L1 := (Subgroup.mem_inf.mp (hDB hd)).1
    have hodd_d : Odd (orderOf d) := by
      refine Odd.of_dvd_nat hoddD ?_
      have h := orderOf_dvd_natCard (⟨d, hd⟩ : ↥D)
      rwa [Subgroup.orderOf_mk] at h
    exact Subgroup.subset_closure ⟨hdL1, orderOf d, hodd_d, pow_orderOf_eq_one d⟩
  refine ⟨D, ?_, hDcard⟩
  exact le_inf (le_inf hDo2 (hDB1.trans (le_sup_left.trans le_sup_left))) hDB1

theorem f112_exists_torus_X2 {L1 L2 S : Subgroup H} {n : ℕ} (hF : F112HypW L1 L2 S)
    (hn : 1 ≤ n) (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    ∃ D : Subgroup H, D ≤ f112saX2 L1 L2 S ⊓ borelOf L2 S ∧ Nat.card D = 2 ^ n - 1 := by
  obtain ⟨D, hD, hDcard⟩ :=
    f112_exists_torus_X1 (L1 := L2) (L2 := L1) hF.symm hn h2
  exact ⟨D, by simpa [f112saX1, f112saX2, bigB_comm] using hD, hDcard⟩

theorem f112_exists_orderThree_X1 {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S)
    (h1 : VA5 L1) :
    ∃ k : H, k ∈ f112saX1 L1 L2 S ∧ k ∈ borelOf L1 S ∧ orderOf k = 3 ∧
      k ∈ Subgroup.normalizer ((S ⊓ L1 : Subgroup H) : Set H) := by
  obtain ⟨D, hD, hD3⟩ := f112_exists_torus_X1 (m := 2) hF (by norm_num) h1
  replace hD3 : Nat.card D = 3 := hD3.trans (by norm_num)
  have hDne : D ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hD3
    exact absurd hD3 (by norm_num)
  obtain ⟨d, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hDne
  have hd3 : orderOf d = 3 := by
    apply orderOf_eq_prime
    · have h := pow_card_eq_one' (G := ↥D) (x := d)
      rwa [hD3] at h
    · exact hd1
  exact ⟨d, (hD d.2).1, (hD d.2).2, (Subgroup.orderOf_coe d).trans hd3, (hD d.2).2.2⟩

theorem f112_conjModPCore_left {L1 L2 S : Subgroup H} (hF : F112Hyp L1 L2 S) (h1 : VA5 L1)
    {k c : H} (hk : k ∈ borelOf L1 S) (hk3 : orderOf k = 3)
    (hck : c * k = k * c) (hcS : c ∈ S) :
    ∀ l ∈ L1, ⁅c, l⁆ ∈ pCoreOf 2 L1 := by
  classical
  obtain ⟨e1⟩ := h1
  obtain ⟨e2⟩ := CFSG.Quasithin.F112J2.nonempty_psl_four_equiv_alt5
  refine CFSG.GroupTheory.AlternatingFive.conjModPCore_eq_one_of_twoPow_of_normalizes_sylow
    (L := L1) (c := c) (e1.trans e2) (hF.1.h1.normalizes hcS) ?_ hF.1.h1.sylow ?_ hk.1 hck hk.2 ?_
  · obtain ⟨m, hm⟩ := hF.1.h1.pgroup ⟨c, hcS⟩
    exact ⟨m, by simpa using congrArg (fun x : ↥S => (x : H)) hm⟩
  · exact ((le_inf Subgroup.le_normalizer hF.1.h1.normalizes).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := S) (K := L1))) hcS
  · exact f112sa_orderOf_mk_pCore_eq_three hk.1 hk3

theorem f112_exists_mul_centralizer_mod_left_of_isL2Quot {L1 L2 S : Subgroup H} {m : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (hnorm : (S.subgroupOf (S ⊔ borelOf L1 S)).Normal) :
    ∀ s ∈ S, ∃ t ∈ S ⊓ f112saK L1 L2 S, ∃ c ∈ S,
      (∀ l ∈ L1, ⁅c, l⁆ ∈ pCoreOf 2 L1) ∧ s = t * c := by
  classical
  obtain ⟨D, hDX1B, hDcard⟩ := f112_exists_torus_X1 hF (by omega : 1 ≤ m) h1
  have hDB : D ≤ borelOf L1 S := hDX1B.trans inf_le_right
  have hDX1 : D ≤ f112saX1 L1 L2 S := hDX1B.trans inf_le_left
  have hDK : D ≤ f112saK L1 L2 S := hDX1.trans le_sup_left
  have hSN : S ⊔ borelOf L1 S ≤ Subgroup.normalizer (S : Set H) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mp hnorm
  have hDN : D ≤ Subgroup.normalizer (S : Set H) :=
    fun d hd => hSN (Subgroup.mem_sup_right (hDB hd))
  haveI : Subgroup.Normalizes D S := ⟨hDN⟩
  have hcommAct : commutatorAction (A := ↥D) (G := ↥S) ≤
      (S ⊓ f112saK L1 L2 S).subgroupOf S := by
    rw [commutatorAction_eq_closure]
    refine (Subgroup.closure_le (K := (S ⊓ f112saK L1 L2 S).subgroupOf S)).mpr ?_
    rintro x ⟨a, g, rfl⟩
    change g⁻¹ * (a • g) ∈ (S ⊓ f112saK L1 L2 S).subgroupOf S
    rw [Subgroup.mem_subgroupOf]
    have hcoe : ((g⁻¹ * (a • g) : ↥S) : H) =
        (g : H)⁻¹ * (a : H) * (g : H) * (a : H)⁻¹ := by
      simp [mul_assoc]
    have hgoal : ((g⁻¹ * (a • g) : ↥S) : H) = ⁅(g : H)⁻¹, (a : H)⁆ := by
      rw [hcoe, commutatorElement_def]
      simp only [mul_assoc, inv_inv]
    rw [hgoal]
    exact f112_commutator_mem_T_of_normal_left (s := (g : H)⁻¹) hF hnorm (hDB a.2) (hDK a.2)
      (S.inv_mem g.2)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsolv : Group.IsSolvable ↥S := by
    haveI : Group.IsNilpotent ↥S := hF.1.h1.pgroup.isNilpotent
    infer_instance
  have hodd : Odd (2 ^ m - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow
      (Even.pow_of_ne_zero (a := (2 : ℕ)) even_two (by omega)) odd_one
  have hcop : Nat.Coprime (Nat.card ↥D) (Nat.card ↥S) := by
    obtain ⟨k, hkS⟩ := hF.1.h1.pgroup.exists_card_eq
    rw [hDcard, hkS]
    exact ((Nat.coprime_two_left.mpr hodd).symm).pow_right k
  have hdecomp : fixedPointSubgroup ↥D ↥S ⊔
      commutatorAction (A := ↥D) (G := ↥S) = ⊤ :=
    CFSG.fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime hsolv hcop
  have hTN : S ≤ Subgroup.normalizer ((S ⊓ f112saK L1 L2 S : Subgroup H) : Set H) :=
    (le_inf Subgroup.le_normalizer ((le_sup_right : S ≤ bigB L1 L2 S).trans
      (f112sa_bigB_le_normalizer_K hF))).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := S) (K := f112saK L1 L2 S))
  haveI : (commutatorAction (A := ↥D) (G := ↥S)).Normal :=
    (commutatorAction_normal_and_invariant (A := ↥D) (G := ↥S)).1
  intro s hs
  have hmem : (⟨s, hs⟩ : ↥S) ∈ fixedPointSubgroup ↥D ↥S ⊔
      commutatorAction (A := ↥D) (G := ↥S) := by
    rw [hdecomp]
    exact Subgroup.mem_top _
  obtain ⟨c, hc, d, hd, hcd⟩ := (Subgroup.mem_sup_of_normal_right).mp hmem
  have hck : ∀ a ∈ D, (c : H) * (a : H) = (a : H) * (c : H) := by
    intro a ha
    have hcA : (⟨a, ha⟩ : ↥D) • c = c := hc ⟨a, ha⟩
    have hconj : (a : H) * (c : H) * (a : H)⁻¹ = (c : H) := by
      have := congrArg (fun x : ↥S => (x : H)) hcA
      simpa using this
    have h : (a : H) * (c : H) = (c : H) * (a : H) := by
      calc (a : H) * (c : H) = ((a : H) * (c : H) * (a : H)⁻¹) * (a : H) := by group
        _ = (c : H) * (a : H) := by rw [hconj]
    exact h.symm
  have hdT : (d : H) ∈ S ⊓ f112saK L1 L2 S :=
    Subgroup.mem_subgroupOf.mp (hcommAct hd)
  have hc2 : ∃ k, (c : H) ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := hF.1.h1.pgroup ⟨(c : H), c.2⟩
    exact ⟨k, by simpa using congrArg (fun x : ↥S => (x : H)) hk⟩
  have hcL : (c : H) ∈ Subgroup.normalizer (L1 : Set H) := hF.1.h1.normalizes c.2
  have hcT : (c : H) ∈
      Subgroup.normalizer ((S ⊓ L1 : Subgroup H) : Set H) :=
    ((le_inf Subgroup.le_normalizer hF.1.h1.normalizes).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := S) (K := L1))) c.2
  have hcl : ∀ l ∈ L1, ⁅(c : H), l⁆ ∈ pCoreOf 2 L1 :=
    commutator_mem_pCoreOf_of_centralizes_torus (L := L1) (T := S ⊓ L1) (D := D)
      (n := m) hm h1 hF.1.h1.sylow (by simpa [borelOf] using hDB) hDcard hc2 hcL hcT hck
  refine ⟨(c : H) * (d : H) * (c : H)⁻¹, ?_, (c : H), c.2, hcl, ?_⟩
  · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact S.mul_mem (S.mul_mem c.2 hdT.1) (S.inv_mem c.2)
    · have hcB : (c : H) ∈ bigB L1 L2 S := (le_sup_right : S ≤ bigB L1 L2 S) c.2
      exact (Subgroup.mem_normalizer_iff.mp
        (f112sa_bigB_le_normalizer_K hF hcB) (d : H)).mp hdT.2
  · have hcdH : s = (c : H) * (d : H) := by
      have h := congrArg (fun x : ↥S => (x : H)) hcd
      simpa using h.symm
    rw [hcdH]
    group

theorem f112_exists_mul_centralizer_mod_right_of_isL2Quot {L1 L2 S : Subgroup H} {m : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (h2 : IsL2Quot m (oTwoQuot ↥L2))
    (hnorm : (S.subgroupOf (S ⊔ borelOf L2 S)).Normal) :
    ∀ s ∈ S, ∃ t ∈ S ⊓ f112saK L1 L2 S, ∃ c ∈ S,
      (∀ l ∈ L2, ⁅c, l⁆ ∈ pCoreOf 2 L2) ∧ s = t * c := by
  have hK : f112saK L2 L1 S = f112saK L1 L2 S := f112saK_comm L1 L2 S
  intro s hs
  obtain ⟨t, ht, c, hc, hcl, hsc⟩ :=
    f112_exists_mul_centralizer_mod_left_of_isL2Quot (L1 := L2) (L2 := L1) hF.symm hm h2 hnorm
      s hs
  exact ⟨t, by simpa [hK] using ht, c, hc, hcl, hsc⟩

end CFSG.Quasithin.F112R.St84
