module

public import Certificates.Kernel.Census.RuR.T
public import Certificates.Kernel.Census.RuR.N
public import Certificates.Kernel.Census.RuR.B
public import CFSG.Certificates.Kernel.Census.TreeProof
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicRuR
import all Certificates.Kernel.Census.RuR.Data
import all CFSG.Certificates.Kernel.Census.ToMain
import all CFSG.Certificates.Kernel.Census.ToMainConj
import all Certificates.Data.Kernel.Census.Packed
import all Certificates.Data.Kernel.Census.PackedConj
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Census.ConjSound
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.Certificates.Kernel.Spor.SiftEq
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
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.Ch1Local
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CertificateChecks.KernelCensus.RuR

open CFSG.KC.Census CFSG.ComponentClassification.RankTwoSporadic.Ru CFSG.Sporadic.RuSchreier
open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CertificateChecks.KernelSporSch

theorem nodes_all : ∀ i < d.nodes.size, nodeF i = true := by
  intro i hi
  rw [Nat.eq_of_beq_eq_true kNs] at hi
  by_cases h1 : i < 15
  · exact List.all_eq_true.1 kN0 i (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  by_cases h2 : i < 87
  · exact List.all_eq_true.1 kN15 i (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  by_cases h3 : i = 87
  · rw [h3]
    exact kN87
  · exact List.all_eq_true.1 kN88 i (List.mem_range'_1.2 ⟨by omega, by omega⟩)

theorem eqA_self (n : ℕ) (a : Array ℕ) : eqA n a a = true := by
  unfold eqA
  rw [allLt_iff]
  intro i _
  exact beq_self_eq_true _

theorem ru_census : ∃ (d : ConjDataP) (ps : List ℕ) (e0 : Array ℕ) (L : ℕ → ℕ) (pe : Array ℕ)
    (O ix : ℕ) (xw : List (List ℕ)) (wits : List (ℕ × ℕ × List (ℕ × List ℕ × List ℕ) × ℕ))
    (em yw : List ℕ), ruCheckR d ps e0 L pe O ix xw wits em yw = true := by
  obtain ⟨e1, e2, hid⟩ := SP.pid_good24 (n := 128) (w := 7) (by norm_num) (by norm_num)
  have G : SP.Good 128 7 := ⟨by norm_num, by norm_num, e1, e2⟩
  have C := SP.canonC_facts kCanon
  have hinW : ∀ P, canon1 128 7 P = true → pvalid 128 7 P = true →
      inWP P = (fun a => eqA 128 a (idA 128)) (unpackP 128 7 P) :=
    fun P hP _ => (SP.eqA_pid G hP).symm
  have htree := ptree_sound_proved (n := 128) (w := 7) (ps := ps)
    (inW := fun a => eqA 128 a (idA 128)) (inWP := inWP) (d := d) (e0 := e0)
    (by norm_num) (by norm_num) (by norm_num) kCanon kE0c hinW kPc kInv kTab kRl kR nodes_all
  have hppc : ∀ m, unpackP 128 7 (ppcA 128 7 d.xs m) = pcA 128 (d.xs.map (unpackP 128 7)) m ∧
      canon1 128 7 (ppcA 128 7 d.xs m) = true := fun m => SP.ppcA_eq G d.xs m C.xs
  have hE0 := kE0m
  simp only [Bool.and_eq_true] at hE0
  have he0s := hE0.1.1.1
  have hems := hE0.1.1.2
  have he00 := hE0.1.2
  have he01 := hE0.2
  have hbase : base = ruPS := rfl
  have hwi : wits.all (fun t => Nat.blt t.1 d.nodes.size) = true := kWi
  refine ⟨d, ps, e0, L, pe, O, ix, xw, wits, em, yw, ?_⟩
  unfold ruCheckR
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨htree, kPs⟩, kLen⟩, he0s⟩, hems⟩, ?_⟩, ?_⟩, ?_⟩, kInvL⟩, kPts⟩,
    kXl⟩, kXw⟩, hbase ▸ kRel⟩, kRes⟩, kCov⟩, ?_⟩, rfl⟩, kYw⟩, ?_⟩, ?_⟩, kPe⟩, ?_⟩, ?_⟩
  · rw [Nat.eq_of_beq_eq_true he00, (hppc _).1]
    exact eqA_self _ _
  · rw [Nat.eq_of_beq_eq_true he01, (hppc _).1]
    exact eqA_self _ _
  · refine List.all_eq_true.2 fun k hk => ?_
    have hk' : k < 18 := List.mem_range.1 hk
    have hL : L k = RuT4060.L (15 + k) := by
      have hb : Nat.blt k 18 = true := Nat.blt_eq.mpr hk'
      unfold L
      rw [hb]
      rfl
    have hf : (ruField4060 3)[k]! = ruArr4060 (15 + k) := by
      rw [ruField4060, getElem!_pos _ k (by simpa [ruLines4060] using hk'), Array.getElem_ofFn]
      rfl
    rw [hL, hf, RuLines.row4060 (by omega)]
    exact eqA_self _ _
  · refine List.all_eq_true.2 fun t ht => ?_
    have hw := List.all_eq_true.1 kWit t ht
    have hwl := List.all_eq_true.1 kWl t ht
    have hti := Nat.blt_eq.mp (List.all_eq_true.1 hwi t ht)
    unfold witF at hw
    simp only [Bool.and_eq_true, List.all_eq_true] at hw ⊢
    obtain ⟨⟨hme, hmt⟩, hwb⟩ := hw
    have hcn : maskCert 128 (d.nodes[t.1]!.basis.map (unpackP 128 7)) = cN[t.1]!.toMain 128 7 := by
      have := SP.cN_get G C.basis t.1
      rw [SP.map_get _ _ (by simpa using hti), SP.map_get _ _ hti] at this
      exact this
    have hmem : ∀ m, pmem cN[t.1]! (ppcA 128 7 d.xs m) = true →
        memA 128 (maskCert 128 (d.nodes[t.1]!.basis.map (unpackP 128 7)))
          (pcA 128 (d.xs.map (unpackP 128 7)) m) = true := by
      intro m hm
      have e := SP.memA_eq (c := cN[t.1]!) (SP.cN_canon G C.basis t.1) (hppc m).2
      rw [hcn, ← (hppc m).1]
      rw [e]
      exact hm
    refine ⟨⟨⟨?_, hmem _ hme⟩, fun f hf => hmem _ (hmt f hf)⟩, hbase ▸ hwb⟩
    intro f hf
    have := List.all_eq_true.1 hwl f hf
    simp only [Bool.and_eq_true, List.all_eq_true] at this
    exact this
  · have e : pe[0]! = RuT4060.L 0 := rfl
    have hr : ruE0[0]! = ruArr4060 0 := by simp [ruE0, ruA0A]
    rw [e, hr, RuLines.row4060 (by norm_num)]
    exact eqA_self _ _
  · have e : pe[1]! = RuEndR.F 0 := rfl
    rw [e, RuEnd.r_eq]
    exact eqA_self _ _
  · have := kE0
    simp only [Bool.and_eq_true] at this
    exact this.1
  · have := kE0
    simp only [Bool.and_eq_true] at this
    exact this.2

end CertificateChecks.KernelCensus.RuR

end
