module

public import CFSG.RankThree.PartOne.K1327.Final
public import CFSG.RankThree.PartOne.Q1327T.MPerm3
public import CFSG.RankThree.PartOne.Q1327T.MCells
public import CFSG.RankThree.PartOne.Q1327R.Out9
import CFSG.RankThree.PartOne.Q1327.Out
import CFSG.RankThree.PartOne.S12.Sec127

public section

namespace CFSG.RankThree.PartOne.Q1327T

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K1320
  CFSG.RankThree.PartOne.K1327 CFSG.RankThree.PartOne.Q1327
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

@[expose] def KF1327M : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G)
    (f r : ℕ) (R : Subgroup G) (s s' zs : MulAut E) (Jc : Subgroup G),
    Hyp G p A c L E f r R s s' zs → JcData p E c R s Jc →
    ∀ φ ∈ torusImage E Jc, ∃ e : E, φ e ≠ e⁻¹

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
  {f r : ℕ} {R : Subgroup G} {s s' zs : MulAut E}

theorem kf1327Q_of_leavesM
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : SchreierFor InCatalog) (hRe : Sec13Reinst) (hTwo : TwoActionInputs)
    (hFull : K156.Full106Stmt) (hSLB : N143.SectionListBound) (hI613 : N143.Item613ListIdx)
    (hBridge : N143.EvenListBridge) (hLS : KF1327S) (hM : KF1327M) (hLP5 : KF1327P5)
    (hLB : KF1327BM) (hLR9 : KF1327Row9) (hLOut : KF1327Out) : K1327.KF1327Q := by
  intro G _ _ p A c L E f h hF hF13 hT hEA hnL3 hf2 hpf hmodel hweyl r R hr hrf hRcard hRL hRE
    hRnorm s s' hs hsL hs' hs'L hKs hKs' hss' hcomm hRs hRs' zs hzs hzc hzL hmov hKz hzs_s hzs_s'
    hRz
  have H : Hyp G p A c L E f r R s s' zs :=
    ⟨h, hF, hF13, hT, hEA, hnL3, hf2, hpf, hmodel, hweyl, hr, hrf, hRcard, hRL, hRE, hRnorm, hs,
      hsL, hs', hs'L, hKs, hKs', hss', hcomm, hRs, hRs', hzs, hzc, hzL, hmov, hKz, hzs_s, hzs_s',
      hRz⟩
  have hp := h.prime
  have hp5 := Sec12Three.five_le h
  have hcard : Nat.card E = p ^ 3 := by rw [hEA]; exact h.A_card
  obtain ⟨Jc, hJ⟩ := exists_Jc hGA hS H
  obtain ⟨hq, hθ⟩ := Jc_isQuasisimple hGA hS hRe hTwo hFull H hJ
  obtain ⟨a, N, A₀, S, ha1, ha2, hN1, hN2, hN3, hN4, hA₀1, hA₀2, hA₀3, hS1, hS2, hS3, hS4, hS5⟩ :=
    hLS G p A c L E f r R s s' zs H
  have d : SDatum p E R s f a N A₀ S :=
    ⟨ha1, ha2, hN1, hN2, hN3, hN4, hA₀1, hA₀2, hA₀3, hS1, hS2, hS3, hS4, hS5⟩
  have hEven := evenLie_Jc hGA hS hRe hTwo hFull hSLB hI613 hBridge hLP5 H hJ d
  have hlist := list_Jc hSLB H hJ hq
  have hbase := t123Base_Jc hGA hS hRe hTwo hFull H hJ d.A₀_le d.A₀_elem d.A₀_card d.S_le d.S_ne
    d.S_two d.A₀_norm d.comm
  have hsolv : Group.IsSolvable ↥(torusImage E Jc) :=
    isSolvable_of_le_torusWeyl H (Sec127.torusImage_le_torusWeyl E Jc)
  have hneg := hM G p A c L E f r R s s' zs Jc H hJ
  have hirr := Jc_irreducible hGA H hJ
  have hsT : s ∈ torusImage E Jc := mem_torusImage_Jc H hJ (mem_clsOf_self p E s)
  have hsRef : IsAutReflection p E s := hs.1
  have hKJ : kZero p E s ≤ Jc := hJ.K_le s (mem_clsOf_self p E s)
  have hKle : kZero p E s ≤ Jc ⊓ Subgroup.centralizer (autFixedInG E s : Set G) :=
    le_inf hKJ (kZero_le_centralizer_fixed p E s)
  have hKθ := kZero_mem_thetaComponents_inf hp (KFAt.toLiftAt hKs).1 hKJ
  have hKmov : autMovedInG E s ≤ kZero p E s := hKs.2.2.2.1
  obtain ⟨f', hf'1, hf'p, hmodel'⟩ := hLB G p Jc A₀ E hbase hlist hEven hsolv hneg hirr
    ⟨s, kZero p E s, f, hsT, hsRef, hKle, hKθ, hKmov, hKs.2.1, hf2, hpf⟩
  have hf'2 : 2 ≤ f' := by
    by_contra hlt
    have hf : f' = 1 := by omega
    subst hf
    have hle := Nat.le_of_dvd (by norm_num) hf'p
    omega
  have hZJ : Subgroup.center ↥Jc = ⊥ :=
    psuFourEvenCenterTrivial_of_multipliers hGA ↥Jc f' hf'2 hq hmodel'
  have hK9 := hLR9 G p f' Jc E hp hp5 hf'2 hf'p hq hZJ hmodel' h.E_elem hJ.E_le hcard s
    (kZero p E s) hsT hsRef hKle hKθ hKmov
  have hff : f' = f := psl_two_deg_unique hK9 hKs.2.1
  rw [hff] at hmodel'
  rw [hff] at hf'p hf'2
  have hEmax : ∀ F : Subgroup G, IsElementaryAbelian p F → F ≤ Subgroup.centralizer (E : Set G) →
      E ≤ F → F = E := by
    intro F hF' hFc hEF
    exact h.E_max F hF' (by rw [← hEA]; exact hFc) hEF
  have hOut := hLOut G p f Jc E hp hp5 hf2 hpf hq hZJ hmodel' h.E_elem hJ.E_le hcard hEmax
  have hJle : Jof p R ≤ Jc := Jof_le_Jc_of_out H hJ hOut
  have hJeq : Jc = Jof p R := le_antisymm (Jc_le_Jof H hJ) hJle
  subst hJeq
  exact Equivariance.statedClassicalModel_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hθ).symm
    hmodel'

theorem kf1327Q_of_remM
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : SchreierFor InCatalog) (hRe : Sec13Reinst) (hTwo : TwoActionInputs)
    (hFull : K156.Full106Stmt) (hSLB : N143.SectionListBound) (hI613 : N143.Item613ListIdx)
    (hBridge : N143.EvenListBridge) (hP5 : KF1327P5) (hB : KF1327BM) (hRem : Row8U3Inspection ∧
        KF1327M) :
    K1327.KF1327Q :=
  kf1327Q_of_leavesM hGA hS hRe hTwo hFull hSLB hI613 hBridge
    (kf1327S_of_inspectionM hGA hS hSLB hRem.1) hRem.2 hP5 hB Q1327R.kf1327Row9_holds
    Q1327R.kf1327Out_holds

end CFSG.RankThree.PartOne.Q1327T
