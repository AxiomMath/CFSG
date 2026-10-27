module

public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveDataResDefs
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLDType
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseLabel
import CFSG.LocalAnalysis.StandardType.GGTwA5ThreeFrame
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylRest5
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpCount
import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthWeylOrdD
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsuAux
import CFSG.LocalAnalysis.StandardType.MarkingClassical
import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Q2ProofFinal
import CFSG.LocalAnalysis.StandardType.GGStdSubExist
import CFSG.LocalAnalysis.StandardType.GGTypeACompatDiagRank
import CFSG.LocalAnalysis.StandardType.GGNsq2Strict
import CFSG.LocalAnalysis.StandardType.GGAutomizerJoinInduced
import CFSG.LocalAnalysis.StandardType.GGTBTorDatum

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem nsQ2U62_weyl
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hFix : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer L Bs, φ b = b) → (b : G) ∈ Subgroup.zpowers x)
    (hlab : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) p Bs L) :
    p = 3 ∧ GGWeylOfType 3 (CoxeterMatrix.A 5) (ggAutomizer L Bs) ∧ Nat.card Bs ≤ 3 ^ 6 := by
  have hp3 : p = 3 := by
    obtain ⟨hp, -, -, -, -⟩ := hcfg.tableB_facts
    obtain ⟨-, lab, -, hraw⟩ := hlab
    obtain ⟨R, _, I, F, -, -, θ, hP⟩ := largeEvenRawDatum_exists hraw
    obtain ⟨⟨hrow, hn1, -⟩, -, -⟩ := hP
    refine (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp ?_
    have h := hrow.2
    rw [hn1] at h
    norm_num at h
    exact h
  subst hp3
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hL : GGInnerDiagOnLabel (fun p lab => lab.tag = .twA ∧ lab.rank = 5 ∧ p = 3 ∧
      3 ∣ 2 ^ lab.n + 1) 3 Bs L := by
    refine largeEvenMarking_mono (fun lab R _ I F θ hP => ?_) hlab
    obtain ⟨⟨hrow, hn1, hr5⟩, hN', hBsI⟩ := hP
    have hdvd : 3 ∣ 2 ^ lab.n + 1 := by
      simp [hn1]
    refine ⟨⟨?_, hr5, rfl, hdvd⟩, hN', hBsI⟩
    rcases hrow.1 with ⟨htw, -⟩ | ⟨-, hr3⟩
    · exact htw
    · omega
  have hM : GGInnerDiagOnLab GGUnitDvd63Label 3 Bs L := by
    refine largeEvenMarking_mono (fun lab R _ I F θ hP => ?_) hL
    obtain ⟨⟨htw, hr5, -, hdvd⟩, hN', hBsI⟩ := hP
    exact ⟨⟨⟨htw, by omega, hdvd, by omega⟩, hr5, rfl⟩,
      Or.inr (Or.inl ⟨by simp [LargeEvenUntwisted, htw], by simp [htw], hdvd⟩), hN', hBsI⟩
  have hr : ∀ hN : Bs ≤ Subgroup.normalizer (L : Set G),
      3 ^ 4 ≤ Nat.card (ggGamma L hN).range := by
    intro hN
    have hcard := Line63.H5.ggUnitDvd63BstarRankInput_holds G 3 B Bs x L D J hcfg hM
    have hmul := card_range_ggGamma_mul_of hp hBs hxBs hS.2.2.1 hLx hS.2.2.2.2 hN
    rw [← hmul, pow_succ] at hcard
    exact Nat.le_of_mul_le_mul_right hcard hp.pos
  have hMark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧
      3 ∣ ggTorM lab) 3 Bs L := by
    refine largeEvenMarking_mono (fun lab R _ I F θ hP => ?_) hL
    obtain ⟨⟨htw, hr5, -, hdvd⟩, hN', hBsI⟩ := hP
    exact ⟨⟨htw, hr5, by simpa [ggTorM, htw] using hdvd⟩, hN', hBsI⟩
  obtain ⟨f, hf, hpq, -, hN, hTor⟩ := ggTwA5Three_torData hcfg hMark hr
  have hodd : Odd (2 ^ f + 1) := by
    obtain ⟨g, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
    rw [pow_succ]
    exact ⟨2 ^ g, by omega⟩
  have hW := NSJoin.weylOfType_of_torData (by norm_num : (3 : ℕ) ≠ 2) hodd hpq
    (ggIntCartan_A 5) hBs hcfg.2.1.2.2.2 hN hTor
  refine ⟨rfl, hW, ?_⟩
  have hle := card_le_pow_mul_card_of_weylOfType hW ((Subgroup.zpowers x).subgroupOf Bs)
    (fun b hb => Subgroup.mem_subgroupOf.mpr (hFix b hb))
  have hF : Nat.card ((Subgroup.zpowers x).subgroupOf Bs) ≤ 3 :=
    card_le_of_le_zpowers hp hBs hxBs _ (fun b hb => Subgroup.mem_subgroupOf.mp hb)
  rw [Fintype.card_fin] at hle
  calc Nat.card Bs ≤ 3 ^ 5 * Nat.card ((Subgroup.zpowers x).subgroupOf Bs) := hle
    _ ≤ 3 ^ 5 * 3 := Nat.mul_le_mul_left _ hF
    _ = 3 ^ 6 := by norm_num

theorem nsQ2U62_member_weyl
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) (hBBs : B = Bs)
    {X : Subgroup G} (hX : X ∈ 𝒦)
    (hlab : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1) 3 Bs X) :
    GGWeylOfType 3 (CoxeterMatrix.A 5) (ggAutomizer X Bs) ∧ Nat.card Bs ≤ 3 ^ 6 := by
  subst B
  obtain ⟨y, hnbr⟩ := hcfg.2.2.2.1.2 X hX
  have hconf : GGConfig 3 Bs Bs x L D J := hcfg.1.1
  have hH : GGResHyp 3 Bs Bs x L D J y X :=
    ⟨hconf, hcfg.1.2.1, hcfg.1.2.2.1, hcfg.1.2.2.2.1, hnbr, hcfg.2.1 y X hnbr,
      Or.inr hcfg.2.1⟩
  obtain ⟨lab, hΛ, hHas, R, hRg, I, F, θ, hcov⟩ := largeEvenMarking_exists_hasLabel hlab
  obtain ⟨⟨htw, hr5, hn1⟩, -, -⟩ := hcov
  have hp3 : Nat.Prime 3 := hconf.tableB_facts.1
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  obtain ⟨f, hN, hf, hpq, hTor⟩ := ggTwA5Three_torDataAt hRig hLB hPJ hH
    (Or.inr ⟨rfl, rfl⟩) rfl hΛ hHas ⟨htw, hr5, by rw [hn1]; norm_num⟩
  have hodd : Odd (2 ^ f + 1) := by
    obtain ⟨g, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
    rw [pow_succ]
    exact ⟨2 ^ g, by omega⟩
  have hBs : IsElemAbelian 3 Bs := hconf.tableB_facts.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hconf.2.1.2.2.2
  have hW := NSJoin.weylOfType_of_torData (by norm_num : (3 : ℕ) ≠ 2) hodd hpq
    (ggIntCartan_A 5) hBs hSC hN hTor
  refine ⟨hW, ?_⟩
  have hfix : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer X Bs, φ b = b) →
      (b : G) ∈ Subgroup.zpowers y := by
    intro b hb
    have hbB : (b : G) ∈ Bs ⊓ Subgroup.centralizer (X : Set G) :=
      Subgroup.mem_inf.mpr ⟨b.2, ggTD_fix_mem_centralizer hodd hpq hBs hSC hN hTor b hb⟩
    rwa [inf_centralizer_eq_zpowers_of_sHat hnbr.1] at hbB
  have hyBs : y ∈ Bs := hnbr.1.2.1
  have hle := card_le_pow_mul_card_of_weylOfType hW ((Subgroup.zpowers y).subgroupOf Bs)
    (fun b hb => Subgroup.mem_subgroupOf.mpr (hfix b hb))
  have hF : Nat.card ((Subgroup.zpowers y).subgroupOf Bs) ≤ 3 :=
    card_le_of_le_zpowers hp3 hBs hyBs _ (fun b hb => Subgroup.mem_subgroupOf.mp hb)
  rw [Fintype.card_fin] at hle
  calc Nat.card Bs ≤ 3 ^ 5 * Nat.card ((Subgroup.zpowers y).subgroupOf Bs) := hle
    _ ≤ 3 ^ 5 * 3 := Nat.mul_le_mul_left _ hF
    _ = 3 ^ 6 := by norm_num

theorem nsQ2U62_card_D
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hFix : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer L Bs, φ b = b) → (b : G) ∈ Subgroup.zpowers x)
    (hlab : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) p Bs L)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hD : GGIsWeylMatrixD M) :
    Nat.card Bs = 3 ^ 6 ∧ ∃ σ : Fin 6 ≃ ι, M = (ggCoxeterMatrixD 6).reindex σ := by
  obtain ⟨rfl, hW, hle⟩ := nsQ2U62_weyl hcfg.1.1 hFix hlab
  obtain ⟨k, σ, hk4, hM⟩ := hD
  have hge : 3 ^ k ≤ Nat.card Bs := ggDk_card_bstar_ge hcfg hpres hk4 hM
  have hk_le : k ≤ 6 :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp (hge.trans hle)
  obtain ⟨eW, -⟩ := hW
  obtain ⟨eP, -⟩ := ggCoxeterA_mulEquivPerm 5
  have hWcard : Nat.card ↥(ggAutomizer L Bs) = 720 := by
    rw [← Nat.card_congr eW.toEquiv, Nat.card_congr eP.toEquiv,
      Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    norm_num
  have hcardK : Nat.card ↥(ggAutomizerJoin L Bs 𝒦) = 2 ^ (k - 1) * k.factorial := by
    rw [← Nat.card_congr e.toEquiv, hM,
      Nat.card_congr ((ggCoxeterMatrixD k).reindexGroupEquiv σ).toEquiv]
    exact OrthF3.card_coxeterD_eq k hk4
  have : Finite (MulAut ↥Bs) :=
    Finite.of_injective (fun f : MulAut ↥Bs => (f : ↥Bs → ↥Bs))
      (fun f g h => DFunLike.ext f g (fun x => congrFun h x))
  have hdiv : 720 ∣ 2 ^ (k - 1) * k.factorial := by
    rw [← hWcard, ← hcardK]
    exact Subgroup.card_dvd_of_le (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl))
  interval_cases k
  · norm_num at hdiv
  · norm_num at hdiv
  · exact ⟨le_antisymm hle hge, σ, hM⟩

end CFSG.StandardType

end
