module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeakNbr
public import CFSG.LocalAnalysis.StandardType.GGSecFiveDataResDefs
public import CFSG.LocalAnalysis.StandardType.GGNSJoinByType
public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs
public import CFSG.LocalAnalysis.StandardType.GGResidualRk1UnitaryTwo
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSQ2U62Setup
import CFSG.ClassicalGroups.Unitary.Finite
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseLabel
import CFSG.LocalAnalysis.StandardType.GGNsq2Main
import CFSG.LocalAnalysis.StandardType.GGNsq2Rank
import CFSG.LocalAnalysis.StandardType.GGNsq2Strict
import CFSG.LocalAnalysis.StandardType.GGRCWeylCard
import CFSG.LocalAnalysis.StandardType.GGResidualRk1Frame
import CFSG.LocalAnalysis.StandardType.GGRk1ConclExSix
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthWeylOrdD
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsuAux
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosAdapterAux
import CFSG.LocalAnalysis.StandardType.GGSecFivePrimDefs
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpCount
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAux
import CFSG.LocalAnalysis.StandardType.GGTDAutomizer
import CFSG.LocalAnalysis.StandardType.GGTwA5ThreeFrame

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint

private theorem three_pow_six_le_of_typeD
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e)
    (hD : NSJoin.NSTypeD M) {X : Subgroup G}
    (hle : ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (h720 : Nat.card ↥(ggAutomizer X Bs) = 720) :
    3 ^ 6 ≤ Nat.card ↥Bs := by
  have hD' : GGIsWeylMatrixD M := hD
  obtain ⟨k, σ, hk4, hM⟩ := hD'
  have hcardK : Nat.card ↥(ggAutomizerJoin L Bs 𝒦) = 2 ^ (k - 1) * k.factorial := by
    rw [← Nat.card_congr e.toEquiv, hM,
      Nat.card_congr ((ggCoxeterMatrixD k).reindexGroupEquiv σ).toEquiv]
    exact OrthF3.card_coxeterD_eq k hk4
  have hdiv : 720 ∣ 2 ^ (k - 1) * k.factorial := by
    rw [← h720, ← hcardK]
    exact Subgroup.card_dvd_of_le hle
  have hk6 : 6 ≤ k := by
    by_contra hk
    have hk5 : k ≤ 5 := by omega
    interval_cases k <;> norm_num at hdiv
  calc 3 ^ 6 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk6
    _ ≤ Nat.card ↥Bs := ggDk_card_bstar_ge hcfg hpres hk4 hM

private theorem three_pow_six_le_of_typeA (hTB : GGTBFixInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hA : GGIsWeylMatrixA M) {X : Subgroup G}
    (hX : GGSecFiveWeakNbr 3 B Bs x L D J 𝒦 X)
    (h720 : Nat.card ↥(ggAutomizer X Bs) = 720) :
    3 ^ 6 ≤ Nat.card ↥Bs := by
  obtain ⟨m, σ, -, hM⟩ := hA
  have hcardK : Nat.card ↥(ggAutomizerJoin L Bs 𝒦) = (m + 1).factorial := by
    rw [← Nat.card_congr e.toEquiv, hM, card_coxeterGroup_reindex, l05nK3a_card_coxeterA]
  obtain ⟨y, hnb⟩ := hX.1
  have hlt := ggPhanStrict_card_lt_join_of_nbr hTB hcfg hnb hX.2
  rw [h720, hcardK] at hlt
  have hm7 : 7 ≤ m + 1 := by
    by_contra h
    have hle : (m + 1).factorial ≤ Nat.factorial 6 := Nat.factorial_le (by omega)
    rw [show Nat.factorial 6 = 720 by decide] at hle
    omega
  have h7 : 7 ∣ Nat.card ↥(ggAutomizerJoin L Bs 𝒦) := by
    rw [hcardK]
    exact Nat.dvd_factorial (by norm_num) hm7
  exact three_pow_six_le_card_of_seven_dvd (ggRouteCfg_isElemAbelian hcfg) h7

theorem three_pow_six_le_card_of_nbr_card_automizer (hTB : GGTBFixInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e)
    (hTAD : GGIsWeylMatrixA M ∨ NSJoin.NSTypeD M)
    {X : Subgroup G} (hX : GGSecFiveWeakNbr 3 B Bs x L D J 𝒦 X)
    (h720 : Nat.card ↥(ggAutomizer X Bs) = 720) :
    3 ^ 6 ≤ Nat.card ↥Bs := by
  rcases hTAD with hA | hD
  · exact three_pow_six_le_of_typeA hTB hcfg e hA hX h720
  · exact three_pow_six_le_of_typeD hcfg hpres hD hX.2 h720

theorem nsQ2U62_weyl_nbr
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {y : G} {X : Subgroup G} (hnb : GGNbr p B x D J y X)
    (h : GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) p Bs X) :
    p = 3 ∧ GGWeylOfType 3 (CoxeterMatrix.A 5) (ggAutomizer X Bs) := by
  have hp3 : p = 3 := by
    obtain ⟨hp, -, -, -, -⟩ := hcfg.tableB_facts
    obtain ⟨-, lab, -, hraw⟩ := h
    obtain ⟨R, _, I, F, -, -, θ, hP⟩ := largeEvenRawDatum_exists hraw
    obtain ⟨⟨hrow, hn1, -⟩, -, -⟩ := hP
    refine (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp ?_
    have h := hrow.2
    rw [hn1] at h
    norm_num at h
    exact h
  subst hp3
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  obtain ⟨hperf, lab, hΛ, hraw⟩ := h
  obtain ⟨R, _, I, F, -, -, θ, hP⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨⟨hrow, hn1, hr5⟩, -, -⟩ := hP
  have htw : lab.tag = .twA := by
    rcases hrow.1 with ⟨htw, -⟩ | ⟨-, hr3⟩
    · exact htw
    · omega
  have hdvd : 3 ∣ 2 ^ lab.n + 1 := hrow.2
  have hmk : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs X := by
    refine ⟨hperf, lab, hΛ, largeEvenRawDatum_mono (fun R _ I F hQ => ?_) hraw⟩
    obtain ⟨hs, hna, θ', hP'⟩ := hQ
    exact ⟨hs, hna, θ', ⟨rfl, hP'.2⟩⟩
  have hMark : GGInnerDiagOnLabel (fun _ lab' => lab'.tag = .twA ∧ lab'.rank = 5 ∧
      3 ∣ ggTorM lab') 3 Bs X := by
    refine largeEvenMarking_mono (fun lab' R _ I F θ' hP' => ?_) hmk
    obtain ⟨rfl, hN', hBsI⟩ := hP'
    exact ⟨⟨htw, hr5, by simpa [ggTorM, htw] using hdvd⟩, hN', hBsI⟩
  obtain ⟨f, hf, hpq, -, hN, hTor⟩ := ggTwA5Three_torData hcfg hMark
    (fun hN => ggTwA5Three_rank hLB hP hcfg hnb (Or.inr rfl) hmk ⟨htw, hr5, hdvd⟩ hN)
  have hodd : Odd (2 ^ f + 1) := by
    obtain ⟨g, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
    rw [pow_succ]
    exact ⟨2 ^ g, by omega⟩
  have hW := NSJoin.weylOfType_of_torData (by norm_num : (3 : ℕ) ≠ 2) hodd hpq
    (ggIntCartan_A 5) hBs hcfg.2.1.2.2.2 hN hTor
  exact ⟨rfl, hW⟩

section Concl


theorem ggRk1ConclEx_of_twA5_two_of_card_six (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {Bs X : Subgroup G} (hBs : IsElemAbelian 3 Bs)
    (hnsX : ¬ GGSplitLie 3 X)
    (h : GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) 3 Bs X)
    (hW : GGWeylOfType 3 (CoxeterMatrix.A 5) (ggAutomizer X Bs)) {r₀ : MulAut ↥Bs}
    (hr₀A : r₀ ∈ ggAutomizer X Bs) (hr₀R : GGIsReflection 3 r₀)
    (hr₀6 : Nat.card ↥(ggRankOneIn X Bs r₀) = 6) :
    ∀ r ∈ ggAutomizer X Bs, GGIsReflection 3 r → GGRk1ConclEx 3 Bs X r := by
  have hconc₀ : GGRk1ConclEx 3 Bs X r₀ := by
    obtain ⟨lab, hΛ, hhas, -, -, -, -, -, hrow, -⟩ := largeEvenMarking_exists_hasLabel h
    have htag : lab.tag = .twA := by
      rcases hrow.1.1 with ⟨ht, -⟩ | ⟨ht, hr3⟩
      · exact ht
      · omega
    refine ggRk1ConclEx_of_card_six rfl hnsX hr₀A hr₀R.1 hr₀6 ⟨lab, hΛ, hhas⟩ ?_
    intro lab' hΛ' hhas'
    have hn := NSJoin.ggLabelIso_n_eq (hRig lab lab' _ hΛ hΛ' hhas hhas')
      (by rw [htag]; decide) (fun ht => by rw [htag] at ht; exact absurd ht (by decide))
    omega
  intro r hrA hrR
  obtain ⟨a, ha, hconj⟩ := GGWeylOfType.exists_conj_of_typeA (p := 3) (n := 5)
    (by norm_num) (by norm_num) hBs hW hr₀A hr₀R hrA hrR
  rw [hconj]
  exact ggRk1ConclEx_conj hconc₀ ha

end Concl

private theorem exists_rankOne_card_six_of_twA5_nbr
    (hTB : GGTBFixInput) (hU62 : GGU62OuterDiagInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e)
    (hTAD : GGIsWeylMatrixA M ∨ NSJoin.NSTypeD M)
    {X : Subgroup G} (hX : GGSecFiveWeakNbr 3 B Bs x L D J 𝒦 X)
    (h : GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) 3 Bs X)
    (hW : GGWeylOfType 3 (CoxeterMatrix.A 5) (ggAutomizer X Bs))
    (hC3 : Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ 3) :
    ∃ r ∈ ggAutomizer X Bs, GGIsReflection 3 r ∧ Nat.card ↥(ggRankOneIn X Bs r) = 6 := by
  obtain ⟨y, hnb⟩ := hX.1
  have h720 : Nat.card ↥(ggAutomizer X Bs) = 720 := by
    obtain ⟨eW, -⟩ := hW
    obtain ⟨eP, -⟩ := ggCoxeterA_mulEquivPerm 5
    rw [← Nat.card_congr eW.toEquiv, Nat.card_congr eP.toEquiv, Nat.card_eq_fintype_card,
      Fintype.card_perm, Fintype.card_fin]
    norm_num
  have h36 := three_pow_six_le_card_of_nbr_card_automizer hTB hcfg hpres hTAD hX h720
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, _hf, _hfin, lab, m', θ, hK, -, hmrank, hSide, hdvd, hperf, -, hBsN, hbs⟩ :=
    ggNSLieN3A_esuCore h (fun p lab hl => hl.1)
  have : CharP K 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := lab.n) hK
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨-, hn1, hr5⟩ := hSide
  change n = 1 at hn1
  change rank = 5 at hr5
  change m' = rank + 1 at hmrank
  subst hn1
  subst hr5
  have hm6 : m' = 6 := by omega
  subst hm6
  exact ggNsq2Member_exists_rankOne_of_or hU62 hcfg
    (ggNSPosPD_routeCfg_cent_K Nat.prime_three hnb) hC3 hK hdvd θ hperf hBsN hbs
    (fun _ => Or.inl h36)

theorem ggRk1ConclEx_of_twA5_two_nbr
    (hRig : GGLabelRigidInput) (hTB : GGTBFixInput) (hU62 : GGU62OuterDiagInput)
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hTAD : GGIsWeylMatrixA M ∨ NSJoin.NSTypeD M)
    {X : Subgroup G} (hX : GGSecFiveWeakNbr p B Bs x L D J 𝒦 X) (hnsX : ¬ GGSplitLie p X)
    (h : GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) p Bs X)
    (hC3 : Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ 3) :
    ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e → GGRk1ConclEx p Bs X r := by
  obtain ⟨y, hnb⟩ := hX.1
  obtain ⟨hp3, hW⟩ := nsQ2U62_weyl_nbr hLB hP hcfg.1.1 hnb h
  subst hp3
  obtain ⟨r₀, hr₀A, hr₀R, hr₀6⟩ :=
    exists_rankOne_card_six_of_twA5_nbr hTB hU62 hcfg hpres hTAD hX h hW hC3
  intro r hrA hrC
  exact ggRk1ConclEx_of_twA5_two_of_card_six hRig (ggRouteCfg_isElemAbelian hcfg) hnsX h hW
    hr₀A hr₀R hr₀6 r hrA (ggCoxRefl_isReflection hpres.2 hrC)

end CFSG.StandardType

end
