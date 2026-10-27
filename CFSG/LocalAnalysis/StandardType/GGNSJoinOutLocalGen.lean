module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinGenMember
public import CFSG.LocalAnalysis.StandardType.GGSecFiveL1PhanLocal
public import CFSG.LocalAnalysis.StandardType.GGSecFiveL1PhanTransfer
public import CFSG.LocalAnalysis.StandardType.GGMemberUnitaryGen
public import CFSG.LocalAnalysis.StandardType.GGMemberUnitaryRk1
public import CFSG.LocalAnalysis.StandardType.GGRk1SplitMember
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosAssemble
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNbrRefl
import CFSG.LocalAnalysis.StandardType.GGNbrBalance
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrCoxOrder
import CFSG.LocalAnalysis.StandardType.GGSimplyLacedWeyl
import CFSG.LocalAnalysis.StandardType.GGNSJoinRankOneOfRk1
import CFSG.LocalAnalysis.StandardType.GGReflectionBasic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem

namespace NSJoin

section WeakNotSplit


theorem nsWeakNotSplit
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hns : ¬ GGSplitLie p L)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    {r₀ : MulAut ↥Bs} (hrLA : r₀ ∈ ggAutomizer L Bs) (hr₀C : r₀ ∈ ggCoxRefl M e)
    (h6₀ : Nat.card ↥(ggRankOneIn L Bs r₀) ≠ 6) (hseed : ggRankOnePerf Bs r₀ = ggRankOneIn L Bs r₀)
    (hRkL : GGRk1Concl p Bs L r₀) {y : G} {K : Subgroup G} (hK : GGNbr p B x D J y K)
    (hKA : ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) : ¬ GGSplitLie p K := by
  intro hs
  have hKnbr : K = L ∨ ∃ y : G, GGNbr p B x D J y K := Or.inr ⟨y, hK⟩
  obtain ⟨rK, hrKA', hrKC⟩ := ggPhanNbr_refl_of_split_nbr hcfg hpres h3 ⟨y, hK⟩ hKA hs
  have hRkK : GGRk1Concl p Bs K rK := ggRk1Concl_split_nbr hcfg hpres hKnbr hs hrKA' hrKC
  have hL1K : ggRankOnePerf Bs rK = ggRankOneIn K Bs rK :=
    ggL1_transfer_nbr hcfg hns hpres h3 hrLA hr₀C h6₀ hseed hKnbr hrKA' hrKC hRkL hRkK
  exact ggNotSplitLie_of_rk1_data hcfg hns hpres h3 hr₀C hrKC hRkL hRkK hseed hL1K hs

end WeakNotSplit

section A5


theorem nsNbrLocalGenInputOf_A5
    (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hEn : GGSecFiveNSEnnolaInput)
    (hQ2 : GGSecFiveNSQ2Input) (hFix : GGTBFixInput) (hWA : GGTBFixNbrXInput)
    (hPumpNbr : NSPumpNbrInput)
    (hJA2 : NSJA2InputOf (fun {ι : Type} (M : CoxeterMatrix ι) => NSTypeA5 M))
    (hSolv : GGSecFiveAllFixedSolvInput) (ha₀ : GGLNoncyclicInput)
    (hSch : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier) :
    NSNbrLocalGenInputOf (fun {ι : Type} (M : CoxeterMatrix ι) => NSTypeA5 M) := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hns hguard y K hK hKA
  obtain ⟨ι, M, e, hpres, hT, hbig⟩ := hguard
  have hA : ∃ (m : ℕ) (σ : Fin m ≃ ι), 5 ≤ m ∧ M = (CoxeterMatrix.A m).reindex σ := hT
  have hTAD : NSTypeAD M := (nsTypeAD_iff M).2 (Or.inl hT)
  have h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := fun i j hij => NSTypeAD.le_three hTAD i j hij
  obtain ⟨r₀, hr₀J, _r', _hr'J, hr₀refl, _hr'refl, _horder⟩ :=
    hJA2 G p B Bs x L D J 𝒦 ⟨hcfg, hns, ⟨ι, M, e, hpres, hT, hbig⟩⟩
  have hC : GGConfig p B Bs x L D J := hcfg.1.1
  have hI : GGThmIHyp p B x L := hC.1
  have hp : p.Prime := by
    obtain ⟨-, -, -, -, -, hβ, -, -⟩ := hI
    exact hβ.1
  have hJL : J ≤ L := (hC.2.2.1.2.2.2.2.2.1.1).trans inf_le_left
  have hpJ : p ∣ Nat.card J := hP G p B x L D J hI hC.2.2
  have hJK : J ≤ K := le_of_ggNbr hL hI hC.2.2 hpJ hK
  have hrKA : r₀ ∈ ggAutomizer K Bs := ggAutomizer_mono Bs hJK hr₀J
  have hrLA : r₀ ∈ ggAutomizer L Bs := ggAutomizer_mono Bs hJL hr₀J
  have hr₀C : r₀ ∈ ggCoxRefl M e :=
    ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres h3 (hKA hrKA) hr₀refl
  have hguardAD : NSJoinGuard p L Bs 𝒦 := ⟨ι, M, e, hpres, hTAD, hbig⟩
  obtain ⟨hPumpWe, -⟩ := hPumpNbr G p B Bs x L D J 𝒦 ⟨hcfg, hns, hguardAD⟩ y K hK
  obtain ⟨ιK, MK, hMKweyl, f, hfrefl⟩ := hPumpWe
  have hpresK : GGCoxeterPres p (ggAutomizer K Bs) MK f := ⟨hMKweyl, hfrefl⟩
  have hriC : ∀ i : ιK, ((f (MK.simple i) : ↥(ggAutomizer K Bs)) : MulAut ↥Bs) ∈
      ggCoxRefl M e :=
    fun i => ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres h3
      (hKA (f (MK.simple i)).2) (hfrefl i)
  have h3MK : ∀ i j : ιK, i ≠ j → MK.M i j ≤ 3 := by
    intro i j _hij
    have hf := ggCoxRefl_mul_orderOf_le_three hpres.1 h3 (hriC i) (hriC j)
    have hs : (MK.simple i * MK.simple j) ^ 2 = 1 ∨ (MK.simple i * MK.simple j) ^ 3 = 1 := by
      rcases hf with h2 | h3
      · left
        refine f.injective ?_
        apply Subtype.val_injective
        simpa [map_pow, map_mul, Subgroup.coe_mul, Subgroup.coe_pow] using h2
      · right
        refine f.injective ?_
        apply Subtype.val_injective
        simpa [map_pow, map_mul, Subgroup.coe_mul, Subgroup.coe_pow] using h3
    rcases hs with h2 | h3
    · have hdvd : MK.M i j ∣ 2 := by
        rw [← MK.toCoxeterSystem.orderOf_simple_mul_simple i j]
        exact orderOf_dvd_of_pow_eq_one h2
      exact (Nat.le_of_dvd (by norm_num) hdvd).trans (by norm_num)
    · have hdvd : MK.M i j ∣ 3 := by
        rw [← MK.toCoxeterSystem.orderOf_simple_mul_simple i j]
        exact orderOf_dvd_of_pow_eq_one h3
      exact Nat.le_of_dvd (by norm_num) hdvd
  have hconnK : GGSimplyLacedConnected MK := ggSimplyLacedConnected_of_weyl hMKweyl h3MK
  have hKnbr : K = L ∨ ∃ y : G, GGNbr p B x D J y K := Or.inr ⟨y, hK⟩
  have hUL : GGMemberUnitary p Bs L :=
    ggInnerDiagUnitary_of_ennola_q2_nbr hEn hQ2 hFix hWA hL hP hcfg hns hpres hA hbig (Or.inl rfl) hns
  have hRkL : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → GGRk1Concl p Bs L r :=
    fun r hrA hrC => ggRk1Concl_unitary_nbr hcfg hpres (Or.inl rfl) hns hUL hrA hrC
  have h6₀ : Nat.card ↥(ggRankOneIn L Bs r₀) ≠ 6 := hbig r₀ hrLA hr₀C
  have hsolv : Group.IsSolvable ↥(Subgroup.centralizer (Bs : Set G)) :=
    SecFiveL1Solv.bstar_solvable_of_all_fixed_solvable ha₀ hL hcfg hpJ
      (hSolv G p B Bs x L D J 𝒦 hcfg)
      (fun X hX => ggSecFive_outSolvable_of_member hSch hcfg hX)
  have hseed : ggRankOnePerf Bs r₀ = ggRankOneIn L Bs r₀ :=
    ggL1_seed_of_concl ha₀ hsolv (ggSecFive_outSolvable_of_member hSch hcfg (Or.inl rfl)) hcfg hns
      hpres h3 hrLA hr₀refl h6₀ (hRkL r₀ hrLA hr₀C)
  have hnsK : ¬ GGSplitLie p K :=
    nsWeakNotSplit hcfg hns hpres h3 hrLA hr₀C h6₀ hseed (hRkL r₀ hrLA hr₀C) hK hKA
  have hUK : GGMemberUnitary p Bs K :=
    ggInnerDiagUnitary_of_ennola_q2_nbr hEn hQ2 hFix hWA hL hP hcfg hns hpres hA hbig
      (Or.inr ⟨⟨y, hK⟩, hKA⟩) hnsK
  have hRkK : ∀ r ∈ ggAutomizer K Bs, r ∈ ggCoxRefl M e → GGRk1Concl p Bs K r :=
    fun r hrA hrC => ggRk1Concl_unitary_nbr hcfg hpres hKnbr hnsK hUK hrA hrC
  have hL1K : ∀ r ∈ ggAutomizer K Bs, r ∈ ggCoxRefl M e →
      ggRankOnePerf Bs r = ggRankOneIn K Bs r :=
    fun r hrA hrC => ggL1_transfer_nbr hcfg hns hpres h3 hrLA hr₀C h6₀ hseed hKnbr hrA hrC
      (hRkL r₀ hrLA hr₀C) (hRkK r hrA hrC)
  have hL1L : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e →
      ggRankOnePerf Bs r = ggRankOneIn L Bs r :=
    fun r hrA hrC => ggL1_transfer_nbr hcfg hns hpres h3 hrLA hr₀C h6₀ hseed (Or.inl rfl) hrA hrC
      (hRkL r₀ hrLA hr₀C) (hRkL r hrA hrC)
  have hGenC : GGGenConcl M Bs K L 𝒦 e :=
    ggGenConcl_unitary_nbr hcfg hns hpres h3 hbig hKnbr hKA hnsK hUK ⟨r₀, hrLA, hr₀C⟩ hL1K hL1L
  have hgen : K ≤ ⨆ r : MulAut ↥Bs, ⨆ (_ : r ∈ ggAutomizer K Bs),
      ⨆ (_ : GGIsReflection p r), ggRankOneIn K Bs r := by
    refine (le_of_eq hGenC).trans ?_
    refine iSup_le fun r => iSup_le fun hr => ?_
    have hr' : r ∈ ggAutomizer K Bs ∧ r ∈ ggCoxRefl M e := by simpa using hr
    have hrA : r ∈ ggAutomizer K Bs := hr'.1
    have hrCc : r ∈ ggCoxRefl M e := hr'.2
    exact (le_iSup (fun (_ : GGIsReflection p r) => ggRankOneIn K Bs r)
        (ggCoxRefl_isReflection (fun i => hpres.2 i) hrCc)).trans
      ((le_iSup (fun (_ : r ∈ ggAutomizer K Bs) =>
          ⨆ (_ : GGIsReflection p r), ggRankOneIn K Bs r) hrA).trans
        (le_iSup (fun r => ⨆ (_ : r ∈ ggAutomizer K Bs),
          ⨆ (_ : GGIsReflection p r), ggRankOneIn K Bs r) r))
  have h6 : Nat.card ↥(ggRankOneIn K Bs r₀) ≠ 6 := by
    have hEq : ggRankOneIn K Bs r₀ = ggRankOneIn L Bs r₀ := (hL1K r₀ hrKA hr₀C).symm.trans hseed
    rw [hEq]
    exact h6₀
  have hmin := ggRankOneIn_minimal_of_concl (hRkK r₀ hrKA hr₀C) h6
  have horbit : ∀ r ∈ ggAutomizer K Bs, GGIsReflection p r →
      ∃ a ∈ ggAutomizer K Bs, a * r₀ * a⁻¹ = r := by
    intro r hrAK hrrefl
    have hrC : r ∈ ggCoxRefl MK f :=
      ggCoxRefl_of_cfg hcfg (ggAutomizer_le_top K Bs) hpresK h3MK hrAK hrrefl
    have hr₀CK : r₀ ∈ ggCoxRefl MK f :=
      ggCoxRefl_of_cfg hcfg (ggAutomizer_le_top K Bs) hpresK h3MK hrKA hr₀refl
    obtain ⟨a, haA, ha⟩ := ggCoxRefl_conj_of_connected f hconnK hr₀CK hrC
    exact ⟨a, haA, ha.symm⟩
  exact ⟨r₀, hr₀J, hr₀refl.1, hr₀refl.ne_one hp, hJK, hgen, hmin, horbit⟩

theorem nsNbrOutLocalGenInputOf_A5
    (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hEn : GGSecFiveNSEnnolaInput)
    (hQ2 : GGSecFiveNSQ2Input) (hFix : GGTBFixInput) (hWA : GGTBFixNbrXInput)
    (hPumpNbr : NSPumpNbrInput)
    (hJA2 : NSJA2InputOf (fun {ι : Type} (M : CoxeterMatrix ι) => NSTypeA5 M))
    (hSolv : GGSecFiveAllFixedSolvInput) (ha₀ : GGLNoncyclicInput)
    (hSch : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier) :
    NSNbrOutLocalGenInputOf (fun {ι : Type} (M : CoxeterMatrix ι) => NSTypeA5 M) :=
  fun G _ _ p B Bs x L D J 𝒦 hcfg hns hguard y K hK _ hKA =>
    nsNbrLocalGenInputOf_A5 hL hP hEn hQ2 hFix hWA hPumpNbr hJA2 hSolv ha₀ hSch G p B Bs x L D J 𝒦
      hcfg hns hguard y K hK hKA

end A5

end NSJoin

end CFSG.StandardType
