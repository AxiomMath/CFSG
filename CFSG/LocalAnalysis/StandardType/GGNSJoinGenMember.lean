module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinGen
public import CFSG.LocalAnalysis.StandardType.GGNSJoinRMChain
public import CFSG.LocalAnalysis.StandardType.GGNSJoinByType
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


@[expose] def NSNbrOutLocalGenInputOf (T : ∀ {ι : Type}, CoxeterMatrix ι → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      NSJoinGuardOf T p L Bs 𝒦 →
      ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → K ∉ 𝒦 →
        ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦 →
        ∃ r₀ : MulAut ↥Bs, r₀ ∈ ggAutomizer J Bs ∧ r₀ ^ 2 = 1 ∧ r₀ ≠ 1 ∧ J ≤ K ∧
          (K ≤ ⨆ r : MulAut ↥Bs, ⨆ (_ : r ∈ ggAutomizer K Bs),
            ⨆ (_ : GGIsReflection p r), ggRankOneIn K Bs r) ∧
          (∀ N : Subgroup G, N ≤ ggRankOneIn K Bs r₀ → N ≠ ⊥ →
            (∀ a ∈ ggRankOneIn K Bs r₀, ∀ b ∈ N, a * b * a⁻¹ ∈ N) → ggRankOneIn K Bs r₀ ≤ N) ∧
          (∀ r ∈ ggAutomizer K Bs, GGIsReflection p r →
            ∃ a ∈ ggAutomizer K Bs, a * r₀ * a⁻¹ = r)

theorem nsNbrLocalGen_of_member {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hL : GGLBalanceInput)
    (hT3 : ∀ {ι : Type} {M : CoxeterMatrix ι}, T M → ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hL1 : GGSecFiveL1PhanInput) (hRk1 : GGSecFiveRk1PhanInput) (hGenP : GGSecFiveGenPhanInput)
    (hNbr : GGSecFiveNonSplitNbrInput) (hP : GGStdSubPrimeInput) (hPumpNbr : NSPumpNbrInputOf T)
    (hJA2 : NSJA2InputOf T) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
      (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
        NSJoinGuardOf T p L Bs 𝒦 →
        ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → K ∈ 𝒦 →
          ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦 →
          ∃ r₀ : MulAut ↥Bs, r₀ ∈ ggAutomizer J Bs ∧ r₀ ^ 2 = 1 ∧ r₀ ≠ 1 ∧ J ≤ K ∧
            (K ≤ ⨆ r : MulAut ↥Bs, ⨆ (_ : r ∈ ggAutomizer K Bs),
              ⨆ (_ : GGIsReflection p r), ggRankOneIn K Bs r) ∧
            (∀ N : Subgroup G, N ≤ ggRankOneIn K Bs r₀ → N ≠ ⊥ →
              (∀ a ∈ ggRankOneIn K Bs r₀, ∀ b ∈ N, a * b * a⁻¹ ∈ N) → ggRankOneIn K Bs r₀ ≤ N) ∧
            (∀ r ∈ ggAutomizer K Bs, GGIsReflection p r →
              ∃ a ∈ ggAutomizer K Bs, a * r₀ * a⁻¹ = r) := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hns hguard y K hK hmem hKA
  obtain ⟨ι, M, e, hpres, hT, hbig⟩ := hguard
  obtain ⟨r₀, hr₀J, _r', _hr'J, hr₀refl, _hr'refl, _horder⟩ :=
    hJA2 G p B Bs x L D J 𝒦 ⟨hcfg, hns, ⟨ι, M, e, hpres, hT, hbig⟩⟩
  have hC : GGConfig p B Bs x L D J := hcfg.1.1
  have hI : GGThmIHyp p B x L := hC.1
  have hp : p.Prime := by
    obtain ⟨-, -, -, -, -, hβ, -, -⟩ := hI
    exact hβ.1
  have hJL : J ≤ L := (hC.2.2.1.2.2.2.2.2.1.1).trans inf_le_left
  have hJK : J ≤ K :=
    le_of_ggNbr hL hI hC.2.2 (hP G p B x L D J hI hC.2.2) hK
  have hrKA : r₀ ∈ ggAutomizer K Bs := ggAutomizer_mono Bs hJK hr₀J
  have hrLA : r₀ ∈ ggAutomizer L Bs := ggAutomizer_mono Bs hJL hr₀J
  have hr₀C : r₀ ∈ ggCoxRefl M e :=
    ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres (hT3 hT)
      (ggAutomizer_le_ggAutomizerJoin (Or.inr hmem) hrKA) hr₀refl
  obtain ⟨hPumpWe, -⟩ := hPumpNbr G p B Bs x L D J 𝒦 ⟨hcfg, hns, ⟨ι, M, e, hpres, hT, hbig⟩⟩ y K hK
  obtain ⟨ιK, MK, hMKweyl, f, hfrefl⟩ := hPumpWe
  have hpresK : GGCoxeterPres p (ggAutomizer K Bs) MK f := ⟨hMKweyl, hfrefl⟩
  have hriC : ∀ i : ιK, ((f (MK.simple i) : ↥(ggAutomizer K Bs)) : MulAut ↥Bs) ∈
      ggCoxRefl M e :=
    fun i => ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres (hT3 hT)
      (ggAutomizer_le_ggAutomizerJoin (Or.inr hmem) (f (MK.simple i)).2) (hfrefl i)
  have h3MK : ∀ i j : ιK, i ≠ j → MK.M i j ≤ 3 := by
    intro i j _hij
    have hf := ggCoxRefl_mul_orderOf_le_three hpres.1 (hT3 hT) (hriC i) (hriC j)
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
  have hnsK : ¬ GGSplitLie p K :=
    hNbr G p B Bs x L D J 𝒦 hcfg hns ι M e hpres (hT3 hT) hbig K hmem
  have hgen : K ≤ ⨆ r : MulAut ↥Bs, ⨆ (_ : r ∈ ggAutomizer K Bs),
      ⨆ (_ : GGIsReflection p r), ggRankOneIn K Bs r := by
    refine (le_of_eq (hGenP G p B Bs x L D J 𝒦 hcfg hns ι M e hpres (hT3 hT) hbig K
      (Or.inr hmem) hnsK)).trans ?_
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
    have hL1K := hL1 G p B Bs x L D J 𝒦 hcfg hns ι M e hpres (hT3 hT) hbig K (Or.inr hmem)
      r₀ hrKA hr₀C
    have hL1L := hL1 G p B Bs x L D J 𝒦 hcfg hns ι M e hpres (hT3 hT) hbig L (Or.inl rfl)
      r₀ hrLA hr₀C
    have hEq : ggRankOneIn K Bs r₀ = ggRankOneIn L Bs r₀ := by rw [← hL1K, hL1L]
    rw [hEq]
    exact hbig r₀ hrLA hr₀C
  have hmin : ∀ N : Subgroup G, N ≤ ggRankOneIn K Bs r₀ → N ≠ ⊥ →
      (∀ a ∈ ggRankOneIn K Bs r₀, ∀ b ∈ N, a * b * a⁻¹ ∈ N) → ggRankOneIn K Bs r₀ ≤ N :=
    ggRankOneIn_minimal_of_rk1 hRk1 hcfg hns hpres (hT3 hT) (Or.inr hmem) hrKA hr₀refl h6
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

theorem nsNbrLocalGenInputOf_of_out {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hL : GGLBalanceInput)
    (hT3 : ∀ {ι : Type} {M : CoxeterMatrix ι}, T M → ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hL1 : GGSecFiveL1PhanInput) (hRk1 : GGSecFiveRk1PhanInput) (hGenP : GGSecFiveGenPhanInput)
    (hNbr : GGSecFiveNonSplitNbrInput) (hP : GGStdSubPrimeInput) (hPumpNbr : NSPumpNbrInputOf T)
    (hJA2 : NSJA2InputOf T) (hOut : NSNbrOutLocalGenInputOf T) : NSNbrLocalGenInputOf T := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hns hguard y K hK hKA
  by_cases hmem : K ∈ 𝒦
  · exact nsNbrLocalGen_of_member hL hT3 hL1 hRk1 hGenP hNbr hP hPumpNbr hJA2 G p B Bs x L D J 𝒦
      hcfg hns hguard y K hK hmem hKA
  · exact hOut G p B Bs x L D J 𝒦 hcfg hns hguard y K hK hmem hKA

theorem nsNbrLocalGenInputOf_of_members {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hL : GGLBalanceInput)
    (hTAD : ∀ {ι : Type} {M : CoxeterMatrix ι}, T M → NSTypeAD M)
    (hT3 : ∀ {ι : Type} {M : CoxeterMatrix ι}, T M → ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hL1 : GGSecFiveL1PhanInput) (hRk1 : GGSecFiveRk1PhanInput) (hGenP : GGSecFiveGenPhanInput)
    (hNbr : GGSecFiveNonSplitNbrInput) (hP : GGStdSubPrimeInput) (hPumpNbr : NSPumpNbrInput)
    (hJA2 : NSJA2InputOf T) (hOut : NSNbrOutLocalGenInputOf T) : NSNbrLocalGenInputOf T :=
  nsNbrLocalGenInputOf_of_out hL hT3 hL1 hRk1 hGenP hNbr hP
    (fun G _ _ p B Bs x L D J 𝒦 hreg =>
      hPumpNbr G p B Bs x L D J 𝒦 ⟨hreg.1, hreg.2.1, NSJoinGuardOf.mono hTAD hreg.2.2⟩)
    hJA2 hOut

end NSJoin

end CFSG.StandardType

end
