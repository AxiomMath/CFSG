module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinGenMember
public import CFSG.LocalAnalysis.StandardType.GGSecFiveL1PhanTransfer
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeakNbr
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

namespace NSJoin


@[expose] def NSWeakRk1InputOf (T : ∀ {ι : Type}, CoxeterMatrix ι → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      NSJoinGuardOf T p L Bs 𝒦 →
      ∀ K : Subgroup G, GGSecFiveWeakNbr p B Bs x L D J 𝒦 K →
        ∀ r ∈ ggAutomizer K Bs, GGIsReflection p r → GGRk1Concl p Bs K r

@[expose] def NSWeakGenInputOf (T : ∀ {ι : Type}, CoxeterMatrix ι → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      NSJoinGuardOf T p L Bs 𝒦 →
      ∀ K : Subgroup G, GGSecFiveWeakNbr p B Bs x L D J 𝒦 K →
        K ≤ ⨆ r : MulAut ↥Bs, ⨆ (_ : r ∈ ggAutomizer K Bs), ⨆ (_ : GGIsReflection p r),
          ggRankOneIn K Bs r

theorem nsNbrOutLocalGenInputOf_of_weak' {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hL : GGLBalanceInput)
    (hT3 : ∀ {ι : Type} {M : CoxeterMatrix ι}, T M → ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hBaseL1 : GGSecFiveL1PhanInput) (hBaseRk1 : GGSecFiveRk1PhanInput)
    (hP : GGStdSubPrimeInput) (hPumpNbr : NSPumpNbrInputOf T) (hJA2 : NSJA2InputOf T)
    (hWRk1 : NSWeakRk1InputOf T) (hWGen : NSWeakGenInputOf T) : NSNbrOutLocalGenInputOf T := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hns hguard y K hK hmem hKA
  obtain ⟨ι, M, e, hpres, hT, hbig⟩ := hguard
  have h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := hT3 hT
  obtain ⟨r₀, hr₀J, _r', _hr'J, hr₀refl, _hr'refl, _horder⟩ :=
    hJA2 G p B Bs x L D J 𝒦 ⟨hcfg, hns, ι, M, e, hpres, hT, hbig⟩
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
    ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres h3 (hKA hrKA) hr₀refl
  obtain ⟨hPumpWe, -⟩ := hPumpNbr G p B Bs x L D J 𝒦 ⟨hcfg, hns, ⟨ι, M, e, hpres, hT, hbig⟩⟩ y K hK
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
  have hw : GGSecFiveWeakNbr p B Bs x L D J 𝒦 K := ⟨⟨y, hK⟩, hKA⟩
  have hgen := hWGen G p B Bs x L D J 𝒦 hcfg hns ⟨ι, M, e, hpres, hT, hbig⟩ K hw
  have hRkL : GGRk1Concl p Bs L r₀ :=
    hBaseRk1 G p B Bs x L D J 𝒦 hcfg hns ι M e hpres h3 L (Or.inl rfl) r₀ hrLA hr₀C
  have hRkK : GGRk1Concl p Bs K r₀ :=
    hWRk1 G p B Bs x L D J 𝒦 hcfg hns ⟨ι, M, e, hpres, hT, hbig⟩ K hw r₀ hrKA hr₀refl
  have hseed : ggRankOnePerf Bs r₀ = ggRankOneIn L Bs r₀ :=
    hBaseL1 G p B Bs x L D J 𝒦 hcfg hns ι M e hpres h3 hbig L (Or.inl rfl) r₀ hrLA hr₀C
  have hL1K : ggRankOnePerf Bs r₀ = ggRankOneIn K Bs r₀ :=
    ggL1_transfer_nbr hcfg hns hpres h3 hrLA hr₀C (hbig r₀ hrLA hr₀C) hseed (Or.inr ⟨y, hK⟩) hrKA hr₀C
      hRkL hRkK
  have hEq : ggRankOneIn K Bs r₀ = ggRankOneIn L Bs r₀ := by
    rw [← hL1K, hseed]
  have hmin : ∀ N : Subgroup G, N ≤ ggRankOneIn K Bs r₀ → N ≠ ⊥ →
      (∀ a ∈ ggRankOneIn K Bs r₀, ∀ b ∈ N, a * b * a⁻¹ ∈ N) →
      ggRankOneIn K Bs r₀ ≤ N := by
    rw [hEq]
    exact ggRankOneIn_minimal_of_rk1 hBaseRk1 hcfg hns hpres h3 (Or.inl rfl) hrLA hr₀refl
      (hbig r₀ hrLA hr₀C)
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

theorem nsNbrOutLocalGenInputOf_of_weak {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hL : GGLBalanceInput)
    (hTAD : ∀ {ι : Type} {M : CoxeterMatrix ι}, T M → NSTypeAD M)
    (hT3 : ∀ {ι : Type} {M : CoxeterMatrix ι}, T M → ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hBaseL1 : GGSecFiveL1PhanInput) (hBaseRk1 : GGSecFiveRk1PhanInput)
    (hP : GGStdSubPrimeInput) (hPumpNbr : NSPumpNbrInput) (hJA2 : NSJA2InputOf T)
    (hWRk1 : NSWeakRk1InputOf T) (hWGen : NSWeakGenInputOf T) : NSNbrOutLocalGenInputOf T :=
  nsNbrOutLocalGenInputOf_of_weak' hL hT3 hBaseL1 hBaseRk1 hP
    (fun G _ _ p B Bs x L D J 𝒦 hreg =>
      hPumpNbr G p B Bs x L D J 𝒦 ⟨hreg.1, hreg.2.1, NSJoinGuardOf.mono hTAD hreg.2.2⟩)
    hJA2 hWRk1 hWGen

end NSJoin

end CFSG.StandardType

end
