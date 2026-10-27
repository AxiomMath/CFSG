module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34D33
public import CFSG.Quasithin.Background.F918P8
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem513D3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedSp StatedClassicalModel StatedProj StatedScalars
open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative Pointwise

theorem d310_of_d35_of_orbSup_eq_top (h35 : D35) {W : Type} [CommGroup W] [Finite W]
    {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} (hD : D3Std M Mp T L V) (hMp : Mp = L)
    (htop : orbSup T V = ⊤) : (∀ t ∈ T, t ∈ stabSub V) ∨ D310Two T L V := by
  have hC' := d310_centralizer_le_center hD.hyp hMp
  subst hMp
  by_cases hT : ∀ t ∈ T, t ∈ stabSub V
  · exact Or.inl hT
  · right
    push Not at hT
    have hlt := d310_lt_orbSup hT
    obtain ⟨-, ⟨t₀, ht₀, ht₀n⟩, h4, h5⟩ := h35 W M Mp T Mp V hD hlt hC'
    refine ⟨?_, ⟨t₀, ht₀, ht₀n⟩, fun t ht htn => ?_⟩
    · unfold D35Five at h5
      rcases h5 with h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · have hs := (h4 t ht htn).2
      refine ⟨?_, d310_not_secIsoL hD ht hs⟩
      rw [htop, top_inf_eq] at hs
      exact hs

section Internal

variable {Γ : Type} [Group Γ]

theorem orbSup_autOn_eq_top (I T : Subgroup Γ) [IsMulCommutative ↥(conjClosure I T)] :
    orbSup (autOn T (conjClosure I T)) (I.subgroupOf (conjClosure I T)) = ⊤ := by
  set W := conjClosure I T with hWdef
  have hTW : T ≤ Subgroup.normalizer (W : Set Γ) := le_normalizer_conjClosure I T
  have hbiSup : (⨆ y ∈ autOn T W, y • I.subgroupOf W) =
      ⨆ y ∈ onA W T, y • I.subgroupOf W :=
    biSup_smul_eq_of_actCompat (actCompat_autOn_onA T) _
  rw [orbSup_eq_biSup_smul, hbiSup]
  apply Subgroup.map_injective W.subtype_injective
  rw [map_biSup_smul hTW, Subgroup.map_subgroupOf_eq_of_le (le_conjClosure I T),
    map_subtype_top]

variable [Finite Γ]

theorem eq_conjClosure_of_d35 (h35 : D35) {M K T I : Subgroup Γ} (hM : SQTKGroup ↥M)
    (hT : IsSylowTwoOf T M) (hMK : M ≤ Subgroup.normalizer (K : Set Γ)) (hMKT : M = K ⊔ T)
    (hI : IsIrrPlusIn K (conjClosure I T) T I) (hVT : IsElemAbelian 2 (conjClosure I T))
    (hO2 : pCoreOf 2 (autOn M (conjClosure I T)) = ⊥)
    (hKq : CFSG.IsQuasisimple ↥(autOn K (conjClosure I T)))
    (hq : qhatInt M (conjClosure I T) hVT ≤ 2)
    (hnot : ∀ (V : Type) [CommGroup V] (T' L' : Subgroup (MulAut V)) (U : Subgroup V),
      Nonempty (↥L' ≃* ↥(autOn K (conjClosure I T))) → ¬ D310Two T' L' U) :
    I = conjClosure I T := by
  have : IsMulCommutative ↥(conjClosure I T) := hVT.1
  have hq' : qhatOf (autOn M (conjClosure I T)) ≤ ((2 : ℚ) : WithTop ℚ) := by
    have h2 : qhatInt M (conjClosure I T) hVT ≤ ((2 : ℚ) : WithTop ℚ) := by exact_mod_cast hq
    exact h2
  have hD := d3Std_of_internal hM hT hMK hMKT hI hVT.2 hO2 hKq hq'
  rcases d310_of_d35_of_orbSup_eq_top h35 hD rfl (orbSup_autOn_eq_top I T) with hstab | htwo
  · have hTW : T ≤ Subgroup.normalizer (conjClosure I T : Set Γ) := le_normalizer_conjClosure I T
    refine le_antisymm (le_conjClosure I T) (conjClosure_le fun t ht i hi => ?_)
    have hτ : conjAct (conjClosure I T) ⟨t, hTW ht⟩ ∈ autOn T (conjClosure I T) :=
      ⟨⟨t, hTW ht⟩, ht, rfl⟩
    exact (hstab _ hτ ⟨i, le_conjClosure I T hi⟩).mpr hi
  · exact (hnot _ _ _ _ ⟨MulEquiv.refl _⟩ htwo).elim

theorem d310L2Fact_of_d35 (h35 : D35) : D310L2Fact := by
  intro Γ _ _ M K T I n hM hT _ hMK hMKT hI hVT hO2 hL hq
  have hX : IsPSL 2 2 n ↥(autOn K (conjClosure I T)) :=
    CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hL
  have hn : 1 ≤ n := hX.1.2.1
  have hcard := card_of_isPSL_two hX
  have h2 : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) 2
  have h3 : 3 ≤ (2 ^ n) ^ 2 - 1 := by
    have : 4 ≤ (2 ^ n) ^ 2 := by nlinarith
    omega
  refine eq_conjClosure_of_d35 h35 hM hT hMK hMKT hI hVT hO2
    (isQuasisimple_of_isPSL hX ?_ ?_) hq
    fun V _ T' L' U ⟨e⟩ => not_d310Two_of_isPSL_two hX T' L' U e
  · rw [hcard]
    positivity
  · rw [hcard]
    exact Nat.not_prime_mul (by omega) (by omega)

theorem d310L34Fact_of_d35 (h35 : D35) : D310L34Fact := by
  intro Γ _ _ M K T I hM hT _ hMK hMKT hI hVT hO2 hL hq
  have hX : IsPSL 3 2 2 ↥(autOn K (conjClosure I T)) :=
    CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hL
  have hcard := card_of_isPSL_three_four hX
  refine eq_conjClosure_of_d35 h35 hM hT hMK hMKT hI hVT hO2
    (isQuasisimple_of_isPSL hX (by rw [hcard]; norm_num) (by rw [hcard]; norm_num)) hq
    fun V _ T' L' U ⟨e⟩ => not_d310Two_of_isPSL_three_four hX T' L' U e

end Internal

end CFSG.Quasithin.H13
