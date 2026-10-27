module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b
public import CFSG.LocalAnalysis.UniquenessCase.UC1S4Defs462
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XChiefY
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XOddQuot
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XNoQuot
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XBasic
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.GroupTheory.ThreeTranspositions (HasE9)

variable {G : Type} [Group G] [Finite G]

private theorem n924x_opp_le_self (p : ℕ) (Y : Subgroup G) : Opp p Y ≤ Y := by
  unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
  exact (closure_le Y).2 fun _ hx => hx.1

private theorem n924x_exists_chief_factor_under_of_le {r : ℕ} {X Y U W : Subgroup G}
    (hXY : X ≤ Y) (hUW : CFSG.ABGLocalTools.IsChiefFactorUnder r Y U W) :
    ∃ U₁ : Subgroup G, W ≤ U₁ ∧ U₁ ≤ U ∧ X ≤ normalizer (U₁ : Set G) ∧ U₁ ≠ W ∧
      CFSG.ABGLocalTools.IsChiefFactorUnder r X U₁ W := by
  classical
  have hWU : W ≤ U := hUW.1.le
  have hXU : X ≤ normalizer (U : Set G) := hXY.trans hUW.2.1
  have hex : ∃ m : ℕ, ∃ U₁ : Subgroup G, W ≤ U₁ ∧ U₁ ≤ U ∧
      X ≤ normalizer (U₁ : Set G) ∧ U₁ ≠ W ∧ m = Nat.card U₁ :=
    ⟨Nat.card U, U, hWU, le_rfl, hXU, (ne_of_lt hUW.1).symm, rfl⟩
  obtain ⟨U₁, hWU₁, hU₁U, hXU₁, hU₁ne, hU₁card⟩ := Nat.find_spec hex
  have hmin : ∀ V : Subgroup G, W ≤ V → V ≤ U → X ≤ normalizer (V : Set G) → V ≠ W →
      Nat.card U₁ ≤ Nat.card V := by
    intro V hWV hVU hXV hVne
    rw [← hU₁card]
    exact Nat.find_min' hex ⟨V, hWV, hVU, hXV, hVne, rfl⟩
  refine ⟨U₁, hWU₁, hU₁U, hXU₁, hU₁ne, ?_⟩
  refine ⟨lt_of_le_of_ne hWU₁ (Ne.symm hU₁ne), hXU₁, hXY.trans hUW.2.2.1, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    exact hUW.2.2.2.1 x (hU₁U hx) y hy
  · intro x hx y hy
    exact hUW.2.2.2.2.1 x (hU₁U hx) y (hU₁U hy)
  · intro x hx
    exact hUW.2.2.2.2.2.1 x (hU₁U hx)
  · intro X' hWX' hX'U₁ hNX'
    by_cases hX'W : X' = W
    · exact Or.inl hX'W
    · exact Or.inr (Subgroup.eq_of_le_of_card_ge hX'U₁
        (hmin X' hWX' (hX'U₁.trans hU₁U) hNX' hX'W))

theorem I9_le_of_hyp97_L2_4n (D : Data G) (hK462 : UCK.K462)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    {Y H D₃ S X : Subgroup G} {n : ℕ} (hyp : F09.Hyp97 D Y H D₃ S) (hYX : Opp 3 Y = X)
    (hn : 1 < n) (hL2 : IsL2 (Bar2 X) (2 * n)) (hXp : ⁅X, X⁆ = X)
    (hSH : CFSG.ABGLocalTools.IsSylowOf 2 S H) (hXY : (X.subgroupOf Y).Normal)
    (hHt : H ≠ ⊤) : F09.I9 H ≤ D.M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hIM
  obtain ⟨⟨hY9, hH9, hD₃X, hZ3⟩, -, -, hSY⟩ := hyp
  have hYH : Y ≤ H := hH9.1
  have hYM : Y ≤ D.M := hY9.1
  have hXleY : X ≤ Y := hYX ▸ n924x_opp_le_self 3 Y
  have hYnX : Y ≤ normalizer (X : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXleY).mp hXY
  have hZX : D₃ ≤ X := hYX ▸ hD₃X
  have hHK : CFSG.Open.IsKGroup ↥H :=
    CFSG.Open.IsKProper.isKGroup D.standing.kProper H hHt
  have hXH : X ≤ H := hXleY.trans hYH
  have hIleH : F09.I9 H ≤ H := Subgroup.map_subtype_le (CFSG.pPrimeCore 3 ↥H)
  have hKK : CFSG.Open.IsKGroup ↥X := CFSG.Open.IsKGroup.of_le hHK hXH
  have hKG : CFSG.Open.IsKGroup ↥(F09.I9 H ⊔ Y) :=
    CFSG.Open.IsKGroup.of_le hHK (sup_le hIleH hYH)
  have hE9 : ¬ HasE9 ↥(Opp 3 Y) := F09.not_hasE9_opp ⟨hY9, hH9, hD₃X, hZ3⟩
  have hE9X : ¬ HasE9 ↥X := hYX ▸ hE9
  have hDU : D₃ ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M :=
    hY9.2.2 D₃ (hD₃X.trans (n924x_opp_le_self 3 Y)) hZ3
  have hCZ : centralizer (D₃ : Set G) ≤ D.M :=
    (Subgroup.centralizer_le_normalizer (D₃ : Set G)).trans
      (CFSG.LocalAnalysis.RankThreeUC.normalizer_le_of_mem_uniqueSet D.maxLocal hDU)
  have hHI : H ≤ normalizer (F09.I9 H : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro h hh x hx
    have hx' : x ∈ (CFSG.pPrimeCore 3 ↥H).map H.subtype := hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx'
    exact Subgroup.mem_map.mpr
      ⟨⟨h, hh⟩ * y * ⟨h, hh⟩⁻¹,
        (CFSG.pPrimeCore_normal (p := 3) (G := ↥H)).conj_mem y hy ⟨h, hh⟩, rfl⟩
  have hI3 : ¬ 3 ∣ Nat.card (F09.I9 H) := by
    change ¬ 3 ∣ Nat.card ((CFSG.pPrimeCore 3 ↥H).map H.subtype)
    rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
      (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥H))
  have hXgen : ∀ B : Subgroup G, B ≤ X → X ≤ normalizer (B : Set G) → D₃ ≤ B → B = X :=
    fun B hBX hXB hD₃B => eq_of_normal_of_isL2 hXp hL2 hBX hXB hD₃B hZ3
  obtain ⟨r, U, W, hr, hr3, hUW, hUle, hWM, hUMleW, hfix⟩ :=
    exists_chief_factor_not_le_Y hSch hKG hZX hXleY hYnX hZ3 hYM hCZ hXp hXgen
      (hYH.trans hHI) hI3 hIM
  by_cases hr2 : r = 2
  · have hUH : U ≤ H := hUle.trans hIleH
    have hSU : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ U) U := by
      have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 S (S ⊔ U) :=
        hSH.of_le le_sup_left (sup_le hSH.le hUH)
      exact hSyl.inf_of_le_normalizer le_sup_right
        (sup_le (hSY.le.trans hUW.2.1) Subgroup.le_normalizer)
    have hle : S ⊓ U ≤ W :=
      (le_inf inf_le_right (inf_le_left.trans (hSY.le.trans hYM))).trans hUMleW
    have hUWn : U ≤ normalizer (W : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      intro u hu w hw
      exact hUW.2.2.2.1 u hu w hw
    haveI hWn : (W.subgroupOf U).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hUW.1.le).mpr hUWn
    have hP : IsPGroup 2 (↥U ⧸ W.subgroupOf U) := by
      intro g
      refine ⟨1, ?_⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective (s := W.subgroupOf U) g
      rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr
        (by simpa using (hr2 ▸ hUW.2.2.2.2.2.1 (x : G) x.2))
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hP
    have hWidx : (W.subgroupOf U).index = 2 ^ k := by
      rw [Subgroup.index_eq_card, hk]
    have hdvd : (W.subgroupOf U).index ∣ ((S ⊓ U).subgroupOf U).index :=
      Subgroup.index_dvd_of_le fun _ hx => hle hx
    have hodd : ¬ 2 ∣ ((S ⊓ U).subgroupOf U).index :=
      (CFSG.ABGLocalTools.isSylowOf_iff.mp hSU).2.2
    have hk0 : k = 0 := by
      by_contra hk0
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      exact hodd (dvd_trans (hWidx ▸ dvd_pow_self 2 (Nat.succ_ne_zero j)) hdvd)
    have hWtop : W.subgroupOf U = ⊤ :=
      (Subgroup.index_eq_one).mp (by rw [hWidx, hk0, pow_zero])
    exact absurd (le_antisymm (Subgroup.subgroupOf_eq_top.mp hWtop) hUW.1.le)
      (ne_of_gt hUW.1)
  · obtain ⟨U₁, hWU₁, hU₁U, hXU₁, hU₁ne, hUW₁⟩ :=
      n924x_exists_chief_factor_under_of_le hXleY hUW
    have hfix₁ : ∀ u ∈ U₁, (∀ x ∈ D₃, x * u * x⁻¹ * u⁻¹ ∈ W) → u ∈ W :=
      fun u hu h => hfix u (hU₁U hu) h
    obtain ⟨N, hNn, hN3, hcases⟩ :=
      chief_quot_cases_odd hK462 hKK hE9X hXp hZX hZ3 hXgen hr hr2 hUW₁ hfix₁
    haveI : N.Normal := hNn
    exact false_of_odd_quot (Q := ↥X) hn hL2 N hN3 hcases

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
