module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFifteenProof
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFifteenSwap
public import CFSG.GroupTheory.PCore.QuotMulAut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.CGT.Timmesfeld75 (IsTI)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isL3_image_bar2 {L N : Subgroup G} (hLN : L ≤ N)
    (hsub : CFSG.Open.IsSubnormal L N) (h7 : IsL2Over17 (Bar2 L) 7) :
    IsL3 ↥((L.subgroupOf N).map (QuotientGroup.mk' (CFSG.pCore 2 ↥N))) 1 := by
  have hL3 : IsL3 (Bar2 L) 1 := isL3_one_of_isL2Over17_seven h7
  obtain ⟨e, -⟩ := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20d_bar2Equiv hLN hsub
  exact CFSG.Blueprint.LieModel.of_mulEquiv e hL3

@[expose] noncomputable def autBar2 {L N : Subgroup G} :
    ↥(N ⊓ normalizer (L : Set G)) →* MulAut (Bar2 L) :=
  (CFSG.pCoreQuotMulAut ↥L).comp
    ((Subgroup.normalizerMonoidHom L).comp (Subgroup.inclusion inf_le_right))

theorem autBar2_apply_mk_coe {L N : Subgroup G} (x : ↥(N ⊓ normalizer (L : Set G)))
    (v : ↥L) :
    (autBar2 (L := L) (N := N) x) (v : Bar2 L) =
      (QuotientGroup.mk (Subgroup.normalizerMonoidHom L
        (Subgroup.inclusion inf_le_right x) v) : Bar2 L) :=
  CFSG.pCoreQuotMulAut_mk _ v

theorem autBar2_eq_one_iff {L N : Subgroup G}
    (x : ↥(N ⊓ normalizer (L : Set G))) :
    autBar2 (L := L) (N := N) x = 1 ↔
      (x : G) ∈ centSection N L (CFSG.Open.pCoreOf 2 L) := by
  constructor
  · intro hx
    have hnormB : (x : G) ∈ normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L x.2.2
    refine ⟨x.2.1, x.2.2, hnormB, ?_⟩
    intro a ha
    let v : ↥L := ⟨a, ha⟩
    have hq : (QuotientGroup.mk (Subgroup.normalizerMonoidHom L
        (Subgroup.inclusion inf_le_right x) v) : Bar2 L) = (v : Bar2 L) := by
      have h := congrArg (fun f : MulAut (Bar2 L) => f (v : Bar2 L)) hx
      simpa [autBar2_apply_mk_coe] using h
    have hdiv : Subgroup.normalizerMonoidHom L (Subgroup.inclusion inf_le_right x) v / v ∈
        CFSG.pCore 2 ↥L := QuotientGroup.eq_iff_div_mem.mp hq
    have hdivG : ((Subgroup.normalizerMonoidHom L (Subgroup.inclusion inf_le_right x) v / v :
        ↥L) : G) ∈ CFSG.Open.pCoreOf 2 L := Subgroup.mem_map_of_mem L.subtype hdiv
    have hw : ((Subgroup.normalizerMonoidHom L (Subgroup.inclusion inf_le_right x) v : ↥L) : G)
        = (x : G) * a * (x : G)⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe L (Subgroup.inclusion inf_le_right x) v
    rw [Subgroup.coe_div, hw] at hdivG
    simpa [div_eq_mul_inv, mul_assoc] using hdivG
  · intro hx
    obtain ⟨-, -, -, hcent⟩ := hx
    ext q
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
    rw [autBar2_apply_mk_coe]
    apply QuotientGroup.eq_iff_div_mem.mpr
    have hw : ((Subgroup.normalizerMonoidHom L (Subgroup.inclusion inf_le_right x) v : ↥L) : G)
        = (x : G) * (v : G) * (x : G)⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe L (Subgroup.inclusion inf_le_right x) v
    have hmem : ((Subgroup.normalizerMonoidHom L (Subgroup.inclusion inf_le_right x) v / v :
        ↥L) : G) ∈ CFSG.Open.pCoreOf 2 L := by
      rw [Subgroup.coe_div, hw]
      simpa [div_eq_mul_inv, mul_assoc] using hcent (v : G) v.2
    exact (Subgroup.mem_map_iff_mem L.subtype_injective).mp hmem

theorem pCore_three_bar2_eq_bot {L : Subgroup G} (h7 : IsL2Over17 (Bar2 L) 7) :
    CFSG.pCore 3 (Bar2 L) = ⊥ := by
  have hcard : Nat.card (Bar2 L) = 168 :=
    card_of_isL2Odd_seven (isL2Odd_seven_of_isL2Over17_seven h7)
  obtain ⟨r, f, hr, hr2, hq, hf, hmodel⟩ := h7
  have hsimple : IsSimpleGroup (Bar2 L) := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hmodel
  have hnot : ¬ IsPGroup 3 (Bar2 L) := by
    intro hp
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
    rw [hcard] at hn
    have h2 : 2 ∣ 3 ^ n := by rw [← hn]; norm_num
    exact absurd (Nat.prime_two.dvd_of_dvd_pow h2) (by norm_num)
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal (Bar2 L) _ hsimple
    (CFSG.pCore 3 (Bar2 L)) (CFSG.pCore_normal) with h | h
  · exact h
  · exfalso
    have hp : IsPGroup 3 (⊤ : Subgroup (Bar2 L)) := by
      have hpc := CFSG.pCore_isPGroup (p := 3) (G := Bar2 L)
      rwa [h] at hpc
    exact hnot (hp.of_equiv Subgroup.topEquiv)

theorem oTwoThreeIn_eq_pCoreOf {L : Subgroup G} (h7 : IsL2Over17 (Bar2 L) 7) :
    CFSG.Quasithin.oTwoThreeIn L = CFSG.Open.pCoreOf 2 L := by
  have h3 : CFSG.pCore 3 (Bar2 L) = ⊥ := pCore_three_bar2_eq_bot h7
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    rw [h3] at hy
    have hy1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) y = 1 := Subgroup.mem_bot.mp hy
    exact hyx ▸ Subgroup.mem_map_of_mem L.subtype ((QuotientGroup.eq_one_iff y).mp hy1)
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨y, ?_, hyx⟩
    rw [h3]
    exact Subgroup.mem_bot.mpr ((QuotientGroup.eq_one_iff y).mpr hy)

theorem exists_bar2_data {L N : Subgroup G} (hLN : L ≤ N)
    (hsub : CFSG.Open.IsSubnormal L N) (hperf : ⁅L, L⁆ = L)
    (hq : CFSG.Open.IsQuasisimple (Bar2 L)) :
    ∃ (Z : Type) (_ : Group Z) (ψ : ↥N →* Z), Function.Surjective ψ ∧
      (∀ x : ↥N, ψ x = 1 ↔ (x : G) ∈ CFSG.Open.pCoreOf 2 N) ∧
      CFSG.IsComponent ((L.subgroupOf N).map ψ) := by
  refine ⟨Bar2 N, inferInstance, QuotientGroup.mk' (CFSG.pCore 2 ↥N),
    QuotientGroup.mk'_surjective _, ?_, ?_⟩
  · intro x
    exact CFSG.Quasithin.mk_eq_one_iff_mem_pCoreOf x
  · exact PartTwo.s13_barImage_isComponent (M := N) (L := L) ⟨hsub, hperf, hq⟩

theorem exists_bar2_data_l3 {L N : Subgroup G} (hLN : L ≤ N)
    (hsub : CFSG.Open.IsSubnormal L N) (hperf : ⁅L, L⁆ = L)
    (hq : CFSG.Open.IsQuasisimple (Bar2 L)) (h7 : IsL2Over17 (Bar2 L) 7) :
    ∃ (Z : Type) (_ : Group Z) (ψ : ↥N →* Z), Function.Surjective ψ ∧
      (∀ x : ↥N, ψ x = 1 ↔ (x : G) ∈ CFSG.Open.pCoreOf 2 N) ∧
      CFSG.IsComponent ((L.subgroupOf N).map ψ) ∧
      IsL3 ↥((L.subgroupOf N).map ψ) 1 := by
  refine ⟨Bar2 N, inferInstance, QuotientGroup.mk' (CFSG.pCore 2 ↥N),
    QuotientGroup.mk'_surjective _, ?_, ?_, ?_⟩
  · intro x
    exact CFSG.Quasithin.mk_eq_one_iff_mem_pCoreOf x
  · exact PartTwo.s13_barImage_isComponent (M := N) (L := L) ⟨hsub, hperf, hq⟩
  · exact isL3_image_bar2 hLN hsub h7

@[expose] def Gap17_15_threeConj (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q) : Prop :=
  IsL2Over17 (Bar2 L) 7 → ¬ IsL2Over17 (Bar2 (L ⊔ D.T)) 7 →
    ¬ 2 < (CFSG.LocalAnalysis.UniquenessCase.UC22.conjSetOf D.M L).ncard

@[expose] def Gap17_15_autPGL2 (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q) : Prop :=
  IsL2Over17 (Bar2 L) 7 → ¬ IsL2Over17 (Bar2 (L ⊔ D.T)) 7 →
    (L.subgroupOf (L ⊔ D.T)).Normal →
    CFSG.Quasithin.F6.IsPGL2 7 (Bar2 (L ⊔ D.T)) ∧
    ∃ (A : Type) (_ : Group A)
      (φ : ↥((L ⊔ D.T) ⊓ normalizer (L : Set G)) →* A),
      Function.Surjective φ ∧
      (∀ x : ↥((L ⊔ D.T) ⊓ normalizer (L : Set G)),
        φ x = 1 ↔ (x : G) ∈ centSection (L ⊔ D.T) L (oTwoThreeIn L)) ∧
      CFSG.Quasithin.F6.IsPGL2 7 A

@[expose] def Gap17_15_pairPGL2 (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q) : Prop :=
  CFSG.Quasithin.F6.IsPGL2 7 (Bar2 (L ⊔ D.T)) →
    CFSG.LocalAnalysis.WeakClosure81.InFSq 1 (L ⊔ D.T)

theorem gap17_15_pairOuter_of (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q) (h17_7 : R17_7At D V₀ V L r q hC)
    (hAut : Gap17_15_autPGL2 D V₀ V L r q hC)
    (hPGLInFSq : Gap17_15_threeConjInFSq D V₀ V L r q hC)
    (hSplit : Gap17_15_swapSplit D V₀ V L r q hC)
    (hSwPair : Gap17_15_swapPairInner D V₀ V L r q hC)
    (hSwInFSq : Gap17_15_swapInFSq D V₀ V L r q hC)
    (hPairPGL : Gap17_15_pairPGL2 D V₀ V L r q hC) :
    Gap17_15_pairOuter D V₀ V L r q hC := by
  intro h7 hYs
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le hC.memL.1
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hNM : L ⊔ D.T ≤ D.M := sup_le hLM hTM
  have hO2 : ∀ g : G, g ∉ D.M →
      ¬ twoResidual (L ⊔ D.T) ≤ conjSubgroup D.M g := by
    intro g hg hle
    exact twoResidual_not_le_conjSubgroup_of_uniqueMax D.maxLocal h17_7.1
      (CFSG.Quasithin.H13.A5.le_twoResidual_of_perfect hC.memL.2.1 le_sup_left) hg hle
  by_cases hN : (L.subgroupOf (L ⊔ D.T)).Normal
  · obtain ⟨hPGL, -⟩ := hAut h7 hYs hN
    have hEq : (L ⊔ D.T) ⊔ (L ⊔ D.T) ⊔ D.T = L ⊔ D.T := by
      rw [sup_idem, sup_eq_left.mpr le_sup_right]
    have hU : UniqueMax D.M (L ⊔ D.T) :=
      uc22p22u_uniqueMax_mono D le_sup_left hNM h17_7.1
    refine ⟨L ⊔ D.T, L ⊔ D.T, le_sup_right, hNM, le_sup_right, hNM, ?_,
      hPairPGL hPGL, hPairPGL hPGL, hO2, hO2, ?_⟩
    · rw [hEq]; exact le_sup_left
    · rw [hEq]; exact hU
  · rcases hSplit h7 hN with hInner | hOuter
    ·
      obtain ⟨X₁, X₂, hX₁L, hX₂L, hX₁c, hX₂c, hperm₁, hperm₂, hLgen⟩ :=
        hSwPair h7 hYs hInner hN
      have hIF₁ : CFSG.LocalAnalysis.WeakClosure81.InFSq 1 (X₁ ⊔ D.T) :=
        hSwInFSq h7 hYs hInner hN X₁ hX₁L hX₁c hperm₁
      have hIF₂ : CFSG.LocalAnalysis.WeakClosure81.InFSq 1 (X₂ ⊔ D.T) :=
        hSwInFSq h7 hYs hInner hN X₂ hX₂L hX₂c hperm₂
      have hH₁M : X₁ ⊔ D.T ≤ D.M := sup_le (hX₁L.trans hLM) hTM
      have hH₂M : X₂ ⊔ D.T ≤ D.M := sup_le (hX₂L.trans hLM) hTM
      have hgen : L ≤ (X₁ ⊔ D.T) ⊔ (X₂ ⊔ D.T) ⊔ D.T := by
        have hEq : (X₁ ⊔ D.T) ⊔ (X₂ ⊔ D.T) ⊔ D.T = X₁ ⊔ X₂ ⊔ D.T := by ac_rfl
        rw [hEq]; exact hLgen
      have hU : UniqueMax D.M ((X₁ ⊔ D.T) ⊔ (X₂ ⊔ D.T) ⊔ D.T) :=
        uc22p22u_uniqueMax_mono D hgen (sup_le (sup_le hH₁M hH₂M) hTM) h17_7.1
      refine ⟨X₁ ⊔ D.T, X₂ ⊔ D.T, le_sup_right, hH₁M, le_sup_right, hH₂M, hgen, hIF₁, hIF₂,
        ?_, ?_, hU⟩
      · intro g hg hle
        have hXle : X₁ ≤ twoResidual (X₁ ⊔ D.T) :=
          le_twoResidual_of_odd_prime_card (H := X₁ ⊔ D.T) (X := X₁) le_sup_left
            Nat.prime_three (by norm_num) hX₁c
        have hXg : X₁ ≤ conjSubgroup D.M g := hXle.trans hle
        have h3dvd : 3 ∣ Nat.card ↥(L ⊓ conjSubgroup D.M g) := by
          have hXleLinf : X₁ ≤ L ⊓ conjSubgroup D.M g := le_inf hX₁L hXg
          have hcard := Subgroup.card_dvd_of_le hXleLinf
          rwa [hX₁c] at hcard
        have hg' : g⁻¹ ∉ D.M := fun h => hg (by simpa using D.M.inv_mem h)
        refine h17_7.2 h7 g⁻¹ hg' ⟨Nat.prime_three, ?_⟩
        simpa [conjSubgroup] using h3dvd
      · intro g hg hle
        have hXle : X₂ ≤ twoResidual (X₂ ⊔ D.T) :=
          le_twoResidual_of_odd_prime_card (H := X₂ ⊔ D.T) (X := X₂) le_sup_left
            Nat.prime_three (by norm_num) hX₂c
        have hXg : X₂ ≤ conjSubgroup D.M g := hXle.trans hle
        have h3dvd : 3 ∣ Nat.card ↥(L ⊓ conjSubgroup D.M g) := by
          have hXleLinf : X₂ ≤ L ⊓ conjSubgroup D.M g := le_inf hX₂L hXg
          have hcard := Subgroup.card_dvd_of_le hXleLinf
          rwa [hX₂c] at hcard
        have hg' : g⁻¹ ∉ D.M := fun h => hg (by simpa using D.M.inv_mem h)
        refine h17_7.2 h7 g⁻¹ hg' ⟨Nat.prime_three, ?_⟩
        simpa [conjSubgroup] using h3dvd
    ·
      have hPGL := hOuter
      have hIF : CFSG.LocalAnalysis.WeakClosure81.InFSq 1 (L ⊔ D.T) :=
        hPGLInFSq h7 hPGL
      have hEq : (L ⊔ D.T) ⊔ (L ⊔ D.T) ⊔ D.T = L ⊔ D.T := by
        rw [sup_idem, sup_eq_left.mpr le_sup_right]
      have hU : UniqueMax D.M (L ⊔ D.T) :=
        uc22p22u_uniqueMax_mono D le_sup_left hNM h17_7.1
      refine ⟨L ⊔ D.T, L ⊔ D.T, le_sup_right, hNM, le_sup_right, hNM, ?_,
        hIF, hIF, hO2, hO2, ?_⟩
      · rw [hEq]; exact le_sup_left
      · rw [hEq]; exact hU

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

end

