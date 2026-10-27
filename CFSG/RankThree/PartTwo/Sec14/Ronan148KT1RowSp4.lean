module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148KT1Rows
public import CFSG.RankThree.PartTwo.Sec14.Ronan148KT1RowRuTh
public import CFSG.RankThree.PartTwo.Sec14.Ronan148KT1RowGH
public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusSp4Main
public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusSp4Odd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoSchreier
import CFSG.ClassicalGroups.Symplectic.Simple
import CFSG.Timmesfeld.Orders.ClassicalLinear
import CFSG.GH74.GLS.IVK.L2.Fixed
import CFSG.RankThree.PartTwo.KFacts.K71IdentPSU3
public import CFSG.GH74.GLS.Balance.SolvAPIDefs
public import CFSG.HardMathSupport.Cooperstein.Proving.NineThreeTransfer
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabThCentU
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFDefs
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Basic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8L4
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.RankThree.PartTwo.Sec11.Inverter1118Proof
public import CFSG.RankThree.PartTwo.Sec11.Inverter1118ProofSteps
public import CFSG.RankThree.PartTwo.Sec11.Item1121Proof
public import CFSG.RankThree.PartTwo.Sec11.Item119K
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.RankThree.PartTwo.Sec14.Item142ResProofPGL
public import CFSG.RankThree.PartTwo.Sec15.Item157
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
public import CFSG.RankThree.PartTwo.Sec16.Item169HJ
public import CFSG.RankThree.PartTwo.Sec17.Item1724Two
public import CFSG.RankThree.PartTwo.Sec17.Item17TailSteps
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
public import CFSG.RankThree.PartTwo.Sec20.OneSteps
public import CFSG.RankThree.PartTwo.Sec21.Item211ProofListOf
public import CFSG.RankThree.PartTwo.Sec4.Item41NarrowGriess
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowSpor
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434CharThreeAssembly
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVDefs
public import CFSG.RankThree.S4Free.SuzukiEight
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FixedFieldCard
public import CFSG.Walter.J1Props
public import Certificates.Certificate14953
public import Certificates.Certificate8166

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148K

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSp)
open CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  (spScalars ker_proj proj_surjective conjAut gsp multiplier conjAut_mem_inner_of_isSquare
    spScalars_le_center)
open CFSG.RankThree.PartTwo.Sec6.BThreeCensus
  (sp4EquivProj center_statedProj_sp4_eq_bot center_statedProj_sp4_eq_bot_of_four_le
    orderOf_ne_three_of_card_prime sq_eq_one_of_mem_spScalars eq_of_mul_inv_mem_center
    eq_one_of_pow_three_of_not_three_dvd eq_bot_of_commute_of_mem_statedSp three_ne_zero_of_charTwo
    three_ne_zero_of_charP card_statedSp_two_of_card_two map_subgroupOf_subgroupMap)
open CFSG.RankThree.PartTwo.KFacts
  (psp4_odd_order_three_field_descent sp4_even_order_three_field_descent
    conjAut_mem_inner_of_charTwo mem_range_proj_spIncl_iff proj_spIncl_injective
    mem_range_conj_comp_iff exists_card_eq_two_pow spIncl)
open CFSG.RankThree.PartTwo.Sec4.RonanK429H
  (subsingleton_of_isPerfect_of_card_primeFactors primeFactors_card_le_two_of_dvd)
open CFSG.GH74.GLS.IVK (fixedField)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem sp4R148_bot_of_mulEquiv {S Q : Type} [Group S] [Group Q] (e : S ≃* Q)
    (h : ∀ β : MulAut Q, β ^ 3 = 1 → ∀ C Y : Subgroup Q, (∀ z, z ∈ C ↔ β z = z) → Y ≤ C →
      (Y.subgroupOf C).IsSubnormal → Group.IsPerfect Y → ¬ 3 ∣ Nat.card Y → Y = ⊥) :
    ∀ β : MulAut S, β ^ 3 = 1 → ∀ C Y : Subgroup S, (∀ z, z ∈ C ↔ β z = z) → Y ≤ C →
      (Y.subgroupOf C).IsSubnormal → Group.IsPerfect Y → ¬ 3 ∣ Nat.card Y → Y = ⊥ := by
  intro β hβ C Y hC hYC hsn hYp hY3
  set f : S →* Q := e.toMonoidHom with hf
  have hfz : ∀ z, z ∈ C.map f ↔ MulAut.congr e β z = z := by
    intro z
    rw [MulAut.congr_apply]
    constructor
    · rintro ⟨c, hc, rfl⟩
      simp [(hC c).mp hc, hf]
    · intro hz
      refine ⟨e.symm z, (hC _).mpr ?_, by simp [hf]⟩
      apply e.injective
      simpa using hz
  have hsn' : ((Y.map f).subgroupOf (C.map f)).IsSubnormal := by
    rw [← map_subgroupOf_subgroupMap]
    exact hsn.map (e.subgroupMap C).surjective
  have hYp' : Group.IsPerfect (Y.map f) := Group.IsPerfect.map f
  have hY3' : ¬ 3 ∣ Nat.card (Y.map f) := by
    rwa [Subgroup.card_map_of_injective e.injective]
  have key := h (MulAut.congr e β) (by rw [← map_pow, hβ, map_one]) (C.map f) (Y.map f) hfz
    (Subgroup.map_mono hYC) hsn' hYp' hY3'
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp key

theorem sp4R148Odd_bot {F : Type} [Field F] [Finite F] {p : ℕ}
    [Fact p.Prime] [CharP F p] (hp3 : 3 < p) (hF : Nat.card F = p)
    (h3 : 3 ∣ Nat.card (StatedProj (StatedSp 2 F))) :
    ∀ β : MulAut (StatedProj (StatedSp 2 F)), β ^ 3 = 1 →
      ∀ C Y : Subgroup (StatedProj (StatedSp 2 F)), (∀ z, z ∈ C ↔ β z = z) → Y ≤ C →
      (Y.subgroupOf C).IsSubnormal → Group.IsPerfect Y → ¬ 3 ∣ Nat.card Y → Y = ⊥ := by
  have hp : p.Prime := Fact.out
  have h4 : 4 ≤ Nat.card F := by omega
  have hodd : ringChar F ≠ 2 := by
    rw [ringChar.eq F p]
    omega
  have h3F : (3 : F) ≠ 0 := three_ne_zero_of_charP (by omega)
  have hsimpP : IsSimpleGroup (StatedProj (StatedSp 2 F)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F 2 (by norm_num)
      (Or.inl (Or.inr h4))
  have hZ := center_statedProj_sp4_eq_bot_of_four_le h4
  intro β hβ C Y hC hYC hsn hYp hY3
  have hD : β ∈ (conjAut 2 F).range := by
    by_contra hD
    obtain ⟨σ, hσ3, -⟩ := psp4_odd_order_three_field_descent hodd β hβ hD
    exact orderOf_ne_three_of_card_prime hp hF σ hσ3
  obtain ⟨A, rfl⟩ := hD
  have hinner : conjAut 2 F A ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (StatedProj (StatedSp 2 F)) := by
    have h4A : conjAut 2 F A = conjAut 2 F (A ^ 2) ^ 2 := by
      rw [← map_pow, ← pow_mul, map_pow]
      calc conjAut 2 F A = conjAut 2 F A ^ 3 * conjAut 2 F A := by rw [hβ, one_mul]
        _ = conjAut 2 F A ^ (2 * 2) := by rw [← pow_succ]
    rw [h4A]
    refine Subgroup.pow_mem _ (conjAut_mem_inner_of_isSquare ⟨(multiplier 2 F A : F), ?_⟩) 2
    rw [map_pow, Units.val_pow_eq_pow_val, sq]
  obtain ⟨x, hx⟩ := hinner
  have hx3 : x ^ 3 = 1 := by
    have h1 : MulAut.conj (x ^ 3) = 1 := by rw [map_pow, hx, hβ]
    have h2 : x ^ 3 ∈ Subgroup.center (StatedProj (StatedSp 2 F)) := by
      rw [Subgroup.mem_center_iff]
      intro z
      have := congrArg (fun φ : MulAut (StatedProj (StatedSp 2 F)) => φ z) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc z * x ^ 3 = x ^ 3 * z * (x ^ 3)⁻¹ * x ^ 3 := by rw [this]
        _ = x ^ 3 * z := by group
    rw [hZ, Subgroup.mem_bot] at h2
    exact h2
  by_cases hx1 : x = 1
  ·
    have hβ1 : conjAut 2 F A = 1 := by rw [← hx, hx1, map_one]
    have hCtop : C = ⊤ := by
      ext z
      simp [hC z, hβ1]
    have hsimp : IsSimpleGroup C :=
      ((MulEquiv.subgroupCongr hCtop).trans Subgroup.topEquiv).isSimpleGroup
    rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hsimp hsn with h | h
    · rw [Subgroup.subgroupOf_eq_bot] at h
      rw [eq_bot_iff]
      intro y hy
      exact Subgroup.mem_bot.mpr (Subgroup.disjoint_def.mp h hy (hYC hy))
    · rw [Subgroup.subgroupOf_eq_top] at h
      exfalso
      apply hY3
      have hYtop : Y = ⊤ := eq_top_iff.mpr (by rw [← hCtop]; exact h)
      rw [hYtop, Subgroup.card_top]
      exact h3
  obtain ⟨g₀, hg₀⟩ := proj_surjective (r := 2) (K := F) x
  have hz : g₀ ^ 3 ∈ spScalars 2 F := by
    rw [← ker_proj, MonoidHom.mem_ker, map_pow, hg₀, hx3]
  set g : StatedSp 2 F := g₀ ^ 4 with hg
  have hgx : proj 2 F g = x := by
    rw [hg, map_pow, hg₀]
    calc x ^ 4 = x ^ 3 * x := pow_succ x 3
      _ = x := by rw [hx3, one_mul]
  have hg3 : (g : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) F) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow]
    have : g ^ 3 = 1 := by
      calc g ^ 3 = ((g₀ ^ 3) ^ 2) ^ 2 := by rw [hg, ← pow_mul, ← pow_mul, ← pow_mul]
        _ = 1 := by rw [sq_eq_one_of_mem_spScalars hz, one_pow]
    rw [this, Subgroup.coe_one]
  have hg1 : (g : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) F) ≠ 1 := by
    intro h1
    apply hx1
    rw [← hgx, show g = 1 from Subtype.ext h1, map_one]
  have : Group.IsPerfect Y := hYp
  set Ŷ := Y.comap (QuotientGroup.mk' (spScalars 2 F)) with hŶ
  set D := ⁅Ŷ, Ŷ⁆ with hD
  have hDp : Group.IsPerfect D :=
    CFSG.RankThree.SubgroupLists.isPerfect_commutator_comap spScalars_le_center Y
  have hDmap : D.map (proj 2 F) = Y := CFSG.RankThree.SubgroupLists.map_commutator_comap Y
  have hD3 : ¬ 3 ∣ Nat.card D := by
    intro h3D
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' 3 h3D
    have hd3 : (d : StatedSp 2 F) ^ 3 = 1 := by
      have h1 := pow_orderOf_eq_one d
      rw [hd] at h1
      rw [← Subgroup.coe_pow, h1, Subgroup.coe_one]
    have hpd : proj 2 F d ∈ Y := hDmap ▸ ⟨d, d.2, rfl⟩
    have hpd1 : proj 2 F d = 1 :=
      eq_one_of_pow_three_of_not_three_dvd hY3 hpd (by rw [← map_pow, hd3, map_one])
    have hdz : (d : StatedSp 2 F) ∈ spScalars 2 F := by
      rw [← ker_proj]
      exact hpd1
    have hd2 := sq_eq_one_of_mem_spScalars hdz
    have hd1 : (d : StatedSp 2 F) = 1 := by
      calc (d : StatedSp 2 F) = (d : StatedSp 2 F) ^ 3 * ((d : StatedSp 2 F) ^ 2)⁻¹ := by group
        _ = 1 := by rw [hd3, hd2, inv_one, one_mul]
    rw [show d = 1 from Subtype.ext hd1, orderOf_one] at hd
    omega
  have hfix : ∀ y ∈ D, (MulAut.conj g).toMonoidHom y = y := by
    refine eq_of_mul_inv_mem_center hDp (MulAut.conj g).toMonoidHom fun y hy => ?_
    apply spScalars_le_center
    rw [← ker_proj, MonoidHom.mem_ker, map_mul, map_inv]
    have hyY : proj 2 F y ∈ Y := hDmap ▸ ⟨y, hy, rfl⟩
    have h1 := (hC _).mp (hYC hyY)
    rw [← hx, MulAut.conj_apply] at h1
    change proj 2 F (g * y * g⁻¹) * (proj 2 F y)⁻¹ = 1
    rw [map_mul, map_mul, map_inv, hgx, h1, mul_inv_cancel]
  set D' : Subgroup (Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) F) :=
    D.map (StatedSp 2 F).subtype with hD'
  have hD'bot : D' = ⊥ := by
    refine eq_bot_of_commute_of_mem_statedSp h3F g.2 hg3 hg1 D' ?_ ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      have h1 := congrArg Subtype.val (hfix y hy)
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] at h1
      change (y : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) F) * (g : Matrix.GeneralLinearGroup
        (Fin 2 ⊕ Fin 2) F) = (g : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) F) *
          (y : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) F)
      calc (y : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) F) * (g : Matrix.GeneralLinearGroup
            (Fin 2 ⊕ Fin 2) F) = (g : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) F) * y *
              (g : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) F)⁻¹ *
                (g : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) F) := by rw [h1]
        _ = (g : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) F) * y := by group
    · exact Group.IsPerfect.map _
    · rwa [Subgroup.card_map_of_injective (StatedSp 2 F).subtype_injective]
  have hDbot : D = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective D (StatedSp 2 F).subtype_injective).mp hD'bot
  rw [← hDmap, hDbot, Subgroup.map_bot]

theorem sp4R148Two_bot {F : Type} [Field F] [Finite F] [CharP F 2]
    (hsimpP : IsSimpleGroup (StatedProj (StatedSp 2 F)))
    (h3 : 3 ∣ Nat.card (StatedProj (StatedSp 2 F))) :
    ∀ β : MulAut (StatedProj (StatedSp 2 F)), β ^ 3 = 1 →
      ∀ C Y : Subgroup (StatedProj (StatedSp 2 F)), (∀ z, z ∈ C ↔ β z = z) → Y ≤ C →
      (Y.subgroupOf C).IsSubnormal → Group.IsPerfect Y → ¬ 3 ∣ Nat.card Y → Y = ⊥ := by
  have h3F : (3 : F) ≠ 0 := three_ne_zero_of_charTwo
  intro β hβ C Y hC hYC hsn hYp hY3
  by_cases hD : β ∈ (conjAut 2 F).range
  ·
    obtain ⟨A, rfl⟩ := hD
    obtain ⟨x, hx⟩ := conjAut_mem_inner_of_charTwo A
    rw [← hx] at hβ hC
    have hx3 : x ^ 3 = 1 := by
      have h1 : MulAut.conj (x ^ 3) = 1 := by rw [map_pow]; exact hβ
      have h2 : x ^ 3 ∈ Subgroup.center (StatedProj (StatedSp 2 F)) := by
        rw [Subgroup.mem_center_iff]
        intro z
        have := congrArg (fun φ : MulAut (StatedProj (StatedSp 2 F)) => φ z) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        calc z * x ^ 3 = x ^ 3 * z * (x ^ 3)⁻¹ * x ^ 3 := by rw [this]
          _ = x ^ 3 * z := by group
      rw [center_statedProj_sp4_eq_bot, Subgroup.mem_bot] at h2
      exact h2
    by_cases hx1 : x = 1
    · subst hx1
      have hCtop : C = ⊤ := by
        ext z
        simp [hC z]
      have hsimp : IsSimpleGroup C :=
        ((MulEquiv.subgroupCongr hCtop).trans Subgroup.topEquiv).isSimpleGroup
      rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hsimp hsn with h | h
      · rw [Subgroup.subgroupOf_eq_bot] at h
        rw [eq_bot_iff]
        intro y hy
        exact Subgroup.mem_bot.mpr (Subgroup.disjoint_def.mp h hy (hYC hy))
      · rw [Subgroup.subgroupOf_eq_top] at h
        exfalso
        apply hY3
        have hYtop : Y = ⊤ := eq_top_iff.mpr (by rw [← hCtop]; exact h)
        rw [hYtop, Subgroup.card_top]
        exact h3
    ·
      set e : StatedSp 2 F ≃* StatedProj (StatedSp 2 F) := sp4EquivProj with he
      set g : StatedSp 2 F := e.symm x with hg
      have hg3 : (g : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) F) ^ 3 = 1 := by
        rw [← Subgroup.coe_pow, hg, ← map_pow, hx3, map_one, Subgroup.coe_one]
      have hg1 : (g : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) F) ≠ 1 := by
        intro h1
        apply hx1
        have : g = 1 := Subtype.ext h1
        rw [hg] at this
        have := congrArg e this
        rwa [MulEquiv.apply_symm_apply, map_one] at this
      set Y₀ : Subgroup (StatedSp 2 F) := Y.map e.symm.toMonoidHom with hY₀
      have hY₀p : Group.IsPerfect Y₀ := by
        have := hYp
        exact Group.IsPerfect.map _
      have hY₀card : Nat.card Y₀ = Nat.card Y := Subgroup.card_map_of_injective e.symm.injective
      set Y₁ : Subgroup (Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) F) :=
        Y₀.map (StatedSp 2 F).subtype with hY₁
      have hY₁ : Y₁ = ⊥ := by
        refine eq_bot_of_commute_of_mem_statedSp h3F g.2 hg3 hg1 Y₁ ?_ ?_ ?_
        · rintro _ ⟨q, ⟨y, hy, rfl⟩, rfl⟩
          have hyC := (hC y).mp (hYC hy)
          rw [MulAut.conj_apply] at hyC
          have h1 : e.symm y * g = g * e.symm y := by
            rw [hg, ← map_mul, ← map_mul]
            congr 1
            calc y * x = x * y * x⁻¹ * x := by rw [hyC]
              _ = x * y := by group
          exact congrArg Subtype.val h1
        · have := hY₀p
          exact Group.IsPerfect.map _
        · rwa [Subgroup.card_map_of_injective (StatedSp 2 F).subtype_injective, hY₀card]
      have hY₀ : Y₀ = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective Y₀ (StatedSp 2 F).subtype_injective).mp hY₁
      exact (Subgroup.map_eq_bot_iff_of_injective Y e.symm.injective).mp hY₀
  ·
    obtain ⟨σ, hσ3, H, hβH⟩ := sp4_even_order_three_field_descent β hβ hD
    set ι : StatedSp 2 (fixedField σ) →* StatedProj (StatedSp 2 F) :=
      (conjAut 2 F H : StatedProj (StatedSp 2 F) ≃* StatedProj (StatedSp 2 F)).toMonoidHom.comp
        ((proj 2 F).comp (spIncl σ)) with hι
    have hιinj : Function.Injective ι :=
      (conjAut 2 F H).injective.comp (proj_spIncl_injective σ)
    have hCι : C = ι.range := by
      ext z
      rw [hC z, hβH]
      exact (mem_range_conj_comp_iff _ _ _ (mem_range_proj_spIncl_iff σ) z).symm
    have eC : C ≃* StatedSp 2 (fixedField σ) :=
      (MulEquiv.subgroupCongr hCι).trans (MonoidHom.ofInjective hιinj).symm
    have : CharP (fixedField σ) 2 := RingHom.charP _ (fixedField σ).subtype_injective 2
    have : Finite (fixedField σ) := Subtype.finite
    have hCe : C ≃* StatedProj (StatedSp 2 (fixedField σ)) := eC.trans sp4EquivProj
    by_cases h4 : 4 ≤ Nat.card (fixedField σ)
    ·
      have hsimpK : IsSimpleGroup (StatedProj (StatedSp 2 (fixedField σ))) :=
        CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp _ 2 (by norm_num)
          (Or.inl (Or.inr h4))
      have hsimp : IsSimpleGroup C := hCe.isSimpleGroup
      have hC3 : 3 ∣ Nat.card C := by
        obtain ⟨m, -, hm⟩ := exists_card_eq_two_pow (ringChar.eq (fixedField σ) 2)
        have h3q : 3 ∣ Nat.card (fixedField σ) ^ (2 * 1) - 1 := by
          have h4m : Nat.card (fixedField σ) ^ (2 * 1) = 4 ^ m := by
            rw [hm, mul_one, ← pow_mul, mul_comm, pow_mul]
            norm_num
          rw [h4m]
          have hmod : 4 ^ m % 3 = 1 := by
            rw [Nat.pow_mod]
            norm_num
          omega
        rw [Nat.card_congr hCe.toEquiv,
          CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo 2]
        exact Dvd.dvd.mul_left (h3q.trans (Finset.dvd_prod_of_mem
          (fun j => Nat.card (fixedField σ) ^ (2 * j) - 1) (by simp))) _
      rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hsimp hsn with h | h
      · rw [Subgroup.subgroupOf_eq_bot] at h
        rw [eq_bot_iff]
        intro y hy
        exact Subgroup.mem_bot.mpr (Subgroup.disjoint_def.mp h hy (hYC hy))
      · rw [Subgroup.subgroupOf_eq_top] at h
        exfalso
        apply hY3
        have hYC' : Y = C := le_antisymm hYC h
        rw [hYC']
        exact hC3
    ·
      have h2 : Nat.card (fixedField σ) = 2 := by
        have : Fintype (fixedField σ) := Fintype.ofFinite _
        have hdvd : 2 ∣ Nat.card (fixedField σ) := by
          rw [Nat.card_eq_fintype_card]
          exact (CharP.cast_eq_zero_iff (fixedField σ) 2 _).mp (FiniteField.cast_card_eq_zero _)
        have hpos : 0 < Nat.card (fixedField σ) := Nat.card_pos
        omega
      have hC720 : Nat.card C = 720 := by
        rw [Nat.card_congr eC.toEquiv, card_statedSp_two_of_card_two h2]
      have hdY : Nat.card Y ∣ 720 := by
        rw [← hC720]
        exact Subgroup.card_dvd_of_le hYC
      have hcop : Nat.Coprime (Nat.card Y) (3 ^ 2) :=
        Nat.Coprime.pow_right 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hY3).symm
      have h80 : Nat.card Y ∣ 2 ^ 4 * 5 ^ 1 := by
        refine hcop.dvd_of_dvd_mul_right ?_
        norm_num
        exact hdY
      have hpf : (Nat.card Y).primeFactors.card ≤ 2 :=
        primeFactors_card_le_two_of_dvd Nat.prime_two (by norm_num) h80
      haveI := subsingleton_of_isPerfect_of_card_primeFactors hpf
      exact Subgroup.eq_bot_of_subsingleton _

theorem sp4R148_outer_solvable {S K : Type} [Group S] [Field K] [Finite K]
    (e : S ≃* StatedProj (StatedSp 2 K)) : Group.IsSolvable (Outer S) := by
  haveI : Group.IsSolvable (Outer (StatedProj (StatedSp 2 K))) :=
    (CFSG.ComponentClassification.CatalogueBSymplecticTwo.symplectic_two_schreier K).2
  exact CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv e.symm

theorem rowOf143_psp4_prime (p : ℕ) [Fact p.Prime] (hp : 3 < p) :
    RowOf143 (projSp 2 (GaloisField p 1)) := by
  unfold RowOf143
  intro S _ _ hS hnc hφ h3
  obtain ⟨φ⟩ := hφ
  have hF : Nat.card (GaloisField p 1) = p := by
    rw [GaloisField.card p 1 one_ne_zero, pow_one]
  set e : S ≃* StatedProj (StatedSp 2 (GaloisField p 1)) :=
    φ.trans (Sec4.projSpEquivStatedProj 2 (GaloisField p 1)) with he
  have hOutS : Group.IsSolvable (Outer S) := sp4R148_outer_solvable e
  have h3P : 3 ∣ Nat.card (StatedProj (StatedSp 2 (GaloisField p 1))) := by
    rw [← Nat.card_congr e.toEquiv]
    exact h3
  refine row143_of_inner_kgroup hS hnc
    (fun P _ hPp _ => le_inner_of_perfect_outSolvable hOutS P hPp) ?_
  intro β hβ Y hYfix hYsub _ hYperf hY3
  exact sp4R148_bot_of_mulEquiv e (sp4R148Odd_bot hp hF h3P) β hβ (Sec4.autFix β) Y
    (fun z => Sec4.mem_autFix) hYfix hYsub hYperf hY3

theorem rowOf143_sp4_two (n : ℕ) (hn : 1 ≤ n) :
    RowOf143 (projSp 2 (GaloisField 2 n)) := by
  clear hn
  unfold RowOf143
  intro S _ _ hS hnc hφ h3
  obtain ⟨φ⟩ := hφ
  set e : S ≃* StatedProj (StatedSp 2 (GaloisField 2 n)) :=
    φ.trans (Sec4.projSpEquivStatedProj 2 (GaloisField 2 n)) with he
  have hOutS : Group.IsSolvable (Outer S) := sp4R148_outer_solvable e
  have h3P : 3 ∣ Nat.card (StatedProj (StatedSp 2 (GaloisField 2 n))) := by
    rw [← Nat.card_congr e.toEquiv]
    exact h3
  have hsimpP : IsSimpleGroup (StatedProj (StatedSp 2 (GaloisField 2 n))) := e.symm.isSimpleGroup
  refine row143_of_inner_kgroup hS hnc
    (fun P _ hPp _ => le_inner_of_perfect_outSolvable hOutS P hPp) ?_
  intro β hβ Y hYfix hYsub _ hYperf hY3
  exact sp4R148_bot_of_mulEquiv e (sp4R148Two_bot hsimpP h3P) β hβ (Sec4.autFix β) Y
    (fun z => Sec4.mem_autFix) hYfix hYsub hYperf hY3

end CFSG.RankThree.PartTwo.Sec14.Ronan148K
