module

public import CFSG.RankThree.GF2n.Tim81.Sec6.RootSetupBasic
public import CFSG.RankThree.GF2n.Tim81.Cited.Sec7
public import CFSG.Timmesfeld.Transvection.Subgroup
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapLiftBasic
import CFSG.GroupTheory.CentralQuotientLift
import CFSG.GroupTheory.OddCentralQuotient
import CFSG.Timmesfeld.Bridge.OddTranspPairL2
import CFSG.ClassicalGroups.UnitaryFlag.StatedBridge
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapLift
import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OddSplitClassical
public import CFSG.Timmesfeld.Transvection.QTwoSU

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Timmesfeld CFSG.Timmesfeld.ARS
  CFSG.Timmesfeld.Transvection CFSG.GroupTheory CFSG.SeitzReduction.UnitaryPilot
  CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.Transvection.QTwo

variable {K : Type} [Group K] [Finite K] {X : Subgroup K} {Δ : Set (Subgroup K)} {f : ℕ}

private theorem mem_restrict_top {H : Type*} [Group H] {Δ : Set (Subgroup H)}
    {A' : Subgroup ↥(⊤ : Subgroup H)} :
    A' ∈ Timmesfeld.ARS.restrict Δ ⊤ ↔ ∃ A ∈ Δ, A.subgroupOf ⊤ = A' := by
  simp [Timmesfeld.ARS.restrict]

private theorem commuting_subgroupOf_top {H : Type*} [Group H] {A B : Subgroup H} :
    Commuting (A.subgroupOf ⊤) (B.subgroupOf ⊤) ↔ Commuting A B := by
  rw [Timmesfeld.ARS.Restrict.commuting_subgroupOf_iff]
  simp

private theorem exists_special_of_special_restrict_top {H : Type*} [Group H]
    {Δ : Set (Subgroup H)} {A B : Subgroup H}
    (hsp : Special (Timmesfeld.ARS.restrict Δ ⊤) (A.subgroupOf ⊤) (B.subgroupOf ⊤)) :
    Special Δ A B := by
  obtain ⟨hmem, hcA, hcB⟩ := hsp
  obtain ⟨C, hC, hCeq⟩ := mem_restrict_top.mp hmem
  have hCAB : C = ⁅A, B⁆ := by
    refine (Timmesfeld.ARS.subgroupOf_inj_of_le le_top le_top).mp ?_
    calc C.subgroupOf ⊤ = ⁅A.subgroupOf ⊤, B.subgroupOf ⊤⁆ := hCeq
      _ = ⁅A, B⁆.subgroupOf ⊤ :=
        Timmesfeld.ARS.Restrict.commutator_subgroupOf le_top le_top
  refine ⟨?_, ?_, ?_⟩
  · rw [← hCAB]
    exact hC
  · rw [Timmesfeld.ARS.Restrict.commutator_subgroupOf le_top le_top,
      commuting_subgroupOf_top] at hcA
    exact hcA
  · rw [Timmesfeld.ARS.Restrict.commutator_subgroupOf le_top le_top,
      commuting_subgroupOf_top] at hcB
    exact hcB

private theorem isTransvectionClass_restrict_top {H : Type*} [Group H]
    {Δ : Set (Subgroup H)} (h : IsTransvectionClass Δ) :
    IsTransvectionClass (Timmesfeld.ARS.restrict Δ ⊤) := by
  obtain ⟨E₀, hE₀⟩ := h.root.conj_class
  have hE₀mem : E₀ ∈ Δ := by
    rw [hE₀]
    simpa using Set.mem_range_self (f := fun g : H => conjSub E₀ g) (1 : H)
  have hroot : IsRootClass (Timmesfeld.ARS.restrict Δ ⊤) := by
    refine Timmesfeld.ARS.isRootClass_restrict h.root hE₀mem le_top ?_ ?_
    · intro B hB _
      rw [hE₀] at hB
      obtain ⟨g, rfl⟩ := hB
      exact ⟨g, Subgroup.mem_top g, rfl⟩
    · calc ⊤ = ⨆ A ∈ Δ, A := h.root.gen.symm
        _ ≤ ⨆ B ∈ {B | B ∈ Δ ∧ B ≤ ⊤}, B := by
          refine iSup₂_le fun B hB => ?_
          exact le_iSup₂ (f := fun (X : Subgroup H)
            (_ : X ∈ {B | B ∈ Δ ∧ B ≤ ⊤}) => X) B ⟨hB, le_top⟩
  refine ⟨hroot, ?_⟩
  rintro A' hA' B' hB' hsp
  obtain ⟨A, hA, rfl⟩ := mem_restrict_top.mp hA'
  obtain ⟨B, hB, rfl⟩ := mem_restrict_top.mp hB'
  exact h.noSpecial A hA B hB (exists_special_of_special_restrict_top hsp)

private theorem pointsDetermined_restrict_top {H : Type*} [Group H] {Δ : Set (Subgroup H)}
    (h : PointsDetermined Δ) : PointsDetermined (Timmesfeld.ARS.restrict Δ ⊤) := by
  intro A' hA' B' hB' hsame
  obtain ⟨A, hA, rfl⟩ := mem_restrict_top.mp hA'
  obtain ⟨B, hB, rfl⟩ := mem_restrict_top.mp hB'
  have hAB : A = B := h A hA B hB fun C hC => by
    have hC' : C.subgroupOf ⊤ ∈ Timmesfeld.ARS.restrict Δ ⊤ :=
      mem_restrict_top.mpr ⟨C, hC, rfl⟩
    have := hsame (C.subgroupOf ⊤) hC'
    rwa [commuting_subgroupOf_top, commuting_subgroupOf_top] at this
  rw [hAB]

theorem transvectionHyp_restrict_top {H : Type*} [Group H] {Δ : Set (Subgroup H)}
    (h : TransvectionHyp H Δ) (h4 : ∀ A ∈ Δ, 4 ≤ Nat.card A) :
    TransvectionHyp ↥(⊤ : Subgroup H) (restrict Δ ⊤) := by
  haveI : Finite H := h.finite
  refine ⟨inferInstance, isTransvectionClass_restrict_top h.cls,
    pointsDetermined_restrict_top h.points, ?_, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro x hx
    have hxH : (x : H) ∈ Subgroup.center H := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact congrArg Subtype.val
        (Subgroup.mem_center_iff.mp hx (⟨y, Subgroup.mem_top y⟩ : ↥(⊤ : Subgroup H)))
    rw [h.center, Subgroup.mem_bot] at hxH
    exact Subtype.ext (by simpa using hxH)
  · obtain ⟨A, hA, B, hB, hAB, hcomm⟩ := h.rank
    refine ⟨A.subgroupOf ⊤, mem_restrict_top.mpr ⟨A, hA, rfl⟩,
      B.subgroupOf ⊤, mem_restrict_top.mpr ⟨B, hB, rfl⟩, ?_, ?_⟩
    · intro he
      exact hAB ((Timmesfeld.ARS.subgroupOf_inj_of_le le_top le_top).mp he)
    · rw [commuting_subgroupOf_top]
      exact hcomm
  · rintro ⟨A', hA', hA'2⟩
    obtain ⟨A, hA, rfl⟩ := mem_restrict_top.mp hA'
    have hcard : Nat.card (A.subgroupOf ⊤) = Nat.card A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_top).toEquiv
    have h4A := h4 A hA
    omega

theorem RootSetup.transvectionHyp (h : RootSetup X Δ f) (hPts : Tim90Points)
    (hrank : ∃ A ∈ Δ, ∃ B ∈ Δ, A ≠ B ∧ ⁅A, B⁆ = ⊥) :
    TransvectionHyp (quotY X) (quotDelta X Δ) := by
  haveI : Finite (quotY X) := inferInstance
  refine ⟨inferInstance, h.isTransvectionClass_quot, ?_, h.center_quot, ?_, ?_⟩
  · refine hPts (quotY X) (quotDelta X Δ) h.isTransvectionClass_quot ?_ ?_
    · intro A' hA' B' hB'
      by_cases hAB : A' = B'
      · subst hAB
        exact Or.inl (h.isTransvectionClass_quot.root.commuting_self hA')
      · rcases h.quot_pair A' hA' B' hB' hAB with hc | hl
        · exact Or.inl (Timmesfeld.ARS.commuting_iff_commutator_eq_bot.mpr hc)
        · exact Or.inr hl
    · exact h.no_nilpotent_quot
  · obtain ⟨A, hA, B, hB, hAB, hcomm⟩ := hrank
    refine ⟨quotSub X A, ⟨A, hA, rfl⟩, quotSub X B, ⟨B, hB, rfl⟩, ?_, ?_⟩
    · intro he
      exact hAB (h.quotSub_inj hA hB he)
    · exact Timmesfeld.ARS.commuting_iff_commutator_eq_bot.mpr
        ((h.commutator_quotSub_eq_bot_iff hA hB).mpr hcomm)
  · rintro ⟨A', ⟨A, hA, rfl⟩, hA'2⟩
    have hcard := h.card_quotSub hA
    have h4 : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := pow_le_pow_right' (by norm_num) h.two_le
    omega

private theorem su_oddCentralSplit
    {f m : ℕ} (hf : 2 ≤ f) (hm : 4 ≤ m) :
    OddCentralSplit
      ↥(Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) m) := by
  have hF : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 :=
    card_galoisField_two_mul (le_trans (by norm_num : 1 ≤ 2) hf)
  have hdat : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f
      (GaloisField 2 (2 * f)) :=
    CFSG.ClassicalGroups.UnitaryFlag.unitaryFieldDataOfCard hF
  have hsplit : OddCentralSplit (StatedSU m (2 ^ f) (GaloisField 2 (2 * f))) :=
    CFSG.SeitzReduction.UnitaryPilot.oddCentralSplit_unitarySU (f := f)
      (K := GaloisField 2 (2 * f)) hdat (le_trans (by norm_num : 2 ≤ 4) hm) (by
        intro h3
        exact absurd (Prod.mk.inj h3).1
          (Nat.ne_of_gt (lt_of_lt_of_le (by norm_num : 3 < 4) hm)))
  exact hsplit.of_mulEquiv (CFSG.LieType.Universal.Unitary.equivStatedSU
    (p := 2) (f := f) hF m).symm

private theorem range_sup_center_eq_top {X : Subgroup K} {S : Type} [Group S]
    {Φ : S →* quotY X} (hΦ : Function.Surjective Φ) {Ψ₀ : S →* ↥X}
    (hΨ₀ : (quotMap X).comp Ψ₀ = Φ) :
    Ψ₀.range ⊔ Subgroup.center ↥X = ⊤ := by
  have h1 : (Ψ₀.range).map (quotMap X) = ⊤ := by
    rw [← MonoidHom.range_comp, hΨ₀, MonoidHom.range_eq_top.mpr hΦ]
  have h2 := Subgroup.comap_map_eq (f := quotMap X) (H := Ψ₀.range)
  rw [h1, Subgroup.comap_top, QuotientGroup.ker_mk'] at h2
  exact h2.symm

private theorem RootSetup.exists_eq_map_of_mem {h : RootSetup X Δ f} {S : Type} [Group S]
    {Φ : S →* quotY X} {Γ : Set (Subgroup S)}
    (hΓ : ∀ A' : Subgroup (quotY X), A' ∈ quotDelta X Δ ↔ ∃ U ∈ Γ, A' = U.map Φ)
    (hΓ2 : (∀ U ∈ Γ, IsPGroup 2 U) ∨ Function.Injective Φ)
    {Ψ₀ : S →* ↥X} (hΨ₀ : (quotMap X).comp Ψ₀ = Φ) {A : Subgroup K} (hA : A ∈ Δ) :
    ∃ U ∈ Γ, A = U.map (X.subtype.comp Ψ₀) := by
  obtain ⟨U, hU, hUeq⟩ := (hΓ (quotSub X A)).mp ⟨A, hA, rfl⟩
  refine ⟨U, hU, ?_⟩
  have h2 : (U.map Ψ₀).map (quotMap X) = (A.subgroupOf X).map (quotMap X) := by
    rw [Subgroup.map_map U (quotMap X) Ψ₀, hΨ₀]
    exact hUeq.symm
  have hU2 : IsPGroup 2 (U.map Ψ₀) := by
    rcases hΓ2 with h2' | hinj
    · exact (h2' U hU).map Ψ₀
    · have hUΦ : Nat.card (U.map Φ) = 2 ^ f := by
        rw [← hUeq]
        exact h.card_quotSub hA
      have hcard : Nat.card U = 2 ^ f := by
        rw [← Subgroup.card_map_of_injective (K := U) (f := Φ) hinj]
        exact hUΦ
      exact (IsPGroup.of_card hcard).map Ψ₀
  have hA2 : IsPGroup 2 (A.subgroupOf X) := (h.isPGroup hA).comap_subtype
  have hEq : U.map Ψ₀ = A.subgroupOf X :=
    eq_of_map_mk_eq_of_le_center le_rfl h.odd_card_center hU2 hA2 h2
  have hmap : U.map (X.subtype.comp Ψ₀) = (U.map Ψ₀).map X.subtype :=
    (Subgroup.map_map U X.subtype Ψ₀).symm
  rw [hmap, hEq, Subgroup.map_subgroupOf_eq_of_le (h.le A hA)]

private theorem RootSetup.mem_of_exists_eq_map {h : RootSetup X Δ f} {S : Type} [Group S]
    {Φ : S →* quotY X} {Γ : Set (Subgroup S)}
    (hΓ : ∀ A' : Subgroup (quotY X), A' ∈ quotDelta X Δ ↔ ∃ U ∈ Γ, A' = U.map Φ)
    (hΓ2 : (∀ U ∈ Γ, IsPGroup 2 U) ∨ Function.Injective Φ)
    {Ψ₀ : S →* ↥X} (hΨ₀ : (quotMap X).comp Ψ₀ = Φ) {A : Subgroup K}
    (hA : ∃ U ∈ Γ, A = U.map (X.subtype.comp Ψ₀)) : A ∈ Δ := by
  obtain ⟨U, hU, rfl⟩ := hA
  have hmap : U.map (X.subtype.comp Ψ₀) = (U.map Ψ₀).map X.subtype :=
    (Subgroup.map_map U X.subtype Ψ₀).symm
  have hle : U.map (X.subtype.comp Ψ₀) ≤ X := by
    rw [hmap]
    exact Subgroup.map_subtype_le _
  have hsub : (U.map (X.subtype.comp Ψ₀)).subgroupOf X = U.map Ψ₀ := by
    refine Subgroup.map_injective (f := X.subtype) X.subtype_injective ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hle, hmap]
  have hquot : quotSub X (U.map (X.subtype.comp Ψ₀)) = U.map Φ := by
    change ((U.map (X.subtype.comp Ψ₀)).subgroupOf X).map (quotMap X) = U.map Φ
    rw [hsub, Subgroup.map_map U (quotMap X) Ψ₀, hΨ₀]
  have hmem : quotSub X (U.map (X.subtype.comp Ψ₀)) ∈ quotDelta X Δ :=
    (hΓ _).mpr ⟨U, hU, hquot⟩
  obtain ⟨A₀, hA₀, hA₀eq⟩ := hmem
  have hA2 : IsPGroup 2 ((U.map (X.subtype.comp Ψ₀)).subgroupOf X) := by
    rcases hΓ2 with h2' | hinj
    · rw [hmap]
      exact (((h2' U hU).map Ψ₀).map X.subtype).comap_subtype (K := X)
    · have hq : Nat.card (quotSub X (U.map (X.subtype.comp Ψ₀))) = 2 ^ f := by
        rw [← hA₀eq]
        exact h.card_quotSub hA₀
      have hUΦ : Nat.card (U.map Φ) = 2 ^ f := by
        rw [← hquot]
        exact hq
      have hcard : Nat.card U = 2 ^ f := by
        rw [← Subgroup.card_map_of_injective (K := U) (f := Φ) hinj]
        exact hUΦ
      rw [hmap]
      exact (((IsPGroup.of_card hcard).map Ψ₀).map X.subtype).comap_subtype (K := X)
  have hA₀2 : IsPGroup 2 (A₀.subgroupOf X) := (h.isPGroup hA₀).comap_subtype
  have hEq : (U.map (X.subtype.comp Ψ₀)).subgroupOf X = A₀.subgroupOf X :=
    eq_of_map_mk_eq_of_le_center le_rfl h.odd_card_center hA2 hA₀2 (by
      change quotSub X (U.map (X.subtype.comp Ψ₀)) = quotSub X A₀
      rw [hquot, hA₀eq]
      exact hquot.symm)
  have hfinal : U.map (X.subtype.comp Ψ₀) = A₀ := by
    have hh := congrArg (Subgroup.map X.subtype) hEq
    rw [Subgroup.map_subgroupOf_eq_of_le hle,
      Subgroup.map_subgroupOf_eq_of_le (h.le A₀ hA₀)] at hh
    exact hh
  rw [hfinal]
  exact hA₀

theorem RootSetup.lift (h : RootSetup X Δ f) {S : Type} [Group S] [Finite S]
    (hS : OddCentralSplit S) {Φ : S →* quotY X}
    (hΦ : Function.Surjective Φ) {Γ : Set (Subgroup S)}
    (hΓ : ∀ A' : Subgroup (quotY X), A' ∈ quotDelta X Δ ↔ ∃ U ∈ Γ, A' = U.map Φ)
    (hΓ2 : (∀ U ∈ Γ, IsPGroup 2 U) ∨ Function.Injective Φ) :
    ∃ Ψ : S →* K, Ψ.ker ≤ Φ.ker ∧ Ψ.range = X ∧
      ∀ A : Subgroup K, A ∈ Δ ↔ ∃ U ∈ Γ, A = U.map Ψ := by
  have hπ : Function.Surjective (quotMap X) := QuotientGroup.mk'_surjective _
  have hker : (quotMap X).ker ≤ Subgroup.center ↥X := by
    rw [QuotientGroup.ker_mk']
  have hodd : Odd (Nat.card (quotMap X).ker) := by
    rw [QuotientGroup.ker_mk']
    exact h.odd_card_center
  obtain ⟨Ψ₀, hΨ₀⟩ := exists_lift_of_oddCentralSplit hS hπ hker hodd Φ
  have hMtop := range_sup_center_eq_top (X := X) hΦ hΨ₀
  have hM : Ψ₀.range = ⊤ :=
    CFSG.Timmesfeld.Bridge.OddTransp.eq_top_of_sup_center_eq_top
      h.isPerfect.commutator_eq_top hMtop
  refine ⟨X.subtype.comp Ψ₀, ?_, ?_, ?_⟩
  · intro s hs
    rw [MonoidHom.mem_ker] at hs ⊢
    have h1 : Ψ₀ s = 1 := X.subtype_injective (by simpa using hs)
    have h2 : Φ s = 1 := by
      rw [← DFunLike.congr_fun hΨ₀ s]
      simp only [MonoidHom.comp_apply, h1, map_one]
    exact h2
  · rw [MonoidHom.range_comp, hM, Subgroup.map_top, Subgroup.range_subtype]
  · intro A
    exact ⟨h.exists_eq_map_of_mem hΓ hΓ2 hΨ₀, h.mem_of_exists_eq_map hΓ hΓ2 hΨ₀⟩

private theorem isSpImage_of_transvectionData
    {h : RootSetup X Δ f} {n : ℕ}
    (hn : 2 ≤ n) {Φ : ↥(StatedSp n (GaloisField 2 f)) →* quotY X}
    (hΦinj : Function.Injective Φ) (hΦrange : Φ.range = ⊤)
    (hΦmem : ∀ A' : Subgroup (quotY X), A' ∈ quotDelta X Δ ↔
      ∃ g, A' = (conjSub ((Symplectic.rootDatum n (GaloisField 2 f)).rootGroup
        (Pi.single (⟨n - 1, Nat.sub_lt (lt_of_lt_of_le (by norm_num : 0 < 2) hn)
          (by norm_num : 0 < 1)⟩ : Fin n) 1)) g).map Φ) :
    IsSpImage X Δ f n (le_trans (by norm_num : 1 ≤ 2) hn) := by
  let T : Subgroup ↥(StatedSp n (GaloisField 2 f)) :=
    (Symplectic.rootDatum n (GaloisField 2 f)).rootGroup
      (Pi.single (⟨n - 1, by omega⟩ : Fin n) 1)
  let Γ : Set (Subgroup ↥(StatedSp n (GaloisField 2 f))) := Set.range fun g => conjSub T g
  have hΦsurj : Function.Surjective Φ := MonoidHom.range_eq_top.mp hΦrange
  have hΓ : ∀ A' : Subgroup (quotY X), A' ∈ quotDelta X Δ ↔ ∃ U ∈ Γ, A' = U.map Φ := by
    intro A'
    rw [hΦmem A']
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨conjSub T g, ⟨g, rfl⟩, rfl⟩
    · rintro ⟨U, ⟨g, rfl⟩, rfl⟩
      exact ⟨g, rfl⟩
  obtain ⟨Ψ, hker, hrange, hmem⟩ := h.lift (S := ↥(StatedSp n (GaloisField 2 f)))
    (CFSG.SeitzReduction.SeitzQ2.oddCentralSplit_statedSp n (GaloisField 2 f)) hΦsurj hΓ
    (Or.inr hΦinj)
  have hΨker : Ψ.ker = ⊥ :=
    le_bot_iff.mp (hker.trans_eq (MonoidHom.ker_eq_bot_iff Φ |>.mpr hΦinj))
  refine ⟨Ψ, MonoidHom.ker_eq_bot_iff Ψ |>.mp hΨker, hrange, ?_⟩
  intro U
  rw [hmem U]
  constructor
  · rintro ⟨U', ⟨g, rfl⟩, hU'⟩
    exact ⟨g, hU'⟩
  · rintro ⟨g, hU'⟩
    exact ⟨conjSub T g, ⟨g, rfl⟩, hU'⟩

private theorem isSUImage_of_transvectionData
    {h : RootSetup X Δ f} (hf : 1 ≤ f)
    {m : ℕ} (hm : 4 ≤ m)
    {Φ : ↥(Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) m) →* quotY X}
    (hΦker : Φ.ker = Subgroup.center
      ↥(Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) m))
    (hΦrange : Φ.range = ⊤)
    (hΦmem : ∀ A' : Subgroup (quotY X), A' ∈ quotDelta X Δ ↔
      ∃ g, A' = (conjSub ((Unitary.rootDatum (card_galoisField_two_mul hf) m).rootGroup
        (unitaryLongRoot m (by omega))) g).map Φ) :
    IsSUImage X Δ f m hf (by omega) := by
  have hF : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 :=
    card_galoisField_two_mul (by omega)
  let T : Subgroup ↥(Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) m) :=
    (Unitary.rootDatum hF m).rootGroup (unitaryLongRoot m (by omega))
  let Γ : Set (Subgroup ↥(Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) m)) :=
    Set.range fun g => conjSub T g
  haveI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  have hT2 : IsPGroup 2 T := by
    have hγ : CFSG.LieType.Universal.Unitary.toStd m (unitaryLongRoot m (by omega)) ≠ 0 := by
      rw [toStd_unitaryLongRoot]
      intro hzero
      have hc := congrFun hzero (coord₀ m (by omega))
      rw [weight_idx₀] at hc
      simp at hc
    exact CFSG.LieType.Steinberg.isPGroup_rootGroup
      (σ := unitaryInvolution (GaloisField 2 (2 * f)) 2 f)
      (hσ := unitaryInvolution_involutive hF) (p := 2)
      (γ := unitaryLongRoot m (by omega)) hγ
  have hΦsurj : Function.Surjective Φ := MonoidHom.range_eq_top.mp hΦrange
  have hΓ : ∀ A' : Subgroup (quotY X), A' ∈ quotDelta X Δ ↔ ∃ U ∈ Γ, A' = U.map Φ := by
    intro A'
    rw [hΦmem A']
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨conjSub T g, ⟨g, rfl⟩, rfl⟩
    · rintro ⟨U, ⟨g, rfl⟩, rfl⟩
      exact ⟨g, rfl⟩
  have hΓ2 : (∀ U ∈ Γ, IsPGroup 2 U) ∨ Function.Injective Φ := by
    left
    rintro U ⟨g, rfl⟩
    exact hT2.map (MulAut.conj g).toMonoidHom
  obtain ⟨Ψ, hker, hrange, hmem⟩ := h.lift (S :=
    ↥(Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) m))
    (su_oddCentralSplit (f := f) (m := m) h.two_le hm) hΦsurj hΓ hΓ2
  refine ⟨Ψ, ?_, hrange, ?_⟩
  · rw [hΦker] at hker
    exact hker
  · intro U
    rw [hmem U]
    constructor
    · rintro ⟨U', ⟨g, rfl⟩, hU'⟩
      exact ⟨g, hU'⟩
    · rintro ⟨g, hU'⟩
      exact ⟨conjSub T g, ⟨g, rfl⟩, hU'⟩

theorem RootSetup.recog
    (h : RootSetup X Δ f)
    (hT : SubgroupTransvectionStatement) (hPts : Tim90Points)
    (hrank : ∃ A ∈ Δ, ∃ B ∈ Δ, A ≠ B ∧ ⁅A, B⁆ = ⊥) :
    (∃ m, ∃ hm : 4 ≤ m, IsSUImage X Δ f m (Nat.one_le_of_lt h.two_le)
        (Nat.le_trans (Nat.le_add_right 2 2) hm)) ∨
      ∃ m, ∃ hm : 2 ≤ m, IsSpImage X Δ f m (Nat.one_le_of_lt hm) := by
  have hf : 1 ≤ f := by have := h.two_le; omega
  have h4 : ∀ A ∈ quotDelta X Δ, 4 ≤ Nat.card A := by
    intro A hA
    obtain ⟨B, hB, rfl⟩ := hA
    rw [h.card_quotSub hB]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := pow_le_pow_right' (by norm_num) h.two_le
  obtain ⟨f', hf', hcard', hconj'⟩ :=
    hT (quotY X) ⊤ (quotDelta X Δ) (fun _ _ => le_top)
      (transvectionHyp_restrict_top (h.transvectionHyp hPts hrank) h4)
  obtain ⟨A, hA⟩ := h.nonempty
  have hf'f : f' = f :=
    Nat.pow_right_injective (a := 2) (by norm_num)
      ((hcard' (quotSub X A) ⟨A, hA, rfl⟩).symm.trans (h.card_quotSub hA))
  subst f'
  rcases hconj' with ⟨n, hn, Φ, hΦinj, hΦrange, hΦmem⟩ |
    ⟨m, hm, Φ, hΦker, hΦrange, hΦmem⟩
  · exact Or.inr ⟨n, hn, isSpImage_of_transvectionData (h := h) (n := n) hn
      hΦinj hΦrange hΦmem⟩
  · exact Or.inl ⟨m, hm, isSUImage_of_transvectionData (h := h) (m := m) hf hm
      hΦker hΦrange hΦmem⟩

end CFSG.RankThree.GF2n.Tim81
