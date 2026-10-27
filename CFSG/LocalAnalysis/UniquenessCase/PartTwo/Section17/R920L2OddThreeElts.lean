module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.R920L2Y2Normal
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XThreeEltsCore
import CFSG.GroupTheory.ThreeTranspositions.QuotientLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open CFSG.GroupTheory.ThreeTranspositions (HasE9)

variable {G : Type} [Group G] [Finite G]

private theorem normal_map_pCore_subtype {Z : Type} [Group Z] {X : Subgroup Z} [X.Normal] :
    ((CFSG.pCore 2 ↥X).map X.subtype).Normal :=
  ConjAct.normal_of_characteristic_of_normal (H := X) (K := CFSG.pCore 2 ↥X)

private theorem isL2_map_quotient_pCore {Z : Type} [Group Z] {X : Subgroup Z} {m : ℕ}
    (Ō : Subgroup Z) [Ō.Normal] (hŌ : Ō = (CFSG.pCore 2 ↥X).map X.subtype)
    (hL2 : IsL2 (Bar2 X) m) : IsL2 ↥(X.map (QuotientGroup.mk' Ō)) m := by
  classical
  let O : Subgroup ↥X := CFSG.pCore 2 ↥X
  let mk : Z →* Z ⧸ Ō := QuotientGroup.mk' Ō
  let X' : Subgroup (Z ⧸ Ō) := X.map mk
  let φ : ↥X →* Z ⧸ Ō := mk.comp X.subtype
  let f : ↥X →* ↥X' := φ.codRestrict X' (fun x => Subgroup.mem_map_of_mem mk x.2)
  have hfsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hfker : f.ker = O := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : φ x = 1 := congrArg Subtype.val hx
      have h2 : (x : Z) ∈ Ō := (QuotientGroup.eq_one_iff (N := Ō) (x : Z)).mp h1
      rw [hŌ] at h2
      obtain ⟨o, ho, hox⟩ := Subgroup.mem_map.mp h2
      exact Subtype.ext hox ▸ ho
    · intro hx
      apply Subtype.ext
      change (QuotientGroup.mk' Ō) (x : Z) = (1 : Z ⧸ Ō)
      exact (QuotientGroup.eq_one_iff (N := Ō) (x : Z)).mpr (by
        rw [hŌ]
        exact Subgroup.mem_map_of_mem X.subtype hx)
  have hX'L2 : IsL2 ↥X' m :=
    CFSG.Blueprint.LieModel.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hfker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective f hfsurj)) hL2
  exact hX'L2

private theorem normal_map_mk'_pCore {Z : Type} [Group Z] {X : Subgroup Z} (Ō : Subgroup Z)
    [Ō.Normal] (hXn : X.Normal) : (X.map (QuotientGroup.mk' Ō)).Normal :=
  hXn.map (QuotientGroup.mk' Ō) (QuotientGroup.mk'_surjective Ō)

private theorem not_hasE9_quotient_map_pCore {Z : Type} [Group Z] [Finite Z] {X : Subgroup Z}
    (Ō : Subgroup Z) [Ō.Normal] (hŌ : Ō = (CFSG.pCore 2 ↥X).map X.subtype)
    (hZ : ¬ HasE9 Z) : ¬ HasE9 (Z ⧸ Ō) := by
  have hŌ2 : IsPGroup 2 Ō := by
    rw [hŌ]
    exact (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).map X.subtype
  have hŌnot3 : ¬ 3 ∣ Nat.card Ō := by
    obtain ⟨k, hk⟩ := hŌ2.exists_card_dvd_pow
    intro h3
    exact absurd (Nat.prime_three.dvd_of_dvd_pow (h3.trans hk)) (by norm_num)
  exact fun h => hZ (CFSG.GroupTheory.ThreeTranspositions.hasE9_of_hasE9_quotient Ō hŌnot3 h)

private theorem map_mem_map_of_isPGroup_three {Z : Type} [Group Z] [Finite Z] {X : Subgroup Z}
    {m : ℕ} (Ō : Subgroup Z) [Ō.Normal] (hX'n : (X.map (QuotientGroup.mk' Ō)).Normal)
    (hX'L2 : IsL2 ↥(X.map (QuotientGroup.mk' Ō)) m) (hE9 : ¬ HasE9 (Z ⧸ Ō)) {z : Z}
    (hz : IsPGroup 3 (Subgroup.zpowers z)) :
    QuotientGroup.mk' Ō z ∈ X.map (QuotientGroup.mk' Ō) := by
  have hz' : IsPGroup 3 (Subgroup.zpowers (QuotientGroup.mk' Ō z)) := by
    rw [← MonoidHom.map_zpowers (f := QuotientGroup.mk' Ō) (x := z)]
    exact hz.map _
  exact mem_of_isPGroup_three_of_isL2_normal hX'n hX'L2 hE9 hz'

private theorem mem_of_map_mk'_of_mem {Z : Type} [Group Z] (X Ō : Subgroup Z) [Ō.Normal]
    (hŌle : Ō ≤ X) {z : Z}
    (hz : QuotientGroup.mk' Ō z ∈ X.map (QuotientGroup.mk' Ō)) : z ∈ X := by
  obtain ⟨x, hxX, hxeq⟩ := Subgroup.mem_map.mp hz
  have hmemO : x⁻¹ * z ∈ Ō := by
    apply (QuotientGroup.eq_one_iff (N := Ō) (x⁻¹ * z)).mp
    show QuotientGroup.mk' Ō (x⁻¹ * z) = 1
    rw [map_mul, map_inv, hxeq, inv_mul_cancel]
  have hz_eq : x * (x⁻¹ * z) = z := by group
  rw [← hz_eq]
  exact X.mul_mem hxX (hŌle hmemO)

theorem kFactL2ThreeElts_holds :
    ∀ (Z : Type) [Group Z] [Finite Z] (X : Subgroup Z) (m : ℕ), X.Normal → ⁅X, X⁆ = X →
      IsL2 (Bar2 X) m → CFSG.Open.pRank 3 (⊤ : Subgroup Z) ≤ 1 →
      ∀ z : Z, IsPGroup 3 (Subgroup.zpowers z) → z ∈ X := by
  classical
  intro Z _ _ X m hXn _ hL2 hrank z hz
  haveI : X.Normal := hXn
  have hE9Z : ¬ HasE9 Z := fun h => absurd h.two_le_pRank (by omega)
  let O : Subgroup ↥X := CFSG.pCore 2 ↥X
  let Ō : Subgroup Z := O.map X.subtype
  haveI hŌn : Ō.Normal := normal_map_pCore_subtype
  have hŌ : Ō = (CFSG.pCore 2 ↥X).map X.subtype := rfl
  have hX'L2 : IsL2 ↥(X.map (QuotientGroup.mk' Ō)) m := isL2_map_quotient_pCore Ō hŌ hL2
  have hX'n : (X.map (QuotientGroup.mk' Ō)).Normal := normal_map_mk'_pCore Ō hXn
  have hE9Z' : ¬ HasE9 (Z ⧸ Ō) := not_hasE9_quotient_map_pCore Ō hŌ hE9Z
  have hmem : QuotientGroup.mk' Ō z ∈ X.map (QuotientGroup.mk' Ō) :=
    map_mem_map_of_isPGroup_three Ō hX'n hX'L2 hE9Z' hz
  exact mem_of_map_mk'_of_mem X Ō (Subgroup.map_subtype_le O) hmem

private theorem opp_eq_of_le_normalizer' {X Y : Subgroup G} {n : ℕ}
    (hperf : ⁅X, X⁆ = X) (hL2 : IsL2 (Bar2 X) n) (hXY : X ≤ Y)
    (hYnorm : Y ≤ normalizer (X : Set G)) (h3 : CFSG.Open.pRank 3 (Opp 3 Y) ≤ 1) :
    Opp 3 Y = X ∧ pCoreOf 2 X ≤ pCoreOf 2 Y := by
  have hB0 := kFactL2ThreeElts_holds
  let X₁ : Subgroup G := Opp 3 Y
  have hX₁Y : X₁ ≤ Y := F09.opp_le_self 3 Y
  have hXopp : Opp 3 X = X := opp3_eq_self_of_isL2 hperf hL2
  have hOppXle : Opp 3 X ≤ Opp 3 Y :=
    Subgroup.closure_mono fun x hx => ⟨hXY hx.1, hx.2⟩
  have hXX₁ : X ≤ X₁ := hXopp.symm.le.trans hOppXle
  have hprankX₁ : CFSG.Open.pRank 3 X₁ ≤ 1 := h3
  let X' : Subgroup ↥X₁ := X.subgroupOf X₁
  have hX'norm : X'.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXX₁).mpr (hX₁Y.trans hYnorm)
  have hperf' : ⁅X', X'⁆ = X' := by
    refine (Subgroup.map_subtype_inj (H := X₁)).mp ?_
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hXX₁, hperf]
  have hL2' : IsL2 (Bar2 X') n := by
    have hker : IsPGroup 2 (Subgroup.subgroupOfEquivOfLe hXX₁).symm.toMonoidHom.ker := by
      have hb : (Subgroup.subgroupOfEquivOfLe hXX₁).symm.toMonoidHom.ker = ⊥ :=
        MonoidHom.ker_eq_bot _ (Subgroup.subgroupOfEquivOfLe hXX₁).symm.injective
      rw [hb]
      exact IsPGroup.of_bot
    obtain ⟨eBar⟩ := CFSG.nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker
      (p := 2) (Subgroup.subgroupOfEquivOfLe hXX₁).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hXX₁).symm.surjective hker
    exact CFSG.Blueprint.LieModel.of_mulEquiv eBar hL2
  have hprankTop : CFSG.Open.pRank 3 (⊤ : Subgroup ↥X₁) ≤ 1 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup X₁]
    exact hprankX₁
  have hthree : ∀ z : ↥X₁, IsPGroup 3 (Subgroup.zpowers z) → z ∈ X' :=
    hB0 ↥X₁ X' n hX'norm hperf' hL2' hprankTop
  have hX₁X : X₁ ≤ X := by
    intro y hy
    change y ∈ Subgroup.closure {x : G | x ∈ Y ∧ ∃ k : ℕ, orderOf x = 3 ^ k} at hy
    have hsub : {x : G | x ∈ Y ∧ ∃ k : ℕ, orderOf x = 3 ^ k} ⊆ X := by
      rintro x ⟨hxY, k, hk⟩
      have hxX₁ : x ∈ X₁ := Subgroup.subset_closure ⟨hxY, k, hk⟩
      have hz3 : IsPGroup 3 (Subgroup.zpowers (⟨x, hxX₁⟩ : ↥X₁)) :=
        IsPGroup.of_card (n := k)
          (by rw [Nat.card_zpowers, ← Subgroup.orderOf_coe, hk])
      exact Subgroup.mem_subgroupOf.mp (hthree ⟨x, hxX₁⟩ hz3)
    exact (Subgroup.closure_le X).mpr hsub hy
  have hOppEq : Opp 3 Y = X := le_antisymm hX₁X hXX₁
  have hXYp : pCoreOf 2 X ≤ pCoreOf 2 Y :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans hXY)
      (hYnorm.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
  exact ⟨hOppEq, hXYp⟩

theorem normal_opp_eq_of_mem_calY2_of_calC' (D : Data G)
    {L Y : Subgroup G} {n : ℕ} (hL : L ∈ calC D.M) (hL2 : IsL2 (Bar2 L) n)
    (hY : Y ∈ F09.calY2_9 D) (hLY : L ≤ Y) :
    (L.subgroupOf Y).Normal ∧ Opp 3 Y = L ∧ pCoreOf 2 Y ≠ ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨N, hNmem, hNM⟩ : ∃ N ∈ calMOf Y, N ≠ D.M := by
    by_contra h
    apply hY.2.1
    ext N
    simp only [Set.mem_singleton_iff]
    constructor
    · intro hN
      by_contra hNne
      exact h ⟨N, hN, hNne⟩
    · intro hND
      rw [hND]
      exact ⟨D.maxLocal, hY.1.1⟩
  have hNH9 : N ∈ F09.calH9 D Y := by
    rcases hY.2.2.1 hNmem with h | h
    · exact h
    · exact absurd (Set.mem_singleton_iff.mp h) hNM
  have hYN : Y ≤ N := hNH9.1
  have hprankL9 : CFSG.Open.pRank 3 (F09.L9 Y N) ≤ 1 := hNH9.2.2.le
  have hOppLle : Opp 3 L ≤ Opp 3 Y :=
    Subgroup.closure_mono fun x hx => ⟨hLY hx.1, hx.2⟩
  have hL9le : F09.L9 L (N ⊓ D.M) ≤ F09.L9 Y N := by
    change (⨆ w : ↥(N ⊓ D.M), (Opp 3 L).map (MulAut.conj (w : G)).toMonoidHom) ≤ F09.L9 Y N
    refine iSup_le fun w => ?_
    have hwN : (w : G) ∈ N := (Subgroup.mem_inf.mp w.2).1
    exact (Subgroup.map_mono (f := (MulAut.conj (w : G)).toMonoidHom) hOppLle).trans
      (le_iSup (fun n : ↥N => (Opp 3 Y).map (MulAut.conj (n : G)).toMonoidHom)
        ⟨(w : G), hwN⟩)
  have hprankL9L : CFSG.Open.pRank 3 (F09.L9 L (N ⊓ D.M)) ≤ 1 :=
    (CFSG.SectionRank.pRank_mono (by norm_num) hL9le).trans hprankL9
  have hNMnorm : N ⊓ D.M ≤ normalizer (L : Set G) :=
    le_normalizer_of_pRank_L9_le_one hL hL2 inf_le_right hprankL9L
  have hYnorm : Y ≤ normalizer (L : Set G) :=
    (le_inf hYN hY.1.1).trans hNMnorm
  have hLnormY : (L.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).mpr hYnorm
  have h3Y : CFSG.Open.pRank 3 (Opp 3 Y) ≤ 1 :=
    (CFSG.SectionRank.pRank_mono (by norm_num) (F09.opp_le_L9 Y N)).trans hprankL9
  obtain ⟨hOppEq, hpc⟩ := opp_eq_of_le_normalizer' hL.2.1 hL2 hLY hYnorm h3Y
  have hLbot : pCoreOf 2 L ≠ ⊥ :=
    pCoreOf_ne_bot_of_mem_calC D.standing.charTwo D.maxLocal.1 hL
  exact ⟨hLnormY, hOppEq, fun hbot => hLbot (bot_unique (hbot ▸ hpc))⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
