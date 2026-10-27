module

public import CFSG.RankThree.PartTwo.Sec18.Item181
import CFSG.RankThree.PartTwo.Sec18.Item186a
import CFSG.RankThree.PartTwo.Sec4.Item413Setup
import CFSG.RankThree.PartTwo.KFacts.KS18OuterCore
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartTwo.Sec4.T444.Basic
import CFSG.Fischer.Classification.Recognition.PSU6

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item4443SL

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem ctx444_subgroupOf {A M H : Subgroup G} (h : Ctx444 G A M)
    (hH : H ∈ Late.scriptH₀ A M) : Ctx444 H (A.subgroupOf H) ((H ⊓ M).subgroupOf H) where
  sectionFourHyp := sectionFourHyp_subgroup h.sectionFourHyp H
  isE27 := Sec18.isE27_subgroupOf h.isE27 (Sec18.le_of_mem_scriptH₀ hH)
  lt_top := by
    refine lt_top_iff_ne_top.mpr fun heq => Sec18.inf_ne_of_mem_scriptH₀ hH
      (le_antisymm inf_le_left fun x hx => ?_)
    have hmem : (⟨x, hx⟩ : H) ∈ (H ⊓ M).subgroupOf H := heq ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hmem
  pRank_eq := by
    have hAH := Sec18.le_of_mem_scriptH₀ hH
    have hA' := Sec18.isE27_subgroupOf h.isE27 hAH
    apply le_antisymm
    · calc CFSG.Open.pRank 3 ((H ⊓ M).subgroupOf H)
          ≤ CFSG.Open.pRank 3 (((H ⊓ M).subgroupOf H).map H.subtype) :=
            Sec18.pRank_subgroupOf_le 3 Nat.prime_three _
        _ = CFSG.Open.pRank 3 (H ⊓ M) := by rw [Subgroup.map_subgroupOf_eq_of_le inf_le_left]
        _ ≤ CFSG.Open.pRank 3 M :=
            CFSG.RankThreeEvenClassification.Helpers.pRank_mono 3 Nat.prime_three inf_le_right
        _ = 3 := h.pRank_eq
    · have hsub : A.subgroupOf H ≤ (H ⊓ M).subgroupOf H := fun x hx =>
        Subgroup.mem_subgroupOf.mpr ⟨x.2, h.le (Subgroup.mem_subgroupOf.mp hx)⟩
      calc 3 = CFSG.Open.pRank 3 (A.subgroupOf H) := hA'.pRank_eq.symm
        _ ≤ _ := CFSG.RankThreeEvenClassification.Helpers.pRank_mono 3 Nat.prime_three hsub
  gamma_le := by
    intro y hy
    have hmem := Sec18.gamma_subgroupOf_le (X := H) (A := A) (A.subgroupOf H)
      (Subgroup.map_subgroupOf_eq_of_le (Sec18.le_of_mem_scriptH₀ hH))
      (Subgroup.mem_map_of_mem H.subtype hy)
    exact Subgroup.mem_subgroupOf.mpr ⟨y.2, h.gamma_le (Subgroup.mem_inf.mp hmem).1⟩

section Ctx


theorem exists_ctx4443 (h442 : Item4_44_2) {A M : Subgroup G} (h : Ctx444 G A M)
    {H : Subgroup G} (hH : H ∈ Late.scriptH₀ A M) : ∃ s : G, Ctx4443 G A M H s := by
  obtain ⟨s, hs⟩ := h442 H (A.subgroupOf H) ((H ⊓ M).subgroupOf H) (ctx444_subgroupOf h hH)
    (Sec18.top_mem_scriptH₀_subgroupOf hH)
  exact ⟨s, ⟨h, hH, Sec18.concl4442_of_subgroupOf (Sec18.le_of_mem_scriptH₀ hH) hs⟩⟩

end Ctx

theorem forall_mem_pCoreOf_of_commutator_ne {X : Type} [Group X] [Finite X] {I Q : Subgroup X}
    (hIp : Group.IsPerfect I) (hIq : CFSG.IsQuasisimple (I ⧸ CFSG.pCore 2 I))
    (hQI : Q ≤ Subgroup.normalizer (I : Set X)) (hne : ⁅I, Q⁆ ≠ I) :
    ∀ q ∈ Q, ∀ x ∈ I, q * x * q⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := ⁅I, Q⁆ with hD
  have hDI : D ≤ I := Subgroup.le_normalizer_iff_commutator_le_left.mp hQI
  have hID : I ≤ Subgroup.normalizer (D : Set X) := Subgroup.normalizer_commutator_ge_left I Q
  set D' : Subgroup I := D.subgroupOf I with hD'
  have hD'n : D'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hDI).mpr hID
  set φ := QuotientGroup.mk' (CFSG.pCore 2 I) with hφ
  have hD'φ : (D'.map φ).Normal := hD'n.map φ (QuotientGroup.mk'_surjective _)
  rcases LocalCores.quasisimple_normal_subgroups hIq hD'φ with htop | hcen
  ·
    exfalso
    apply hne
    have hsurj : Function.Surjective ((QuotientGroup.mk' D').comp (CFSG.pCore 2 I).subtype) := by
      intro qq
      obtain ⟨i, rfl⟩ := QuotientGroup.mk'_surjective D' qq
      have hi : φ i ∈ D'.map φ := htop ▸ Subgroup.mem_top _
      obtain ⟨d, hd, hdi⟩ := hi
      rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hdi
      refine ⟨⟨d⁻¹ * i, hdi⟩, ?_⟩
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq]
      change (d⁻¹ * i)⁻¹ * i ∈ D'
      rw [show (d⁻¹ * i)⁻¹ * i = i⁻¹ * d * i by group]
      have := hD'n.conj_mem d hd i⁻¹
      simpa [mul_assoc] using this
    have hTs : Group.IsNilpotent (CFSG.pCore 2 I) := CFSG.pCore_isPGroup.isNilpotent
    have hsolv : Group.IsSolvable (I ⧸ D') := Group.isSolvable_of_surjective hsurj
    have hperf : Group.IsPerfect (I ⧸ D') :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective D')
    have hsub : Subsingleton (I ⧸ D') := by
      by_contra hnt
      rw [not_subsingleton_iff_nontrivial] at hnt
      exact Group.IsPerfect.not_isSolvable _ hsolv
    refine le_antisymm hDI fun x hx => ?_
    have h1 : (QuotientGroup.mk' D' ⟨x, hx⟩ : I ⧸ D') = 1 := Subsingleton.elim _ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  ·
    intro q hq x hx
    set c : MulAut I := I.normalizerMonoidHom ⟨q, hQI hq⟩ with hc
    have hcx : ∀ y : I, ((c y : I) : X) = q * y * q⁻¹ := fun y => rfl
    set σ : MulAut (I ⧸ CFSG.pCore 2 I) :=
      QuotientGroup.congr (CFSG.pCore 2 I) (CFSG.pCore 2 I) c (CFSG.pCore_map_iso 2 c) with hσ
    have hσφ : ∀ y : I, σ (φ y) = φ (c y) := fun y => rfl
    have hperf : commutator (I ⧸ CFSG.pCore 2 I) = ⊤ :=
      (Group.IsPerfect.ofSurjective
        (QuotientGroup.mk'_surjective (CFSG.pCore 2 I))).commutator_eq_top
    have hfix := KFacts.KS18.eq_of_mul_inv_mem_center hperf σ (fun l => by
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 I) l
      change σ (φ y) * (φ y)⁻¹ ∈ _
      rw [hσφ, ← map_inv, ← map_mul]
      refine hcen ⟨c y * y⁻¹, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
      have h1 : ((c y * y⁻¹ : I) : X) = (⁅(y : X), q⁆)⁻¹ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hcx, commutatorElement_def]
        group
      rw [h1]
      exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator y.2 hq)) (φ ⟨x, hx⟩)
    rw [hσφ, hφ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hfix
    have h2 : (⟨x, hx⟩ : I) * ((c ⟨x, hx⟩)⁻¹ * ⟨x, hx⟩) * (⟨x, hx⟩ : I)⁻¹ ∈ CFSG.pCore 2 I :=
      (CFSG.pCore_normal (p := 2) (G := I)).conj_mem _ hfix _
    have h3 : (⟨x, hx⟩ : I) * ((c ⟨x, hx⟩)⁻¹ * ⟨x, hx⟩) * (⟨x, hx⟩ : I)⁻¹ =
        (c ⟨x, hx⟩ * (⟨x, hx⟩ : I)⁻¹)⁻¹ := by group
    rw [h3] at h2
    have h4 := Subgroup.inv_mem _ h2
    rw [inv_inv, Sec18.mem_pCore_iff_mem_pCoreOf] at h4
    simpa [hcx] using h4

end CFSG.RankThree.PartTwo.Sec4.Item4443SL
