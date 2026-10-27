module

public import CFSG.RankThree.PartTwo.Sec15.Item155wProofDefs
public import CFSG.RankThree.PartTwo.Sec15.Item155RProof
import CFSG.RankThree.PartTwo.Sec15.Item155Proof
import CFSG.RankThree.PartTwo.Sec15.Item153TwinProofTools
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
public import CFSG.RankThree.PartTwo.Sec15.Item153Claims

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem n155_mem_maximalTwoLocalsContaining {A : Subgroup G} (h153 : Item153Main A (lB A))
    {K : Subgroup G} (hK : K ∈ scriptY0Star A (lB A)) :
    n155 A K ∈ CFSG.maximalTwoLocalsContaining ((K ⊔ A : Subgroup G) : Set G) := by
  rw [(h153 K hK).1]
  exact Set.mem_singleton _

theorem le_normalizer_of_isPerfect_of_le_n155 {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h152 : Item152 A (lB A)) (h153 : Item153Main A (lB A))
    {K : Subgroup G} (hK : K ∈ scriptY0Star A (lB A)) {J : Subgroup G}
    (hJp : Group.IsPerfect ↥J) (hJN : J ≤ n155 A K) : J ≤ Subgroup.normalizer (K : Set G) :=
  Proof153Twin.le_normalizer_of_isPerfect_of_le h h152 hK
    (n155_mem_maximalTwoLocalsContaining h153 hK) hJp hJN

theorem le_of_le_n155' {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h152 : Item152 A (lB A)) (h153 : Item153Main A (lB A)) {K X J : Subgroup G}
    (hK : K ∈ scriptY0Star A (lB A)) (hX4 : X ∈ scriptY4 A (lB A))
    (hJ0 : J ∈ scriptY0 A (lB A)) (hXJ : X ≤ J) (hXK : X ≤ K) (hJN : J ≤ n155 A K) : J ≤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJNK : J ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_of_isPerfect_of_le_n155 h h152 h153 hK (isPerfect_of_mem_scriptY4 hJ0.1) hJN
  have hq : IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J) := hJ0.1.2.2.2
  set O := CFSG.pCore 2 ↥J with hO
  set V := (J ⊓ K).subgroupOf J with hV
  have hVn : V.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
    (Late.le_normalizer_inf Subgroup.le_normalizer hJNK)
  have hVmap : (V.map (QuotientGroup.mk' O)).Normal := hVn.map _ (QuotientGroup.mk'_surjective O)
  have hXV : X.subgroupOf J ≤ V := fun x hx => Subgroup.mem_subgroupOf.mpr
    ⟨x.2, hXK (Subgroup.mem_subgroupOf.mp hx)⟩
  have hJle : J ≤ (J ⊓ K) ⊔ CFSG.Open.pCoreOf 2 J := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hVmap with htop | hcen
    · have hsup : V ⊔ O = ⊤ := by
        have h1 := Subgroup.comap_map_eq (QuotientGroup.mk' O) V
        rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at h1
        exact h1.symm
      intro x hx
      have hx' : (⟨x, hx⟩ : ↥J) ∈ V ⊔ O := hsup ▸ Subgroup.mem_top _
      rw [Subgroup.mem_sup_of_normal_left] at hx'
      obtain ⟨v, hv, o, ho, hvo⟩ := hx'
      have hvG : (v : G) ∈ J ⊓ K := Subgroup.mem_subgroupOf.mp hv
      have hoG : (o : G) ∈ CFSG.Open.pCoreOf 2 J := (mem_pCoreOf_iff155 o).mpr ho
      have hxe : x = (v : G) * (o : G) := by
        have := congrArg Subtype.val hvo
        simpa using this.symm
      rw [hxe]
      exact mul_mem (Subgroup.mem_sup_left hvG) (Subgroup.mem_sup_right hoG)
    · exfalso
      have hNs : Group.IsSolvable O := by
        have := (CFSG.pCore_isPGroup : IsPGroup 2 O).isNilpotent
        infer_instance
      have hKs := isSolvable_comap_center O hNs
      have hVK : V ≤ (Subgroup.center (↥J ⧸ O)).comap (QuotientGroup.mk' O) :=
        fun x hx => hcen (Subgroup.mem_map_of_mem _ hx)
      have hXs : Group.IsSolvable (X.subgroupOf J) :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion (hXV.trans hVK))
          (Subgroup.inclusion_injective _)
      have hXs' : Group.IsSolvable ↥X := Group.isSolvable_of_surjective
        (f := (Subgroup.subgroupOfEquivOfLe hXJ).toMonoidHom) (MulEquiv.surjective _)
      have hXp : Group.IsPerfect ↥X := isPerfect_of_mem_scriptY4 hX4
      have : Nontrivial ↥X :=
        (Subgroup.nontrivial_iff_ne_bot X).mpr (ne_bot_of_mem_scriptY4 hX4)
      exact Group.IsPerfect.not_isSolvable ↥X hXs'
  have hOK : CFSG.Open.pCoreOf 2 J ≤ Subgroup.normalizer (K : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 J).trans hJNK
  have hcop : Nat.Coprime 3 (Nat.card (CFSG.Open.pCoreOf 2 J)) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) J)
    rw [hn]
    exact Nat.Coprime.pow_right _ (by norm_num)
  calc J = oPrimeResidualOf 3 J := hJ0.1.2.1
    _ ≤ K := by
      rw [oPrimeResidualOf_eq_closure, Subgroup.closure_le]
      rintro x ⟨hx, k, hk⟩
      have hle' : (J ⊓ K) ⊔ CFSG.Open.pCoreOf 2 J ≤ K ⊔ CFSG.Open.pCoreOf 2 J :=
        sup_le_sup_right inf_le_right _
      have hx' : x ∈ K ⊔ CFSG.Open.pCoreOf 2 J := hle' (hJle hx)
      exact mem_left_of_pow_prime_pow Nat.prime_three hOK hcop hx' hk

theorem one155w_of {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h152 : Item152 A (lB A)) (h153 : Item153Main A (lB A)) (hUp : Step155Up A c L)
    {Y : Subgroup G} (hY : IsY155 A Y) (hab : Above155w A (oPrimeResidualOf 3 Y))
    (htwo : ∀ Y', IsY155 A Y' → oPrimeResidualOf 3 Y' = oPrimeResidualOf 3 Y → Two155w A Y') :
    One155 A Y := by
  intro hom
  set X := oPrimeResidualOf 3 Y with hX
  have hX4 : X ∈ scriptY4 A (lB A) := hY.2.1
  have hXY : X ≤ Y := oPrimeResidualOf_le_self 3 Y
  have hYX : Y ≤ Subgroup.normalizer (X : Set G) :=
    le_normalizer_oPrimeResidualOf Subgroup.le_normalizer
  obtain ⟨N₀, hN₀⟩ := exists_mem_maximalTwoLocalsContaining hY.1.1
  have hN₀' : N₀ ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ Y : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact hN₀
  obtain ⟨hYN, hAN, hN2, hNF⟩ := facts_of_mem_maximalTwoLocalsContaining h hN₀
  obtain ⟨K₀, hK₀N, hXK₀, hK₀0⟩ := h152 X hX4 N₀ hN2 (hXY.trans hYN) hNF
  obtain ⟨hK₀Y, hK₀res⟩ := isY155_of_mem_scriptY0 hK₀0
  have hN₀K : N₀ ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ K₀ : Subgroup G) : Set G) :=
    ⟨hN₀.1, fun x hx => (sup_le hAN (le_of_mem_thetaComponentsIn hK₀N)) hx⟩
  have hYΔ : Y ≤ delta A (lB A) N₀ := hY.1.2.le.trans (delta_mono hYN)
  suffices H : ∃ K₁ ∈ scriptY0Star A (lB A), K₀ ≤ K₁ ∧ delta A (lB A) N₀ ≤ n155 A K₁ by
    obtain ⟨K₁, hK₁, hK₀K₁, hΔK₁⟩ := H
    refine ⟨K₁, hK₁, hXK₀.trans hK₀K₁, ?_⟩
    have hYN₁ : Y ≤ n155 A K₁ := hYΔ.trans hΔK₁
    have hK₁N₁ : K₁ ∈ thetaComponentsIn (n155 A K₁) :=
      mem_thetaComponentsIn_of_item152 h h152 hK₁ (n155_mem_maximalTwoLocalsContaining h153 hK₁)
    exact le_normalizer_of_mem_thetaComponentsIn (hYN₁.trans Subgroup.le_normalizer) hK₁N₁
      (hXK₀.trans hK₀K₁) (isPerfect_of_mem_scriptY4 hX4) (ne_bot_of_mem_scriptY4 hX4) hYX
  have hΓ₀ : ∀ K₁ ∈ scriptY0Star A (lB A), K₀ ≤ K₁ →
      K₁ ∈ gam155 A (lB A) K₀ (oPrimeResidualOf 3 K₀) := fun K₁ hK₁ hK₀K₁ =>
    ⟨hK₁, by rw [hK₀res]; exact hK₀K₁, hK₀K₁.trans Subgroup.le_normalizer⟩
  rcases eq_or_lt_of_le hXK₀ with hXeq | hXlt
  ·
    obtain ⟨K₁, hK₁le, hK₁⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY0 A (lB A))) hK₀0
    refine ⟨K₁, hK₁, hK₁le, ?_⟩
    have hres : oPrimeResidualOf 3 K₀ = oPrimeResidualOf 3 Y := by rw [hK₀res, ← hXeq]
    refine htwo K₀ hK₀Y hres K₁ (hΓ₀ K₁ hK₁ hK₁le) (Or.inl ?_) N₀ hN₀K
    rw [hres]
    exact hom
  ·
    obtain ⟨K₁, hK₀K₁, hK₁⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY0 A (lB A))) hK₀0
    have hOm : omg155 A K₀ ∨ K₁ = K₀ ⊔ CFSG.Open.pCoreOf 2 K₁ := by
      by_cases hcl : ∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧
          L' ∈ lA A c' ∧ L' = (L' ⊓ X) ⊔ CFSG.Open.pCoreOf 2 L'
      · exact Or.inl (omg155_of_le hXK₀ hcl)
      · have hcl1 := hom.resolve_right hcl
        exact hUp h Y hY hcl1.1 hcl1.2 hcl N₀ hN₀' K₀ hK₀N hK₀0 hXlt K₁ hK₁ hK₀K₁
    refine ⟨K₁, hK₁, hK₀K₁, ?_⟩
    have hlt : oPrimeResidualOf 3 Y < oPrimeResidualOf 3 K₀ := by
      rw [hK₀res]
      exact hXlt
    refine (hab K₀ hK₀Y hlt).2 K₁ (hΓ₀ K₁ hK₁ hK₀K₁) ?_ N₀ hN₀K
    rw [hK₀res]
    exact hOm

theorem item155_of_item155w {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (hN : Step155N A c L) (hw : Item155w A (lB A)) : Item155 A (lB A) := by
  rw [item155_iff]
  intro Y hY
  obtain ⟨h1, h2⟩ := item155w_iff.mp hw Y hY
  exact ⟨h1, two155_of_two155w h hN h2⟩

theorem item155R_of_item155wR (hN : Step155NR) (hw : Item155wR) : Item155R :=
  fun G _ _ A c L hR => item155_of_item155w hR.toSec14Std (hN G A c L hR) (hw G A c L hR)

end CFSG.RankThree.PartTwo.Sec15
