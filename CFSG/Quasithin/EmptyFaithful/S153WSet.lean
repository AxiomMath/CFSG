module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS2Basic

public section

namespace CFSG.QuasithinUnique.AppCS2W

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.AppC
  CFSG.QuasithinUnique.DoubleA3 CFSG.QuasithinUnique.AppCS2 Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H S L : Subgroup G}

structure WSet {G : Type} [Group G] [Finite G] (H S L : Subgroup G) : Prop where
  sylow : IsSylowTwoOf S H
  block : IsChi0Block H L
  thompson : ⁅L, thompsonJ S⁆ = L
  eq_join : H = conjJoin S L ⊔ S

structure WDbl {G : Type} [Group G] [Finite G] (H S L : Subgroup G) (t : G) : Prop where
  hcs : WSet H S L
  h5 : IsAltType L 5
  ht : t ∈ S
  hne : conjR L t ≠ L
  hjoin : conjJoin S L = L ⊔ conjR L t
  hcomm : ⁅L, conjR L t⁆ = ⊥

namespace WSet

theorem isShort (hcs : WSet H S L) : IsShort2 L := hcs.block.1.1

theorem le_H (hcs : WSet H S L) : L ≤ H := hcs.block.1.2.1

theorem pCoreOf_le_S (hcs : WSet H S L) : pCoreOf 2 H ≤ S := hcs.sylow.pCoreOf_le

theorem isSylowTwoOf_inf (hcs : WSet H S L) : IsSylowTwoOf (S ⊓ L) L :=
  CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal hcs.sylow hcs.block.1.2.1
    hcs.block.1.2.2

end WSet

namespace WDbl

variable {t : G} (D : WDbl H S L t)
include D

theorem comm_elem' : ∀ a ∈ L, ∀ b ∈ conjR L t, a * b = b * a := by
  intro a ha b hb
  have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp D.hcomm
  exact (Subgroup.mem_centralizer_iff.mp (this ha) b hb).symm

theorem H_le_normalizer_conjJoin : H ≤ normalizer (conjJoin S L : Set G) := by
  rw [D.hcs.eq_join]
  exact sup_le Subgroup.le_normalizer (C56.S_le_normalizer_conjJoin L)

theorem blockQ_le_pCoreOf_conjJoin : blockQ L ≤ pCoreOf 2 (conjJoin S L) := by
  have hLK : L ≤ conjJoin S L := C56.le_conjJoin L (one_mem _)
  refine C1.le_pCoreOf_of_normalized ((C1.blockQ_le L).trans hLK) ?_ (C1.blockQ_isPGroup L)
  rw [D.hjoin]
  refine sup_le (C1.le_normalizer_blockQ L) ?_
  exact C5.le_normalizer_of_commute fun u hu a ha =>
    (D.comm_elem' a (C1.blockQ_le L ha) u hu).symm

theorem pCoreOf_conjJoin_le : pCoreOf 2 (conjJoin S L) ≤ pCoreOf 2 H := by
  have hKH : conjJoin S L ≤ H := by
    rw [D.hcs.eq_join]
    exact le_sup_left
  refine C1.le_pCoreOf_of_normalized
    ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _).trans hKH)
    (fun g hg => ?_) (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _)
  exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (conjJoin S L)
    (D.H_le_normalizer_conjJoin hg)

theorem blockU_le_pCoreOf_general : blockU L ≤ pCoreOf 2 H :=
  (C1.blockU_le_blockQ D.hcs.isShort).trans
    (D.blockQ_le_pCoreOf_conjJoin.trans D.pCoreOf_conjJoin_le)

theorem bb1 : ∀ p ∈ pCoreOf 2 H, ∀ l ∈ L, p * l * p⁻¹ * l⁻¹ ∈ blockU L := by
  intro p hp l hl
  refine C1.commutator_mem_blockU_double D.hcs.isShort D.comm_elem' D.hcs.le_H ?_ hp hl
  rw [← D.hjoin]
  exact D.H_le_normalizer_conjJoin

theorem c55 {M₀ : Subgroup G} (hC52 : C5.NoCommonNormal S H M₀) (hSM : S ≤ M₀) :
    ∃ y ∈ M₀, ¬ conjR (blockU L) y ≤ pCoreOf 2 H := by
  by_contra hcon
  push Not at hcon
  have hL := D.hcs.isShort
  set U := blockU L with hU
  set P := pCoreOf 2 H with hP
  set X : Subgroup G := ⨆ y : M₀, conjR U (y : G) with hX
  have hXP : X ≤ P := iSup_le fun y => hcon y y.2
  have hUX : U ≤ X := by
    have h1 : conjR U ((⟨1, one_mem _⟩ : M₀) : G) ≤ X :=
      le_iSup (fun y : M₀ => conjR U (y : G)) ⟨1, one_mem _⟩
    have h2 : conjR U ((⟨1, one_mem _⟩ : M₀) : G) = U := conjSubgroup_one U
    rwa [h2] at h1
  have hXne : X ≠ ⊥ := fun h => C56.blockU_ne_bot hL (le_bot_iff.mp (h ▸ hUX))
  have hXS : X ≤ S := hXP.trans D.hcs.pCoreOf_le_S
  have hM₀X : M₀ ≤ normalizer (X : Set G) := by
    intro m hm
    rw [← conjSubgroup_eq_iff_mem_normalizer]
    have hle : conjSubgroup X m ≤ X := by
      have : conjSubgroup X m = ⨆ y : M₀, conjSubgroup (conjR U (y : G)) m := by
        simp only [conjSubgroup, hX]
        exact Subgroup.map_iSup _ _
      rw [this]
      refine iSup_le fun y => ?_
      have : conjSubgroup (conjR U (y : G)) m = conjR U ((y : G) * m) :=
        conjSubgroup_conjSubgroup U (y : G) m
      rw [this]
      exact le_iSup (fun y : M₀ => conjR U (y : G)) ⟨(y : G) * m, mul_mem y.2 hm⟩
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [C5.card_conjSubgroup])
  have key : ∀ l ∈ L, ∀ x ∈ X, l * x * l⁻¹ ∈ X := by
    intro l hl x hx
    refine Subgroup.iSup_induction (fun y : M₀ => conjR U (y : G))
      (C := fun x => l * x * l⁻¹ ∈ X) hx ?_ ?_ ?_
    · intro y x hxy
      have hxP : x ∈ P := hcon y y.2 hxy
      have hc : l * x * l⁻¹ * x⁻¹ ∈ U := by
        have h1 := D.bb1 x hxP l hl
        have e : l * x * l⁻¹ * x⁻¹ = (x * l * x⁻¹ * l⁻¹)⁻¹ := by group
        rw [e]
        exact inv_mem h1
      have hxX : x ∈ X := le_iSup (fun y : M₀ => conjR U (y : G)) y hxy
      have e : l * x * l⁻¹ = (l * x * l⁻¹ * x⁻¹) * x := by group
      rw [e]
      exact mul_mem (hUX hc) hxX
    · simp
    · intro a b ha hb
      have e : l * (a * b) * l⁻¹ = (l * a * l⁻¹) * (l * b * l⁻¹) := by group
      rw [e]
      exact mul_mem ha hb
  have hLX : L ≤ normalizer (X : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => key l hl x hx
    · intro h
      have := key l⁻¹ (inv_mem hl) _ h
      simpa [mul_assoc] using this
  have hHX : H ≤ normalizer (X : Set G) := by
    rw [D.hcs.eq_join]
    refine sup_le (iSup_le fun s => ?_) (hSM.trans hM₀X)
    rintro g ⟨l, hl, rfl⟩
    have hs : (s : G) ∈ normalizer (X : Set G) := hM₀X (hSM s.2)
    have e : (MulAut.conj (s : G)).toMonoidHom l = (s : G) * l * (s : G)⁻¹ := by
      simp [MulAut.conj_apply]
    rw [e]
    exact mul_mem (mul_mem hs (hLX hl)) (inv_mem hs)
  exact hC52 X hXS hXne hHX hM₀X

theorem not_conj_le_of_mem_diff {M₀ : Subgroup G} (hC52 : C5.NoCommonNormal S H M₀) (hSM : S ≤ M₀)
    (h2 : S.relIndex M₀ = 2) {x : G} (hx : x ∈ M₀) (hxS : x ∉ S) :
    ¬ conjR (blockU L) x ≤ pCoreOf 2 H := by
  obtain ⟨y, hy, hyU⟩ := D.c55 hC52 hSM
  have hyS : y ∉ S := by
    intro hyS
    apply hyU
    have hUP := D.blockU_le_pCoreOf_general
    have hPn : y ∈ normalizer (pCoreOf 2 H : Set G) :=
      CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H (D.hcs.sylow.le hyS)
    have := C5.conjSubgroup_mono hUP y
    rwa [C5.conjSubgroup_eq_self hPn] at this
  have hs : y⁻¹ * x ∈ S := inv_mul_mem_of_relIndex_two h2 hy hyS hx hxS
  intro hxP
  apply hyU
  have hPn : (y⁻¹ * x)⁻¹ ∈ normalizer (pCoreOf 2 H : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
      (D.hcs.sylow.le (inv_mem hs))
  have h1 := C5.conjSubgroup_mono hxP (y⁻¹ * x)⁻¹
  rw [C56.conjR_eq, conjSubgroup_conjSubgroup, C5.conjSubgroup_eq_self hPn] at h1
  have e : x * (y⁻¹ * x)⁻¹ = y := by group
  rw [e] at h1
  exact h1

end WDbl

end CFSG.QuasithinUnique.AppCS2W
