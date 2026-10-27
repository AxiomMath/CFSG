module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67Cfg
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Cfg1667

variable {M V W₁ W₂ : Subgroup G} {g : G}

theorem not_mem_of_inCalO (h : Cfg1667 M V W₁ W₂) (hg : InCalO 1 M ⊥ V g) : g ∉ M := by
  intro hgM
  have hgn : g ∈ normalizer (V : Set G) := by rwa [h.normalizer_eq]
  have hconj : conjSubgroup V g = V := conjSubgroup_eq_iff_mem_normalizer.2 hgn
  exact hg.1.1 ((le_of_eq hconj).trans h.le_M)

theorem relIndex_U (h : Cfg1667 M V W₁ W₂) (hg : InCalO 1 M ⊥ V g) :
    (V ⊓ conjSubgroup M g).relIndex V = 2 := by
  have hV : IsPGroup 2 V := IsElemAbelian.isPGroup h.elemAbelian
  have hpow : (conjSubgroup M g).relIndex V = 2 ^ E3.mQuot V (conjSubgroup M g) :=
    E3.relIndex_eq_two_pow hV (conjSubgroup M g)
  have hne : (conjSubgroup M g).relIndex V ≠ 1 := fun h1 =>
    hg.2.1 (Subgroup.relIndex_eq_one.1 h1)
  have hle : E3.mQuot V (conjSubgroup M g) ≤ 1 := hg.1.2.1
  have hk0 : E3.mQuot V (conjSubgroup M g) ≠ 0 := fun h0 =>
    hne (by rw [hpow, h0, pow_zero])
  have hk1 : E3.mQuot V (conjSubgroup M g) = 1 := by omega
  rw [Subgroup.inf_relIndex_left, hpow, hk1, pow_one]

theorem card_U (h : Cfg1667 M V W₁ W₂) (hg : InCalO 1 M ⊥ V g) :
    Nat.card (V ⊓ conjSubgroup M g : Subgroup G) = 8 := by
  have hV : IsPGroup 2 V := IsElemAbelian.isPGroup h.elemAbelian
  have hm : E3.mQuot V (V ⊓ conjSubgroup M g) = 1 := by
    show padicValNat 2 ((V ⊓ conjSubgroup M g).relIndex V) = 1
    rw [relIndex_U h hg]
    exact padicValNat_self
  have hc := E3.card_eq_two_pow_mul hV (inf_le_left : V ⊓ conjSubgroup M g ≤ V)
  rw [hm, pow_one, h.card_V] at hc
  omega

theorem relIndex_B (h : Cfg1667 M V W₁ W₂) (hg : InCalO 1 M ⊥ V g) :
    (conjSubgroup V g ⊓ M).relIndex (conjSubgroup V g) = 2 := by
  have h' := relIndex_U (h.conj g) (inCalO_bot_swap hg)
  simpa only [conjSubgroup_conjSubgroup_inv] using h'

theorem card_B (h : Cfg1667 M V W₁ W₂) (hg : InCalO 1 M ⊥ V g) :
    Nat.card (conjSubgroup V g ⊓ M : Subgroup G) = 8 := by
  have h' := card_U (h.conj g) (inCalO_bot_swap hg)
  simpa only [conjSubgroup_conjSubgroup_inv] using h'

theorem le_normalizer_U (h : Cfg1667 M V W₁ W₂) :
    conjSubgroup V g ⊓ M ≤ normalizer ((V ⊓ conjSubgroup M g : Subgroup G) : Set G) := by
  refine (le_inf ?_ ?_).trans (inf_normalizer_le_normalizer_inf (H := V)
    (K := conjSubgroup M g))
  · intro b hb
    rw [h.normalizer_eq]
    exact hb.2
  · intro b hb
    exact Subgroup.le_normalizer ((E3.conjSubgroup_mono_left g h.le_M) hb.1)

theorem le_normalizer_B (h : Cfg1667 M V W₁ W₂) :
    V ⊓ conjSubgroup M g ≤ normalizer ((conjSubgroup V g ⊓ M : Subgroup G) : Set G) := by
  have hnorm : normalizer (conjSubgroup V g : Set G) = conjSubgroup M g := by
    rw [← E3.conjSubgroup_normalizer V g, h.normalizer_eq]
  refine (le_inf ?_ ?_).trans (inf_normalizer_le_normalizer_inf (H := conjSubgroup V g)
    (K := M))
  · intro u hu
    rw [hnorm]
    exact hu.2
  · intro u hu
    exact Subgroup.le_normalizer (h.le_M hu.1)

theorem commutator_V_B_le (h : Cfg1667 M V W₁ W₂) (hg : InCalO 1 M ⊥ V g) :
    ⁅V, conjSubgroup V g ⊓ M⁆ ≤ V ⊓ conjSubgroup M g := by
  rw [Subgroup.commutator_le]
  intro v hv b hb
  have hbnormV : b ∈ normalizer (V : Set G) := by
    rw [h.normalizer_eq]
    exact hb.2
  have hbvinv : b * v⁻¹ * b⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.1 hbnormV v⁻¹).1 (V.inv_mem hv)
  have hbnormU : b ∈ normalizer ((V ⊓ conjSubgroup M g : Subgroup G) : Set G) :=
    le_normalizer_U h hb
  have hiff : (⟨v, hv⟩ : V) ∈ (V ⊓ conjSubgroup M g).subgroupOf V ↔
      (⟨b * v⁻¹ * b⁻¹, hbvinv⟩ : V) ∈ (V ⊓ conjSubgroup M g).subgroupOf V := by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact (Subgroup.inv_mem_iff (V ⊓ conjSubgroup M g : Subgroup G) (x := v)).symm.trans
      (Subgroup.mem_normalizer_iff.1 hbnormU v⁻¹)
  have hprod : (⟨v, hv⟩ * ⟨b * v⁻¹ * b⁻¹, hbvinv⟩ : V) ∈
      (V ⊓ conjSubgroup M g).subgroupOf V :=
    (Subgroup.mul_mem_iff_of_index_two (H := (V ⊓ conjSubgroup M g).subgroupOf V)
      (relIndex_U h hg)).2 hiff
  have hmem : v * (b * v⁻¹ * b⁻¹) ∈ V ⊓ conjSubgroup M g :=
    (Subgroup.mem_subgroupOf).1 hprod
  rw [commutatorElement_def, show v * b * v⁻¹ * b⁻¹ = v * (b * v⁻¹ * b⁻¹) by group]
  exact hmem

theorem commutator_Vg_U_le (h : Cfg1667 M V W₁ W₂) (hg : InCalO 1 M ⊥ V g) :
    ⁅conjSubgroup V g, V ⊓ conjSubgroup M g⁆ ≤ conjSubgroup V g ⊓ M := by
  have h' := commutator_V_B_le (h.conj g) (inCalO_bot_swap hg)
  simpa only [conjSubgroup_conjSubgroup_inv] using h'

theorem commutator_U_B_le (h : Cfg1667 M V W₁ W₂) (hg : InCalO 1 M ⊥ V g) :
    ⁅V ⊓ conjSubgroup M g, conjSubgroup V g ⊓ M⁆ ≤
      (V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M) := by
  rw [Subgroup.commutator_le]
  intro u hu b hb
  rw [Subgroup.mem_inf]
  constructor
  · have hbnorm : b ∈ normalizer ((V ⊓ conjSubgroup M g : Subgroup G) : Set G) :=
      le_normalizer_U h hb
    have hbu : b * u⁻¹ * b⁻¹ ∈ V ⊓ conjSubgroup M g :=
      (Subgroup.mem_normalizer_iff.1 hbnorm u⁻¹).1 ((V ⊓ conjSubgroup M g).inv_mem hu)
    rw [commutatorElement_def, show u * b * u⁻¹ * b⁻¹ = u * (b * u⁻¹ * b⁻¹) by group]
    exact (V ⊓ conjSubgroup M g).mul_mem hu hbu
  · have hunorm : u ∈ normalizer ((conjSubgroup V g ⊓ M : Subgroup G) : Set G) :=
      le_normalizer_B h hu
    have hub : u * b * u⁻¹ ∈ conjSubgroup V g ⊓ M :=
      (Subgroup.mem_normalizer_iff.1 hunorm b).1 hb
    rw [commutatorElement_def, show u * b * u⁻¹ * b⁻¹ = (u * b * u⁻¹) * b⁻¹ by group]
    exact (conjSubgroup V g ⊓ M).mul_mem hub ((conjSubgroup V g ⊓ M).inv_mem hb)

theorem U_inf_B_eq (h : Cfg1667 M V W₁ W₂) :
    (V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M) = V ⊓ conjSubgroup V g := by
  have hle : conjSubgroup V g ≤ conjSubgroup M g := E3.conjSubgroup_mono_left g h.le_M
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    exact Subgroup.mem_inf.2 ⟨hx.1.1, hx.2.1⟩
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    exact Subgroup.mem_inf.2
      ⟨Subgroup.mem_inf.2 ⟨hx.1, hle hx.2⟩, Subgroup.mem_inf.2 ⟨hx.2, h.le_M hx.1⟩⟩

theorem card_U_inf_B_le (h : Cfg1667 M V W₁ W₂) (hg : InCalO 1 M ⊥ V g) :
    Nat.card ((V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M) : Subgroup G) ≤ 2 := by
  rw [U_inf_B_eq h]
  exact h.card_inf_le g (not_mem_of_inCalO h hg)

end Cfg1667

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
