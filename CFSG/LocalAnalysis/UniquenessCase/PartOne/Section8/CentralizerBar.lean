module

public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem mem_normalizer_of_forall_commutator_mem {L : Subgroup G} {x : G}
    (h : ∀ y ∈ L, ⁅x, y⁆ ∈ CFSG.Open.pCoreOf 2 L) :
    x ∈ Subgroup.normalizer (L : Set G) := by
  have hOle : CFSG.Open.pCoreOf 2 L ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hmaple : L.map (MulAut.conj x).toMonoidHom ≤ L := by
    rintro z ⟨y, hy, rfl⟩
    change x * y * x⁻¹ ∈ L
    have hxy : x * y * x⁻¹ = ⁅x, y⁆ * y := by
      rw [commutatorElement_def]
      group
    rw [hxy]
    exact L.mul_mem (hOle (h y hy)) hy
  have hmap : L.map (MulAut.conj x).toMonoidHom = L :=
    Subgroup.eq_of_le_of_card_ge hmaple (by
      rw [Subgroup.card_map_of_injective (MulAut.conj x).injective])
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap

@[expose] def centralizerBar (P L : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ P ∧ ∀ y ∈ L, ⁅x, y⁆ ∈ CFSG.Open.pCoreOf 2 L}
  one_mem' := by
    refine ⟨P.one_mem, ?_⟩
    intro y _
    simpa using (CFSG.Open.pCoreOf 2 L).one_mem
  mul_mem' := by
    intro x₁ x₂ hx₁ hx₂
    obtain ⟨hx₁P, hx₁⟩ := hx₁
    obtain ⟨hx₂P, hx₂⟩ := hx₂
    refine ⟨P.mul_mem hx₁P hx₂P, ?_⟩
    intro y hy
    rw [commutatorElement_mul_left_eq_conj_mul]
    have hx₂y : ⁅x₂, y⁆ ∈ CFSG.Open.pCoreOf 2 L := hx₂ y hy
    have hx₁N : x₁ ∈ Subgroup.normalizer (L : Set G) :=
      mem_normalizer_of_forall_commutator_mem hx₁
    have hx₁O : x₁ ∈
        Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) L hx₁N
    exact (CFSG.Open.pCoreOf 2 L).mul_mem
      ((Subgroup.mem_normalizer_iff.mp hx₁O _).1 hx₂y) (hx₁ y hy)
  inv_mem' := by
    intro x hx
    obtain ⟨hxP, hx⟩ := hx
    refine ⟨P.inv_mem hxP, ?_⟩
    intro y hy
    rw [commutatorElement_inv_left]
    have hxN : x ∈ Subgroup.normalizer (L : Set G) :=
      mem_normalizer_of_forall_commutator_mem hx
    have hxO : x ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) L hxN
    have hxinvO : x⁻¹ ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
      (Subgroup.normalizer _).inv_mem hxO
    have hyx : ⁅y, x⁆ ∈ CFSG.Open.pCoreOf 2 L := by
      rw [← commutatorElement_inv]
      exact (CFSG.Open.pCoreOf 2 L).inv_mem (hx y hy)
    simpa using (Subgroup.mem_normalizer_iff.mp hxinvO _).1 hyx

theorem mem_centralizerBar_iff {P L : Subgroup G} {x : G} :
    x ∈ centralizerBar P L ↔
      x ∈ P ∧ ∀ y ∈ L, ⁅x, y⁆ ∈ CFSG.Open.pCoreOf 2 L :=
  Iff.rfl

theorem centralizerBar_le (P L : Subgroup G) : centralizerBar P L ≤ P :=
  fun _ hx => hx.1

theorem centralizerBar_normal {P L : Subgroup G}
    (hPNL : P ≤ Subgroup.normalizer (L : Set G)) :
    ((centralizerBar P L).subgroupOf P).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (centralizerBar_le P L)]
  intro p hp
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    obtain ⟨hcP, hcommc⟩ := mem_centralizerBar_iff.mp hc
    refine mem_centralizerBar_iff.mpr
      ⟨P.mul_mem (P.mul_mem hp hcP) (P.inv_mem hp), ?_⟩
    intro y hy
    have hpN : p ∈ Subgroup.normalizer (L : Set G) := hPNL hp
    have hpN' : p⁻¹ ∈ Subgroup.normalizer (L : Set G) := hPNL (P.inv_mem hp)
    have hy' : p⁻¹ * y * p ∈ L := by
      simpa using (Subgroup.mem_normalizer_iff.mp hpN' y).1 hy
    have hpO : p ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) L hpN
    have hconj : p * ⁅c, p⁻¹ * y * p⁆ * p⁻¹ = ⁅p * c * p⁻¹, y⁆ := by
      rw [commutatorElement_def]
      group
    rw [← hconj]
    exact (Subgroup.mem_normalizer_iff.mp hpO _).1 (hcommc _ hy')
  · intro hpc
    obtain ⟨hpcP, hcommpc⟩ := mem_centralizerBar_iff.mp hpc
    refine mem_centralizerBar_iff.mpr ⟨?_, ?_⟩
    · have hc : p⁻¹ * (p * c * p⁻¹) * p = c := by group
      rw [← hc]
      exact P.mul_mem (P.mul_mem (P.inv_mem hp) hpcP) hp
    · intro y hy
      have hpN : p ∈ Subgroup.normalizer (L : Set G) := hPNL hp
      have hpN' : p⁻¹ ∈ Subgroup.normalizer (L : Set G) := hPNL (P.inv_mem hp)
      have hy' : p * y * p⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hpN y).1 hy
      have hp'O : p⁻¹ ∈
          Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
        CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) L hpN'
      have hconj : p⁻¹ * ⁅p * c * p⁻¹, p * y * p⁻¹⁆ * p = ⁅c, y⁆ := by
        rw [commutatorElement_def]
        group
      rw [← hconj]
      simpa using (Subgroup.mem_normalizer_iff.mp hp'O _).1 (hcommpc _ hy')

theorem commutator_eq_bot_centralizerBar {P Q L : Subgroup G}
    (hQ : Q ≤ L) (hQO2 : Q ⊓ CFSG.Open.pCoreOf 2 L = ⊥)
    (hPQ : P ≤ Subgroup.normalizer (Q : Set G)) :
    ⁅Q, centralizerBar P L⁆ = ⊥ := by
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro q hq c hc
  have hqL : q ∈ L := hQ hq
  have hcP : c ∈ P := (mem_centralizerBar_iff.mp hc).1
  have hcQ : c ∈ Subgroup.normalizer (Q : Set G) := hPQ hcP
  have hcommQ : ⁅q, c⁆ ∈ Q := by
    have hconj : c * q⁻¹ * c⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp hcQ q⁻¹).1 (Q.inv_mem hq)
    rw [commutatorElement_def]
    simpa [mul_assoc] using Q.mul_mem hq hconj
  have hcommO : ⁅q, c⁆ ∈ CFSG.Open.pCoreOf 2 L := by
    have hcq : ⁅c, q⁆ ∈ CFSG.Open.pCoreOf 2 L :=
      (mem_centralizerBar_iff.mp hc).2 q hqL
    rw [← commutatorElement_inv]
    exact (CFSG.Open.pCoreOf 2 L).inv_mem hcq
  have hmem : ⁅q, c⁆ ∈ Q ⊓ CFSG.Open.pCoreOf 2 L := ⟨hcommQ, hcommO⟩
  rw [hQO2] at hmem
  exact hmem

theorem le_centralizerBar_iff {P Y L : Subgroup G} (hY : Y ≤ P) :
    Y ≤ centralizerBar P L ↔ ⁅L, Y⁆ ≤ CFSG.Open.pCoreOf 2 L := by
  constructor
  · intro h
    rw [Subgroup.commutator_le]
    intro l hl y hy
    have hyl : ⁅y, l⁆ ∈ CFSG.Open.pCoreOf 2 L := (h hy).2 l hl
    have h2 : ⁅l, y⁆ = ⁅y, l⁆⁻¹ := (commutatorElement_inv y l).symm
    rw [h2]
    exact (CFSG.Open.pCoreOf 2 L).inv_mem hyl
  · intro h y hy
    refine mem_centralizerBar_iff.mpr ⟨hY hy, ?_⟩
    intro l hl
    have h1 : ⁅l, y⁆ ∈ CFSG.Open.pCoreOf 2 L := Subgroup.commutator_le.mp h l hl y hy
    have h2 : ⁅y, l⁆ = ⁅l, y⁆⁻¹ := (commutatorElement_inv l y).symm
    rw [h2]
    exact (CFSG.Open.pCoreOf 2 L).inv_mem h1

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
