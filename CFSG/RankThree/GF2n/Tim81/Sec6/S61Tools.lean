module

public import CFSG.RankThree.GF2n.Tim81.Sec5.Defs

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n
open CFSG.Timmesfeld.Bridge
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G]

theorem commutator_mem_kOf_of_mem_normalizer {V H : Subgroup G} {f x : G}
    (hfH : f ∈ Subgroup.normalizer (H : Set G))
    (hfW : f ∈ Subgroup.centralizer (Tim79a.xOf V H : Set G)) (hx : x ∈ H) :
    ⁅f, x⁆ ∈ kOf V H := by
  rw [mem_kOf_iff]
  refine ⟨?_, ?_⟩
  · have h1 : f * x * f⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp hfH x).mp hx
    have h2 : ⁅f, x⁆ = (f * x * f⁻¹) * x⁻¹ := by rw [commutatorElement_def]
    rw [h2]
    exact H.mul_mem h1 (H.inv_mem hx)
  · have hfC : f⁻¹ ∈ Subgroup.centralizer (Tim79a.xOf V H : Set G) :=
      (Subgroup.centralizer (Tim79a.xOf V H : Set G)).inv_mem hfW
    have hxN : x ∈ Subgroup.normalizer (Tim79a.xOf V H : Set G) :=
      Tim79a.H_le_normalizer_xOf V H hx
    have hconj : x * f⁻¹ * x⁻¹ ∈ Subgroup.centralizer (Tim79a.xOf V H : Set G) :=
      (Subgroup.mem_normalizer_iff.mp (mem_normalizer_centralizer hxN) f⁻¹).mp hfC
    have heq : ⁅f, x⁆ = f * (x * f⁻¹ * x⁻¹) := by rw [commutatorElement_def]; group
    rw [heq]
    exact (Subgroup.centralizer (Tim79a.xOf V H : Set G)).mul_mem hfW hconj

theorem commutator_conj_mem_of_quotMod {H K W : Subgroup G} (hs : QuotMod.Hyp H K W) {f y k : G}
    (hfH : ∀ z ∈ H, ⁅f, z⁆ ∈ K) (hy : y ∈ H) (hk : k ∈ K) (hfk : ⁅f, k⁆ ∈ W) :
    ⁅f, y * k * y⁻¹⁆ ∈ W := by
  have hn : ⁅f, y⁆ ∈ K := hfH y hy
  have hk' : y * k * y⁻¹ ∈ K := hs.conj y hy k hk
  have hw' : y * ⁅f, k⁆ * y⁻¹ ∈ W := hs.conj₀ y hy ⁅f, k⁆ hfk
  have hid : ⁅f, y * k * y⁻¹⁆ =
      (⁅f, y⁆ * (y * ⁅f, k⁆ * y⁻¹) * ⁅f, y⁆⁻¹) *
        (⁅f, y⁆ * (y * k * y⁻¹) * ⁅f, y⁆⁻¹ * (y * k * y⁻¹)⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [hid]
  exact W.mul_mem (hs.conj_mem hn hw') (hs.comm ⁅f, y⁆ hn (y * k * y⁻¹) hk')

theorem IsL2Gen.exists_orderOf_eq_three {A B : Subgroup G} (h : IsL2Gen A B) :
    ∃ a ∈ A, ∃ b ∈ B, orderOf (a * b) = 3 := by
  obtain ⟨F, hField, hFin, hCharP, φ, hcard, hA, hB⟩ := h
  letI := hField
  letI := hFin
  letI := hCharP
  have hu : utriElt (1 : F) ∈ (A.subgroupOf (A ⊔ B)).map φ.toMonoidHom := by
    rw [hA]
    exact utriElt_mem_utri 1
  have hl : ltriElt (1 : F) ∈ (B.subgroupOf (A ⊔ B)).map φ.toMonoidHom := by
    rw [hB]
    exact ltriElt_mem_ltri 1
  obtain ⟨aH, haA, ha⟩ := Subgroup.mem_map.mp hu
  obtain ⟨bH, hbB, hb⟩ := Subgroup.mem_map.mp hl
  refine ⟨(aH : G), Subgroup.mem_subgroupOf.mp haA, (bH : G),
    Subgroup.mem_subgroupOf.mp hbB, ?_⟩
  have hmul : ((aH : G) * (bH : G)) = ((aH * bH : ↥(A ⊔ B)) : G) := rfl
  rw [hmul, Subgroup.orderOf_coe]
  have hφ : φ (aH * bH) = utriElt (1 : F) * ltriElt 1 := by
    have h := congrArg₂ (· * ·) ha hb
    simpa [map_mul] using h
  rw [← MulEquiv.orderOf_eq φ (aH * bH), hφ]
  exact orderOf_utriElt_mul_ltriElt (one_mul 1)

end CFSG.RankThree.GF2n.Tim81
