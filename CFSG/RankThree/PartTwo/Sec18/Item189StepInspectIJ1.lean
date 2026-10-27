module

public import CFSG.RankThree.PartTwo.Sec18.Item189StepInspectIDefs
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupJ1Max
import CFSG.RankThree.PartTwo.Sec3.J1SevenFactProof

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

theorem inspect189J1 :
    Inspect189J1 := by
  intro Y _ _ X Q x hd ⟨e⟩
  have := hd.normal
  obtain ⟨x, rfl⟩ : ∃ x' : X, (x' : Y) = x := ⟨⟨x, hd.mem⟩, rfl⟩
  let ψ : X ≃* CFSG.Sporadic.J1.J := e.trans CFSG.Sporadic.J1.nativeEquiv
  set M := (X ⊓ Subgroup.normalizer (Q : Set Y)) ⊔
    (X ⊓ Subgroup.normalizer (Subgroup.zpowers (x : Y) : Set Y))
  show X ≤ M
  have hT : CFSG.ABGLocalTools.IsSylowOf 2 (Q ⊓ X) X :=
    hd.sylow.inf_of_le_normalizer le_top (by rw [Subgroup.normalizer_eq_top])
  obtain ⟨S, hS⟩ := hT.exists_sylow_eq_subgroupOf
  have hSM : (S : Subgroup X) ≤ M.subgroupOf X := by
    rw [hS]
    exact fun t ht => Subgroup.mem_sup_left ⟨ht.2, Subgroup.le_normalizer ht.1⟩
  have h8 : 2 ^ 3 ∣ Nat.card (M.subgroupOf X) := by
    refine (S.pow_dvd_card_of_pow_dvd_card ?_).trans (Subgroup.card_dvd_of_le hSM)
    rw [Nat.card_congr ψ.toEquiv, CFSG.Sporadic.J1.card_J]
    norm_num
  have hx3 : orderOf (ψ x) = 3 := by
    rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe, hd.orderOf_eq]
  obtain ⟨P₁, hP₁⟩ := Sec3.J1SevenFactProof.sylow_three_eq CFSG.Sporadic.J1.card_J hx3
  obtain ⟨P₀, hP₀⟩ :=
    Sec3.J1SevenFactProof.sylow_three_eq CFSG.Sporadic.J1.card_J CFSG.Sporadic.J1.orderOf_b
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq CFSG.Sporadic.J1.J P₀ P₁
  let θ : CFSG.Sporadic.J1.J ≃* X := (MulAut.conj g).trans ψ.symm
  have hθ : (Subgroup.zpowers CFSG.Sporadic.J1.b).map θ.toMonoidHom = Subgroup.zpowers x := by
    have h1 : (Subgroup.zpowers CFSG.Sporadic.J1.b).map (MulAut.conj g).toMonoidHom =
        Subgroup.zpowers (ψ x) := by
      rw [← hP₀, ← hP₁, ← hg]
      rfl
    rw [show θ.toMonoidHom = ψ.symm.toMonoidHom.comp (MulAut.conj g).toMonoidHom from rfl,
      ← Subgroup.map_map, h1, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply]
  set W := (M.subgroupOf X).comap θ.toMonoidHom with hW
  have hNW : OvergroupJ1.N ≤ W := by
    rw [hW, ← Subgroup.map_le_iff_le_comap, OvergroupJ1.N, OvergroupJ1.H,
      Subgroup.map_equiv_normalizer_eq, hθ]
    intro u hu
    have hu' := Subgroup.le_normalizer_map X.subtype (Subgroup.mem_map_of_mem X.subtype hu)
    rw [MonoidHom.map_zpowers] at hu'
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right ⟨u.2, hu'⟩)
  have hcard : Nat.card W = Nat.card (M.subgroupOf X) := by
    rw [hW, Subgroup.comap_equiv_eq_map_symm', Subgroup.card_map_of_injective θ.symm.injective]
  rcases OvergroupJ1.eq_or_eq_top hNW with h | h
  · rw [h, OvergroupJ1.card_N.1] at hcard
    rw [← hcard] at h8
    norm_num at h8
  · intro k hk
    have hk' : θ.symm ⟨k, hk⟩ ∈ W := by
      rw [h]
      exact Subgroup.mem_top _
    rw [hW, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at hk'
    exact hk'

end CFSG.RankThree.PartTwo.Sec18
