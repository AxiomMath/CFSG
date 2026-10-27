module

public import CFSG.ClassicalInvolution.WeakCT.StandardPair
import CFSG.ClassicalInvolution.WeakCT.Standard
public import CFSG.LieType.CurtisTits.SpecialLinear

public section

namespace CFSG.StandardType

open CFSG.ClassicalInvolution.WeakCT

section Pair

variable {K : Type} [Field K] {X : Type} [Group X]

theorem linearBlockStandardPair_eq_sup {W U V : Subgroup X}
    (h : LinearBlockStandardPair K W U V) : W = U ⊔ V := by
  obtain ⟨θ, hrange, -, hU, hV⟩ := pair_normalize h
  rw [← hrange, MonoidHom.range_eq_map, ← B12_sup_B23 (K := K), Subgroup.map_sup, hU, hV]

theorem linearBlockStandardPair_subgroupOf {W U V : Subgroup X} (H : Subgroup X) (hW : W ≤ H)
    (h : LinearBlockStandardPair K W U V) :
    LinearBlockStandardPair K (W.subgroupOf H) (U.subgroupOf H) (V.subgroupOf H) := by
  obtain ⟨θ, c, hrange, hker, hor⟩ := h
  let θ' : Matrix.SpecialLinearGroup (Fin 3) K →* ↥H :=
    θ.codRestrict H (fun x => hW (hrange ▸ (⟨x, rfl⟩ : θ x ∈ θ.range)))
  have hcomp : H.subtype.comp θ' = θ := by ext x; rfl
  have hmap : ∀ A : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K),
      A.map θ' = (A.map θ).subgroupOf H := by
    intro A
    apply Subgroup.map_injective (f := H.subtype) Subtype.coe_injective
    rw [Subgroup.map_map, hcomp, Subgroup.subgroupOf_map_subtype]
    exact (inf_eq_left.mpr (le_trans (Subgroup.map_le_range (f := θ) A)
      (by rw [hrange]; exact hW))).symm
  have hker' : θ'.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) := by
    have hθ' : θ'.ker = θ.ker := MonoidHom.ker_codRestrict θ H _
    rw [hθ']
    exact hker
  refine ⟨θ', c, ?_, hker', ?_⟩
  · rw [MonoidHom.range_eq_map, hmap, ← MonoidHom.range_eq_map, hrange]
  · rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by rw [hmap, h1], by rw [hmap, h2]⟩
    · exact Or.inr ⟨by rw [hmap, h1], by rw [hmap, h2]⟩

end Pair

section System

variable {X : Type} [Group X]

theorem iSup_subgroupOf_eq_top {ι : Type*} (S : ι → Subgroup X) (H : Subgroup X)
    (hS : ∀ i, S i ≤ H) (hgen : ⨆ i, S i = H) : ⨆ i, (S i).subgroupOf H = ⊤ := by
  apply Subgroup.map_injective (f := H.subtype) Subtype.coe_injective
  rw [Subgroup.map_iSup, Subgroup.map_top]
  have h : ∀ i, ((S i).subgroupOf H).map H.subtype = S i := by
    intro i
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.mpr (hS i)
  rw [iSup_congr h, hgen, Subgroup.range_subtype]

theorem tier1_subtype_system {ι : Type} (S : ι → Subgroup X) (H : Subgroup X)
    (hgen : ⨆ i, S i = H) {k : ℕ} (e : Fin k ≃ ι) (Pc Pp : Fin k → Fin k → Prop) {K : Type}
    [Field K] (hcomm : ∀ i j, Pc i j → ∀ a ∈ S (e i), ∀ b ∈ S (e j), a * b = b * a)
    (hpair : ∀ i j, Pp i j → ∃ W, LinearBlockStandardPair K W (S (e i)) (S (e j))) :
    ⨆ i : Fin k, (S (e i)).subgroupOf H = ⊤ ∧
      (∀ i j, Pc i j → ∀ a ∈ (S (e i)).subgroupOf H, ∀ b ∈ (S (e j)).subgroupOf H,
        a * b = b * a) ∧
      (∀ i j, Pp i j → ∃ W, LinearBlockStandardPair K W ((S (e i)).subgroupOf H)
        ((S (e j)).subgroupOf H)) := by
  have hS : ∀ i : Fin k, S (e i) ≤ H := by
    intro i
    rw [← hgen]
    exact le_iSup (fun j => S j) (e i)
  refine ⟨?_, ?_, ?_⟩
  · exact iSup_subgroupOf_eq_top (fun i : Fin k => S (e i)) H hS
      (by rw [Equiv.iSup_comp (g := S) e, hgen])
  · intro i j hij a ha b hb
    rw [Subgroup.mem_subgroupOf] at ha hb
    exact Subtype.ext (hcomm i j hij (a : X) ha (b : X) hb)
  · intro i j hij
    obtain ⟨W, hW⟩ := hpair i j hij
    have hle : W ≤ H := by
      rw [linearBlockStandardPair_eq_sup hW]
      exact sup_le (hS i) (hS j)
    exact ⟨W.subgroupOf H, linearBlockStandardPair_subgroupOf H hle hW⟩

end System

end CFSG.StandardType

end
