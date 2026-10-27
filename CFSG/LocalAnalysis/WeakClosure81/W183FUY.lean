module

public import CFSG.LocalAnalysis.WeakClosure81.W183FUBorel
public import CFSG.LocalAnalysis.WeakClosure81.W183TwoL24Two
import CFSG.LocalAnalysis.WeakClosure81.W183Abs3

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsU3)

theorem w183fu_E25_of_commuting {W : Type*} [Group W] {z₁ z₂ : W} (h₁ : orderOf z₁ = 5)
    (h₂ : orderOf z₂ = 5) (hcomm : z₁ * z₂ = z₂ * z₁)
    (hdisj : Subgroup.zpowers z₁ ⊓ Subgroup.zpowers z₂ = ⊥) :
    IsElemAbelian 5 (Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂) ∧
      Nat.card ↥(Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂) = 25 := by
  classical
  have hA5 : ∀ a : Subgroup.zpowers z₁, (a : W) ^ 5 = 1 := by
    intro a
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
    rw [← hi]
    have h5 : z₁ ^ 5 = 1 := by rw [← h₁]; exact pow_orderOf_eq_one z₁
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h5, one_zpow]
  have hB5 : ∀ b : Subgroup.zpowers z₂, (b : W) ^ 5 = 1 := by
    intro b
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp b.2
    rw [← hi]
    have h5 : z₂ ^ 5 = 1 := by rw [← h₂]; exact pow_orderOf_eq_one z₂
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h5, one_zpow]
  have hcAB : ∀ (a : Subgroup.zpowers z₁) (b : Subgroup.zpowers z₂),
      Commute (a : W) (b : W) := by
    intro a b
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
    rw [← hi, ← hj]
    exact (show Commute z₁ z₂ from hcomm).zpow_zpow i j
  set φ : Subgroup.zpowers z₁ × Subgroup.zpowers z₂ →* W :=
    MonoidHom.noncommCoprod (Subgroup.zpowers z₁).subtype (Subgroup.zpowers z₂).subtype
      (fun a b => by simpa using hcAB a b) with hφ
  have hinj : Function.Injective φ := by
    rw [hφ, MonoidHom.noncommCoprod_injective]
    refine ⟨(Subgroup.zpowers z₁).subtype_injective, (Subgroup.zpowers z₂).subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
    exact disjoint_iff_inf_le.mpr (le_of_eq hdisj)
  have hrange : φ.range = Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂ := by
    rw [hφ, MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have hcard : Nat.card ↥(Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂) = 25 := by
    rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod,
      Nat.card_zpowers, Nat.card_zpowers, h₁, h₂]
  have habel : IsElemAbelian 5 (Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂) := by
    rw [← hrange]
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨p, hp⟩ := a.2
      obtain ⟨q, hq⟩ := b.2
      apply Subtype.ext
      show (a : W) * (b : W) = (b : W) * (a : W)
      rw [← hp, ← hq, ← map_mul, ← map_mul]
      congr 1
      exact Prod.ext (mul_comm' p.1 q.1) (mul_comm' p.2 q.2)
    · obtain ⟨p, hp⟩ := hx
      obtain ⟨m, n⟩ := p
      rw [← hp, ← map_pow, Prod.pow_mk]
      have h1 : m ^ 5 = 1 := Subtype.ext (hA5 m)
      have h2 : n ^ 5 = 1 := Subtype.ext (hB5 n)
      rw [h1, h2]
      exact map_one φ
  exact ⟨habel, hcard⟩

section Certified


variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem w183fu_E25 {Y T L₁ L₂ : Subgroup (LGL 2 V)} (hT : IsSylowIn 2 T Y)
    (htwo : Br2TwoComp Y T L₁ L₂) (hshape₁ : IsU3 ↥L₁ 2) (hshape₂ : IsU3 ↥L₂ 2) :
    ∃ E : Subgroup (LGL 2 V),
      E ≤ Y ⊓ Subgroup.normalizer ((T ⊓ L₁ ⊔ T ⊓ L₂ : Subgroup (LGL 2 V)) : Set (LGL 2 V)) ∧
        IsElemAbelian 5 E ∧ Nat.card E = 25 := by
  obtain ⟨hQ₁, hQ₂⟩ := w183tp_two_sylow hT htwo
  obtain ⟨z₁, hz₁, hz₁o⟩ := w183fu_five_borel hshape₁ hQ₁
  obtain ⟨z₂, hz₂, hz₂o⟩ := w183fu_five_borel hshape₂ hQ₂
  have hL12 : L₁ ⊓ L₂ = ⊥ := by
    haveI := htwo.simple₁
    exact w183_inf_eq_bot_of_commute htwo.nonab₁ htwo.comm
  have hcomm : z₁ * z₂ = z₂ * z₁ := htwo.comm z₁ hz₁.1 z₂ hz₂.1
  have hdisj : Subgroup.zpowers z₁ ⊓ Subgroup.zpowers z₂ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx₁ : x ∈ L₁ := (Subgroup.zpowers_le.mpr hz₁.1) hx.1
    have hx₂ : x ∈ L₂ := (Subgroup.zpowers_le.mpr hz₂.1) hx.2
    have : x ∈ L₁ ⊓ L₂ := ⟨hx₁, hx₂⟩
    rwa [hL12] at this
  obtain ⟨hE, hcard⟩ := w183fu_E25_of_commuting hz₁o hz₂o hcomm hdisj
  refine ⟨Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂, ?_, hE, hcard⟩
  refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
  · exact ⟨htwo.le₁ hz₁.1, w183tp_two_borel_mem htwo hz₁⟩
  · exact ⟨htwo.le₂ hz₂.1, w183tp_two_borel_mem' htwo hz₂⟩

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
