module

public import CFSG.Quasithin.H13.NQRigidCPUModule
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorSection

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup CFSG.Quasithin
open CFSG.QuasithinUnique.Setup.Family (IsComp IsBestOffender)

variable {V : Type} [CommGroup V] [Finite V]

theorem section_of_bestOffender (hV : ∀ v : V, v * v = 1) {G₀ L₀ B : Subgroup (MulAut V)}
    (hL : IsComp L₀ G₀) (hB : IsBestOffender G₀ B) (hLB : ⁅L₀, B⁆ ≠ ⊥) :
    ∃ (W₀ : Type) (_ : CommGroup W₀) (_ : Finite W₀) (_ : Nontrivial W₀),
      (∀ w : W₀, w * w = 1) ∧ ∃ L₁ B₁ : Subgroup (MulAut W₀), CFSG.IsQuasisimple ↥L₁ ∧
        (∀ U : Subgroup W₀, (∀ g ∈ L₁, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤) ∧
        IsElemAbelian2 B₁ ∧ B₁ ≠ ⊥ ∧ B₁ ≤ normalizer (L₁ : Set (MulAut W₀)) ∧
        IsQuadratic B₁ ∧ Nat.card W₀ ≤ Nat.card B₁ * Nat.card (fixV B₁) ∧
        Nonempty (↥L₁ ⧸ center ↥L₁ ≃* ↥L₀ ⧸ center ↥L₀) := by
  classical
  obtain ⟨hBN, -, ⟨S⟩⟩ :=
    CFSG.QuasithinUnique.Setup.Layer.Actor.irreducibleSectionProp V hV G₀ L₀ B hL hB hLB
  have hLq : CFSG.IsQuasisimple ↥L₀ :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mpr hL.2.2)
  set fL : ↥L₀ →* MulAut S.W := S.τW.comp (inclusion le_sup_left) with hfL
  set fB : ↥B →* MulAut S.W := S.τW.comp (inclusion le_sup_right) with hfB
  have hW2 : ∀ w : S.W, w * w = 1 := by
    intro w
    obtain ⟨v, rfl⟩ := S.π_surjective w
    rw [← map_mul]
    have h1 : v * v = 1 := Subtype.ext (by
      rw [coe_mul, OneMemClass.coe_one]
      exact hV v)
    rw [h1, map_one]
  refine ⟨S.W, S.commGroup, S.finite, S.nontrivial, hW2, fL.range, fB.range, S.lbar_quasisimple,
    fun U hU => S.irreducible U fun x hx u hu => ?_, S.abar_elem, S.abar_ne_bot, ?_,
    S.abar_quadratic, S.abar_offender, ?_⟩
  · have hx' : x = inclusion le_sup_left ⟨(x : MulAut V), hx⟩ := Subtype.ext rfl
    rw [hx']
    exact hU _ ⟨⟨(x : MulAut V), hx⟩, rfl⟩ u hu
  ·
    rintro _ ⟨b, rfl⟩
    rw [mem_normalizer_iff]
    have hconj : ∀ (c : ↥B) (l : ↥L₀), fB c * fL l * (fB c)⁻¹ =
        fL ⟨(c : MulAut V) * l * (c : MulAut V)⁻¹,
          (mem_normalizer_iff.mp (hBN c.2) l).mp l.2⟩ := by
      intro c l
      rw [hfB, hfL, MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_inv,
        ← map_mul, ← map_mul]
      rfl
    intro y
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨_, (hconj b l).symm⟩
    · rintro ⟨l, hl⟩
      refine ⟨⟨(b : MulAut V)⁻¹ * l * (b : MulAut V)⁻¹⁻¹,
        (mem_normalizer_iff.mp (hBN (inv_mem b.2)) l).mp l.2⟩, ?_⟩
      have h1 := hconj b⁻¹ l
      have h2 : fB b⁻¹ = (fB b)⁻¹ := map_inv fB b
      rw [h2, inv_inv, hl] at h1
      rw [show (⟨(b : MulAut V)⁻¹ * l * (b : MulAut V)⁻¹⁻¹, _⟩ : ↥L₀) =
        ⟨((b⁻¹ : ↥B) : MulAut V) * l * ((b⁻¹ : ↥B) : MulAut V)⁻¹,
          (mem_normalizer_iff.mp (hBN (b⁻¹).2) l).mp l.2⟩ from rfl, ← h1]
      group
  ·
    have hsurj : Function.Surjective fL.rangeRestrict := fL.rangeRestrict_surjective
    have hker : fL.rangeRestrict.ker ≤ center ↥L₀ := by
      rcases CFSG.LocalCores.quasisimple_normal_subgroups hLq
          (MonoidHom.normal_ker fL.rangeRestrict) with h | h
      · exfalso
        apply S.lbar_ne_bot
        rw [eq_bot_iff]
        rintro _ ⟨l, rfl⟩
        have hl : l ∈ fL.rangeRestrict.ker := h ▸ mem_top l
        have hl' := congrArg Subtype.val (MonoidHom.mem_ker.mp hl)
        exact (mem_bot).mpr hl'
      · exact h
    exact ⟨(centerQuotEquivOfSurjective hLq.1 fL.rangeRestrict hsurj hker).symm⟩

end CFSG.Quasithin.H13.NQRigid
