module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139Defs
import CFSG.Quasithin.Background.ASVolIRu.StUnique
import CFSG.Quasithin.Recognition.RuTypeSL3
import CFSG.Quasithin.Background.F918E1
import CFSG.LargeExtraspecial.D73IdentPSL

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open CFSG.Quasithin CFSG.Quasithin.RuType CFSG.Quasithin.RuType.SL3 CFSG.Open
open CFSG.Quasithin.G11
open scoped MatrixGroups

private theorem gapL32_commuting_eq_id {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : Representation (ZMod 2) SL(3, ZMod 2) M) (χ : M →+ Matrix (Fin 3) (Fin 3) (ZMod 2))
    (hinj : Function.Injective χ) (htr : ∀ m, IsTraceZero (χ m))
    (hsurj : ∀ A, IsTraceZero A → ∃ m, χ m = A)
    (hequi : ∀ (g : SL(3, ZMod 2)) (m : M), χ (ρ g m) = stAct g (χ m))
    (f : M →ₗ[ZMod 2] M) (hinjf : Function.Injective f)
    (hcomm : ∀ (g : SL(3, ZMod 2)) (m : M), f (ρ g m) = ρ g (f m)) (m : M) : f m = m := by
  have hA0 : IsTraceZero stA0 := by decide +kernel
  obtain ⟨m0, hm0⟩ := hsurj stA0 hA0
  have hfix0 : ∀ g ∈ P0, ρ g m0 = m0 := fun g hg => hinj (by rw [hequi, hm0, stA0_fix g hg])
  have hfm0 : ∀ g ∈ P0, ρ g (f m0) = f m0 := fun g hg => by rw [← hcomm, hfix0 g hg]
  have h1 : f m0 = 0 ∨ f m0 = m0 := by
    rcases fix_P0_st (χ (f m0)) (htr _) (fun g hg => by rw [← hequi, hfm0 g hg]) with h | h
    · exact Or.inl (hinj (by rw [h, map_zero]))
    · exact Or.inr (hinj (by rw [h, hm0]))
  have hstA0ne : stA0 ≠ 0 := by decide +kernel
  have hm0ne : m0 ≠ 0 := by
    intro h
    rw [h, map_zero] at hm0
    exact hstA0ne hm0.symm
  have h2 : f m0 = m0 := by
    rcases h1 with h | h
    · exact absurd (hinjf (by rw [h, map_zero])) hm0ne
    · exact h
  have hsmul : ∀ (a : ZMod 2) (x : M), χ (a • x) = a • χ x := by
    intro a x
    rcases zmod_two_cases a with rfl | rfl <;> simp
  obtain ⟨c, hc⟩ := exists_stComb (htr m)
  have hsum : m = ∑ i, c i • ρ (stGens i) m0 := by
    apply hinj
    rw [map_sum, ← hc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsmul, hequi, hm0]
    rfl
  calc f m = f (∑ i, c i • ρ (stGens i) m0) := by rw [← hsum]
    _ = ∑ i, c i • ρ (stGens i) (f m0) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, hcomm]
    _ = m := by rw [h2, ← hsum]

theorem gapEndL32_holds : GapEndL32 := by
  intro Q _ _ hQ2 L hL3 hirrOn hcard
  have hirr : ∀ B : Subgroup Q, (∀ l ∈ L, ∀ b ∈ B, l b ∈ B) → B = ⊥ ∨ B = ⊤ :=
    fun B hB => hirrOn.2.2.2 B hB bot_le le_top
  haveI : Module (ZMod 2) (Additive Q) :=
    AddCommGroup.zmodModule (G := Additive Q) (fun x => by
      have hx := hQ2 (Additive.toMul x)
      rw [two_nsmul]
      apply Additive.toMul.injective
      rw [toMul_add, ← pow_two]
      exact hx)
  haveI : Finite (Additive Q) := inferInstanceAs (Finite Q)
  have hcardV : Nat.card (Additive Q) = 2 ^ 8 :=
    (Nat.card_congr (Additive.ofMul : Q ≃ Additive Q)).symm.trans hcard
  have hSC := (show CFSG.Blueprint.LieModel ↥L .PSL 3 2 1 from hL3).statedClassicalModel_of_ne_zero
    (by norm_num : (3 : ℕ) ≠ 0)
  obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := hSC
  have hK2 : Nat.card K = 2 := by simpa using hK
  obtain ⟨eK2⟩ := CFSG.LargeExtraspecial.DW.D73.nonempty_mulEquiv_SL_of_card_two hK2 3
  let eL : ↥L ≃* SL(3, ZMod 2) := eK.trans eK2
  let Φ := mulAutLin Q
  let ρ : Representation (ZMod 2) SL(3, ZMod 2) (Additive Q) :=
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom).comp
      ((Φ : MulAut Q →* (Additive Q ≃ₗ[ZMod 2] Additive Q)).comp
        (L.subtype.comp eL.symm.toMonoidHom))
  have hρ : ∀ (g : SL(3, ZMod 2)) (m : Additive Q),
      ρ g m = Additive.ofMul ((eL.symm g : MulAut Q) (Additive.toMul m)) := fun _ _ => rfl
  have hirrρ : ∀ N : Submodule (ZMod 2) (Additive Q), (∀ g : SL(3, ZMod 2), ∀ m ∈ N, ρ g m ∈ N) →
      N = ⊥ ∨ N = ⊤ := by
    intro N hN
    let B : Subgroup Q :=
      { carrier := {q | Additive.ofMul q ∈ N}
        mul_mem' := fun {a b} ha hb => by
          show Additive.ofMul (a * b) ∈ N
          rw [ofMul_mul]
          exact N.add_mem (show Additive.ofMul a ∈ N from ha) (show Additive.ofMul b ∈ N from hb)
        one_mem' := N.zero_mem
        inv_mem' := fun {a} ha => by
          have := N.neg_mem (show Additive.ofMul a ∈ N from ha)
          show Additive.ofMul a⁻¹ ∈ N
          rwa [ofMul_inv] }
    have hstab : ∀ l ∈ L, ∀ b ∈ B, l b ∈ B := by
      intro l hl b hb
      have hg : eL.symm (eL ⟨l, hl⟩) = ⟨l, hl⟩ := eL.symm_apply_apply _
      have h := hN (eL ⟨l, hl⟩) (Additive.ofMul b) hb
      rw [hρ, hg] at h
      exact h
    rcases hirr B hstab with h | h
    · left
      refine (Submodule.eq_bot_iff N).2 fun v hv => ?_
      have hv' : Additive.toMul v ∈ B := by
        change Additive.ofMul (Additive.toMul v) ∈ N
        simpa using hv
      rw [h, Subgroup.mem_bot] at hv'
      exact Additive.toMul.injective hv'
    · right
      refine (eq_top_iff).2 fun v _ => ?_
      have hv' : Additive.toMul v ∈ B := by rw [h]; exact Subgroup.mem_top _
      exact hv'
  obtain ⟨χ, hinj, htr, hsurj, hequi⟩ := stUnique (Additive Q) ρ hcardV hirrρ
  refine (Subgroup.eq_bot_iff_forall _).2 fun c hc => ?_
  rw [Subgroup.mem_centralizer_iff] at hc
  have hcomm : ∀ (g : SL(3, ZMod 2)) (m : Additive Q),
      (Φ c).toLinearMap (ρ g m) = ρ g ((Φ c).toLinearMap m) := by
    intro g m
    have hl : ((eL.symm g : ↥L) : MulAut Q) ∈ (L : Set (MulAut Q)) := (eL.symm g).2
    have h := congrArg (fun φ : MulAut Q => φ (Additive.toMul m)) (hc _ hl)
    rw [hρ, hρ]
    exact congrArg Additive.ofMul h.symm
  have hfix := gapL32_commuting_eq_id ρ χ hinj htr hsurj hequi (Φ c).toLinearMap
    (Φ c).injective hcomm
  ext x
  have := hfix (Additive.ofMul x)
  simpa [Φ, mulAutLin_apply] using this

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139
