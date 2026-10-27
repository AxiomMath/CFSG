module

public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofGlueInj
public import CFSG.LocalAnalysis.StandardType.GGTypeAEndNodeBlock
public import CFSG.LocalAnalysis.StandardType.GGTypeAFarPerm

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LieType.Universal.SpecialLinear Matrix

section Generated

variable {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G} {n : ℕ} {F : Type} [Field F]
  {φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) F →* G} {x y : G}

theorem ggTypeANbr_generated (hC : GGFarCtx p Bs φ₁ φ₂ x y) {J K' : Subgroup G}
    (hJ : (φ₂.comp (slUpperBlockHom n F)).range = J) (hK : φ₂.range = K') :
    K' ≤ ⨆ (g : G) (_ : g ∈ K' ⊓ Subgroup.normalizer (Bs : Set G)),
      J.map (MulAut.conj g).toMonoidHom := by
  set H := ⨆ (g : G) (_ : g ∈ K' ⊓ Subgroup.normalizer (Bs : Set G)),
    J.map (MulAut.conj g).toMonoidHom with hH
  have hgen : ∀ (a b : Fin (n + 1)) (hab : a ≠ b) (c : F),
      φ₂ (SpecialLinearGroup.transvection hab c) ∈ H := by
    intro a b hab c
    have hs : ({a, b} : Finset (Fin (n + 1))).card <
        (Finset.univ : Finset (Fin (n + 1))).card := by
      have hle : ({a, b} : Finset (Fin (n + 1))).card ≤ 2 := by
        have h' := Finset.card_insert_le a ({b} : Finset (Fin (n + 1)))
        simpa using h'
      have := hC.three_le
      simp only [Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card hs
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap i (Fin.last n) with hσ
    have hσa : σ a ≠ Fin.last n := by
      intro h
      apply hi.1
      have := congrArg σ h
      rw [hσ, Equiv.swap_apply_self] at this
      rw [Equiv.swap_apply_right] at this
      exact this.symm
    have hσb : σ b ≠ Fin.last n := by
      intro h
      apply hi.2
      have := congrArg σ h
      rw [hσ, Equiv.swap_apply_self] at this
      rw [Equiv.swap_apply_right] at this
      exact this.symm
    have hu : slPerm hC.two σ * SpecialLinearGroup.transvection hab c * (slPerm hC.two σ)⁻¹ =
        SpecialLinearGroup.transvection (σ.injective.ne hab) c := by
      simpa using conj_transvection_of_coe_eq_signedPerm (coe_slPerm hC.two σ)
        (fun s => by simp) hab c
    have hmem : ∀ (A B : Fin (n + 1)) (hAB : A ≠ B) (hA : A ≠ Fin.last n) (hB : B ≠ Fin.last n),
        φ₂ (SpecialLinearGroup.transvection hAB c) ∈ J := by
      intro A B hAB hA hB
      obtain ⟨a', ha'⟩ : ∃ a' : Fin n, a'.castSucc = A :=
        ⟨A.castPred hA, Fin.castSucc_castPred _ _⟩
      obtain ⟨b', hb'⟩ : ∃ b' : Fin n, b'.castSucc = B :=
        ⟨B.castPred hB, Fin.castSucc_castPred _ _⟩
      subst ha' hb'
      have hab' : a' ≠ b' := fun h => hAB (by rw [h])
      rw [← hJ]
      exact ⟨SpecialLinearGroup.transvection hab' c, by
        simp only [MonoidHom.comp_apply, slUpperBlockHom_transvection]⟩
    have hJmem := hmem (σ a) (σ b) (σ.injective.ne hab) hσa hσb
    have hgK : (φ₂ (slPerm hC.two σ))⁻¹ ∈ K' ⊓ Subgroup.normalizer (Bs : Set G) :=
      ⟨Subgroup.inv_mem _ (hK ▸ ⟨_, rfl⟩), Subgroup.inv_mem _ (hC.perm_mem_normalizer₂ σ)⟩
    have hconj : φ₂ (SpecialLinearGroup.transvection hab c) =
        (MulAut.conj (φ₂ (slPerm hC.two σ))⁻¹).toMonoidHom
          (φ₂ (SpecialLinearGroup.transvection (σ.injective.ne hab) c)) := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hu, map_mul, map_mul, map_inv]
      group
    rw [hconj]
    exact (le_iSup₂ (f := fun (g : G) (_ : g ∈ K' ⊓ Subgroup.normalizer (Bs : Set G)) =>
      J.map (MulAut.conj g).toMonoidHom) _ hgK) (Subgroup.mem_map_of_mem _ hJmem)
  rw [← hK]
  rintro _ ⟨s, rfl⟩
  have hs : s ∈ Subgroup.closure (Set.range
      (fun t : TransvectionStruct (Fin (n + 1)) F => t.toSpecialLinearGroup)) := by
    rw [SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field]
    exact Subgroup.mem_top s
  refine Subgroup.closure_induction (p := fun s _ => φ₂ s ∈ H) ?_ ?_ ?_ ?_ hs
  · rintro _ ⟨⟨a, b, hab, c⟩, rfl⟩
    exact hgen a b hab c
  · rw [map_one]
    exact H.one_mem
  · intro s t _ _ hs ht
    rw [map_mul]
    exact H.mul_mem hs ht
  · intro s _ hs
    rw [map_inv]
    exact H.inv_mem hs

end Generated

end CFSG.StandardType

end
