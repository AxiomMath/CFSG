module

public import CFSG.Quasithin.Background.C124YLBase
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.B2FactorizationOffender

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.YL

open CFSG.Quasithin CFSG.Open

variable {G : Type} [Group G] [Finite G] {V R : Subgroup G} (hV : IsElemAbelian 2 V)

theorem fixes_of_baum (hVR : V ≤ R) (hRN : R ≤ Subgroup.normalizer (V : Set G))
    {s : MulAut (IntMod V hV)} (hs : s ∈ autI hV (baum R)) {v : IntMod V hV}
    (hv : v ∈ fixV (autI hV (thompsonJ R))) : s v = v := by
  have hJN : thompsonJ R ≤ Subgroup.normalizer (V : Set G) :=
    (thompsonJ_le_self R).trans hRN
  have hvC := (mem_fixV_autI hV hJN v).1 hv
  have hvR : v.val ∈ R ⊓ Subgroup.centralizer (thompsonJ R : Set G) := ⟨hVR v.val_mem, hvC⟩
  have hv2 : v.val ^ 2 = 1 := by simpa [pow_two] using hV.2 v.val v.val_mem
  have hΩ : v.val ∈ omegaOneCenterOf (thompsonJ R) := by
    rw [← (omegaOne_centralizer_thompsonJ R).1]
    exact Subgroup.subset_closure ⟨hvR, hv2⟩
  obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hs
  refine IntMod.val_injective ?_
  rw [convI_apply_val]
  have hgc := Subgroup.mem_centralizer_iff.1 hg.2 v.val hΩ
  rw [← hgc, mul_inv_cancel_right]

theorem jst_eq_iSup (hRN : R ≤ Subgroup.normalizer (V : Set G)) :
    autI hV (thompsonJ R) = ⨆ (A : Subgroup G) (_ : IsMaxElemAbelian R A), autI hV A :=
  autI_iSup₂ hV (fun _ hA => hA.1.trans hRN)

theorem jst_le_baum (R : Subgroup G) : autI hV (thompsonJ R) ≤ autI hV (baum R) :=
  autI_mono hV (B2F.thompsonJ_le_baum R)

theorem baum_le_R (R : Subgroup G) : autI hV (baum R) ≤ autI hV R :=
  autI_mono hV (B2F.baum_le R)

theorem autI_eq_bot_or_mem {A : Subgroup G} (hA : IsMaxElemAbelian R A) :
    autI hV A = ⊥ ∨ autI hV A ∈ offenderImages hV R := by
  by_cases h : A ≤ Subgroup.centralizer (V : Set G)
  · exact Or.inl (autI_eq_bot_of_le_centralizer hV h)
  · exact Or.inr ⟨A, ⟨hA, h⟩, rfl⟩

theorem jst_normalizes {x : MulAut (IntMod V hV)}
    (hx : x ∈ autI hV R) : B1.conjAut x (autI hV (thompsonJ R)) = autI hV (thompsonJ R) := by
  obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hx
  have h := autI_cjSub hV g.2 (thompsonJ R)
  rw [cjSub_thompsonJ (Subgroup.le_normalizer hg)] at h
  rw [conjAut_eq_map]
  exact h

theorem woff_of_mem_offenderImages (hVR : V ≤ R) (hRN : R ≤ Subgroup.normalizer (V : Set G))
    (U Z : Subgroup (IntMod V hV)) {B : Subgroup (MulAut (IntMod V hV))}
    (hB : B ∈ offenderImages hV R) : WOff U Z B ∧ B ≤ autI hV R := by
  have h := offenderImages_isFFStarOffender hV hVR hRN hB
  have hW : Nat.card (IntMod V hV) ≤ Nat.card B * Nat.card (fixV B) := by
    have := h.2.2.2 ⊥ bot_le
    rwa [B1.card_bot_mul_card_fixV] at this
  exact ⟨⟨h.2.1, h.2.2.1, card_le_liftFix_of_offender U Z hW⟩, h.1⟩

end CFSG.Quasithin.C124.YL
