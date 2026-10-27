module

public import CFSG.Quasithin.Background.GoldschmidtE23Mixed

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B2F

namespace GE23

section Abstract

variable {V : Type} [CommGroup V] [Finite V] {X T M : Subgroup (MulAut V)}

theorem exists_isFFStarMin_mem {P : Set (Subgroup (MulAut V))} (hP : IsStableFF X P) :
    ∃ A ∈ P, IsFFStarMin X A := by
  obtain ⟨A₀, hA₀P, hmin⟩ := Set.exists_min_image P (fun B => Nat.card B) (Set.toFinite P) hP.1
  refine ⟨A₀, hA₀P, hP.2.1 A₀ hA₀P, fun B hB hBA => ?_⟩
  exact Subgroup.eq_of_le_of_card_ge hBA.2.2.1 (hmin B (hP.2.2.2 A₀ hA₀P B hBA))

theorem ffJP_eq_ffJ (hB : B69.BlkCtx X T M) (h : MinParabolic X T M) (hns : ¬ Group.IsSolvable ↥X)
    {P : Set (Subgroup (MulAut V))} (hP : IsStableFF X P) : ffJP P X = ffJ X := by
  classical
  set N := ffJP P X with hNdef
  have hPN : ∀ A ∈ P, A ≤ N := fun A hA => B19.le_ffJP hA (hP.2.1 A hA).1
  refine le_antisymm (iSup₂_le fun A hA => iSup_le fun _ =>
    le_iSup₂_of_le A (hP.2.1 A hA) le_rfl) ?_
  rw [B69.ffJ_eq_blk hB]
  refine iSup₂_le fun L hL => ?_
  obtain ⟨A₀, hA₀P, hA₀⟩ := exists_isFFStarMin_mem hP
  obtain ⟨L₀, hL₀, hLA₀⟩ := B69.exists_component_of_nonsolvable hB.hV hB.hP4 h hB.hO2 hns hA₀
  obtain ⟨t, ht, hconj⟩ := B69.exists_conj_component h hL₀ hL
  have htX : t ∈ X := h.isSylow.1 ht
  have hA₁P : B6.conjSub t A₀ ∈ P := hP.2.2.1 A₀ hA₀P t htX
  have hA₁ : IsFFStarMin X (B6.conjSub t A₀) := B69.isFFStarMin_conjSub hA₀ htX
  have hLA₁ : ⁅L, B6.conjSub t A₀⁆ = L := by
    rw [← hconj, B69.commutator_conjSub, hLA₀]
  have hLN : L ≤ N := by
    rw [← hLA₁]
    refine Subgroup.commutator_le.2 fun l hl a ha => ?_
    have h1 : l * a * l⁻¹ ∈ N := B1Red.ffJP_conj_mem hP (hL.1 hl) (hPN _ hA₁P ha)
    exact N.mul_mem h1 (N.inv_mem (hPN _ hA₁P ha))
  refine B69.blk_le_iff.2 ⟨hLN, fun A' hA' hLA' => ?_⟩
  have hW₀ : commV L ∈ IrrPlus L (⊤ : Subgroup V) :=
    B69.commV_mem_irrPlus hB.hV hB.hctx hA₁ hL hLA₁
  have hLq := hL.2.2
  have hperf : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hLq.1
  have hnt : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial hLq
  rcases B69.compShape_iff.1 (hB.hctx _ L hA₁ hL hLA₁ (commV L) hW₀) with hNat₁ | hAlt₁
  · rcases B69.compShape_iff.1 (hB.hctx A' L hA' hL hLA' (commV L) hW₀) with hNat' | hAlt'
    · exact hNat'.2.1.1.trans hLN
    · obtain ⟨⟨e, -, hbin⟩, -, -⟩ := hNat₁
      exact (not_nat_and_alt hperf hnt hbin hAlt').elim
  · exact (hB.hG1 _ L hA₁ hL hLA₁ hAlt₁ A' hA' hLA').trans (sup_le hLN (hPN _ hA₁P))

end Abstract

end GE23

end CFSG.Quasithin
