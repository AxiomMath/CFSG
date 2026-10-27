module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3NatEnd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3NatIrr
public import CFSG.Quasithin.Background.SmithD310UCaseI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}

private theorem s16t3_mem_irrSet_iff' (I : Subgroup W) :
    I ∈ irrSet L ↔ I ∈ IrrPlus L (⊤ : Subgroup W) := by
  rw [irrSet, Set.mem_setOf_eq, mem_irrPlus_top_iff]
  constructor
  · rintro ⟨hcomm, hlt, hstab, -, hirr⟩
    exact ⟨hstab, hcomm, hlt, hirr⟩
  · rintro ⟨hstab, hcomm, hlt, hirr⟩
    refine ⟨hcomm, hlt, hstab, fun x hx w hw => ⟨hstab x hx w hw.1, ?_⟩, hirr⟩
    rw [mem_fixV.1 hw.2 x hx]
    exact hw.2

private theorem s16t3_perfect_of_quasisimple (hq : CFSG.Open.IsQuasisimple ↥L) :
    ⁅L, L⁆ = L := by
  have htop : commutator ↥L = ⊤ := hq.1
  have hmap := congrArg (Subgroup.map (L.subtype : ↥L →* MulAut W)) htop
  rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, L.range_subtype] at hmap
  exact hmap

private noncomputable def s16t3_qact (W : Type) [CommGroup W] (L : Subgroup (MulAut W)) :
    MulDistribMulAction ↥(Subgroup.normalizer (L : Set (MulAut W)))
      (W ⧸ modFix L (⊤ : Subgroup W)) :=
  quotAct (V := W) (X := L) (T := Subgroup.normalizer (L : Set (MulAut W))) (W := ⊤)
    le_rfl (fun _ _ _ _ => trivial)

private theorem s16t3_fixed_quot_eq_bot (hq : CFSG.Open.IsQuasisimple ↥L) :
    letI := s16t3_qact W L
    XMod.fixed ↥L (⊤ : Subgroup (W ⧸ modFix L (⊤ : Subgroup W))) = ⊥ := by
  letI := s16t3_qact W L
  have hZ : modFix L (⊤ : Subgroup W) = fixV L := by
    rw [modFix, fixed_eq_inf_fixV, top_inf_eq]
  apply le_bot_iff.1
  intro q hqfix
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (modFix L (⊤ : Subgroup W)) q
  have hcommZ : ∀ l : ↥L, ((l : MulAut W) w) * w⁻¹ ∈ fixV L := by
    intro l
    have h1 : (QuotientGroup.mk (((l : MulAut W) w)) :
        W ⧸ modFix L (⊤ : Subgroup W)) = QuotientGroup.mk w := by
      have h := hqfix.2 l
      change (l • (QuotientGroup.mk w : W ⧸ modFix L (⊤ : Subgroup W))) =
        (QuotientGroup.mk w : W ⧸ modFix L (⊤ : Subgroup W)) at h
      rw [XMod.smul_quotMk] at h
      exact h
    have h2 := QuotientGroup.eq_iff_div_mem.1 h1
    rwa [hZ, div_eq_mul_inv] at h2
  let c : ↥L →* W :=
    { toFun := fun l => (l : MulAut W) w * w⁻¹
      map_one' := by simp
      map_mul' := fun l₁ l₂ => by
        have hfix : (l₁ : MulAut W) ((l₂ : MulAut W) w * w⁻¹) =
            (l₂ : MulAut W) w * w⁻¹ :=
          (mem_fixV.1 (hcommZ l₂)) (l₁ : MulAut W) l₁.2
        have key : (l₁ : MulAut W) ((l₂ : MulAut W) w) =
            ((l₂ : MulAut W) w * w⁻¹) * ((l₁ : MulAut W) w) := by
          have h2 : (l₂ : MulAut W) w = ((l₂ : MulAut W) w * w⁻¹) * w := by group
          conv_lhs => rw [h2]
          rw [map_mul, hfix]
        show ((l₁ * l₂ : ↥L) : MulAut W) w * w⁻¹ =
          ((l₁ : MulAut W) w * w⁻¹) * ((l₂ : MulAut W) w * w⁻¹)
        rw [Subgroup.coe_mul]
        simp only [MulAut.mul_apply, key]
        ac_rfl }
  have hcomm : commutator ↥L = ⊤ := hq.1
  have hker : (⊤ : Subgroup ↥L) ≤ c.ker := by
    rw [← hcomm]
    change ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ ≤ c.ker
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_inv, map_inv]
    simp [mul_comm, mul_assoc, mul_left_comm]
  have hw : w ∈ fixV L := by
    have h2 : ∀ l : ↥L, (l : MulAut W) w * w⁻¹ = 1 := fun l =>
      MonoidHom.mem_ker.1 (hker (Subgroup.mem_top l))
    refine mem_fixV.2 fun l hl => ?_
    have h3 := h2 ⟨l, hl⟩
    rw [mul_inv_eq_one] at h3
    exact h3
  rw [← hZ] at hw
  exact (QuotientGroup.eq_one_iff w).2 hw

private theorem s16t3_commOf_eq_of_isIrr (hq : CFSG.Open.IsQuasisimple ↥L)
    {Y : Subgroup (W ⧸ modFix L (⊤ : Subgroup W))}
    (hY : letI := s16t3_qact W L; XMod.IsIrr ↥L Y) :
    letI := s16t3_qact W L; XMod.commOf ↥L Y = Y := by
  letI := s16t3_qact W L
  have hfix := s16t3_fixed_quot_eq_bot (W := W) (L := L) hq
  rcases hY.2.2 (XMod.commOf ↥L Y) (XMod.isInv_commOf Y) bot_le
    (XMod.commOf_le_of_isInv hY.1) with h | h
  · exfalso
    have hle : Y ≤ XMod.fixed ↥L (⊤ : Subgroup (W ⧸ modFix L (⊤ : Subgroup W))) :=
      XMod.commOf_eq_bot_iff.1 h
    rw [hfix] at hle
    exact hY.2.1.ne' (le_bot_iff.1 hle)
  · exact h

private theorem s16t3_stableUnder_commSub {J : Subgroup W} (hJ : StableUnder L J) :
    StableUnder L (commSub J L) := by
  intro l hl i hi
  unfold commSub at hi ⊢
  induction hi using Subgroup.closure_induction with
  | mem c hc =>
    obtain ⟨x, hx, w, hw, rfl⟩ := hc
    have e : l (x w * w⁻¹) = ((l * x) w * w⁻¹) * (l w * w⁻¹)⁻¹ := by
      simp only [map_mul, map_inv, MulAut.mul_apply]
      group
    rw [e]
    exact mul_mem (Subgroup.subset_closure ⟨l * x, L.mul_mem hl hx, w, hw, rfl⟩)
      (inv_mem (Subgroup.subset_closure ⟨l, hl, w, hw, rfl⟩))
  | one => rw [map_one]; exact one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  | inv a _ ha => rw [map_inv]; exact inv_mem ha

theorem s16t3_commSub_mem_irrSet_of_natural (hq : CFSG.Open.IsQuasisimple ↥L)
    {I : Subgroup W} (hZI : fixV L ≤ I) (hnat : SumOfNatShape L I (fixV L) 1) :
    commSub I L ∈ irrSet L ∧ SumOfNatShape L (commSub I L) (commSub I L ⊓ fixV L) 1 ∧
      commSub I L ⊔ fixV L = I := by
  have hIirr := SumOfNatShape.isIrrOn hq hnat
  have hperf := s16t3_perfect_of_quasisimple (L := L) hq
  have hstable : StableUnder L (commSub I L) := s16t3_stableUnder_commSub hIirr.2.1
  have hIJ : commSub I L ≤ I := commSub_le_of_invariant hIirr.2.1
  have hcomm : commSub (commSub I L) L = commSub I L :=
    CFSG.Quasithin.SmithD310U.commSub_commSub_eq hperf I
  have hIZ : commSub I L ⊔ fixV L = I := by
    have hle : commSub I L ⊔ fixV L ≤ I := sup_le hIJ hZI
    have hstab : StableUnder L (commSub I L ⊔ fixV L) := by
      intro l hl x hx
      rcases Subgroup.mem_sup.1 hx with ⟨a, ha, b, hb, rfl⟩
      exact Subgroup.mem_sup.2
        ⟨l a, hstable l hl a ha, l b, hIirr.2.2.1 l hl b hb, (map_mul l a b).symm⟩
    rcases hIirr.2.2.2 (commSub I L ⊔ fixV L) hstab le_sup_right hle with hfix | hJ
    · exfalso
      obtain ⟨l, hl, u, hu, hlu⟩ := SumOfNatShape.exists_move hq hnat
      have hgen : l u * u⁻¹ ∈ commSub I L := Subgroup.subset_closure ⟨l, hl, u, hu, rfl⟩
      have hlefix : commSub I L ≤ fixV L := by rw [← hfix]; exact le_sup_left
      exact hlu (hlefix hgen)
    · exact hJ
  have hInat := SumOfNatShape.restrict hnat hIJ hstable hIZ
  exact ⟨⟨hcomm, SumOfNatShape.isIrrOn hq hInat⟩, hInat, hIZ⟩

theorem s16t3_summands (h : SumOfNatShape L (⊤ : Subgroup W) (fixV L) 3) :
    ∃ I : Fin 3 → Subgroup W, (∀ i, fixV L ≤ I i) ∧
      (∀ i, I i ⊓ (fixV L ⊔ ⨆ (j : Fin 3) (_ : j ≠ i), I j) ≤ fixV L) ∧
      (fixV L ⊔ ⨆ i, I i) = ⊤ ∧
      (∀ i, SumOfNatShape L (I i) (fixV L) 1) := by
  obtain ⟨n, hcases⟩ := h
  rcases hcases with ⟨hS, hsum⟩ | ⟨hS, hsum⟩ | ⟨hS, hsum⟩ | ⟨hS, hsum⟩ | ⟨hS, hsum⟩
  · obtain ⟨I, hZI, hind, hsup, hN⟩ := hsum
    exact ⟨I, hZI, hind, hsup, fun i =>
      ⟨n, Or.inl ⟨hS, s16t3_sumOfNat_singleton (hZI i) (hN i)⟩⟩⟩
  · obtain ⟨I, hZI, hind, hsup, hN⟩ := hsum
    exact ⟨I, hZI, hind, hsup, fun i =>
      ⟨n, Or.inr (Or.inl ⟨hS, s16t3_sumOfNat_singleton (hZI i) (hN i)⟩)⟩⟩
  · obtain ⟨I, hZI, hind, hsup, hN⟩ := hsum
    exact ⟨I, hZI, hind, hsup, fun i =>
      ⟨n, Or.inr (Or.inr (Or.inl ⟨hS, s16t3_sumOfNat_singleton (hZI i) (hN i)⟩))⟩⟩
  · obtain ⟨I, hZI, hind, hsup, hN⟩ := hsum
    exact ⟨I, hZI, hind, hsup, fun i =>
      ⟨n, Or.inr (Or.inr (Or.inr (Or.inl ⟨hS, s16t3_sumOfNat_singleton (hZI i) (hN i)⟩)))⟩⟩
  · obtain ⟨I, hZI, hind, hsup, hN⟩ := hsum
    exact ⟨I, hZI, hind, hsup, fun i =>
      ⟨n, Or.inr (Or.inr (Or.inr (Or.inr ⟨hS, s16t3_sumOfNat_singleton (hZI i) (hN i)⟩)))⟩⟩

theorem s16t3_isIrr_tilde_of_mem_irrSet (hq : CFSG.Open.IsQuasisimple ↥L)
    {I : Subgroup W} (hI : I ∈ irrSet L) :
    XMod.IsIrr ↥L (tilde L (⊤ : Subgroup W) I) := by
  exact (isIrr_tilde (V := W) (X := L) (W := (⊤ : Subgroup W))
    ((s16t3_mem_irrSet_iff' I).1 hI)).1

theorem s16t3_lift (hq : CFSG.Open.IsQuasisimple ↥L)
    {Y : Subgroup (W ⧸ modFix L (⊤ : Subgroup W))} (hY : XMod.IsIrr ↥L Y) :
    modComm L (Y.comap (QuotientGroup.mk' (modFix L (⊤ : Subgroup W)))) ∈ irrSet L ∧
      tilde L (⊤ : Subgroup W)
        (modComm L (Y.comap (QuotientGroup.mk' (modFix L (⊤ : Subgroup W))))) = Y := by
  letI := s16t3_qact W L
  have htop : tilde L (⊤ : Subgroup W) (⊤ : Subgroup W) = ⊤ :=
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  have hle : Y ≤ tilde L (⊤ : Subgroup W) (⊤ : Subgroup W) := by rw [htop]; exact le_top
  obtain ⟨hmem, htilde⟩ := lift_mem_irrPlus (V := W) (X := L) (W := (⊤ : Subgroup W)) hY
    (s16t3_commOf_eq_of_isIrr hq hY) hle
  exact ⟨(s16t3_mem_irrSet_iff' _).2 hmem, htilde⟩

private noncomputable def s16t3_irrSetEquiv (hq : CFSG.Open.IsQuasisimple ↥L) :
    ↥(irrSet L) ≃ {Y : Subgroup (W ⧸ modFix L (⊤ : Subgroup W)) // XMod.IsIrr ↥L Y} where
  toFun I := ⟨tilde L (⊤ : Subgroup W) I.1, s16t3_isIrr_tilde_of_mem_irrSet hq I.2⟩
  invFun Y := ⟨modComm L (Y.1.comap (QuotientGroup.mk' (modFix L (⊤ : Subgroup W)))),
    (s16t3_lift hq Y.2).1⟩
  left_inv I := by
    apply Subtype.ext
    dsimp only
    have hZ : modFix L (⊤ : Subgroup W) = fixV L := by
      rw [modFix, fixed_eq_inf_fixV, top_inf_eq]
    rw [comap_tilde]
    show XMod.commOf ↥L ((I : Subgroup W) ⊔ modFix L (⊤ : Subgroup W)) = (I : Subgroup W)
    rw [commOf_eq_commSub, commSub_sup_fixV (by rw [hZ])]
    exact (mem_irrPlus_top_iff.1 ((s16t3_mem_irrSet_iff' (I : Subgroup W)).1 I.2)).2.1
  right_inv Y := by
    apply Subtype.ext
    exact (s16t3_lift hq Y.2).2

theorem s16t3_card_irrSet_eq_quot (hq : CFSG.Open.IsQuasisimple ↥L) :
    Nat.card ↥(irrSet L) =
      Nat.card {Y : Subgroup (W ⧸ modFix L (⊤ : Subgroup W)) // XMod.IsIrr ↥L Y} :=
  Nat.card_congr (s16t3_irrSetEquiv hq)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
