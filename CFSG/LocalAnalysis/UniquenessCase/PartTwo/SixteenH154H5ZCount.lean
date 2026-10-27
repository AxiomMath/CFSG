module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ZWorld
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrCountCA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrCountCB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrCountCD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrCountCE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrCountCG
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrCountCJ

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.SmithD39Two CFSG.Open Subgroup
  CFSG.LocalAnalysis.UniquenessCase.UC22

variable {U : Type} [CommGroup U] [Finite U] {L : Subgroup (MulAut U)}

private theorem s16h_zcount_fixV_map_mk_eq_bot :
    (fixV L).map (QuotientGroup.mk' (modFix L (⊤ : Subgroup U))) = ⊥ := by
  have hZ : modFix L (⊤ : Subgroup U) = fixV L := by
    rw [modFix, fixed_eq_inf_fixV, top_inf_eq]
  rw [← hZ, QuotientGroup.map_mk'_self]

private theorem s16h_zcount_tilde_sup_fixV (J : Subgroup U) :
    tilde L (⊤ : Subgroup U) (J ⊔ fixV L) = tilde L (⊤ : Subgroup U) J := by
  unfold tilde
  rw [Subgroup.map_sup, s16h_zcount_fixV_map_mk_eq_bot, sup_bot_eq]

private theorem s16h_zcount_tilde_iSup {ι : Sort*} (J : ι → Subgroup U) :
    (⨆ i, tilde L (⊤ : Subgroup U) (J i)) = tilde L (⊤ : Subgroup U) (⨆ i, J i) := by
  unfold tilde
  rw [Subgroup.map_iSup]

private theorem s16h_zcount_shape_one (hsl3 : IsSLn ↥L 3 1) {I : Subgroup U}
    (hZI : fixV L ≤ I) (hnat : BinaryNaturalSL L I (fixV L) 3 1) :
    SumOfNatShape L I (fixV L) 1 := by
  refine ⟨3, Or.inl ⟨hsl3, ?_⟩⟩
  refine ⟨fun _ => I, fun _ => hZI, ?_, ?_, fun _ => hnat⟩
  · intro i
    have hbot : (⨆ (j : Fin 1) (_ : j ≠ i), I) = ⊥ := by
      apply iSup_eq_bot.mpr
      intro j
      apply iSup_eq_bot.mpr
      intro hj
      exact absurd (Subsingleton.elim j i) hj
    rw [hbot, sup_bot_eq]
    exact inf_le_right
  · rw [iSup_const, sup_eq_right.mpr hZI]

private theorem s16h_zcount_quot_summands (hq : CFSG.Open.IsQuasisimple ↥L) {k : ℕ}
    {I : Fin k → Subgroup U} (hZI : ∀ i, fixV L ≤ I i)
    (hind : ∀ i, I i ⊓ (fixV L ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j) ≤ fixV L)
    (hsup : fixV L ⊔ ⨆ i, I i = ⊤)
    (hnat : ∀ i, BinaryNaturalSL L (I i) (fixV L) 3 1) (hsl3 : IsSLn ↥L 3 1) :
    (∀ i, XMod.IsIrr ↥L (tilde L (⊤ : Subgroup U) (I i))) ∧
      iSupIndep (fun i => tilde L (⊤ : Subgroup U) (I i)) ∧
      (⨆ i, tilde L (⊤ : Subgroup U) (I i)) = ⊤ := by
  have hshape : ∀ i, SumOfNatShape L (I i) (fixV L) 1 :=
    fun i => s16h_zcount_shape_one hsl3 (hZI i) (hnat i)
  have hcomm : ∀ i, commSub (I i) L ∈ irrSet L :=
    fun i => (s16t3_commSub_mem_irrSet_of_natural (L := L) hq (hZI i) (hshape i)).1
  refine ⟨fun i => ?_, ?_, ?_⟩
  · have hIi : tilde L (⊤ : Subgroup U) (I i) =
        tilde L (⊤ : Subgroup U) (commSub (I i) L) := by
      conv_lhs => rw [← (s16t3_commSub_mem_irrSet_of_natural (L := L) hq (hZI i)
        (hshape i)).2.2]
      exact s16h_zcount_tilde_sup_fixV (commSub (I i) L)
    rw [hIi]
    exact s16t3_isIrr_tilde_of_mem_irrSet (L := L) hq (hcomm i)
  · rw [iSupIndep_def]
    intro i
    rw [disjoint_iff]
    rw [Subgroup.eq_bot_iff_forall]
    intro q hqmem
    obtain ⟨hqi, hqj⟩ := Subgroup.mem_inf.1 hqmem
    obtain ⟨a, ha, haq⟩ :=
      (mem_tilde_iff (X := L) (W := (⊤ : Subgroup U)) (I := I i)).1 hqi
    have h2 : (⨆ (j : Fin k) (_ : j ≠ i), tilde L (⊤ : Subgroup U) (I j)) =
        tilde L (⊤ : Subgroup U) (⨆ (j : Fin k) (_ : j ≠ i), I j) := by
      simp_rw [s16h_zcount_tilde_iSup]
    rw [h2] at hqj
    obtain ⟨b, hb, hbq⟩ :=
      (mem_tilde_iff (X := L) (W := (⊤ : Subgroup U))
        (I := ⨆ (j : Fin k) (_ : j ≠ i), I j)).1 hqj
    have hab : (QuotientGroup.mk a : U ⧸ modFix L (⊤ : Subgroup U)) =
        QuotientGroup.mk b := by
      rw [haq, hbq]
    have hZ : modFix L (⊤ : Subgroup U) = fixV L := by
      rw [modFix, fixed_eq_inf_fixV, top_inf_eq]
    have hz : a⁻¹ * b ∈ modFix L (⊤ : Subgroup U) := QuotientGroup.eq.1 hab
    have hzfix : a⁻¹ * b ∈ fixV L := by
      rwa [hZ] at hz
    have hain : a ∈ I i ⊓ (fixV L ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j) := by
      refine Subgroup.mem_inf.2 ⟨ha, ?_⟩
      rw [sup_comm]
      refine Subgroup.mem_sup.2 ⟨b, hb, (a⁻¹ * b)⁻¹, inv_mem hzfix, ?_⟩
      rw [mul_inv_rev, inv_inv]
      exact mul_inv_cancel_left b a
    have hfix : a ∈ fixV L := hind i hain
    rw [← haq]
    exact (QuotientGroup.eq_one_iff a).2 (by rwa [hZ])
  · have hgen : (⨆ i, tilde L (⊤ : Subgroup U) (I i)) =
        tilde L (⊤ : Subgroup U) (⨆ i, I i) := by
      simp_rw [s16h_zcount_tilde_iSup]
    rw [hgen]
    calc tilde L (⊤ : Subgroup U) (⨆ i, I i)
        = tilde L (⊤ : Subgroup U) (fixV L ⊔ ⨆ i, I i) := by
          rw [sup_comm, s16h_zcount_tilde_sup_fixV]
      _ = tilde L (⊤ : Subgroup U) (⊤ : Subgroup U) := by rw [hsup]
      _ = ⊤ := Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

private theorem s16h_zcount_two {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q]
    [MulDistribMulAction Γ Q] [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1)
    {Λ : Subgroup Γ} {S : Fin 2 → Subgroup Q} (hS : ∀ i, XMod.IsIrr ↥Λ (S i))
    (hind : iSupIndep S) (htop : (⨆ i, S i) = ⊤)
    (hlen : ∀ i, IsotypicOfLength ↥Λ (isoComp ↥Λ (S i)) (S i)
      (Nat.card {k : Fin 2 // XMod.Iso ↥Λ (S k) (S i)}))
    (hE : ∀ i, Nat.card (Module.End ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod (hS i).1)) = 2) :
    Nat.card {Y : Subgroup Q // XMod.IsIrr ↥Λ Y} ≤ 3 := by
  classical
  let c : Fin 2 → ℕ := fun i => Nat.card {k : Fin 2 // XMod.Iso ↥Λ (S k) (S i)}
  let n : Fin 2 → ℕ :=
    fun i => Nat.card {J : Subgroup Q // XMod.IsIrr ↥Λ J ∧ XMod.Iso ↥Λ J (S i)}
  have hn : ∀ i, n i = 2 ^ c i - 1 := fun i => s16t3_card_iso_type hQ (hS i) (hlen i) (hE i)
  have hex : ∀ Y : Subgroup Q, XMod.IsIrr ↥Λ Y → ∃ i, XMod.Iso ↥Λ Y (S i) := by
    intro Y hY
    exact CFSG.Quasithin.SmithD391.exists_iso_of_le_iSup (A := ↥Λ) (S := S) hS hY
      (by rw [htop]; exact le_top)
  by_cases hiso : XMod.Iso ↥Λ (S 1) (S 0)
  · have hc0 : c 0 = 2 := by
      rw [show c 0 = Nat.card {k : Fin 2 // XMod.Iso ↥Λ (S k) (S 0)} from rfl,
        Nat.card_eq_two_iff]
      refine ⟨⟨0, XMod.Iso.refl (S 0)⟩, ⟨1, hiso⟩, ?_, ?_⟩
      · simp
      · ext x
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
        rcases x with ⟨k, hk⟩
        fin_cases k
        · exact Or.inl (Subtype.ext rfl)
        · exact Or.inr (Subtype.ext rfl)
    have hn0 : n 0 = 3 := by rw [hn 0, hc0]; norm_num
    have hcover : ∀ Y : Subgroup Q, XMod.IsIrr ↥Λ Y → XMod.Iso ↥Λ Y (S 0) := by
      intro Y hY
      obtain ⟨i, hi⟩ := hex Y hY
      fin_cases i
      · exact hi
      · exact hi.trans hiso
    have hcard : Nat.card {Y : Subgroup Q // XMod.IsIrr ↥Λ Y} = n 0 := by
      change Nat.card {Y : Subgroup Q // XMod.IsIrr ↥Λ Y} =
        Nat.card {J : Subgroup Q // XMod.IsIrr ↥Λ J ∧ XMod.Iso ↥Λ J (S 0)}
      exact Nat.card_congr
        { toFun := fun Y => ⟨Y.1, Y.2, hcover Y.1 Y.2⟩
          invFun := fun J => ⟨J.1, J.2.1⟩
          left_inv := fun Y => Subtype.ext rfl
          right_inv := fun J => Subtype.ext rfl }
    rw [hcard, hn0]
  · have hiso' : ¬ XMod.Iso ↥Λ (S 0) (S 1) :=
      fun h => hiso (XMod.Iso.symm (hS 0).1 h)
    have hc0 : c 0 = 1 := by
      rw [show c 0 = Nat.card {k : Fin 2 // XMod.Iso ↥Λ (S k) (S 0)} from rfl,
        Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => ?_⟩, ⟨⟨0, XMod.Iso.refl (S 0)⟩⟩⟩
      have hval : ∀ x : {k : Fin 2 // XMod.Iso ↥Λ (S k) (S 0)}, (x : Fin 2) = 0 := by
        rintro ⟨k, hk⟩
        fin_cases k
        · rfl
        · exact absurd hk hiso
      exact Subtype.ext ((hval a).trans (hval b).symm)
    have hc1 : c 1 = 1 := by
      rw [show c 1 = Nat.card {k : Fin 2 // XMod.Iso ↥Λ (S k) (S 1)} from rfl,
        Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => ?_⟩, ⟨⟨1, XMod.Iso.refl (S 1)⟩⟩⟩
      have hval : ∀ x : {k : Fin 2 // XMod.Iso ↥Λ (S k) (S 1)}, (x : Fin 2) = 1 := by
        rintro ⟨k, hk⟩
        fin_cases k
        · exact absurd hk hiso'
        · rfl
      exact Subtype.ext ((hval a).trans (hval b).symm)
    have hn0 : n 0 = 1 := by rw [hn 0, hc0]; norm_num
    have hn1 : n 1 = 1 := by rw [hn 1, hc1]; norm_num
    have hcover : ∀ Y : Subgroup Q, XMod.IsIrr ↥Λ Y →
        XMod.Iso ↥Λ Y (S 0) ∨ XMod.Iso ↥Λ Y (S 1) := by
      intro Y hY
      obtain ⟨i, hi⟩ := hex Y hY
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr hi
    let A := {J : Subgroup Q // XMod.IsIrr ↥Λ J ∧ XMod.Iso ↥Λ J (S 0)}
    let B := {J : Subgroup Q // XMod.IsIrr ↥Λ J ∧ XMod.Iso ↥Λ J (S 1)}
    let f : {Y : Subgroup Q // XMod.IsIrr ↥Λ Y} → A ⊕ B := fun Y =>
      if h : XMod.Iso ↥Λ Y.1 (S 0) then Sum.inl ⟨Y.1, Y.2, h⟩
      else Sum.inr ⟨Y.1, Y.2, (hcover Y.1 Y.2).resolve_left h⟩
    have hf : Function.Injective f := by
      intro a b hab
      by_cases ha : XMod.Iso ↥Λ a.1 (S 0)
      · by_cases hb : XMod.Iso ↥Λ b.1 (S 0)
        · have hfa : f a = Sum.inl ⟨a.1, a.2, ha⟩ := dif_pos ha
          have hfb : f b = Sum.inl ⟨b.1, b.2, hb⟩ := dif_pos hb
          rw [hfa, hfb] at hab
          have hinner : (⟨a.1, a.2, ha⟩ : A) = ⟨b.1, b.2, hb⟩ := Sum.inl.inj hab
          exact Subtype.ext (congrArg (fun z : A => (z : Subgroup Q)) hinner)
        · have hfa : f a = Sum.inl ⟨a.1, a.2, ha⟩ := dif_pos ha
          have hfb : f b = Sum.inr ⟨b.1, b.2, (hcover b.1 b.2).resolve_left hb⟩ :=
            dif_neg hb
          rw [hfa, hfb] at hab
          exact absurd hab Sum.inl_ne_inr
      · by_cases hb : XMod.Iso ↥Λ b.1 (S 0)
        · have hfa : f a = Sum.inr ⟨a.1, a.2, (hcover a.1 a.2).resolve_left ha⟩ :=
            dif_neg ha
          have hfb : f b = Sum.inl ⟨b.1, b.2, hb⟩ := dif_pos hb
          rw [hfa, hfb] at hab
          exact absurd hab Sum.inr_ne_inl
        · have hfa : f a = Sum.inr ⟨a.1, a.2, (hcover a.1 a.2).resolve_left ha⟩ :=
            dif_neg ha
          have hfb : f b = Sum.inr ⟨b.1, b.2, (hcover b.1 b.2).resolve_left hb⟩ :=
            dif_neg hb
          rw [hfa, hfb] at hab
          have hinner : (⟨a.1, a.2, (hcover a.1 a.2).resolve_left ha⟩ : B) =
              ⟨b.1, b.2, (hcover b.1 b.2).resolve_left hb⟩ := Sum.inr.inj hab
          exact Subtype.ext (congrArg (fun z : B => (z : Subgroup Q)) hinner)
    calc Nat.card {Y : Subgroup Q // XMod.IsIrr ↥Λ Y}
        ≤ Nat.card (A ⊕ B) := Nat.card_le_card_of_injective f hf
      _ = n 0 + n 1 := by rw [Nat.card_sum]
      _ = 2 := by rw [hn0, hn1]
      _ ≤ 3 := by norm_num

theorem s16h_L3World_card_irr_le_three {U : Type} [CommGroup U] [Finite U]
    {N L : Subgroup (MulAut U)} (h : s16h_L3World N L) {k : ℕ} (hk : k ≤ 2)
    (hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1) L ⊤ (fixV L) k) :
    Nat.card ↥(irrSet L) ≤ 3 := by
  obtain ⟨I, hZI, hind, hsup, hnat⟩ := hsum
  have hq : CFSG.Open.IsQuasisimple ↥L := h.quasi
  rw [s16t3_card_irrSet_eq_quot hq]
  have hsummands := s16h_zcount_quot_summands hq hZI hind hsup hnat h.sl3
  obtain ⟨hS, hindS, htopS⟩ := hsummands
  interval_cases k
  · have hbot : (⊥ : Subgroup (U ⧸ modFix L (⊤ : Subgroup U))) = ⊤ := by
      simpa using htopS
    have hsub : Subsingleton
        {Y : Subgroup (U ⧸ modFix L (⊤ : Subgroup U)) // XMod.IsIrr ↥L Y} := by
      refine ⟨fun Y Z => ?_⟩
      exfalso
      have hle : Y.1 ≤ (⊥ : Subgroup (U ⧸ modFix L (⊤ : Subgroup U))) := by
        rw [hbot]; exact le_top
      have hYbot : Y.1 = ⊥ := le_bot_iff.mp hle
      exact (ne_of_gt Y.2.2.1) hYbot
    have hle : Nat.card
        {Y : Subgroup (U ⧸ modFix L (⊤ : Subgroup U)) // XMod.IsIrr ↥L Y} ≤ 1 :=
      Finite.card_le_one_iff_subsingleton.mpr hsub
    omega
  · have htop1 : tilde L (⊤ : Subgroup U) (I 0) = ⊤ := by
      simpa using htopS
    have hsub : Subsingleton
        {Y : Subgroup (U ⧸ modFix L (⊤ : Subgroup U)) // XMod.IsIrr ↥L Y} := by
      refine ⟨fun Y Z => ?_⟩
      have hY : Y.1 = tilde L (⊤ : Subgroup U) (I 0) := by
        have hYle : Y.1 ≤ tilde L (⊤ : Subgroup U) (I 0) := by
          rw [htop1]; exact le_top
        rcases (hS 0).2.2 Y.1 Y.2.1 bot_le hYle with hbot | htop
        · exact absurd hbot (ne_of_gt Y.2.2.1)
        · exact htop
      have hZ : Z.1 = tilde L (⊤ : Subgroup U) (I 0) := by
        have hZle : Z.1 ≤ tilde L (⊤ : Subgroup U) (I 0) := by
          rw [htop1]; exact le_top
        rcases (hS 0).2.2 Z.1 Z.2.1 bot_le hZle with hbot | htop
        · exact absurd hbot (ne_of_gt Z.2.2.1)
        · exact htop
      exact Subtype.ext (hY.trans hZ.symm)
    have hle : Nat.card
        {Y : Subgroup (U ⧸ modFix L (⊤ : Subgroup U)) // XMod.IsIrr ↥L Y} ≤ 1 :=
      Finite.card_le_one_iff_subsingleton.mpr hsub
    omega
  · have hQ : ∀ q : U ⧸ modFix L (⊤ : Subgroup U), q ^ 2 = 1 := by
      intro q
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
      rw [← QuotientGroup.mk_pow, pow_two, h.elem w, QuotientGroup.mk_one]
    have hS' : ∀ i : Fin 2, XMod.IsIrr ↥(⊤ : Subgroup ↥L)
        (tilde L (⊤ : Subgroup U) (I i)) :=
      fun i => (s16t3_isIrr_top_iff (A := ↥L) _).2 (hS i)
    have hres := s16h_zcount_two hQ hS' hindS htopS
      (fun i => s16t3_isotypicOfLength_isoComp hS' hindS htopS (hS' i))
      (fun i => s16t3_card_end_eq_two_of_endUnits (hS' i)
        (s16t3_endUnitsTrivial_tilde hq (s16h_zcount_shape_one h.sl3 (hZI i) (hnat i))))
    rw [← s16t3_card_irr_top (A := ↥L)]
    exact hres

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
