module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37.ModelChar

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37

open CFSG.KC.Misc.F7 CFSG.KC.Loop CFSG.RankThree.Native.ONTriple
open CFSG.CosetTable (genSub subsetOf)

attribute [local irreducible] dotProduct


@[expose] noncomputable def letG (s : ℕ) : GM := if s % 2 = 0 then (gMG (s / 2))⁻¹ else gMG (s / 2)

theorem coe_letG {s : ℕ} (hs : s < 16) : ((letG s : GM) : Mat45ˣ) = letU s := by
  have h8 : s / 2 < 8 := by omega
  rw [letG, letU, dif_pos h8]
  by_cases h : s % 2 = 0
  · rw [if_pos h, if_pos h, Subgroup.coe_inv, coe_gMG h8]
  · rw [if_neg h, if_neg h, coe_gMG h8]

theorem ptS_step {k : ℕ} (hk : k < nPt) (h0 : k ≠ 0) :
    ptS k = letG (rLet (ptRec k)) • ptS (rPar (ptRec k)) := by
  rw [smul_sub7, coe_letG (tree_step hk h0).2.1]
  exact (tree_step hk h0).2.2.2

theorem startOf_zero : startOf 0 = 0 := rfl

theorem exists_mH_smul : ∀ k < nPt, ∃ h ∈ mH, h • ptS (startOf k) = ptS k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases h0 : k = 0
    · subst h0
      exact ⟨1, mH.one_mem, by rw [startOf_zero, one_smul]⟩
    by_cases hroot : k = startOf k
    · exact ⟨1, mH.one_mem, by rw [← hroot, one_smul]⟩
    obtain ⟨hp, hs, hr, -⟩ := tree_step hk h0
    obtain ⟨hodd, h12, hge⟩ := hr hroot
    obtain ⟨h', hh', e'⟩ := ih _ hp (hp.trans hk)
    rw [startOf_of_le hge hp.le] at e'
    have hl : letG (rLet (ptRec k)) = gMG (rLet (ptRec k) / 2) := by
      rw [letG, if_neg (by omega)]
    refine ⟨letG (rLet (ptRec k)) * h', mH.mul_mem ?_ hh', ?_⟩
    · rw [hl]
      exact gMG_mem_mH (by omega)
    · rw [mul_smul, e', ← ptS_step hk h0]

theorem ptS_mem_orbit : ∀ k < nPt, ptS k ∈ MulAction.orbit GM W := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases h0 : k = 0
    · subst h0
      exact MulAction.mem_orbit_self _
    obtain ⟨hp, -, -, -⟩ := tree_step hk h0
    obtain ⟨g, hg⟩ := ih _ hp (hp.trans hk)
    have hg' : g • W = ptS (rPar (ptRec k)) := hg
    refine ⟨letG (rLet (ptRec k)) * g, ?_⟩
    change (letG (rLet (ptRec k)) * g) • W = ptS k
    rw [mul_smul, hg', ← ptS_step hk h0]

theorem gMG_eq_modelEquiv
    (x : Fin 8) :
    modelEquiv (PresentedGroup.of x) = gMG x.val := by
  apply Subtype.ext
  rw [modelEquiv_apply, psiM_of, coe_gMG x.isLt]

theorem card_mH_ge :
    3753792 ≤ Nat.card mH := by
  classical
  set G0 := genSub {r : FreeGroup (Fin 8) | r ∈ (coverRels 1 1 1).map FreeGroup.mk}
    (subsetOf 8 [0, 1, 2, 3, 4, 5]) with hG0
  obtain ⟨-, hidx⟩ := index_FHat_one_le
  have hmul := G0.card_mul_index
  have hFcard : Nat.card (FHat 1 1 1) = 1382446517760 := card_FHat_one
  rw [hFcard] at hmul
  rw [← hG0] at hidx
  have hG0card : 3753792 ≤ Nat.card G0 := by
    by_contra h
    have h' : Nat.card G0 ≤ 3753791 := by omega
    have := Nat.mul_le_mul h' hidx
    omega
  have hmap : G0.map modelEquiv.toMonoidHom ≤ mH := by
    rw [hG0, genSub, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have hx' : x.val < 6 := by
      simp only [Set.mem_ofPred_eq, subsetOf, List.mem_filter, List.mem_finRange, true_and,
        List.contains_eq_any_beq, List.any_eq_true, beq_iff_eq] at hx
      obtain ⟨y, hy, hxy⟩ := hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      omega
    rw [SetLike.mem_coe, MulEquiv.coe_toMonoidHom, gMG_eq_modelEquiv]
    exact gMG_mem_mH hx'
  have hmapcard : Nat.card (G0.map modelEquiv.toMonoidHom) = Nat.card G0 :=
    Subgroup.card_map_of_injective modelEquiv.injective
  exact hG0card.trans (hmapcard ▸ Subgroup.card_le_of_le hmap)

noncomputable abbrev pm1 : Subgroup (ZMod 7)ˣ := Subgroup.zpowers (-1)

theorem card_pm1 : Nat.card pm1 = 2 := by
  rw [Nat.card_zpowers]
  apply orderOf_eq_prime
  · decide
  · decide

theorem chiW_mH_mem {h : GM} (hh : h ∈ mH) : chiW ⟨h, mH_le_stab hh⟩ ∈ pm1 := by
  have hle : mH ≤ (pm1.comap chiW).map (MulAction.stabilizer GM W).subtype := by
    rw [Subgroup.closure_le]
    rintro _ ⟨l, rfl⟩
    refine ⟨⟨gMG l, gMG_mem_stab l.isLt⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    have e : chiW ⟨gMG l, gMG_mem_stab l.isLt⟩ = -1 := Units.ext (by
      rw [chiW_gMG l.isLt]
      rfl)
    rw [e]
    exact Subgroup.mem_zpowers _
  obtain ⟨s, hs, hse⟩ := hle hh
  have e : s = ⟨h, mH_le_stab hh⟩ := Subtype.ext hse
  rw [← e]
  exact hs

theorem units_seven_cases (u : (ZMod 7)ˣ) :
    ∃ a < 2, ∃ b < 3, (u : ZMod 7) = (-1) ^ a * 4 ^ b := by
  have hu : (u : ZMod 7) ≠ 0 := u.ne_zero
  generalize (u : ZMod 7) = x at hu
  revert x
  decide

theorem exists_chiW_eq {n : MulAction.stabilizer GM W}
    (hn : ((chiW n : (ZMod 7)ˣ) : ZMod 7) = -1) (u : (ZMod 7)ˣ) :
    ∃ a < 2, ∃ b < 3, chiW (n ^ a * ⟨zG, zG_mem_stab⟩ ^ b) = u := by
  obtain ⟨a, ha, b, hb, e⟩ := units_seven_cases u
  refine ⟨a, ha, b, hb, Units.ext ?_⟩
  rw [e, map_mul, map_pow, map_pow, Units.val_mul, Units.val_pow_eq_pow_val,
    Units.val_pow_eq_pow_val, hn, chiW_zG]

theorem card_range_chiW : Nat.card chiW.range = 6 := by
  have hn : ((chiW ⟨gMG 0, gMG_mem_stab (by norm_num)⟩ : (ZMod 7)ˣ) : ZMod 7) = -1 :=
    chiW_gMG (by norm_num)
  have htop : chiW.range = ⊤ := by
    rw [eq_top_iff]
    intro u _
    obtain ⟨a, -, b, -, e⟩ := exists_chiW_eq hn u
    exact ⟨_, e⟩
  rw [htop, Subgroup.card_top, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  rfl

theorem card_stab_ge :
    11261376 ≤ Nat.card (MulAction.stabilizer GM W) := by
  classical
  have hfin : Finite GM := Nat.finite_of_card_ne_zero (by rw [card_GM]; norm_num)
  set ψ : mH →* (ZMod 7)ˣ := chiW.comp (Subgroup.inclusion mH_le_stab) with hψ
  have hrange : Nat.card ψ.range ≤ 2 := by
    have : ψ.range ≤ pm1 := by
      rintro _ ⟨h, rfl⟩
      exact chiW_mH_mem h.2
    exact (Subgroup.card_le_of_le this).trans card_pm1.le
  have hH : Nat.card mH = Nat.card ψ.ker * Nat.card ψ.range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hS : Nat.card (MulAction.stabilizer GM W) = Nat.card chiW.ker * 6 := by
    rw [← card_range_chiW, ← Subgroup.index_ker, Subgroup.card_mul_index]
  have hker : Nat.card ψ.ker ≤ Nat.card chiW.ker := by
    have hinj : Function.Injective (fun x : ψ.ker =>
        (⟨Subgroup.inclusion mH_le_stab x.1, by
          have := x.2
          rw [MonoidHom.mem_ker] at this ⊢
          exact this⟩ : chiW.ker)) := by
      intro x y hxy
      apply Subtype.ext
      apply Subgroup.inclusion_injective mH_le_stab
      exact congrArg Subtype.val hxy
    exact Nat.card_le_card_of_injective _ hinj
  have hHge := card_mH_ge
  nlinarith

noncomputable abbrev XW : Set Sub7 := MulAction.orbit GM W

theorem finite_GM :
    Finite GM :=
  Nat.finite_of_card_ne_zero (by rw [card_GM]; norm_num)

theorem card_XW_le :
    Nat.card XW ≤ 122760 := by
  have := finite_GM
  have h1 := (MulAction.stabilizer GM W).card_mul_index
  rw [MulAction.index_stabilizer, card_GM] at h1
  have h2 := card_stab_ge
  change Nat.card (MulAction.orbit GM W) ≤ 122760
  rw [Nat.card_coe_set_eq]
  by_contra hc
  have h3 := Nat.mul_le_mul h2 (Nat.succ_le_of_lt (not_le.1 hc))
  omega

@[expose] noncomputable def ptX (k : Fin nPt) : XW := ⟨ptS k, ptS_mem_orbit k k.isLt⟩

theorem ptX_injective : Function.Injective ptX := fun i j e =>
  Fin.ext (ptS_inj i.isLt j.isLt (congrArg Subtype.val e))

theorem ptX_bijective :
    Function.Bijective ptX := by
  have := finite_GM
  have hfin : Finite XW := Set.finite_range _ |>.to_subtype
  refine ptX_injective.bijective_of_nat_card_le ?_
  rw [Nat.card_eq_fintype_card (α := Fin nPt), Fintype.card_fin]
  exact card_XW_le

theorem card_XW :
    Nat.card XW = 122760 := by
  rw [← Nat.card_congr (Equiv.ofBijective _ ptX_bijective), Nat.card_eq_fintype_card,
    Fintype.card_fin]
  rfl

theorem exists_ptS
    {q : Sub7} (hq : q ∈ XW) :
    ∃ k < nPt, ptS k = q := by
  obtain ⟨k, hk⟩ := ptX_bijective.2 ⟨q, hq⟩
  exact ⟨k, k.isLt, congrArg Subtype.val hk⟩

theorem card_stab_W :
    Nat.card (MulAction.stabilizer GM W) = 11261376 := by
  have h1 := (MulAction.stabilizer GM W).card_mul_index
  rw [MulAction.index_stabilizer, card_GM, ← Nat.card_coe_set_eq, card_XW] at h1
  exact Nat.eq_of_mul_eq_mul_right (show 0 < 122760 by norm_num) (h1.trans (by norm_num))

theorem exists_fix_chiW
    {q : Sub7} (hq : q ∈ XW)
    (u : (ZMod 7)ˣ) :
    ∃ s : MulAction.stabilizer GM W, (s : GM) • q = q ∧ chiW s = u := by
  obtain ⟨k, hk, rfl⟩ := exists_ptS hq
  obtain ⟨o, ho, hlo, hhi⟩ := exists_range hk
  obtain ⟨f1, f2, hl, hfix⟩ := orbFix_parts ho
  have hfk : fixP o < nPt := lt_of_lt_of_le f2 (orbStart_succ_le ho)
  have hsk := startOf_of_mem ho hlo hhi
  have hsf := startOf_of_mem ho f1 f2
  obtain ⟨h1, hh1, e1⟩ := exists_mH_smul k hk
  obtain ⟨h2, hh2, e2⟩ := exists_mH_smul _ hfk
  rw [hsk] at e1
  rw [hsf] at e2
  set c := h1 * h2⁻¹ with hc
  have hcm : c ∈ mH := mH.mul_mem hh1 (mH.inv_mem hh2)
  have hce : c • ptS (fixP o) = ptS k := by rw [hc, mul_smul, ← e2, inv_smul_smul, e1]
  set fS : MulAction.stabilizer GM W := ⟨gMG (fixL o), gMG_mem_stab hl⟩
  set cS : MulAction.stabilizer GM W := ⟨c, mH_le_stab hcm⟩
  set nS : MulAction.stabilizer GM W := cS * fS * cS⁻¹
  set zS : MulAction.stabilizer GM W := ⟨zG, zG_mem_stab⟩
  have hfS : (fS : GM) • ptS (fixP o) = ptS (fixP o) := by
    change gMG (fixL o) • _ = _
    rw [smul_sub7, coe_gMG (by omega)]
    exact hfix
  have hnS : ((nS : MulAction.stabilizer GM W) : GM) • ptS k = ptS k := by
    change (c * gMG (fixL o) * c⁻¹) • ptS k = ptS k
    rw [mul_smul, mul_smul, ← hce, inv_smul_smul]
    change c • ((fS : GM) • ptS (fixP o)) = _
    rw [hfS]
  have hn : ((chiW nS : (ZMod 7)ˣ) : ZMod 7) = -1 := by
    have e : chiW nS = chiW fS := by
      rw [map_mul, map_mul, map_inv, mul_comm (chiW cS) (chiW fS), mul_assoc, mul_inv_cancel,
        mul_one]
    rw [e]
    exact chiW_gMG hl
  obtain ⟨a, -, b, -, hab⟩ := exists_chiW_eq hn u
  refine ⟨nS ^ a * zS ^ b, ?_, hab⟩
  let T : Subgroup (MulAction.stabilizer GM W) :=
    (MulAction.stabilizer GM (ptS k)).comap (MulAction.stabilizer GM W).subtype
  have hnT : nS ∈ T := Subgroup.mem_comap.2 (MulAction.mem_stabilizer_iff.2 hnS)
  have hzT : zS ∈ T := Subgroup.mem_comap.2 (MulAction.mem_stabilizer_iff.2 (zG_smul _))
  exact MulAction.mem_stabilizer_iff.1
    (Subgroup.mem_comap.1 (T.mul_mem (T.pow_mem hnT a) (T.pow_mem hzT b)))

@[expose] def rangeSizes : Fin 5 → ℕ := ![1, 58653, 52136, 5586, 6384]

theorem rangeSizes_eq (o : Fin 5) : orbStart (o + 1) - orbStart o = rangeSizes o := by
  fin_cases o <;> rfl

set_option maxRecDepth 100000 in
theorem rangeSizes_blocks : ∀ S : Finset (Fin 5), (0 : Fin 5) ∈ S →
    (∑ o ∈ S, rangeSizes o) ∣ 122760 → S = {0} ∨ S = Finset.univ := by
  decide

theorem ptX_eq_smul {i j : Fin nPt} {g : GM} (h : g • ptS i = ptS j) : g • ptX i = ptX j :=
  Subtype.ext h

open scoped Pointwise in
theorem isBlock_W_cases
    {B : Set XW}
    (h0 : (⟨W, MulAction.mem_orbit_self W⟩ : XW) ∈ B) (hB : MulAction.IsBlock GM B) :
    B = {⟨W, MulAction.mem_orbit_self W⟩} ∨ B = Set.univ := by
  classical
  have := finite_GM
  set w0 : XW := ⟨W, MulAction.mem_orbit_self W⟩
  have hHB : ∀ h ∈ mH, ∀ x ∈ B, h • x ∈ B := by
    intro h hh x hx
    have hw : h • w0 = w0 := Subtype.ext (MulAction.mem_stabilizer_iff.1 (mH_le_stab hh))
    have hhB : h • B = B := hB.smul_eq_of_mem h0 (by rw [hw]; exact h0)
    rw [← hhB]
    exact Set.smul_mem_smul_set hx
  have hrange : ∀ i j : Fin nPt, rangeOf i = rangeOf j → ptX i ∈ B → ptX j ∈ B := by
    intro i j hij hi
    obtain ⟨hi1, hi2⟩ := rangeOf_mem i.isLt
    obtain ⟨hj1, hj2⟩ := rangeOf_mem j.isLt
    have hsi := startOf_of_mem (rangeOf i).isLt hi1 hi2
    have hsj := startOf_of_mem (rangeOf j).isLt hj1 hj2
    rw [hij] at hsi
    obtain ⟨a, ha, ea⟩ := exists_mH_smul i i.isLt
    obtain ⟨b, hb, eb⟩ := exists_mH_smul j j.isLt
    rw [hsi] at ea
    rw [hsj] at eb
    have e : ptX j = (b * a⁻¹) • ptX i :=
      (ptX_eq_smul (by rw [mul_smul, ← ea, inv_smul_smul, eb])).symm
    rw [e]
    exact hHB _ (mH.mul_mem hb (mH.inv_mem ha)) _ hi
  set S : Finset (Fin 5) := Finset.univ.filter fun o : Fin 5 =>
    ∃ k, ∃ hk : k < nPt, rangeOf k = o ∧ ptX ⟨k, hk⟩ ∈ B
  have hmemS : ∀ i : Fin nPt, ptX i ∈ B ↔ rangeOf i ∈ S := by
    intro i
    constructor
    · intro hi
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, i, i.isLt, rfl, hi⟩
    · intro hi
      obtain ⟨j, hj, hji, hjB⟩ := (Finset.mem_filter.1 hi).2
      exact hrange ⟨j, hj⟩ i hji hjB
  have h0S : (0 : Fin 5) ∈ S :=
    (hmemS ⟨0, by rw [nPt_eq]; norm_num⟩).1 h0
  have hcardB : Set.ncard B = ∑ o ∈ S, rangeSizes o := by
    have e1 : B = ptX '' {i : Fin nPt | rangeOf i ∈ S} := by
      ext x
      obtain ⟨i, rfl⟩ := ptX_bijective.2 x
      constructor
      · intro hx
        exact ⟨i, (hmemS i).1 hx, rfl⟩
      · rintro ⟨j, hj, hji⟩
        rw [← ptX_injective hji]
        exact (hmemS j).2 hj
    rw [e1, Set.ncard_image_of_injective _ ptX_injective]
    have e2 : Fin.val '' {i : Fin nPt | rangeOf i ∈ S} =
        ↑(S.biUnion fun o => Finset.Ico (orbStart o) (orbStart ((o : ℕ) + 1))) := by
      ext k
      simp only [Set.mem_image, Set.mem_setOf_eq, Finset.coe_biUnion, Finset.coe_Ico,
        Set.mem_iUnion, Set.mem_Ico, Finset.mem_coe, exists_prop]
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨rangeOf i, hi, rangeOf_mem i.isLt⟩
      · rintro ⟨o, ho, h1, h2⟩
        have hk : k < nPt := lt_of_lt_of_le h2 (orbStart_succ_le o.isLt)
        have hko : rangeOf k = o := Fin.ext (rangeOf_eq o.isLt h1 h2)
        refine ⟨⟨k, hk⟩, ?_, rfl⟩
        change rangeOf k ∈ S
        rw [hko]
        exact ho
    rw [← Set.ncard_image_of_injective _ Fin.val_injective, e2, Set.ncard_coe_finset,
      Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun o _ => ?_
      rw [Nat.card_Ico, rangeSizes_eq]
    · intro o _ o' _ hoo'
      change Disjoint (Finset.Ico _ _) (Finset.Ico _ _)
      rw [Finset.disjoint_left]
      intro k hk hk'
      rw [Finset.mem_Ico] at hk hk'
      exact hoo' (Fin.ext ((rangeOf_eq o.isLt hk.1 hk.2).symm.trans
        (rangeOf_eq o'.isLt hk'.1 hk'.2)))
  have hdvd : (∑ o ∈ S, rangeSizes o) ∣ 122760 := by
    rw [← hcardB, ← card_XW]
    exact hB.ncard_dvd_card ⟨w0, h0⟩
  have h0X : w0 = ptX ⟨0, by rw [nPt_eq]; norm_num⟩ := rfl
  rcases rangeSizes_blocks S h0S hdvd with hS | hS
  · left
    ext x
    obtain ⟨i, rfl⟩ := ptX_bijective.2 x
    rw [hmemS, hS, Finset.mem_singleton, Set.mem_singleton_iff, h0X]
    constructor
    · intro h
      have hi := (rangeOf_mem i.isLt).2
      rw [h, orbStart_eq] at hi
      have hi0 : i = ⟨0, by rw [nPt_eq]; norm_num⟩ := Fin.ext (by simpa using hi)
      rw [hi0]
    · intro h
      rw [ptX_injective h]
      rfl
  · right
    ext x
    obtain ⟨i, rfl⟩ := ptX_bijective.2 x
    rw [hmemS, hS]
    simp

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37
