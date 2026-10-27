
module

public import CFSG.Monster.B.TwoA.Base.FrameBase

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.Visible
  CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.VisCert

theorem pairVec_eq_zero {x y m : Fin 24} (hx : m ≠ x) (hy : m ≠ y) (b : ZMod 2) :
    pairVec x y b m = 0 := by
  rw [pairVec_apply, ite_eq_right hx, ite_eq_right hy]
  ring

theorem hInt_pairVec_disjoint {x y k l : Fin 24} (hxk : x ≠ k) (hxl : x ≠ l) (hyk : y ≠ k)
    (hyl : y ≠ l) (b c : ZMod 2) : hInt (pairVec x y b) (pairVec k l c) = 0 := by
  rw [hInt, Finset.sum_eq_zero, Int.zero_ediv]
  intro m _
  by_cases hmx : m = x
  · subst hmx
    rw [pairVec_eq_zero hxk hxl, mul_zero]
  · by_cases hmy : m = y
    · subst hmy
      rw [pairVec_eq_zero hyk hyl, mul_zero]
    · rw [pairVec_eq_zero hmx hmy, zero_mul]

theorem bL_pairCls_disjoint {x y k l : Fin 24} (hxy : x ≠ y) (hkl : k ≠ l) (hxk : x ≠ k)
    (hxl : x ≠ l) (hyk : y ≠ k) (hyl : y ≠ l) (b c : ZMod 2) :
    bL (pairCls x y b) (pairCls k l c) = 0 := by
  rw [pairCls, pairCls, Griess.classOf_eq_cls (pairVec_mem hxy b).1,
    Griess.classOf_eq_cls (pairVec_mem hkl c).1, bL_apply]
  change QuadraticMap.polarBilin qL _ _ = 0
  rw [bL_cls, hInt_pairVec_disjoint hxk hxl hyk hyl]
  rfl

theorem pairCls_add_pairCls_not_short {x y k l : Fin 24} (hxy : x ≠ y) (hkl : k ≠ l) (hxk : x ≠ k)
    (hxl : x ≠ l) (hyk : y ≠ k) (hyl : y ≠ l) (b c : ZMod 2) :
    pairCls x y b + pairCls k l c ∉ shortSet := by
  have hu := pairVec_mem hxy b
  have hv := pairVec_mem hkl c
  set u : codeLatticeSubgroup allOnes_mem_C := ⟨pairVec x y b, hu.1⟩
  set v : codeLatticeSubgroup allOnes_mem_C := ⟨pairVec k l c, hv.1⟩
  have huu : Griess.hL u u = 4 := Griess.hL_eq_four_of_mem_minVecs hu
  have hvv : Griess.hL v v = 4 := Griess.hL_eq_four_of_mem_minVecs hv
  have huv : Griess.hL u v = 0 := hInt_pairVec_disjoint hxk hxl hyk hyl b c
  have hne : u ≠ v := fun h => by rw [h, hvv] at huv; norm_num at huv
  have hne' : u ≠ -v := fun h => by
    rw [h, map_neg, AddMonoidHom.neg_apply, hvv] at huv; norm_num at huv
  obtain ⟨-, hiff, -, -⟩ := rootless_short_sums Griess.hL Griess.hL_symm Griess.hL_min huu hvv
    hne hne'
  rintro ⟨w, hw, hwcl⟩
  have hnot : ¬(Griess.hL u v = 2 ∨ Griess.hL u v = -2) := by rw [huv]; norm_num
  apply hnot
  apply hiff.1
  rw [pairCls, pairCls, ← Griess.classOf_add_of_mem hu.1 hv.1, classOf_of_mem hw.1,
    classOf_of_mem (add_mem_codeLattice allOnes_mem_C hu.1 hv.1), Submodule.Quotient.eq,
    mem_two_range_iff] at hwcl
  obtain ⟨t, ht⟩ := hwcl
  refine ⟨⟨w, hw.1⟩, -t, ?_, Griess.hL_eq_four_of_mem_minVecs hw⟩
  apply Subtype.ext
  have ht' : (2 : ℤ) • (t : Fin 24 → ℤ) = w - (pairVec x y b + pairVec k l c) := ht
  change pairVec x y b + pairVec k l c = w + (2 : ℕ) • (-(t : Fin 24 → ℤ))
  rw [two_nsmul, ← two_smul ℤ, smul_neg, ht']
  abel

theorem pairCls_mem_vPerpL
    {x y : Fin 24} (hxy : x ≠ y) (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (hy0 : y ≠ 0) (hy1 : y ≠ 1) (b : ZMod 2) : pairCls x y b ∈ vPerpL v0 := by
  change bL v0 (pairCls x y b) = 0
  rw [v0_eq_pairCls]
  exact bL_pairCls_disjoint (by decide) hxy (Ne.symm hx0) (Ne.symm hy0) (Ne.symm hx1)
    (Ne.symm hy1) 0 b

structure OffPair (x y : Fin 24) : Prop where
  ne : x ≠ y
  x0 : x ≠ 0
  x1 : x ≠ 1
  y0 : y ≠ 0
  y1 : y ≠ 1

theorem OffPair.symm {x y : Fin 24} (h : OffPair x y) : OffPair y x :=
  ⟨h.ne.symm, h.y0, h.y1, h.x0, h.x1⟩

@[expose] def pairW
    (x y : Fin 24) (h : OffPair x y) (b : ZMod 2) : Wv v0 :=
  Submodule.Quotient.mk ⟨pairCls x y b, pairCls_mem_vPerpL h.ne h.x0 h.x1 h.y0 h.y1 b⟩

theorem pairW_comm
    {x y : Fin 24} (h : OffPair x y) (b : ZMod 2) :
    pairW y x h.symm b = pairW x y h b :=
  congrArg Submodule.Quotient.mk (Subtype.ext (pairCls_comm h.ne b))

theorem pairW_one
    {x y : Fin 24} (h : OffPair x y) : pairW x y h 1 = pairW x y h 0 + wFr := by
  rw [pairW, pairW, wFr, ← Submodule.Quotient.mk_add]
  congr 1
  apply Subtype.ext
  change pairCls x y 1 = pairCls x y 0 + twoΩCls
  rw [add_comm, twoΩCls_add_pairCls h.ne]
  rfl

theorem pairW_add_one
    {x y : Fin 24} (h : OffPair x y) (b : ZMod 2) :
    pairW x y h (b + 1) = pairW x y h b + wFr := by
  rcases (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) b with rfl | rfl
  · rw [zero_add, pairW_one]
  · rw [show (1 : ZMod 2) + 1 = 0 by decide, pairW_one, add_assoc, ← two_smul (ZMod 2) wFr,
      show (2 : ZMod 2) = 0 by decide, zero_smul, add_zero]

theorem pairW_ne_zero
    {x y : Fin 24} (h : OffPair x y) (b : ZMod 2) : pairW x y h b ≠ 0 := by
  rw [pairW, Ne, mk_eq_zero_iff]
  rintro (h0 | h0)
  · exact VisCert.zero_notMem_shortSet (h0 ▸ pairCls_mem_shortSet h.ne b)
  · have := (pairCls_eq_iff h.ne (by decide : (0 : Fin 24) ≠ 1) b 0).1 (h0.trans v0_eq_pairCls)
    rcases this.1 with ⟨hx, -⟩ | ⟨hx, -⟩
    · exact h.x0 hx
    · exact h.x1 hx

theorem pairW_eq_iff
    {x y k l : Fin 24} (h : OffPair x y) (h' : OffPair k l) (b c : ZMod 2) :
    pairW x y h b = pairW k l h' c ↔ ((x = k ∧ y = l) ∨ (x = l ∧ y = k)) ∧ b = c := by
  rw [← pairCls_eq_iff h.ne h'.ne]
  constructor
  · intro he
    rw [pairW, pairW, Submodule.Quotient.eq] at he
    have he' : pairCls x y b - pairCls k l c ∈ vLineL v0 := he
    rcases mem_vLineL.1 he' with h0 | h0
    · exact sub_eq_zero.1 h0
    · exfalso
      have e : pairCls x y b = pairCls k l c + pairCls 0 1 0 := by
        rw [← v0_eq_pairCls, ← h0, add_sub_cancel]
      exact pairCls_add_pairCls_not_short h'.ne (by decide) h'.x0 h'.x1 h'.y0 h'.y1 c 0
        (e ▸ pairCls_mem_shortSet h.ne b)
  · intro he
    exact congrArg Submodule.Quotient.mk (Subtype.ext he)

theorem pairW_ne_wFr
    {x y : Fin 24} (h : OffPair x y) (b : ZMod 2) : pairW x y h b ≠ wFr := by
  rw [pairW, wFr, Ne, Submodule.Quotient.eq]
  intro he
  have he' : pairCls x y b - twoΩCls ∈ vLineL v0 := he
  rcases mem_vLineL.1 he' with h0 | h0
  · exact twoΩCls_not_short (sub_eq_zero.1 h0 ▸ pairCls_mem_shortSet h.ne b)
  ·
    have e : pairCls x y b = pairCls 0 1 1 := by
      rw [← twoΩCls_add_v0, ← h0, add_sub_cancel]
    have := (pairCls_eq_iff h.ne (by decide : (0 : Fin 24) ≠ 1) b 1).1 e
    rcases this.1 with ⟨hx, -⟩ | ⟨hx, -⟩
    · exact h.x0 hx
    · exact h.x1 hx

theorem OffPair.perm {x y : Fin 24} (h : OffPair x y) {p : AutPerm} (hp : p ∈ Ppair) :
    OffPair ((p : Equiv.Perm (Fin 24)) x) ((p : Equiv.Perm (Fin 24)) y) :=
  ⟨(p : Equiv.Perm (Fin 24)).injective.ne h.ne, (Ppair_apply_ne hp h.x0 h.x1).1,
    (Ppair_apply_ne hp h.x0 h.x1).2, (Ppair_apply_ne hp h.y0 h.y1).1,
    (Ppair_apply_ne hp h.y0 h.y1).2⟩

theorem wAct_monomial_pairW
    {a : C} {p : AutPerm} (hk : (QuotientGroup.mk (gO a * PO p) : OLq) ∈
    Kstab v0) {x y : Fin 24} (h : OffPair x y) (b : ZMod 2) :
    wAct v0 ⟨_, hk⟩ (pairW x y h b) =
      pairW _ _ (h.perm ((mk_mem_Kstab_iff_monomial a p).1 hk).1)
        (b + (a : Fin 24 → ZMod 2) x + (a : Fin 24 → ZMod 2) y) := by
  rw [pairW, wAct_mk, pairW]
  congr 2
  change kOp (QuotientGroup.mk (gO a * PO p)) (pairCls x y b) = _
  rw [kOp_mk, modTwoEnd_gO_mul_PO_pairCls a p h.ne]

theorem wFr_eq_decW :
    wFr = decW 31 := by
  obtain ⟨hm, he⟩ := decW_eq_mk 31
  rw [he, wFr]
  congr 1
  apply Subtype.ext
  change twoΩCls = dec (Native.actD 22 Native.quotientBasis 31)
  rw [show Native.actD 22 Native.quotientBasis 31 = 63 by decide, dec_seed]

@[expose] def pairN (x y : ℕ) (i : ℕ) : ℤ := if i = x then 4 else if i = y then -4 else 0

theorem cls_pairN_eq {x y : Fin 24} (hxy : x ≠ y)
    (h : (fun i : Fin 24 => pairN x y i) = pairVec x y 0) {r : ℕ}
    (hr : rowCheck (pairN x y) r = true) : pairCls x y 0 = dec r := by
  have hmem : (fun i : Fin 24 => pairN x y i) ∈ codeLattice C := h ▸ (pairVec_mem hxy 0).1
  rw [← cls_eq_dec_of_rowCheck hmem hr, pairCls, Griess.classOf_eq_cls (pairVec_mem hxy 0).1]
  exact cls_congr _ h.symm

theorem pairN_eq (x y : Fin 24) (hxy : x ≠ y) :
    (fun i : Fin 24 => pairN x y i) = pairVec x y 0 := by
  funext i
  rw [pairN, pairVec_apply, sgnI_zero]
  by_cases hx : i = x
  · subst hx
    simp [hxy]
  · have hx' : (i : ℕ) ≠ x := fun h => hx (Fin.ext h)
    by_cases hy : i = y
    · subst hy
      simp [hx, hx']
    · have hy' : (i : ℕ) ≠ y := fun h => hy (Fin.ext h)
      simp [hx, hy, hx', hy']

theorem pairW_eq_decW
    {x y : Fin 24} (h : OffPair x y) {r c : ℕ}
    (hr : rowCheck (pairN x y) r = true) (hc : Native.actD 22 Native.quotientBasis c = r) :
    pairW x y h 0 = decW c := by
  obtain ⟨hm, he⟩ := decW_eq_mk c
  rw [he, pairW]
  congr 1
  apply Subtype.ext
  change pairCls x y 0 = dec (Native.actD 22 Native.quotientBasis c)
  rw [hc]
  exact cls_pairN_eq h.ne (pairN_eq x y h.ne) hr

theorem offPair23 : OffPair 2 3 := ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem offPair45 : OffPair 4 5 := ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem offPair89 : OffPair 8 9 := ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem pairW23_eq_decW :
    pairW 2 3 offPair23 0 = decW 12288 :=
  pairW_eq_decW offPair23 (r := 49152) (by decide +kernel) (by decide)

theorem pairW45_eq_decW :
    pairW 4 5 offPair45 0 = decW 49152 :=
  pairW_eq_decW offPair45 (r := 196608) (by decide +kernel) (by decide)

theorem pairW89_eq_decW :
    pairW 8 9 offPair89 0 = decW 393216 :=
  pairW_eq_decW offPair89 (r := 1572864) (by decide +kernel) (by decide)

end CFSG.Monster.B.TwoA
