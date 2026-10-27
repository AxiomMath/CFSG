module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMK

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NGM.MF

open CFSG.QuasithinUnique.A6Facts Subgroup CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.WeakClosure81
open scoped Pointwise

set_option maxRecDepth 100000

variable {i : Fin 4}

structure XDesc (H : Subgroup ↥(GB i)) (L : List (List ℕ)) : Prop where
  mem : ∀ x, x ∈ H ↔ code x.1 ∈ L
  surj : ∀ c ∈ L, ∃ x ∈ H, code x.1 = c

theorem XDesc.card {H : Subgroup ↥(GB i)} {L : List (List ℕ)} (h : XDesc H L) (hnd : L.Nodup) :
    Nat.card H = L.length := by
  classical
  let f : H → L.toFinset := fun x => ⟨code x.1.1, List.mem_toFinset.2 ((h.mem x).1 x.2)⟩
  have hf : Function.Bijective f := by
    refine ⟨fun x y hxy => Subtype.ext (Subtype.ext (code_injective (congrArg Subtype.val hxy))),
      fun ⟨c, hc⟩ => ?_⟩
    obtain ⟨x, hx, rfl⟩ := h.surj c (List.mem_toFinset.1 hc)
    exact ⟨⟨x, hx⟩, rfl⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup hnd]

theorem xdesc_of_ldesc {H : Subgroup P16} {L : List (List ℕ)} (h : LDesc H L) (hH : H ≤ GB i) :
    XDesc (H.subgroupOf (GB i)) L :=
  ⟨fun x => h.mem x.1, fun c hc => by
    obtain ⟨σ, hσ, rfl⟩ := h.surj c hc
    exact ⟨⟨σ, hH hσ⟩, hσ, rfl⟩⟩

@[expose] def cBlk1Inv (c : List ℕ) : List ℕ :=
  (List.range 16).map fun k => if k < 8 then (cinv c).getD k 0 else k

@[expose] def T0Chk (tLit t0Gen t0Lit : List (List ℕ)) : Bool :=
  t0Lit.all tLit.contains && t0Lit.all cpresLo &&
  t0Gen.all (fun g => l1Lit.contains (cconj g (code a1)) && l1Lit.contains (cconj g (code b1))) &&
  t0Lit.all fun c => !(l1Lit.contains (cBlk1Inv c)) || t0Lit.contains (cBlk1Inv c)

structure T0Data (tLit t0Gen t0Lit : List (List ℕ)) : Prop where
  desc : LDesc (closureC t0Gen) t0Lit
  gen : ∀ c ∈ t0Gen, c ∈ t0Lit
  chk : T0Chk tLit t0Gen t0Lit = true

theorem code_eq_cBlk1Inv {σ τ : P16} (hσ : σ ∈ fixHiP)
    (hτ : ∀ k : Fin 16, k.val < 8 → (τ⁻¹ k).val < 8) (hστ : σ * τ ∈ fixLoP) :
    code σ = cBlk1Inv (code τ) := by
  apply List.ext_getElem
  · simp [code_length, cBlk1Inv]
  · intro j h1 h2
    have hj : j < 16 := by simpa [code_length] using h1
    rw [code_getElem]
    simp only [cBlk1Inv, List.getElem_map, List.getElem_range]
    split_ifs with h
    · rw [← code_inv, show (code τ⁻¹).getD j 0 = ((τ⁻¹ ⟨j, hj⟩ : Fin 16) : ℕ) from
        codeN_getD τ⁻¹ ⟨j, hj⟩]
      have := hστ (τ⁻¹ ⟨j, hj⟩) (hτ _ h)
      simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.Perm.coe_inv,
        Equiv.apply_symm_apply] at this
      rw [this]
      rfl
    · rw [hσ ⟨j, hj⟩ (by simp only; omega)]

section T0

variable {tLit t0Gen t0Lit : List (List ℕ)} (hT : LDesc (TB i) tLit) (h0 : T0Data tLit t0Gen t0Lit)
include h0

theorem t0chk_parts : (∀ c ∈ t0Lit, c ∈ tLit) ∧ (∀ c ∈ t0Lit, cpresLo c = true) ∧
    (∀ g ∈ t0Gen, cconj g (code a1) ∈ l1Lit ∧ cconj g (code b1) ∈ l1Lit) ∧
    (∀ c ∈ t0Lit, cBlk1Inv c ∈ l1Lit → cBlk1Inv c ∈ t0Lit) := by
  have h := h0.chk
  simp only [T0Chk, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, fun c hc hl => ?_⟩
  rcases h4 c hc with h5 | h5
  · rw [List.contains_iff_mem.2 hl] at h5
    exact absurd h5 (by decide)
  · exact h5

include hT in
theorem T0_le_TB : closureC t0Gen ≤ TB i := fun σ hσ =>
  (hT.mem σ).2 ((t0chk_parts h0).1 _ ((h0.desc.mem σ).1 hσ))

theorem T0_presLo {σ : P16} (hσ : σ ∈ closureC t0Gen) :
    ∀ k : Fin 16, k.val < 8 → (σ k).val < 8 :=
  cpresLo_iff.1 ((t0chk_parts h0).2.1 _ ((h0.desc.mem σ).1 hσ))

theorem T0_le_normL01 : closureC t0Gen ≤ normalizer ((L01 : Subgroup P16) : Set P16) := by
  apply closureC_le
  intro g hg
  apply mem_normalizer_of_map_le
  rw [L01, MonoidHom.map_closure, closure_le]
  rintro _ ⟨x, hx, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq] at hx
  obtain ⟨ha, hb⟩ := (t0chk_parts h0).2.2.1 _ hg
  rcases hx with rfl | rfl
  · rw [← code_conj] at ha
    exact (l1_desc.mem _).2 ha
  · rw [← code_conj] at hb
    exact (l1_desc.mem _).2 hb

abbrev R1x (i : Fin 4) (t0Gen : List (List ℕ)) : Subgroup ↥(GB i) := (closureC t0Gen ⊓ fixLoP).subgroupOf (GB i)

abbrev T0x (i : Fin 4) (t0Gen : List (List ℕ)) : Subgroup ↥(GB i) := (closureC t0Gen).subgroupOf (GB i)

theorem T0_le_normR1 : closureC t0Gen ≤ normalizer ((closureC t0Gen ⊓ fixLoP : Subgroup P16) :
    Set P16) := by
  intro t ht
  apply mem_normalizer_of_forall
  intro r hr
  obtain ⟨hr1, hrf⟩ := mem_inf.1 hr
  refine mem_inf.2 ⟨mul_mem (mul_mem ht hr1) (inv_mem ht), fun k hk => ?_⟩
  have h1 := T0_presLo h0 (inv_mem ht) k hk
  simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  rw [hrf _ h1]
  simp

omit h0 in
theorem L1b_le_normR1 : L1b i ≤ normalizer ((R1x i t0Gen : Subgroup ↥(GB i)) : Set ↥(GB i)) :=
  le_normalizer_of_commute fun _ hk _ hx =>
    Subtype.ext (commute_of_fixHiP_fixLoP (L01_le_fixHiP hk) hx.2)

theorem T0x_le_normR1 : T0x i t0Gen ≤ normalizer ((R1x i t0Gen : Subgroup ↥(GB i)) : Set ↥(GB i)) :=
  fun _ hx => mem_normalizer_subgroupOf (T0_le_normR1 h0 hx)

theorem T0x_le_normL1 : T0x i t0Gen ≤ normalizer ((L1b i : Subgroup ↥(GB i)) : Set ↥(GB i)) :=
  fun _ hx => mem_normalizer_subgroupOf (T0_le_normL01 h0 hx)

theorem cent_le_R1 : (L1b i ⊔ T0x i t0Gen) ⊓ centralizer ((L1b i : Subgroup ↥(GB i)) : Set ↥(GB i))
    ≤ R1x i t0Gen := by
  rintro x ⟨hxH, hxc⟩
  have hmem : x ∈ ((L1b i : Set ↥(GB i)) * (T0x i t0Gen : Set ↥(GB i))) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ (T0x_le_normL1 h0)]
    exact hxH
  obtain ⟨l, hl, t, ht, rfl⟩ := hmem
  have hcomm : ∀ y ∈ L01, (l * t : ↥(GB i)).1 * y = y * (l * t : ↥(GB i)).1 := by
    intro y hy
    have := mem_centralizer_iff.1 hxc ⟨y, L01_le_GB i hy⟩ hy
    exact (congrArg Subtype.val this).symm
  have hpres : ∀ k : Fin 16, k.val < 8 → ((l * t : ↥(GB i)).1 k).val < 8 := by
    intro k hk
    change ((l : P16) ((t : P16) k)).val < 8
    exact lt_of_mem_fixHiP (L01_le_fixHiP hl) (T0_presLo h0 ht k hk)
  have hfix := fixLo_of_commute hpres hcomm
  have hlc : code l.1 = cBlk1Inv (code t.1) :=
    code_eq_cBlk1Inv (L01_le_fixHiP hl) (T0_presLo h0 (inv_mem ht)) hfix
  have hlT : (l : P16) ∈ closureC t0Gen := by
    rw [h0.desc.mem, hlc]
    refine (t0chk_parts h0).2.2.2 _ ((h0.desc.mem _).1 ht) ?_
    rw [← hlc]
    exact (l1_desc.mem _).1 hl
  exact ⟨mul_mem hlT ht, hfix⟩

end T0

@[expose] def CentT0Chk (tLit t0Lit : List (List ℕ)) (u : List ℕ) : Bool :=
  tLit.all fun t => !(ccomm t u) || t0Lit.contains t

@[expose] def FiveChk (tLit t0Lit AL : List (List ℕ)) (u n c a b : List ℕ) : Bool :=
  AL.all t0Lit.contains && 2 * (AL.filter cfixLo).length == AL.length &&
  AL.contains u && CentT0Chk tLit t0Lit u &&
  l1Lit.contains n && l1Lit.contains c && AL.contains a && AL.contains b &&
  AL.all (fun x => tLit.contains (cconj (cinv c) x) && tLit.contains (cconj (cinv c) (cconj n x))) &&
  !(ccomm a (cconj n b))

section Five

variable {tLit t0Gen t0Lit : List (List ℕ)} (hT : LDesc (TB i) tLit) (h0 : T0Data tLit t0Gen t0Lit)
  (hTp : IsPGroup 2 (Tb i))
include hT h0 hTp

theorem fiveWit_of_chk {A : Subgroup ↥(GB i)} {AL : List (List ℕ)} (hA : XDesc A AL)
    (hnd : AL.Nodup) {u n c a b : List ℕ}
    (hchk : FiveChk tLit t0Lit AL u n c a b = true) :
    FiveWit (L1b i) (L2b i) (Tb i) A (L1b i ⊔ T0x i t0Gen) (R1x i t0Gen) (L1b i) := by
  simp only [FiveChk, CentT0Chk, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem,
    beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true'] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hAT0, hidx⟩, hu⟩, hcen⟩, hn⟩, hc⟩, ha⟩, hb⟩, hconj⟩, hab⟩ := hchk
  have hAT0' : A ≤ T0x i t0Gen := fun x hx => (h0.desc.mem x.1).2 (hAT0 _ ((hA.mem x).1 hx))
  have hR1T0 : R1x i t0Gen ≤ T0x i t0Gen := fun x hx => hx.1
  refine
    { le := hAT0'.trans le_sup_right
      R_le := hR1T0.trans le_sup_right
      R_norm := sup_le L1b_le_normR1 (T0x_le_normR1 h0)
      R_le_T := fun x hx => T0_le_TB hT h0 hx.1
      idx := ?_
      core := ?_
      Lh_le := le_sup_left
      Lh_norm := sup_le le_normalizer (T0x_le_normL1 h0)
      simple := isSimpleGroup_L1b i
      inter := ?_
      cent := cent_le_R1 h0
      good := ?_
      pair := ?_ }
  ·
    have hdesc : XDesc (R1x i t0Gen ⊓ A) (AL.filter cfixLo) := by
      refine ⟨fun x => ?_, fun d hd => ?_⟩
      · rw [mem_inf, List.mem_filter, ← hA.mem]
        constructor
        · rintro ⟨⟨-, hf⟩, hx⟩
          exact ⟨hx, cfixLo_iff.2 hf⟩
        · rintro ⟨hx, hf⟩
          exact ⟨⟨hAT0' hx, cfixLo_iff.1 hf⟩, hx⟩
      · rw [List.mem_filter] at hd
        obtain ⟨x, hx, rfl⟩ := hA.surj d hd.1
        exact ⟨x, ⟨⟨hAT0' hx, cfixLo_iff.1 hd.2⟩, hx⟩, rfl⟩
    have h1 := relIndex_mul_card (R1x i t0Gen) A
    rw [hdesc.card (hnd.filter _), hA.card hnd, ← hidx] at h1
    have hpos : 0 < (AL.filter cfixLo).length :=
      List.length_pos_of_mem (List.mem_filter.2 ⟨(hA.mem 1).1 (one_mem A), by
        rw [Subgroup.coe_one, code_one]; decide⟩)
    exact Nat.eq_of_mul_eq_mul_right hpos h1
  ·
    refine le_sup_of_le_right fun x hx => ?_
    have hxT : x ∈ Tb i := hx.1
    have hxc : code x.1 ∈ tLit := (mem_Tb_iff i hT x).1 hxT
    obtain ⟨uX, huA, huc⟩ := hA.surj u hu
    have hxu : x ∈ centralizer (A : Set ↥(GB i)) := by
      have := (coreIn_le_right _ _ hx).2
      exact this
    have h1 : ccomm (code x.1) u = true := by
      rw [← huc, ccomm_iff]
      have := mem_centralizer_iff.1 hxu uX huA
      exact (congrArg Subtype.val this).symm
    rcases hcen _ hxc with h2 | h2
    · rw [h1] at h2
      exact absurd h2 (by decide)
    · exact (h0.desc.mem _).2 h2
  ·
    rw [eq_bot_iff]
    rintro x ⟨hx1, -, hx2⟩
    rw [mem_bot]
    apply Subtype.ext
    have : (x : P16) ∈ fixHiP ⊓ fixLoP := ⟨L01_le_fixHiP hx1, hx2⟩
    rw [fixHiP_inf_fixLoP, mem_bot] at this
    exact this
  ·
    obtain ⟨y, hy, hy3⟩ := three_L i
    exact ⟨y, hy, hy3, Or.inl hy⟩
  ·
    obtain ⟨nX, hnL, hnc⟩ := exists_L1b i hn
    obtain ⟨cX, hcL, hcc⟩ := exists_L1b i hc
    obtain ⟨aX, haA, hac⟩ := hA.surj a ha
    obtain ⟨bX, hbA, hbc⟩ := hA.surj b hb
    refine ⟨nX, mem_sup_left hnL, ?_, aX, haA, bX, hbA, ?_⟩
    · refine (hTp.map (MulAut.conj cX).toMonoidHom).to_le (sup_le ?_ ?_)
      · intro x hx
        have h1 := (hconj _ ((hA.mem x).1 hx)).1
        rw [← hcc, ← code_inv, ← code_conj] at h1
        refine ⟨cX⁻¹ * x * cX, (mem_Tb_iff i hT _).2 ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
        simpa [Subgroup.coe_mul, Subgroup.coe_inv] using h1
      · rintro _ ⟨x, hx, rfl⟩
        have h1 := (hconj _ ((hA.mem x).1 hx)).2
        rw [← hnc, ← code_conj, ← hcc, ← code_inv, ← code_conj] at h1
        refine ⟨cX⁻¹ * (nX * x * nX⁻¹) * cX, (mem_Tb_iff i hT _).2 ?_,
          by simp [MulAut.conj_apply, mul_assoc]⟩
        simpa [Subgroup.coe_mul, Subgroup.coe_inv] using h1
    · intro he
      have h1 : ccomm (code aX.1) (cconj (code nX.1) (code bX.1)) = true := by
        rw [← code_conj, ccomm_iff]
        have := congrArg Subtype.val he
        simpa [Subgroup.coe_mul, Subgroup.coe_inv] using this
      rw [hac, hnc, hbc, hab] at h1
      exact Bool.noConfusion h1

end Five

end CFSG.LocalAnalysis.WeakClosure81.NGM.MF
