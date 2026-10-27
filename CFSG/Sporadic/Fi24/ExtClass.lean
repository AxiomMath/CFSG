module

public import CFSG.Sporadic.Fi24.ExtGroup
public import CFSG.Sporadic.Fi24.ExtOrbitCert
public import CFSG.Blueprint.FischerDefs

public section

namespace CFSG.Sporadic.Fi24

open CFSG.F3.Native Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] noncomputable def tSub (S : Sub781) : Sub781 := ⟨S.sp.map (Matrix.mulVecLin mT)⟩

theorem tSub_sp (S : Sub781) : (tSub S).sp = S.sp.map (Matrix.mulVecLin mT) := rfl

theorem tSub_smul
    (g : J) (S : Sub781) : tSub (g • S) = tAut g • tSub S := by
  apply Sub781.ext'
  rw [tSub_sp, smul_sp, smul_sp, tSub_sp, ← Submodule.map_comp, ← Submodule.map_comp,
    ← Matrix.mulVecLin_mul, ← Matrix.mulVecLin_mul, mat_tAut, Matrix.mul_assoc (mT * mat g) mT mT,
    mT_mul_mT, Matrix.mul_one]

theorem tSub_tSub
    (S : Sub781) : tSub (tSub S) = S := by
  apply Sub781.ext'
  rw [tSub_sp, tSub_sp, ← Submodule.map_comp, ← Matrix.mulVecLin_mul, mT_mul_mT,
    Matrix.mulVecLin_one, Submodule.map_id]

theorem tSub_pt_zero :
    tSub (pt 0) = pt 0 := by
  apply Sub781.ext'
  rw [tSub_sp]
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    rw [Matrix.mulVecLin_apply, mT_mulVec_of_mem hv]
    exact (pt 0).sp.neg_mem hv
  · intro v hv
    refine ⟨-v, (pt 0).sp.neg_mem hv, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_neg, mT_mulVec_of_mem hv, neg_neg]

theorem tSub_mem_orbit
    {S : Sub781} (hS : S ∈ MulAction.orbit J (pt 0)) :
    tSub S ∈ MulAction.orbit J (pt 0) := by
  obtain ⟨g, rfl⟩ := hS
  exact ⟨tAut g, by
    show tAut g • pt 0 = tSub (g • pt 0)
    rw [tSub_smul, tSub_pt_zero]⟩

@[expose] noncomputable def tPt
    (k : Fin 306936) : Fin 306936 :=
  ptEquiv.symm ⟨tSub (ptEquiv k : Sub781), tSub_mem_orbit (ptEquiv k).2⟩

theorem pt_tPt
    (k : Fin 306936) : pt (tPt k).val = tSub (pt k.val) := by
  rw [← ptEquiv_apply, tPt, Equiv.apply_symm_apply]
  show tSub (ptEquiv k : Sub781) = tSub (pt k.val)
  rw [ptEquiv_apply]

theorem lt_nPts (k : Fin 306936) : k.val < nPts := by rw [nPts_eq]; exact k.isLt

theorem eq_of_pt_eq
    {k k' : Fin 306936} (h : pt k.val = pt k'.val) : k = k' :=
  Fin.ext (pt_inj (lt_nPts k) (lt_nPts k') h)

theorem tPt_tPt
    (k : Fin 306936) : tPt (tPt k) = k :=
  eq_of_pt_eq (by rw [pt_tPt, pt_tPt, tSub_tSub])

@[expose] noncomputable def tPerm :
    Equiv.Perm (Fin 306936) :=
  Function.Involutive.toPerm tPt tPt_tPt

theorem pt_tPerm
    (k : Fin 306936) : pt (tPerm k).val = tSub (pt k.val) := pt_tPt k

theorem tPerm_tPerm
    (k : Fin 306936) : tPerm (tPerm k) = k := tPt_tPt k

theorem tPerm_smul
    (g : J) (k : Fin 306936) : tPerm (g • k) = tAut g • tPerm k :=
  eq_of_pt_eq (by rw [pt_tPerm, pt_smul, pt_smul, tSub_smul, pt_tPerm])

theorem tPerm_root :
    tPerm root = root := eq_of_pt_eq (by rw [pt_tPerm]; exact tSub_pt_zero)

theorem tPerm_smul_root
    (g : J) : tPerm (g • root) = tAut g • root := by
  rw [tPerm_smul, tPerm_root]

theorem tPerm_smul_of_mem
    {h : J} (hh : h ∈ MulAction.stabilizer J root) (k : Fin 306936) :
    tPerm (h • k) = h • tPerm k := by
  rw [tPerm_smul, tAut_of_mem_stabilizer hh]

theorem jR_comm_tR
    {h : J} (hh : h ∈ MulAction.stabilizer J root) : jR h * tR = tR * jR h :=
  Subtype.ext ((mem_stabilizer_iff_commute h).1 hh)

@[expose] noncomputable def cls
    (k : Fin 306936) : R :=
  jR (Classical.choose (MulAction.exists_smul_eq J root k)) * tR *
    (jR (Classical.choose (MulAction.exists_smul_eq J root k)))⁻¹

theorem cls_smul_root
    (g : J) : cls (g • root) = jR g * tR * (jR g)⁻¹ := by
  have hg' := Classical.choose_spec (MulAction.exists_smul_eq J root (g • root))
  set g' := Classical.choose (MulAction.exists_smul_eq J root (g • root))
  have hh : g⁻¹ * g' ∈ MulAction.stabilizer J root := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, hg', inv_smul_smul]
  have hc := jR_comm_tR hh
  have e : jR g' = jR g * jR (g⁻¹ * g') := by rw [← map_mul, mul_inv_cancel_left]
  show jR g' * tR * (jR g')⁻¹ = _
  calc jR g' * tR * (jR g')⁻¹ =
        jR g * (jR (g⁻¹ * g') * tR) * (jR (g⁻¹ * g'))⁻¹ * (jR g)⁻¹ := by rw [e]; group
    _ = jR g * tR * (jR g)⁻¹ := by rw [hc]; group

theorem cls_root : cls root = tR := by
  have := cls_smul_root 1
  rwa [one_smul, map_one, one_mul, inv_one, mul_one] at this

theorem cls_smul
    (g : J) (k : Fin 306936) : cls (g • k) = jR g * cls k * (jR g)⁻¹ := by
  obtain ⟨g', rfl⟩ := MulAction.exists_smul_eq J root k
  rw [smul_smul, cls_smul_root, cls_smul_root, map_mul]
  group

theorem cls_injective :
    Function.Injective cls := by
  intro k k' h
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq J root k
  obtain ⟨g', rfl⟩ := MulAction.exists_smul_eq J root k'
  rw [cls_smul_root, cls_smul_root] at h
  have hc : jR (g⁻¹ * g') * tR = tR * jR (g⁻¹ * g') := by
    rw [map_mul, map_inv]
    calc (jR g)⁻¹ * jR g' * tR = (jR g)⁻¹ * (jR g' * tR * (jR g')⁻¹) * jR g' := by group
      _ = (jR g)⁻¹ * (jR g * tR * (jR g)⁻¹) * jR g' := by rw [h]
      _ = tR * ((jR g)⁻¹ * jR g') := by group
  have hc' := congrArg Subtype.val hc
  have hs : g⁻¹ * g' ∈ MulAction.stabilizer J root :=
    (mem_stabilizer_iff_commute (g⁻¹ * g')).2 hc'
  rw [MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff] at hs
  exact hs.symm

@[expose] def D24 :
    Set R := {x | IsConj tR x}

theorem cls_mem
    (k : Fin 306936) : cls k ∈ D24 := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq J root k
  rw [cls_smul_root]
  exact isConj_iff.2 ⟨jR g, rfl⟩

theorem exists_cls
    {x : R} (hx : x ∈ D24) : ∃ k, cls k = x := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hx
  obtain ⟨g, rfl | rfl⟩ := eq_jR_or c
  · exact ⟨g • root, cls_smul_root g⟩
  · refine ⟨g • root, ?_⟩
    rw [cls_smul_root]
    simp only [mul_inv_rev, tR_inv, mul_assoc, tR_mul_tR_mul]

theorem cls_eq_of_mk_eq
    {k k' : Fin 306936}
    (h : (⟨cls k, cls_mem k⟩ : D24) = ⟨cls k', cls_mem k'⟩) : k = k' := by
  have h' := congrArg Subtype.val h
  have h'' : cls k = cls k' := h'
  exact cls_injective h''

@[expose] noncomputable def clsEquiv :
    Fin 306936 ≃ D24 :=
  Equiv.ofBijective (fun k => ⟨cls k, cls_mem k⟩)
    ⟨fun _ _ h => cls_eq_of_mk_eq h, fun x =>
      ⟨(exists_cls x.2).choose, Subtype.ext (exists_cls x.2).choose_spec⟩⟩

theorem clsEquiv_apply
    (k : Fin 306936) : (clsEquiv k : R) = cls k := rfl

theorem clsEquiv_smul_root
    (g : J) : (clsEquiv (g • root) : R) = jR g * tR * (jR g)⁻¹ :=
  cls_smul_root g

theorem clsEquiv_smul
    (g : J) (k : Fin 306936) :
    (clsEquiv (g • k) : R) = jR g * clsEquiv k * (jR g)⁻¹ := cls_smul g k

theorem cls_tPerm
    (k : Fin 306936) : cls (tPerm k) = tR * cls k * tR := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq J root k
  rw [tPerm_smul_root, cls_smul_root, cls_smul_root, ← tR_mul_jR_mul_tR]
  simp only [mul_inv_rev, tR_inv, mul_assoc, tR_mul_tR_mul]

theorem clsEquiv_tPerm
    (k : Fin 306936) :
    (clsEquiv (tPerm k) : R) = tR * clsEquiv k * tR := cls_tPerm k

theorem cls_mul_cls
    (k : Fin 306936) : cls k * cls k = 1 := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq J root k
  rw [cls_smul_root]
  calc jR g * tR * (jR g)⁻¹ * (jR g * tR * (jR g)⁻¹) = jR g * (tR * tR) * (jR g)⁻¹ := by group
    _ = 1 := by rw [tR_mul_tR, mul_one, mul_inv_cancel]

theorem tR_mul_cls_smul
    {h : J} (hh : h ∈ MulAction.stabilizer J root) (k : Fin 306936) :
    tR * cls (h • k) = jR h * (tR * cls k) * (jR h)⁻¹ := by
  rw [cls_smul]
  calc tR * (jR h * cls k * (jR h)⁻¹) = (tR * jR h) * cls k * (jR h)⁻¹ := by group
    _ = jR h * (tR * cls k) * (jR h)⁻¹ := by rw [← jR_comm_tR hh]; group

theorem orderOf_conj' {G : Type*} [Group G] (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]

theorem orderOf_tR_mul_cls_smul
    {h : J} (hh : h ∈ MulAction.stabilizer J root)
    (k : Fin 306936) : orderOf (tR * cls (h • k)) = orderOf (tR * cls k) := by
  rw [tR_mul_cls_smul hh, orderOf_conj']

theorem val_tR_mul_cls (g : J) :
    (((tR * cls (g • root) : R) : GL (Fin 781) (ZMod 3)) : Matrix (Fin 781) (Fin 781) (ZMod 3)) =
      mT * (mat g * mT * mat g⁻¹) := by
  rw [cls_smul_root]
  rfl

theorem letterOK_P1 :
    LetterOK (mulW matTW (mulW (mulW matA matTW) matA)) (mT * (mA * mT * mA)) :=
  letterOK_matT.mulW ((letterOK_matA.mulW letterOK_matT).mulW letterOK_matA)

theorem letterOK_P2 :
    LetterOK (mulW matTW (mulW (mulW matB matTW) (mulW matB matB)))
    (mT * (mB * mT * (mB * mB))) :=
  letterOK_matT.mulW ((letterOK_matB.mulW letterOK_matT).mulW (letterOK_matB.mulW letterOK_matB))

theorem canonRows_P1 :
    canonRows 781 (mulW matTW (mulW (mulW matA matTW) matA)) = true :=
  canonRows_mulW baseFacts.T_canon (canonRows_mulW (canonRows_mulW baseFacts.A_canon
    baseFacts.T_canon) baseFacts.A_canon)

theorem canonRows_P2 :
    canonRows 781 (mulW matTW (mulW (mulW matB matTW) (mulW matB matB))) =
    true :=
  canonRows_mulW baseFacts.T_canon (canonRows_mulW (canonRows_mulW baseFacts.B_canon
    baseFacts.T_canon) (canonRows_mulW baseFacts.B_canon baseFacts.B_canon))

noncomputable abbrev p1 : Fin 306936 := a • root

noncomputable abbrev p2 : Fin 306936 := b • root

theorem val_tR_mul_cls_p1 :
    (((tR * cls p1 : R) : GL (Fin 781) (ZMod 3)) : Matrix (Fin 781) (Fin 781) (ZMod 3)) =
      mT * (mA * mT * mA) := by
  rw [val_tR_mul_cls, a_inv]; rfl

theorem val_tR_mul_cls_p2 :
    (((tR * cls p2 : R) : GL (Fin 781) (ZMod 3)) : Matrix (Fin 781) (Fin 781) (ZMod 3)) =
      mT * (mB * mT * (mB * mB)) := by
  rw [val_tR_mul_cls, mat_b_inv]; rfl

theorem R_ext {x y : R}
    (h : (((x : R) : GL (Fin 781) (ZMod 3)) : Matrix (Fin 781) (Fin 781) (ZMod 3)) =
      ((y : GL (Fin 781) (ZMod 3)) : Matrix (Fin 781) (Fin 781) (ZMod 3))) : x = y :=
  Subtype.ext (Units.ext h)

@[expose] noncomputable def valR :
    R →* Matrix (Fin 781) (Fin 781) (ZMod 3) :=
  (Units.coeHom _).comp R.subtype

theorem valR_apply (x : R) :
    valR x = (((x : R) : GL (Fin 781) (ZMod 3)) : Matrix (Fin 781) (Fin 781) (ZMod 3)) := rfl

theorem valR_injective :
    Function.Injective valR := fun x y h =>
  R_ext (by rw [← valR_apply, ← valR_apply]; exact h)

theorem orderOf_tR_mul_cls_p1 :
    orderOf (tR * cls p1) = 2 := by
  apply orderOf_eq_prime
  · apply valR_injective
    rw [map_pow, map_one, valR_apply, val_tR_mul_cls_p1, ← letterOK_P1.mat, pow_two,
      ← matW_mulW (m := 781) (by norm_num) letterOK_P1.wf letterOK_P1.wf
        (by rw [letterOK_P1.size]), (eq_of_eqRows normFacts.P1_sq).2, matW_idW (by norm_num)]
  · intro h
    apply matW_ne_of_eqRows canonRows_P1 normFacts.P1_ne
    rw [letterOK_P1.mat, ← val_tR_mul_cls_p1, h]
    rfl

theorem orderOf_tR_mul_cls_p2 :
    orderOf (tR * cls p2) = 3 := by
  apply orderOf_eq_prime
  · apply valR_injective
    rw [map_pow, map_one, valR_apply, val_tR_mul_cls_p2, ← letterOK_P2.mat, pow_three,
      ← matW_mulW (m := 781) (by norm_num) letterOK_P2.wf letterOK_P2.wf
        (by rw [letterOK_P2.size]),
      ← matW_mulW (m := 781) (by norm_num) letterOK_P2.wf (RowsWF.mulW letterOK_P2.wf
        letterOK_P2.wf) (by rw [mulW_size, letterOK_P2.size]),
      (eq_of_eqRows normFacts.P2_cube).2, matW_idW (by norm_num)]
  · intro h
    apply matW_ne_of_eqRows canonRows_P2 normFacts.P2_ne
    rw [letterOK_P2.mat, ← val_tR_mul_cls_p2, h]
    rfl

theorem eq_of_sq_cube {G : Type*} [Group G] {x : G} (h2 : x * x = 1) (h3 : x ^ 3 = 1) :
    x = 1 := by
  calc x = x ^ 3 * (x * x)⁻¹ := by group
    _ = 1 := by rw [h3, h2, inv_one, mul_one]

theorem tPerm_eq_self_iff_commute
    (k : Fin 306936) :
    tPerm k = k ↔ tR * cls k = cls k * tR := by
  rw [← cls_injective.eq_iff, cls_tPerm]
  constructor
  · intro h
    calc tR * cls k = tR * cls k * tR * tR := by rw [mul_assoc _ tR tR, tR_mul_tR, mul_one]
      _ = cls k * tR := by rw [h]
  · intro h
    rw [h, mul_assoc, tR_mul_tR, mul_one]

theorem tPerm_p1 : tPerm p1 = p1 := by
  rw [tPerm_eq_self_iff_commute]
  have h2 : (tR * cls p1) * (tR * cls p1) = 1 := by
    have := pow_orderOf_eq_one (tR * cls p1)
    rwa [orderOf_tR_mul_cls_p1, pow_two] at this
  calc tR * cls p1 = tR * ((tR * cls p1) * (tR * cls p1)) * cls p1 := by
        rw [h2, mul_one]
    _ = (tR * tR) * cls p1 * tR * (cls p1 * cls p1) := by group
    _ = cls p1 * tR := by rw [tR_mul_tR, cls_mul_cls, one_mul, mul_one]

theorem tPerm_p2 : tPerm p2 ≠ p2 := by
  rw [Ne, tPerm_eq_self_iff_commute]
  intro h
  have h3 : (tR * cls p2) ^ 3 = 1 := by
    have := pow_orderOf_eq_one (tR * cls p2)
    rwa [orderOf_tR_mul_cls_p2] at this
  have h2 : (tR * cls p2) * (tR * cls p2) = 1 := by
    calc (tR * cls p2) * (tR * cls p2) = tR * (cls p2 * tR) * cls p2 := by group
      _ = tR * (tR * cls p2) * cls p2 := by rw [h]
      _ = (tR * tR) * (cls p2 * cls p2) := by group
      _ = 1 := by rw [tR_mul_tR, cls_mul_cls, one_mul]
  have := eq_of_sq_cube (G := R) h2 h3
  have h1 := orderOf_tR_mul_cls_p2
  rw [this, orderOf_one] at h1
  exact absurd h1 (by norm_num)

theorem subLab_subRoot :
    subLab (⟨subRoot, by decide⟩ : Fin 306936) = 2 := by
  have hpos : 0 < (Finset.univ.filter (fun p : Fin 306936 => subLab p = 2)).card := by
    rw [card_subLab_two]; norm_num
  obtain ⟨q, hq⟩ := Finset.card_pos.1 hpos
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
  obtain ⟨⟨h, hh⟩, hhq⟩ := two_mem_orbit hq
  have := subLab_inv h hh ⟨subRoot, by decide⟩
  change subLab (h • _) = _ at this
  rw [show (h • (⟨subRoot, by decide⟩ : Fin 306936)) = q from hhq, hq] at this
  exact this.symm

theorem subLab_p1 :
    subLab p1 = 2 := subLab_a_root

theorem p1_ne_root : p1 ≠ root :=
  fun h => absurd (subLab_eq_zero.2 h) (by rw [subLab_p1]; decide)

theorem mem_stabilizer_of_lvl
    {h : J} (hh : h ∈ lvl 1) : h ∈ MulAction.stabilizer J root := by
  rw [stabilizer_root]; exact hh

theorem subLab_cases (k : Fin 306936) : subLab k = 0 ∨ subLab k = 1 ∨ subLab k = 2 := by
  rcases subLab k with ⟨_ | _ | _ | n, hn⟩
  · left; rfl
  · right; left; rfl
  · right; right; rfl
  · omega

theorem subLab_p2 :
    subLab p2 = 1 := by
  have h0 : p2 ≠ root := fun h => tPerm_p2 (by rw [h, tPerm_root])
  rcases subLab_cases p2 with h | h | h
  · exact absurd (subLab_eq_zero.1 h) h0
  · exact h
  · exfalso
    obtain ⟨g, hg, hgp⟩ := subLab_orb p1 p2 (subLab_p1.trans h.symm)
    apply tPerm_p2
    rw [← hgp, tPerm_smul_of_mem (mem_stabilizer_of_lvl hg), tPerm_p1]

theorem orderOf_tR_mul_cls
    (k : Fin 306936) :
    orderOf (tR * cls k) = if k = root then 1 else if subLab k = 2 then 2 else 3 := by
  by_cases h0 : k = root
  · rw [ite_eq_left h0, h0, cls_root, tR_mul_tR, orderOf_one]
  rw [ite_eq_right h0]
  by_cases h2 : subLab k = 2
  · rw [ite_eq_left h2]
    obtain ⟨g, hg, rfl⟩ := subLab_orb p1 k (subLab_p1.trans h2.symm)
    rw [orderOf_tR_mul_cls_smul (mem_stabilizer_of_lvl hg), orderOf_tR_mul_cls_p1]
  · rw [ite_eq_right h2]
    have h1 : subLab k = 1 := by
      rcases subLab_cases k with h | h | h
      · exact absurd (subLab_eq_zero.1 h) h0
      · exact h
      · exact absurd h h2
    obtain ⟨g, hg, rfl⟩ := subLab_orb p2 k (subLab_p2.trans h1.symm)
    rw [orderOf_tR_mul_cls_smul (mem_stabilizer_of_lvl hg), orderOf_tR_mul_cls_p2]

theorem tPerm_eq_self_iff
    (k : Fin 306936) : tPerm k = k ↔ k = root ∨ subLab k = 2 := by
  constructor
  · intro h
    by_contra hc
    rw [not_or] at hc
    have h1 : subLab k = 1 := by
      rcases subLab_cases k with h' | h' | h'
      · exact absurd (subLab_eq_zero.1 h') hc.1
      · exact h'
      · exact absurd h' hc.2
    obtain ⟨g, hg, hgk⟩ := subLab_orb k p2 (h1.trans subLab_p2.symm)
    apply tPerm_p2
    rw [← hgk, tPerm_smul_of_mem (mem_stabilizer_of_lvl hg), h]
  · rintro (rfl | h2)
    · exact tPerm_root
    · obtain ⟨g, hg, rfl⟩ := subLab_orb p1 k (subLab_p1.trans h2.symm)
      rw [tPerm_smul_of_mem (mem_stabilizer_of_lvl hg), tPerm_p1]

theorem card_fixed_tPerm :
    (Finset.univ.filter fun k : Fin 306936 => tPerm k = k).card = 31672 := by
  have e : (Finset.univ.filter fun k : Fin 306936 => tPerm k = k) =
      (Finset.univ.filter fun k => subLab k = 0) ∪ (Finset.univ.filter fun k => subLab k = 2) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, tPerm_eq_self_iff,
      subLab_eq_zero]
  have hd : Disjoint (Finset.univ.filter fun k : Fin 306936 => subLab k = 0)
      (Finset.univ.filter fun k => subLab k = 2) :=
    Finset.disjoint_filter.2 fun k _ h0 h2 => by rw [h0] at h2; exact absurd h2 (by decide)
  rw [e, Finset.card_union_of_disjoint hd, card_subLab_zero, card_subLab_two]

theorem card_moved_tPerm :
    (Finset.univ.filter fun k : Fin 306936 => tPerm k ≠ k).card = 275264 := by
  have e : (Finset.univ.filter fun k : Fin 306936 => tPerm k ≠ k) =
      Finset.univ.filter fun k => subLab k = 1 := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, tPerm_eq_self_iff,
      subLab_eq_zero.symm, not_or]
    rcases subLab_cases k with h | h | h <;> simp [h]
  rw [e, card_subLab_one]

theorem orderOf_mem_D24
    {x : R} (hx : x ∈ D24) : orderOf x = 2 := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hx
  rw [orderOf_conj', orderOf_tR]

theorem orderOf_mul_mem_D24
    {x y : R} (hx : x ∈ D24) (hy : y ∈ D24) :
    orderOf (x * y) = 1 ∨ orderOf (x * y) = 2 ∨ orderOf (x * y) = 3 := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hx
  have hy' : c⁻¹ * y * c⁻¹⁻¹ ∈ D24 :=
    (show IsConj tR y from hy).trans (isConj_iff.2 ⟨c⁻¹, rfl⟩)
  obtain ⟨k, hk⟩ := exists_cls hy'
  have e : c * tR * c⁻¹ * y = c * (tR * cls k) * c⁻¹ := by rw [hk]; group
  rw [e, orderOf_conj', orderOf_tR_mul_cls]
  split_ifs <;> simp

theorem conj_mem_closure_D24
    {x : R} (hx : x ∈ Subgroup.closure D24) (g : R) :
    g * x * g⁻¹ ∈ Subgroup.closure D24 := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    exact Subgroup.subset_closure ((show IsConj tR y from hy).trans (isConj_iff.2 ⟨g, rfl⟩))
  | one => rw [mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
  | mul y z _ _ hy hz =>
    have e : g * (y * z) * g⁻¹ = (g * y * g⁻¹) * (g * z * g⁻¹) := by group
    rw [e]; exact Subgroup.mul_mem _ hy hz
  | inv y _ hy =>
    have e : g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ := by group
    rw [e]; exact Subgroup.inv_mem _ hy

theorem tR_mul_cls_p1_eq :
    tR * cls p1 = jR (tAut a * a⁻¹) := by
  rw [cls_smul_root, map_mul, map_inv, ← tR_mul_jR_mul_tR]
  group

theorem closure_D24 :
    Subgroup.closure D24 = ⊤ := by
  have := isSimpleGroup_J
  have hN : (Subgroup.comap jR (Subgroup.closure D24)).Normal := ⟨fun n hn g => by
    show jR (g * n * g⁻¹) ∈ Subgroup.closure D24
    rw [map_mul, map_mul, map_inv]
    exact conj_mem_closure_D24 (Subgroup.mem_comap.mp hn) (jR g)⟩
  have hmem : tAut a * a⁻¹ ∈ Subgroup.comap jR (Subgroup.closure D24) := by
    show jR (tAut a * a⁻¹) ∈ Subgroup.closure D24
    rw [← tR_mul_cls_p1_eq]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (IsConj.refl tR))
      (Subgroup.subset_closure (cls_mem p1))
  have hne : Subgroup.comap jR (Subgroup.closure D24) ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.mem_bot] at hmem
    have h2 := orderOf_tR_mul_cls_p1
    rw [tR_mul_cls_p1_eq, hmem, map_one, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have htop := (IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (Subgroup.comap jR (Subgroup.closure D24))).resolve_left hne
  rw [eq_top_iff]
  intro x _
  have hg : ∀ g : J, jR g ∈ Subgroup.closure D24 := fun g => by
    have : g ∈ Subgroup.comap jR (Subgroup.closure D24) := by rw [htop]; trivial
    exact this
  obtain ⟨g, rfl | rfl⟩ := eq_jR_or x
  · exact hg g
  · exact Subgroup.mul_mem _ (hg g) (Subgroup.subset_closure (IsConj.refl tR))

theorem pair_R :
    CFSG.Blueprint.Fischer.Pair R D24 :=
  ⟨inferInstance, ⟨tR, rfl⟩, fun _ he => orderOf_mem_D24 he,
    fun _ he _ hf => by rcases orderOf_mul_mem_D24 he hf with h | h | h <;> simp [h],
    closure_D24⟩

theorem card_D24 :
    Nat.card D24 = 306936 := by
  rw [← Nat.card_congr clsEquiv, Nat.card_eq_fintype_card, Fintype.card_fin]


theorem cls_ne_tR_iff
    (k : Fin 306936) : cls k ≠ tR ↔ k ≠ root := by
  rw [← cls_root, Ne, Ne, cls_injective.eq_iff]

theorem mem_localClass_iff
    (k : Fin 306936) :
    cls k ∈ CFSG.Blueprint.Fischer.LocalClass D24 tR ↔ subLab k = 2 := by
  unfold CFSG.Blueprint.Fischer.LocalClass
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨-, hne, hc⟩
    have := (tPerm_eq_self_iff k).1 ((tPerm_eq_self_iff_commute k).2 hc.symm)
    exact this.resolve_left ((cls_ne_tR_iff k).1 hne)
  · intro h2
    refine ⟨cls_mem k, (cls_ne_tR_iff k).2 fun h => ?_, ?_⟩
    · rw [h, subLab_eq_zero.2 rfl] at h2
      exact absurd h2 (by decide)
    · exact ((tPerm_eq_self_iff_commute k).1 ((tPerm_eq_self_iff k).2 (Or.inr h2))).symm

theorem card_localClass :

    Nat.card (CFSG.Blueprint.Fischer.LocalClass D24 tR) = 31671 := by
  have e : CFSG.Blueprint.Fischer.LocalClass D24 tR = cls '' {k | subLab k = 2} := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, rfl⟩ := exists_cls hx.1
      exact ⟨k, (mem_localClass_iff k).1 hx, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact (mem_localClass_iff k).2 hk
  rw [e, Nat.card_image_of_injective cls_injective, ← card_subLab_two,
    ← Fintype.card_subtype, Nat.card_eq_fintype_card]
  exact Fintype.card_congr (Equiv.refl _)

end CFSG.Sporadic.Fi24
