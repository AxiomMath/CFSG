module

public import CFSG.Sporadic.Fi22.Transpositions
public import CFSG.Sporadic.Fi22.CentCert
public import CFSG.Fischer.T46
public import CFSG.Perm.ChainSift
import all CFSG.Fischer.F4
public import CFSG.Blueprint.FischerDefs
public import CFSG.Fischer.T46UnitaryBase

public section

namespace CFSG.Sporadic.Fi22

open CFSG.F3.Native Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
  CFSG.F4.Native CFSG.Blueprint.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
attribute [local irreducible] CFSG.F4.Native.uPts phiData phiPos

theorem centCert_parts :
    (eaPts orb).size = 693 ∧ phiData.size = 693 ∧
    (∀ i < 693, phiData[i]! < 693 ∧ phiPos[phiData[i]!]! = i) ∧
    (∀ l ∈ lv1, (∀ i < 693, (ePos (eaPts orb))[ap (chainLetters orb)[l]! (eaPts orb)[i]!]! < 693) ∧
      sift t46Trees t46Letters t46Base t46Q 0
        (rrImg (eaPts orb) (ePos (eaPts orb)) (chainLetters orb)[l]!) = true) ∧
    (∀ s < 6, CFSG.KS.Fi22Cent.GSK s < 693 ∧ ∀ j < 693,
      uPts[phiData[(ePos (eaPts orb))[cPt orb (eaPts orb)[CFSG.KS.Fi22Cent.GSK s]!
        (eaPts orb)[j]!]!]!]! =
        normC (tvC uPts[phiData[CFSG.KS.Fi22Cent.GSK s]!]! uPts[phiData[j]!]!)) ∧
    (CFSG.KS.Fi22Cent.ORK 0 = CFSG.KS.Fi22Cent.GSK 0 ∧
      (∀ t, 1 ≤ t → t < 693 → CFSG.KS.Fi22Cent.TPK t < t ∧ CFSG.KS.Fi22Cent.TGK t < 6 ∧
        CFSG.KS.Fi22Cent.ORK t = (ePos (eaPts orb))[cPt orb
          (eaPts orb)[CFSG.KS.Fi22Cent.GSK (CFSG.KS.Fi22Cent.TGK t)]!
          (eaPts orb)[CFSG.KS.Fi22Cent.ORK (CFSG.KS.Fi22Cent.TPK t)]!]!) ∧
      ∀ i < 693, CFSG.KS.Fi22Cent.OIK i < 693 ∧ CFSG.KS.Fi22Cent.ORK (CFSG.KS.Fi22Cent.OIK i) = i) ∧
    (∀ k ∈ aWord, k ∈ eaPts orb) ∧
    (∀ q ∈ chainQ, iterN (ap (wordTab orb (genTables orb (-2)) aWord)) 9 q = ap orb.alpha q) ∧
    (∀ k ∈ aWord2, k ∈ eaPts orb) ∧
    (∀ q ∈ chainQ, iterN (ap (wordTab orb (genTables orb (-2)) aWord2)) 11 q = ap orb.alpha q) := by
  have h : centChecksK orb = true := cent_certificate
  unfold centChecksK centGenOK centTreeOK cPowOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true', allIn_eq_true,
    List.all_eq_true, Array.contains_iff_mem, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, ⟨⟨h6a, h6b⟩, h6c⟩⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  refine ⟨h1, h2, fun i hi => ?_, fun l hl => ?_, fun s hs => ?_, ⟨h6a, fun t ht1 ht2 => ?_,
    fun i hi => ?_⟩, h7, h8, h9, h10⟩
  · exact h3 i (Nat.zero_le _) hi
  · obtain ⟨ha, hb⟩ := h4 l hl
    exact ⟨fun i hi => ha i (Nat.zero_le _) hi, hb⟩
  · obtain ⟨ha, hb⟩ := h5 s (Nat.zero_le _) hs
    exact ⟨ha, fun j hj => hb j (Nat.zero_le _) hj⟩
  · obtain ⟨⟨ha, hb⟩, hc⟩ := h6b t ht1 ht2
    exact ⟨ha, hb, hc⟩
  · exact h6c i (Nat.zero_le _) hi

noncomputable abbrev ea : Array ℕ := eaPts orb

theorem mem_ea {k : ℕ} : k ∈ ea ↔ k < 3510 ∧ k ≠ 0 ∧ ap orb.alpha k = k := by
  unfold ea eaPts
  rw [List.mem_toArray, List.mem_filter, List.mem_range]
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]

theorem ea_size : ea.size = 693 := centCert_parts.1

theorem ea_nodup : ea.toList.Nodup := by
  unfold ea eaPts
  rw [List.toList_toArray]
  exact List.nodup_range.filter _

theorem ea_get_mem {i : ℕ} (hi : i < 693) : ea[i]! ∈ ea := by
  rw [getElem!_pos ea i (by rw [ea_size]; exact hi)]
  exact Array.getElem_mem _

theorem ea_get_lt
    {i : ℕ} (hi : i < 693) : ea[i]! < 3510 := (mem_ea.1 (ea_get_mem hi)).1

theorem ePos_get {k : ℕ} (hk : k < 3510) : (ePos ea)[k]! = ea.toList.idxOf k := by
  unfold ePos
  rw [getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem ePos_ea {i : ℕ} (hi : i < 693) : (ePos ea)[ea[i]!]! = i := by
  rw [ePos_get (ea_get_lt hi), getElem!_pos ea i (by rw [ea_size]; exact hi),
    ← Array.getElem_toList]
  exact List.get_idxOf ea_nodup ⟨i, by rw [Array.length_toList, ea_size]; exact hi⟩

theorem ePos_lt_iff
    {k : ℕ} (hk : k < 3510) : (ePos ea)[k]! < 693 ↔ k ∈ ea := by
  rw [ePos_get hk, ← ea_size, ← Array.length_toList, List.idxOf_lt_length_iff,
    Array.mem_toList_iff]

theorem ea_ePos {k : ℕ} (hk : k ∈ ea) : ea[(ePos ea)[k]!]! = k := by
  have hlt := (ePos_lt_iff (mem_ea.1 hk).1).2 hk
  rw [getElem!_pos ea _ (by rw [ea_size]; exact hlt), ← Array.getElem_toList]
  simp only [ePos_get (mem_ea.1 hk).1]
  exact List.getElem_idxOf _

noncomputable abbrev star : Set J := LocalClass D a

theorem conjPt_mem_star {k : ℕ} (hk : k ∈ ea) : conjPt k ∈ star := by
  obtain ⟨hk1, hk0, hka⟩ := mem_ea.1 hk
  have hk1' : k < orb.keys.size := by rw [orb_size]; exact hk1
  refine ⟨mem_D_iff.2 ⟨k, hk1, rfl⟩, fun h => hk0 ?_, ?_⟩
  · rw [← conjPt_zero] at h
    exact conjPt_inj hk1' (by rw [orb_size]; norm_num) h
  · have h := conj_a_conjPt hk1'
    rw [hka, mul_inv_eq_iff_eq_mul] at h
    exact h.symm

theorem mem_ea_of_mem_star
    {x : J} (hx : x ∈ star) : ∃ k ∈ ea, x = conjPt k := by
  obtain ⟨hxD, hxa, hxc⟩ := hx
  obtain ⟨k, hk, rfl⟩ := mem_D_iff.1 hxD
  have hk' : k < orb.keys.size := by rw [orb_size]; exact hk
  refine ⟨k, mem_ea.2 ⟨hk, fun h0 => hxa (by rw [h0, conjPt_zero]), ?_⟩, rfl⟩
  have h := conj_a_conjPt hk'
  rw [← hxc, mul_assoc, mul_inv_cancel, mul_one] at h
  have hlt : ap orb.alpha k < orb.keys.size := (conjFacts.alpha k hk').1
  exact (conjPt_inj hlt hk' h.symm)

noncomputable def posFun
    (i : Fin 693) : star :=
  ⟨conjPt ea[i.val]!, conjPt_mem_star (ea_get_mem i.2)⟩

theorem posFun_bijective :
    Function.Bijective posFun := by
  constructor
  · intro i j h
    have h' := congrArg Subtype.val h
    have hi := ea_get_lt i.2
    have hj := ea_get_lt j.2
    have := conjPt_inj (by rw [orb_size]; exact hi) (by rw [orb_size]; exact hj) h'
    apply Fin.ext
    rw [← ePos_ea i.2, ← ePos_ea j.2, this]
  · rintro ⟨x, hx⟩
    obtain ⟨k, hk, rfl⟩ := mem_ea_of_mem_star hx
    refine ⟨⟨(ePos ea)[k]!, (ePos_lt_iff (mem_ea.1 hk).1).2 hk⟩, ?_⟩
    apply Subtype.ext
    show conjPt ea[(ePos ea)[k]!]! = conjPt k
    rw [ea_ePos hk]

noncomputable def posEquiv :
    Fin 693 ≃ star := Equiv.ofBijective posFun posFun_bijective

theorem posEquiv_apply
    (i : Fin 693) : (posEquiv i : J) = conjPt ea[i.val]! := by
  simp only [posEquiv, posFun, Equiv.ofBijective_apply]

noncomputable def phiFun (i : Fin 693) : Fin 693 :=
  ⟨phiData[i.val]!, (centCert_parts.2.2.1 i.val i.2).1⟩

theorem phiFun_injective : Function.Injective phiFun := by
  intro i j h
  apply Fin.ext
  rw [← (centCert_parts.2.2.1 i.val i.2).2, ← (centCert_parts.2.2.1 j.val j.2).2]
  exact congrArg (fun u => phiPos[u]!) (congrArg Fin.val h)

noncomputable def phiEquiv : Fin 693 ≃ Fin 693 :=
  Equiv.ofBijective phiFun (Finite.injective_iff_bijective.1 phiFun_injective)

theorem phiEquiv_apply
    (i : Fin 693) : (phiEquiv i).val = phiData[i.val]! := by
  simp only [phiEquiv, phiFun, Equiv.ofBijective_apply]

theorem phiEquiv_symm_val
    (u : Fin 693) : (phiEquiv.symm u).val = phiPos[u.val]! := by
  obtain ⟨i, rfl⟩ := phiEquiv.surjective u
  rw [Equiv.symm_apply_apply, phiEquiv_apply, (centCert_parts.2.2.1 i.val i.2).2]

noncomputable def ptE :
    Fin 693 ≃ star := phiEquiv.symm.trans posEquiv

theorem ptE_apply
    (u : Fin 693) : (ptE u : J) = conjPt ea[phiPos[u.val]!]! := by
  rw [ptE, Equiv.trans_apply, posEquiv_apply, phiEquiv_symm_val]

noncomputable abbrev Ca : Subgroup J := Subgroup.centralizer {a}

theorem mem_Ca
    {g : J} : g ∈ Ca ↔ g * a = a * g := Subgroup.mem_centralizer_singleton_iff

theorem conj_mem_star
    {g : J} (hg : g ∈ Ca) {x : J} (hx : x ∈ star) : g * x * g⁻¹ ∈ star := by
  obtain ⟨hxD, hxa, hxc⟩ := hx
  have hga := mem_Ca.1 hg
  have hgag : g * a * g⁻¹ = a := by rw [hga, mul_assoc, mul_inv_cancel, mul_one]
  refine ⟨(hxD : IsConj a x).trans (isConj_iff.2 ⟨g, rfl⟩), fun h => hxa ?_, ?_⟩
  · have : x = g⁻¹ * a * g := by rw [← h]; group
    rw [this, mul_assoc, ← hga, ← mul_assoc, inv_mul_cancel, one_mul]
  · calc g * x * g⁻¹ * a = g * x * (g⁻¹ * a * g) * g⁻¹ := by group
      _ = g * x * a * g⁻¹ := by
          rw [show g⁻¹ * a * g = a by rw [mul_assoc, ← hga, ← mul_assoc, inv_mul_cancel, one_mul]]
      _ = g * a * x * g⁻¹ := by rw [mul_assoc g x a, hxc, ← mul_assoc]
      _ = a * (g * x * g⁻¹) := by rw [hga]; group

noncomputable instance starAction : MulAction Ca star where
  smul g x := ⟨(g : J) * x * (g : J)⁻¹, conj_mem_star g.2 x.2⟩
  one_smul x := Subtype.ext (show ((1 : Ca) : J) * (x : J) * ((1 : Ca) : J)⁻¹ = x by simp)
  mul_smul g h x := Subtype.ext (show ((g * h : Ca) : J) * (x : J) * ((g * h : Ca) : J)⁻¹ =
      (g : J) * ((h : J) * x * (h : J)⁻¹) * (g : J)⁻¹ by
    rw [Subgroup.coe_mul, mul_inv_rev]; group)

theorem starAction_val
    (g : Ca) (x : star) : ((g • x : star) : J) = (g : J) * x * (g : J)⁻¹ :=
  rfl

noncomputable instance ptAction :
    MulAction Ca (Fin 693) := Equiv.mulAction Ca ptE

noncomputable abbrev rho :
    Ca →* Equiv.Perm (Fin 693) := MulAction.toPermHom Ca (Fin 693)

theorem rho_apply
    (g : Ca) (u : Fin 693) : rho g u = ptE.symm (g • ptE u) := rfl

theorem ptE_symm_posEquiv
    (j : Fin 693) : ptE.symm (posEquiv j) = phiEquiv j := by
  rw [Equiv.symm_apply_eq, ptE, Equiv.trans_apply, Equiv.symm_apply_apply]

theorem rho_val
    (g : Ca) {L : Table} (hL : Rep 3510 L (g : J))
    (hcl : ∀ i < 693, (ePos ea)[ap L ea[i]!]! < 693) (u : Fin 693) :
    (rho g u).val = (rrImg ea (ePos ea) L)[u.val]! := by
  have hi : phiPos[u.val]! < 693 := by rw [← phiEquiv_symm_val]; exact (phiEquiv.symm u).2
  set k := ea[phiPos[u.val]!]! with hk
  have hk3 : k < 3510 := ea_get_lt hi
  have hk' : ap L k < 3510 := by rw [hL k hk3]; exact idx_lt _ hk3
  have hmem : ap L k ∈ ea := (ePos_lt_iff hk').1 (hcl _ hi)
  have hj := (ePos_lt_iff hk').2 hmem
  have hconj : (g : J) * conjPt k * (g : J)⁻¹ = conjPt (ap L k) := by
    rw [hL k hk3]
    exact ((idx_eq_iff hk3 (idx_lt _ hk3)).1 rfl)
  have hstar : g • ptE u = posEquiv ⟨(ePos ea)[ap L k]!, hj⟩ := by
    apply Subtype.ext
    rw [starAction_val, ptE_apply, posEquiv_apply, ← hk, hconj, ea_ePos hmem]
  rw [rho_apply, hstar, ptE_symm_posEquiv, phiEquiv_apply]
  unfold rrImg
  rw [getElem!_pos _ u.val (by simp), Array.getElem_ofFn]

theorem closed_of_rep
    (g : Ca) {L : Table} (hL : Rep 3510 L (g : J)) :
    ∀ i < 693, (ePos ea)[ap L ea[i]!]! < 693 := by
  intro i hi
  have hk3 := ea_get_lt hi
  have hk' : ap L ea[i]! < 3510 := by rw [hL _ hk3]; exact idx_lt _ hk3
  have hconj : (g : J) * conjPt ea[i]! * (g : J)⁻¹ = conjPt (ap L ea[i]!) := by
    rw [hL _ hk3]
    exact ((idx_eq_iff hk3 (idx_lt _ hk3)).1 rfl)
  have hmem := conj_mem_star g.2 (conjPt_mem_star (ea_get_mem hi))
  rw [hconj] at hmem
  obtain ⟨k, hk, hkeq⟩ := mem_ea_of_mem_star hmem
  have := conjPt_inj (by rw [orb_size]; exact hk') (by rw [orb_size]; exact (mem_ea.1 hk).1) hkeq
  rw [this]
  exact (ePos_lt_iff (mem_ea.1 hk).1).2 hk

theorem rho_val'
    (g : Ca) {L : Table} (hL : Rep 3510 L (g : J)) (u : Fin 693) :
    (rho g u).val = (rrImg ea (ePos ea) L)[u.val]! :=
  rho_val g hL (closed_of_rep g hL) u

theorem Ca_eq_lvl : Ca = lvl 1 := by
  rw [← stabilizer_root]
  ext g
  rw [mem_Ca, MulAction.mem_stabilizer_iff, smul_eq_iff]
  show g * a = a * g ↔ g * conjPt 0 * g⁻¹ = conjPt 0
  rw [conjPt_zero, mul_inv_eq_iff_eq_mul]

theorem rho_mem_T46_of_table
    (g : Ca) {L : Table} (hL : Rep 3510 L (g : J))
    (hs : sift t46Trees t46Letters t46Base t46Q 0 (rrImg ea (ePos ea) L) = true) :
    rho g ∈ CFSG.Fischer.T46 := by
  refine chain_sift_mem CFSG.Fischer.rep_t46Letters CFSG.Fischer.t46_sep
    CFSG.Fischer.localCert_parts.2.1 (by unfold rrImg t46Q; simp) (fun t ht => ?_) hs
  have ht' : t < 693 := by unfold t46Q at ht; simpa using ht
  rw [CFSG.Fischer.t46Q_get ht', idx_of_lt _ ht']
  exact (rho_val' g hL ⟨t, ht'⟩).symm

theorem rho_mem_T46
    (g : Ca) : rho g ∈ CFSG.Fischer.T46 := by
  obtain ⟨g, hg⟩ := g
  have hg1 : g ∈ lvl 1 := Ca_eq_lvl ▸ hg
  induction hg1 using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    exact rho_mem_T46_of_table _ (rep_pairG_all l (levelLetters_lt hl))
      (centCert_parts.2.2.2.1 l hl).2
  | one => exact (map_one rho) ▸ CFSG.Fischer.T46.one_mem
  | mul x y hx hy ihx ihy =>
    have hx' : x ∈ Ca := Ca_eq_lvl ▸ hx
    have hy' : y ∈ Ca := Ca_eq_lvl ▸ hy
    have : (⟨x * y, hg⟩ : Ca) = ⟨x, hx'⟩ * ⟨y, hy'⟩ := rfl
    rw [this, map_mul]
    exact CFSG.Fischer.T46.mul_mem (ihx hx') (ihy hy')
  | inv x hx ihx =>
    have hx' : x ∈ Ca := Ca_eq_lvl ▸ hx
    have : (⟨x⁻¹, hg⟩ : Ca) = (⟨x, hx'⟩ : Ca)⁻¹ := rfl
    rw [this, map_inv]
    exact CFSG.Fischer.T46.inv_mem (ihx hx')

theorem genG_neg_two : genG (-2) = b⁻¹ := by
  unfold genG
  simp only [show (-2 : ℤ) ≠ 1 by decide, show (-2 : ℤ) ≠ -1 by decide,
    show (-2 : ℤ) ≠ 2 by decide, ite_false]

theorem rep_cTab :
    ∀ k < 3510, Rep 3510 (cTab orb (genTables orb (-2)) k) (conjPt k) := by
  intro k hk
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [cTab.eq_def, conjPt.eq_def]
    by_cases h : 0 < k ∧ ap orb.par k < k
    · rw [dite_eq_left h, dite_eq_left h]
      have hp := ih _ h.2 (lt_trans h.2 hk)
      by_cases hl : ap orb.lab k = 1
      · have hlab : labG (ap orb.lab k) = a := by simp [labG, hl]
        rw [ite_eq_left (by simp [hl]), hlab, a_inv]
        exact (rep_alpha.compT hp).compT rep_alpha
      · have hlab : labG (ap orb.lab k) = b := by simp [labG, hl]
        rw [ite_eq_right (by simp [hl]), hlab]
        have hbi := rep_gen (-2)
        rw [genG_neg_two] at hbi
        exact (rep_beta.compT hp).compT hbi
    · rw [dite_eq_right h, dite_eq_right h]
      exact rep_alpha

@[expose] noncomputable def starCa
    (i : ℕ) (hi : i < 693) : Ca :=
  ⟨conjPt ea[i]!, mem_Ca.2 (conjPt_mem_star (ea_get_mem hi)).2.2⟩

theorem starCa_val
    (i : ℕ) (hi : i < 693) : (starCa i hi : J) = conjPt ea[i]! := rfl

@[expose] noncomputable def tvPt
    (m : Fin 693) : Equiv.Perm (Fin 693) :=
  CFSG.Fischer.piGU (CFSG.Fischer.tvGU (CFSG.Fischer.uVec m)
    (CFSG.Fischer.uVec_iso CFSG.Fischer.ptsFacts m.2))

theorem rep_tvPt
    (m : Fin 693) : Rep 693 (tvTable uPts[m.val]!) (tvPt m) := by
  have h := CFSG.Fischer.rep_tvTable (CFSG.Fischer.uVec m)
    (CFSG.Fischer.uVec_iso CFSG.Fischer.ptsFacts m.2)
  rw [CFSG.Fischer.codeOf_uVec CFSG.Fischer.ptsFacts m.2] at h
  exact CFSG.Fischer.rep_piGU h

theorem phiData_lt
    {i : ℕ} (hi : i < 693) : phiData[i]! < 693 := (centCert_parts.2.2.1 i hi).1

section Propagation

open CFSG.Fischer CFSG.KS.Fi22Cent Matrix

private theorem cube_one : ∀ c : F4, c ≠ 0 → c ^ 2 * c = 1 := by decide

private theorem tvM_smul {c : F4} (hc : c ≠ 0) (v : W) : tvM (c • v) = tvM v := by
  rw [Matrix.ext_iff_mulVec]
  intro x
  rw [tvM_mulVec, tvM_mulVec, hermStd_smul_right, smul_smul, mul_right_comm, cube_one c hc,
    one_mul]

theorem tvPt_val (w u : Fin 693) :
    (tvPt w u).val = ptIdx ((tvM (uVec w)).mulVec (uVec u)) := by
  unfold tvPt
  rw [MulAction.toPermHom_apply, MulAction.toPerm_apply, smul_val]
  rfl

theorem tvPt_conj (w u : Fin 693) :
    tvPt w * tvPt u * (tvPt w)⁻¹ = tvPt (tvPt w u) := by
  have hw := uVec_iso ptsFacts w.2
  have hu := uVec_iso ptsFacts u.2
  set g := tvGU (uVec w) hw
  have hg : IsIsom ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) := g.2
  have hz : (tvM (uVec w)).mulVec (uVec u) ≠ 0 :=
    mulVec_ne_zero (tvGL (uVec w) hw) (uVec_ne_zero ptsFacts u.2)
  have hiz : hermStd ((tvM (uVec w)).mulVec (uVec u)) ((tvM (uVec w)).mulVec (uVec u)) = 0 := by
    exact (hermStd_mulVec g (uVec u) (uVec u)).trans hu
  obtain ⟨c, hc, hcz⟩ := normV_eq_smul hz
  have hv : uVec (tvPt w u) = c • (tvM (uVec w)).mulVec (uVec u) := by
    rw [tvPt_val, uVec_ptIdx ptsFacts hz hiz, hcz]
  have key : g * tvGU (uVec u) hu * g⁻¹ =
      tvGU (uVec (tvPt w u)) (uVec_iso ptsFacts (tvPt w u).2) := by
    apply Subtype.ext
    apply Units.ext
    rw [Matrix.ext_iff_mulVec]
    intro x
    change (((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) * tvM (uVec u) *
      (((g : GL (Fin 6) F4)⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)).mulVec x =
        (tvM (uVec (tvPt w u))).mulVec x
    rw [← mulVec_mulVec, ← mulVec_mulVec, conj_tvM hg, hv, tvM_smul hc]
    rfl
  change piGU g * piGU (tvGU (uVec u) hu) * (piGU g)⁻¹ = tvPt (tvPt w u)
  rw [← map_mul, ← map_inv, ← map_mul, key]
  rfl

theorem phiPos_lt (u : Fin 693) : phiPos[u.val]! < 693 := by
  rw [← phiEquiv_symm_val]
  exact (phiEquiv.symm u).2

theorem conj_mem_ea (g : Ca)
    {i : ℕ} (hi : i < 693) : idx 3510 (g : J) ea[i]! ∈ ea := by
  have hk3 := ea_get_lt hi
  have hk' : idx 3510 (g : J) ea[i]! < 3510 := idx_lt _ hk3
  have hconj : (g : J) * conjPt ea[i]! * (g : J)⁻¹ = conjPt (idx 3510 (g : J) ea[i]!) :=
    (idx_eq_iff hk3 hk').1 rfl
  have hmem := conj_mem_star g.2 (conjPt_mem_star (ea_get_mem hi))
  rw [hconj] at hmem
  obtain ⟨k, hk, hkeq⟩ := mem_ea_of_mem_star hmem
  have := conjPt_inj (by rw [orb_size]; exact hk') (by rw [orb_size]; exact (mem_ea.1 hk).1) hkeq
  rw [this]
  exact hk

theorem rho_val_idx
    (g : Ca) (u : Fin 693) :
    (rho g u).val = phiData[(ePos ea)[idx 3510 (g : J) ea[phiPos[u.val]!]!]!]! := by
  have hi := phiPos_lt u
  set k := ea[phiPos[u.val]!]! with hk
  have hk3 : k < 3510 := ea_get_lt hi
  have hk' : idx 3510 (g : J) k < 3510 := idx_lt _ hk3
  have hmem : idx 3510 (g : J) k ∈ ea := conj_mem_ea g hi
  have hj := (ePos_lt_iff hk').2 hmem
  have hconj : (g : J) * conjPt k * (g : J)⁻¹ = conjPt (idx 3510 (g : J) k) :=
    (idx_eq_iff hk3 hk').1 rfl
  have hstar : g • ptE u = posEquiv ⟨(ePos ea)[idx 3510 (g : J) k]!, hj⟩ := by
    apply Subtype.ext
    rw [starAction_val, ptE_apply, posEquiv_apply, ← hk, hconj, ea_ePos hmem]
  rw [rho_apply, hstar, ptE_symm_posEquiv, phiEquiv_apply]

theorem idx_conjPt {k x : ℕ} (hk : k < 3510) (hx : x < 3510) :
    idx 3510 (conjPt k) x = cPt orb k x :=
  (rep_cTab k hk x hx).symm

theorem idx_uPts {y : ℕ} (hy : y < 693) :
    uPts.toList.idxOf uPts[y]! = y := by
  have hs : y < uPts.toList.length := by rw [Array.length_toList, ptsFacts.size]; exact hy
  rw [getElem!_pos uPts y (by rw [ptsFacts.size]; exact hy), ← Array.getElem_toList]
  exact List.get_idxOf (uPts_nodup ptsFacts) ⟨y, hs⟩

@[expose] def TvAt
    (i : ℕ) : Prop :=
  ∀ hi : i < 693, rho (starCa i hi) = tvPt ⟨phiData[i]!, phiData_lt hi⟩

noncomputable abbrev σc (g i : ℕ) : ℕ :=
  (ePos ea)[cPt orb ea[g]! ea[i]!]!

theorem σc_spec {g i : ℕ}
    (hg : g < 693) (hi : i < 693) :
    σc g i < 693 ∧ ea[σc g i]! = idx 3510 (conjPt ea[g]!) ea[i]! := by
  have hm := conj_mem_ea (starCa g hg) hi
  rw [starCa_val] at hm
  have e : cPt orb ea[g]! ea[i]! = idx 3510 (conjPt ea[g]!) ea[i]! :=
    (idx_conjPt (ea_get_lt hg) (ea_get_lt hi)).symm
  unfold σc
  rw [e]
  exact ⟨(ePos_lt_iff (mem_ea.1 hm).1).2 hm, ea_ePos hm⟩

theorem rho_starCa_pt {g i : ℕ}
    (hg : g < 693) (hi : i < 693) :
    (rho (starCa g hg) ⟨phiData[i]!, phiData_lt hi⟩).val = phiData[σc g i]! := by
  rw [rho_val_idx]
  have hp : phiPos[phiData[i]!]! = i := (centCert_parts.2.2.1 i hi).2
  simp only [hp, starCa_val]
  unfold σc
  rw [idx_conjPt (ea_get_lt hg) (ea_get_lt hi)]

theorem tvAt_step
    {g i : ℕ} (hg : g < 693) (hi : i < 693) (hTg : TvAt g)
    (hTi : TvAt i) : TvAt (σc g i) := by
  intro hs
  obtain ⟨-, he⟩ := σc_spec hg hi
  have hstar : starCa (σc g i) hs = starCa g hg * starCa i hi * (starCa g hg)⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, starCa_val]
    rw [he]
    exact ((idx_eq_iff (ea_get_lt hi) (idx_lt _ (ea_get_lt hi))).1 rfl).symm
  have hpt : tvPt ⟨phiData[g]!, phiData_lt hg⟩ ⟨phiData[i]!, phiData_lt hi⟩ =
      ⟨phiData[σc g i]!, phiData_lt hs⟩ := by
    apply Fin.ext
    rw [← hTg hg, rho_starCa_pt hg hi]
  rw [hstar, map_mul, map_mul, map_inv, hTg hg, hTi hi, tvPt_conj, hpt]

theorem tvAt_gen
    {g : ℕ}
    (h : ∀ j < 693, uPts[phiData[σc g j]!]! = normC (tvC uPts[phiData[g]!]! uPts[phiData[j]!]!)) :
    TvAt g := by
  intro hg'
  ext u
  have hj := phiPos_lt u
  have hu : phiData[phiPos[u.val]!]! = u.val := by
    rw [← phiEquiv_symm_val, ← phiEquiv_apply, Equiv.apply_symm_apply]
  have hu' : u = ⟨phiData[phiPos[u.val]!]!, phiData_lt hj⟩ := Fin.ext hu.symm
  rw [hu', rho_starCa_pt hg' hj]
  have hR := rep_tvPt ⟨phiData[g]!, phiData_lt hg'⟩ phiData[phiPos[u.val]!]! (phiData_lt hj)
  rw [idx_of_lt _ (phiData_lt hj), Equiv.Perm.smul_def] at hR
  rw [← hR]
  obtain ⟨hs, -⟩ := σc_spec hg' hj
  have hm := h _ hj
  have hm4 : uPts[phiData[σc g (phiPos[u.val]!)]!]! < 4096 :=
    (mem_uPts.1 (uPts_get_mem ptsFacts (phiData_lt hs))).1
  rw [ap_tvTable _ (phiData_lt hj) hm.symm hm4, idx_uPts (phiData_lt hs)]

theorem tvAt_all
    {i : ℕ} (hi : i < 693) : TvAt i := by
  obtain ⟨hgen, htree⟩ := centCert_parts.2.2.2.2
  have hG : ∀ s < 6, TvAt (GSK s) := fun s hs => tvAt_gen (hgen s hs).2
  have hT : ∀ t < 693, ORK t < 693 ∧ TvAt (ORK t) := by
    intro t ht
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      rcases Nat.eq_zero_or_pos t with rfl | ht0
      · rw [htree.1.1]
        exact ⟨(hgen 0 (by norm_num)).1, hG 0 (by norm_num)⟩
      · obtain ⟨h1, h2, h3⟩ := htree.1.2.1 t ht0 ht
        obtain ⟨hp, hTp⟩ := ih _ h1 (by omega)
        have hgl := (hgen _ h2).1
        rw [h3]
        exact ⟨(σc_spec hgl hp).1, tvAt_step hgl hp (hG _ h2) hTp⟩
  obtain ⟨h1, h2⟩ := htree.1.2.2 i hi
  rw [← h2]
  exact (hT _ h1).2

end Propagation

theorem rho_starCa
    (i : ℕ) (hi : i < 693) :
    rho (starCa i hi) = tvPt ⟨phiData[i]!, phiData_lt hi⟩ :=
  tvAt_all hi hi

theorem ptE_mem_Ca
    (u : Fin 693) : (ptE u : J) ∈ Ca := mem_Ca.2 (ptE u).2.2.2

theorem rho_ptE
    (u : Fin 693) : rho ⟨ptE u, ptE_mem_Ca u⟩ = tvPt u := by
  have hi : phiPos[u.val]! < 693 := by rw [← phiEquiv_symm_val]; exact (phiEquiv.symm u).2
  have hu : phiData[phiPos[u.val]!]! = u.val := by
    rw [← phiEquiv_symm_val, ← phiEquiv_apply, Equiv.apply_symm_apply]
  have h : (⟨ptE u, ptE_mem_Ca u⟩ : Ca) = starCa _ hi := by
    apply Subtype.ext
    rw [starCa_val, ptE_apply]
  rw [h, rho_starCa]
  congr 1
  exact Fin.ext hu

noncomputable abbrev Hloc :
    Subgroup Ca := (LocalGroup D a).subgroupOf Ca

theorem starCa_mem
    (i : ℕ) (hi : i < 693) : starCa i hi ∈ Hloc :=
  Subgroup.mem_subgroupOf.2 (Subgroup.subset_closure (conjPt_mem_star (ea_get_mem hi)))

theorem tvPt_mem
    (m : Fin 693) : tvPt m ∈ Hloc.map rho := by
  have hi : phiPos[m.val]! < 693 := by rw [← phiEquiv_symm_val]; exact (phiEquiv.symm m).2
  have hm : phiData[phiPos[m.val]!]! = m.val := by
    rw [← phiEquiv_symm_val, ← phiEquiv_apply, Equiv.apply_symm_apply]
  refine ⟨starCa _ hi, starCa_mem _ hi, ?_⟩
  rw [rho_starCa]
  congr 1
  exact Fin.ext hm

theorem piGU_tvGU_congr
    {v w : CFSG.Fischer.W} (h : v = w) (hv : CFSG.Fischer.hermStd v v = 0)
    (hw : CFSG.Fischer.hermStd w w = 0) :
    CFSG.Fischer.piGU (CFSG.Fischer.tvGU v hv) = CFSG.Fischer.piGU (CFSG.Fischer.tvGU w hw) := by
  subst h; rfl

private theorem vecOfCode_zero : CFSG.Fischer.vecOfCode 0 = 0 := by
  funext i; fin_cases i <;> rfl

theorem tvGU_zero (h : CFSG.Fischer.hermStd 0 0 = 0) : CFSG.Fischer.tvGU 0 h = 1 := by
  apply Subtype.ext
  apply Units.ext
  show CFSG.Fischer.tvM 0 = 1
  simp [CFSG.Fischer.tvM]

theorem t46G_mem
    (z : ℤ) : CFSG.Fischer.t46G z ∈ Hloc.map rho := by
  unfold CFSG.Fischer.t46G
  by_cases hk : z.natAbs - 1 < 46
  · obtain ⟨m, hm, hmc⟩ := Array.mem_iff_getElem.1 (CFSG.Fischer.tvGens_facts.2 _ hk)
    have hm' : m < 693 := by rw [← CFSG.Fischer.ptsFacts.size]; exact hm
    have hv : CFSG.Fischer.vecOfCode tvGens[z.natAbs - 1]! = CFSG.Fischer.uVec m := by
      unfold CFSG.Fischer.uVec
      rw [getElem!_pos uPts m hm, hmc]
    rw [piGU_tvGU_congr hv _ (CFSG.Fischer.uVec_iso CFSG.Fischer.ptsFacts hm')]
    exact tvPt_mem ⟨m, hm'⟩
  · have h0 : tvGens[z.natAbs - 1]! = 0 :=
      getElem!_neg tvGens _ (by rw [CFSG.Fischer.tvGens_facts.1]; exact hk)
    have hv : CFSG.Fischer.vecOfCode tvGens[z.natAbs - 1]! = 0 := by rw [h0, vecOfCode_zero]
    rw [piGU_tvGU_congr hv _ (by simp [CFSG.Fischer.hermStd]), tvGU_zero, map_one]
    exact Subgroup.one_mem _

theorem T46_le_map :
    CFSG.Fischer.T46 ≤ Hloc.map rho := by
  unfold CFSG.Fischer.T46 CFSG.Fischer.t46lvl levelGroup lettersGroup
  rw [Subgroup.closure_le]
  rintro _ ⟨l, -, rfl⟩
  have hw : ∀ j, CFSG.Fischer.t46gs j ∈ Hloc.map rho := fun j => by
    unfold CFSG.Fischer.t46gs wordG
    exact Subgroup.list_prod_mem _ fun x hx => by
      obtain ⟨z, -, rfl⟩ := List.mem_map.1 hx
      exact t46G_mem z
  unfold pairG
  split_ifs
  · exact hw _
  · exact Subgroup.inv_mem _ (hw _)

theorem range_rho :
    rho.range = CFSG.Fischer.T46 := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩; exact rho_mem_T46 g
  · exact T46_le_map.trans (Subgroup.map_le_range _ _)

theorem map_Hloc :
    Hloc.map rho = CFSG.Fischer.T46 :=
  le_antisymm ((Subgroup.map_le_range _ _).trans range_rho.le) T46_le_map

theorem card_Ca :
    Nat.card Ca = 18393661440 := by rw [Ca_eq_lvl, card_lvl_one]

theorem card_ker_rho :
    Nat.card rho.ker = 2 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup rho.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange rho).toEquiv, range_rho,
    CFSG.Fischer.card_T46, card_Ca] at h1
  omega

@[expose] noncomputable def aCa : Ca := ⟨a, mem_Ca.2 rfl⟩

theorem aCa_val : (aCa : J) = a := rfl

theorem rho_aCa : rho aCa = 1 := by
  ext u
  rw [rho_apply]
  have : aCa • ptE u = ptE u := by
    apply Subtype.ext
    rw [starAction_val]
    show a * (ptE u : J) * a⁻¹ = ptE u
    rw [← (ptE u).2.2.2, mul_assoc, mul_inv_cancel, mul_one]
  rw [this, Equiv.symm_apply_apply]
  rfl

theorem aCa_ne_one :
    aCa ≠ 1 := fun h => a_ne_one (congrArg Subtype.val h)

theorem orderOf_aCa :
    orderOf aCa = 2 := by
  rw [← orderOf_injective Ca.subtype Subtype.val_injective aCa]
  exact orderOf_a

theorem ker_rho :
    rho.ker = Subgroup.zpowers aCa := by
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · rw [Subgroup.zpowers_le]; exact rho_aCa
  · rw [card_ker_rho, Nat.card_zpowers, orderOf_aCa]

theorem rep_unique
    {T : Table} {g h : J} (hg : Rep 3510 T g) (hh : Rep 3510 T h) : g = h := by
  have : h⁻¹ * g = 1 := eq_one_of_fix_all fun i => by
    have e : g • i = h • i := by
      apply Fin.ext
      have e := (hg i.val i.2).symm.trans (hh i.val i.2)
      rw [idx_of_lt _ i.2, idx_of_lt _ i.2] at e
      exact e
    rw [mul_smul, e, inv_smul_smul]
  rw [inv_mul_eq_one] at this
  exact this.symm

theorem rep_wordTab (w : List ℕ) (hw : ∀ k ∈ w, k < 3510) :
    Rep 3510 (wordTab orb (genTables orb (-2)) w) (w.map conjPt).prod := by
  induction w with
  | nil => simpa [wordTab] using Rep.idT (G := J) (n := 3510) (by norm_num)
  | cons k w ih =>
    simp only [wordTab, List.foldr_cons, List.map_cons, List.prod_cons]
    exact (rep_cTab k (hw k (by simp))).compT (ih fun k' hk' => hw k' (by simp [hk']))

theorem iterN_congr {f g : ℕ → ℕ} (hfg : ∀ y < 3510, f y = g y) (hg : ∀ y < 3510, g y < 3510) :
    ∀ n x, x < 3510 → iterN f n x = iterN g n x
  | 0, _, _ => rfl
  | n + 1, x, hx => by
    simp only [iterN]
    rw [hfg x hx]
    exact iterN_congr hfg hg n _ (hg x hx)

theorem idx_pow (g : J) (n x : ℕ) :
    idx 3510 (g ^ n) x = iterN (idx 3510 g) n x := by
  induction n generalizing x with
  | zero => rw [pow_zero, idx_one]; rfl
  | succ n ih => rw [pow_succ, idx_mul, ih]; rfl

private theorem chainQ_lt : ∀ q ∈ chainQ, q < 3510 := by decide

theorem pow_eq_a_of (w : List ℕ) (m : ℕ) (hw : ∀ k ∈ w, k < 3510)
    (hp : ∀ q ∈ chainQ, iterN (ap (wordTab orb (genTables orb (-2)) w)) m q = ap orb.alpha q) :
    ((w.map conjPt).prod) ^ m = a := by
  have hR := rep_wordTab w hw
  have hq : ∀ q ∈ chainQ, idx 3510 (((w.map conjPt).prod) ^ m) q = idx 3510 a q := by
    intro q hq
    have hq3 := chainQ_lt q hq
    rw [idx_pow, ← iterN_congr (fun y hy => hR y hy) (fun y hy => idx_lt _ hy) m q hq3, hp q hq,
      rep_alpha q hq3]
  have h1 : a⁻¹ * ((w.map conjPt).prod) ^ m = 1 := by
    apply sep
    intro t ht
    have hmem : chainQ[t]! ∈ chainQ := by
      rw [getElem!_pos chainQ t ht]
      exact Array.getElem_mem ht
    rw [idx_mul, hq _ hmem, idx_inv_idx]
  exact (inv_mul_eq_one.1 h1).symm

theorem aWord_mem : ∀ k ∈ aWord, k ∈ ea :=
  centCert_parts.2.2.2.2.2.2.1

theorem aWord2_mem : ∀ k ∈ aWord2, k ∈ ea :=
  centCert_parts.2.2.2.2.2.2.2.2.1

theorem a_eq_word :
    ((aWord.map conjPt).prod) ^ 9 = a :=
  pow_eq_a_of aWord 9 (fun k hk => (mem_ea.1 (aWord_mem k hk)).1) centCert_parts.2.2.2.2.2.2.2.1

theorem a_eq_word2 :
    ((aWord2.map conjPt).prod) ^ 11 = a :=
  pow_eq_a_of aWord2 11 (fun k hk => (mem_ea.1 (aWord2_mem k hk)).1)
    centCert_parts.2.2.2.2.2.2.2.2.2

theorem a_mem_localGroup :
    a ∈ LocalGroup D a := by
  have h : ((aWord.map conjPt).prod) ^ 9 ∈ LocalGroup D a := by
    apply Subgroup.pow_mem
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    exact Subgroup.subset_closure (conjPt_mem_star (aWord_mem k hk))
  rwa [a_eq_word] at h

theorem aCa_mem_Hloc :
    aCa ∈ Hloc := Subgroup.mem_subgroupOf.2 a_mem_localGroup

theorem Hloc_eq_top :
    Hloc = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hg : rho g ∈ Hloc.map rho := by rw [map_Hloc]; exact rho_mem_T46 g
  obtain ⟨h, hh, hgh⟩ := hg
  have hk : h⁻¹ * g ∈ rho.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hgh, inv_mul_cancel]
  rw [ker_rho] at hk
  have hk' : h⁻¹ * g ∈ Hloc :=
    (Subgroup.zpowers_le.2 aCa_mem_Hloc) hk
  have := Hloc.mul_mem hh hk'
  rwa [mul_inv_cancel_left] at this

theorem localGroup_eq :
    LocalGroup D a = Ca := by
  apply le_antisymm
  · rw [LocalGroup, Subgroup.closure_le]
    intro x hx
    exact mem_Ca.2 hx.2.2
  · intro g hg
    have : (⟨g, hg⟩ : Ca) ∈ Hloc := by rw [Hloc_eq_top]; trivial
    exact Subgroup.mem_subgroupOf.1 this

end CFSG.Sporadic.Fi22
