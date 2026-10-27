
module

public import CFSG.Sporadic.Co2Schreier.KernelBase

public import CFSG.Sporadic.Co2Schreier.KerCheck
public import CFSG.Sporadic.Co2Schreier.Centralizers
public import CFSG.Sporadic.Co2Schreier.Cores
public import CFSG.Sporadic.Co2Schreier.ChainCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.Arrays
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.Co2Schreier.CoreCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.ChainCheck
public meta import Std.Data.HashMap
public import CFSG.Sporadic.Co2Schreier.KerCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.WitCheck
public meta import CFSG.Sporadic.Co2Schreier.CoreCheck
public import CFSG.Sporadic.Co2Schreier.OrbitCheck
public meta import CFSG.Sporadic.Co2Schreier.OrbitCheck
public import CFSG.Sporadic.Co2Schreier.TextCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.Text
public import CFSG.Sporadic.Co2Cert.CheckInputs
public import CFSG.Sporadic.Co2Cert.OrderCheckInputs

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert

section Hom

variable {G H : Type*} [Group G] [Group H] (f : G →* H)

end Hom

theorem kerFacts : KerFacts := by
  have h := ker_check
  simp only [kerCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩,
    h14⟩, h15⟩, h16⟩, h17⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

theorem rep_zeta
    {k : ℕ} (hk : k < 32) : Rep 2300 kerData.zs[k]! (zeta k) := by
  change Rep 2300 (centerIdxR.map fun k => enumR.elems[k]!).toArray[k]! _
  rw [toArray_map_getElem! _ _ 0 (by rw [centerIdxR_length]; exact hk)]
  exact enumR_facts.rep (centerIdxR_lt k hk)

theorem zeta_mem_centerIn
    {k : ℕ} (hk : k < 32) : zeta k ∈ CFSG.centerIn locR := by
  refine (enumR_facts.mem_centerIn_iff repTuple_r (centerIdxR_lt k hk)).2 ?_
  rw [(coreOK_spec coreR_check.1).2.2]
  exact getD_mem (by rw [centerIdxR_length]; exact hk)

theorem exists_zeta
    {v : Equiv.Perm (Fin 2300)} (hv : v ∈ CFSG.centerIn locR) :
    ∃ k < 32, v = zeta k := by
  obtain ⟨m, hm, rfl⟩ := enumR_facts.exists_elt repTuple_r (Subgroup.mem_inf.1 hv).1
  have h := (enumR_facts.mem_centerIn_iff repTuple_r hm).1 hv
  rw [(coreOK_spec coreR_check.1).2.2] at h
  obtain ⟨k, hk, hkm⟩ := (mem_iff_exists_getD (d := 0)).1 h
  exact ⟨k, by rw [← centerIdxR_length]; exact hk, by rw [zeta, hkm]⟩

theorem zeta_zero : zeta 0 = 1 := enumR_facts.elt_zero

theorem zeta_mem_P
    {k : ℕ} (hk : k < 32) : zeta k ∈ co2P :=
  locD_le_P (locR_le_D (Subgroup.mem_inf.1 (zeta_mem_centerIn hk)).1)

theorem rep_dArrs
    {i : ℕ} (hi : i < 2) : Rep 2300 kerData.d[i]! (dTuple.getD i 1) :=
  repTuple_d.rep (by rw [dTuple_length]; exact hi)

theorem repTuple_cand
    {k0 k1 : ℕ} (hk0 : k0 < 32) (hk1 : k1 < 32) :
    RepTuple 2300 (candArrs kerData k0 k1) (candTuple k0 k1) :=
  repTuple_pair (rep_compA (rep_dArrs (by norm_num)) (rep_zeta hk0))
    (rep_compA (rep_dArrs (by norm_num)) (rep_zeta hk1))

section Fix

variable {α : MulAut co2P}
  (hα : ∀ c : co2P, (c : Equiv.Perm (Fin 2300)) ∈ locC → α c = c)
include hα

theorem mem_D_of_fix
    {x : co2P} (hx : (x : Equiv.Perm (Fin 2300)) ∈ locD) :
    ((α x : co2P) : Equiv.Perm (Fin 2300)) ∈ locD := by
  rw [locD_eq_centralizer] at hx ⊢
  have ht : α tP = tP := fix_of_mem_S hα locT_mem_S
  have hcomm : x * tP = tP * x :=
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hx).2)
  have h2 := congrArg α hcomm
  rw [map_mul, map_mul, ht] at h2
  exact Subgroup.mem_inf.2 ⟨(α x).2,
    Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val h2)⟩

theorem inv_mul_mem_centerIn
    {x : co2P} (hx : (x : Equiv.Perm (Fin 2300)) ∈ locD) :
    (x : Equiv.Perm (Fin 2300))⁻¹ * ((α x : co2P) : Equiv.Perm (Fin 2300)) ∈
      CFSG.centerIn locR := by
  rw [← locD_inf_centralizer_R]
  refine Subgroup.mem_inf.2 ⟨locD.mul_mem (locD.inv_mem hx) (mem_D_of_fix hα hx), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have hrD : r ∈ locD := locR_le_D hr
  have hrP : r ∈ co2P := locD_le_P hrD
  have hxr : (x : Equiv.Perm (Fin 2300)) * r * (x : Equiv.Perm (Fin 2300))⁻¹ ∈ locR := by
    have := locR_normal.conj_mem ⟨r, hrD⟩ (Subgroup.mem_subgroupOf.2 hr) ⟨x, hx⟩
    exact Subgroup.mem_subgroupOf.1 this
  have h1 : α ⟨r, hrP⟩ = ⟨r, hrP⟩ := fix_of_mem_S hα (locR_le_S hr)
  have h3 : α (x * ⟨r, hrP⟩ * x⁻¹) = x * ⟨r, hrP⟩ * x⁻¹ := fix_of_mem_S hα (locR_le_S hxr)
  rw [map_mul, map_mul, map_inv, h1] at h3
  have h4 : ((α x : co2P) : Equiv.Perm (Fin 2300)) * r * ((α x : co2P) : Equiv.Perm (Fin 2300))⁻¹ =
      (x : Equiv.Perm (Fin 2300)) * r * (x : Equiv.Perm (Fin 2300))⁻¹ :=
    congrArg Subtype.val h3
  calc r * ((x : Equiv.Perm (Fin 2300))⁻¹ * ((α x : co2P) : Equiv.Perm (Fin 2300)))
      = (x : Equiv.Perm (Fin 2300))⁻¹ * ((x : Equiv.Perm (Fin 2300)) * r *
          (x : Equiv.Perm (Fin 2300))⁻¹) * ((α x : co2P) : Equiv.Perm (Fin 2300)) := by group
    _ = (x : Equiv.Perm (Fin 2300))⁻¹ * (((α x : co2P) : Equiv.Perm (Fin 2300)) * r *
          ((α x : co2P) : Equiv.Perm (Fin 2300))⁻¹) *
            ((α x : co2P) : Equiv.Perm (Fin 2300)) := by rw [h4]
    _ = (x : Equiv.Perm (Fin 2300))⁻¹ * ((α x : co2P) : Equiv.Perm (Fin 2300)) * r := by group

theorem exists_image_dP
    (i : ℕ) :
    ∃ k < 32, ((α (dP i) : co2P) : Equiv.Perm (Fin 2300)) = dTuple.getD i 1 * zeta k := by
  obtain ⟨k, hk, he⟩ := exists_zeta (inv_mul_mem_centerIn hα (x := dP i) (dTuple_getD_mem_D i))
  exact ⟨k, hk, inv_mul_eq_iff_eq_mul.1 he⟩

theorem candOK_of_fix
    {k0 k1 : ℕ} (hk0 : k0 < 32) (hk1 : k1 < 32)
    (h0 : ((α (dP 0) : co2P) : Equiv.Perm (Fin 2300)) = dTuple.getD 0 1 * zeta k0)
    (h1 : ((α (dP 1) : co2P) : Equiv.Perm (Fin 2300)) = dTuple.getD 1 1 * zeta k1) :
    candOK kerData k0 k1 = true := by
  have hes := map_dPs h0 h1
  have hE := repTuple_cand hk0 hk1
  have hinv := allLt_iff.1 (allLt_iff.1 kerFacts.inv k0 hk0) k1 hk1
  rw [Bool.and_eq_true] at hinv
  have hext : ∀ ds : List (List ℤ), ∀ j : ℕ, (((extendTuple dPs ds).getD j 1 : co2P) :
      Equiv.Perm (Fin 2300)) = (extendTuple dTuple ds).getD j 1 := fun ds j => by
    rw [← dPs_map_subtype, ← map_getD_extendTuple]
    rfl
  have hextα : ∀ ds : List (List ℤ), ∀ j : ℕ, ((α ((extendTuple dPs ds).getD j 1) : co2P) :
      Equiv.Perm (Fin 2300)) = (extendTuple (candTuple k0 k1) ds).getD j 1 := fun ds j => by
    rw [← hes, ← map_getD_extendTuple, ← map_getD_extendTuple]
    rfl
  have hword : ∀ (gs : List co2P) (w : List ℤ), ((wordValue gs w : co2P) :
      Equiv.Perm (Fin 2300)) = wordValue (gs.map co2P.subtype) w := fun gs w =>
    map_wordValue co2P.subtype gs w
  have hwordα : ∀ (gs : List co2P) (w : List ℤ), α (wordValue gs w) =
      wordValue (gs.map α.toMonoidHom) w := fun gs w => map_wordValue α.toMonoidHom gs w
  simp only [candOK, Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨fun j hj => ?_, allLt_iff.2 fun i hi => ?_⟩, fun w hw => ?_⟩
  ·
    have hsj := List.all_eq_true.1 kerFacts.siftD j hj
    rw [Bool.and_eq_true, decide_eq_true_eq] at hsj
    have hj' : j < (extendTuple dTuple kerData.derivD).length := by
      rw [extendTuple_length, dTuple_length]
      exact hsj.1
    have hRd := (repTuple_d.extend (by rw [dTuple_length]; exact kerFacts.extD)
      kerFacts.invD).rep hj'
    have hRe := (hE.extend (by rw [candTuple_length]; exact kerFacts.extD) hinv.1).rep
      (by rw [extendTuple_length, candTuple_length]; exact hsj.1)
    have hmem : (((extendTuple dPs kerData.derivD).getD j 1 : co2P) :
        Equiv.Perm (Fin 2300)) ∈ locS := by
      rw [hext]
      exact mem_locS_of_sift hRd hsj.2
    have hfix := fix_of_mem_S hα hmem
    have := congrArg (fun y : co2P => (y : Equiv.Perm (Fin 2300))) hfix
    simp only [hextα, hext] at this
    exact (eqA_iff hRe hRd).2 this
  ·
    have hi' : i < localRec.rWords.length := hi
    have hw : localRec.rWords.getD i [] ∈ localRec.rWords := getD_mem hi'
    have hlw : lettersOK (2 + localRec.dStrongDerivations.length)
        (localRec.rWords.getD i []) = true := List.all_eq_true.1 kerFacts.rW _ hw
    have hRr : Rep 2300 kerData.r[i]! (wordValue dStarTuple (localRec.rWords.getD i [])) := by
      have := repTuple_r.rep (h := i) (by rw [rTuple, List.length_map]; exact hi')
      rwa [rTuple, List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_map,
        ← List.getD_eq_getElem _ [] hi'] at this
    have hEx := hE.extend (by rw [candTuple_length]; exact kerFacts.extL) hinv.2
    have hRe := hEx.word hinv.2 (w := localRec.rWords.getD i [])
      (by rw [extendTuple_length, candTuple_length]; exact hlw)
    have hmem : ((wordValue (extendTuple dPs localRec.dStrongDerivations)
        (localRec.rWords.getD i []) : co2P) : Equiv.Perm (Fin 2300)) ∈ locS := by
      rw [hword, map_extendTuple, dPs_map_subtype]
      exact locR_le_S (Subgroup.subset_closure (List.mem_map.2 ⟨_, hw, rfl⟩))
    have hfix := fix_of_mem_S hα hmem
    rw [hwordα, map_extendTuple] at hfix
    have := congrArg (fun y : co2P => (y : Equiv.Perm (Fin 2300))) hfix
    simp only [hword, map_extendTuple, hes, dPs_map_subtype] at this
    exact (eqA_iff hRe hRr).2 this
  ·
    have hlw : lettersOK 2 w = true := List.all_eq_true.1 kerFacts.addW w hw
    have hRd := repTuple_d.word wordFacts.invD (w := w) (by rw [dTuple_length]; exact hlw)
    have hRe := hE.word (allInv_of_extendArrs hinv.1) (w := w)
      (by rw [candTuple_length]; exact hlw)
    have hmem : ((wordValue dPs w : co2P) : Equiv.Perm (Fin 2300)) ∈ locS := by
      rw [hword, dPs_map_subtype]
      exact mem_locS_of_sift hRd (List.all_eq_true.1 kerFacts.siftAdd w hw)
    have hfix := fix_of_mem_S hα hmem
    rw [hwordα] at hfix
    have := congrArg (fun y : co2P => (y : Equiv.Perm (Fin 2300))) hfix
    simp only [hword, hes, dPs_map_subtype] at this
    exact (eqA_iff hRe hRd).2 this

theorem survivors_of_fix :
    ((α (dP 0) : co2P) : Equiv.Perm (Fin 2300)) = dTuple.getD 0 1 ∧
      (((α (dP 1) : co2P) : Equiv.Perm (Fin 2300)) = dTuple.getD 1 1 ∨
        ((α (dP 1) : co2P) : Equiv.Perm (Fin 2300)) = dTuple.getD 1 1 * zeta 9) := by
  obtain ⟨k0, hk0, h0⟩ := exists_image_dP hα 0
  obtain ⟨k1, hk1, h1⟩ := exists_image_dP hα 1
  have hc := allLt_iff.1 (allLt_iff.1 kerFacts.cand k0 hk0) k1 hk1
  rw [candOK_of_fix hα hk0 hk1 h0 h1, Bool.not_true, Bool.false_or,
    beq_iff_eq.1 kerFacts.surv] at hc
  have hc' : [k0, k1] = [0, 0] ∨ [k0, k1] = [0, 9] := by simpa using hc
  rcases hc' with h | h
  · simp only [List.cons.injEq, and_true] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [zeta_zero, mul_one] at h0 h1
    exact ⟨h0, Or.inl h1⟩
  · simp only [List.cons.injEq, and_true] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [zeta_zero, mul_one] at h0
    exact ⟨h0, Or.inr h1⟩

end Fix

theorem closure_C_dPs :
    Subgroup.closure (co2P.subtype ⁻¹'
      ((locC : Set (Equiv.Perm (Fin 2300))) ∪ {g | g ∈ dTuple})) = ⊤ := by
  have h : Subgroup.closure ((locC : Set (Equiv.Perm (Fin 2300))) ∪ {g | g ∈ dTuple}) = co2P := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, ← locD, locC_sup_locD]
  exact closure_subtype_preimage_eq_top h

theorem eq_of_agree
    {f g : MulAut co2P}
    (hC : ∀ c : co2P, (c : Equiv.Perm (Fin 2300)) ∈ locC → f c = g c)
    (h0 : f (dP 0) = g (dP 0)) (h1 : f (dP 1) = g (dP 1)) : f = g := by
  refine MulEquiv.toMonoidHom_injective (MonoidHom.eq_of_eqOn_dense closure_C_dPs ?_)
  intro x hx
  rcases (Set.mem_union _ _ _).1 (Set.mem_preimage.1 hx) with hx | hx
  · exact hC x (SetLike.mem_coe.1 hx)
  · obtain ⟨k, hk, hkx⟩ := (mem_iff_exists_getD (d := 1)).1
      (show co2P.subtype x ∈ dTuple from hx)
    rw [dTuple_length] at hk
    have hx' : x = dP k := Subtype.ext hkx.symm
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · rw [hx']
      exact h0
    · rw [hx']
      exact h1

theorem conj_zP_apply_of_mem_C
    {c : co2P} (hc : (c : Equiv.Perm (Fin 2300)) ∈ locC) :
    MulAut.conj zP c = c := by
  rw [MulAut.conj_apply]
  have h := Subgroup.mem_centralizer_singleton_iff.1 (locC_le_centralizer hc)
  apply Subtype.ext
  change locZ * (c : Equiv.Perm (Fin 2300)) * locZ⁻¹ = c
  rw [← h, mul_inv_cancel_right]

theorem rep_kerData_z :
    Rep 2300 kerData.z locZ := by
  have e : kerData.z = zArr := by simp only [kerData]
  rw [e]
  exact rep_z

theorem conj_zP_d0 :
    MulAut.conj zP (dP 0) = dP 0 := by
  rw [MulAut.conj_apply]
  apply Subtype.ext
  change locZ * dTuple.getD 0 1 * locZ⁻¹ = dTuple.getD 0 1
  have h := (commA_iff (rep_dArrs (by norm_num)) rep_kerData_z).1 kerFacts.comm0
  rw [← h, mul_inv_cancel_right]

theorem conj_zP_d1 :
    ((MulAut.conj zP (dP 1) : co2P) : Equiv.Perm (Fin 2300)) = dTuple.getD 1 1 * zeta 9 := by
  rw [MulAut.conj_apply]
  change locZ * dTuple.getD 1 1 * locZ⁻¹ = dTuple.getD 1 1 * zeta 9
  have h := (eqA_iff (rep_compA rep_kerData_z (rep_dArrs (by norm_num)))
    (rep_compA (rep_compA (rep_dArrs (by norm_num)) (rep_zeta (by norm_num))) rep_kerData_z)).1
    kerFacts.conj1
  rw [h, mul_inv_cancel_right]

theorem conj_zP_ne_one :
    MulAut.conj zP ≠ 1 := by
  intro h
  have h1 := congrArg (fun f : MulAut co2P => ((f (dP 1) : co2P) : Equiv.Perm (Fin 2300))) h
  simp only [MulAut.one_apply, MulAut.conj_apply] at h1
  change locZ * dTuple.getD 1 1 * locZ⁻¹ = dTuple.getD 1 1 at h1
  have h3 := (commA_iff (rep_dArrs (by norm_num)) rep_kerData_z).2
    (mul_inv_eq_iff_eq_mul.1 h1).symm
  have h4 := kerFacts.comm1
  rw [h3] at h4
  exact absurd h4 (by decide)

theorem CTUC_Co2_pointwise_first_centralizer_kernel :
    {α : MulAut co2P | ∀ c : co2P, (c : Equiv.Perm (Fin 2300)) ∈ locC → α c = c} =
      {1, MulAut.conj zP} ∧ MulAut.conj zP ≠ 1 := by
  refine ⟨Set.ext fun α => ⟨fun hα => ?_, ?_⟩, conj_zP_ne_one⟩
  · obtain ⟨h0, h1 | h1⟩ := survivors_of_fix hα
    · exact Or.inl (eq_of_agree (fun c hc => by rw [hα c hc]; rfl) (Subtype.ext h0)
        (Subtype.ext h1))
    · refine Or.inr (eq_of_agree (fun c hc => by rw [hα c hc, conj_zP_apply_of_mem_C hc])
        (Subtype.ext ?_) (Subtype.ext ?_))
      · rw [h0, conj_zP_d0]
        rfl
      · rw [h1, conj_zP_d1]
  · rintro (rfl | rfl) c hc
    · rfl
    · exact conj_zP_apply_of_mem_C hc

end CFSG.Sporadic.Co2Schreier
