module

public import CFSG.Sporadic.Fi23.Pair
public import CFSG.Sporadic.Fi23.CentCert
public import CFSG.Sporadic.Fi22.Transpositions

public section

namespace CFSG.Sporadic.Fi23

open Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Blueprint.Fischer
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable def frozen {α : Sort*} (a : α) : α := Classical.choose (⟨a, rfl⟩ : ∃ b, b = a)

theorem frozen_eq {α : Sort*} (a : α) : frozen a = a :=
  Classical.choose_spec (⟨a, rfl⟩ : ∃ b, b = a)

noncomputable def dT : Table := frozen (dTable orb)

noncomputable def biT : Table := frozen (genTables orb (-2))

noncomputable def bi22 : Table := frozen (Fi22.Native.genTables Fi22.orb (-2))

noncomputable def ea : Array ℕ := frozen (starPts dT)

noncomputable def ePos : Array ℕ := frozen (starPos ea)

noncomputable def phiD : Array ℕ := frozen starPhi

noncomputable def phiP : Array ℕ := frozen starPhiPos

noncomputable abbrev act23 (k m : ℕ) : ℕ := treeAct orb.par orb.lab orb.alpha orb.beta dT biT k m

noncomputable abbrev act22 (k m : ℕ) : ℕ :=
  treeAct Fi22.orb.par Fi22.orb.lab Fi22.orb.alpha Fi22.orb.beta Fi22.orb.alpha bi22 k m

theorem centCert_parts :
    ea.size = 3510 ∧ phiD.size = 3510 ∧
    (∀ i < 3510, phiD[i]! < 3510 ∧ phiP[phiD[i]!]! = i) ∧
    (∀ i < 3510, ∀ j < 3510, phiD[ePos[act23 ea[i]! ea[j]!]!]! = act22 phiD[i]! phiD[j]!) ∧
    (∀ k ∈ starWord, k ∈ ea) ∧
    powT 31671 11 (starWordTab orb dT biT starWord) = dT := by
  have h : centChecks orb Fi22.orb 3 = true := cent_certificate
  unfold centChecks at h
  simp only [Bool.and_eq_true, beq_iff_eq, allIn_eq_true, List.all_eq_true,
    Array.contains_iff_mem, decide_eq_true_eq] at h
  rw [← frozen_eq (dTable orb), ← dT, ← frozen_eq (genTables orb (-2)), ← biT,
    ← frozen_eq (Fi22.Native.genTables Fi22.orb (-2)), ← bi22, ← frozen_eq (starPts dT), ← ea,
    ← frozen_eq (starPos ea), ← ePos, ← frozen_eq starPhi, ← phiD, ← frozen_eq starPhiPos,
    ← phiP] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, h2, fun i hi => h3 i (Nat.zero_le _) hi, fun i hi j hj => ?_, h5, h6⟩
  have := allIn_eq_true.1 (parAll_eq_true h4 i hi) j (Nat.zero_le _) hj
  rwa [beq_iff_eq] at this

theorem treeAct_spec {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)]
    {par lab al be D bi : Table} {x y r : G} (hal : Rep n al x) (hbe : Rep n be y)
    (hbi : Rep n bi y⁻¹) (hD : Rep n D r) (hx : x⁻¹ = x) (c : ℕ → G)
    (hc : ∀ k, c k = if 0 < k ∧ ap par k < k then
      (if ap lab k = 1 then x else y) * c (ap par k) * (if ap lab k = 1 then x else y)⁻¹ else r) :
    ∀ k, ∀ m < n, treeAct par lab al be D bi k m = idx n (c k) m := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro m hm
    rw [treeAct.eq_def, hc k]
    by_cases h : 0 < k ∧ ap par k < k
    · rw [dite_eq_left h, ite_eq_left h]
      by_cases hl : ap lab k = 1
      · have hm' : ap al m < n := by rw [hal m hm]; exact idx_lt x hm
        rw [ite_eq_left (beq_iff_eq.2 hl), ite_eq_left hl, ih _ h.2 _ hm',
          hal _ (idx_lt _ hm'), hx, idx_mul, idx_mul, ← hal m hm]
      · have hm' : ap bi m < n := by rw [hbi m hm]; exact idx_lt _ hm
        rw [ite_eq_right (fun e => hl (beq_iff_eq.1 e)), ite_eq_right hl, ih _ h.2 _ hm',
          hbe _ (idx_lt _ hm'), idx_mul, idx_mul, ← hbi m hm]
    · rw [dite_eq_right h, ite_eq_right h]
      exact hD m hm

theorem rep_biT : Rep 31671 biT b⁻¹ := by
  have h := rep_gen (-2)
  have e : genG (-2) = b⁻¹ := by
    unfold genG
    simp only [show (-2 : ℤ) ≠ 1 by decide, show (-2 : ℤ) ≠ -1 by decide,
      show (-2 : ℤ) ≠ 2 by decide, ite_false]
  rw [e, ← frozen_eq (genTables orb (-2))] at h
  exact h

theorem rep_bi22 :
    Rep 3510 bi22 Fi22.b⁻¹ := by
  have h := Fi22.rep_gen (-2)
  have e : Fi22.genG (-2) = Fi22.b⁻¹ := by
    unfold Fi22.genG
    simp only [show (-2 : ℤ) ≠ 1 by decide, show (-2 : ℤ) ≠ -1 by decide,
      show (-2 : ℤ) ≠ 2 by decide, ite_false]
  rw [e, ← frozen_eq (Fi22.Native.genTables Fi22.orb (-2))] at h
  exact h

theorem rep_letter (x : ℕ) :
    Rep 31671 (if x = 0 then orb.alpha else orb.beta) (if x = 0 then a else b) := by
  split_ifs
  · exact rep_alpha
  · exact rep_beta

theorem rep_dWordTab (w : List ℕ) :
    Rep 31671 (w.foldr (fun x T => compT 31671 (if x = 0 then orb.alpha else orb.beta) T)
      (idT 31671)) (wordJ w) := by
  induction w with
  | nil => simpa [wordJ] using Rep.idT (G := J) (n := 31671) (by norm_num)
  | cons x w ih =>
    have e : wordJ (x :: w) = (if x = 0 then a else b) * wordJ w := by
      simp only [wordJ, List.map_cons, List.prod_cons]
    rw [List.foldr_cons, e]
    exact (rep_letter x).compT ih

theorem rep_dT : Rep 31671 dT d := by
  have h : Rep 31671 (dTable orb) d := Rep.powT (by norm_num) (rep_dWordTab dWord) 7
  rw [← frozen_eq (dTable orb)] at h
  exact h

theorem conjPt_eq
    (k : ℕ) : conjPt k = if 0 < k ∧ ap orb.par k < k then
    (if ap orb.lab k = 1 then a else b) * conjPt (ap orb.par k) *
      (if ap orb.lab k = 1 then a else b)⁻¹ else d := by
  rw [conjPt.eq_def]
  simp only [labG, dite_eq_ite]

theorem fi22_conjPt_eq
    (k : ℕ) : Fi22.conjPt k = if 0 < k ∧ ap Fi22.orb.par k < k then
    (if ap Fi22.orb.lab k = 1 then Fi22.a else Fi22.b) * Fi22.conjPt (ap Fi22.orb.par k) *
      (if ap Fi22.orb.lab k = 1 then Fi22.a else Fi22.b)⁻¹ else Fi22.a := by
  rw [Fi22.conjPt.eq_def]
  simp only [Fi22.labG, dite_eq_ite]

theorem act23_spec :
    ∀ k, ∀ m < 31671, act23 k m = idx 31671 (conjPt k) m :=
  treeAct_spec rep_alpha rep_beta rep_biT rep_dT a_inv conjPt conjPt_eq

theorem act22_spec :
    ∀ k, ∀ m < 3510, act22 k m = idx 3510 (Fi22.conjPt k) m :=
  treeAct_spec Fi22.rep_alpha Fi22.rep_beta rep_bi22 Fi22.rep_alpha Fi22.a_inv Fi22.conjPt
    fi22_conjPt_eq

abbrev D23 : Set J := {x | IsConj d x}

theorem mem_ea
    {k : ℕ} : k ∈ ea ↔ k < 31671 ∧ k ≠ 0 ∧ ap dT k = k := by
  rw [ea, frozen_eq]
  unfold starPts
  rw [List.mem_toArray, List.mem_filter, List.mem_range]
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]

theorem ea_size :
    ea.size = 3510 := centCert_parts.1

theorem ea_nodup : ea.toList.Nodup := by
  rw [ea, frozen_eq]
  unfold starPts
  rw [List.toList_toArray]
  exact List.nodup_range.filter _

theorem ea_get_mem
    {i : ℕ} (hi : i < 3510) : ea[i]! ∈ ea := by
  rw [getElem!_pos ea i (by rw [ea_size]; exact hi)]
  exact Array.getElem_mem _

theorem ea_get_lt
    {i : ℕ} (hi : i < 3510) : ea[i]! < 31671 := (mem_ea.1 (ea_get_mem hi)).1

theorem ePos_get
    {k : ℕ} (hk : k < 31671) : ePos[k]! = ea.toList.idxOf k := by
  rw [ePos, frozen_eq]
  simp only [starPos]
  rw [getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem ePos_ea
    {i : ℕ} (hi : i < 3510) : ePos[ea[i]!]! = i := by
  rw [ePos_get (ea_get_lt hi), getElem!_pos ea i (by rw [ea_size]; exact hi),
    ← Array.getElem_toList]
  exact List.get_idxOf ea_nodup ⟨i, by rw [Array.length_toList, ea_size]; exact hi⟩

theorem ePos_lt_iff
    {k : ℕ} (hk : k < 31671) : ePos[k]! < 3510 ↔ k ∈ ea := by
  rw [ePos_get hk, ← ea_size, ← Array.length_toList, List.idxOf_lt_length_iff,
    Array.mem_toList_iff]

theorem ea_ePos
    {k : ℕ} (hk : k ∈ ea) : ea[ePos[k]!]! = k := by
  have hlt := (ePos_lt_iff (mem_ea.1 hk).1).2 hk
  rw [getElem!_pos ea _ (by rw [ea_size]; exact hlt), ← Array.getElem_toList]
  simp only [ePos_get (mem_ea.1 hk).1]
  exact List.getElem_idxOf _

noncomputable abbrev star : Set J := LocalClass D23 d

theorem star_commute
    {x : J} (hx : x ∈ star) : x * d = d * x := hx.2.2

theorem conj_d_conjPt
    {k : ℕ} (hk : k < 31671) : d * conjPt k * d⁻¹ = conjPt (ap dT k) := by
  rw [rep_dT k hk]
  exact (idx_eq_iff hk (idx_lt _ hk)).1 rfl

theorem conjPt_mem_star {k : ℕ} (hk : k ∈ ea) : conjPt k ∈ star := by
  obtain ⟨hk1, hk0, hkd⟩ := mem_ea.1 hk
  refine ⟨(isConj_d_iff _).2 ⟨⟨k, hk1⟩, rfl⟩, fun h => hk0 ?_, ?_⟩
  · rw [← conjPt_zero] at h
    exact conjPt_inj (by rw [orb_size]; exact hk1) (by rw [orb_size]; norm_num) h
  · have h := conj_d_conjPt hk1
    rw [hkd, mul_inv_eq_iff_eq_mul] at h
    exact h.symm

theorem mem_ea_of_mem_star
    {x : J} (hx : x ∈ star) : ∃ k ∈ ea, x = conjPt k := by
  obtain ⟨hxD, hxd, hxc⟩ := hx
  obtain ⟨⟨k, hk⟩, rfl⟩ := (isConj_d_iff x).1 hxD
  refine ⟨k, mem_ea.2 ⟨hk, fun h0 => hxd ?_, ?_⟩, rfl⟩
  · simp only [h0, conjPt_zero]
  · have h := conj_d_conjPt hk
    rw [← hxc, mul_inv_cancel_right] at h
    have hlt : ap dT k < 31671 := by rw [rep_dT k hk]; exact idx_lt d hk
    exact conjPt_inj (by rw [orb_size]; exact hlt) (by rw [orb_size]; exact hk) h.symm

noncomputable def posFun
    (i : Fin 3510) : star :=
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
    refine ⟨⟨ePos[k]!, (ePos_lt_iff (mem_ea.1 hk).1).2 hk⟩, ?_⟩
    apply Subtype.ext
    show conjPt ea[ePos[k]!]! = conjPt k
    rw [ea_ePos hk]

noncomputable def posEquiv :
    Fin 3510 ≃ star := Equiv.ofBijective posFun posFun_bijective

theorem posEquiv_apply
    (i : Fin 3510) : (posEquiv i : J) = conjPt ea[i.val]! := by
  simp only [posEquiv, posFun, Equiv.ofBijective_apply]

theorem phiD_lt
    {i : ℕ} (hi : i < 3510) : phiD[i]! < 3510 := (centCert_parts.2.2.1 i hi).1

noncomputable def phiFun
    (i : Fin 3510) : Fin 3510 := ⟨phiD[i.val]!, phiD_lt i.2⟩

theorem phiFun_injective :
    Function.Injective phiFun := by
  intro i j h
  apply Fin.ext
  rw [← (centCert_parts.2.2.1 i.val i.2).2, ← (centCert_parts.2.2.1 j.val j.2).2]
  exact congrArg (fun u => phiP[u]!) (congrArg Fin.val h)

noncomputable def phiEquiv :
    Fin 3510 ≃ Fin 3510 :=
  Equiv.ofBijective phiFun (Finite.injective_iff_bijective.1 phiFun_injective)

theorem phiEquiv_apply
    (i : Fin 3510) : (phiEquiv i).val = phiD[i.val]! := by
  simp only [phiEquiv, phiFun, Equiv.ofBijective_apply]

theorem phiEquiv_symm_val
    (u : Fin 3510) : (phiEquiv.symm u).val = phiP[u.val]! := by
  obtain ⟨i, rfl⟩ := phiEquiv.surjective u
  rw [Equiv.symm_apply_apply, phiEquiv_apply, (centCert_parts.2.2.1 i.val i.2).2]

theorem phiP_lt
    {k : ℕ} (hk : k < 3510) : phiP[k]! < 3510 := by
  rw [← phiEquiv_symm_val ⟨k, hk⟩]
  exact (phiEquiv.symm _).2

theorem phiD_phiP
    {k : ℕ} (hk : k < 3510) : phiD[phiP[k]!]! = k := by
  rw [← phiEquiv_symm_val ⟨k, hk⟩, ← phiEquiv_apply, Equiv.apply_symm_apply]

noncomputable def ptE :
    Fin 3510 ≃ star := phiEquiv.symm.trans posEquiv

theorem ptE_apply
    (u : Fin 3510) : (ptE u : J) = conjPt ea[phiP[u.val]!]! := by
  rw [ptE, Equiv.trans_apply, posEquiv_apply, phiEquiv_symm_val]

theorem ptE_symm_posEquiv
    (j : Fin 3510) : ptE.symm (posEquiv j) = phiEquiv j := by
  rw [Equiv.symm_apply_eq, ptE, Equiv.trans_apply, Equiv.symm_apply_apply]

noncomputable abbrev Cd : Subgroup J := Subgroup.centralizer {d}

theorem mem_Cd
    {g : J} : g ∈ Cd ↔ g * d = d * g := Subgroup.mem_centralizer_singleton_iff

theorem conj_mem_star
    {g : J} (hg : g ∈ Cd) {x : J} (hx : x ∈ star) : g * x * g⁻¹ ∈ star := by
  obtain ⟨hxD, hxd, hxc⟩ := hx
  have hgd := mem_Cd.1 hg
  have hgdg : g⁻¹ * d * g = d := by rw [mul_assoc, ← hgd, ← mul_assoc, inv_mul_cancel, one_mul]
  refine ⟨(hxD : IsConj d x).trans (isConj_iff.2 ⟨g, rfl⟩), fun h => hxd ?_, ?_⟩
  · have : x = g⁻¹ * d * g := by rw [← h]; group
    rw [this, hgdg]
  · calc g * x * g⁻¹ * d = g * x * (g⁻¹ * d * g) * g⁻¹ := by group
      _ = g * x * d * g⁻¹ := by rw [hgdg]
      _ = g * d * x * g⁻¹ := by rw [mul_assoc g x d, hxc, ← mul_assoc]
      _ = d * (g * x * g⁻¹) := by rw [hgd]; group

noncomputable instance starAction : MulAction Cd star where
  smul g x := ⟨(g : J) * x * (g : J)⁻¹, conj_mem_star g.2 x.2⟩
  one_smul x := Subtype.ext (show ((1 : Cd) : J) * (x : J) * ((1 : Cd) : J)⁻¹ = x by simp)
  mul_smul g h x := Subtype.ext (show ((g * h : Cd) : J) * (x : J) * ((g * h : Cd) : J)⁻¹ =
      (g : J) * ((h : J) * x * (h : J)⁻¹) * (g : J)⁻¹ by
    rw [Subgroup.coe_mul, mul_inv_rev]; group)

theorem starAction_val
    (g : Cd) (x : star) : ((g • x : star) : J) = (g : J) * x * (g : J)⁻¹ :=
  rfl

noncomputable instance ptAction :
    MulAction Cd (Fin 3510) := Equiv.mulAction Cd ptE

noncomputable abbrev rho :
    Cd →* Equiv.Perm (Fin 3510) := MulAction.toPermHom Cd (Fin 3510)

theorem rho_apply
    (g : Cd) (u : Fin 3510) : rho g u = ptE.symm (g • ptE u) := by
  rw [MulAction.toPermHom_apply, MulAction.toPerm_apply]
  exact Equiv.smul_def ptE g u

noncomputable abbrev pi22 : Fi22.J →* Equiv.Perm (Fin 3510) :=
  MulAction.toPermHom Fi22.J (Fin 3510)

theorem pi22_injective :
    Function.Injective pi22 := MulAction.toPerm_injective

theorem pi22_apply_val
    (g : Fi22.J) (u : Fin 3510) : (pi22 g u).val = idx 3510 g u.val := by
  rw [MulAction.toPermHom_apply, MulAction.toPerm_apply, idx_of_lt _ u.2]

theorem card_range_pi22 : Nat.card pi22.range = 64561751654400 := by
  rw [← Fi22.card_J]
  exact Nat.card_congr (MonoidHom.ofInjective pi22_injective).toEquiv.symm

@[expose] noncomputable def starCd
    (i : ℕ) (hi : i < 3510) : Cd :=
  ⟨conjPt ea[i]!, mem_Cd.2 (star_commute (conjPt_mem_star (ea_get_mem hi)))⟩

theorem starCd_val
    (i : ℕ) (hi : i < 3510) : (starCd i hi : J) = conjPt ea[i]! := rfl

theorem rho_starCd
    (i : ℕ) (hi : i < 3510) :
    rho (starCd i hi) = pi22 (Fi22.conjPt phiD[i]!) := by
  ext u
  have hj := phiP_lt u.2
  have hm := ea_get_lt hj
  have hidx : act23 ea[i]! ea[phiP[u.val]!]! = idx 31671 (conjPt ea[i]!) ea[phiP[u.val]!]! :=
    act23_spec _ _ hm
  have hlt : act23 ea[i]! ea[phiP[u.val]!]! < 31671 := by rw [hidx]; exact idx_lt _ hm
  have hconj : conjPt ea[i]! * conjPt ea[phiP[u.val]!]! * (conjPt ea[i]!)⁻¹ =
      conjPt (act23 ea[i]! ea[phiP[u.val]!]!) := (idx_eq_iff hm hlt).1 hidx.symm
  have hmem : act23 ea[i]! ea[phiP[u.val]!]! ∈ ea := by
    have := conj_mem_star (starCd i hi).2 (conjPt_mem_star (ea_get_mem hj))
    rw [starCd_val, hconj] at this
    obtain ⟨k, hk, hke⟩ := mem_ea_of_mem_star this
    rw [conjPt_inj (by rw [orb_size]; exact hlt) (by rw [orb_size]; exact (mem_ea.1 hk).1) hke]
    exact hk
  have hpos := (ePos_lt_iff hlt).2 hmem
  have hstar : starCd i hi • ptE u = posEquiv ⟨ePos[act23 ea[i]! ea[phiP[u.val]!]!]!, hpos⟩ := by
    apply Subtype.ext
    rw [starAction_val, ptE_apply, posEquiv_apply, ea_ePos hmem, starCd_val]
    exact hconj
  rw [rho_apply, hstar, ptE_symm_posEquiv, phiEquiv_apply, centCert_parts.2.2.2.1 i hi _ hj,
    phiD_phiP u.2, act22_spec _ _ u.2, pi22_apply_val]

theorem rho_star
    (x : Cd) (hx : (x : J) ∈ star) :
    ∃ k < 3510, rho x = pi22 (Fi22.conjPt k) := by
  obtain ⟨k, hk, hke⟩ := mem_ea_of_mem_star hx
  have hi := (ePos_lt_iff (mem_ea.1 hk).1).2 hk
  refine ⟨_, phiD_lt hi, ?_⟩
  rw [← rho_starCd _ hi]
  congr 1
  apply Subtype.ext
  rw [starCd_val, ea_ePos hk, hke]

noncomputable abbrev Hloc :
    Subgroup Cd := (LocalGroup D23 d).subgroupOf Cd

theorem starCd_mem
    (i : ℕ) (hi : i < 3510) : starCd i hi ∈ Hloc :=
  Subgroup.mem_subgroupOf.2 (Subgroup.subset_closure (conjPt_mem_star (ea_get_mem hi)))

theorem pi22_conjPt_mem
    {k : ℕ} (hk : k < 3510) : pi22 (Fi22.conjPt k) ∈ Hloc.map rho :=
  ⟨starCd _ (phiP_lt hk), starCd_mem _ (phiP_lt hk), by rw [rho_starCd, phiD_phiP hk]⟩

theorem range_pi22_le :
    pi22.range ≤ Hloc.map rho := by
  rw [MonoidHom.range_eq_map, ← Fi22.closure_D, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨k, hk, rfl⟩ := Fi22.mem_D_iff.1 hx
  exact pi22_conjPt_mem hk

@[expose] noncomputable def dCd : Cd := ⟨d, mem_Cd.2 rfl⟩

theorem dCd_val : (dCd : J) = d := rfl

theorem rho_dCd : rho dCd = 1 := by
  ext u
  rw [rho_apply]
  have : dCd • ptE u = ptE u := by
    apply Subtype.ext
    rw [starAction_val, dCd_val, ← star_commute (ptE u).2, mul_inv_cancel_right]
  rw [this, Equiv.symm_apply_apply, Equiv.Perm.one_apply]

theorem orderOf_dCd :
    orderOf dCd = 2 := by
  rw [← orderOf_injective Cd.subtype Subtype.val_injective dCd]
  exact orderOf_d

theorem card_range_mul_card_ker :
    Nat.card rho.range * Nat.card rho.ker = 129123503308800 := by
  rw [← card_centralizer_d, Subgroup.card_eq_card_quotient_mul_card_subgroup rho.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange rho).toEquiv]

theorem two_le_card_ker :
    2 ≤ Nat.card rho.ker := by
  rw [← orderOf_dCd, ← Nat.card_zpowers]
  exact Subgroup.card_le_of_le (Subgroup.zpowers_le.2 rho_dCd)

theorem range_rho :
    rho.range = pi22.range := by
  symm
  apply Subgroup.eq_of_le_of_card_ge (range_pi22_le.trans (Subgroup.map_le_range _ _))
  rw [card_range_pi22]
  have h2 : Nat.card rho.range * 2 ≤ 129123503308800 :=
    card_range_mul_card_ker ▸ Nat.mul_le_mul_left _ two_le_card_ker
  omega

theorem card_ker_rho :
    Nat.card rho.ker = 2 := by
  have h1 := card_range_mul_card_ker
  rw [range_rho, card_range_pi22] at h1
  omega

theorem ker_rho :
    rho.ker = Subgroup.zpowers dCd :=
  (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 rho_dCd)
    (by rw [card_ker_rho, Nat.card_zpowers, orderOf_dCd])).symm

theorem pi22_mem_range
    (g : Fi22.J) : pi22 g ∈ rho.range := by
  rw [range_rho]
  exact ⟨g, rfl⟩

theorem rep_unique
    {T : Table} {g h : J} (hg : Rep 31671 T g) (hh : Rep 31671 T h) : g = h := by
  have : h⁻¹ * g = 1 := eq_one_of_fix_all fun i => by
    have e : g • i = h • i := by
      apply Fin.ext
      have e := (hg i.val i.2).symm.trans (hh i.val i.2)
      rw [idx_of_lt _ i.2, idx_of_lt _ i.2] at e
      exact e
    rw [mul_smul, e, inv_smul_smul]
  rw [inv_mul_eq_one] at this
  exact this.symm

theorem rep_actTab
    (k : ℕ) : Rep 31671 (treeActTab orb dT biT k) (conjPt k) := by
  intro m hm
  have h := act23_spec k m hm
  have hlt : act23 k m < 2 ^ 32 := by rw [h]; exact (idx_lt _ hm).trans (by norm_num)
  unfold treeActTab
  rw [ap_ofFn _ hm, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hlt, h]

theorem rep_wordTab
    (w : List ℕ) : Rep 31671 (starWordTab orb dT biT w) (w.map conjPt).prod := by
  induction w with
  | nil => simpa [starWordTab] using Rep.idT (G := J) (n := 31671) (by norm_num)
  | cons k w ih =>
    rw [starWordTab, List.foldr_cons, List.map_cons, List.prod_cons]
    exact (rep_actTab k).compT ih

theorem d_eq_word :
    ((starWord.map conjPt).prod) ^ 11 = d := by
  have h := (rep_wordTab starWord).powT (by norm_num) 11
  rw [centCert_parts.2.2.2.2.2] at h
  exact rep_unique h rep_dT

@[expose] noncomputable def ofStar
    (x : star) : Cd := ⟨x, mem_Cd.2 (star_commute x.2)⟩

theorem ofStar_val (x : star) : (ofStar x : J) = x := rfl

theorem star_transitive
    (x y : star) : ∃ c : Cd, c • x = y := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Fi22.J (ptE.symm x) (ptE.symm y)
  obtain ⟨c, hc⟩ := pi22_mem_range g
  refine ⟨c, ptE.symm.injective ?_⟩
  have h : rho c (ptE.symm x) = pi22 g (ptE.symm x) := by rw [hc]
  rw [rho_apply, Equiv.apply_symm_apply, MulAction.toPermHom_apply, MulAction.toPerm_apply,
    hg] at h
  exact h

theorem ofStar_mul_mem
    (x y : star) : ofStar x * ofStar y ∈ commutator Cd := by
  obtain ⟨c, hc⟩ := star_transitive x y
  have hy : ofStar y = c * ofStar x * c⁻¹ := by
    apply Subtype.ext
    rw [← hc, ofStar_val, starAction_val]
    rfl
  have hx2 : (ofStar x)⁻¹ = ofStar x := by
    rw [inv_eq_iff_mul_eq_one]
    apply Subtype.ext
    have h2 := pow_orderOf_eq_one (x : J)
    rw [orderOf_of_isConj x.2.1, pow_two] at h2
    exact h2
  have e : ofStar x * ofStar y = ⁅ofStar x, c⁆ := by
    rw [hy, commutatorElement_def, hx2]
    group
  rw [e, _root_.commutator_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem word_mem_commutator :
    ∀ (w : List ℕ), (∀ k ∈ w, k ∈ ea) → w.length % 2 = 0 →
    ∃ c ∈ commutator Cd, (c : J) = (w.map conjPt).prod
  | [], _, _ => ⟨1, Subgroup.one_mem _, by simp⟩
  | [_], _, h => absurd h (by simp)
  | k :: k' :: w, hw, h => by
    have hlen : w.length % 2 = 0 := by
      simp only [List.length_cons] at h
      omega
    obtain ⟨c, hc, hce⟩ := word_mem_commutator w (fun j hj => hw j (by simp [hj])) hlen
    have hk := conjPt_mem_star (hw k (by simp))
    have hk' := conjPt_mem_star (hw k' (by simp))
    refine ⟨ofStar ⟨_, hk⟩ * ofStar ⟨_, hk'⟩ * c,
      Subgroup.mul_mem _ (ofStar_mul_mem _ _) hc, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hce, ofStar_val, ofStar_val, List.map_cons,
      List.map_cons, List.prod_cons, List.prod_cons, mul_assoc]

theorem dCd_mem_commutator :
    dCd ∈ commutator Cd := by
  obtain ⟨c, hc, hce⟩ := word_mem_commutator starWord centCert_parts.2.2.2.2.1 (by decide)
  have : dCd = c ^ 11 := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, hce, d_eq_word, dCd_val]
  rw [this]
  exact Subgroup.pow_mem _ hc 11

theorem d_mem_localGroup :
    d ∈ LocalGroup D23 d := by
  have h : ((starWord.map conjPt).prod) ^ 11 ∈ LocalGroup D23 d := by
    apply Subgroup.pow_mem
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    exact Subgroup.subset_closure (conjPt_mem_star (centCert_parts.2.2.2.2.1 k hk))
  rwa [d_eq_word] at h

theorem dCd_mem_Hloc :
    dCd ∈ Hloc := Subgroup.mem_subgroupOf.2 d_mem_localGroup

theorem Hloc_eq_top :
    Hloc = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hg : rho g ∈ Hloc.map rho := range_pi22_le (by rw [← range_rho]; exact ⟨g, rfl⟩)
  obtain ⟨h, hh, hgh⟩ := hg
  have hk : h⁻¹ * g ∈ rho.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hgh, inv_mul_cancel]
  rw [ker_rho] at hk
  have hk' : h⁻¹ * g ∈ Hloc := (Subgroup.zpowers_le.2 dCd_mem_Hloc) hk
  have := Hloc.mul_mem hh hk'
  rwa [mul_inv_cancel_left] at this

theorem localGroup_eq :
    LocalGroup D23 d = Subgroup.centralizer ({d} : Set J) := by
  apply le_antisymm
  · rw [LocalGroup, Subgroup.closure_le]
    intro x hx
    exact mem_Cd.2 (star_commute hx)
  · intro g hg
    have : (⟨g, hg⟩ : Cd) ∈ Hloc := by rw [Hloc_eq_top]; trivial
    exact Subgroup.mem_subgroupOf.1 this

theorem center_C :
    Subgroup.center (Subgroup.centralizer ({d} : Set J)) = Subgroup.zpowers dCd := by
  apply le_antisymm
  · intro z hz
    rw [← ker_rho, MonoidHom.mem_ker]
    obtain ⟨g, hg⟩ : rho z ∈ pi22.range := by rw [← range_rho]; exact ⟨z, rfl⟩
    have hgc : g ∈ Subgroup.center Fi22.J := by
      rw [Subgroup.mem_center_iff]
      intro h
      obtain ⟨c, hc⟩ := pi22_mem_range h
      apply pi22_injective
      rw [map_mul, map_mul, hg, ← hc, ← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz c]
    rw [Fi22.center_eq_bot, Subgroup.mem_bot] at hgc
    rw [← hg, hgc, map_one]
  · rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
    intro c
    exact Subtype.ext (mem_Cd.1 c.2)

theorem card_center_C :
    Nat.card (Subgroup.center (Subgroup.centralizer ({d} : Set J))) = 2 := by
  rw [center_C, Nat.card_zpowers, orderOf_dCd]

theorem center_C_map :
    (Subgroup.center (Subgroup.centralizer ({d} : Set J))).map
      (Subgroup.centralizer ({d} : Set J)).subtype = Subgroup.zpowers d := by
  rw [center_C, MonoidHom.map_zpowers]
  rfl

theorem commutator_C :
    commutator (Subgroup.centralizer ({d} : Set J)) = ⊤ := by
  have hmap : (commutator Cd).map rho = rho.range := by
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, range_rho,
      MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← _root_.commutator_def,
      Fi22.commutator_eq_top]
  rw [eq_top_iff]
  intro g _
  have hg : rho g ∈ (commutator Cd).map rho := by rw [hmap]; exact ⟨g, rfl⟩
  obtain ⟨c, hc, hcg⟩ := hg
  have hk : c⁻¹ * g ∈ rho.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hcg, inv_mul_cancel]
  rw [ker_rho] at hk
  have hk' : c⁻¹ * g ∈ commutator Cd := (Subgroup.zpowers_le.2 dCd_mem_commutator) hk
  have := Subgroup.mul_mem _ hc hk'
  rwa [mul_inv_cancel_left] at this

theorem pi22_ofInjective_symm (x : pi22.range) :
    pi22 ((MonoidHom.ofInjective pi22_injective).symm x) = x := by
  conv_rhs => rw [← (MonoidHom.ofInjective pi22_injective).apply_symm_apply x]
  rw [MonoidHom.ofInjective_apply]

noncomputable def quotCenterEquiv :
    Subgroup.centralizer ({d} : Set J) ⧸ Subgroup.center (Subgroup.centralizer ({d} : Set J)) ≃*
      Fi22.J :=
  (QuotientGroup.quotientMulEquivOfEq (center_C.trans ker_rho.symm)).trans
    ((QuotientGroup.quotientKerEquivRange rho).trans
      ((MulEquiv.subgroupCongr range_rho).trans (MonoidHom.ofInjective pi22_injective).symm))

theorem pi22_quotCenterEquiv
    (c : Cd) :
    pi22 (quotCenterEquiv (c : Cd ⧸ Subgroup.center Cd)) = rho c := by
  unfold quotCenterEquiv
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    QuotientGroup.quotientMulEquivOfEq_mk, pi22_ofInjective_symm, MulEquiv.subgroupCongr_apply]
  rfl

noncomputable def localGroupEquiv :
    LocalGroup D23 d ≃* Cd := MulEquiv.subgroupCongr localGroup_eq

theorem localGroupEquiv_val
    (f : LocalGroup D23 d) : (localGroupEquiv f : J) = f :=
  MulEquiv.subgroupCongr_apply _ _

theorem map_center_localGroupEquiv :
    (Subgroup.center (LocalGroup D23 d)).map (localGroupEquiv : LocalGroup D23 d →* Cd) =
      Subgroup.center Cd := by
  simp

noncomputable def localQuotientEquiv :
    LocalQuotient D23 d ≃* Fi22.J :=
  (QuotientGroup.congr (Subgroup.center (LocalGroup D23 d)) (Subgroup.center Cd) localGroupEquiv
    map_center_localGroupEquiv).trans quotCenterEquiv

theorem pi22_localQuotientEquiv
    (f : LocalGroup D23 d) :
    pi22 (localQuotientEquiv (f : LocalQuotient D23 d)) = rho (localGroupEquiv f) := by
  unfold localQuotientEquiv
  rw [MulEquiv.trans_apply, QuotientGroup.congr_mk, pi22_quotCenterEquiv]

theorem localQuotientEquiv_image :
    localQuotientEquiv '' LocalImages D23 d = Fi22.D := by
  ext x
  constructor
  · rintro ⟨q, ⟨f, hf, rfl⟩, rfl⟩
    obtain ⟨k, hk, hrho⟩ := rho_star (localGroupEquiv f) (by rw [localGroupEquiv_val]; exact hf)
    have h := pi22_localQuotientEquiv f
    rw [hrho] at h
    rw [pi22_injective h]
    exact Fi22.mem_D_iff.2 ⟨k, hk, rfl⟩
  · intro hx
    obtain ⟨k, hk, rfl⟩ := Fi22.mem_D_iff.1 hx
    have hi := phiP_lt hk
    have hf : conjPt ea[phiP[k]!]! ∈ LocalGroup D23 d :=
      Subgroup.subset_closure (conjPt_mem_star (ea_get_mem hi))
    refine ⟨((⟨_, hf⟩ : LocalGroup D23 d) : LocalQuotient D23 d),
      ⟨⟨_, hf⟩, conjPt_mem_star (ea_get_mem hi), rfl⟩, ?_⟩
    apply pi22_injective
    have e : localGroupEquiv ⟨_, hf⟩ = starCd _ hi := by
      apply Subtype.ext
      rw [localGroupEquiv_val, starCd_val]
    rw [pi22_localQuotientEquiv, e, rho_starCd, phiD_phiP hk]

end CFSG.Sporadic.Fi23
