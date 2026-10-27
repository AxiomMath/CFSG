module

public import CFSG.Quasithin.H13.AS91Sec3Twelve
public import Certificates.Certificate89021

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.AS91.M24G

open CFSG.ASVolI.ChH CFSG.Quasithin.H.Mathieu CFSG.Monster.Code

@[expose] noncomputable def setClass (T : Finset (Fin 24)) : W11 := cocodeCoords.κ (eY T)

@[expose] noncomputable def sextClass (U : Finset (Finset (Fin 24))) : W11 :=
  if h : U.Nonempty then setClass h.choose else 1

theorem W11_mul_self (w : W11) : w * w = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  simp only [toAdd_mul, Pi.add_apply, toAdd_one, Pi.zero_apply]
  exact CharTwo.add_self_eq_zero _

private theorem eY_union_of_disjoint {S T : Finset (Fin 24)} (h : Disjoint S T) :
    eY (S ∪ T) = eY S * eY T := by
  apply Multiplicative.toAdd.injective
  funext i
  simp only [toAdd_mul, Pi.add_apply, toAdd_eY, Finset.mem_union]
  by_cases hS : i ∈ S
  · have hT : i ∉ T := fun hT => Finset.disjoint_left.1 h hS hT
    simp [hS, hT]
  · by_cases hT : i ∈ T <;> simp [hS, hT]

private theorem eY_mem_coreMod {T : Finset (Fin 24)} (hT : Even T.card) :
    eY T ∈ G6.coreMod 24 := by
  rw [mem_coreMod_iff, sum_toAdd_eY]
  exact (ZMod.natCast_eq_zero_iff_even).2 hT

theorem setClass_eq_of_octad {S T : Finset (Fin 24)} (hS : Even S.card) (hT : Even T.card)
    (hd : Disjoint S T) (hO : IsOctad (S ∪ T)) : setClass S = setClass T := by
  have h1 : cocodeCoords.κ (eY S * eY T) = 1 := by
    refine (cocodeCoords.ker_iff _ ?_).2 ?_
    · exact (G6.coreMod 24).mul_mem (eY_mem_coreMod hS) (eY_mem_coreMod hT)
    · rw [← eY_union_of_disjoint hd]
      exact hO.2
  rw [map_mul] at h1
  have h2 : setClass T * setClass T = 1 := W11_mul_self _
  have h3 : setClass S = (setClass T)⁻¹ := eq_inv_of_mul_eq_one_left h1
  rw [h3]
  exact inv_eq_of_mul_eq_one_right h2

theorem sextClass_eq {U : Finset (Finset (Fin 24))} (hU : IsSextet U) {T : Finset (Fin 24)}
    (hT : T ∈ U) : sextClass U = setClass T := by
  have hne : U.Nonempty := ⟨T, hT⟩
  rw [sextClass, dif_pos hne]
  set T₀ := hne.choose with hT₀
  have hT₀U : T₀ ∈ U := hne.choose_spec
  by_cases h : T₀ = T
  · rw [h]
  · exact setClass_eq_of_octad (by rw [hU.2.1 T₀ hT₀U]; decide) (by rw [hU.2.1 T hT]; decide)
      (hU.2.2.1 T₀ hT₀U T hT h) (hU.2.2.2.2 T₀ hT₀U T hT h)

theorem setClass_smul {σ : S24} (hσ : σ ∈ M24g) {T : Finset (Fin 24)} (hT : Even T.card) :
    setClass (σ • T) = rho11 AutPerm le_rfl ⟨σ, hσ⟩ (setClass T) := by
  unfold setClass
  rw [smul_finset_eq_map, ← permAct_eY]
  exact cocodeCoords.κ_permAct_rho AutPerm (fun _ hσ => preserves_cocode hσ) ⟨σ, hσ⟩
    (eY_mem_coreMod hT)

private theorem sextet_nonempty {U : Finset (Finset (Fin 24))} (hU : IsSextet U) : U.Nonempty := by
  rw [← Finset.card_pos, hU.1]
  norm_num

theorem sextClass_smul {σ : S24} (hσ : σ ∈ M24g) {U : Finset (Finset (Fin 24))}
    (hU : IsSextet U) :
    sextClass (σ • U) = rho11 AutPerm le_rfl ⟨σ, hσ⟩ (sextClass U) := by
  obtain ⟨T, hT⟩ := sextet_nonempty hU
  rw [sextClass_eq hU hT, sextClass_eq ((isSextet_smul_iff hσ).2 hU)
    (Finset.smul_mem_smul_finset hT)]
  exact setClass_smul hσ (by rw [hU.2.1 T hT]; decide)

theorem sextClass_ne_one {U : Finset (Finset (Fin 24))} (hU : IsSextet U) : sextClass U ≠ 1 := by
  obtain ⟨T, hT⟩ := sextet_nonempty hU
  rw [sextClass_eq hU hT, setClass]
  intro h
  have h4 := hU.2.1 T hT
  have h1 := (cocodeCoords.ker_iff _ (eY_mem_coreMod (by rw [h4]; decide))).1 h
  have h2 := (eY_mem_golayC_iff T (by omega)).1 h1
  rw [h2] at h4
  simp at h4

theorem treeValid_get {α : Type} [Inhabited α] [DecidableEq α] {valid : α → Bool}
    {steps : List (α → α)} {base : α} {r : Array α × Array ℕ × Array ℕ}
    (h : Native.treeValid valid steps base r = true) :
    0 < r.1.size ∧ r.1[0]! = base ∧ ∀ j < r.1.size, valid r.1[j]! = true ∧
      (j = 0 ∨ (r.2.1[j]! < j ∧ r.2.2[j]! < steps.length ∧
        (steps.getD r.2.2[j]! id) r.1[r.2.1[j]!]! = r.1[j]!)) := by
  unfold Native.treeValid at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Native.allLt_iff,
    Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, h5⟩ := h
  refine ⟨h1, h2, fun j hj => ?_⟩
  obtain ⟨hv, hj'⟩ := h5 j hj
  refine ⟨hv, ?_⟩
  rcases hj' with h0 | ⟨⟨h3, h4⟩, h6⟩
  · exact Or.inl h0
  · exact Or.inr ⟨h3, h4, h6⟩

theorem exists_smul_of_tree {G X : Type*} {α : Type} [Group G] [MulAction G X] [Inhabited α]
    [DecidableEq α] (H : Subgroup G) {m : ℕ} (P : Fin m → G) (hP : ∀ j, P j ∈ H)
    {valid : α → Bool} {steps : List (α → α)} (hm : steps.length = m) (f : α → X)
    (hstep : ∀ (j : Fin m) (a : α), valid a = true → f (steps.getD j id a) = P j • f a)
    {base : α} {r : Array α × Array ℕ × Array ℕ}
    (h : Native.treeValid valid steps base r = true) :
    ∀ q ∈ r.1.toList, ∃ σ ∈ H, σ • f base = f q := by
  obtain ⟨-, h0, hall⟩ := treeValid_get h
  have key : ∀ j, j < r.1.size → ∃ σ ∈ H, σ • f base = f r.1[j]! := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      rcases (hall j hj).2 with rfl | ⟨hpar, hgen, hstp⟩
      · exact ⟨1, H.one_mem, by rw [one_smul, h0]⟩
      · obtain ⟨σ, hσ, hσf⟩ := ih r.2.1[j]! hpar (lt_trans hpar hj)
        have hv := (hall r.2.1[j]! (lt_trans hpar hj)).1
        have hgm : r.2.2[j]! < m := hm ▸ hgen
        refine ⟨P ⟨r.2.2[j]!, hgm⟩ * σ, H.mul_mem (hP _) hσ, ?_⟩
        have hs := hstep ⟨r.2.2[j]!, hgm⟩ r.1[r.2.1[j]!]! hv
        rw [mul_smul, hσf, ← hs]
        exact congrArg f hstp
  intro q hq
  obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 (Array.mem_toList_iff.1 hq)
  obtain ⟨σ, hσ, hσf⟩ := key j hj
  exact ⟨σ, hσ, by rw [hσf, getElem!_pos r.1 j hj]⟩

@[expose] def clsMask (q : ℕ) : ℕ := Native.clsOf (Native.sextList ())[q]!

section Spec


theorem s0Fix_spec : ∀ g ∈ Native.s0Tabs, Native.img g 255 = 255 ∧
    Native.imgTrio g Native.baseTrio = Native.baseTrio ∧
    Native.imgSext g Native.baseSext = Native.baseSext ∧
    Native.imgSext g Native.pairPart = Native.pairPart :=
  Certificates.certificate89021.1

theorem tripleOrbit_spec : ∃ r : Array (ℕ × ℕ × ℕ) × Array ℕ × Array ℕ,
    Native.treeValid Native.validTriple (Native.s0Tabs.map Native.imgTriple) (0, 8, 16) r = true ∧
      1024 ≤ r.1.size ∧ (r.1.toList.map Native.keyTriple).Nodup :=
  Certificates.certificate89021.2.1

theorem tupleOrbit_spec : ∃ r : Array Native.OSP × Array ℕ × Array ℕ,
    Native.treeValid Native.validOSP (Native.lTabs.map Native.imgOSP) Native.tup0 r = true ∧
      63 ≤ r.1.size ∧ (r.1.toList.map Native.keyOSP).Nodup :=
  Certificates.certificate89021.2.2.1

theorem fixed_spec : (∀ m < 2048, (∀ a ∈ Native.s0Tabs, Native.toddAct a m = m) →
    m = 0 ∨ m = 31) ∧ ∀ a ∈ Native.s0Tabs, Native.toddAct a 31 = 31 :=
  Certificates.certificate89021.2.2.2.1

theorem clsDistinct_spec : (Native.sextList ()).size = 1771 ∧
    (∀ q < 1771, ∀ q' < q, clsMask q ≠ clsMask q') ∧ Native.clsOf Native.baseSext = 31 :=
  Certificates.certificate89021.2.2.2.2.1

theorem trioDet_spec : ∀ p < 3795,
    (∀ q ∈ Native.sextsThrough (Native.sextList ()) Native.baseTrio,
      Native.trioIn (Native.trioList ())[p]! (Native.sextList ())[q]! = true) → p = 0 :=
  Certificates.certificate89021.2.2.2.2.2.1

theorem v0_spec : Native.sortL (0 :: (Native.sextsThrough (Native.sextList ())
      Native.baseTrio).map clsMask) = Native.v0List ∧ Native.closedXor Native.v0List = true ∧
    Native.closedXor Native.vpList = true :=
  Certificates.certificate89021.2.2.2.2.2.2.1

def IsCls (m : ℕ) : Prop := ∃ q < 1771, clsMask q = m

theorem span_spec : ∀ v < 2048, ∀ w < 2048, v ≠ 0 → v ≠ 31 → w ≠ 0 → w ≠ 31 → w ≠ v →
    w ≠ 31 ^^^ v → IsCls v → IsCls (31 ^^^ v) → IsCls w → IsCls (31 ^^^ w) → IsCls (v ^^^ w) →
    IsCls (31 ^^^ v ^^^ w) → (Native.sp8 v w).Nodup ∧
      ((∀ a ∈ Native.s0Tabs, Native.toddAct a v ∈ Native.sp8 v w ∧
          Native.toddAct a w ∈ Native.sp8 v w) →
        Native.sortL (Native.sp8 v w) = Native.v0List ∨
          Native.sortL (Native.sp8 v w) = Native.vpList) :=
  Certificates.certificate89021.2.2.2.2.2.2.2.1

theorem spaceOrbit_spec : ∃ r : Array (List ℕ) × Array ℕ × Array ℕ,
    Native.treeValid Native.validSp (Native.genTabs.map Native.stepSp) Native.vpList r = true ∧
      3796 ≤ r.1.size ∧ (r.1.toList.map Native.keySp).Nodup :=
  Certificates.certificate89021.2.2.2.2.2.2.2.2

end Spec

theorem setClass_maskFin (B : ℕ) : setClass (maskFin B) = toW 11 (actM ccECols B) := by
  unfold setClass
  rw [eY_maskFin]
  show Multiplicative.ofAdd (ccE (bvec 24 B)) = _
  rw [ccE_bvec]
  rfl

theorem clsMask_lt (q : ℕ) : clsMask q < 2 ^ 11 := by
  unfold clsMask Native.clsOf
  rw [actM_eq_actM]
  exact actM_lt ccECols_lt _

section Cert


theorem sextClass_sextFin {q : ℕ} (hq : q < 1771) :
    sextClass (sextFin q) = toW 11 (clsMask q) := by
  obtain ⟨h1, -⟩ := sextList_get hq (rfl : (Native.sextList ())[q]! = _)
  obtain ⟨B, rest, hBr⟩ : ∃ B rest, (Native.sextList ())[q]! = B :: rest := by
    cases hs : (Native.sextList ())[q]! with
    | nil => rw [hs] at h1; simp at h1
    | cons B rest => exact ⟨B, rest, rfl⟩
  have hmem : maskFin B ∈ sextFin q :=
    mem_sextOfL.2 ⟨B, by rw [hBr]; exact List.mem_cons_self, rfl⟩
  rw [sextClass_eq (isSextet_sextFin hq) hmem, setClass_maskFin, clsMask, hBr]
  simp only [Native.clsOf, List.headD_cons]
  exact congrArg (toW 11) (actM_eq_actM _ _).symm

theorem sextClass_inj {U U' : Finset (Finset (Fin 24))} (hU : IsSextet U) (hU' : IsSextet U')
    (h : sextClass U = sextClass U') : U = U' := by
  obtain ⟨q, hq, rfl⟩ := (isSextet_iff U).1 hU
  obtain ⟨q', hq', rfl⟩ := (isSextet_iff U').1 hU'
  rw [sextClass_sextFin hq, sextClass_sextFin hq'] at h
  have h2 : clsMask q = clsMask q' := toW_inj (clsMask_lt q) (clsMask_lt q') h
  rw [show q = q' from ?_]
  rcases lt_trichotomy q q' with hlt | heq | hgt
  · exact absurd h2.symm (clsDistinct_spec.2.1 q' hq' q hlt)
  · exact heq
  · exact absurd h2 (clsDistinct_spec.2.1 q hq q' hgt)

end Cert

@[expose] noncomputable def trioSpace (t : Finset (Finset (Fin 24))) : Subgroup W11 :=
  Subgroup.closure {w | ∃ U, IsSextet U ∧ TrioIn t U ∧ sextClass U = w}

private def QSet (t : Finset (Finset (Fin 24))) : Set W11 :=
  {w | w = 1 ∨ ∃ U, IsSextet U ∧ TrioIn t U ∧ sextClass U = w}

private theorem mem_gen_smul {σ : S24} (hσ : σ ∈ M24g) {t : Finset (Finset (Fin 24))}
    {w : W11} : (∃ U, IsSextet U ∧ TrioIn (σ • t) U ∧ sextClass U = w) ↔
      ∃ w₀, (∃ U, IsSextet U ∧ TrioIn t U ∧ sextClass U = w₀) ∧
        rho11 AutPerm le_rfl ⟨σ, hσ⟩ w₀ = w := by
  constructor
  · rintro ⟨U, hU, htU, rfl⟩
    have hU' : IsSextet (σ⁻¹ • U) := (isSextet_smul_iff (M24g.inv_mem hσ)).2 hU
    refine ⟨sextClass (σ⁻¹ • U), ⟨σ⁻¹ • U, hU', ?_, rfl⟩, ?_⟩
    · have h := (trioIn_smul_iff σ⁻¹).2 htU
      rwa [inv_smul_smul] at h
    · rw [← sextClass_smul hσ hU', smul_inv_smul]
  · rintro ⟨w₀, ⟨U, hU, htU, rfl⟩, rfl⟩
    exact ⟨σ • U, (isSextet_smul_iff hσ).2 hU, (trioIn_smul_iff σ).2 htU,
      sextClass_smul hσ hU⟩

private theorem mem_QSet_smul {σ : S24} (hσ : σ ∈ M24g) {t : Finset (Finset (Fin 24))}
    {w : W11} : w ∈ QSet (σ • t) ↔
      ∃ w₀ ∈ QSet t, rho11 AutPerm le_rfl ⟨σ, hσ⟩ w₀ = w := by
  constructor
  · rintro (rfl | h)
    · exact ⟨1, Or.inl rfl, map_one _⟩
    · obtain ⟨w₀, hw₀, e⟩ := (mem_gen_smul hσ).1 h
      exact ⟨w₀, Or.inr hw₀, e⟩
  · rintro ⟨w₀, rfl | h, rfl⟩
    · exact Or.inl (map_one _)
    · exact Or.inr ((mem_gen_smul hσ).2 ⟨w₀, h, rfl⟩)

theorem trioSpace_smul {σ : S24} (hσ : σ ∈ M24g) {t : Finset (Finset (Fin 24))}
    (_ht : IsTrio t) :
    trioSpace (σ • t) = (trioSpace t).map (rho11 AutPerm le_rfl ⟨σ, hσ⟩).toMonoidHom := by
  unfold trioSpace
  rw [MonoidHom.map_closure]
  congr 1
  ext w
  rw [Set.mem_image]
  exact mem_gen_smul hσ

section Cert2


private theorem closedXor_spec {L : List ℕ} (h : Native.closedXor L = true) :
    ∀ a ∈ L, ∀ b ∈ L, a ^^^ b ∈ L := by
  unfold Native.closedXor at h
  simp only [List.all_eq_true, List.contains_iff_mem, decide_eq_true_eq] at h
  exact h

private theorem mem_sextsThrough_base {q : ℕ} :
    q ∈ Native.sextsThrough (Native.sextList ()) Native.baseTrio ↔
      q < 1771 ∧ TrioIn (trioFin 0) (sextFin q) := by
  unfold Native.sextsThrough
  simp only [List.mem_filter, List.mem_range, Native.nSext]
  constructor
  · rintro ⟨hq, h⟩
    refine ⟨hq, (trioIn_iff zero_lt_3795 hq).1 ?_⟩
    rw [trioList_zero]
    simpa using h
  · rintro ⟨hq, h⟩
    refine ⟨hq, ?_⟩
    have h' := (trioIn_iff zero_lt_3795 hq).2 h
    rw [trioList_zero] at h'
    simpa using h'

private theorem QSet_base_iff {w : W11} :
    w ∈ QSet (trioFin 0) ↔ ∃ m ∈ Native.v0List, toW 11 m = w := by
  obtain ⟨hv0, -, -⟩ := v0_spec
  constructor
  · rintro (rfl | ⟨U, hU, htU, rfl⟩)
    · exact ⟨0, by simp [Native.v0List], toW_zero 11⟩
    · obtain ⟨q, hq, rfl⟩ := (isSextet_iff U).1 hU
      refine ⟨clsMask q, ?_, (sextClass_sextFin hq).symm⟩
      rw [← hv0, mem_sortL]
      exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨q, mem_sextsThrough_base.2 ⟨hq, htU⟩, rfl⟩)
  · rintro ⟨m, hm, rfl⟩
    rw [← hv0, mem_sortL, List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact Or.inl (toW_zero 11)
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hm
      obtain ⟨hq1, hq2⟩ := mem_sextsThrough_base.1 hq
      exact Or.inr ⟨sextFin q, isSextet_sextFin hq1, hq2, sextClass_sextFin hq1⟩

private theorem QSet_mul {t : Finset (Finset (Fin 24))} (ht : IsTrio t) {w w' : W11}
    (hw : w ∈ QSet t) (hw' : w' ∈ QSet t) : w * w' ∈ QSet t := by
  have key : ∀ w w', w ∈ QSet t → w' ∈ QSet t → w * w' ∈ QSet t := by
    refine forall_trio_of_base
      (P := fun t => ∀ w w', w ∈ QSet t → w' ∈ QSet t → w * w' ∈ QSet t) ?_ ?_ ht
    · intro g hg l hl w w' hw hw'
      obtain ⟨w₀, hw₀, rfl⟩ := (mem_QSet_smul hg).1 hw
      obtain ⟨w₁, hw₁, rfl⟩ := (mem_QSet_smul hg).1 hw'
      exact (mem_QSet_smul hg).2 ⟨w₀ * w₁, hl w₀ w₁ hw₀ hw₁, map_mul _ _ _⟩
    · intro w w' hw hw'
      obtain ⟨m, hm, rfl⟩ := QSet_base_iff.1 hw
      obtain ⟨m', hm', rfl⟩ := QSet_base_iff.1 hw'
      rw [← toW_xor]
      exact QSet_base_iff.2 ⟨_, closedXor_spec v0_spec.2.1 m hm m' hm', rfl⟩
  exact key w w' hw hw'

theorem mem_trioSpace {t : Finset (Finset (Fin 24))} (ht : IsTrio t) {w : W11} :
    w ∈ trioSpace t ↔ w = 1 ∨ ∃ U, IsSextet U ∧ TrioIn t U ∧ sextClass U = w := by
  constructor
  · intro h
    have key : w ∈ QSet t := by
      refine Subgroup.closure_induction (p := fun x _ => x ∈ QSet t) (fun x hx => Or.inr hx)
        (Or.inl rfl) (fun x y _ _ hx hy => QSet_mul ht hx hy) (fun x _ hx => ?_) h
      have e : x⁻¹ = x := inv_eq_of_mul_eq_one_right (W11_mul_self x)
      exact (congrArg (· ∈ QSet t) e).mpr hx
    exact key
  · rintro (rfl | h)
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure h

private theorem trioSpace_inj_base {s : Finset (Finset (Fin 24))} (hs : IsTrio s)
    (h : trioSpace (trioFin 0) = trioSpace s) : s = trioFin 0 := by
  obtain ⟨p, hp, rfl⟩ := (isTrio_iff s).1 hs
  have h0 : IsTrio (trioFin 0) := isTrio_trioFin zero_lt_3795
  have hq : ∀ q ∈ Native.sextsThrough (Native.sextList ()) Native.baseTrio,
      Native.trioIn (Native.trioList ())[p]! (Native.sextList ())[q]! = true := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := mem_sextsThrough_base.1 hq
    have hmem : sextClass (sextFin q) ∈ trioSpace (trioFin 0) :=
      (mem_trioSpace h0).2 (Or.inr ⟨sextFin q, isSextet_sextFin hq1, hq2, rfl⟩)
    rw [h] at hmem
    rcases (mem_trioSpace hs).1 hmem with h1 | ⟨U, hU, hpU, hUe⟩
    · exact absurd h1 (sextClass_ne_one (isSextet_sextFin hq1))
    · have hU' := sextClass_inj hU (isSextet_sextFin hq1) hUe
      subst hU'
      exact (trioIn_iff hp hq1).2 hpU
  rw [trioDet_spec p hp hq]

theorem trioSpace_inj {t t' : Finset (Finset (Fin 24))} (ht : IsTrio t) (ht' : IsTrio t')
    (h : trioSpace t = trioSpace t') : t = t' := by
  obtain ⟨g, hg, hgt⟩ := trio_transitive ht
  have hgt' : IsTrio (g • t') := (isTrio_smul_iff hg).2 ht'
  have h1 : trioSpace (trioFin 0) = trioSpace (g • t') := by
    rw [← hgt, trioSpace_smul hg ht, trioSpace_smul hg ht', h]
  have h2 := trioSpace_inj_base hgt' h1
  rw [← hgt] at h2
  exact smul_left_cancel g h2.symm

end Cert2

@[expose] def s0Perm0 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 7, 6, 5, 4, 14, 15, 12, 13, 9, 8, 11, 10, 23, 22, 21, 20, 16, 17, 18, 19]
  invFun :=
    ![0, 1, 2, 3, 7, 6, 5, 4, 13, 12, 15, 14, 10, 11, 8, 9, 20, 21, 22, 23, 19, 18, 17, 16]
  left_inv := by decide
  right_inv := by decide

@[expose] def s0Perm1 : Equiv.Perm (Fin 24) where
  toFun := ![4, 5, 6, 7, 1, 0, 3, 2, 12, 13, 14, 15, 9, 8, 11, 10, 18, 19, 16, 17, 23, 22, 21, 20]
  invFun :=
    ![5, 4, 7, 6, 0, 1, 2, 3, 13, 12, 15, 14, 8, 9, 10, 11, 18, 19, 16, 17, 23, 22, 21, 20]
  left_inv := by decide
  right_inv := by decide

@[expose] def s0Perm2 : Equiv.Perm (Fin 24) where
  toFun := ![4, 5, 7, 6, 1, 0, 2, 3, 12, 13, 15, 14, 9, 8, 10, 11, 23, 22, 20, 21, 18, 19, 17, 16]
  invFun :=
    ![5, 4, 6, 7, 0, 1, 3, 2, 13, 12, 14, 15, 8, 9, 11, 10, 23, 22, 20, 21, 18, 19, 17, 16]
  left_inv := by decide
  right_inv := by decide

@[expose] def s0Perm3 : Equiv.Perm (Fin 24) where
  toFun := ![4, 5, 7, 6, 1, 0, 2, 3, 20, 21, 23, 22, 17, 16, 18, 19, 15, 14, 12, 13, 10, 11, 9, 8]
  invFun :=
    ![5, 4, 6, 7, 0, 1, 3, 2, 23, 22, 20, 21, 18, 19, 17, 16, 13, 12, 14, 15, 8, 9, 11, 10]
  left_inv := by decide
  right_inv := by decide

@[expose] def s0Perm : Fin 4 → Equiv.Perm (Fin 24) := ![s0Perm0, s0Perm1, s0Perm2, s0Perm3]

theorem repT_s0Perm (j : Fin 4) : RepT (Native.s0Tabs.getD j #[]) (s0Perm j) := by
  revert j
  unfold RepT
  decide +kernel

theorem s0Tabs_getD_mem (j : Fin 4) : Native.s0Tabs.getD j #[] ∈ Native.s0Tabs := by
  revert j
  decide +kernel

private theorem s0Perm_basis :
    ∀ (j : Fin 4) (i : Fin 12), CFSG.Monster.Code.B i ∘ ⇑(s0Perm j) ∈ CFSG.Monster.Code.C := by
  decide +kernel

private theorem s0Perm_basis' :
    ∀ (j : Fin 4) (i : Fin 12), CFSG.Monster.Code.B i ∘ ⇑(s0Perm j)⁻¹ ∈ CFSG.Monster.Code.C := by
  decide +kernel

theorem s0Perm_mem (j : Fin 4) : s0Perm j ∈ M24g :=
  mem_AutPerm_of_basis (s0Perm_basis j) (s0Perm_basis' j)

@[expose] def sylS0 : Subgroup S24 := Subgroup.closure (Set.range s0Perm)

theorem s0Perm_mem_sylS0 (j : Fin 4) : s0Perm j ∈ sylS0 := Subgroup.subset_closure ⟨j, rfl⟩

theorem sylS0_le : sylS0 ≤ M24g :=
  (Subgroup.closure_le M24g).2 (by rintro _ ⟨j, rfl⟩; exact s0Perm_mem j)

abbrev Tup3 : Type :=
  Finset (Fin 24) × Finset (Finset (Fin 24)) × Finset (Finset (Fin 24))

@[expose] def tupF (x : Native.OSP) : Tup3 := (maskFin x.1, sextOfL x.2.1, sextOfL x.2.2)

theorem tupF_img {t : Array ℕ} {g : S24} (h : RepT t g) (x : Native.OSP) :
    tupF (Native.imgOSP t x) = g • tupF x := by
  simp only [tupF, Native.imgOSP, Prod.smul_mk, Prod.mk.injEq]
  exact ⟨maskFin_img h x.1, (smul_sextOfL h x.2.1).symm, (smul_sextOfL h x.2.2).symm⟩

theorem sextOfL_inj {u u' : List ℕ} (hu : u.Pairwise (· < ·)) (hu' : u'.Pairwise (· < ·))
    (hlt : ∀ x ∈ u, x < 2 ^ 24) (hlt' : ∀ x ∈ u', x < 2 ^ 24) (h : sextOfL u = sextOfL u') :
    u = u' := by
  apply List.Pairwise.eq_of_mem_iff hu hu'
  intro x
  constructor
  · intro hx
    have hm : maskFin x ∈ sextOfL u' := by
      rw [← h]
      exact mem_sextOfL.2 ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := mem_sextOfL.1 hm
    rw [← maskFin_inj (hlt' y hy) (hlt x hx) hxy]
    exact hy
  · intro hx
    have hm : maskFin x ∈ sextOfL u := by
      rw [h]
      exact mem_sextOfL.2 ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := mem_sextOfL.1 hm
    rw [← maskFin_inj (hlt y hy) (hlt' x hx) hxy]
    exact hy

private theorem validOSP_get {x : Native.OSP} (h : Native.validOSP x = true) :
    x.1 < 2 ^ 24 ∧ (∀ m ∈ x.2.1, m < 2 ^ 24) ∧ (∀ m ∈ x.2.2, m < 2 ^ 24) ∧
      x.2.1.Pairwise (· < ·) ∧ x.2.2.Pairwise (· < ·) := by
  unfold Native.validOSP at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem tupF_inj {x y : Native.OSP} (hx : Native.validOSP x = true)
    (hy : Native.validOSP y = true) (h : tupF x = tupF y) : x = y := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := validOSP_get hx
  obtain ⟨b1, b2, b3, b4, b5⟩ := validOSP_get hy
  simp only [tupF, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  exact Prod.ext (maskFin_inj a1 b1 h1)
    (Prod.ext (sextOfL_inj a4 b4 a2 b2 h2) (sextOfL_inj a5 b5 a3 b3 h3))

theorem treeValid_valid {α : Type} [Inhabited α] [DecidableEq α] {valid : α → Bool}
    {steps : List (α → α)} {base : α} {r : Array α × Array ℕ × Array ℕ}
    (h : Native.treeValid valid steps base r = true) : ∀ q ∈ r.1.toList, valid q = true := by
  obtain ⟨-, -, hall⟩ := treeValid_get h
  intro q hq
  obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 (Array.mem_toList_iff.1 hq)
  rw [← getElem!_pos r.1 j hj]
  exact (hall j hj).1

@[expose] def ptOf (a : ℕ) : Fin 24 := Fin.ofNat 24 a

private theorem ptOf_eq {a : ℕ} (ha : a < 24) : ptOf a = ⟨a, ha⟩ :=
  Fin.ext (by simp [ptOf, Fin.val_ofNat, Nat.mod_eq_of_lt ha])

private theorem ptOf_repT {t : Array ℕ} {g : S24} (h : RepT t g) {a : ℕ} (ha : a < 24) :
    ptOf (t[a]!) = g (ptOf a) := by
  have h1 := h ⟨a, ha⟩
  simp only at h1
  rw [ptOf_eq ha, h1, ptOf]
  simp [Fin.ext_iff, Fin.val_ofNat, Nat.mod_eq_of_lt (g ⟨a, ha⟩).2]

@[expose] def trF (x : ℕ × ℕ × ℕ) : Fin 24 × Fin 24 × Fin 24 :=
  (ptOf x.1, ptOf x.2.1, ptOf x.2.2)

private theorem trF_inj {x y : ℕ × ℕ × ℕ} (hx : Native.validTriple x = true)
    (hy : Native.validTriple y = true) (h : trF x = trF y) : x = y := by
  unfold Native.validTriple at hx hy
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hx hy
  obtain ⟨⟨hx1, hx2⟩, hx3⟩ := hx
  obtain ⟨⟨hy1, hy2⟩, hy3⟩ := hy
  simp only [trF, Prod.mk.injEq, ptOf_eq hx1, ptOf_eq hx2, ptOf_eq hx3, ptOf_eq hy1,
    ptOf_eq hy2, ptOf_eq hy3, Fin.mk.injEq] at h
  exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2)

section Syl


theorem s0Perm_fix_trio (j : Fin 4) : s0Perm j • trioFin 0 = trioFin 0 := by
  obtain ⟨-, h2, -⟩ := s0Fix_spec _ (s0Tabs_getD_mem j)
  rw [smul_trioFin (repT_s0Perm j) (by norm_num : 0 < 3795), trioList_zero, h2, trioFin,
    trioList_zero]

theorem s0Perm_mem_stab (j : Fin 4) : s0Perm j ∈ StabTrio0 :=
  mem_StabTrio0.2 ⟨s0Perm_mem j, s0Perm_fix_trio j⟩

theorem s0Perm_fix_tup (j : Fin 4) : s0Perm j • tupF Native.tup0 = tupF Native.tup0 := by
  obtain ⟨e1, -, e3, e4⟩ := s0Fix_spec _ (s0Tabs_getD_mem j)
  have e : Native.imgOSP (Native.s0Tabs.getD j #[]) Native.tup0 = Native.tup0 := by
    show (Native.img _ 255, Native.imgSext _ Native.baseSext, Native.imgSext _ Native.pairPart) =
      (255, Native.baseSext, Native.pairPart)
    rw [e1, e3, e4]
  rw [← tupF_img (repT_s0Perm j), e]

theorem ncard_orbit_tup0 : 63 ≤ (MulAction.orbit StabTrio0 (tupF Native.tup0)).ncard := by
  obtain ⟨r, hr, hsz, hnd⟩ := tupleOrbit_spec
  have key := exists_smul_of_tree (G := S24) (X := Tup3) StabTrio0 lPerm lPerm_mem_stab
    (valid := Native.validOSP) (steps := Native.lTabs.map Native.imgOSP)
    (by simp [Native.lTabs]) tupF (fun j a _ => by
      rw [getD_map_of_lt _ Native.lTabs #[] id j.2]
      exact tupF_img (repT_lPerm j) a) hr
  set c := r.1.toList with hc
  have hcnd : c.Nodup := List.Nodup.of_map _ hnd
  have hvalid := treeValid_valid hr
  have hsub : ((c.toFinset.image tupF : Finset Tup3) : Set Tup3) ⊆
      MulAction.orbit StabTrio0 (tupF Native.tup0) := by
    intro y hy
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    obtain ⟨σ, hσ, hσq⟩ := key q (List.mem_toFinset.1 hq)
    exact ⟨⟨σ, hσ⟩, hσq⟩
  have hcard : (c.toFinset.image tupF).card = c.length := by
    rw [Finset.card_image_of_injOn, List.toFinset_card_of_nodup hcnd]
    intro x hx y hy hxy
    exact tupF_inj (hvalid x (List.mem_toFinset.1 hx)) (hvalid y (List.mem_toFinset.1 hy)) hxy
  calc 63 ≤ c.length := by simpa [hc] using hsz
    _ = (↑(c.toFinset.image tupF) : Set Tup3).ncard := by rw [Set.ncard_coe_finset, hcard]
    _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)


theorem card_sylS0_le : Nat.card sylS0 ≤ 1024 := by
  have hle : sylS0 ≤ StabTrio0 ⊓ MulAction.stabilizer S24 (tupF Native.tup0) :=
    (Subgroup.closure_le _).2 (by
      rintro _ ⟨j, rfl⟩
      exact ⟨s0Perm_mem_stab j, MulAction.mem_stabilizer_iff.2 (s0Perm_fix_tup j)⟩)
  have hos : Nat.card (MulAction.orbit StabTrio0 (tupF Native.tup0)) *
      Nat.card (MulAction.stabilizer StabTrio0 (tupF Native.tup0)) = Nat.card StabTrio0 := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup StabTrio0 (tupF Native.tup0))
  rw [card_StabTrio0, Nat.card_coe_set_eq] at hos
  have hinj : Nat.card sylS0 ≤ Nat.card (MulAction.stabilizer StabTrio0 (tupF Native.tup0)) := by
    refine Nat.card_le_card_of_injective
      (fun s => ⟨⟨s.1, (hle s.2).1⟩, MulAction.mem_stabilizer_iff.2
        (MulAction.mem_stabilizer_iff.1 (hle s.2).2)⟩) ?_
    intro a b hab
    exact Subtype.ext (congrArg (fun z => (z.1 : S24)) hab)
  have h63 := Nat.mul_le_mul_right
    (Nat.card (MulAction.stabilizer StabTrio0 (tupF Native.tup0))) ncard_orbit_tup0
  omega

theorem card_sylS0_ge : 1024 ≤ Nat.card sylS0 := by
  obtain ⟨r, hr, hsz, hnd⟩ := tripleOrbit_spec
  have key := exists_smul_of_tree (G := S24) (X := Fin 24 × Fin 24 × Fin 24) sylS0 s0Perm
    s0Perm_mem_sylS0 (valid := Native.validTriple) (steps := Native.s0Tabs.map Native.imgTriple)
    (by simp [Native.s0Tabs]) trF (fun j a ha => by
      rw [getD_map_of_lt _ Native.s0Tabs #[] id j.2]
      unfold Native.validTriple at ha
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ha
      obtain ⟨⟨h1, h2⟩, h3⟩ := ha
      have hr := repT_s0Perm j
      simp only [trF, Native.imgTriple, Prod.smul_mk, Equiv.Perm.smul_def]
      rw [ptOf_repT hr h1, ptOf_repT hr h2, ptOf_repT hr h3]) hr
  set c := r.1.toList with hc
  have hcnd : c.Nodup := List.Nodup.of_map _ hnd
  have hvalid := treeValid_valid hr
  set Y : Finset (Fin 24 × Fin 24 × Fin 24) := c.toFinset.image trF with hY
  have hcard : Y.card = c.length := by
    rw [hY, Finset.card_image_of_injOn, List.toFinset_card_of_nodup hcnd]
    intro x hx y hy hxy
    exact trF_inj (hvalid x (List.mem_toFinset.1 hx)) (hvalid y (List.mem_toFinset.1 hy)) hxy
  have hmem : ∀ y : ↥Y, ∃ σ : ↥sylS0, (σ : S24) • trF (0, 8, 16) = y.1 := by
    intro y
    obtain ⟨q, hq, hqy⟩ := Finset.mem_image.1 y.2
    obtain ⟨σ, hσ, hσq⟩ := key q (List.mem_toFinset.1 hq)
    exact ⟨⟨σ, hσ⟩, hσq.trans hqy⟩
  choose g hg using hmem
  have hginj : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    rw [← hg a, ← hg b, hab]
  have h1 := Nat.card_le_card_of_injective g hginj
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, hcard] at h1
  have : c.length = r.1.size := by simp [hc]
  omega

theorem card_sylS0 : Nat.card sylS0 = 2 ^ 10 := by
  have h1 := card_sylS0_le
  have h2 := card_sylS0_ge
  norm_num
  omega

end Syl

section Sylow


theorem exists_conj_sylS0 (P : Subgroup S24) (hP : P ≤ M24g) (hcard : Nat.card P = 2 ^ 10) :
    ∃ g : ↥M24g, ∀ x : ↥M24g, (x : S24) ∈ P ↔ ((g⁻¹ * x * g : ↥M24g) : S24) ∈ sylS0 := by
  have hG : Nat.card ↥M24g = 244823040 := CFSG.Monster.Code.card_AutPerm
  have hfac : (Nat.card ↥M24g).factorization 2 = 10 := by
    rw [hG]
    have : (244823040 : ℕ) = 2 ^ 10 * 239085 := by norm_num
    rw [this, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS0 : Nat.card (sylS0.subgroupOf M24g) = 2 ^ (Nat.card ↥M24g).factorization 2 := by
    rw [hfac, ← card_sylS0]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe sylS0_le).toEquiv
  have hPc : Nat.card (P.subgroupOf M24g) = 2 ^ (Nat.card ↥M24g).factorization 2 := by
    rw [hfac, ← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP).toEquiv
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥M24g (Sylow.ofCard _ hS0) (Sylow.ofCard _ hPc)
  have hQ : P.subgroupOf M24g = MulAut.conj g • sylS0.subgroupOf M24g := by
    have := congrArg (fun Q : Sylow 2 ↥M24g => (Q : Subgroup ↥M24g)) hg
    simpa [Sylow.coe_subgroup_smul] using this.symm
  refine ⟨g, fun x => ?_⟩
  rw [← Subgroup.mem_subgroupOf, hQ, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    Subgroup.mem_subgroupOf]
  exact Iff.rfl

end Sylow

private theorem img_eq_permM {a : Array ℕ} {σ : Equiv.Perm (Fin 24)} (h : RepT a σ) (x : ℕ) :
    Native.img a x = permM a x := by
  have hasarr : HasArr σ a := fun i => (h i).symm
  have hlt : permM a x < 2 ^ 24 := by
    refine actM_lt (cs := permCols a) (fun c hc => ?_) x
    simp only [permCols, List.mem_map, List.mem_range] at hc
    obtain ⟨j, hj, rfl⟩ := hc
    have hj' : a[j]! < 24 := by
      have h1 := h ⟨j, hj⟩
      simp only at h1
      rw [h1]
      exact (σ ⟨j, hj⟩).2
    exact Nat.pow_lt_pow_right (by norm_num) hj'
  apply bvec_inj (img_lt h x) hlt
  rw [← permWord_bvec hasarr x]
  funext i
  have key : (Native.img a x).testBit i = x.testBit ((σ⁻¹ i : Fin 24) : ℕ) := by
    rw [Bool.eq_iff_iff, testBit_img]
    constructor
    · rintro ⟨i', hi', hx, hai⟩
      have h1 := h ⟨i', hi'⟩
      simp only at h1
      have h2 : σ ⟨i', hi'⟩ = i := Fin.ext (h1.symm.trans hai)
      have h3 : (σ⁻¹ i : Fin 24) = ⟨i', hi'⟩ := by rw [← h2]; simp
      rw [h3]
      exact hx
    · intro hx
      refine ⟨((σ⁻¹ i : Fin 24) : ℕ), (σ⁻¹ i).2, hx, ?_⟩
      rw [h (σ⁻¹ i)]
      simp
  simp only [bvec_apply, permWord, Function.comp_apply, key]

private theorem toddAct_eq {a : Array ℕ} {σ : Equiv.Perm (Fin 24)} (h : RepT a σ) (m : ℕ) :
    Native.toddAct a m = act11 a m := by
  have e1 : Native.actM Native.liftEColsN m = actM liftECols m := actM_eq_actM _ _
  rw [Native.toddAct, img_eq_permM h, e1, actM_eq_actM, act11]
  rfl

theorem toddAct_lt {a : Array ℕ} {σ : Equiv.Perm (Fin 24)} (h : RepT a σ) (m : ℕ) :
    Native.toddAct a m < 2048 := by
  rw [toddAct_eq h]
  simpa using act11_lt a m

theorem rho11_toW_native {t : Array ℕ} {g : S24} (hg : g ∈ M24g) (h : RepT t g) (m : ℕ) :
    rho11 AutPerm le_rfl ⟨g, hg⟩ (toW 11 m) = toW 11 (Native.toddAct t m) := by
  rw [toddAct_eq h]
  exact rho11_toW AutPerm le_rfl ⟨g, hg⟩ (fun i => (h i).symm) m

@[expose] noncomputable def rhoG : ↥M24g →* MulAut W11 := rho11 AutPerm le_rfl

noncomputable local instance toddAction : MulAction ↥M24g W11 where
  smul σ w := rhoG σ w
  one_smul w := by
    show rhoG 1 w = w
    rw [map_one]
    rfl
  mul_smul σ τ w := by
    show rhoG (σ * τ) w = rhoG σ (rhoG τ w)
    rw [map_mul]
    rfl

noncomputable local instance spAction : MulAction ↥M24g (Subgroup W11) where
  smul σ H := H.map (rhoG σ).toMonoidHom
  one_smul H := by
    have e : (rhoG 1).toMonoidHom = MonoidHom.id W11 :=
      MonoidHom.ext fun w => by rw [map_one]; rfl
    show H.map (rhoG 1).toMonoidHom = H
    rw [e, Subgroup.map_id]
  mul_smul σ τ H := by
    have e : (rhoG (σ * τ)).toMonoidHom = (rhoG σ).toMonoidHom.comp (rhoG τ).toMonoidHom :=
      MonoidHom.ext fun w => by
        show rhoG (σ * τ) w = rhoG σ (rhoG τ w)
        rw [map_mul]
        rfl
    show H.map (rhoG (σ * τ)).toMonoidHom = (H.map (rhoG τ).toMonoidHom).map (rhoG σ).toMonoidHom
    rw [Subgroup.map_map, e]

theorem smul_W11_def (σ : ↥M24g) (w : W11) : σ • w = rho11 AutPerm le_rfl σ w := rfl

theorem smul_sp_def (σ : ↥M24g) (H : Subgroup W11) :
    σ • H = H.map (rho11 AutPerm le_rfl σ).toMonoidHom := rfl

@[expose] def sylS0G : Subgroup ↥M24g := sylS0.subgroupOf M24g

theorem mem_sylS0G {x : ↥M24g} : x ∈ sylS0G ↔ (x : S24) ∈ sylS0 := Subgroup.mem_subgroupOf

@[expose] def s0G (j : Fin 4) : ↥M24g := ⟨s0Perm j, s0Perm_mem j⟩

theorem s0G_smul_toW (j : Fin 4) (m : ℕ) :
    s0G j • toW 11 m = toW 11 (Native.toddAct (Native.s0Tabs.getD j #[]) m) :=
  rho11_toW_native (s0Perm_mem j) (repT_s0Perm j) m

theorem smul_inv_smul_W11 (g : ↥M24g) (w : W11) : g • g⁻¹ • w = w := by
  have h := inv_smul_smul g⁻¹ w
  rwa [inv_inv] at h

theorem smul_one_W11 (x : ↥M24g) : x • (1 : W11) = 1 := map_one (rhoG x)

section Fix


theorem sylS0G_fix_iff (w : W11) :
    (∀ x ∈ sylS0G, x • w = w) ↔ (w = 1 ∨ w = toW 11 31) := by
  constructor
  · intro h
    obtain ⟨m, hm, rfl⟩ := toW_surj 11 w
    have hm' : m < 2048 := by simpa using hm
    have hfixed : ∀ a ∈ Native.s0Tabs, Native.toddAct a m = m := by
      intro a ha
      obtain ⟨j, hj⟩ := exists_repT_of_mem (tabs := Native.s0Tabs) (n := 4) rfl repT_s0Perm ha
      have h0 := h (s0G j) (mem_sylS0G.2 (s0Perm_mem_sylS0 j))
      have h1 : toW 11 (Native.toddAct a m) = toW 11 m := by
        rw [← rho11_toW_native (s0Perm_mem j) hj m]
        exact h0
      have hlt : Native.toddAct a m < 2 ^ 11 := by simpa using toddAct_lt hj m
      exact toW_inj hlt hm h1
    rcases fixed_spec.1 m hm' hfixed with rfl | rfl
    · exact Or.inl (toW_zero 11)
    · exact Or.inr rfl
  · rintro (rfl | rfl) x hx
    · exact smul_one_W11 x
    · have hfix : ∀ j : Fin 4, s0G j ∈ MulAction.stabilizer ↥M24g (toW 11 31) := by
        intro j
        rw [MulAction.mem_stabilizer_iff, s0G_smul_toW]
        exact congrArg (toW 11) (fixed_spec.2 _ (s0Tabs_getD_mem j))
      have hle : sylS0 ≤ (MulAction.stabilizer ↥M24g (toW 11 31)).map M24g.subtype :=
        (Subgroup.closure_le _).2 (by
          rintro _ ⟨j, rfl⟩
          exact ⟨s0G j, hfix j, rfl⟩)
      obtain ⟨y, hy, hyx⟩ := hle (mem_sylS0G.1 hx)
      have : y = x := Subtype.ext hyx
      subst this
      exact hy

theorem clsMask_zero : clsMask 0 = 31 := by
  unfold clsMask
  rw [sextList_zero]
  exact clsDistinct_spec.2.2

theorem sextClass_sextFin_zero : sextClass (sextFin 0) = toW 11 31 := by
  rw [sextClass_sextFin zero_lt_1771, clsMask_zero]


theorem fix_sylow (P : Subgroup S24) (hP : P ≤ M24g) (hcard : Nat.card P = 2 ^ 10) :
    ∃ U, IsSextet U ∧ ∀ w : W11,
      (∀ (σ : S24) (hσ : σ ∈ P), rho11 AutPerm le_rfl ⟨σ, hP hσ⟩ w = w) ↔
        (w = 1 ∨ w = sextClass U) := by
  obtain ⟨g, hg⟩ := exists_conj_sylS0 P hP hcard
  have hU0 : IsSextet (sextFin 0) := isSextet_sextFin zero_lt_1771
  refine ⟨(g : S24) • sextFin 0, (isSextet_smul_iff g.2).2 hU0, fun w => ?_⟩
  have hcls : sextClass ((g : S24) • sextFin 0) = g • toW 11 31 := by
    rw [sextClass_smul g.2 hU0, sextClass_sextFin_zero]
    rfl
  rw [hcls]
  have key : (∀ (σ : S24) (hσ : σ ∈ P), rho11 AutPerm le_rfl ⟨σ, hP hσ⟩ w = w) ↔
      ∀ x ∈ sylS0G, x • (g⁻¹ • w) = g⁻¹ • w := by
    constructor
    · intro h x hx
      have hyP : ((g * x * g⁻¹ : ↥M24g) : S24) ∈ P := by
        rw [hg (g * x * g⁻¹)]
        have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
        rw [e]
        exact mem_sylS0G.1 hx
      have h1 : (g * x * g⁻¹ : ↥M24g) • w = w := h _ hyP
      rw [mul_smul, mul_smul] at h1
      calc x • g⁻¹ • w = g⁻¹ • g • x • g⁻¹ • w := by rw [inv_smul_smul]
        _ = g⁻¹ • w := by rw [h1]
    · intro h σ hσ
      have hx : (g⁻¹ * ⟨σ, hP hσ⟩ * g : ↥M24g) ∈ sylS0G :=
        mem_sylS0G.2 ((hg ⟨σ, hP hσ⟩).1 hσ)
      have h2 : (g⁻¹ * ⟨σ, hP hσ⟩ * g : ↥M24g) • g⁻¹ • w = g⁻¹ • w := h _ hx
      have h3 : g⁻¹ • (⟨σ, hP hσ⟩ : ↥M24g) • w = g⁻¹ • w := by
        calc g⁻¹ • (⟨σ, hP hσ⟩ : ↥M24g) • w
            = g⁻¹ • (⟨σ, hP hσ⟩ : ↥M24g) • g • g⁻¹ • w := by rw [smul_inv_smul_W11]
          _ = (g⁻¹ * ⟨σ, hP hσ⟩ * g : ↥M24g) • g⁻¹ • w := by simp only [mul_smul]
          _ = g⁻¹ • w := h2
      have h4 : (⟨σ, hP hσ⟩ : ↥M24g) • w = w := smul_left_cancel g⁻¹ h3
      exact h4
  rw [key, sylS0G_fix_iff, inv_smul_eq_iff, inv_smul_eq_iff, smul_one_W11]

end Fix

@[expose] noncomputable def spOf (L : List ℕ) : Subgroup W11 :=
  Subgroup.closure {w | ∃ m ∈ L, toW 11 m = w}

theorem mem_spOf {L : List ℕ} (hc : ∀ a ∈ L, ∀ b ∈ L, a ^^^ b ∈ L) (h0 : 0 ∈ L) {w : W11} :
    w ∈ spOf L ↔ ∃ m ∈ L, toW 11 m = w := by
  constructor
  · intro h
    refine Subgroup.closure_induction (p := fun x _ => ∃ m ∈ L, toW 11 m = x) (fun x hx => hx)
      ⟨0, h0, toW_zero 11⟩ ?_ ?_ h
    · rintro x y _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      exact ⟨a ^^^ b, hc a ha b hb, toW_xor 11 a b⟩
    · rintro x _ ⟨a, ha, rfl⟩
      exact ⟨a, ha, (inv_eq_of_mul_eq_one_right (W11_mul_self _)).symm⟩
  · rintro ⟨m, hm, rfl⟩
    exact Subgroup.subset_closure ⟨m, hm, rfl⟩

theorem spOf_step {t : Array ℕ} {g : S24} (hg : g ∈ M24g) (h : RepT t g) (L : List ℕ) :
    spOf (Native.stepSp t L) = (spOf L).map (rho11 AutPerm le_rfl ⟨g, hg⟩).toMonoidHom := by
  unfold spOf
  rw [MonoidHom.map_closure]
  congr 1
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_image, Native.stepSp, mem_sortL, List.mem_map]
  constructor
  · rintro ⟨m, ⟨m₀, hm₀, rfl⟩, rfl⟩
    exact ⟨toW 11 m₀, ⟨m₀, hm₀, rfl⟩, rho11_toW_native hg h m₀⟩
  · rintro ⟨x, ⟨m₀, hm₀, rfl⟩, rfl⟩
    exact ⟨_, ⟨m₀, hm₀, rfl⟩, (rho11_toW_native hg h m₀).symm⟩

private theorem validSp_get {L : List ℕ} (h : Native.validSp L = true) :
    (∀ m ∈ L, m < 2048) ∧ L.Pairwise (· < ·) ∧ (∀ a ∈ L, ∀ b ∈ L, a ^^^ b ∈ L) ∧ 0 ∈ L := by
  unfold Native.validSp at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.contains_iff_mem] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, ?_, h4⟩
  have h3' := h3
  unfold Native.closedXor at h3'
  simp only [List.all_eq_true, List.contains_iff_mem, decide_eq_true_eq] at h3'
  exact h3'

private theorem spOf_inj {L L' : List ℕ} (hL : Native.validSp L = true)
    (hL' : Native.validSp L' = true) (h : spOf L = spOf L') : L = L' := by
  obtain ⟨hlt, hsort, hc, h0⟩ := validSp_get hL
  obtain ⟨hlt', hsort', hc', h0'⟩ := validSp_get hL'
  apply List.Pairwise.eq_of_mem_iff hsort hsort'
  intro x
  constructor
  · intro hx
    have h1 : toW 11 x ∈ spOf L := Subgroup.subset_closure ⟨x, hx, rfl⟩
    rw [h, mem_spOf hc' h0'] at h1
    obtain ⟨m, hm, e⟩ := h1
    have e' : m = x := toW_inj (by simpa using hlt' m hm) (by simpa using hlt x hx) e
    rw [← e']
    exact hm
  · intro hx
    have h1 : toW 11 x ∈ spOf L' := Subgroup.subset_closure ⟨x, hx, rfl⟩
    rw [← h, mem_spOf hc h0] at h1
    obtain ⟨m, hm, e⟩ := h1
    have e' : m = x := toW_inj (by simpa using hlt m hm) (by simpa using hlt' x hx) e
    rw [← e']
    exact hm

@[expose] def genG (j : Fin 3) : ↥M24g := ⟨genPerm j, genPerm_mem j⟩

section Orbit


theorem ncard_orbit_vp : 3796 ≤ (MulAction.orbit ↥M24g (spOf Native.vpList)).ncard := by
  classical
  obtain ⟨r, hr, hsz, hnd⟩ := spaceOrbit_spec
  have key := exists_smul_of_tree (G := ↥M24g) (X := Subgroup W11) ⊤ genG
    (fun j => Subgroup.mem_top _) (valid := Native.validSp)
    (steps := Native.genTabs.map Native.stepSp) (by simp [Native.genTabs]) spOf
    (fun j a _ => by
      rw [getD_map_of_lt _ Native.genTabs #[] id j.2]
      exact spOf_step (genPerm_mem j) (genTabs_rep j) a) hr
  set c := r.1.toList with hc
  have hcnd : c.Nodup := List.Nodup.of_map _ hnd
  have hvalid := treeValid_valid hr
  have hsub : ((c.toFinset.image spOf : Finset (Subgroup W11)) : Set (Subgroup W11)) ⊆
      MulAction.orbit ↥M24g (spOf Native.vpList) := by
    intro y hy
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    obtain ⟨σ, -, hσq⟩ := key q (List.mem_toFinset.1 hq)
    exact ⟨σ, hσq⟩
  have hcard : (c.toFinset.image spOf).card = c.length := by
    rw [Finset.card_image_of_injOn, List.toFinset_card_of_nodup hcnd]
    intro x hx y hy hxy
    exact spOf_inj (hvalid x (List.mem_toFinset.1 hx)) (hvalid y (List.mem_toFinset.1 hy)) hxy
  calc 3796 ≤ c.length := by simpa [hc] using hsz
    _ = (↑(c.toFinset.image spOf) : Set (Subgroup W11)).ncard := by
        rw [Set.ncard_coe_finset, hcard]
    _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)

end Orbit

section Classify


theorem eq_space_of_invariant (V : Subgroup W11) (hV : Nat.card V = 8) (h31 : toW 11 31 ∈ V)
    (hsext : ∀ v ∈ V, v ≠ 1 → ∃ U, IsSextet U ∧ sextClass U = v)
    (hinv : ∀ j : Fin 4, ∀ v ∈ V, s0G j • v ∈ V) :
    (∀ w, w ∈ V ↔ ∃ m ∈ Native.v0List, toW 11 m = w) ∨
      (∀ w, w ∈ V ↔ ∃ m ∈ Native.vpList, toW 11 m = w) := by
  classical
  set Ml : List ℕ := (List.range (2 ^ 11)).filter (fun m => decide (toW 11 m ∈ V)) with hMl
  have hmem : ∀ m, m ∈ Ml ↔ m < 2 ^ 11 ∧ toW 11 m ∈ V := by
    intro m
    simp [hMl, List.mem_filter, List.mem_range]
  have hlen : Ml.length = 8 := by
    have h := (MaskCoords.std 11).card_eq V (fun m => decide (toW 11 m ∈ V))
      (fun m _ => by simp [MaskCoords.std])
    rw [hV] at h
    exact h.symm
  have hnd : Ml.Nodup := List.nodup_range.filter _
  have hxor : ∀ a ∈ Ml, ∀ b ∈ Ml, a ^^^ b ∈ Ml := by
    intro a ha b hb
    rw [hmem] at ha hb ⊢
    refine ⟨Nat.xor_lt_two_pow ha.1 hb.1, ?_⟩
    rw [toW_xor]
    exact V.mul_mem ha.2 hb.2
  have h31' : 31 ∈ Ml := (hmem 31).2 ⟨by norm_num, h31⟩
  have hcls : ∀ m ∈ Ml, m ≠ 0 → IsCls m := by
    intro m hm hm0
    obtain ⟨hlt, hmV⟩ := (hmem m).1 hm
    have hne : toW 11 m ≠ 1 := fun h =>
      hm0 (toW_inj hlt (by norm_num) (h.trans (toW_zero 11).symm))
    obtain ⟨U, hU, hUe⟩ := hsext _ hmV hne
    obtain ⟨q, hq, rfl⟩ := (isSextet_iff U).1 hU
    rw [sextClass_sextFin hq] at hUe
    exact ⟨q, hq, toW_inj (clsMask_lt q) hlt hUe⟩
  have hex1 : ∃ v ∈ Ml, v ≠ 0 ∧ v ≠ 31 := by
    by_contra hcon
    push Not at hcon
    have hsub : Ml.toFinset ⊆ ({0, 31} : Finset ℕ) := by
      intro m hm
      rw [List.mem_toFinset] at hm
      by_cases h0 : m = 0
      · simp [h0]
      · simp [hcon m hm h0]
    have h1 := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hnd, hlen] at h1
    have h2 : ({0, 31} : Finset ℕ).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨v, hv, hv0, hv31⟩ := hex1
  have hex2 : ∃ w ∈ Ml, w ≠ 0 ∧ w ≠ 31 ∧ w ≠ v ∧ w ≠ 31 ^^^ v := by
    by_contra hcon
    push Not at hcon
    have hsub : Ml.toFinset ⊆ ({0, 31, v, 31 ^^^ v} : Finset ℕ) := by
      intro m hm
      rw [List.mem_toFinset] at hm
      by_cases h0 : m = 0
      · simp [h0]
      by_cases h1 : m = 31
      · simp [h1]
      by_cases h2 : m = v
      · simp [h2]
      · have h3 := hcon m hm h0 h1 h2
        simp [h3]
    have h1 := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hnd, hlen] at h1
    have h2 : ({0, 31, v, 31 ^^^ v} : Finset ℕ).card ≤ 4 := Finset.card_le_four
    omega
  obtain ⟨w, hw, hw0, hw31, hwv, hwv31⟩ := hex2
  have hvl : v < 2048 := by simpa using ((hmem v).1 hv).1
  have hwl : w < 2048 := by simpa using ((hmem w).1 hw).1
  have m1 : 31 ^^^ v ∈ Ml := hxor 31 h31' v hv
  have m2 : 31 ^^^ w ∈ Ml := hxor 31 h31' w hw
  have m3 : v ^^^ w ∈ Ml := hxor v hv w hw
  have m4 : 31 ^^^ v ^^^ w ∈ Ml := hxor (31 ^^^ v) m1 w hw
  have n1 : 31 ^^^ v ≠ 0 := fun h => hv31 (Nat.xor_eq_zero_iff.1 h).symm
  have n2 : 31 ^^^ w ≠ 0 := fun h => hw31 (Nat.xor_eq_zero_iff.1 h).symm
  have n3 : v ^^^ w ≠ 0 := fun h => hwv (Nat.xor_eq_zero_iff.1 h).symm
  have n4 : 31 ^^^ v ^^^ w ≠ 0 := fun h => hwv31 (Nat.xor_eq_zero_iff.1 h).symm
  obtain ⟨hndsp, himp⟩ := span_spec v hvl w hwl hv0 hv31 hw0 hw31 hwv hwv31 (hcls v hv hv0)
    (hcls _ m1 n1) (hcls w hw hw0) (hcls _ m2 n2) (hcls _ m3 n3) (hcls _ m4 n4)
  have hsp_sub : (Native.sp8 v w).toFinset ⊆ Ml.toFinset := by
    intro m hm
    rw [List.mem_toFinset] at hm ⊢
    simp only [Native.sp8, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hmem 0).2 ⟨by norm_num, by rw [toW_zero]; exact V.one_mem⟩
    · exact h31'
    · exact hv
    · exact m1
    · exact hw
    · exact m2
    · exact m3
    · exact m4
  have hspcard : (Native.sp8 v w).toFinset.card = 8 := by
    rw [List.toFinset_card_of_nodup hndsp]
    rfl
  have hsp_eq : (Native.sp8 v w).toFinset = Ml.toFinset :=
    Finset.eq_of_subset_of_card_le hsp_sub (by
      rw [List.toFinset_card_of_nodup hnd, hlen, hspcard])
  have hiff : ∀ m, m ∈ Ml ↔ m ∈ Native.sp8 v w := by
    intro m
    rw [← List.mem_toFinset, ← hsp_eq, List.mem_toFinset]
  have hinv' : ∀ a ∈ Native.s0Tabs, Native.toddAct a v ∈ Native.sp8 v w ∧
      Native.toddAct a w ∈ Native.sp8 v w := by
    intro a ha
    obtain ⟨j, hj⟩ := exists_repT_of_mem (tabs := Native.s0Tabs) (n := 4) rfl repT_s0Perm ha
    have key : ∀ x ∈ Ml, Native.toddAct a x ∈ Ml := by
      intro x hx
      obtain ⟨hxl, hxV⟩ := (hmem x).1 hx
      rw [hmem]
      refine ⟨by simpa using toddAct_lt hj x, ?_⟩
      have h1 := hinv j _ hxV
      have e : s0G j • toW 11 x = toW 11 (Native.toddAct a x) :=
        rho11_toW_native (s0Perm_mem j) hj x
      rw [e] at h1
      exact h1
    exact ⟨(hiff _).1 (key v hv), (hiff _).1 (key w hw)⟩
  rcases himp hinv' with h | h
  · left
    intro w'
    constructor
    · intro hw'
      obtain ⟨m, hm, rfl⟩ := toW_surj 11 w'
      refine ⟨m, ?_, rfl⟩
      rw [← h, mem_sortL, ← hiff, hmem]
      exact ⟨hm, hw'⟩
    · rintro ⟨m, hm, rfl⟩
      rw [← h, mem_sortL, ← hiff, hmem] at hm
      exact hm.2
  · right
    intro w'
    constructor
    · intro hw'
      obtain ⟨m, hm, rfl⟩ := toW_surj 11 w'
      refine ⟨m, ?_, rfl⟩
      rw [← h, mem_sortL, ← hiff, hmem]
      exact ⟨hm, hw'⟩
    · rintro ⟨m, hm, rfl⟩
      rw [← h, mem_sortL, ← hiff, hmem] at hm
      exact hm.2

end Classify

theorem exists_fixed_of_pgroup {Q : Subgroup ↥M24g} (hQ : IsPGroup 2 Q) (V : Subgroup W11)
    (hV : Nat.card V = 8) (hinv : ∀ x ∈ Q, ∀ v ∈ V, x • v ∈ V) :
    ∃ w ∈ V, w ≠ 1 ∧ ∀ x ∈ Q, x • w = w := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let X : SubMulAction ↥Q W11 :=
    { carrier := {w | w ∈ V ∧ w ≠ 1}
      smul_mem' := fun x w hw => by
        refine ⟨?_, fun h => hw.2 ?_⟩
        · rw [Subgroup.smul_def]
          exact hinv _ x.2 w hw.1
        · rw [Subgroup.smul_def, smul_W11_def] at h
          exact (MulEquiv.map_eq_one_iff _).1 h }
  have hX : Nat.card X = 7 := by
    have e : Nat.card X = ({w : W11 | w ∈ V ∧ w ≠ 1}).ncard := Nat.card_congr (Equiv.refl _)
    have e2 : ({w : W11 | w ∈ V ∧ w ≠ 1}) = (V : Set W11) \ {1} := by
      ext w
      simp
    rw [e, e2, Set.ncard_diff_singleton_of_mem V.one_mem, ← Nat.card_coe_set_eq]
    show Nat.card V - 1 = 7
    omega
  obtain ⟨z, hz⟩ := hQ.nonempty_fixed_point_of_prime_not_dvd_card X (by rw [hX]; norm_num)
  refine ⟨z.1, z.2.1, z.2.2, fun x hx => ?_⟩
  have h1 := MulAction.mem_fixedPoints.1 hz ⟨x, hx⟩
  have h2 := congrArg Subtype.val h1
  rwa [SubMulAction.val_smul, Subgroup.smul_def] at h2

section Main


theorem card_sylS0G : Nat.card sylS0G = 2 ^ 10 := by
  rw [← card_sylS0]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe sylS0_le).toEquiv

theorem eq_trioSpace_of_invariant (P : Subgroup S24) (hP : P ≤ M24g) (hcard : Nat.card P = 2 ^ 10)
    (V : Subgroup W11) (hV : Nat.card V = 8)
    (hsext : ∀ v ∈ V, v ≠ 1 → ∃ U, IsSextet U ∧ sextClass U = v)
    (hinv : ∀ (σ : S24) (hσ : σ ∈ P), ∀ v ∈ V, rho11 AutPerm le_rfl ⟨σ, hP hσ⟩ v ∈ V)
    (hstab : Nat.card ↥{σ : ↥M24g | V.map (rho11 AutPerm le_rfl σ).toMonoidHom = V} = 64512) :
    ∃ t, IsTrio t ∧ V = trioSpace t := by
  obtain ⟨g, hg⟩ := exists_conj_sylS0 P hP hcard
  have hh0 : IsTrio (trioFin 0) := isTrio_trioFin zero_lt_3795
  let V' : Subgroup W11 := g⁻¹ • V
  have hV'mem : ∀ w, w ∈ V' ↔ ∃ v ∈ V, g⁻¹ • v = w := fun w => Subgroup.mem_map
  have hcard' : Nat.card V' = 8 := by
    rw [← hV]
    exact Subgroup.card_map_of_injective (MulEquiv.injective _)
  have hinvP : ∀ x ∈ sylS0G, ∀ v ∈ V', x • v ∈ V' := by
    intro x hx v hv
    obtain ⟨v₀, hv₀, rfl⟩ := (hV'mem v).1 hv
    have hyP : ((g * x * g⁻¹ : ↥M24g) : S24) ∈ P := by
      rw [hg (g * x * g⁻¹)]
      have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
      rw [e]
      exact mem_sylS0G.1 hx
    have h1 : (g * x * g⁻¹ : ↥M24g) • v₀ ∈ V := hinv _ hyP v₀ hv₀
    refine (hV'mem _).2 ⟨_, h1, ?_⟩
    rw [mul_smul, mul_smul, inv_smul_smul]
  have hsext' : ∀ v ∈ V', v ≠ 1 → ∃ U, IsSextet U ∧ sextClass U = v := by
    intro v hv hv1
    obtain ⟨v₀, hv₀, rfl⟩ := (hV'mem v).1 hv
    have hv₀1 : v₀ ≠ 1 := fun h => hv1 (by rw [h]; exact smul_one_W11 _)
    obtain ⟨U₀, hU₀, hU₀e⟩ := hsext v₀ hv₀ hv₀1
    refine ⟨((g⁻¹ : ↥M24g) : S24) • U₀, (isSextet_smul_iff (g⁻¹).2).2 hU₀, ?_⟩
    rw [sextClass_smul (g⁻¹).2 hU₀, hU₀e]
    rfl
  have hQ : IsPGroup 2 sylS0G := IsPGroup.of_card (n := 10) card_sylS0G
  obtain ⟨w, hwV', hw1, hwfix⟩ := exists_fixed_of_pgroup hQ V' hcard' hinvP
  have h31 : toW 11 31 ∈ V' := by
    rcases (sylS0G_fix_iff w).1 hwfix with h | h
    · exact absurd h hw1
    · rw [← h]
      exact hwV'
  have hgen : ∀ j : Fin 4, ∀ v ∈ V', s0G j • v ∈ V' := fun j v hv =>
    hinvP (s0G j) (mem_sylS0G.2 (s0Perm_mem_sylS0 j)) v hv
  have hVV : g • V' = V := by
    have h := inv_smul_smul g⁻¹ V
    rwa [inv_inv] at h
  rcases eq_space_of_invariant V' hcard' h31 hsext' hgen with hcase | hcase
  ·
    have hVeq : V' = trioSpace (trioFin 0) := by
      ext w
      rw [hcase w]
      exact (QSet_base_iff (w := w)).symm.trans (mem_trioSpace hh0).symm
    refine ⟨(g : S24) • trioFin 0, (isTrio_smul_iff g.2).2 hh0, ?_⟩
    rw [trioSpace_smul g.2 hh0, ← hVV, hVeq]
    rfl
  · exfalso
    have hVp : V' = spOf Native.vpList := by
      ext w
      rw [hcase w]
      exact (mem_spOf (closedXor_spec (v0_spec.2.2)) (by simp [Native.vpList])).symm
    have hG : Nat.card ↥M24g = 244823040 := CFSG.Monster.Code.card_AutPerm
    have hos : Nat.card (MulAction.orbit ↥M24g V) * Nat.card (MulAction.stabilizer ↥M24g V) =
        Nat.card ↥M24g := by
      rw [← Nat.card_prod]
      exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup ↥M24g V)
    have hst : Nat.card (MulAction.stabilizer ↥M24g V) = 64512 := hstab
    rw [hG, hst] at hos
    have horb : Nat.card (MulAction.orbit ↥M24g V) = 3795 := by omega
    have heq : MulAction.orbit ↥M24g (spOf Native.vpList) = MulAction.orbit ↥M24g V := by
      rw [← hVp]
      exact MulAction.orbit_eq_iff.2 ⟨g⁻¹, rfl⟩
    have h3796 := ncard_orbit_vp
    rw [heq, ← Nat.card_coe_set_eq, horb] at h3796
    omega

end Main

end CFSG.Quasithin.H13.AS91.M24G
