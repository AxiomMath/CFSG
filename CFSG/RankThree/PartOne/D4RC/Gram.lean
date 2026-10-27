module

public import CFSG.LocalAnalysis.SeitzReduction.LongRootPairs
public import CFSG.RankThree.PartOne.D4RC.Dichotomy

public section

namespace CFSG.RankThree.PartOne.D4RC

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.SEITZ7 CFSG.Timmesfeld.ARS
  CFSG.SeitzReduction

variable {K : Type} [Field K]

theorem rg_isRoot_neg : IsRoot d4 (-highRoot d4) := IsRoot.neg (isRoot_highRoot d4)

abbrev rgHi : Label d4 := Sum.inr ⟨highRoot d4, isRoot_highRoot d4⟩

abbrev rgLo : Label d4 := Sum.inr ⟨-highRoot d4, rg_isRoot_neg⟩

@[expose] noncomputable def rgEntry (g : Module.End K (RootModule d4 K)) : K :=
  g (Finsupp.single rgHi 1) rgLo

@[expose] def rgCheck : Bool :=
  (List.range (Tag.rootCertificate d4).roots.length).all fun k =>
    (!decide (height ((Tag.rootCertificate d4).root k) = height (highRoot d4)) ||
        (List.ofFn ((Tag.rootCertificate d4).root k) == List.ofFn (highRoot d4))) &&
      (!decide (height ((Tag.rootCertificate d4).root k) = -height (highRoot d4)) ||
        (List.ofFn ((Tag.rootCertificate d4).root k) == List.ofFn (-highRoot d4)))

theorem rgCheck_eq_true : rgCheck = true := by decide +kernel

theorem rg_height_cases {α : Fin d4.rank → ℤ} (hα : IsRoot d4 α) :
    (height α = height (highRoot d4) → α = highRoot d4) ∧
      (height α = -height (highRoot d4) → α = -highRoot d4) ∧
      -height (highRoot d4) ≤ height α ∧ height α ≤ height (highRoot d4) := by
  have hle := height_le_height_highRoot hα
  have hge := height_le_height_highRoot (IsRoot.neg hα)
  have hneg : height (-α) = -height α := by simp [height, Finset.sum_neg_distrib]
  rw [hneg] at hge
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .D4) hα
  have hc := rgCheck_eq_true
  simp only [rgCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not] at hc
  obtain ⟨h1, h2⟩ := hc k hk
  refine ⟨fun e => ?_, fun e => ?_, by linarith, hle⟩
  · rcases h1 with h | h
    · exact absurd e h
    · exact RootCertificate.eq_of_ofFn_beq h
  · rcases h2 with h | h
    · exact absurd e h
    · exact RootCertificate.eq_of_ofFn_beq h

omit [Field K] in
theorem rg_weight_lt_hi {a : Label d4} (ha : a ≠ rgHi) : a.weight < rgHi.weight := by
  rcases a with i | ⟨α, hα⟩
  · exact height_highRoot_pos d4
  · obtain ⟨h1, -, -, h4⟩ := rg_height_cases hα
    refine lt_of_le_of_ne h4 fun e => ha ?_
    have : α = highRoot d4 := h1 e
    subst this
    rfl

omit [Field K] in
theorem rg_weight_lo_lt {a : Label d4} (ha : a ≠ rgLo) : rgLo.weight < a.weight := by
  have hneg : height (-highRoot d4) = -height (highRoot d4) := by
    simp [height, Finset.sum_neg_distrib]
  rcases a with i | ⟨α, hα⟩
  · change height (-highRoot d4) < 0
    have := height_highRoot_pos d4
    rw [hneg]
    linarith
  · change height (-highRoot d4) < height α
    obtain ⟨-, h2, h3, -⟩ := rg_height_cases hα
    rw [hneg]
    refine lt_of_le_of_ne h3 fun e => ha ?_
    have : α = -highRoot d4 := h2 e.symm
    subst this
    rfl

theorem rg_col {A : Module.End K (RootModule d4 K)} (hA : IsUpperTriangular d4 K A) :
    A (Finsupp.single rgHi 1) = A (Finsupp.single rgHi 1) rgHi • Finsupp.single rgHi 1 := by
  ext a
  by_cases ha : a = rgHi
  · subst ha
    simp
  · have h0 : (Finsupp.single rgHi (1 : K)) a = 0 := by simp [Ne.symm ha]
    rw [Finsupp.smul_apply, h0, smul_zero]
    exact hA a rgHi (Or.inl (rg_weight_lt_hi ha))

theorem rg_row {A : Module.End K (RootModule d4 K)} (hA : IsUpperTriangular d4 K A)
    (v : RootModule d4 K) : A v rgLo = A (Finsupp.single rgLo 1) rgLo * v rgLo := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, Finsupp.add_apply, hx, hy, Finsupp.add_apply, mul_add]
  | single c r =>
    rw [← Finsupp.smul_single_one, map_smul, Finsupp.smul_apply, Finsupp.smul_apply,
      smul_eq_mul, smul_eq_mul]
    by_cases hc : c = rgLo
    · subst hc
      simp only [Finsupp.single_eq_same, mul_one]
      ring
    · have h0 : (Finsupp.single c (1 : K)) rgLo = 0 := by simp [hc]
      rw [hA rgLo c (Or.inl (rg_weight_lo_lt hc)), h0]
      ring

theorem rg_upper {b : ModGL d4 K} (hb : b ∈ borelGroup d4 K) :
    IsUpperTriangular d4 K (b : Module.End K (RootModule d4 K)) :=
  (triangular_borel_structure.{0, 0} d4 K).2.2.2.2.2.2.2.2.2.1 b hb

theorem rg_entry_borel_mul {b b' : ModGL d4 K} (hb : b ∈ borelGroup d4 K)
    (hb' : b' ∈ borelGroup d4 K) (m : ModGL d4 K) :
    ∃ r c : K, r ≠ 0 ∧ c ≠ 0 ∧
      rgEntry ((b * m * b' : ModGL d4 K) : Module.End K (RootModule d4 K)) =
        r * rgEntry (m : Module.End K (RootModule d4 K)) * c := by
  obtain ⟨c, hcol⟩ : ∃ c : K, (b' : Module.End K (RootModule d4 K)) (Finsupp.single rgHi 1) =
      c • Finsupp.single rgHi 1 := ⟨_, rg_col (rg_upper hb')⟩
  obtain ⟨r, hrow⟩ : ∃ r : K, ∀ v, (b : Module.End K (RootModule d4 K)) v rgLo = r * v rgLo :=
    ⟨_, rg_row (rg_upper hb)⟩
  refine ⟨r, c, ?_, ?_, ?_⟩
  · intro h0
    have h1 := hrow (((b⁻¹ : ModGL d4 K) : Module.End K (RootModule d4 K))
      (Finsupp.single rgLo 1))
    rw [h0, zero_mul, ← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Module.End.one_apply, Finsupp.single_eq_same] at h1
    exact one_ne_zero h1
  · intro h0
    rw [h0, zero_smul] at hcol
    have h2 := congrArg (((b'⁻¹ : ModGL d4 K) : Module.End K (RootModule d4 K)) ·) hcol
    simp only [map_zero] at h2
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Module.End.one_apply] at h2
    have h3 := congrArg (· rgHi) h2
    simp at h3
  · simp only [rgEntry, Units.val_mul, Module.End.mul_apply]
    rw [hcol, map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul, hrow]
    ring

theorem rg_list_prod_weylElt_rootVec (ω : List (Fin d4.rank)) {β : Fin d4.rank → ℤ}
    (hβ : IsRoot d4 β) : ∃ ε : K, ε ≠ 0 ∧
      (((ω.map fun i => weylElt d4 K i 1).prod : ModGL d4 K) :
        Module.End K (RootModule d4 K)) (rootVec d4 K β) =
        ε • rootVec d4 K ((coxeterSystem d4).wordProd ω • β) := by
  induction ω with
  | nil => exact ⟨1, one_ne_zero, by simp⟩
  | cons i ω ih =>
    obtain ⟨ε, hε, h⟩ := ih
    refine ⟨ε * ((-1) ^ stringDown d4 i ((coxeterSystem d4).wordProd ω • β) *
      (((1 : Kˣ) ^ (-∑ j, d4.cartan i j * ((coxeterSystem d4).wordProd ω • β) j) : Kˣ) : K)),
      mul_ne_zero hε (by simp), ?_⟩
    have e : (coxeterSystem d4).wordProd (i :: ω) • β =
        reflect d4 i ((coxeterSystem d4).wordProd ω • β) := by
      rw [CoxeterSystem.wordProd_cons, mul_smul]
      exact simple_smul i _
    rw [e, List.map_cons, List.prod_cons, Units.val_mul, Module.End.mul_apply, h, map_smul,
      weylElt_rootVec i 1 (IsRoot.smul hβ _), smul_smul]

theorem rg_entry_canonicalRep (w : WeylGroup d4) :
    rgEntry ((canonicalRep (coxeterSystem d4) K w : ModGL d4 K) :
      Module.End K (RootModule d4 K)) ≠ 0 ↔ w • highRoot d4 = -highRoot d4 := by
  classical
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem d4).exists_isReduced w
  obtain ⟨ε, hε, h⟩ := rg_list_prod_weylElt_rootVec (K := K) ω (isRoot_highRoot d4)
  have hv : (Finsupp.single rgHi 1 : RootModule d4 K) = rootVec d4 K (highRoot d4) :=
    (CFSG.LieType.Chevalley.rootVec_eq_single (isRoot_highRoot d4)).symm
  have hlo := CFSG.LieType.Ree.rootVec_apply_inr (K := K) ((coxeterSystem d4).wordProd ω •
    highRoot d4) ⟨-highRoot d4, rg_isRoot_neg⟩
  rw [rgEntry, canonicalRep_wordProd hω, hv, h, Finsupp.smul_apply, smul_eq_mul, hlo]
  constructor
  · intro hne
    by_contra hw
    exact hne (by rw [ite_eq_right_iff.2 (fun h => absurd h hw), mul_zero])
  · intro hw
    rw [ite_eq_left_iff.2 (fun h => absurd hw h), mul_one]
    exact hε

theorem rg_isPGroup_of_entry_eq_zero [Finite K] [CharP K 2] {g : ModGL d4 K}
    (hg : g ∈ adjointGroup d4 K) (h0 : rgEntry (g : Module.End K (RootModule d4 K)) = 0) :
    IsPGroup 2 ↥(rootSubgroup d4 K (highRoot d4) ⊔
      (rootSubgroup d4 K (highRoot d4)).map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨w, hw⟩ := exists_mem_bruhatCell_of_mem_adjointGroup hg
  obtain ⟨b₀, -, heq, hpos⟩ := highRoot_pair_of_mem_bruhatCell hw
  obtain ⟨b, hb, b', hb', hbg⟩ := mem_bruhatCell.1 hw
  have hne : w • highRoot d4 ≠ -highRoot d4 := by
    intro hwθ
    obtain ⟨r, c, hr, hc, he⟩ := rg_entry_borel_mul hb hb' (canonicalRep (coxeterSystem d4) K w)
    rw [hbg, h0] at he
    have := (rg_entry_canonicalRep (K := K) w).2 hwθ
    exact this (by
      rcases mul_eq_zero.1 (mul_eq_zero.1 he.symm |>.resolve_right hc) with h | h
      · exact absurd h hr
      · exact h)
  obtain ⟨v, hv⟩ := hpos hne
  have h2 : IsPGroup 2 ↥((rootSubgroup d4 K (highRoot d4) ⊔
      rootSubgroup d4 K (w • highRoot d4)).map
        (MulAut.conj (canonicalRep (coxeterSystem d4) K v)).toMonoidHom) :=
    (isPGroup_posUnipotent_of_charP 2).to_le hv
  have h3 : IsPGroup 2 ↥(rootSubgroup d4 K (highRoot d4) ⊔ rootSubgroup d4 K (w • highRoot d4)) :=
    h2.of_equiv (Subgroup.equivMapOfInjective _ _
      (MulAut.conj (canonicalRep (coxeterSystem d4) K v)).injective).symm
  rw [heq]
  exact h3.map _

theorem rg_coe_xPar_mem {γ : Fin d4.rank → ℤ} (hγ : IsRoot d4 γ) (c : K) :
    ((xPar (rootOperatorFamily d4) γ c : adjointGroup d4 K) : ModGL d4 K) ∈
      rootSubgroup d4 K γ := by
  have h := (rootOperatorFamily d4).pinnedX_eq_eltUnit K hγ
    (((rootOperatorFamily d4).pinnedFamilySign γ : K) * c)
  rw [← mul_assoc, (rootOperatorFamily d4).pinnedFamilySign_mul_self K γ, one_mul] at h
  rw [xPar_of_isRoot hγ]
  exact mem_rootSubgroup.2 ⟨_, h⟩

theorem rg_d4Root_22 : d4Root 22 = highRoot d4 := by decide

theorem rg_Xh_le [CharP K 2] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c) :
    (Xh σ).map (((adjointGroup d4 K).subtype).comp (twistedGroup σ).subtype) ≤
      rootSubgroup d4 K (highRoot d4) := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨c, -, hc⟩ := (mem_Xh_iff hσ x).1 hx
  change (((x : adjointGroup d4 K)) : ModGL d4 K) ∈ _
  rw [hc, xH, ← rg_d4Root_22]
  exact rg_coe_xPar_mem (isRoot_d4 (by norm_num)) c

theorem rg_not_opposite_of_entry [Finite K] [CharP K 2] {σ : K →+* K}
    (hσ : ∀ c, σ (σ (σ c)) = c) [IsSimpleGroup (twistedGroup σ)] {g : twistedGroup σ}
    (h0 : rgEntry ((((g : adjointGroup d4 K)) : ModGL d4 K) : Module.End K (RootModule d4 K)) =
      0) :
    ¬ Opposite (Xh σ) (conjSub (Xh σ) g) := by
  have : Finite (twistedGroup σ) := inferInstance
  set φ : twistedGroup σ →* ModGL d4 K := ((adjointGroup d4 K).subtype).comp
    (twistedGroup σ).subtype with hφ
  have hφi : Function.Injective φ :=
    (adjointGroup d4 K).subtype_injective.comp (twistedGroup σ).subtype_injective
  have hP := rg_isPGroup_of_entry_eq_zero (K := K) (g := φ g) (g : adjointGroup d4 K).2 h0
  have hle : (Xh σ ⊔ conjSub (Xh σ) g).map φ ≤ rootSubgroup d4 K (highRoot d4) ⊔
      (rootSubgroup d4 K (highRoot d4)).map (MulAut.conj (φ g)).toMonoidHom := by
    rw [Subgroup.map_sup]
    refine sup_le_sup (rg_Xh_le hσ) ?_
    have e : (conjSub (Xh σ) g).map φ = ((Xh σ).map φ).map (MulAut.conj (φ g)).toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
    rw [e]
    exact Subgroup.map_mono (rg_Xh_le hσ)
  have hP' : IsPGroup 2 ↥((Xh σ ⊔ conjSub (Xh σ) g).map φ) := hP.to_le hle
  exact Sec3.not_opposite_of_isPGroup_sup (rcg_isRootClass hσ) rcg_Xh_mem
    (rcg_conjSub_mem rcg_Xh_mem g)
    (hP'.of_equiv (Subgroup.equivMapOfInjective _ _ hφi).symm)

theorem rg_opposite_entry_ne_zero [Finite K] [CharP K 2] {σ : K →+* K}
    (hσ : ∀ c, σ (σ (σ c)) = c) [IsSimpleGroup (twistedGroup σ)] {g g' : twistedGroup σ}
    (hop : Opposite (conjSub (Xh σ) g) (conjSub (Xh σ) g')) :
    rgEntry ((((g⁻¹ * g' : twistedGroup σ) : adjointGroup d4 K) : ModGL d4 K) :
      Module.End K (RootModule d4 K)) ≠ 0 := by
  intro h0
  apply rg_not_opposite_of_entry hσ h0
  have := rcg_opposite_conj hop g⁻¹
  rwa [conjSub_conjSub_inv', ← conjSub_mul] at this

theorem rg_perm_highRoot : permLattice TwistTag.D4.perm (highRoot d4) = highRoot d4 ∧
    permLattice TwistTag.D4.perm.symm (-highRoot d4) = -highRoot d4 := by
  decide

theorem rg_entry_twistHom (σ : K →+* K) (g : ModGL d4 K) :
    rgEntry ((twistHom TwistTag.D4 K σ g : ModGL d4 K) : Module.End K (RootModule d4 K)) =
      σ (rgEntry (g : Module.End K (RootModule d4 K))) := by
  have hv : (Finsupp.single rgHi 1 : RootModule d4 K) = rootVec d4 K (highRoot d4) :=
    (CFSG.LieType.Chevalley.rootVec_eq_single (isRoot_highRoot d4)).symm
  have hP : (diagramMap TwistTag.D4 K : Module.End K (RootModule d4 K))
      (Finsupp.single rgHi 1) = Finsupp.single rgHi 1 := by
    rw [hv, diagramMap_rootVec TwistTag.D4 K _ (isRoot_highRoot d4), rg_perm_highRoot.1]
  have hP' : (((diagramMap TwistTag.D4 K)⁻¹ : ModGL d4 K) : Module.End K (RootModule d4 K))
      (Finsupp.single rgHi 1) = Finsupp.single rgHi 1 := by
    conv_lhs => rw [← hP]
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Module.End.one_apply]
  have hlo : ∀ w : RootModule d4 K,
      (diagramMap TwistTag.D4 K : Module.End K (RootModule d4 K)) w rgLo = w rgLo := by
    intro w
    change (Finsupp.domLCongr (labelPerm TwistTag.D4.perm TwistTag.D4.cartan_perm) w) rgLo = _
    rw [Finsupp.domLCongr_apply, Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply]
    congr 1
    change Sum.inr ⟨permLattice TwistTag.D4.perm.symm (-highRoot d4), _⟩ = rgLo
    simp only [rg_perm_highRoot.2]
  rw [rgEntry, rgEntry, coe_twistHom, Module.End.mul_apply, Module.End.mul_apply, hP', hlo,
    entrywise_single, Finsupp.mapRange_apply]

theorem rg_entry_fixed {σ : K →+* K} {g : adjointGroup d4 K}
    (hg : g ∈ twistFixed TwistTag.D4 K σ) :
    σ (rgEntry (((g : ModGL d4 K)) : Module.End K (RootModule d4 K))) =
      rgEntry (((g : ModGL d4 K)) : Module.End K (RootModule d4 K)) := by
  rw [← rg_entry_twistHom]
  have h := congrArg Subtype.val ((mem_twistFixed TwistTag.D4 K σ).1 hg)
  rw [coe_twistC] at h
  rw [h]

end CFSG.RankThree.PartOne.D4RC
