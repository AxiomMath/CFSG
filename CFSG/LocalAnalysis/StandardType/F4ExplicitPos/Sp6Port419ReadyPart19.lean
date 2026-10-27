module

public import CFSG.LieType.Chevalley.A2CommutatorCheck
public import CFSG.LieType.SeitzGeneration.HeisTorusU87Arith
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderThree
public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart18
public import CFSG.LieType.AlgebraicGroups.TangentSpace

@[expose] public section

public section
open CFSG.Open CFSG.LieType.Universal CFSG.LieType.RootSystem

public section
open CFSG.Open

public noncomputable section
open CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
open scoped CFSG.ConvolutionPoints

public noncomputable section
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.AlgebraicGroups WithConv
open scoped CFSG.ConvolutionPoints

public section

public section

public noncomputable section

namespace CFSG.LieType.Steinberg.Adjoint
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.RootWalk
variable {τ : Tag}
open AVec

namespace AdjData
variable (D : AdjData τ) (R : Type*) [CommRing R]
variable {R}

theorem sum_zipWith_hUnit_without117 (j : Fin τ.rank) {w : List ℤ} (hw : w.length = τ.rank) :
    (List.zipWith (· * ·) (hUnit j) w).sum = w.getD j 0 := by
  rw [sum_zipWith_mul_without117, hw, ← Fin.sum_univ_eq_sum_range (fun m =>
      (hUnit j).getD m 0 * w.getD m 0)]
  simp only [hUnit_getD_without117, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

theorem actM_hvec_interp_without117 (M k : ℕ) (v : List ℤ) :
    (D.actM M k (.hvec v)).interp τ R =
      (((List.zipWith (· * ·) v (D.hpart k)).sum : ℤ) : R) •
        rootVec τ R (τ.rootCertificate.root k) := by
  simp only [actM, interp_norm_without117, interp_root_without117]

theorem recOp_interp_without117
    (k : ℕ) {u : AVec} (hu : u.WF τ) :
    D.recOp R k (u.interp τ R) = (D.act k u).interp τ R := by
  cases u with
  | zero => simp [act, actM]
  | root m c =>
    rw [act_eq_without117, actM_root_interp_without117]
    rcases hu with rfl | hm
    · simp
    · rw [interp_root_without117, rootVec_of_isRoot'_without117 (isRoot_rootCertificate_root hm),
        map_smul,
        recOp_single_without117]
      simp only [ofLabel]
      rw [pos_root_without117 hm, act_eq_without117]
  | hvec v =>
    rw [interp_hvec_without117, map_sum, act_eq_without117, actM_hvec_interp_without117,
        sum_zipWith_mul_without117, hpart_length_without117,
      ← Fin.sum_univ_eq_sum_range (fun m => v.getD m 0 * (D.hpart k).getD m 0), Int.cast_sum,
      Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hVec, recOp_single_without117]
    simp only [ofLabel]
    rw [act_eq_without117, actM_hvec_interp_without117,
        sum_zipWith_hUnit_without117 j (D.hpart_length_without117 k), smul_smul,
      Int.cast_mul]

variable {D}

theorem checkTables_at_without117 (hT : D.checkTables = true) {b : ℕ}
    (hb : b < τ.rootCertificate.roots.length) :
    D.neg b < τ.rootCertificate.roots.length ∧
      τ.rootCertificate.root (D.neg b) = -τ.rootCertificate.root b ∧
      ∀ i : Fin τ.rank, D.img b i = τ.rootCertificate.image b i ∧
        (if b = (i : ℕ) then D.dn b i = 2 ∧ D.upl b i = 0
          else if b = D.neg i then D.dn b i = 0 ∧ D.upl b i = 2
          else D.dn b i = τ.stringData.down b i ∧ D.upl b i = τ.stringData.up b i) ∧
        D.par b i = (∑ j, τ.cartan i j * τ.rootCertificate.root b j).natAbs % 2 ∧
        (if D.upI b i = 0 then τ.stringData.memDec τ.rootCertificate
            (τ.rootCertificate.root b + Pi.single i 1) = false
          else D.upI b i - 1 < τ.rootCertificate.roots.length ∧
            τ.rootCertificate.root (D.upI b i - 1) =
              τ.rootCertificate.root b + Pi.single i 1) ∧
        (if D.downI b i = 0 then τ.stringData.memDec τ.rootCertificate
            (τ.rootCertificate.root b - Pi.single i 1) = false
          else D.downI b i - 1 < τ.rootCertificate.roots.length ∧
            τ.rootCertificate.root (D.downI b i - 1) =
              τ.rootCertificate.root b - Pi.single i 1) := by
  have h := hT
  simp only [checkTables, nR, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
    List.mem_finRange, true_implies] at h
  obtain ⟨⟨hn, hr⟩, hi⟩ := h b hb
  refine ⟨of_decide_eq_true hn, RootCertificate.eq_of_ofFn_beq (beq_iff_eq.2 hr), fun i => ?_⟩
  obtain ⟨⟨⟨⟨hi1, hi2⟩, hi3⟩, hi4⟩, hi5⟩ := hi i
  refine ⟨hi1, ?_, hi3, ?_, ?_⟩
  · split_ifs at hi2 ⊢ <;> simpa using hi2
  · split_ifs at hi4 ⊢
    · simpa using hi4
    · simp only [Bool.and_eq_true, beq_iff_eq] at hi4
      exact ⟨of_decide_eq_true hi4.1, List.ofFn_injective hi4.2⟩
  · split_ifs at hi5 ⊢
    · simpa using hi5
    · simp only [Bool.and_eq_true, beq_iff_eq] at hi5
      exact ⟨of_decide_eq_true hi5.1, List.ofFn_injective hi5.2⟩

theorem neg_lt_without117 (hT : D.checkTables = true) {b : ℕ} (hb : b <
    τ.rootCertificate.roots.length) :
    D.neg b < τ.rootCertificate.roots.length :=
  (checkTables_at_without117 hT hb).1

theorem root_neg_without117 (hT : D.checkTables = true) {b : ℕ} (hb : b <
    τ.rootCertificate.roots.length) :
    τ.rootCertificate.root (D.neg b) = -τ.rootCertificate.root b :=
  (checkTables_at_without117 hT hb).2.1

theorem img_eq_without117 (hT : D.checkTables = true) {b : ℕ} (hb : b <
    τ.rootCertificate.roots.length)
    (i : Fin τ.rank) : D.img b i = τ.rootCertificate.image b i :=
  ((checkTables_at_without117 hT hb).2.2 i).1

theorem img_lt_without117
    (hT : D.checkTables = true) {b : ℕ} (hb : b < τ.rootCertificate.roots.length)
    (i : Fin τ.rank) : D.img b i < τ.rootCertificate.roots.length := by
  rw [img_eq_without117 hT hb]
  exact rootCertificate_image_lt hb i

theorem root_img_without117
    (hT : D.checkTables = true) {b : ℕ} (hb : b < τ.rootCertificate.roots.length)
    (i : Fin τ.rank) :
    τ.rootCertificate.root (D.img b i) = reflect τ i (τ.rootCertificate.root b) := by
  rw [img_eq_without117 hT hb]
  exact rootCertificate_root_image hb i

theorem neg_simple_without117
    (hT : D.checkTables = true) (i : Fin τ.rank) :
    D.neg i = τ.rootCertificate.image i i := by
  refine rootCertificate_root_injOn (neg_lt_without117 hT
      (CFSG.LieType.Chevalley.RootOps.val_lt_rootCertificate_length i))
    (rootCertificate_image_lt (CFSG.LieType.Chevalley.RootOps.val_lt_rootCertificate_length i) i) ?_
  rw [root_neg_without117 hT (CFSG.LieType.Chevalley.RootOps.val_lt_rootCertificate_length i),
      rootCertificate_root_image (CFSG.LieType.Chevalley.RootOps.val_lt_rootCertificate_length i),
          root_simple_without117,
    reflect_single_self]

theorem dn_eq_without117
    (hT : D.checkTables = true) {b : ℕ} (hb : b < τ.rootCertificate.roots.length)
    (i : Fin τ.rank) : D.dn b i = stringDown τ i (τ.rootCertificate.root b) := by
  have h := ((checkTables_at_without117 hT hb).2.2 i).2.1
  rw [stringDown_rootCertificate_root hb i, downAt, ← neg_simple_without117 hT i]
  split_ifs at h ⊢
  · exact h.1
  · exact h.1
  · exact h.1

theorem par_eq_without117 (hT : D.checkTables = true) {b : ℕ} (hb : b <
    τ.rootCertificate.roots.length)
    (i : Fin τ.rank) :
    D.par b i = (∑ j, τ.cartan i j * τ.rootCertificate.root b j).natAbs % 2 :=
  ((checkTables_at_without117 hT hb).2.2 i).2.2.1

theorem not_isRoot_of_upI_without117
    (hT : D.checkTables = true) {b : ℕ}
    (hb : b < τ.rootCertificate.roots.length) {i : Fin τ.rank} (h : D.upI b i = 0) :
    ¬IsRoot τ (τ.rootCertificate.root b + Pi.single i 1) := by
  have h' := ((checkTables_at_without117 hT hb).2.2 i).2.2.2.1
  rw [ite_eq_left h] at h'
  rw [← StringData.memDec_iff τ.rootCertificate_check τ.stringData_check, h']
  exact Bool.false_ne_true

theorem upI_spec_without117 (hT : D.checkTables = true) {b : ℕ} (hb : b <
    τ.rootCertificate.roots.length)
    {i : Fin τ.rank} (h : D.upI b i ≠ 0) :
    D.upI b i - 1 < τ.rootCertificate.roots.length ∧
      τ.rootCertificate.root (D.upI b i - 1) = τ.rootCertificate.root b + Pi.single i 1 := by
  have h' := ((checkTables_at_without117 hT hb).2.2 i).2.2.2.1
  rwa [ite_eq_right h] at h'

theorem not_isRoot_of_downI_without117
    (hT : D.checkTables = true) {b : ℕ}
    (hb : b < τ.rootCertificate.roots.length) {i : Fin τ.rank} (h : D.downI b i = 0) :
    ¬IsRoot τ (τ.rootCertificate.root b - Pi.single i 1) := by
  have h' := ((checkTables_at_without117 hT hb).2.2 i).2.2.2.2
  rw [ite_eq_left h] at h'
  rw [← StringData.memDec_iff τ.rootCertificate_check τ.stringData_check, h']
  exact Bool.false_ne_true

theorem downI_spec_without117 (hT : D.checkTables = true) {b : ℕ} (hb : b <
    τ.rootCertificate.roots.length)
    {i : Fin τ.rank} (h : D.downI b i ≠ 0) :
    D.downI b i - 1 < τ.rootCertificate.roots.length ∧
      τ.rootCertificate.root (D.downI b i - 1) = τ.rootCertificate.root b - Pi.single i 1 := by
  have h' := ((checkTables_at_without117 hT hb).2.2 i).2.2.2.2
  rwa [ite_eq_right h] at h'

theorem units_neg_one_zpow_without117 (z : ℤ) :
    (((-1 : Rˣ) ^ z : Rˣ) : R) = (-1 : R) ^ (z.natAbs % 2) := by
  rcases Int.even_or_odd z with h | h
  · rw [h.neg_one_zpow, Units.val_one]
    have : z.natAbs % 2 = 0 := by
      obtain ⟨k, rfl⟩ := h
      omega
    rw [this, pow_zero]
  · rw [h.neg_one_zpow, Units.val_neg, Units.val_one]
    have : z.natAbs % 2 = 1 := by
      obtain ⟨k, rfl⟩ := h
      omega
    rw [this, pow_one]

theorem hReflect_getD_without117 (i m : Fin τ.rank) (v : List ℤ) :
    (hReflect i v).getD m 0 =
      v.getD m 0 - if m = i then ∑ l : Fin τ.rank, v.getD l 0 * ((τ.cartan l i).natAbs : ℤ)
        else 0 := by
  rw [hReflect, getD_range_map_without117 _ _ m.2]
  simp only [Fin.val_inj]

theorem hReflect_length_without117 (i : Fin τ.rank) (v : List ℤ) : (hReflect i v).length =
    τ.rank := by
  simp [hReflect]

theorem weylElt_interp_hvec_without117
    (i : Fin τ.rank) (t : Rˣ) (v : List ℤ) :
    (weylElt τ R i t : Module.End R (RootModule τ R)) ((AVec.hvec v).interp τ R) =
      (AVec.hvec (hReflect i v)).interp τ R := by
  simp only [interp_hvec_without117, map_sum, map_smul, weylElt_hVec, hReflect_getD_without117,
      smul_sub,
    Finset.sum_sub_distrib, Int.cast_sub, sub_smul]
  congr 1
  simp only [apply_ite, Int.cast_zero, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, Int.cast_sum, Int.cast_mul, Int.cast_natCast, Finset.sum_smul, smul_smul]

theorem weylElt_interp_without117
    (hT : D.checkTables = true) (i : Fin τ.rank) {u : AVec} (hu : u.WF τ) :
    (weylElt τ R i 1 : Module.End R (RootModule τ R)) (u.interp τ R) = (D.actN i u).interp τ R := by
  cases u with
  | zero => simp [actN]
  | root m c =>
    rcases hu with rfl | hm
    · simp [actN]
    · rw [interp_root_without117, map_smul, weylElt_rootVec i 1 (isRoot_rootCertificate_root hm)]
      simp only [actN, interp_root_without117, one_zpow, Units.val_one, mul_one, smul_smul,
        root_img_without117 hT hm, dn_eq_without117 hT hm, Int.cast_mul, Int.cast_pow,
            Int.cast_neg, Int.cast_one]
  | hvec v => rw [weylElt_interp_hvec_without117, actN, interp_norm_without117]

theorem weylElt_inv_interp_without117
    (hT : D.checkTables = true) (i : Fin τ.rank) {u : AVec}
    (hu : u.WF τ) :
    (((weylElt τ R i 1)⁻¹ : (Module.End R (RootModule τ R))ˣ) : Module.End R (RootModule τ R))
        (u.interp τ R) = (D.actNinv i u).interp τ R := by
  rw [weylElt_inv]
  cases u with
  | zero => simp [actNinv]
  | root m c =>
    rcases hu with rfl | hm
    · simp [actNinv]
    · rw [interp_root_without117, map_smul, weylElt_rootVec i (-1) (isRoot_rootCertificate_root hm)]
      simp only [actNinv, interp_root_without117, smul_smul, root_img_without117 hT hm,
          dn_eq_without117 hT hm, par_eq_without117 hT hm,
        units_neg_one_zpow_without117, Int.natAbs_neg, pow_add, Int.cast_mul, Int.cast_pow,
            Int.cast_neg,
        Int.cast_one]
  | hvec v => rw [weylElt_interp_hvec_without117, actNinv, interp_norm_without117]

theorem actN_wf_without117
    (hT : D.checkTables = true) (i : Fin τ.rank) {u : AVec} (hu : u.WF τ) :
    (D.actN i u).WF τ := by
  cases u with
  | zero => trivial
  | root m c =>
    rcases hu with rfl | hm
    · exact Or.inl (zero_mul _)
    · exact Or.inr (img_lt_without117 hT hm i)
  | hvec v => exact WF.norm_without117 (show (AVec.hvec (hReflect i v)).WF τ from
      hReflect_length_without117 i v)

theorem actNinv_wf_without117
    (hT : D.checkTables = true) (i : Fin τ.rank) {u : AVec} (hu : u.WF τ) :
    (D.actNinv i u).WF τ := by
  cases u with
  | zero => trivial
  | root m c =>
    rcases hu with rfl | hm
    · exact Or.inl (zero_mul _)
    · exact Or.inr (img_lt_without117 hT hm i)
  | hvec v => exact WF.norm_without117 (show (AVec.hvec (hReflect i v)).WF τ from
      hReflect_length_without117 i v)

theorem coroot_length_without117 (k : ℕ) : (D.coroot k).length = τ.rank := by
  simp [coroot]

theorem actM_root_wf_without117 (M k b : ℕ) (c : ℤ) (h : (D.actM M k (.root b 1)).WF τ) :
    (D.actM M k (.root b c)).WF τ := by
  simp only [actM] at h ⊢
  split_ifs with h1 h2
  · exact WF.norm_without117 (by simp [WF, coroot_length_without117])
  · trivial
  · rw [ite_eq_right h1, ite_eq_right h2] at h
    simp only [AVec.norm] at h ⊢
    split_ifs with hc
    · trivial
    · split_ifs at h with hN
      · rw [one_mul] at hN
        exact absurd (by rw [hN, mul_zero]) hc
      · rcases h with h | h
        · exact absurd h hN
        · exact Or.inr h

theorem act_wf_without117 {k : ℕ} (hk : k < τ.rootCertificate.roots.length) (hP : D.ActWF k) {u :
    AVec}
    (hu : u.WF τ) : (D.act k u).WF τ := by
  cases u with
  | zero => trivial
  | root m c =>
    rcases hu with rfl | hm
    · simp only [act, actM]
      split_ifs
      · exact WF.norm_without117 (by simp [WF, coroot_length_without117])
      · trivial
      · simp [AVec.norm, WF]
    · exact D.actM_root_wf_without117 _ k m c (hP m hm)
  | hvec v =>
    simp only [act, actM]
    exact WF.norm_without117 (Or.inr hk)

theorem checkSimple_at_without117 (hS : D.checkSimple = true) (i : Fin τ.rank) :
    (∀ b < τ.rootCertificate.roots.length, D.act i (.root b 1) =
      if b = i then .zero
      else if b = D.neg i then .hvec (hUnit i)
      else if D.upI b i = 0 then .zero
      else .root (D.upI b i - 1) ((D.dn b i : ℤ) + 1)) ∧
    ∀ m : Fin τ.rank, D.act i (.hvec (hUnit m)) = AVec.norm (.root i ((τ.cartan m i).natAbs :
        ℤ)) := by
  simp only [checkSimple, nR, List.all_eq_true, List.mem_finRange, List.mem_range,
    Bool.and_eq_true, AVec.beq_iff_without117, true_implies] at hS
  exact ⟨fun b hb => ((hS i).1 b hb).1, fun m => ((hS i).2 m).1⟩

theorem pos_eq_simple_iff_without117
    {α : {v : Fin τ.rank → ℤ // IsRoot τ v}} (i : Fin τ.rank) :
    pos α = i ↔ α.1 = Pi.single i 1 := by
  rw [pos_eq_iff_without117 (CFSG.LieType.Chevalley.RootOps.val_lt_rootCertificate_length i),
      root_simple_without117, eq_comm]

theorem pos_eq_neg_simple_iff_without117
    (hT : D.checkTables = true)
    {α : {v : Fin τ.rank → ℤ // IsRoot τ v}} (i : Fin τ.rank) :
    pos α = D.neg i ↔ α.1 = -Pi.single i 1 := by
  rw [pos_eq_iff_without117 (neg_lt_without117 hT
      (CFSG.LieType.Chevalley.RootOps.val_lt_rootCertificate_length i)),
          root_neg_without117 hT (CFSG.LieType.Chevalley.RootOps.val_lt_rootCertificate_length i),
              root_simple_without117, eq_comm]

theorem recOp_simple_without117
    (hT : D.checkTables = true) (hS : D.checkSimple = true) (i : Fin τ.rank) :
    D.recOp R i = infE τ R i := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [recOp_single_without117]
  rcases b with m | ⟨α, hα⟩
  · change _ = infE τ R i (hVec τ R m)
    simp only [ofLabel]
    rw [(checkSimple_at_without117 hS i).2 m, interp_norm_without117, interp_root_without117,
        infE_hVec, root_simple_without117,
      Int.cast_natCast]
  · rw [← rootVec_of_isRoot'_without117 hα]
    simp only [ofLabel]
    rw [(checkSimple_at_without117 hS i).1 _ (pos_lt_without117 _)]
    by_cases h₁ : α = Pi.single i 1
    · subst h₁
      rw [ite_eq_left ((pos_eq_simple_iff_without117 i).2 rfl), interp_zero_without117,
          infE_rootVec_single]
    rw [ite_eq_right (mt (pos_eq_simple_iff_without117 i).1 h₁)]
    by_cases h₂ : α = -Pi.single i 1
    · subst h₂
      rw [ite_eq_left ((pos_eq_neg_simple_iff_without117 hT i).2 rfl), infE_rootVec_neg_single,
        interp_hvec_without117]
      simp only [hUnit_getD_without117]
      simp [hVec]
    rw [ite_eq_right (mt (pos_eq_neg_simple_iff_without117 hT i).1 h₂),
        infE_rootVec_of_ne i hα h₁ h₂]
    have hp := pos_lt_without117 (⟨α, hα⟩ : {v : Fin τ.rank → ℤ // IsRoot τ v})
    have hr := root_pos_without117 (⟨α, hα⟩ : {v : Fin τ.rank → ℤ // IsRoot τ v})
    split_ifs with hu
    · rw [interp_zero_without117, rootVec_of_not_isRoot'_without117
        (by simpa [hr] using not_isRoot_of_upI_without117 hT hp hu),
        smul_zero]
    · obtain ⟨-, hm⟩ := upI_spec_without117 hT hp hu
      rw [interp_root_without117, hm, dn_eq_without117 hT hp, hr]
      push_cast
      rfl

theorem actWF_simple_without117 (hT : D.checkTables = true) (hS : D.checkSimple = true) (i : Fin
    τ.rank) :
    D.ActWF i := by
  intro b hb
  rw [(checkSimple_at_without117 hS i).1 b hb]
  split_ifs with h1 h2 h3
  · trivial
  · exact hUnit_length_without117 i
  · trivial
  · exact Or.inr (upI_spec_without117 hT hb h3).1

end AdjData
end CFSG.LieType.Steinberg.Adjoint
end
end
end
end
end
end
end

end
