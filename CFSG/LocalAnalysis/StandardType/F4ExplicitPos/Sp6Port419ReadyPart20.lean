module

public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart19

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
variable {D}

theorem weylSign_eq_without117 (k : ℕ) (i : Fin τ.rank) : D.weylSign k i = 1 ∨
    D.weylSign k i = -1 := by
  unfold weylSign
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem weylSign_mul_self_without117 (k : ℕ) (i : Fin τ.rank) : D.weylSign k i * D.weylSign k i =
    1 := by
  rcases D.weylSign_eq_without117 k i with h | h <;> rw [h] <;> norm_num

theorem checkWeyl_at_without117 (hW : D.checkWeyl = true) {k : ℕ} (hk : k <
    τ.rootCertificate.roots.length)
    (i : Fin τ.rank) :
    ∀ u ∈ basis τ, D.actN i (D.act k (D.actNinv i u)) = (D.act (D.img k i) u).smul (D.weylSign k
        i) := by
  simp only [checkWeyl, checkWeylRange, nR, List.all_eq_true, List.mem_map, List.mem_range,
    List.mem_finRange, true_implies, forall_exists_index, and_imp, weylOne] at hW
  intro u hu
  exact AVec.beq_iff_without117.1 (hW _ k hk (zero_add k) i u hu)

theorem actM_root_wf_of_smul_without117 (M k b : ℕ) {s : ℤ} (hs : s = 1 ∨ s = -1)
    (h : ((D.actM M k (.root b 1)).smul s).WF τ) : (D.actM M k (.root b 1)).WF τ := by
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  simp only [actM] at h ⊢
  split_ifs at h ⊢ with h1 h2
  · exact WF.norm_without117 (by simp [WF, coroot_length_without117])
  · trivial
  · simp only [AVec.norm] at h ⊢
    split_ifs at h ⊢ with hN
    · trivial
    · simp only [AVec.smul, AVec.norm] at h
      rw [ite_eq_right (mul_ne_zero hs0 hN)] at h
      rcases h with h | h
      · exact absurd h (mul_ne_zero hs0 hN)
      · exact Or.inr h

theorem actWF_img_without117
    (hT : D.checkTables = true) (hW : D.checkWeyl = true) {k : ℕ}
    (hk : k < τ.rootCertificate.roots.length) (hP : D.ActWF k) (i : Fin τ.rank) :
    D.ActWF (D.img k i) := by
  intro b hb
  have hu : AVec.root b 1 ∈ basis τ :=
    List.mem_append_left _ (List.mem_map.2 ⟨b, List.mem_range.2 hb, rfl⟩)
  have h := D.checkWeyl_at_without117 hW hk i _ hu
  have hl : (D.actN i (D.act k (D.actNinv i (.root b 1)))).WF τ :=
    actN_wf_without117 hT i (act_wf_without117 hk hP (actNinv_wf_without117 hT i (Or.inr hb)))
  rw [h] at hl
  exact D.actM_root_wf_of_smul_without117 _ _ _ (D.weylSign_eq_without117 k i) hl

theorem pos_reflect_without117
    (hT : D.checkTables = true) {v : Fin τ.rank → ℤ} (hv : IsRoot τ v)
    (i : Fin τ.rank) :
    pos ⟨reflect τ i v, IsRoot.reflect i hv⟩ = D.img (pos ⟨v, hv⟩) i := by
  rw [pos_eq_iff_without117 (img_lt_without117 hT (pos_lt_without117 _) i),
      root_img_without117 hT (pos_lt_without117 _), root_pos_without117]

theorem actWF_pos_without117
    (hT : D.checkTables = true) (hS : D.checkSimple = true)
    (hW : D.checkWeyl = true) {v : Fin τ.rank → ℤ} (hv : IsRoot τ v) : D.ActWF (pos ⟨v, hv⟩) := by
  induction hv with
  | basis j =>
    rw [(pos_eq_simple_iff_without117 j).2 rfl]
    exact actWF_simple_without117 hT hS j
  | reflect i hv ih =>
    rw [pos_reflect_without117 hT hv i]
    exact actWF_img_without117 hT hW (pos_lt_without117 _) ih i

theorem actWF_without117
    (hT : D.checkTables = true) (hS : D.checkSimple = true) (hW : D.checkWeyl = true)
    {k : ℕ} (hk : k < τ.rootCertificate.roots.length) : D.ActWF k := by
  have := actWF_pos_without117 hT hS hW (isRoot_rootCertificate_root hk)
  rwa [pos_root_without117 hk] at this

theorem recOp_weyl_without117
    (hT : D.checkTables = true) (hS : D.checkSimple = true)
    (hW : D.checkWeyl = true) {k : ℕ} (hk : k < τ.rootCertificate.roots.length) (i : Fin τ.rank) :
    (weylElt τ R i 1 : Module.End R (RootModule τ R)) * D.recOp R k *
        (((weylElt τ R i 1)⁻¹ : (Module.End R (RootModule τ R))ˣ) :
          Module.End R (RootModule τ R)) =
      (D.weylSign k i : R) • D.recOp R (D.img k i) := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Module.End.mul_apply,
    LinearMap.smul_apply]
  rw [← interp_ofLabel_without117 R b, weylElt_inv_interp_without117 hT i (ofLabel_wf_without117 b),
    recOp_interp_without117 _ _ (actNinv_wf_without117 hT i (ofLabel_wf_without117 b)),
    weylElt_interp_without117 hT i (act_wf_without117 hk (actWF_without117 hT hS hW hk)
        (actNinv_wf_without117 hT i (ofLabel_wf_without117 b))),
    D.checkWeyl_at_without117 hW hk i _ (ofLabel_mem_basis_without117 b), interp_smul_without117,
    recOp_interp_without117 _ _ (ofLabel_wf_without117 b)]

theorem checkPairs_at_without117 (hP : D.checkPairs = true) {l : ℕ} (hl : l <
    τ.rootCertificate.roots.length)
    (j : Fin τ.rank) (hlj : l ≠ D.neg j) :
    (if D.pairDig l j = 0 then l = j ∨ D.upI l j = 0 else D.pairDig l j / 8 = D.upI l j) ∧
      ∀ u ∈ basis τ, (AVec.sub (D.act j (D.act l u)) (D.act l (D.act j u))) =
        some (if D.pairDig l j = 0 then .zero
          else AVec.smul ((D.pairDig l j % 8 : ℕ) - 4 : ℤ) (D.act (D.pairDig l j / 8 - 1) u)) := by
  simp only [checkPairs, checkPairsRange, nR, List.all_eq_true, List.mem_map, List.mem_range,
    List.mem_finRange, true_implies, forall_exists_index, and_imp] at hP
  have h := hP _ l hl (zero_add l) j
  simp only [Bool.or_eq_true, decide_eq_true_eq, hlj, false_or, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, fun u hu => ?_⟩
  · split_ifs at h1 ⊢
    · simpa using h1
    · simpa using h1
  · simp only [pairOne, List.all_eq_true] at h2
    have h3 := h2 u hu
    rw [← act_eq_without117, ← act_eq_without117, ← act_eq_without117, ← act_eq_without117,
        ← act_eq_without117] at h3
    cases hs : AVec.sub (D.act j (D.act l u)) (D.act l (D.act j u)) with
    | none => rw [hs] at h3; simp [AVec.obeq] at h3
    | some w => rw [hs, AVec.obeq_some_iff_without117] at h3; rw [h3]

theorem recOp_bracket_simple_without117
    (hT : D.checkTables = true) (hS : D.checkSimple = true)
    (hW : D.checkWeyl = true) (hP : D.checkPairs = true) {l : ℕ}
    (hl : l < τ.rootCertificate.roots.length) (j : Fin τ.rank) (hlj : l ≠ D.neg j) :
    D.recOp R j * D.recOp R l - D.recOp R l * D.recOp R j =
      if D.pairDig l j = 0 then 0
      else ((((D.pairDig l j % 8 : ℕ) : ℤ) - 4 : ℤ) : R) • D.recOp R (D.pairDig l j / 8 - 1) := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.sub_apply,
    Module.End.mul_apply]
  have hb := ofLabel_wf_without117 b
  have hlu : (D.act l (ofLabel b)).WF τ := act_wf_without117 hl (actWF_without117 hT hS hW hl) hb
  have hju : (D.act j (ofLabel b)).WF τ :=
    act_wf_without117 (CFSG.LieType.Chevalley.RootOps.val_lt_rootCertificate_length j)
        (actWF_without117 hT hS hW (CFSG.LieType.Chevalley.RootOps.val_lt_rootCertificate_length
            j)) hb
  rw [← interp_ofLabel_without117 R b, recOp_interp_without117 _ _ hb,
      recOp_interp_without117 _ _ hb, recOp_interp_without117 _ _ hlu,
    recOp_interp_without117 _ _ hju,
        ← interp_of_sub_without117 (act_wf_without117
            (CFSG.LieType.Chevalley.RootOps.val_lt_rootCertificate_length j) (actWF_without117 hT
                hS hW (CFSG.LieType.Chevalley.RootOps.val_lt_rootCertificate_length j)) hlu)
      (act_wf_without117 hl (actWF_without117 hT hS hW hl) hju)
      ((D.checkPairs_at_without117 hP hl j hlj).2 _ (ofLabel_mem_basis_without117 b))]
  split_ifs
  · rfl
  · rw [interp_smul_without117, LinearMap.smul_apply, recOp_interp_without117 _ _ hb]

end AdjData

end CFSG.LieType.Steinberg.Adjoint

end

public noncomputable section

namespace CFSG.LieType.Steinberg.Adjoint

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.RootWalk

universe u

variable {τ : Tag}

theorem sRoot_sRoot_without117
    (i : Fin τ.rank) (α : {v : Fin τ.rank → ℤ // IsRoot τ v}) :
    sRoot i (sRoot i α) = α :=
  Subtype.ext (reflect_reflect τ i α.1)

theorem reflect_add_without117
    (i : Fin τ.rank) (u v : Fin τ.rank → ℤ) :
    reflect τ i (u + v) = reflect τ i u + reflect τ i v := by
  rw [← reflectHom_apply, ← reflectHom_apply, ← reflectHom_apply, map_add]

theorem reflect_sub_without117
    (i : Fin τ.rank) (u v : Fin τ.rank → ℤ) :
    reflect τ i (u - v) = reflect τ i u - reflect τ i v := by
  rw [← reflectHom_apply, ← reflectHom_apply, ← reflectHom_apply, map_sub]

theorem not_isRoot_single_add_single_without117 (j : Fin τ.rank) :
    ¬IsRoot τ (Pi.single j 1 + Pi.single j 1) := by
  rw [← two_smul ℤ, isRoot_smul_single_iff]
  omega

theorem units_conj_comm_without117 {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (g : (Module.End R M)ˣ) (a b : Module.End R M) :
    (g : Module.End R M) * (a * b - b * a) * ((g⁻¹ : (Module.End R M)ˣ) : Module.End R M) =
      (g : Module.End R M) * a * ((g⁻¹ : (Module.End R M)ˣ) : Module.End R M) *
          ((g : Module.End R M) * b * ((g⁻¹ : (Module.End R M)ˣ) : Module.End R M)) -
        (g : Module.End R M) * b * ((g⁻¹ : (Module.End R M)ˣ) : Module.End R M) *
          ((g : Module.End R M) * a * ((g⁻¹ : (Module.End R M)ˣ) : Module.End R M)) := by
  simp only [mul_sub, sub_mul, mul_assoc, Units.inv_mul_cancel_left]

theorem stringNorm_of_isRoot_without117 {β γ : Fin τ.rank → ℤ} (h : IsRoot τ (γ - β)) :
    stringNorm β γ = 2 := by
  classical
  exact ite_eq_left h

theorem stringNorm_of_not_isRoot_without117 {β γ : Fin τ.rank → ℤ} (h : ¬IsRoot τ (γ - β)) :
    stringNorm β γ = 1 := by
  classical
  exact ite_eq_right h

theorem stringNorm_reflect_without117
    (i : Fin τ.rank) (β γ : Fin τ.rank → ℤ) :
    stringNorm (reflect τ i β) (reflect τ i γ) = stringNorm β γ := by
  by_cases h : IsRoot τ (γ - β)
  · rw [stringNorm_of_isRoot_without117 h, stringNorm_of_isRoot_without117]
    rw [← reflect_sub_without117, isRoot_reflect_iff]
    exact h
  · rw [stringNorm_of_not_isRoot_without117 h, stringNorm_of_not_isRoot_without117]
    rw [← reflect_sub_without117, isRoot_reflect_iff]
    exact h

namespace AdjData

variable (D : AdjData τ)

variable {D}

theorem checkPairNorm_at_without117 (hN : D.checkPairNorm = true) {l : ℕ}
    (hl : l < τ.rootCertificate.roots.length) (j : Fin τ.rank) (hlj : l ≠ D.neg j)
    (hlj' : l ≠ j) :
    if D.upI l j = 0 then D.pairDig l j = 0
    else (((D.pairDig l j % 8 : ℕ) : ℤ) - 4).natAbs = if D.downI l j = 0 then 1 else 2 := by
  simp only [checkPairNorm, nR, List.all_eq_true, List.mem_range, List.mem_finRange,
    true_implies] at hN
  have h := hN l hl j
  simp only [Bool.or_eq_true, decide_eq_true_eq, hlj, hlj', false_or] at h
  split_ifs at h ⊢ <;> simpa using h

variable (D) (R : Type*) [CommRing R]

variable {D R}

theorem rootSign_eq_without117
    (α : {v : Fin τ.rank → ℤ // IsRoot τ v}) (i : Fin τ.rank) :
    D.rootSign α i = 1 ∨ D.rootSign α i = -1 :=
  D.weylSign_eq_without117 _ i

theorem rootSign_mul_self_without117
    (α : {v : Fin τ.rank → ℤ // IsRoot τ v}) (i : Fin τ.rank) :
    D.rootSign α i * D.rootSign α i = 1 :=
  D.weylSign_mul_self_without117 _ i

theorem rootOp_congr_without117
    {α β : {v : Fin τ.rank → ℤ // IsRoot τ v}} (h : α.1 = β.1) :
    D.rootOp R α = D.rootOp R β := by
  rw [Subtype.ext h]

theorem rootOp_simple_without117
    (hD : D.Valid) (i : Fin τ.rank) :
    D.rootOp R ⟨Pi.single i 1, isRoot_single τ i⟩ = infE τ R i := by
  rw [rootOp, (pos_eq_simple_iff_without117 i).2 rfl, recOp_simple_without117 hD.tables hD.simple]

theorem rootOp_weyl_without117
    (hD : D.Valid) (α : {v : Fin τ.rank → ℤ // IsRoot τ v}) (i : Fin τ.rank) :
    (weylElt τ R i 1 : Module.End R (RootModule τ R)) * D.rootOp R α *
        (((weylElt τ R i 1)⁻¹ : (Module.End R (RootModule τ R))ˣ) :
          Module.End R (RootModule τ R)) =
      (D.rootSign α i : R) • D.rootOp R (sRoot i α) := by
  rw [rootOp, recOp_weyl_without117 hD.tables hD.simple hD.weyl (pos_lt_without117 α), rootOp,
      sRoot,
    pos_reflect_without117 hD.tables α.2 i]
  rfl

theorem rootOp_reflect_without117
    (hD : D.Valid) (α : {v : Fin τ.rank → ℤ // IsRoot τ v}) (i : Fin τ.rank) :
    D.rootOp R (sRoot i α) = (D.rootSign α i : R) •
      ((weylElt τ R i 1 : Module.End R (RootModule τ R)) * D.rootOp R α *
        (((weylElt τ R i 1)⁻¹ : (Module.End R (RootModule τ R))ˣ) :
          Module.End R (RootModule τ R))) := by
  rw [rootOp_weyl_without117 hD, smul_smul, ← Int.cast_mul, rootSign_mul_self_without117,
      Int.cast_one, one_smul]

theorem rootOp_bracket_single_without117
    (hD : D.Valid) (j : Fin τ.rank)
    (γ : {v : Fin τ.rank → ℤ // IsRoot τ v}) (hγ : γ.1 ≠ -Pi.single j 1) :
    (∀ h : IsRoot τ (Pi.single j 1 + γ.1), ∃ N : ℤ,
      N.natAbs = stringNorm (Pi.single j 1) γ.1 ∧
        ∀ (R : Type u) [CommRing R],
          D.rootOp R ⟨Pi.single j 1, isRoot_single τ j⟩ * D.rootOp R γ -
              D.rootOp R γ * D.rootOp R ⟨Pi.single j 1, isRoot_single τ j⟩ =
            (N : R) • D.rootOp R ⟨Pi.single j 1 + γ.1, h⟩) ∧
      (¬IsRoot τ (Pi.single j 1 + γ.1) → ∀ (R : Type u) [CommRing R],
          D.rootOp R ⟨Pi.single j 1, isRoot_single τ j⟩ * D.rootOp R γ -
              D.rootOp R γ * D.rootOp R ⟨Pi.single j 1, isRoot_single τ j⟩ = 0) := by
  have hT := hD.tables
  set l := pos γ with hl_def
  have hl : l < τ.rootCertificate.roots.length := pos_lt_without117 γ
  have hrl : τ.rootCertificate.root l = γ.1 := root_pos_without117 γ
  have hlj : l ≠ D.neg j := fun h => hγ ((pos_eq_neg_simple_iff_without117 hT j).1 h)
  have hsj : pos (⟨Pi.single j 1, isRoot_single τ j⟩ : {v : Fin τ.rank → ℤ // IsRoot τ v}) = j :=
    (pos_eq_simple_iff_without117 j).2 rfl
  by_cases hlj' : l = j
  · have hγj : γ.1 = Pi.single j 1 := (pos_eq_simple_iff_without117 j).1 hlj'
    have hnr : ¬IsRoot τ (Pi.single j 1 + γ.1) := by
      rw [hγj]
      exact not_isRoot_single_add_single_without117 j
    refine ⟨fun h => absurd h hnr, fun _ R _ => ?_⟩
    rw [rootOp_congr_without117 (R := R) (β := ⟨Pi.single j 1, isRoot_single τ j⟩) hγj, sub_self]
  have hN := checkPairNorm_at_without117 hD.pairNorm hl j hlj hlj'
  have hP := (checkPairs_at_without117 hD.pairs hl j hlj).1
  have hbr := fun (R : Type u) [CommRing R] =>
    recOp_bracket_simple_without117 (R := R) hT hD.simple hD.weyl hD.pairs hl j hlj
  by_cases hu : D.upI l j = 0
  · rw [ite_eq_left hu] at hN
    have hnr : ¬IsRoot τ (Pi.single j 1 + γ.1) := by
      rw [add_comm, ← hrl]
      exact not_isRoot_of_upI_without117 hT hl hu
    refine ⟨fun h => absurd h hnr, fun _ R _ => ?_⟩
    rw [rootOp, rootOp, hsj, hbr R, ite_eq_left hN]
  · rw [ite_eq_right hu] at hN
    have hd : D.pairDig l j ≠ 0 := by
      intro h0
      rw [ite_eq_left h0] at hP
      exact hP.elim hlj' hu
    rw [ite_eq_right hd] at hP
    obtain ⟨hm, hmr⟩ := upI_spec_without117 hT hl hu
    have hdn : IsRoot τ (γ.1 - Pi.single j 1) ↔ D.downI l j ≠ 0 := by
      constructor
      · intro hr h0
        exact not_isRoot_of_downI_without117 hT hl h0 (hrl ▸ hr)
      · intro h0
        rw [← hrl, ← (downI_spec_without117 hT hl h0).2]
        exact isRoot_rootCertificate_root (downI_spec_without117 hT hl h0).1
    refine ⟨fun h => ⟨((D.pairDig l j % 8 : ℕ) : ℤ) - 4, ?_, fun R _ => ?_⟩, fun hnr => ?_⟩
    · rw [hN]
      by_cases hd0 : D.downI l j = 0
      · rw [ite_eq_left hd0, stringNorm_of_not_isRoot_without117 (fun hr => (hdn.1 hr) hd0)]
      · rw [ite_eq_right hd0, stringNorm_of_isRoot_without117 (hdn.2 hd0)]
    · rw [rootOp, rootOp, hsj, hbr R, ite_eq_right hd, rootOp, hP]
      congr 2
      rw [eq_comm, pos_eq_iff_without117 hm, hmr, hrl, add_comm]
    · exact absurd (by rw [add_comm, ← hrl, ← hmr]; exact isRoot_rootCertificate_root hm) hnr

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
