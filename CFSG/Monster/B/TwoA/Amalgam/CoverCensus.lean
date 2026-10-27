module

public import CFSG.Monster.B.Geometry.F4Census
public import CFSG.Monster.B.Geometry.ChamberCover
public import CFSG.Monster.B.Geometry.ResidueBuilding

public section

namespace CFSG.Monster.B.Geometry

open CoxeterSystem CFSG.LieType.Chevalley.CosetBuilding

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
variable {C : Type*} {δ : C → C → W}

namespace IsBuildingOn

variable {J : Set ι} {R : Set C} (hB : IsBuildingOn cs δ J R) {q : ι → ℕ}
  (hpan : ∀ y ∈ R, ∀ j ∈ J, {z | z ∈ R ∧ δ y z = cs.simple j}.encard = q j)
include hB hpan

theorem ncard_shellIn_mul_simple {x : C} (hx : x ∈ R) {w : W} {j : ι} (hj : j ∈ J)
    (hw : cs.length (w * cs.simple j) = cs.length w + 1)
    (hfin : {y | y ∈ R ∧ δ x y = w}.Finite) :
    {y | y ∈ R ∧ δ x y = w * cs.simple j}.Finite ∧
      {y | y ∈ R ∧ δ x y = w * cs.simple j}.ncard = {y | y ∈ R ∧ δ x y = w}.ncard * q j := by
  classical
  have hex : ∀ d : ↥{d | d ∈ R ∧ δ x d = w * cs.simple j},
      ∃ z, z ∈ R ∧ δ d.1 z = cs.simple j ∧ δ x z = w := by
    intro d
    obtain ⟨hdR, hd⟩ := d.2
    obtain ⟨z, hz, h1, h2⟩ := hB.exists_simple x hx d.1 hdR j hj
    refine ⟨z, hz, h1, ?_⟩
    rw [h2, hd, mul_assoc, cs.simple_mul_simple_self, mul_one]
  choose φ hφR hφ1 hφ2 using hex
  have hup : ∀ b d : C, b ∈ R → δ x b = w → d ∈ R → δ b d = cs.simple j →
      δ x d = w * cs.simple j := by
    intro b d hb hbw hd hbd
    rw [← hbw]
    exact (hB.mul_simple x hx b hb d hd j hj hbd).2 (by rw [hbw]; exact hw)
  have huniq : ∀ b z d : C, b ∈ R → z ∈ R → d ∈ R → δ x b = w → δ x z = w →
      δ b d = cs.simple j → δ z d = cs.simple j → b = z := by
    intro b z d hb hz hd hbw hzw hbd hzd
    by_contra hne
    have hbz := hB.dist_eq_simple_of_eq_simple hb hd hz hj hbd hzd hne
    have h := (hB.mul_simple x hx b hb z hz j hj hbz).2 (by rw [hbw]; exact hw)
    rw [hzw, hbw] at h
    exact cs.simple_ne_one j (left_eq_mul.mp h)
  have hback : ∀ d : ↥{d | d ∈ R ∧ δ x d = w * cs.simple j}, δ (φ d) d.1 = cs.simple j :=
    fun d => hB.symm_of_eq_simple d.2.1 (hφR d) hj (hφ1 d)
  let e : ↥{d | d ∈ R ∧ δ x d = w * cs.simple j} ≃
      Σ b : ↥{b | b ∈ R ∧ δ x b = w}, ↥{z | z ∈ R ∧ δ b.1 z = cs.simple j} :=
    { toFun := fun d => ⟨⟨φ d, hφR d, hφ2 d⟩, d.1, d.2.1, hback d⟩
      invFun := fun p => ⟨p.2.1, p.2.2.1, hup p.1.1 p.2.1 p.1.2.1 p.1.2.2 p.2.2.1 p.2.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun p => by
        refine Sigma.subtype_ext (Subtype.ext ?_) rfl
        have hd : δ x p.2.1 = w * cs.simple j :=
          hup p.1.1 p.2.1 p.1.2.1 p.1.2.2 p.2.2.1 p.2.2.2
        exact huniq _ _ p.2.1 (hφR ⟨p.2.1, p.2.2.1, hd⟩) p.1.2.1 p.2.2.1
          (hφ2 ⟨p.2.1, p.2.2.1, hd⟩) p.1.2.2 (hback ⟨p.2.1, p.2.2.1, hd⟩) p.2.2.2 }
  have hfib : ∀ b : C, b ∈ R → {z | z ∈ R ∧ δ b z = cs.simple j}.Finite ∧
      {z | z ∈ R ∧ δ b z = cs.simple j}.ncard = q j := by
    intro b hb
    have h := hpan b hb j hj
    exact ⟨Set.finite_of_encard_eq_coe h, by rw [Set.ncard_def, h, ENat.toNat_natCast]⟩
  have : Finite ↥{b | b ∈ R ∧ δ x b = w} := hfin.to_subtype
  have : Fintype ↥{b | b ∈ R ∧ δ x b = w} := Fintype.ofFinite _
  have : ∀ b : ↥{b | b ∈ R ∧ δ x b = w}, Finite ↥{z | z ∈ R ∧ δ b.1 z = cs.simple j} :=
    fun b => (hfib b.1 b.2.1).1.to_subtype
  have : Finite ↥{d | d ∈ R ∧ δ x d = w * cs.simple j} := Finite.of_equiv _ e.symm
  refine ⟨Set.toFinite _, ?_⟩
  rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_sigma,
    ← Nat.card_coe_set_eq {b | b ∈ R ∧ δ x b = w}, Nat.card_eq_fintype_card,
    Finset.sum_congr rfl fun b _ => (Nat.card_coe_set_eq _).trans (hfib b.1 b.2.1).2,
    Finset.sum_const, Finset.card_univ, smul_eq_mul]

theorem shellIn_wordProd {x : C} (hx : x ∈ R) {ω : List ι} (hω : cs.IsReduced ω)
    (hωJ : ∀ i ∈ ω, i ∈ J) :
    {y | y ∈ R ∧ δ x y = cs.wordProd ω}.Finite ∧
      {y | y ∈ R ∧ δ x y = cs.wordProd ω}.ncard = wordWeight q ω := by
  induction ω using List.reverseRecOn with
  | nil =>
    have h : {y | y ∈ R ∧ δ x y = cs.wordProd []} = {x} := Set.ext fun y => by
      simp only [Set.mem_ofPred_eq, cs.wordProd_nil, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hy, h⟩
        exact ((hB.eq_one_iff x hx y hy).mp h).symm
      · rintro rfl
        exact ⟨hx, hB.eq_one_self hx⟩
    rw [h]
    exact ⟨Set.finite_singleton x, by simp⟩
  | append_singleton ω i ih =>
    obtain ⟨hfin, hcard⟩ := ih (isReduced_of_isReduced_concat hω)
      (fun k hk => hωJ k (by simp [hk]))
    rw [cs.wordProd_append, cs.wordProd_singleton, wordWeight_concat, ← hcard]
    exact ncard_shellIn_mul_simple hB hpan hx (hωJ i (by simp))
      (length_mul_simple_of_isReduced_concat hω) hfin

theorem finite_ncard_eq_finsum [Finite W] {x : C} (hx : x ∈ R) :
    R.Finite ∧ R.ncard = ∑ᶠ w ∈ (cs.parabolic J : Set W), weylWeight cs q w := by
  classical
  have : Fintype W := Fintype.ofFinite W
  have hshell : ∀ w ∈ cs.parabolic J, {y | y ∈ R ∧ δ x y = w}.Finite ∧
      {y | y ∈ R ∧ δ x y = w}.ncard = weylWeight cs q w := by
    intro w hw
    obtain ⟨hred, hprod⟩ := (cs.exists_isReduced w).choose_spec
    have hw' : cs.wordProd (cs.exists_isReduced w).choose ∈ cs.parabolic J := by
      rw [← hprod]
      exact hw
    have h := shellIn_wordProd hB hpan hx hred (fun i hi =>
      mem_of_isReduced_of_mem_parabolic cs hred hw' hi)
    rw [← hprod] at h
    exact h
  have hRfin : R.Finite := by
    have hsub : R ⊆ ⋃ w ∈ (cs.parabolic J : Set W), {y | y ∈ R ∧ δ x y = w} := fun y hy =>
      Set.mem_biUnion (x := δ x y) (hB.mem_parabolic x hx y hy) ⟨hy, rfl⟩
    exact ((Set.toFinite _).biUnion fun w hw => (hshell w hw).1).subset hsub
  refine ⟨hRfin, ?_⟩
  rw [finsum_mem_eq_toFinset_sum, Set.ncard_eq_toFinset_card R hRfin,
    Finset.card_eq_sum_card_fiberwise (f := δ x) (t := (cs.parabolic J : Set W).toFinset)
      (fun y hy => by
        simp only [Set.mem_toFinset, SetLike.mem_coe] at hy ⊢
        exact hB.mem_parabolic x hx y ((Set.Finite.mem_toFinset hRfin).mp hy))]
  refine Finset.sum_congr rfl fun w hw => ?_
  have hw' : w ∈ cs.parabolic J := by simpa using hw
  rw [← (hshell w hw').2, ← Set.ncard_coe_finset]
  congr 1
  ext y
  simp

end IsBuildingOn

namespace ChamberSystem

variable {X : ChamberSystem ι C}

theorem finite_ncard_residue_of_isResidueBuilding [Finite W] {J : Set ι} {x : C} {q : ι → ℕ}
    (hX : X.IsResidueBuilding cs J x)
    (hpanel : ∀ y ∈ X.residue J x, ∀ j ∈ J, (X.residue {j} y).encard = q j + 1) :
    (X.residue J x).Finite ∧
      (X.residue J x).ncard = ∑ᶠ w ∈ (cs.parabolic J : Set W), weylWeight cs q w := by
  obtain ⟨δ, hB, hadj⟩ := hX
  refine hB.finite_ncard_eq_finsum (fun y hy j hj => ?_) (X.self_mem_residue J x)
  have hsub : X.residue {j} y ⊆ X.residue J x := fun z hz =>
    mem_residue_trans hy (X.residue_mono (Set.singleton_subset_iff.mpr hj) y hz)
  have heq : {z | z ∈ X.residue J x ∧ δ y z = cs.simple j} = X.residue {j} y \ {y} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hz, h⟩
      refine ⟨mem_residue_singleton.mpr ((hadj y hy z hz j hj).mpr (Or.inr h)), fun hzy => ?_⟩
      rw [hzy, hB.eq_one_self hy] at h
      exact cs.simple_ne_one j h.symm
    · rintro ⟨hz, hne⟩
      have hzR := hsub hz
      refine ⟨hzR, ?_⟩
      rcases (hadj y hy z hzR j hj).mp (mem_residue_singleton.mp hz) with h | h
      · exact absurd ((hB.eq_one_iff y hy z hzR).mp h).symm hne
      · exact h
  rw [heq, Set.encard_sdiff_singleton_of_mem (X.self_mem_residue {j} y), hpanel y hy j hj,
    ← ENat.natCast_one, ← ENat.natCast_add, ← ENat.natCast_sub, Nat.add_sub_cancel]

variable {c₀ : C}

theorem image_coverProj_residue (J : Set ι) (a : X.Cover c₀) :
    X.coverProj c₀ '' (X.universalCover c₀).residue J a = X.residue J (X.coverProj c₀ a) := by
  obtain ⟨γ, hγ, rfl⟩ := exists_eq_cls a
  refine Set.Subset.antisymm (isMorphism_coverProj.mapsTo_residue J _).image_subset ?_
  rintro d ⟨η, hη, hηJ, rfl⟩
  rw [coverProj_cls hγ] at hη ⊢
  refine ⟨X.cls c₀ (γ ++ η), (mem_residue_universalCover_iff hγ).mpr ⟨η, hη, hηJ, rfl⟩, ?_⟩
  rw [coverProj_cls (hγ.append hη), galleryEnd_append]

theorem isResidueIso_coverProj_of_injOn {J : Set ι} {a : X.Cover c₀}
    (hinj : Set.InjOn (X.coverProj c₀) ((X.universalCover c₀).residue J a)) :
    IsResidueIso (X.universalCover c₀) X (X.coverProj c₀) J a := by
  refine ⟨⟨isMorphism_coverProj.mapsTo_residue J a, hinj, ?_⟩, ?_⟩
  · rw [← image_coverProj_residue J a]
    exact Set.surjOn_image _ _
  · obtain ⟨γ, hγ, rfl⟩ := exists_eq_cls a
    intro b hb b' hb' j hj
    refine ⟨fun h => ?_, isMorphism_coverProj j b b'⟩
    obtain ⟨η, hη, hηJ, rfl⟩ := (mem_residue_universalCover_iff hγ).mp hb
    have hγη := hγ.append hη
    rw [coverProj_cls hγη] at h
    set y := X.coverProj c₀ b' with hy
    have hγηy : X.IsGallery c₀ (γ ++ η ++ [(j, y)]) := (isGallery_concat _ _ _).mpr ⟨hγη, h⟩
    have hmem : X.cls c₀ (γ ++ η ++ [(j, y)]) ∈
        (X.universalCover c₀).residue J (X.cls c₀ γ) := by
      refine (mem_residue_universalCover_iff hγ).mpr ⟨η ++ [(j, y)], ?_, ?_, by simp⟩
      · exact (isGallery_concat _ _ _).mpr ⟨hη, by rwa [← galleryEnd_append]⟩
      · intro i hi
        simp only [galleryType_append, List.mem_append, galleryType_cons, galleryType_nil,
          List.mem_singleton] at hi
        rcases hi with hi | rfl
        · exact hηJ i hi
        · exact hj
    have heq : X.cls c₀ (γ ++ η ++ [(j, y)]) = b' :=
      hinj hmem hb' (by rw [coverProj_cls hγηy, galleryEnd_concat])
    rw [← heq]
    exact (universalCover_adj_cls_iff hγη).mpr ⟨y, h, rfl⟩

end ChamberSystem

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def f4WeightSumIn (p : Fin Tag.F4.rank → Bool) : ℕ :=
  ((List.range 1152).map fun k => if (f4Word k).all p then wordWeight f4q (f4Word k) else 0).sum

theorem finsum_weylWeight_in
    {C : Type*} {δ : C → C → WeylGroup .F4}
    (hδ : IsWeylDistanceBuilding (coxeterSystem .F4) δ)
    (hpanel : ∀ i x, (panel (coxeterSystem .F4) δ i x).encard = f4q i + 1)
    (p : Fin Tag.F4.rank → Bool) :
    ∑ᶠ w ∈ ((coxeterSystem .F4).parabolic {i | p i = true} : Set (WeylGroup .F4)),
      weylWeight (coxeterSystem .F4) f4q w = f4WeightSumIn p := by
  classical
  rw [finsum_mem_def, sum_f4, f4WeightSumIn, ← sum_range_eq_list]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hred := isReduced_f4Word k.2
  rw [Set.indicator_apply]
  have hmem : f4Elem k ∈ ((coxeterSystem .F4).parabolic {i | p i = true} : Set _) ↔
      (f4Word k).all p = true := by
    rw [SetLike.mem_coe, f4Elem, mem_parabolic_iff_of_isReduced _ hred]
    simp [List.all_eq_true]
  by_cases h : (f4Word k).all p = true
  · rw [ite_eq_left (hmem.mpr h), ite_eq_left h, f4Elem, weylWeight_wordProd hδ hpanel hred]
  · rw [ite_eq_right (fun h' => h (hmem.mp h')), ite_eq_right h]

theorem f4WeightSumIn_pairs :
    f4WeightSumIn (fun k => decide ((k : ℕ) ≠ 2 ∧ (k : ℕ) ≠ 3)) = 21 ∧
    f4WeightSumIn (fun k => decide ((k : ℕ) ≠ 1 ∧ (k : ℕ) ≠ 3)) = 15 ∧
    f4WeightSumIn (fun k => decide ((k : ℕ) ≠ 1 ∧ (k : ℕ) ≠ 2)) = 15 ∧
    f4WeightSumIn (fun k => decide ((k : ℕ) ≠ 0 ∧ (k : ℕ) ≠ 3)) = 135 ∧
    f4WeightSumIn (fun k => decide ((k : ℕ) ≠ 0 ∧ (k : ℕ) ≠ 2)) = 15 ∧
    f4WeightSumIn (fun k => decide ((k : ℕ) ≠ 0 ∧ (k : ℕ) ≠ 1)) = 105 := by
  decide +kernel

end CFSG.Monster.B.Geometry
