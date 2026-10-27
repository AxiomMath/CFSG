module

public import CFSG.RankThree.Chevalley.SteinbergBID4ThetaFixed
public import CFSG.LieType.Chevalley.TrialityFullAmbientFixedGroup
public import CFSG.RankThree.Chevalley.EvenPinnedRootSL2

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Orbits

variable {K : Type} [Field K] (σ : K →+* K)

theorem ringHom_pow_two_apply (c : K) : (σ ^ 2) c = σ (σ c) := by
  rw [pow_two]
  rfl

theorem coe_orbitX_D4_outer (c : orbitField TwistTag.D4 K σ ⟨0, by decide⟩) :
    (orbitX TwistTag.D4 K σ ⟨0, by decide⟩ c : ModGL TwistTag.D4.tag K) =
      xUnit TwistTag.D4.tag K 0 c * xUnit TwistTag.D4.tag K 1 (σ c) *
        xUnit TwistTag.D4.tag K 3 (σ (σ c)) := by
  rw [coe_orbitX]
  have hcard : (TwistTag.D4.orbit ⟨0, by decide⟩).card = 3 := by decide
  have e0 : TwistTag.D4.orbitMin ⟨0, by decide⟩ = 0 := by decide
  have p1 : TwistTag.D4.perm 0 = 1 := by decide
  have p2 : (TwistTag.D4.perm ^ 2) 0 = 3 := by decide
  have h1 : ∀ c' : K, (1 : K →+* K) c' = c' := fun _ => rfl
  rw [hcard, e0]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_zero, p1, p2,
    Equiv.Perm.coe_one, id_eq, h1, pow_one, ringHom_pow_two_apply, mul_assoc]

theorem coe_orbitY_D4_outer (c : orbitField TwistTag.D4 K σ ⟨0, by decide⟩) :
    (orbitY TwistTag.D4 K σ ⟨0, by decide⟩ c : ModGL TwistTag.D4.tag K) =
      yUnit TwistTag.D4.tag K 0 c * yUnit TwistTag.D4.tag K 1 (σ c) *
        yUnit TwistTag.D4.tag K 3 (σ (σ c)) := by
  rw [coe_orbitY]
  have hcard : (TwistTag.D4.orbit ⟨0, by decide⟩).card = 3 := by decide
  have e0 : TwistTag.D4.orbitMin ⟨0, by decide⟩ = 0 := by decide
  have p1 : TwistTag.D4.perm 0 = 1 := by decide
  have p2 : (TwistTag.D4.perm ^ 2) 0 = 3 := by decide
  have h1 : ∀ c' : K, (1 : K →+* K) c' = c' := fun _ => rfl
  rw [hcard, e0]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_zero, p1, p2,
    Equiv.Perm.coe_one, id_eq, h1, pow_one, ringHom_pow_two_apply, mul_assoc]

theorem coe_orbitX_D4_middle (b : orbitField TwistTag.D4 K σ ⟨1, by decide⟩) :
    (orbitX TwistTag.D4 K σ ⟨1, by decide⟩ b : ModGL TwistTag.D4.tag K) =
      xUnit TwistTag.D4.tag K 2 b := by
  rw [coe_orbitX]
  have hcard : (TwistTag.D4.orbit ⟨1, by decide⟩).card = 1 := by decide
  have e1 : TwistTag.D4.orbitMin ⟨1, by decide⟩ = 2 := by decide
  rw [hcard, e1]
  simp

theorem coe_orbitY_D4_middle (b : orbitField TwistTag.D4 K σ ⟨1, by decide⟩) :
    (orbitY TwistTag.D4 K σ ⟨1, by decide⟩ b : ModGL TwistTag.D4.tag K) =
      yUnit TwistTag.D4.tag K 2 b := by
  rw [coe_orbitY]
  have hcard : (TwistTag.D4.orbit ⟨1, by decide⟩).card = 1 := by decide
  have e1 : TwistTag.D4.orbitMin ⟨1, by decide⟩ = 2 := by decide
  rw [hcard, e1]
  simp

end Orbits


section Generators

open Matrix

variable {Ω : Type} [Field Ω]

abbrev d4QX (k : Fin Tag.D4.rank) (c : Ω) : subsystemGroup Tag.E6 Ω d4Support :=
  ⟨xUnit Tag.E6 Ω (d4Idx k) c, xUnit_mem_subsystemGroup (d4Idx_mem k) c⟩

abbrev d4QY (k : Fin Tag.D4.rank) (c : Ω) : subsystemGroup Tag.E6 Ω d4Support :=
  ⟨yUnit Tag.E6 Ω (d4Idx k) c, yUnit_mem_subsystemGroup (d4Idx_mem k) c⟩

theorem commute_d4QX {k l : Fin Tag.D4.rank} (hkl : Tag.E6.cartan (d4Idx k) (d4Idx l) = 0)
    (c d : Ω) : Commute (d4QX k c) (d4QX l d) := by
  have h0 : (Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ) ⬝ᵥ
      (Tag.E6.symmetrizedCartan *ᵥ Pi.single (d4Idx l) 1) = 0 := by
    rw [Tag.symmetrizedCartan, show Tag.E6.symmetrizer = 1 from rfl, one_mul]
    simpa [mulVec_single] using hkl
  have h := (simply_laced_orthogonal_root_commutation Tag.E6 (Or.inr (Or.inl rfl))).2 Ω _ _
    (isRoot_single _ (d4Idx k)) (isRoot_single _ (d4Idx l)) h0 _
    (Subgroup.subset_closure ⟨c, rfl⟩) _ (Subgroup.subset_closure ⟨d, rfl⟩)
  rw [pinnedX_single, pinnedX_single] at h
  exact Subtype.ext h

theorem commute_d4QY {k l : Fin Tag.D4.rank} (hkl : Tag.E6.cartan (d4Idx k) (d4Idx l) = 0)
    (c d : Ω) : Commute (d4QY k c) (d4QY l d) := by
  have h0 : (-Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ) ⬝ᵥ
      (Tag.E6.symmetrizedCartan *ᵥ -Pi.single (d4Idx l) 1) = 0 := by
    rw [mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg, Tag.symmetrizedCartan,
      show Tag.E6.symmetrizer = 1 from rfl, one_mul]
    simpa [mulVec_single] using hkl
  have h := (simply_laced_orthogonal_root_commutation Tag.E6 (Or.inr (Or.inl rfl))).2 Ω _ _
    (isRoot_neg_single _ (d4Idx k)) (isRoot_neg_single _ (d4Idx l)) h0 _
    (Subgroup.subset_closure ⟨c, rfl⟩) _ (Subgroup.subset_closure ⟨d, rfl⟩)
  rw [pinnedX_neg_single, pinnedX_neg_single] at h
  exact Subtype.ext h

theorem cartan_outer : Tag.E6.cartan (d4Idx 0) (d4Idx 1) = 0 ∧
    Tag.E6.cartan (d4Idx 0) (d4Idx 3) = 0 ∧ Tag.E6.cartan (d4Idx 1) (d4Idx 3) = 0 := by
  decide

abbrev d4OuterX (a a' a'' : Ω) : subsystemGroup Tag.E6 Ω d4Support :=
  d4QX 0 a * d4QX 1 a' * d4QX 3 a''

abbrev d4OuterY (a a' a'' : Ω) : subsystemGroup Tag.E6 Ω d4Support :=
  d4QY 0 a * d4QY 1 a' * d4QY 3 a''

theorem mul_mul_cycle_of_commute {G : Type*} [Group G] {a b c : G} (hab : Commute a b)
    (hac : Commute a c) : b * c * a = a * b * c := by
  rw [mul_assoc, ← hac.eq, ← mul_assoc, ← hab.eq]

theorem mul_mul_cycle_of_commute' {G : Type*} [Group G] {a b c : G} (hac : Commute a c)
    (hbc : Commute b c) : c * a * b = a * b * c := by
  rw [← hac.eq, mul_assoc, ← hbc.eq, ← mul_assoc]


theorem d4QBaseChange_d4QX (Fr : Ω →+* Ω) (k : Fin Tag.D4.rank) (c : Ω) :
    d4QBaseChange Ω Fr (d4QX k c) = d4QX k (Fr c) :=
  Subtype.ext (baseChangeGL_xUnit Fr _ c)

theorem d4QBaseChange_d4QY (Fr : Ω →+* Ω) (k : Fin Tag.D4.rank) (c : Ω) :
    d4QBaseChange Ω Fr (d4QY k c) = d4QY k (Fr c) :=
  Subtype.ext (baseChangeGL_yUnit Fr _ c)

theorem d4Theta_d4QX (Fr : Ω →+* Ω) (k : Fin Tag.D4.rank) (c : Ω) :
    d4Theta Ω Fr 1 (d4QX k c) = d4QX (d4Rho k) (Fr c) ∧
      d4Theta Ω Fr 2 (d4QX k c) = d4QX (d4Rho (d4Rho k)) (Fr c) := by
  refine ⟨?_, ?_⟩
  · rw [d4Theta_apply, d4QBaseChange_d4QX, pow_one]
    exact d4Triality_xUnit k (Fr c)
  · rw [d4Theta_apply, d4QBaseChange_d4QX, pow_two, MulAut.mul_apply]
    rw [show (d4Triality Ω) (d4QX k (Fr c)) = d4QX (d4Rho k) (Fr c) from d4Triality_xUnit k _]
    exact d4Triality_xUnit (d4Rho k) (Fr c)

theorem d4Theta_d4QY (Fr : Ω →+* Ω) (k : Fin Tag.D4.rank) (c : Ω) :
    d4Theta Ω Fr 1 (d4QY k c) = d4QY (d4Rho k) (Fr c) ∧
      d4Theta Ω Fr 2 (d4QY k c) = d4QY (d4Rho (d4Rho k)) (Fr c) := by
  refine ⟨?_, ?_⟩
  · rw [d4Theta_apply, d4QBaseChange_d4QY, pow_one]
    exact d4Triality_yUnit k (Fr c)
  · rw [d4Theta_apply, d4QBaseChange_d4QY, pow_two, MulAut.mul_apply]
    rw [show (d4Triality Ω) (d4QY k (Fr c)) = d4QY (d4Rho k) (Fr c) from d4Triality_yUnit k _]
    exact d4Triality_yUnit (d4Rho k) (Fr c)

theorem d4Rho_values : d4Rho 0 = 1 ∧ d4Rho 1 = 3 ∧ d4Rho 2 = 2 ∧ d4Rho 3 = 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem frob_pow_pow {Fr : Ω →+* Ω} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) (a : Ω) (m : ℕ) :
    Fr (a ^ (q ^ m)) = a ^ (q ^ (m + 1)) := by
  rw [hFr, ← pow_mul, pow_succ]

theorem d4OuterX_mem_d4ThetaFixed {Fr : Ω →+* Ω} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) {e : ℕ}
    (he : e = 1 ∨ e = 2) {a : Ω} (ha : a ^ (q ^ 3) = a) :
    d4OuterX a (a ^ (q ^ e)) (a ^ (q ^ (2 * e))) ∈ d4ThetaFixed Ω Fr e := by
  obtain ⟨h01, h03, h13⟩ := cartan_outer
  rw [mem_d4ThetaFixed, d4OuterX, map_mul, map_mul]
  rcases he with rfl | rfl
  · rw [(d4Theta_d4QX Fr 0 a).1, (d4Theta_d4QX Fr 1 _).1, (d4Theta_d4QX Fr 3 _).1]
    have e1 : Fr a = a ^ (q ^ 1) := by rw [hFr, pow_one]
    have e2 : Fr (a ^ (q ^ 1)) = a ^ (q ^ (2 * 1)) := by rw [frob_pow_pow hFr]
    have e3 : Fr (a ^ (q ^ (2 * 1))) = a := by rw [frob_pow_pow hFr, ha]
    rw [e1, e2, e3]
    exact mul_mul_cycle_of_commute (commute_d4QX h01 _ _) (commute_d4QX h03 _ _)
  · rw [(d4Theta_d4QX Fr 0 a).2, (d4Theta_d4QX Fr 1 _).2, (d4Theta_d4QX Fr 3 _).2]
    have e1 : Fr a = a ^ (q ^ (2 * 2)) := by
      rw [hFr, show 2 * 2 = 3 + 1 by rfl, pow_succ, pow_mul, ha]
    have e2 : Fr (a ^ (q ^ 2)) = a := by rw [frob_pow_pow hFr, ha]
    have e3 : Fr (a ^ (q ^ (2 * 2))) = a ^ (q ^ 2) := by
      rw [frob_pow_pow hFr, show 2 * 2 + 1 = 3 + 2 by rfl, pow_add, pow_mul, ha]
    rw [e1, e2, e3]
    exact mul_mul_cycle_of_commute' (commute_d4QX h03 _ _) (commute_d4QX h13 _ _)

theorem d4OuterY_mem_d4ThetaFixed {Fr : Ω →+* Ω} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) {e : ℕ}
    (he : e = 1 ∨ e = 2) {a : Ω} (ha : a ^ (q ^ 3) = a) :
    d4OuterY a (a ^ (q ^ e)) (a ^ (q ^ (2 * e))) ∈ d4ThetaFixed Ω Fr e := by
  obtain ⟨h01, h03, h13⟩ := cartan_outer
  rw [mem_d4ThetaFixed, d4OuterY, map_mul, map_mul]
  rcases he with rfl | rfl
  · rw [(d4Theta_d4QY Fr 0 a).1, (d4Theta_d4QY Fr 1 _).1, (d4Theta_d4QY Fr 3 _).1]
    have e1 : Fr a = a ^ (q ^ 1) := by rw [hFr, pow_one]
    have e2 : Fr (a ^ (q ^ 1)) = a ^ (q ^ (2 * 1)) := by rw [frob_pow_pow hFr]
    have e3 : Fr (a ^ (q ^ (2 * 1))) = a := by rw [frob_pow_pow hFr, ha]
    rw [e1, e2, e3]
    exact mul_mul_cycle_of_commute (commute_d4QY h01 _ _) (commute_d4QY h03 _ _)
  · rw [(d4Theta_d4QY Fr 0 a).2, (d4Theta_d4QY Fr 1 _).2, (d4Theta_d4QY Fr 3 _).2]
    have e1 : Fr a = a ^ (q ^ (2 * 2)) := by
      rw [hFr, show 2 * 2 = 3 + 1 by rfl, pow_succ, pow_mul, ha]
    have e2 : Fr (a ^ (q ^ 2)) = a := by rw [frob_pow_pow hFr, ha]
    have e3 : Fr (a ^ (q ^ (2 * 2))) = a ^ (q ^ 2) := by
      rw [frob_pow_pow hFr, show 2 * 2 + 1 = 3 + 2 by rfl, pow_add, pow_mul, ha]
    rw [e1, e2, e3]
    exact mul_mul_cycle_of_commute' (commute_d4QY h03 _ _) (commute_d4QY h13 _ _)

theorem d4Middle_mem_d4ThetaFixed {Fr : Ω →+* Ω} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) {e : ℕ}
    (he : e = 1 ∨ e = 2) {b : Ω} (hb : b ^ q = b) :
    d4QX 2 b ∈ d4ThetaFixed Ω Fr e ∧ d4QY 2 b ∈ d4ThetaFixed Ω Fr e := by
  have hFb : Fr b = b := by rw [hFr, hb]
  rw [mem_d4ThetaFixed, mem_d4ThetaFixed]
  rcases he with rfl | rfl
  · rw [(d4Theta_d4QX Fr 2 b).1, (d4Theta_d4QY Fr 2 b).1, hFb]
    exact ⟨rfl, rfl⟩
  · rw [(d4Theta_d4QX Fr 2 b).2, (d4Theta_d4QY Fr 2 b).2, hFb]
    exact ⟨rfl, rfl⟩

variable (Ω) in
@[expose] def d4ThetaGens (q e : ℕ) : Set (subsystemGroup Tag.E6 Ω d4Support) :=
  {g | ∃ a : Ω, a ^ (q ^ 3) = a ∧ (g = d4OuterX a (a ^ (q ^ e)) (a ^ (q ^ (2 * e))) ∨
    g = d4OuterY a (a ^ (q ^ e)) (a ^ (q ^ (2 * e))))} ∪
  {g | ∃ b : Ω, b ^ q = b ∧ (g = d4QX 2 b ∨ g = d4QY 2 b)}

theorem closure_d4ThetaGens_le {Fr : Ω →+* Ω} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) {e : ℕ}
    (he : e = 1 ∨ e = 2) : Subgroup.closure (d4ThetaGens Ω q e) ≤ d4ThetaFixed Ω Fr e := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g (⟨a, ha, rfl | rfl⟩ | ⟨b, hb, rfl | rfl⟩)
  · exact d4OuterX_mem_d4ThetaFixed hFr he ha
  · exact d4OuterY_mem_d4ThetaFixed hFr he ha
  · exact (d4Middle_mem_d4ThetaFixed hFr he hb).1
  · exact (d4Middle_mem_d4ThetaFixed hFr he hb).2

end Generators


section Descent

variable {ℓ d : ℕ} {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {e : ℕ} {σ : K →+* K} {Fr : Ω →+* Ω}

theorem d4Res_image_d4ThetaFixed (hℓ : ℓ.Prime) (hd : 1 ≤ d) (hK : Nat.card K = (ℓ ^ d) ^ 3)
    (he : e = 1 ∨ e = 2) (hσ : ∀ c, σ c = c ^ ((ℓ ^ d) ^ e)) (hFr : ∀ c, Fr c = c ^ (ℓ ^ d))
    (y : ModGL Tag.D4 Ω) :
    (∃ g ∈ d4ThetaFixed Ω Fr e, d4Res Ω g = y) ↔
      y ∈ (graphFixedRootGroup TwistTag.D4 K σ).map (baseChangeGL (algebraMap K Ω)) := by
  have h := (triality_both_field_orientations_simple_full_ambient_fixed_group ℓ d hℓ hd K hK Ω
    e he σ hσ Fr hFr).2.1
  rw [d4Res_mem_fixed_iff Fr he]
  exact Set.ext_iff.1 h y

omit [IsAlgClosure K Ω] in
theorem exists_d4ThetaFixed_equiv_of_image (he : e = 1 ∨ e = 2)
    (himg : ∀ y : ModGL Tag.D4 Ω, (∃ g ∈ d4ThetaFixed Ω Fr e, d4Res Ω g = y) ↔
      y ∈ (graphFixedRootGroup TwistTag.D4 K σ).map (baseChangeGL (algebraMap K Ω))) :
    ∃ φ : d4ThetaFixed Ω Fr e ≃* graphFixedRootGroup TwistTag.D4 K σ,
      ∀ g, baseChangeGL (algebraMap K Ω) (φ g : ModGL TwistTag.D4.tag K) = d4Res Ω g := by
  have hmem : ∀ g : d4ThetaFixed Ω Fr e, ∃ c ∈ graphFixedRootGroup TwistTag.D4 K σ,
      baseChangeGL (algebraMap K Ω) c = d4Res Ω g := fun g =>
    Subgroup.mem_map.1 ((himg _).1 ⟨g, g.2, rfl⟩)
  choose f hf1 hf2 using hmem
  have hinj := baseChangeGL_injective (τ := TwistTag.D4.tag) (algebraMap K Ω)
  let φ : d4ThetaFixed Ω Fr e →* graphFixedRootGroup TwistTag.D4 K σ :=
    { toFun g := ⟨f g, hf1 g⟩
      map_one' := by
        apply Subtype.ext
        apply hinj
        rw [hf2]
        exact (map_one (d4Res Ω)).trans (map_one (baseChangeGL (algebraMap K Ω))).symm
      map_mul' g g' := by
        apply Subtype.ext
        apply hinj
        rw [Subgroup.coe_mul, map_mul (baseChangeGL (algebraMap K Ω)), hf2, hf2, hf2]
        exact map_mul (d4Res Ω) _ _ }
  refine ⟨MulEquiv.ofBijective φ ⟨fun g g' h => ?_, fun c => ?_⟩, fun g => hf2 g⟩
  · have h' : d4Res Ω g = d4Res Ω g' := by
      rw [← hf2, ← hf2]
      exact congrArg (fun x : graphFixedRootGroup TwistTag.D4 K σ =>
        baseChangeGL (algebraMap K Ω) (x : ModGL TwistTag.D4.tag K)) h
    exact Subtype.ext (d4Res_injOn_d4ThetaFixed Fr he g.2 g'.2 h')
  · obtain ⟨g, hg, hgc⟩ := (himg _).2
      (Subgroup.mem_map_of_mem _ c.2)
    refine ⟨⟨g, hg⟩, Subtype.ext (hinj ?_)⟩
    change baseChangeGL (algebraMap K Ω) (f ⟨g, hg⟩) = _
    rw [hf2, hgc]
    rfl

theorem exists_d4ThetaFixed_equiv (hℓ : ℓ.Prime) (hd : 1 ≤ d) (hK : Nat.card K = (ℓ ^ d) ^ 3)
    (he : e = 1 ∨ e = 2) (hσ : ∀ c, σ c = c ^ ((ℓ ^ d) ^ e)) (hFr : ∀ c, Fr c = c ^ (ℓ ^ d)) :
    ∃ φ : d4ThetaFixed Ω Fr e ≃* graphFixedRootGroup TwistTag.D4 K σ,
      ∀ g, baseChangeGL (algebraMap K Ω) (φ g : ModGL TwistTag.D4.tag K) = d4Res Ω g :=
  exists_d4ThetaFixed_equiv_of_image he (d4Res_image_d4ThetaFixed hℓ hd hK he hσ hFr)


theorem d4Res_d4OuterX (a a' a'' : Ω) :
    d4Res Ω (d4OuterX a a' a'') =
      xUnit Tag.D4 Ω 0 a * xUnit Tag.D4 Ω 1 a' * xUnit Tag.D4 Ω 3 a'' := by
  rw [d4OuterX, map_mul, map_mul, d4Res_xUnit, d4Res_xUnit, d4Res_xUnit]

theorem d4Res_d4OuterY (a a' a'' : Ω) :
    d4Res Ω (d4OuterY a a' a'') =
      yUnit Tag.D4 Ω 0 a * yUnit Tag.D4 Ω 1 a' * yUnit Tag.D4 Ω 3 a'' := by
  rw [d4OuterY, map_mul, map_mul, d4Res_yUnit, d4Res_yUnit, d4Res_yUnit]

omit [IsAlgClosure K Ω] in
variable (σ) in
theorem d4Res_d4OuterX_eq_orbitX (c : orbitField TwistTag.D4 K σ ⟨0, by decide⟩) :
    (d4Res Ω (d4OuterX (algebraMap K Ω c) (algebraMap K Ω (σ c))
      (algebraMap K Ω (σ (σ c)))) : ModGL TwistTag.D4.tag Ω) =
      baseChangeGL (algebraMap K Ω) (orbitX TwistTag.D4 K σ ⟨0, by decide⟩ c :
        ModGL TwistTag.D4.tag K) := by
  rw [d4Res_d4OuterX, coe_orbitX_D4_outer, map_mul (baseChangeGL _), map_mul (baseChangeGL _),
    baseChangeGL_xUnit, baseChangeGL_xUnit, baseChangeGL_xUnit]
  rfl

omit [IsAlgClosure K Ω] in
variable (σ) in
theorem d4Res_d4OuterY_eq_orbitY (c : orbitField TwistTag.D4 K σ ⟨0, by decide⟩) :
    (d4Res Ω (d4OuterY (algebraMap K Ω c) (algebraMap K Ω (σ c))
      (algebraMap K Ω (σ (σ c)))) : ModGL TwistTag.D4.tag Ω) =
      baseChangeGL (algebraMap K Ω) (orbitY TwistTag.D4 K σ ⟨0, by decide⟩ c :
        ModGL TwistTag.D4.tag K) := by
  rw [d4Res_d4OuterY, coe_orbitY_D4_outer, map_mul (baseChangeGL _), map_mul (baseChangeGL _),
    baseChangeGL_yUnit, baseChangeGL_yUnit, baseChangeGL_yUnit]
  rfl

omit [IsAlgClosure K Ω] in
variable (σ) in
theorem d4Res_d4QX_eq_orbitX (b : orbitField TwistTag.D4 K σ ⟨1, by decide⟩) :
    (d4Res Ω (d4QX 2 (algebraMap K Ω b)) : ModGL TwistTag.D4.tag Ω) =
      baseChangeGL (algebraMap K Ω) (orbitX TwistTag.D4 K σ ⟨1, by decide⟩ b :
        ModGL TwistTag.D4.tag K) := by
  rw [coe_orbitX_D4_middle, baseChangeGL_xUnit]
  exact d4Res_xUnit _ _

omit [IsAlgClosure K Ω] in
variable (σ) in
theorem d4Res_d4QY_eq_orbitY (b : orbitField TwistTag.D4 K σ ⟨1, by decide⟩) :
    (d4Res Ω (d4QY 2 (algebraMap K Ω b)) : ModGL TwistTag.D4.tag Ω) =
      baseChangeGL (algebraMap K Ω) (orbitY TwistTag.D4 K σ ⟨1, by decide⟩ b :
        ModGL TwistTag.D4.tag K) := by
  rw [coe_orbitY_D4_middle, baseChangeGL_yUnit]
  exact d4Res_yUnit _ _

theorem d4ThetaFixed_eq_closure (hℓ : ℓ.Prime) (hd : 1 ≤ d) (hK : Nat.card K = (ℓ ^ d) ^ 3)
    (he : e = 1 ∨ e = 2) (hσ : ∀ c, σ c = c ^ ((ℓ ^ d) ^ e)) (hFr : ∀ c, Fr c = c ^ (ℓ ^ d)) :
    d4ThetaFixed Ω Fr e = Subgroup.closure (d4ThetaGens Ω (ℓ ^ d) e) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Fintype K := Fintype.ofFinite K
  set q := ℓ ^ d with hqdef
  have hq3 : ∀ c : K, c ^ (q ^ 3) = c := fun c => by
    rw [← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  obtain ⟨σE, hσE⟩ : ∃ σE : K ≃+* K, σE.toRingHom = σ :=
    ⟨RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩,
      RingHom.ext fun _ => rfl⟩
  set A := Subgroup.closure (d4ThetaGens Ω q e)
  have hA : A ≤ d4ThetaFixed Ω Fr e := closure_d4ThetaGens_le hFr he
  set ι := algebraMap K Ω
  have hισ : ∀ c, ι (σ c) = ι c ^ (q ^ e) := fun c => by rw [hσ, map_pow]
  have hισσ : ∀ c, ι (σ (σ c)) = ι c ^ (q ^ (2 * e)) := fun c => by
    rw [hσ, hσ, ← pow_mul, map_pow, two_mul, pow_add]
  have hι3 : ∀ c, ι c ^ (q ^ 3) = ι c := fun c => by rw [← map_pow, hq3]
  let r' : subsystemGroup Tag.E6 Ω d4Support →* ModGL TwistTag.D4.tag Ω := d4Res Ω
  have hgen : ∀ a : Fin TwistTag.D4.foldedTag.rank,
      (orbitRankOneGroup TwistTag.D4 K σ a).map (baseChangeGL ι) ≤ A.map r' := by
    intro a
    rw [orbitRankOneGroup, MonoidHom.map_closure, Subgroup.closure_le]
    obtain ⟨n, hn⟩ := a
    have hn' : n < 2 := hn
    interval_cases n
    · rintro _ ⟨_, ⟨c, rfl⟩ | ⟨c, rfl⟩, rfl⟩
      · refine ⟨d4OuterX (ι c) (ι c ^ (q ^ e)) (ι c ^ (q ^ (2 * e))),
          Subgroup.subset_closure (Or.inl ⟨ι c, hι3 c, Or.inl rfl⟩), ?_⟩
        have h := d4Res_d4OuterX_eq_orbitX (Ω := Ω) σ c
        rw [hισ, hισσ] at h
        exact h
      · refine ⟨d4OuterY (ι c) (ι c ^ (q ^ e)) (ι c ^ (q ^ (2 * e))),
          Subgroup.subset_closure (Or.inl ⟨ι c, hι3 c, Or.inr rfl⟩), ?_⟩
        have h := d4Res_d4OuterY_eq_orbitY (Ω := Ω) σ c
        rw [hισ, hισσ] at h
        exact h
    · have hb : ∀ b : orbitField TwistTag.D4 K σ ⟨1, by decide⟩, ι b ^ q = ι b := by
        intro b
        have hb1 : σ b = b := by
          have := (mem_orbitField (t := TwistTag.D4) (σ := σ)).1 b.2
          rwa [show (TwistTag.D4.orbit ⟨1, by decide⟩).card = 1 by decide, pow_one] at this
        rw [hσ] at hb1
        rw [← map_pow]
        congr 1
        rcases he with rfl | rfl
        · rwa [pow_one] at hb1
        · calc (b : K) ^ q = ((b : K) ^ (q ^ 2)) ^ q := by rw [hb1]
            _ = b := by rw [← pow_mul, ← pow_succ, hq3]
      rintro _ ⟨_, ⟨b, rfl⟩ | ⟨b, rfl⟩, rfl⟩
      · exact ⟨d4QX 2 (ι b), Subgroup.subset_closure (Or.inr ⟨ι b, hb b, Or.inl rfl⟩),
          d4Res_d4QX_eq_orbitX (Ω := Ω) σ b⟩
      · exact ⟨d4QY 2 (ι b), Subgroup.subset_closure (Or.inr ⟨ι b, hb b, Or.inr rfl⟩),
          d4Res_d4QY_eq_orbitY (Ω := Ω) σ b⟩
  have hC0 := (exceptional_fixed_simple_pair_generation TwistTag.D4 K σE).1
  rw [hσE] at hC0
  refine le_antisymm (fun g hg => ?_) hA
  obtain ⟨c, hc, hcg⟩ := Subgroup.mem_map.1 ((d4Res_image_d4ThetaFixed hℓ hd hK he hσ hFr _).1
    ⟨g, hg, rfl⟩)
  have hc' : baseChangeGL ι c ∈ (graphFixedRootGroup TwistTag.D4 K σ).map (baseChangeGL ι) :=
    Subgroup.mem_map_of_mem _ hc
  rw [hC0, Subgroup.map_iSup] at hc'
  obtain ⟨h, hhA, hh⟩ := (iSup_le hgen) hc'
  have e1 : h = g := d4Res_injOn_d4ThetaFixed Fr he (hA hhA) hg (hh.trans hcg)
  rw [← e1]
  exact hhA

end Descent


section SL2

open CFSG.LocalAnalysis.ComponentInitial

variable {Ω : Type} [Field Ω]

theorem simpleRootSL2_injective_of_field (τ : Tag) (i : Fin τ.rank) :
    Function.Injective (simpleRootSL2 τ Ω i) := by
  by_cases h2 : ringChar Ω = 2
  · have : CharP Ω 2 := ringChar.of_eq h2
    exact simpleRootSL2_injective_of_charTwo i
  · exact simpleRootSL2_injective h2 i

theorem exists_d4ThetaFixed_SL2 {Fr : Ω →+* Ω} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) {e : ℕ}
    (he : e = 1 ∨ e = 2) :
    ∃ ψ : SL2 (RingHom.eqLocusField Fr (RingHom.id Ω)) →* d4ThetaFixed Ω Fr e,
      Function.Injective ψ ∧ ∀ b : RingHom.eqLocusField Fr (RingHom.id Ω),
        (((ψ (uSL b) : subsystemGroup Tag.E6 Ω d4Support) : ModGL Tag.E6 Ω) =
          xUnit Tag.E6 Ω 3 b) ∧
        (((ψ (vSL b) : subsystemGroup Tag.E6 Ω d4Support) : ModGL Tag.E6 Ω) =
          yUnit Tag.E6 Ω 3 b) := by
  set k := RingHom.eqLocusField Fr (RingHom.id Ω)
  set F : SL2 k →* ModGL Tag.E6 Ω :=
    (simpleRootSL2 Tag.E6 Ω 3).comp (Matrix.SpecialLinearGroup.map k.subtype)
  have hFu : ∀ b : k, F (uSL b) = xUnit Tag.E6 Ω 3 b := fun b => by
    simp only [F, MonoidHom.comp_apply, map_uSL, simpleRootSL2_uSL]
    rfl
  have hFv : ∀ b : k, F (vSL b) = yUnit Tag.E6 Ω 3 b := fun b => by
    simp only [F, MonoidHom.comp_apply, map_vSL, simpleRootSL2_vSL]
    rfl
  have hb : ∀ b : k, (b : Ω) ^ q = b := fun b => by
    rw [← hFr]
    exact b.2
  set T : Subgroup (SL2 k) :=
    ((d4ThetaFixed Ω Fr e).map (subsystemGroup Tag.E6 Ω d4Support).subtype).comap F
  have hT : T = ⊤ := by
    refine eq_top_iff.2 ?_
    rw [← (sl2_closure_upper_lower : Subgroup.closure (Set.range (uSL (K := k)) ∪
      Set.range vSL) = ⊤), Subgroup.closure_le]
    rintro _ (⟨b, rfl⟩ | ⟨b, rfl⟩)
    · exact ⟨d4QX 2 b, (d4Middle_mem_d4ThetaFixed hFr he (hb b)).1, (hFu b).symm⟩
    · exact ⟨d4QY 2 b, (d4Middle_mem_d4ThetaFixed hFr he (hb b)).2, (hFv b).symm⟩
  have hmem : ∀ A, ∃ g ∈ d4ThetaFixed Ω Fr e, (g : ModGL Tag.E6 Ω) = F A := fun A => by
    have h : A ∈ T := hT ▸ Subgroup.mem_top A
    obtain ⟨g, hg, hgA⟩ := Subgroup.mem_map.1 h
    exact ⟨g, hg, hgA⟩
  choose f hf1 hf2 using hmem
  have hQ : ∀ A, F A ∈ subsystemGroup Tag.E6 Ω d4Support := fun A => by
    rw [← hf2 A]
    exact (f A).2
  let G : SL2 k →* subsystemGroup Tag.E6 Ω d4Support := F.codRestrict _ hQ
  have hG : ∀ A, G A ∈ d4ThetaFixed Ω Fr e := fun A => by
    have e1 : G A = f A := Subtype.ext (hf2 A).symm
    rw [e1]
    exact hf1 A
  refine ⟨G.codRestrict _ hG, fun A B h => ?_, fun b => ⟨hFu b, hFv b⟩⟩
  have h' : F A = F B := congrArg (fun g : d4ThetaFixed Ω Fr e =>
    ((g : subsystemGroup Tag.E6 Ω d4Support) : ModGL Tag.E6 Ω)) h
  have hmap : Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2) k.subtype) :=
    fun X Y hXY => Subtype.ext (Matrix.ext fun i j => Subtype.ext (congrFun (congrFun
      (congrArg Subtype.val hXY) i) j))
  exact hmap (simpleRootSL2_injective_of_field Tag.E6 3 h')

end SL2

end CFSG.RankThree.Chevalley
