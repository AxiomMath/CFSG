module

public import CFSG.RankThree.E6.RootLatticeTools
public import CFSG.LieType.Chevalley.LangWeylChamberStabilizers
public import CFSG.RankThree.Chevalley.EWeylLengthPolynomials
public import CFSG.LieType.Chevalley.FoldedWeylData

public noncomputable section

namespace CFSG.RankThree.E6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint RootSpace

section Dual

variable {K : Type*} [CommRing K]

theorem charVal_sub (z : Fin Tag.E6.rank → K) (x y : Fin Tag.E6.rank → ℤ) :
    charVal z (x - y) = charVal z x - charVal z y := by
  rw [sub_eq_add_neg, charVal_add, charVal_neg, ← sub_eq_add_neg]

@[expose] def dualWeylStabilizer (z : Fin Tag.E6.rank → K) : Subgroup (WeylGroup Tag.E6) where
  carrier := {w | ∀ x, charVal z (w • x) = charVal z x}
  one_mem' x := by rw [one_smul]
  mul_mem' {w w'} hw hw' x := by rw [mul_smul, hw, hw']
  inv_mem' {w} hw x := by rw [← hw (w⁻¹ • x), smul_inv_smul]

theorem mem_dualWeylStabilizer {z : Fin Tag.E6.rank → K} {w : WeylGroup Tag.E6} :
    w ∈ dualWeylStabilizer z ↔ ∀ x, charVal z (w • x) = charVal z x :=
  Iff.rfl

theorem mem_dualWeylStabilizer_iff_dualMatrix {z : Fin Tag.E6.rank → K}
    {w : WeylGroup Tag.E6} :
    w ∈ dualWeylStabilizer z ↔ (dualMatrix K w⁻¹).mulVec z = z := by
  constructor
  · intro hw
    refine eq_of_charVal_single fun j => ?_
    rw [charVal_dualMatrix]
    have h := hw (w⁻¹ • Pi.single j 1)
    rw [smul_inv_smul] at h
    exact h.symm
  · intro h x
    have h' := charVal_dualMatrix z w⁻¹ (w • x)
    rw [h, inv_smul_smul] at h'
    exact h'

theorem rootReflection_mem_dualWeylStabilizer {z : Fin Tag.E6.rank → K}
    {α : Fin Tag.E6.rank → ℤ} (hα : α ∈ rootKernel z) :
    rootReflection α ∈ dualWeylStabilizer z := by
  intro x
  rw [rootReflection_smul hα.1, charVal_sub, charVal_smul, hα.2, mul_zero, sub_zero]

theorem closure_rootReflection_le {z : Fin Tag.E6.rank → K} :
    Subgroup.closure {s | ∃ α ∈ rootKernel z, s = rootReflection α} ≤ dualWeylStabilizer z := by
  rw [Subgroup.closure_le]
  rintro _ ⟨α, hα, rfl⟩
  exact rootReflection_mem_dualWeylStabilizer hα

end Dual

@[expose] def dualVector (r : Fin Tag.E6.rank → ℤ) : RootSpace Tag.E6 :=
  ofPi (Matrix.mulVec (formMatrix Tag.E6)⁻¹ fun i => (r i : ℝ))

theorem inner_dualVector (x : RootSpace Tag.E6) (r : Fin Tag.E6.rank → ℤ) :
    inner ℝ x (dualVector r) = ∑ i, x i * (r i : ℝ) := by
  have hdet : IsUnit (formMatrix Tag.E6).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (posDef_formMatrix Tag.E6).isUnit
  rw [inner_def, dualVector, toPi_ofPi, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet,
    Matrix.one_mulVec]
  rfl

theorem inner_ofLattice_dualVector (v r : Fin Tag.E6.rank → ℤ) :
    inner ℝ (ofLattice v) (dualVector r) = ((charVal r v : ℤ) : ℝ) := by
  rw [inner_dualVector, charVal]
  push_cast
  rfl

theorem eq_of_inner_ofLattice {y y' : RootSpace Tag.E6}
    (h : ∀ v : Fin Tag.E6.rank → ℤ, inner ℝ (ofLattice v) y = inner ℝ (ofLattice v) y') :
    y = y' := by
  refine ext_inner_left ℝ fun x => ?_
  rw [← sum_smul_ofLattice_single x, sum_inner, sum_inner]
  exact Finset.sum_congr rfl fun i _ => by rw [inner_smul_left, inner_smul_left, h]

theorem weylAct_dualVector_eq {r : Fin Tag.E6.rank → ℤ} {w : WeylGroup Tag.E6}
    (h : ∀ v, charVal r (w⁻¹ • v) = charVal r v) :
    weylAct Tag.E6 w (dualVector r) = dualVector r := by
  refine eq_of_inner_ofLattice fun v => ?_
  have e := inner_weylAct_left w⁻¹ (ofLattice v) (dualVector r)
  rw [inv_inv] at e
  rw [← e, weylAct_ofLattice, inner_ofLattice_dualVector, inner_ofLattice_dualVector, h]

section Average

variable {p : ℕ} [Fact p.Prime]

@[expose] def intLift (z : Fin Tag.E6.rank → ZMod p) : Fin Tag.E6.rank → ℤ :=
  fun i => ((z i).val : ℤ)

theorem intLift_cast (z : Fin Tag.E6.rank → ZMod p) (i : Fin Tag.E6.rank) :
    ((intLift z i : ℤ) : ZMod p) = z i := by
  simp [intLift]

theorem charVal_intLift_cast (z : Fin Tag.E6.rank → ZMod p) (x : Fin Tag.E6.rank → ℤ) :
    ((charVal (intLift z) x : ℤ) : ZMod p) = charVal z x := by
  simp only [charVal, Int.cast_sum, Int.cast_mul, Int.cast_id, intLift_cast]

@[expose] def avgColumn (G : Subgroup (WeylGroup Tag.E6)) [Fintype G]
    (z₀ : Fin Tag.E6.rank → ℤ) : Fin Tag.E6.rank → ℤ :=
  fun i => ∑ a : G, charVal z₀ ((a : WeylGroup Tag.E6) • (Pi.single i 1 : Fin Tag.E6.rank → ℤ))

theorem charVal_int_eq (r x : Fin Tag.E6.rank → ℤ) : charVal r x = ∑ i, x i * r i := by
  simp only [charVal, Int.cast_id]

theorem charVal_smul_eq_sum {R : Type*} [CommRing R] (z : Fin Tag.E6.rank → R)
    (w : WeylGroup Tag.E6) (x : Fin Tag.E6.rank → ℤ) :
    charVal z (w • x) = ∑ j, (x j : R) * charVal z (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) := by
  rw [← weylMatrix_mulVec, charVal_mulVec_eq_sum]
  rfl

theorem charVal_avgColumn (G : Subgroup (WeylGroup Tag.E6)) [Fintype G]
    (z₀ : Fin Tag.E6.rank → ℤ) (x : Fin Tag.E6.rank → ℤ) :
    charVal (avgColumn G z₀) x = ∑ a : G, charVal z₀ ((a : WeylGroup Tag.E6) • x) := by
  rw [charVal_int_eq]
  simp only [avgColumn, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [charVal_smul_eq_sum]
  simp only [Int.cast_id]

theorem charVal_avgColumn_smul {G : Subgroup (WeylGroup Tag.E6)} [Fintype G]
    (z₀ : Fin Tag.E6.rank → ℤ) {w : WeylGroup Tag.E6} (hw : w ∈ G) (x : Fin Tag.E6.rank → ℤ) :
    charVal (avgColumn G z₀) (w • x) = charVal (avgColumn G z₀) x := by
  rw [charVal_avgColumn, charVal_avgColumn]
  refine Fintype.sum_equiv (Equiv.mulRight ⟨w, hw⟩) _ _ fun a => ?_
  rw [Equiv.coe_mulRight, Subgroup.coe_mul, mul_smul]

theorem charVal_avgColumn_cast {G : Subgroup (WeylGroup Tag.E6)} [Fintype G]
    {z : Fin Tag.E6.rank → ZMod p} (hG : G ≤ dualWeylStabilizer z) (x : Fin Tag.E6.rank → ℤ) :
    ((charVal (avgColumn G (intLift z)) x : ℤ) : ZMod p) =
      (Fintype.card G : ZMod p) * charVal z x := by
  rw [charVal_avgColumn, Int.cast_sum]
  simp only [charVal_intLift_cast]
  rw [Finset.sum_congr rfl fun a _ => hG a.2 x, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Average

theorem not_dvd_51840 {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) : ¬p ∣ 51840 := by
  intro h
  rw [show (51840 : ℕ) = 2 ^ 7 * 3 ^ 4 * 5 by norm_num] at h
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)
      omega
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)
      omega
  · have := Nat.le_of_dvd (by norm_num) h
    omega

theorem card_weylGroup_E6 : Nat.card (WeylGroup Tag.E6) = 51840 := by
  have : Fintype (WeylGroup Tag.E6) := Fintype.ofFinite _
  exact (CFSG.RankThree.Chevalley.E6_weyl_length_polynomial).2

theorem card_subgroup_ne_zero {p : ℕ} [Fact p.Prime] (hp5 : 5 < p)
    (G : Subgroup (WeylGroup Tag.E6)) [Fintype G] : (Fintype.card G : ZMod p) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have hG : Fintype.card G ∣ 51840 := by
    rw [← card_weylGroup_E6, ← Nat.card_eq_fintype_card]
    exact Subgroup.card_subgroup_dvd_card G
  exact not_dvd_51840 (Fact.out) hp5 (h.trans hG)

section Stabilizer

variable {p : ℕ} [Fact p.Prime]

theorem charVal_avgColumn_eq_zero_iff {G : Subgroup (WeylGroup Tag.E6)} [Fintype G]
    {z : Fin Tag.E6.rank → ZMod p} (hG : G ≤ dualWeylStabilizer z)
    (hrefl : ∀ α ∈ rootKernel z, rootReflection α ∈ G) (hcard : (Fintype.card G : ZMod p) ≠ 0)
    {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) :
    charVal (avgColumn G (intLift z)) α = 0 ↔ α ∈ rootKernel z := by
  constructor
  · intro h
    have h' := charVal_avgColumn_cast hG α
    rw [h, Int.cast_zero, eq_comm] at h'
    exact ⟨hα, (mul_eq_zero.1 h').resolve_left hcard⟩
  · intro hk
    have h := charVal_avgColumn_smul (intLift z) (hrefl α hk) α
    rw [rootReflection_smul_self hα, charVal_neg] at h
    omega

theorem dualWeylStabilizer_eq_closure (hp5 : 5 < p) (z : Fin Tag.E6.rank → ZMod p) :
    dualWeylStabilizer z = Subgroup.closure {s | ∃ α ∈ rootKernel z, s = rootReflection α} := by
  classical
  set U := dualWeylStabilizer z
  have : Fintype U := Fintype.ofFinite _
  set r := avgColumn U (intLift z)
  have hker : ∀ α, IsRoot Tag.E6 α → (charVal r α = 0 ↔ α ∈ rootKernel z) := fun α hα =>
    charVal_avgColumn_eq_zero_iff le_rfl (fun _ h => rootReflection_mem_dualWeylStabilizer h)
      (card_subgroup_ne_zero hp5 U) hα
  refine le_antisymm (fun w hw => ?_) closure_rootReflection_le
  have hfix : w ∈ weylStabilizer Tag.E6 (dualVector r) :=
    weylAct_dualVector_eq fun v => charVal_avgColumn_smul _ (U.inv_mem hw) v
  rw [(exceptional_Lang_Weyl_chamber_point_stabilizers Tag.E6).2.2.2.2.2 (dualVector r)] at hfix
  convert hfix using 2
  ext s
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨α, hα, rfl⟩
    exact ⟨α, hα.1, by rw [inner_ofLattice_dualVector, (hker α hα.1).2 hα, Int.cast_zero], rfl⟩
  · rintro ⟨α, hα, h0, rfl⟩
    rw [inner_ofLattice_dualVector, Int.cast_eq_zero] at h0
    exact ⟨α, (hker α hα).1 h0, rfl⟩

end Stabilizer

section Graph

theorem e6Rho_symm : e6Rho.symm = e6Rho := by
  refine Equiv.ext fun i => ?_
  revert i
  decide

theorem permLattice_e6Rho_e6Rho (x : Fin Tag.E6.rank → ℤ) :
    permLattice e6Rho (permLattice e6Rho x) = x := by
  have h := permLattice_symm_permLattice e6Rho x
  rwa [e6Rho_symm] at h

@[expose] def e6WeylTwist : WeylGroup Tag.E6 ≃* WeylGroup Tag.E6 := weylTwist TwistTag.E6

theorem e6WeylTwist_smul (w : WeylGroup Tag.E6) (x : Fin Tag.E6.rank → ℤ) :
    e6WeylTwist w • x = permLattice e6Rho (w • permLattice e6Rho x) := by
  have h := weylTwist_smul TwistTag.E6 w x
  have hs : TwistTag.E6.perm.symm = e6Rho := e6Rho_symm
  rw [hs] at h
  exact h

theorem rhoMatrix_mul_weylMatrix_mulVec (w : WeylGroup Tag.E6) (x : Fin Tag.E6.rank → ℤ) :
    (rhoMatrix * weylMatrix w⁻¹).mulVec x = permLattice e6Rho (w⁻¹ • x) := by
  rw [← Matrix.mulVec_mulVec, weylMatrix_mulVec, permLattice_eq_mulVec]

variable {K : Type*} [CommRing K]

theorem graph_dual_fixed_iff {z : Fin Tag.E6.rank → K} {w : WeylGroup Tag.E6} :
    (((rhoMatrix * weylMatrix w⁻¹).map (Int.cast : ℤ → K)).transpose).mulVec z = z ↔
      ∀ x, charVal z (w • permLattice e6Rho x) = charVal z x := by
  constructor
  · intro h x
    have h' := charVal_mulVec z (rhoMatrix * weylMatrix w⁻¹) (w • permLattice e6Rho x)
    rw [h, rhoMatrix_mul_weylMatrix_mulVec, inv_smul_smul, permLattice_e6Rho_e6Rho] at h'
    exact h'
  · intro h
    refine eq_of_charVal_single fun j => ?_
    rw [charVal_mulVec, rhoMatrix_mul_weylMatrix_mulVec, ← h, permLattice_e6Rho_e6Rho,
      smul_inv_smul]

theorem graph_conj_smul (w c : WeylGroup Tag.E6) (x : Fin Tag.E6.rank → ℤ) :
    permLattice e6Rho (w⁻¹ • (c • (w • permLattice e6Rho x))) =
      e6WeylTwist (w⁻¹ * c * w) • x := by
  rw [e6WeylTwist_smul, mul_smul, mul_smul]

theorem graph_sq_smul (w : WeylGroup Tag.E6) (x : Fin Tag.E6.rank → ℤ) :
    w • permLattice e6Rho (w • permLattice e6Rho x) = (w * e6WeylTwist w) • x := by
  rw [mul_smul, e6WeylTwist_smul]

end Graph

section TwoSided

variable {p : ℕ} [Fact p.Prime]

@[expose] def graphAvgColumn (r : Fin Tag.E6.rank → ℤ) (w : WeylGroup Tag.E6) :
    Fin Tag.E6.rank → ℤ :=
  fun i => r i + charVal r (permLattice e6Rho (w⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)))

theorem charVal_graphAvgColumn (r : Fin Tag.E6.rank → ℤ) (w : WeylGroup Tag.E6)
    (x : Fin Tag.E6.rank → ℤ) :
    charVal (graphAvgColumn r w) x = charVal r x + charVal r (permLattice e6Rho (w⁻¹ • x)) := by
  have h := charVal_mulVec_eq_sum r (rhoMatrix * weylMatrix w⁻¹) x
  rw [rhoMatrix_mul_weylMatrix_mulVec] at h
  rw [h, charVal_int_eq, charVal_int_eq]
  simp only [graphAvgColumn, mul_add, Finset.sum_add_distrib, Int.cast_id]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [← rhoMatrix_mul_weylMatrix_mulVec, Matrix.mulVec_single_one]
  rfl

variable {z : Fin Tag.E6.rank → ZMod p} {w : WeylGroup Tag.E6}

omit [Fact p.Prime] in
theorem charVal_graph_inv (hb : ∀ x, charVal z (w • permLattice e6Rho x) = charVal z x)
    (x : Fin Tag.E6.rank → ℤ) : charVal z (permLattice e6Rho (w⁻¹ • x)) = charVal z x := by
  have h := hb (permLattice e6Rho (w⁻¹ • x))
  rw [permLattice_e6Rho_e6Rho, smul_inv_smul] at h
  exact h.symm

omit [Fact p.Prime] in
theorem graphConj_mem (hb : ∀ x, charVal z (w • permLattice e6Rho x) = charVal z x)
    {c : WeylGroup Tag.E6} (hc : c ∈ dualWeylStabilizer z) :
    e6WeylTwist (w⁻¹ * c * w) ∈ dualWeylStabilizer z := by
  intro x
  rw [← graph_conj_smul, charVal_graph_inv hb, hc, hb]

omit [Fact p.Prime] in
theorem graphSq_mem (hb : ∀ x, charVal z (w • permLattice e6Rho x) = charVal z x) :
    w * e6WeylTwist w ∈ dualWeylStabilizer z := by
  intro x
  rw [← graph_sq_smul, hb, hb]

variable [Fintype (dualWeylStabilizer z)]

omit [Fact p.Prime] in
theorem charVal_graphAvgColumn_smul
    (hb : ∀ x, charVal z (w • permLattice e6Rho x) = charVal z x)
    {c : WeylGroup Tag.E6} (hc : c ∈ dualWeylStabilizer z) (x : Fin Tag.E6.rank → ℤ) :
    charVal (graphAvgColumn (avgColumn (dualWeylStabilizer z) (intLift z)) w) (c • x) =
      charVal (graphAvgColumn (avgColumn (dualWeylStabilizer z) (intLift z)) w) x := by
  rw [charVal_graphAvgColumn, charVal_graphAvgColumn, charVal_avgColumn_smul _ hc]
  congr 1
  have e : permLattice e6Rho (w⁻¹ • (c • x)) =
      e6WeylTwist (w⁻¹ * c * w) • permLattice e6Rho (w⁻¹ • x) := by
    rw [← graph_conj_smul, permLattice_e6Rho_e6Rho, smul_inv_smul]
  rw [e, charVal_avgColumn_smul _ (graphConj_mem hb hc)]

omit [Fact p.Prime] in
theorem charVal_graphAvgColumn_graph
    (hb : ∀ x, charVal z (w • permLattice e6Rho x) = charVal z x) (x : Fin Tag.E6.rank → ℤ) :
    charVal (graphAvgColumn (avgColumn (dualWeylStabilizer z) (intLift z)) w)
        (w • permLattice e6Rho x) =
      charVal (graphAvgColumn (avgColumn (dualWeylStabilizer z) (intLift z)) w) x := by
  rw [charVal_graphAvgColumn, charVal_graphAvgColumn, inv_smul_smul, permLattice_e6Rho_e6Rho,
    add_comm]
  congr 1
  have e : w • permLattice e6Rho x =
      (w * e6WeylTwist w) • permLattice e6Rho (w⁻¹ • x) := by
    rw [← graph_sq_smul, permLattice_e6Rho_e6Rho, smul_inv_smul]
  rw [e, charVal_avgColumn_smul _ (graphSq_mem hb)]

theorem charVal_graphAvgColumn_cast
    (hb : ∀ x, charVal z (w • permLattice e6Rho x) = charVal z x) (x : Fin Tag.E6.rank → ℤ) :
    ((charVal (graphAvgColumn (avgColumn (dualWeylStabilizer z) (intLift z)) w) x : ℤ) :
        ZMod p) =
      2 * (Fintype.card (dualWeylStabilizer z) : ZMod p) * charVal z x := by
  rw [charVal_graphAvgColumn, Int.cast_add, charVal_avgColumn_cast le_rfl,
    charVal_avgColumn_cast le_rfl, charVal_graph_inv hb]
  ring

theorem charVal_graphAvgColumn_eq_zero_iff (hp5 : 5 < p)
    (hb : ∀ x, charVal z (w • permLattice e6Rho x) = charVal z x)
    {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) :
    charVal (graphAvgColumn (avgColumn (dualWeylStabilizer z) (intLift z)) w) α = 0 ↔
      α ∈ rootKernel z := by
  constructor
  · intro h
    have h' := charVal_graphAvgColumn_cast hb α
    rw [h, Int.cast_zero, eq_comm] at h'
    have h2 : (2 : ZMod p) ≠ 0 := by
      intro h2
      have h2' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h2
      rw [ZMod.natCast_eq_zero_iff] at h2'
      have := Nat.le_of_dvd (by norm_num) h2'
      omega
    refine ⟨hα, (mul_eq_zero.1 h').resolve_left (mul_ne_zero h2 (card_subgroup_ne_zero hp5 _))⟩
  · intro hk
    have h := charVal_graphAvgColumn_smul hb (rootReflection_mem_dualWeylStabilizer hk) α
    rw [rootReflection_smul_self hα, charVal_neg] at h
    omega

end TwoSided

section Real

@[expose] def e6TwistIsometry : RootSpace Tag.E6 ≃ₗᵢ[ℝ] RootSpace Tag.E6 :=
  twistIsometry TwistTag.E6

theorem e6TwistIsometry_ofLattice (v : Fin Tag.E6.rank → ℤ) :
    e6TwistIsometry (ofLattice v) = ofLattice (permLattice e6Rho v) :=
  twistIsometry_ofLattice TwistTag.E6 v

theorem e6TwistIsometry_weylAct (g : WeylGroup Tag.E6) (x : RootSpace Tag.E6) :
    e6TwistIsometry (weylAct Tag.E6 g x) = weylAct Tag.E6 (e6WeylTwist g) (e6TwistIsometry x) :=
  twistIsometry_weylAct TwistTag.E6 g x

theorem weylAct_twist_dualVector_eq {r : Fin Tag.E6.rank → ℤ} {w : WeylGroup Tag.E6}
    (h : ∀ x, charVal r (w • permLattice e6Rho x) = charVal r x) :
    weylAct Tag.E6 w (e6TwistIsometry (dualVector r)) = dualVector r := by
  refine eq_of_inner_ofLattice fun v => ?_
  have e := inner_weylAct_left w⁻¹ (ofLattice v) (e6TwistIsometry (dualVector r))
  rw [inv_inv] at e
  rw [← e, weylAct_ofLattice]
  have e2 : ofLattice (w⁻¹ • v) = e6TwistIsometry (ofLattice (permLattice e6Rho (w⁻¹ • v))) := by
    rw [e6TwistIsometry_ofLattice, permLattice_e6Rho_e6Rho]
  rw [e2, LinearIsometryEquiv.inner_map_map, inner_ofLattice_dualVector,
    inner_ofLattice_dualVector]
  have h' := h (permLattice e6Rho (w⁻¹ • v))
  rw [permLattice_e6Rho_e6Rho, smul_inv_smul] at h'
  rw [h']

end Real

section Chamber

theorem weylAct_eq_of_mem_dominantCone {y : RootSpace Tag.E6} (hy : y ∈ dominantCone Tag.E6) :
    ∀ {g : WeylGroup Tag.E6}, weylAct Tag.E6 g y ∈ dominantCone Tag.E6 →
      weylAct Tag.E6 g y = y := by
  intro g hgy
  induction h : (coxeterSystem Tag.E6).length g using Nat.strong_induction_on generalizing g with
  | _ n ih =>
    by_cases hg1 : g = 1
    · rw [hg1, map_one, LinearIsometryEquiv.coe_one, id]
    obtain ⟨i, hi⟩ := exists_height_neg_of_ne_one (inv_ne_one.2 hg1)
    have hroot := IsRoot.smul (isRoot_single Tag.E6 i) g⁻¹
    have hdesc : (coxeterSystem Tag.E6).IsRightDescent g⁻¹ i :=
      (smul_single_mem_negRoots_iff g⁻¹ i).1 ⟨hroot, hi⟩
    have hlen := (isRightDescent_iff_length g⁻¹ i).1 hdesc
    have e1 : (coxeterSystem Tag.E6).length (g⁻¹ * simple Tag.E6 i) =
        (coxeterSystem Tag.E6).length (simple Tag.E6 i * g) := by
      rw [← (coxeterSystem Tag.E6).length_inv, mul_inv_rev, inv_inv,
        (coxeterSystem Tag.E6).inv_simple]
    rw [e1, (coxeterSystem Tag.E6).length_inv, h] at hlen
    have hzero : inner ℝ (ofLattice (Pi.single i 1)) (weylAct Tag.E6 g y) = 0 := by
      have e : inner ℝ (ofLattice (Pi.single i 1)) (weylAct Tag.E6 g y) =
          inner ℝ (ofLattice (g⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ))) y := by
        rw [← weylAct_ofLattice, inner_weylAct_left, inv_inv]
      have h1 := IsRoot.inner_nonpos_of_mem_dominantCone hroot hi hy
      have h2 := hgy i
      linarith
    have hfix : weylAct Tag.E6 (simple Tag.E6 i * g) y = weylAct Tag.E6 g y := by
      rw [weylAct_mul_apply, weylAct_simple_eq, hzero, mul_zero, zero_div, zero_smul, sub_zero]
    have := ih _ (by omega) (hfix ▸ hgy) rfl
    rw [← hfix, this]

theorem inner_root_eq_zero_iff {y : RootSpace Tag.E6} (hy : y ∈ dominantCone Tag.E6)
    {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) :
    inner ℝ (ofLattice α) y = 0 ↔
      ∀ i, inner ℝ (ofLattice (Pi.single i 1)) y ≠ 0 → α i = 0 := by
  rw [inner_ofLattice_eq_sum]
  have key : ∀ (c : Fin Tag.E6.rank → ℤ), (∀ i, 0 ≤ c i) →
      ((∑ i, (c i : ℝ) * inner ℝ (ofLattice (Pi.single i 1)) y) = 0 ↔
        ∀ i, inner ℝ (ofLattice (Pi.single i 1)) y ≠ 0 → c i = 0) := by
    intro c hc
    rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (by exact_mod_cast hc i) (hy i)]
    refine ⟨fun h i hi => ?_, fun h i _ => ?_⟩
    · exact_mod_cast (mul_eq_zero.1 (h i (Finset.mem_univ i))).resolve_right hi
    · by_cases hi : inner ℝ (ofLattice (Pi.single i 1)) y = 0
      · rw [hi, mul_zero]
      · rw [h i hi, Int.cast_zero, zero_mul]
  rcases hα.nonneg_or_nonpos with hs | hs
  · exact key α hs
  · have h := key (-α) fun i => by simp only [Pi.neg_apply]; linarith [hs i]
    simp only [Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib, neg_eq_zero,
      neg_eq_zero] at h
    exact h

theorem inner_single_e6TwistIsometry (i : Fin Tag.E6.rank) (y : RootSpace Tag.E6) :
    inner ℝ (ofLattice (Pi.single i 1)) (e6TwistIsometry y) =
      inner ℝ (ofLattice (Pi.single (e6Rho i) 1)) y := by
  have e : ofLattice (Pi.single i 1 : Fin Tag.E6.rank → ℤ) =
      e6TwistIsometry (ofLattice (Pi.single (e6Rho i) 1)) := by
    rw [e6TwistIsometry_ofLattice, permLattice_single]
    congr 2
    exact (Equiv.ext_iff.1 (show e6Rho * e6Rho = 1 by decide) i).symm
  rw [e, LinearIsometryEquiv.inner_map_map]

end Chamber

section Walls

@[expose] def support345 : Set (Fin Tag.E6.rank) := {e6Index 2, e6Index 3, e6Index 4}

theorem mem_support345 (i : Fin Tag.E6.rank) :
    i ∈ support345 ↔ (i = e6Index 2 ∨ i = e6Index 3 ∨ i = e6Index 4) := by
  simp only [support345, Set.mem_insert_iff, Set.mem_singleton_iff]

theorem ncard_parabolicRoots_support134 : (parabolicRoots Tag.E6 support134).ncard = 12 :=
  ncard_parabolicRoots_eq mem_support134 (by decide +kernel)

@[expose] def e6Form (x y : Fin Tag.E6.rank → ℤ) : ℤ :=
  ∑ i, x i * ∑ j, Tag.E6.cartan i j * y j

theorem symmetrizedCartan_E6 : Tag.E6.symmetrizedCartan = Tag.E6.cartan := by
  rw [Tag.symmetrizedCartan, Tag.symmetrizer, one_mul]

theorem iform_eq_e6Form (x y : Fin Tag.E6.rank → ℤ) : iform x y = e6Form x y := by
  simp only [iform, e6Form, symmetrizedCartan_E6, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem exists_chainRoot_of_support134 : ∀ m : Fin 72,
    (∀ i, ¬(i = e6Index 0 ∨ i = e6Index 2 ∨ i = e6Index 3) → e6RootVec m i = 0) →
      ∃ k l : Fin 4, k ≠ l ∧ chainRoot chain134 k l = e6RootVec m := by
  decide +kernel

theorem chainRoot134_mem : ∀ k l : Fin 4, k ≠ l → ∃ m : Fin 72,
    e6RootVec m = chainRoot chain134 k l ∧
      ∀ i, ¬(i = e6Index 0 ∨ i = e6Index 2 ∨ i = e6Index 3) → e6RootVec m i = 0 := by
  decide +kernel

theorem orth_unique_chain134 : ∀ i j k l m n : Fin 4, i ≠ j → k ≠ l → m ≠ n →
    e6Form (chainRoot chain134 i j) (chainRoot chain134 k l) = 0 →
    e6Form (chainRoot chain134 i j) (chainRoot chain134 m n) = 0 →
      chainRoot chain134 k l = chainRoot chain134 m n ∨
        chainRoot chain134 k l = -chainRoot chain134 m n := by
  decide +kernel

theorem mem_parabolicRoots_iff {J : Set (Fin Tag.E6.rank)} {α : Fin Tag.E6.rank → ℤ} :
    α ∈ parabolicRoots Tag.E6 J ↔ IsRoot Tag.E6 α ∧ ∀ i ∉ J, α i = 0 :=
  Iff.rfl

theorem exists_chainRoot_of_mem {α : Fin Tag.E6.rank → ℤ}
    (hα : α ∈ parabolicRoots Tag.E6 support134) :
    ∃ k l : Fin 4, k ≠ l ∧ chainRoot chain134 k l = α := by
  obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hα.1
  exact exists_chainRoot_of_support134 m fun i hi => hα.2 i ((mem_support134 i).not.2 hi)

theorem chainRoot134_mem_parabolicRoots {k l : Fin 4} (hkl : k ≠ l) :
    chainRoot chain134 k l ∈ parabolicRoots Tag.E6 support134 := by
  obtain ⟨m, hm, hs⟩ := chainRoot134_mem k l hkl
  rw [← hm]
  exact ⟨isRoot_e6RootVec m, fun i hi => hs i ((mem_support134 i).not.1 hi)⟩

theorem orth_unique_parabolicRoots_support134 {α β γ : Fin Tag.E6.rank → ℤ}
    (hα : α ∈ parabolicRoots Tag.E6 support134) (hβ : β ∈ parabolicRoots Tag.E6 support134)
    (hγ : γ ∈ parabolicRoots Tag.E6 support134) (h1 : e6Form α β = 0) (h2 : e6Form α γ = 0) :
    β = γ ∨ β = -γ := by
  obtain ⟨i, j, hij, rfl⟩ := exists_chainRoot_of_mem hα
  obtain ⟨k, l, hkl, rfl⟩ := exists_chainRoot_of_mem hβ
  obtain ⟨m, n, hmn, rfl⟩ := exists_chainRoot_of_mem hγ
  exact orth_unique_chain134 i j k l m n hij hkl hmn h1 h2

theorem parabolicRoots_mono {J S : Set (Fin Tag.E6.rank)} (h : J ⊆ S) :
    parabolicRoots Tag.E6 J ⊆ parabolicRoots Tag.E6 S :=
  fun _ hα => ⟨hα.1, fun i hi => hα.2 i fun hJ => hi (h hJ)⟩

theorem ncard_parabolicRoots_le {J S : Set (Fin Tag.E6.rank)} (h : J ⊆ S) :
    (parabolicRoots Tag.E6 J).ncard ≤ (parabolicRoots Tag.E6 S).ncard :=
  Set.ncard_le_ncard (parabolicRoots_mono h)
    ((finite_setOf_isRoot Tag.E6).subset fun _ hα => hα.1)

theorem single_mem_parabolicRoots_E6 {J : Set (Fin Tag.E6.rank)} {i : Fin Tag.E6.rank}
    (hi : i ∈ J) : (Pi.single i 1 : Fin Tag.E6.rank → ℤ) ∈ parabolicRoots Tag.E6 J :=
  ⟨isRoot_single Tag.E6 i, fun j hj => Pi.single_eq_of_ne (fun e => hj (by rw [e]; exact hi)) 1⟩

theorem ncard_parabolicRoots_pair {a b : Fin Tag.E6.rank} {n : ℕ}
    (h : (Finset.univ.filter fun m : Fin 72 =>
      ∀ i, ¬(i = a ∨ i = b) → e6RootVec m i = 0).card = n) :
    (parabolicRoots Tag.E6 {a, b}).ncard = n :=
  ncard_parabolicRoots_eq (fun i => by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]) h

theorem ncard_parabolicRoots_single {a : Fin Tag.E6.rank} {n : ℕ}
    (h : (Finset.univ.filter fun m : Fin 72 => ∀ i, ¬i = a → e6RootVec m i = 0).card = n) :
    (parabolicRoots Tag.E6 {a}).ncard = n :=
  ncard_parabolicRoots_eq (fun i => by simp only [Set.mem_singleton_iff]) h

theorem eq_support345 {J : Set (Fin Tag.E6.rank)} (hJρ : ∀ i, i ∈ J ↔ e6Rho i ∈ J)
    {g : WeylGroup Tag.E6}
    (hg : (g • ·) '' parabolicRoots Tag.E6 support134 = parabolicRoots Tag.E6 J) :
    J = support345 := by
  have hcard : (parabolicRoots Tag.E6 J).ncard = 12 := by
    rw [← hg, Set.ncard_image_of_injective _ (MulAction.injective g),
      ncard_parabolicRoots_support134]
  have horth : ∀ α ∈ parabolicRoots Tag.E6 J, ∀ β ∈ parabolicRoots Tag.E6 J,
      ∀ γ ∈ parabolicRoots Tag.E6 J, e6Form α β = 0 → e6Form α γ = 0 → β = γ ∨ β = -γ := by
    rw [← hg]
    rintro _ ⟨α, hα, rfl⟩ _ ⟨β, hβ, rfl⟩ _ ⟨γ, hγ, rfl⟩ h1 h2
    rw [← iform_eq_e6Form, iform_smul, iform_eq_e6Form] at h1 h2
    rcases orth_unique_parabolicRoots_support134 hα hβ hγ h1 h2 with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h]; exact smul_neg g γ)
  have hs := fun {i : Fin Tag.E6.rank} (hi : i ∈ J) => single_mem_parabolicRoots_E6 hi
  have r0 : e6Rho (e6Index 0) = e6Index 5 := by decide
  have r2 : e6Rho (e6Index 2) = e6Index 4 := by decide
  have h0 : e6Index 0 ∉ J := by
    intro h0
    have h5 : e6Index 5 ∈ J := r0 ▸ (hJρ _).1 h0
    have h1 : e6Index 1 ∉ J := fun h1 => by
      rcases horth _ (hs h0) _ (hs h5) _ (hs h1) (by decide +kernel)
          (by decide +kernel) with h | h <;>
        exact absurd h (by decide +kernel)
    have h3 : e6Index 3 ∉ J := fun h3 => by
      rcases horth _ (hs h0) _ (hs h5) _ (hs h3) (by decide +kernel)
          (by decide +kernel) with h | h <;>
        exact absurd h (by decide +kernel)
    have h4 : e6Index 4 ∉ J := fun h4 => by
      rcases horth _ (hs h0) _ (hs h5) _ (hs h4) (by decide +kernel)
          (by decide +kernel) with h | h <;>
        exact absurd h (by decide +kernel)
    have h2 : e6Index 2 ∉ J := fun h2 => h4 (r2 ▸ (hJρ _).1 h2)
    have hsub : J ⊆ {e6Index 0, e6Index 5} := by
      intro i hi
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      revert hi
      change ∀ hi : (e6Index (i : Fin 6)) ∈ J, _
      fin_cases i <;> intro hi
      all_goals first
        | exact Or.inl rfl | exact Or.inr rfl | exact absurd hi h1 | exact absurd hi h2
        | exact absurd hi h3 | exact absurd hi h4
    have := ncard_parabolicRoots_le hsub
    rw [hcard, ncard_parabolicRoots_pair (n := 4) (by decide +kernel)] at this
    omega
  have h5 : e6Index 5 ∉ J := fun h5 => h0 ((hJρ _).2 (by rw [r0]; exact h5) |> fun h => by
    have hρ5 : e6Rho (e6Index 5) = e6Index 0 := by decide
    exact hρ5 ▸ (hJρ _).1 h5)
  have h24 : e6Index 2 ∈ J ↔ e6Index 4 ∈ J := by rw [hJρ, r2]
  have h1 : e6Index 1 ∉ J := by
    intro h1
    by_cases h2 : e6Index 2 ∈ J
    · have h4 := h24.1 h2
      rcases horth _ (hs h1) _ (hs h2) _ (hs h4) (by decide +kernel)
          (by decide +kernel) with h | h <;>
        exact absurd h (by decide +kernel)
    · have h4 : e6Index 4 ∉ J := fun h4 => h2 (h24.2 h4)
      have hsub : J ⊆ {e6Index 1, e6Index 3} := by
        intro i hi
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        revert hi
        change ∀ hi : (e6Index (i : Fin 6)) ∈ J, _
        fin_cases i <;> intro hi
        all_goals first
          | exact Or.inl rfl | exact Or.inr rfl | exact absurd hi h0 | exact absurd hi h2
          | exact absurd hi h4 | exact absurd hi h5
      have := ncard_parabolicRoots_le hsub
      rw [hcard, ncard_parabolicRoots_pair (n := 6) (by decide +kernel)] at this
      omega
  have h2 : e6Index 2 ∈ J := by
    by_contra h2
    have h4 : e6Index 4 ∉ J := fun h4 => h2 (h24.2 h4)
    have hsub : J ⊆ {e6Index 3} := by
      intro i hi
      simp only [Set.mem_singleton_iff]
      revert hi
      change ∀ hi : (e6Index (i : Fin 6)) ∈ J, _
      fin_cases i <;> intro hi
      all_goals first
        | rfl | exact absurd hi h0 | exact absurd hi h1 | exact absurd hi h2
        | exact absurd hi h4 | exact absurd hi h5
    have := ncard_parabolicRoots_le hsub
    rw [hcard, ncard_parabolicRoots_single (n := 2) (by decide +kernel)] at this
    omega
  have h4 := h24.1 h2
  have h3 : e6Index 3 ∈ J := by
    by_contra h3
    have hsub : J ⊆ {e6Index 2, e6Index 4} := by
      intro i hi
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      revert hi
      change ∀ hi : (e6Index (i : Fin 6)) ∈ J, _
      fin_cases i <;> intro hi
      all_goals first
        | exact Or.inl rfl | exact Or.inr rfl | exact absurd hi h0 | exact absurd hi h1
        | exact absurd hi h3 | exact absurd hi h5
    have := ncard_parabolicRoots_le hsub
    rw [hcard, ncard_parabolicRoots_pair (n := 4) (by decide +kernel)] at this
    omega
  have key : ∀ i : Fin 6, (e6Index i ∈ J ↔
      (e6Index i = e6Index 2 ∨ e6Index i = e6Index 3 ∨ e6Index i = e6Index 4)) := by
    intro i
    fin_cases i
    · exact iff_of_false h0 (by decide)
    · exact iff_of_false h1 (by decide)
    · exact iff_of_true h2 (by decide)
    · exact iff_of_true h3 (by decide)
    · exact iff_of_true h4 (by decide)
    · exact iff_of_false h5 (by decide)
  ext i
  rw [mem_support345]
  exact key i

end Walls

section Orientation

theorem chainRoot134_reflect : ∀ k l i j : Fin 4, k ≠ l →
    chainRoot chain134 i j -
        (2 * e6Form (chainRoot chain134 k l) (chainRoot chain134 i j) /
          e6Form (chainRoot chain134 k l) (chainRoot chain134 k l)) • chainRoot chain134 k l =
      chainRoot chain134 (Equiv.swap k l i) (Equiv.swap k l j) := by
  decide +kernel

theorem rootReflection_positive_134 {β : Fin Tag.E6.rank → ℤ}
    (hβ : β ∈ parabolicRoots Tag.E6 support134) :
    IsPositiveTransition (rootReflection β • ·) chain134 chain134 := by
  obtain ⟨k, l, hkl, rfl⟩ := exists_chainRoot_of_mem hβ
  refine ⟨Equiv.swap k l, fun i j => ?_⟩
  dsimp only
  rw [rootReflection_smul hβ.1, corootPair, iform_eq_e6Form, iform_eq_e6Form]
  exact chainRoot134_reflect k l i j hkl

theorem positive_of_mem_closure_134 {g : WeylGroup Tag.E6}
    (hg : g ∈ Subgroup.closure
      {s | ∃ β ∈ parabolicRoots Tag.E6 support134, s = rootReflection β}) :
    IsPositiveTransition (g • ·) chain134 chain134 := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨β, hβ, rfl⟩ := hx
    exact rootReflection_positive_134 hβ
  | one => exact ⟨1, fun i j => by dsimp only; rw [one_smul]; rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨πx, hπx⟩ := hx
    obtain ⟨πy, hπy⟩ := hy
    refine ⟨πx * πy, fun i j => ?_⟩
    have h1 := hπy i j
    have h2 := hπx (πy i) (πy j)
    dsimp only at h1 h2 ⊢
    rw [mul_smul, h1, h2]
    rfl
  | inv x _ hx =>
    obtain ⟨π, hπ⟩ := hx
    refine ⟨π⁻¹, fun i j => ?_⟩
    have h := hπ (π⁻¹ i) (π⁻¹ j)
    have hi : π (π⁻¹ i) = i := Equiv.Perm.inv_eq_iff_eq.1 rfl |>.symm
    have hj : π (π⁻¹ j) = j := Equiv.Perm.inv_eq_iff_eq.1 rfl |>.symm
    dsimp only at h ⊢
    rw [hi, hj] at h
    rw [← h, inv_smul_smul]

@[expose] def wJ345Word : List (Fin 6) := [2, 3, 2, 4, 3, 2]

@[expose] def wJ345 : WeylGroup Tag.E6 := (coxeterSystem Tag.E6).wordProd (e6Word wJ345Word)

theorem rho_e6RootVec_support345 : ∀ m : Fin 72,
    (∀ i, ¬(i = e6Index 2 ∨ i = e6Index 3 ∨ i = e6Index 4) → e6RootVec m i = 0) →
      permLattice e6Rho (e6RootVec m) =
        -((e6Word wJ345Word).foldr (reflect Tag.E6) (e6RootVec m)) := by
  decide +kernel

theorem rho_eq_neg_wJ345 {β : Fin Tag.E6.rank → ℤ} (hβ : β ∈ parabolicRoots Tag.E6 support345) :
    permLattice e6Rho β = -(wJ345 • β) := by
  obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hβ.1
  rw [wJ345, wordProd_e6Word_smul]
  exact rho_e6RootVec_support345 m fun i hi => hβ.2 i ((mem_support345 i).not.2 hi)

theorem wJ345_mem_closure {S : Set (WeylGroup Tag.E6)}
    (hS : ∀ i ∈ support345, simple Tag.E6 i ∈ S) : wJ345 ∈ Subgroup.closure S := by
  have h : ∀ ω : List (Fin 6),
      (∀ i ∈ ω, e6Index i = e6Index 2 ∨ e6Index i = e6Index 3 ∨ e6Index i = e6Index 4) →
      (coxeterSystem Tag.E6).wordProd (e6Word ω) ∈ Subgroup.closure S := by
    intro ω
    induction ω with
    | nil => intro _; exact one_mem _
    | cons i ω ih =>
      intro hω
      change (coxeterSystem Tag.E6).wordProd (e6Index i :: e6Word ω) ∈ _
      rw [CoxeterSystem.wordProd_cons]
      exact mul_mem (Subgroup.subset_closure
          (hS _ ((mem_support345 _).2 (hω i List.mem_cons_self))))
        (ih fun j hj => hω j (List.mem_cons_of_mem i hj))
  exact h wJ345Word (by decide)

end Orientation

section GraphStabilizer

variable {p : ℕ} [Fact p.Prime]

theorem graph_stabilizer_A3 (hp5 : 5 < p) {z : Fin Tag.E6.rank → ZMod p}
    {v : WeylGroup Tag.E6}
    (hv : (v • ·) '' rootKernel z = parabolicRoots Tag.E6 support134) {w : WeylGroup Tag.E6}
    (hb : ∀ x, charVal z (w • permLattice e6Rho x) = charVal z x) :
    ∃ t ∈ Subgroup.closure {s | ∃ α ∈ rootKernel z, s = rootReflection α},
      ∀ α ∈ rootKernel z, w • permLattice e6Rho α = -(t • α) := by
  classical
  have : Fintype (dualWeylStabilizer z) := Fintype.ofFinite _
  set r' := graphAvgColumn (avgColumn (dualWeylStabilizer z) (intLift z)) w
  have hkey : ∀ α, IsRoot Tag.E6 α → (charVal r' α = 0 ↔ α ∈ rootKernel z) := fun α hα =>
    charVal_graphAvgColumn_eq_zero_iff hp5 hb hα
  have hbfix : weylAct Tag.E6 w (e6TwistIsometry (dualVector r')) = dualVector r' :=
    weylAct_twist_dualVector_eq (charVal_graphAvgColumn_graph hb)
  obtain ⟨w₁, Y, hY, hy'⟩ := exists_weylAct_mem_dominantCone (dualVector r')
  set u := w₁⁻¹ with hu
  have huy : weylAct Tag.E6 u (dualVector r') = Y := by
    rw [hy', ← weylAct_mul_apply, hu, inv_mul_cancel, map_one, LinearIsometryEquiv.coe_one, id]
  set J : Set (Fin Tag.E6.rank) := {i | inner ℝ (ofLattice (Pi.single i 1)) Y = 0} with hJdef
  have hinner : ∀ α : Fin Tag.E6.rank → ℤ,
      inner ℝ (ofLattice (u • α)) Y = ((charVal r' α : ℤ) : ℝ) := fun α => by
    rw [← huy, ← weylAct_ofLattice, LinearIsometryEquiv.inner_map_map,
      inner_ofLattice_dualVector]
  have hΦ : (u • ·) '' rootKernel z = parabolicRoots Tag.E6 J := by
    ext β
    constructor
    · rintro ⟨α, hα, rfl⟩
      refine ⟨IsRoot.smul hα.1 u, fun i hi => ?_⟩
      have h0 : inner ℝ (ofLattice (u • α)) Y = 0 := by
        rw [hinner, (hkey α hα.1).2 hα, Int.cast_zero]
      exact (inner_root_eq_zero_iff hY (IsRoot.smul hα.1 u)).1 h0 i hi
    · rintro ⟨hβ, hsupp⟩
      have h0 : inner ℝ (ofLattice β) Y = 0 :=
        (inner_root_eq_zero_iff hY hβ).2 fun i hi => hsupp i hi
      refine ⟨u⁻¹ • β, ?_, smul_inv_smul u β⟩
      have hα : IsRoot Tag.E6 (u⁻¹ • β) := IsRoot.smul hβ u⁻¹
      refine (hkey _ hα).1 ?_
      have := hinner (u⁻¹ • β)
      rw [smul_inv_smul, h0] at this
      exact_mod_cast this.symm
  set a := u * w * e6WeylTwist u⁻¹ with ha_def
  have h1 : weylAct Tag.E6 u⁻¹ Y = dualVector r' := by
    rw [← huy, ← weylAct_mul_apply, inv_mul_cancel, map_one, LinearIsometryEquiv.coe_one, id]
  have haψ : weylAct Tag.E6 a (e6TwistIsometry Y) = Y := by
    calc weylAct Tag.E6 a (e6TwistIsometry Y)
        = weylAct Tag.E6 u (weylAct Tag.E6 w
            (weylAct Tag.E6 (e6WeylTwist u⁻¹) (e6TwistIsometry Y))) := by
          rw [ha_def, weylAct_mul_apply, weylAct_mul_apply]
      _ = weylAct Tag.E6 u (weylAct Tag.E6 w (e6TwistIsometry (weylAct Tag.E6 u⁻¹ Y))) := by
          rw [e6TwistIsometry_weylAct]
      _ = Y := by rw [h1, hbfix, huy]
  have hψdom : e6TwistIsometry Y ∈ dominantCone Tag.E6 := fun i => by
    rw [inner_single_e6TwistIsometry]
    exact hY _
  have hψY : e6TwistIsometry Y = Y := by
    have h := weylAct_eq_of_mem_dominantCone hψdom (g := a) (by rw [haψ]; exact hY)
    rw [haψ] at h
    exact h.symm
  have haY : weylAct Tag.E6 a Y = Y := by
    have h := haψ
    rwa [hψY] at h
  have hJρ : ∀ i, i ∈ J ↔ e6Rho i ∈ J := fun i => by
    simp only [hJdef, Set.mem_ofPred_eq]
    rw [← inner_single_e6TwistIsometry, hψY]
  have hconj : ((u * v⁻¹) • ·) '' parabolicRoots Tag.E6 support134 = parabolicRoots Tag.E6 J := by
    rw [← hv, Set.image_image, ← hΦ]
    congr 1
    funext α
    rw [mul_smul, inv_smul_smul]
  have hJ : J = support345 := eq_support345 hJρ hconj
  have ha : a ∈ Subgroup.closure
      {s | ∃ i, s = simple Tag.E6 i ∧ inner ℝ (ofLattice (Pi.single i 1)) Y = 0} := by
    rw [← weylStabilizer_eq_closure_simple hY]
    exact haY
  have hwJ : wJ345 ∈ Subgroup.closure
      {s | ∃ i, s = simple Tag.E6 i ∧ inner ℝ (ofLattice (Pi.single i 1)) Y = 0} :=
    wJ345_mem_closure fun i hi => ⟨i, rfl, by
      have : i ∈ J := hJ ▸ hi
      exact this⟩
  refine ⟨u⁻¹ * (a * wJ345) * u, ?_, fun α hα => ?_⟩
  ·
    have hmem := mul_mem ha hwJ
    generalize a * wJ345 = x at hmem ⊢
    induction hmem using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl, hi⟩ := hx
      have hi' : (Pi.single i 1 : Fin Tag.E6.rank → ℤ) ∈ (u • ·) '' rootKernel z := by
        rw [hΦ]
        exact single_mem_parabolicRoots_E6 hi
      obtain ⟨α, hα, hαi⟩ := hi'
      refine Subgroup.subset_closure ⟨α, hα, ?_⟩
      have e : α = u⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) := by
        rw [← hαi, inv_smul_smul]
      have hsi : rootReflection (Pi.single i 1 : Fin Tag.E6.rank → ℤ) = simple Tag.E6 i := by
        rw [rootReflection_eq_conj (w := 1) (j := i) (one_smul _ _), one_mul, inv_one, mul_one]
      rw [e, rootReflection_smul_root u⁻¹ (isRoot_single Tag.E6 i), hsi, inv_inv]
    | one => simp
    | mul x y _ _ hx hy =>
      have e : u⁻¹ * (x * y) * u = (u⁻¹ * x * u) * (u⁻¹ * y * u) := by group
      rw [e]
      exact mul_mem hx hy
    | inv x _ hx =>
      have e : u⁻¹ * x⁻¹ * u = (u⁻¹ * x * u)⁻¹ := by group
      rw [e]
      exact inv_mem hx
  ·
    have hβ : u • α ∈ parabolicRoots Tag.E6 support345 := by
      rw [← hJ, ← hΦ]
      exact ⟨α, hα, rfl⟩
    have hρ := rho_eq_neg_wJ345 hβ
    have hδ : e6WeylTwist u⁻¹ • permLattice e6Rho (u • α) = permLattice e6Rho α := by
      rw [e6WeylTwist_smul, permLattice_e6Rho_e6Rho, inv_smul_smul]
    have e1 : wJ345 • (u • α) = -permLattice e6Rho (u • α) := by
      rw [hρ, neg_neg]
    rw [mul_smul, mul_smul, mul_smul, e1, smul_neg, smul_neg, neg_neg, ha_def, mul_smul,
      mul_smul, hδ, inv_smul_smul]

end GraphStabilizer

section Main

variable {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
theorem image_graph_rootKernel {z : Fin Tag.E6.rank → ZMod p} {w : WeylGroup Tag.E6}
    (hb : ∀ x, charVal z (w • permLattice e6Rho x) = charVal z x) :
    (fun x => w • permLattice e6Rho x) '' rootKernel z = rootKernel z := by
  have hρroot : ∀ {x : Fin Tag.E6.rank → ℤ}, IsRoot Tag.E6 x →
      IsRoot Tag.E6 (permLattice e6Rho x) :=
    fun hx => hx.permLattice TwistTag.E6.cartan_perm
  ext β
  constructor
  · rintro ⟨α, hα, rfl⟩
    exact ⟨IsRoot.smul (hρroot hα.1) w, by rw [hb]; exact hα.2⟩
  · intro hβ
    refine ⟨permLattice e6Rho (w⁻¹ • β), ⟨hρroot (IsRoot.smul hβ.1 w⁻¹), ?_⟩, ?_⟩
    · rw [charVal_graph_inv hb]
      exact hβ.2
    · change w • permLattice e6Rho (permLattice e6Rho (w⁻¹ • β)) = β
      rw [permLattice_e6Rho_e6Rho, smul_inv_smul]

theorem E6_large_prime_character_stabilizers_and_A3_graph_action (hp5 : 5 < p)
    (z : Fin Tag.E6.rank → ZMod p) :
    (∀ w : WeylGroup Tag.E6, (dualMatrix (ZMod p) w⁻¹).mulVec z = z ↔
      w ∈ Subgroup.closure {s | ∃ α ∈ rootKernel z, s = rootReflection α}) ∧
    (rootKernel z = ∅ →
      ∀ w : WeylGroup Tag.E6, (dualMatrix (ZMod p) w⁻¹).mulVec z = z ↔ w = 1) ∧
    ∀ v : WeylGroup Tag.E6, (v • ·) '' rootKernel z = parabolicRoots Tag.E6 support134 →
      ∀ w : WeylGroup Tag.E6,
        (((rhoMatrix * weylMatrix w⁻¹).map (Int.cast : ℤ → ZMod p)).transpose).mulVec z = z →
          (fun x => w • permLattice e6Rho x) '' rootKernel z = rootKernel z ∧
          (∃ t ∈ Subgroup.closure {s | ∃ α ∈ rootKernel z, s = rootReflection α},
            ∀ α ∈ rootKernel z, w • permLattice e6Rho α = -(t • α)) ∧
          IsNegativeTransition (fun x => v • (w • permLattice e6Rho (v⁻¹ • x)))
            chain134 chain134 := by
  have hA : ∀ w : WeylGroup Tag.E6, (dualMatrix (ZMod p) w⁻¹).mulVec z = z ↔
      w ∈ Subgroup.closure {s | ∃ α ∈ rootKernel z, s = rootReflection α} := fun w => by
    rw [← dualWeylStabilizer_eq_closure hp5 z, mem_dualWeylStabilizer_iff_dualMatrix]
  refine ⟨hA, fun h0 w => ?_, fun v hv w hbm => ?_⟩
  · rw [hA, h0]
    simp only [Set.mem_empty_iff_false, false_and, exists_false, Set.ofPred_false,
      Subgroup.closure_empty, Subgroup.mem_bot]
  · have hb := graph_dual_fixed_iff.1 hbm
    obtain ⟨t, ht, hbt⟩ := graph_stabilizer_A3 hp5 hv hb
    refine ⟨image_graph_rootKernel hb, ⟨t, ht, hbt⟩, ?_⟩
    have ht' : v * t * v⁻¹ ∈ Subgroup.closure
        {s | ∃ β ∈ parabolicRoots Tag.E6 support134, s = rootReflection β} := by
      clear hbt
      induction ht using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨α, hα, rfl⟩ := hx
        refine Subgroup.subset_closure ⟨v • α, ?_, ?_⟩
        · rw [← hv]
          exact ⟨α, hα, rfl⟩
        · rw [rootReflection_smul_root v hα.1]
      | one => simp
      | mul x y _ _ hx hy =>
        have e : v * (x * y) * v⁻¹ = (v * x * v⁻¹) * (v * y * v⁻¹) := by group
        rw [e]
        exact mul_mem hx hy
      | inv x _ hx =>
        have e : v * x⁻¹ * v⁻¹ = (v * x * v⁻¹)⁻¹ := by group
        rw [e]
        exact inv_mem hx
    obtain ⟨π, hπ⟩ := positive_of_mem_closure_134 ht'
    refine ⟨π, fun i j => ?_⟩
    dsimp only
    by_cases hij : i = j
    · subst hij
      rw [chainRoot_self, chainRoot_self, smul_zero]
      have : permLattice e6Rho (0 : Fin Tag.E6.rank → ℤ) = 0 := rfl
      rw [this, smul_zero, smul_zero]
    · have hc := chainRoot134_mem_parabolicRoots hij
      have hc' : v⁻¹ • chainRoot chain134 i j ∈ rootKernel z := by
        rw [← hv] at hc
        obtain ⟨α, hα, hαc⟩ := hc
        rw [← hαc, inv_smul_smul]
        exact hα
      have hπij := hπ i j
      dsimp only at hπij
      rw [hbt _ hc', smul_neg, chainRoot_swap chain134 (π i) (π j), ← hπij, mul_smul, mul_smul]

end Main

end CFSG.RankThree.E6
