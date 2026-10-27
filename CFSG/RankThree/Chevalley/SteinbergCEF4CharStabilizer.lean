module

public import CFSG.RankThree.Chevalley.SteinbergCEF4WeylLength
public import CFSG.RankThree.E6.RootLatticeTools
public import CFSG.LieType.Chevalley.LangWeylChamberStabilizers

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 RootSpace

namespace F4Weyl

section Real

variable {τ : Tag}

@[expose] def columnVector (r : Fin τ.rank → ℤ) : RootSpace τ :=
  ofPi (Matrix.mulVec (formMatrix τ)⁻¹ fun i => (r i : ℝ))

theorem inner_columnVector (x : RootSpace τ) (r : Fin τ.rank → ℤ) :
    inner ℝ x (columnVector r) = ∑ i, x i * (r i : ℝ) := by
  have hdet : IsUnit (formMatrix τ).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (posDef_formMatrix τ).isUnit
  rw [inner_def, columnVector, toPi_ofPi, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet,
    Matrix.one_mulVec]
  rfl

theorem inner_ofLattice_columnVector (v r : Fin τ.rank → ℤ) :
    inner ℝ (ofLattice v) (columnVector r) = ((charVal r v : ℤ) : ℝ) := by
  rw [inner_columnVector, charVal]
  push_cast
  rfl

theorem eq_of_forall_inner_ofLattice
    {y y' : RootSpace τ}
    (h : ∀ v : Fin τ.rank → ℤ, inner ℝ (ofLattice v) y = inner ℝ (ofLattice v) y') :
    y = y' := by
  refine ext_inner_left ℝ fun x => ?_
  rw [← sum_smul_ofLattice_single x, sum_inner, sum_inner]
  exact Finset.sum_congr rfl fun i _ => by rw [inner_smul_left, inner_smul_left, h]

theorem weylAct_columnVector_eq {r : Fin τ.rank → ℤ} {w : WeylGroup τ}
    (h : ∀ v, charVal r (w⁻¹ • v) = charVal r v) :
    weylAct τ w (columnVector r) = columnVector r := by
  refine eq_of_forall_inner_ofLattice fun v => ?_
  have e := inner_weylAct_left w⁻¹ (ofLattice v) (columnVector r)
  rw [inv_inv] at e
  rw [← e, weylAct_ofLattice, inner_ofLattice_columnVector, inner_ofLattice_columnVector, h]

theorem inner_root_eq_zero_iff_of_mem_dominantCone {y : RootSpace τ}
    (hy : y ∈ dominantCone τ) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    inner ℝ (ofLattice α) y = 0 ↔
      ∀ i, inner ℝ (ofLattice (Pi.single i 1)) y ≠ 0 → α i = 0 := by
  rw [inner_ofLattice_eq_sum]
  have key : ∀ (c : Fin τ.rank → ℤ), (∀ i, 0 ≤ c i) →
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

end Real

section Characters

variable {R : Type*} [CommRing R]

@[expose] def charRootKernel (v : Fin Tag.F4.rank → R) : Set (Fin Tag.F4.rank → ℤ) :=
  {α | IsRoot .F4 α ∧ charVal v α = 0}

@[expose] def charStabilizer (v : Fin Tag.F4.rank → R) : Subgroup (WeylGroup .F4) where
  carrier := {w | ∀ x, charVal v (w • x) = charVal v x}
  one_mem' x := by rw [one_smul]
  mul_mem' {w w'} hw hw' x := by rw [mul_smul, hw, hw']
  inv_mem' {w} hw x := by rw [← hw (w⁻¹ • x), smul_inv_smul]

theorem charVal_sub' (z : Fin Tag.F4.rank → R) (x y : Fin Tag.F4.rank → ℤ) :
    charVal z (x - y) = charVal z x - charVal z y := by
  rw [sub_eq_add_neg, charVal_add, charVal_neg, ← sub_eq_add_neg]

theorem invTranspose_weylToAut_eq (w : WeylGroup .F4) :
    invTranspose (weylToAut .F4 w) = (weylMatrix w⁻¹).transpose := by
  ext i j
  rw [invTranspose, Matrix.transpose_apply, Matrix.transpose_apply, LinearMap.toMatrix'_apply,
    weylMatrix_apply, ← map_inv, weylToAut_apply]

theorem mem_charStabilizer_iff {v : Fin Tag.F4.rank → R} {w : WeylGroup .F4} :
    w ∈ charStabilizer v ↔
      ((invTranspose (weylToAut .F4 w)).map (Int.castRingHom R)).mulVec v = v := by
  have e : (invTranspose (weylToAut .F4 w)).map (Int.castRingHom R) = dualMatrix R w⁻¹ := by
    rw [invTranspose_weylToAut_eq, dualMatrix, Matrix.transpose_map]
    rfl
  rw [e]
  constructor
  · intro hw
    refine eq_of_charVal_single fun j => ?_
    rw [charVal_dualMatrix]
    have h := hw (w⁻¹ • Pi.single j 1)
    rw [smul_inv_smul] at h
    exact h.symm
  · intro h x
    have h' := charVal_dualMatrix v w⁻¹ (w • x)
    rw [h, inv_smul_smul] at h'
    exact h'

theorem rootReflection_mem_charStabilizer {v : Fin Tag.F4.rank → R}
    {α : Fin Tag.F4.rank → ℤ} (hα : α ∈ charRootKernel v) :
    rootReflection α ∈ charStabilizer v := by
  intro x
  rw [rootReflection_smul hα.1, charVal_sub', charVal_smul, hα.2, mul_zero, sub_zero]

theorem closure_rootReflection_le_charStabilizer {v : Fin Tag.F4.rank → R} :
    Subgroup.closure {s | ∃ α ∈ charRootKernel v, s = rootReflection α} ≤ charStabilizer v := by
  rw [Subgroup.closure_le]
  rintro _ ⟨α, hα, rfl⟩
  exact rootReflection_mem_charStabilizer hα

end Characters

section Average

variable {p : ℕ} [Fact p.Prime]

@[expose] def intLiftF4 (z : Fin Tag.F4.rank → ZMod p) : Fin Tag.F4.rank → ℤ :=
  fun i => ((z i).val : ℤ)

theorem charVal_intLiftF4_cast (z : Fin Tag.F4.rank → ZMod p) (x : Fin Tag.F4.rank → ℤ) :
    ((charVal (intLiftF4 z) x : ℤ) : ZMod p) = charVal z x := by
  simp [charVal, intLiftF4]

@[expose] def avgColumnF4 (G : Subgroup (WeylGroup .F4)) [Fintype G]
    (z₀ : Fin Tag.F4.rank → ℤ) : Fin Tag.F4.rank → ℤ :=
  fun i => ∑ a : G, charVal z₀ ((a : WeylGroup .F4) • (Pi.single i 1 : Fin Tag.F4.rank → ℤ))

theorem charVal_avgColumnF4 (G : Subgroup (WeylGroup .F4)) [Fintype G]
    (z₀ : Fin Tag.F4.rank → ℤ) (x : Fin Tag.F4.rank → ℤ) :
    charVal (avgColumnF4 G z₀) x = ∑ a : G, charVal z₀ ((a : WeylGroup .F4) • x) := by
  have hsum : ∀ (w : WeylGroup .F4), charVal z₀ (w • x) =
      ∑ j, (x j : ℤ) * charVal z₀ (w • (Pi.single j 1 : Fin Tag.F4.rank → ℤ)) := fun w => by
    rw [← weylMatrix_mulVec, charVal_mulVec_eq_sum]
    rfl
  simp only [charVal, avgColumnF4, Int.cast_id, Finset.mul_sum] at hsum ⊢
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hsum]

theorem charVal_avgColumnF4_smul {G : Subgroup (WeylGroup .F4)} [Fintype G]
    (z₀ : Fin Tag.F4.rank → ℤ) {w : WeylGroup .F4} (hw : w ∈ G) (x : Fin Tag.F4.rank → ℤ) :
    charVal (avgColumnF4 G z₀) (w • x) = charVal (avgColumnF4 G z₀) x := by
  rw [charVal_avgColumnF4, charVal_avgColumnF4]
  refine Fintype.sum_equiv (Equiv.mulRight ⟨w, hw⟩) _ _ fun a => ?_
  rw [Equiv.coe_mulRight, Subgroup.coe_mul, mul_smul]

theorem charVal_avgColumnF4_cast {G : Subgroup (WeylGroup .F4)} [Fintype G]
    {z : Fin Tag.F4.rank → ZMod p} (hG : G ≤ charStabilizer z) (x : Fin Tag.F4.rank → ℤ) :
    ((charVal (avgColumnF4 G (intLiftF4 z)) x : ℤ) : ZMod p) =
      (Fintype.card G : ZMod p) * charVal z x := by
  rw [charVal_avgColumnF4, Int.cast_sum]
  simp only [charVal_intLiftF4_cast]
  rw [Finset.sum_congr rfl fun a _ => hG a.2 x, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem card_subgroup_ne_zero_F4 (hp3 : 3 < p) (G : Subgroup (WeylGroup .F4)) [Fintype G] :
    (Fintype.card G : ZMod p) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have : Fintype (WeylGroup .F4) := Fintype.ofFinite _
  have hG : Fintype.card G ∣ 1152 := by
    rw [← (weyl_length_polynomial).2, ← Nat.card_eq_fintype_card]
    exact Subgroup.card_subgroup_dvd_card G
  have hp : p.Prime := Fact.out
  have h1 := h.trans hG
  rw [show (1152 : ℕ) = 2 ^ 7 * 3 ^ 2 by norm_num] at h1
  rcases hp.dvd_mul.1 h1 with h2 | h2
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2)
    omega
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2)
    omega

theorem charVal_avgColumnF4_eq_zero_iff {G : Subgroup (WeylGroup .F4)} [Fintype G]
    {z : Fin Tag.F4.rank → ZMod p} (hG : G ≤ charStabilizer z)
    (hrefl : ∀ α ∈ charRootKernel z, rootReflection α ∈ G)
    (hcard : (Fintype.card G : ZMod p) ≠ 0) {α : Fin Tag.F4.rank → ℤ} (hα : IsRoot .F4 α) :
    charVal (avgColumnF4 G (intLiftF4 z)) α = 0 ↔ α ∈ charRootKernel z := by
  constructor
  · intro h
    have h' := charVal_avgColumnF4_cast hG α
    rw [h, Int.cast_zero, eq_comm] at h'
    exact ⟨hα, (mul_eq_zero.1 h').resolve_left hcard⟩
  · intro hk
    have h := charVal_avgColumnF4_smul (intLiftF4 z) (hrefl α hk) α
    rw [rootReflection_smul_self hα, charVal_neg] at h
    omega

end Average

section Kernel

variable {p : ℕ} [Fact p.Prime]

theorem exists_column_of_charStabilizer (hp3 : 3 < p) (z : Fin Tag.F4.rank → ZMod p) :
    ∃ r : Fin Tag.F4.rank → ℤ,
      (∀ α, IsRoot .F4 α → (charVal r α = 0 ↔ α ∈ charRootKernel z)) ∧
      (∀ w ∈ charStabilizer z, ∀ x, charVal r (w • x) = charVal r x) ∧
      (∀ i, ((r i : ℤ) : ZMod p) = 0 → z i = 0) := by
  classical
  set U := charStabilizer z
  have : Fintype U := Fintype.ofFinite _
  refine ⟨avgColumnF4 U (intLiftF4 z), fun α hα =>
    charVal_avgColumnF4_eq_zero_iff le_rfl (fun _ h => rootReflection_mem_charStabilizer h)
      (card_subgroup_ne_zero_F4 hp3 U) hα,
    fun w hw x => charVal_avgColumnF4_smul _ hw x, fun i hi => ?_⟩
  have h := charVal_avgColumnF4_cast (le_rfl : U ≤ charStabilizer z) (Pi.single i 1)
  rw [charVal_single, charVal_single, hi] at h
  exact (mul_eq_zero.1 h.symm).resolve_left (card_subgroup_ne_zero_F4 hp3 U)

theorem charStabilizer_eq_closure (hp3 : 3 < p) (z : Fin Tag.F4.rank → ZMod p) :
    charStabilizer z = Subgroup.closure {s | ∃ α ∈ charRootKernel z, s = rootReflection α} := by
  obtain ⟨r, hker, hfix, -⟩ := exists_column_of_charStabilizer hp3 z
  refine le_antisymm (fun w hw => ?_) closure_rootReflection_le_charStabilizer
  have hw' : w ∈ weylStabilizer .F4 (columnVector r) :=
    weylAct_columnVector_eq fun v => hfix _ ((charStabilizer z).inv_mem hw) v
  rw [(exceptional_Lang_Weyl_chamber_point_stabilizers .F4).2.2.2.2.2 (columnVector r)] at hw'
  convert hw' using 2
  ext s
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨α, hα, rfl⟩
    exact ⟨α, hα.1, by rw [inner_ofLattice_columnVector, (hker α hα.1).2 hα, Int.cast_zero], rfl⟩
  · rintro ⟨α, hα, h0, rfl⟩
    rw [inner_ofLattice_columnVector, Int.cast_eq_zero] at h0
    exact ⟨α, (hker α hα).1 h0, rfl⟩

theorem exists_smul_charRootKernel_eq_parabolicRoots (hp3 : 3 < p)
    {z : Fin Tag.F4.rank → ZMod p} (hz : z ≠ 0) :
    ∃ (u : WeylGroup .F4) (J : Set (Fin Tag.F4.rank)), J ≠ Set.univ ∧
      (fun α => u • α) '' charRootKernel z = parabolicRoots .F4 J := by
  classical
  obtain ⟨r, hker, -, hr⟩ := exists_column_of_charStabilizer hp3 z
  obtain ⟨u, hu⟩ := (exceptional_Lang_Weyl_chamber_point_stabilizers .F4).2.2.1 (columnVector r)
  set Y := weylAct .F4 u (columnVector r) with hY
  refine ⟨u, {i | inner ℝ (ofLattice (Pi.single i 1)) Y = 0}, fun hJ => hz ?_, ?_⟩
  ·
    have hY0 : Y = 0 := eq_of_forall_inner_ofLattice fun v => by
      rw [inner_ofLattice_eq_sum, inner_zero_right]
      refine Finset.sum_eq_zero fun i _ => ?_
      have hi : i ∈ {i | inner ℝ (ofLattice (Pi.single i 1)) Y = 0} := hJ ▸ Set.mem_univ i
      rw [show inner ℝ (ofLattice (Pi.single i 1)) Y = 0 from hi, mul_zero]
    have hy0 : columnVector r = 0 := (LinearIsometryEquiv.map_eq_zero_iff _).1 hY0
    funext i
    refine hr i ?_
    have h := inner_ofLattice_columnVector (Pi.single i 1) r
    rw [hy0, inner_zero_right, charVal_single] at h
    exact_mod_cast (Int.cast_eq_zero.1 h.symm ▸ rfl : ((r i : ℤ) : ZMod p) = ((0 : ℤ) : ZMod p))
  · ext β
    constructor
    · rintro ⟨α, hα, rfl⟩
      refine ⟨IsRoot.smul hα.1 u, fun i hi => ?_⟩
      have h0 : inner ℝ (ofLattice (u • α)) Y = 0 := by
        rw [hY, ← weylAct_ofLattice, LinearIsometryEquiv.inner_map_map,
          inner_ofLattice_columnVector, (hker α hα.1).2 hα, Int.cast_zero]
      exact (inner_root_eq_zero_iff_of_mem_dominantCone hu (IsRoot.smul hα.1 u)).1 h0 i hi
    · rintro ⟨hβ, hβJ⟩
      refine ⟨u⁻¹ • β, (hker _ (IsRoot.smul hβ u⁻¹)).1 ?_, smul_inv_smul u β⟩
      have h0 : inner ℝ (ofLattice β) Y = 0 :=
        (inner_root_eq_zero_iff_of_mem_dominantCone hu hβ).2 fun i hi => hβJ i hi
      have e : inner ℝ (ofLattice (u⁻¹ • β)) (columnVector r) = inner ℝ (ofLattice β) Y := by
        rw [hY, ← weylAct_ofLattice, inner_weylAct_left, inv_inv]
      rw [h0, inner_ofLattice_columnVector] at e
      exact_mod_cast e

end Kernel

theorem coe_closure_singleton_of_mul_self {G : Type*} [Group G] {g : G} (hg : g * g = 1) :
    (Subgroup.closure {g} : Set G) = {1, g} := by
  ext x
  rw [SetLike.mem_coe, Subgroup.mem_closure_singleton]
  constructor
  · rintro ⟨n, rfl⟩
    have h2 : g ^ (2 : ℤ) = 1 := by rw [zpow_two, hg]
    rw [← Int.mul_ediv_add_emod n 2, zpow_add, zpow_mul, h2, one_zpow, one_mul]
    rcases Int.emod_two_eq_zero_or_one n with h | h
    · rw [h, zpow_zero]
      exact Set.mem_insert _ _
    · rw [h, zpow_one]
      exact Set.mem_insert_of_mem _ rfl
  · rintro (h | h)
    · exact ⟨0, by rw [zpow_zero, h]⟩
    · exact ⟨1, by rw [zpow_one, Set.mem_singleton_iff.1 h]⟩

end F4Weyl

open F4Weyl

theorem F4_prime_character_Weyl_stabilizer_parabolic_root_kernel {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) {v : Fin Tag.F4.rank → ZMod p} (hv : v ≠ 0) :
    (∀ w : WeylGroup .F4,
      ((invTranspose (weylToAut .F4 w)).map (Int.castRingHom (ZMod p))).mulVec v = v ↔
        w ∈ Subgroup.closure {s | ∃ α ∈ charRootKernel v, s = rootReflection α}) ∧
    (∃ (u : WeylGroup .F4) (J : Set (Fin Tag.F4.rank)), J ≠ Set.univ ∧
      (fun α => u • α) '' charRootKernel v = parabolicRoots .F4 J) ∧
    ∀ α : Fin Tag.F4.rank → ℤ, charRootKernel v = {α, -α} →
      {w : WeylGroup .F4 |
          ((invTranspose (weylToAut .F4 w)).map (Int.castRingHom (ZMod p))).mulVec v = v} =
        {1, rootReflection α} := by
  have : Fact p.Prime := ⟨hp⟩
  have hW := charStabilizer_eq_closure hp3 v
  refine ⟨fun w => by rw [← mem_charStabilizer_iff, hW],
    exists_smul_charRootKernel_eq_parabolicRoots hp3 hv, fun α hpair => ?_⟩
  have hα : IsRoot .F4 α := by
    have h : α ∈ charRootKernel v := by
      rw [hpair]
      exact Set.mem_insert _ _
    exact h.1
  have hset : {s | ∃ β ∈ charRootKernel v, s = rootReflection β} = {rootReflection α} := by
    rw [hpair]
    ext s
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨β, rfl | rfl, rfl⟩
      · rfl
      · exact rootReflection_neg hα
    · rintro rfl
      exact ⟨α, Or.inl rfl, rfl⟩
  have e : {w : WeylGroup .F4 |
      ((invTranspose (weylToAut .F4 w)).map (Int.castRingHom (ZMod p))).mulVec v = v} =
        (charStabilizer v : Set (WeylGroup .F4)) := by
    ext w
    exact mem_charStabilizer_iff.symm
  rw [e, hW, hset, coe_closure_singleton_of_mul_self (rootReflection_mul_self hα)]

end CFSG.RankThree.Chevalley
