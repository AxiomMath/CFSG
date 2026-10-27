module

public import CFSG.RankThree.E6.RootLatticeTools
public import CFSG.LieType.Chevalley.LangWeylChamberStabilizers
public import CFSG.RankThree.Chevalley.EWeylLengthPolynomials
public import CFSG.LieType.Chevalley.ToralCentralizerBruhat

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint RootSpace
open CFSG.RankThree.E6 (charVal charVal_add charVal_neg charVal_smul charVal_single
  dualMatrix charVal_dualMatrix eq_of_charVal_single weylMatrix_mulVec charVal_mulVec_eq_sum)

variable {τ : Tag}

@[expose] def rootKernel {R : Type*} [CommRing R] (z : Fin τ.rank → R) :
    Set (Fin τ.rank → ℤ) :=
  {α | IsRoot τ α ∧ charVal z α = 0}

theorem mem_rootKernel {R : Type*} [CommRing R] {z : Fin τ.rank → R} {α : Fin τ.rank → ℤ} :
    α ∈ rootKernel z ↔ IsRoot τ α ∧ charVal z α = 0 :=
  Iff.rfl

section Dual

variable {K : Type*} [CommRing K]

theorem charVal_sub (z : Fin τ.rank → K) (x y : Fin τ.rank → ℤ) :
    charVal z (x - y) = charVal z x - charVal z y := by
  rw [sub_eq_add_neg, charVal_add, charVal_neg, ← sub_eq_add_neg]

@[expose] def dualWeylStabilizer (z : Fin τ.rank → K) : Subgroup (WeylGroup τ) where
  carrier := {w | ∀ x, charVal z (w • x) = charVal z x}
  one_mem' x := by rw [one_smul]
  mul_mem' {w w'} hw hw' x := by rw [mul_smul, hw, hw']
  inv_mem' {w} hw x := by rw [← hw (w⁻¹ • x), smul_inv_smul]

theorem mem_dualWeylStabilizer {z : Fin τ.rank → K} {w : WeylGroup τ} :
    w ∈ dualWeylStabilizer z ↔ ∀ x, charVal z (w • x) = charVal z x :=
  Iff.rfl

theorem mem_dualWeylStabilizer_iff_dualMatrix {z : Fin τ.rank → K}
    {w : WeylGroup τ} :
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

theorem rootReflection_mem_dualWeylStabilizer {z : Fin τ.rank → K}
    {α : Fin τ.rank → ℤ} (hα : α ∈ rootKernel z) :
    rootReflection α ∈ dualWeylStabilizer z := by
  intro x
  rw [rootReflection_smul hα.1, charVal_sub, charVal_smul, hα.2, mul_zero, sub_zero]

theorem closure_rootReflection_le {z : Fin τ.rank → K} :
    Subgroup.closure {s | ∃ α ∈ rootKernel z, s = rootReflection α} ≤ dualWeylStabilizer z := by
  rw [Subgroup.closure_le]
  rintro _ ⟨α, hα, rfl⟩
  exact rootReflection_mem_dualWeylStabilizer hα

end Dual

@[expose] def dualVector (r : Fin τ.rank → ℤ) : RootSpace τ :=
  ofPi (Matrix.mulVec (formMatrix τ)⁻¹ fun i => (r i : ℝ))

theorem inner_dualVector (x : RootSpace τ) (r : Fin τ.rank → ℤ) :
    inner ℝ x (dualVector r) = ∑ i, x i * (r i : ℝ) := by
  have hdet : IsUnit (formMatrix τ).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (posDef_formMatrix τ).isUnit
  rw [inner_def, dualVector, toPi_ofPi, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet,
    Matrix.one_mulVec]
  rfl

theorem inner_ofLattice_dualVector (v r : Fin τ.rank → ℤ) :
    inner ℝ (ofLattice v) (dualVector r) = ((charVal r v : ℤ) : ℝ) := by
  rw [inner_dualVector, charVal]
  push_cast
  rfl

theorem eq_of_inner_ofLattice {y y' : RootSpace τ}
    (h : ∀ v : Fin τ.rank → ℤ, inner ℝ (ofLattice v) y = inner ℝ (ofLattice v) y') :
    y = y' := by
  refine ext_inner_left ℝ fun x => ?_
  rw [← sum_smul_ofLattice_single x, sum_inner, sum_inner]
  exact Finset.sum_congr rfl fun i _ => by rw [inner_smul_left, inner_smul_left, h]

theorem weylAct_dualVector_eq {r : Fin τ.rank → ℤ} {w : WeylGroup τ}
    (h : ∀ v, charVal r (w⁻¹ • v) = charVal r v) :
    weylAct τ w (dualVector r) = dualVector r := by
  refine eq_of_inner_ofLattice fun v => ?_
  have e := inner_weylAct_left w⁻¹ (ofLattice v) (dualVector r)
  rw [inv_inv] at e
  rw [← e, weylAct_ofLattice, inner_ofLattice_dualVector, inner_ofLattice_dualVector, h]

section Average

variable {p : ℕ} [Fact p.Prime]

@[expose] def intLift (z : Fin τ.rank → ZMod p) : Fin τ.rank → ℤ :=
  fun i => ((z i).val : ℤ)

theorem intLift_cast (z : Fin τ.rank → ZMod p) (i : Fin τ.rank) :
    ((intLift z i : ℤ) : ZMod p) = z i := by
  simp [intLift]

theorem charVal_intLift_cast (z : Fin τ.rank → ZMod p) (x : Fin τ.rank → ℤ) :
    ((charVal (intLift z) x : ℤ) : ZMod p) = charVal z x := by
  simp only [charVal, Int.cast_sum, Int.cast_mul, Int.cast_id, intLift_cast]

@[expose] def avgColumn (G : Subgroup (WeylGroup τ)) [Fintype G]
    (z₀ : Fin τ.rank → ℤ) : Fin τ.rank → ℤ :=
  fun i => ∑ a : G, charVal z₀ ((a : WeylGroup τ) • (Pi.single i 1 : Fin τ.rank → ℤ))

theorem charVal_int_eq (r x : Fin τ.rank → ℤ) : charVal r x = ∑ i, x i * r i := by
  simp only [charVal, Int.cast_id]

theorem charVal_smul_eq_sum {R : Type*} [CommRing R] (z : Fin τ.rank → R)
    (w : WeylGroup τ) (x : Fin τ.rank → ℤ) :
    charVal z (w • x) = ∑ j, (x j : R) * charVal z (w • (Pi.single j 1 : Fin τ.rank → ℤ)) := by
  rw [← weylMatrix_mulVec, charVal_mulVec_eq_sum]
  rfl

theorem charVal_avgColumn (G : Subgroup (WeylGroup τ)) [Fintype G]
    (z₀ : Fin τ.rank → ℤ) (x : Fin τ.rank → ℤ) :
    charVal (avgColumn G z₀) x = ∑ a : G, charVal z₀ ((a : WeylGroup τ) • x) := by
  rw [charVal_int_eq]
  simp only [avgColumn, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [charVal_smul_eq_sum]
  simp only [Int.cast_id]

theorem charVal_avgColumn_smul {G : Subgroup (WeylGroup τ)} [Fintype G]
    (z₀ : Fin τ.rank → ℤ) {w : WeylGroup τ} (hw : w ∈ G) (x : Fin τ.rank → ℤ) :
    charVal (avgColumn G z₀) (w • x) = charVal (avgColumn G z₀) x := by
  rw [charVal_avgColumn, charVal_avgColumn]
  refine Fintype.sum_equiv (Equiv.mulRight ⟨w, hw⟩) _ _ fun a => ?_
  rw [Equiv.coe_mulRight, Subgroup.coe_mul, mul_smul]

theorem charVal_avgColumn_cast {G : Subgroup (WeylGroup τ)} [Fintype G]
    {z : Fin τ.rank → ZMod p} (hG : G ≤ dualWeylStabilizer z) (x : Fin τ.rank → ℤ) :
    ((charVal (avgColumn G (intLift z)) x : ℤ) : ZMod p) =
      (Fintype.card G : ZMod p) * charVal z x := by
  rw [charVal_avgColumn, Int.cast_sum]
  simp only [charVal_intLift_cast]
  rw [Finset.sum_congr rfl fun a _ => hG a.2 x, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Average

theorem card_subgroup_ne_zero {p : ℕ} [Fact p.Prime] (hord : ¬ p ∣ Nat.card (WeylGroup τ))
    (G : Subgroup (WeylGroup τ)) [Fintype G] : (Fintype.card G : ZMod p) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have hG : Fintype.card G ∣ Nat.card (WeylGroup τ) := by
    rw [← Nat.card_eq_fintype_card]
    exact Subgroup.card_subgroup_dvd_card G
  exact hord (h.trans hG)

section Stabilizer

variable {p : ℕ} [Fact p.Prime]

theorem charVal_avgColumn_eq_zero_iff {G : Subgroup (WeylGroup τ)} [Fintype G]
    {z : Fin τ.rank → ZMod p} (hG : G ≤ dualWeylStabilizer z)
    (hrefl : ∀ α ∈ rootKernel z, rootReflection α ∈ G) (hcard : (Fintype.card G : ZMod p) ≠ 0)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
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

theorem dualWeylStabilizer_eq_closure (hord : ¬ p ∣ Nat.card (WeylGroup τ))
    (z : Fin τ.rank → ZMod p) :
    dualWeylStabilizer z = Subgroup.closure {s | ∃ α ∈ rootKernel z, s = rootReflection α} := by
  classical
  set U := dualWeylStabilizer z
  have : Fintype U := Fintype.ofFinite _
  set r := avgColumn U (intLift z)
  have hker : ∀ α, IsRoot τ α → (charVal r α = 0 ↔ α ∈ rootKernel z) := fun α hα =>
    charVal_avgColumn_eq_zero_iff le_rfl (fun _ h => rootReflection_mem_dualWeylStabilizer h)
      (card_subgroup_ne_zero hord U) hα
  refine le_antisymm (fun w hw => ?_) closure_rootReflection_le
  have hfix : w ∈ weylStabilizer τ (dualVector r) :=
    weylAct_dualVector_eq fun v => charVal_avgColumn_smul _ (U.inv_mem hw) v
  rw [(exceptional_Lang_Weyl_chamber_point_stabilizers τ).2.2.2.2.2 (dualVector r)] at hfix
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
theorem dualWeylStabilizer_eq_bot_of_regular {p : ℕ} [Fact p.Prime]
    (hord : ¬ p ∣ Nat.card (WeylGroup τ)) (z : Fin τ.rank → ZMod p)
    (hreg : ∀ α : Fin τ.rank → ℤ, IsRoot τ α → charVal z α ≠ 0) :
    dualWeylStabilizer z = ⊥ := by
  rw [dualWeylStabilizer_eq_closure hord z]
  have : {s | ∃ α ∈ rootKernel z, s = rootReflection α} = (∅ : Set (WeylGroup τ)) := by
    refine Set.eq_empty_of_forall_notMem fun s ⟨α, hα, _⟩ => hreg α hα.1 hα.2
  rw [this, Subgroup.closure_empty]

theorem not_dvd_card_weylGroup_E {p : ℕ} (hp : p.Prime) (hp7 : 7 < p) {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) : ¬ p ∣ Nat.card (WeylGroup τ) := by
  have : Fintype (WeylGroup τ) := Fintype.ofFinite _
  have hsmall : ∀ q : ℕ, q.Prime → q ∣ 2 ^ 14 * 3 ^ 5 * 5 ^ 2 * 7 → q ≤ 7 := by
    intro q hq h
    rcases (Nat.Prime.dvd_mul hq).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hq).1 h with h | h
      · rcases (Nat.Prime.dvd_mul hq).1 h with h | h
        · exact (Nat.le_of_dvd (by norm_num) (hq.dvd_of_dvd_pow h)).trans (by norm_num)
        · exact (Nat.le_of_dvd (by norm_num) (hq.dvd_of_dvd_pow h)).trans (by norm_num)
      · exact (Nat.le_of_dvd (by norm_num) (hq.dvd_of_dvd_pow h)).trans (by norm_num)
    · exact Nat.le_of_dvd (by norm_num) h
  intro hdvd
  have hW : Nat.card (WeylGroup τ) ∣ 2 ^ 14 * 3 ^ 5 * 5 ^ 2 * 7 := by
    rcases hτ with rfl | rfl | rfl
    · rw [(CFSG.RankThree.Chevalley.E6_weyl_length_polynomial).2]
      norm_num
    · rw [(CFSG.RankThree.Chevalley.E7_weyl_length_polynomial).2]
      norm_num
    · rw [(CFSG.RankThree.Chevalley.E8_weyl_length_polynomial).2]
      norm_num
  have := hsmall p hp (hdvd.trans hW)
  omega

section Regular

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem rootChar_eq_zpow {M : Type} [Field M] {τ : Tag} {ζ : Mˣ} (v : Fin τ.rank → ℕ)
    (a : Fin τ.rank → Mˣ) (ha : ∀ i, a i = ζ ^ v i) (l : Fin τ.rank → ℤ) :
    rootChar a l = ζ ^ (∑ i, (v i : ℤ) * l i) := by
  simp only [rootChar, ha, ← zpow_natCast, ← zpow_mul, Finset.prod_zpow_eq_zpow_sum]

theorem rootChar_eq_rootChar_iff {M : Type} [Field M] {τ : Tag} {p : ℕ} {ζ : Mˣ}
    (hζ : orderOf ζ = p) (v : Fin τ.rank → ℕ) (a : Fin τ.rank → Mˣ) (ha : ∀ i, a i = ζ ^ v i)
    (l l' : Fin τ.rank → ℤ) :
    rootChar a l = rootChar a l' ↔
      charVal (fun i => (v i : ZMod p)) l = charVal (fun i => (v i : ZMod p)) l' := by
  rw [rootChar_eq_zpow v a ha, rootChar_eq_zpow v a ha, zpow_eq_zpow_iff_modEq, hζ,
    ← ZMod.intCast_eq_intCast_iff]
  have hc : ∀ u : Fin τ.rank → ℤ, ∑ i, ((v i : ℕ) : ZMod p) * (u i : ZMod p) =
      ∑ i, (u i : ZMod p) * ((v i : ℕ) : ZMod p) := fun u =>
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  simp only [charVal, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
  rw [hc l, hc l']

theorem regular_prime_toral_centralizer (τ : Tag) (M : Type) [Field M] [Finite M] {p : ℕ}
    (hp : p.Prime) (hord : ¬ p ∣ Nat.card (WeylGroup τ)) (hpM : p ∣ Nat.card Mˣ)
    {x : ModGL τ M} (hxH : x ∈ torusGroup τ M) (hxp : orderOf x = p)
    (hreg : ∀ a : Fin τ.rank → Mˣ, x = rootDiagUnit τ a →
      ∀ α : Fin τ.rank → ℤ, IsRoot τ α → rootChar a α ≠ 1) :
    adjointGroup τ M ⊓ Subgroup.centralizer {x} = torusGroup τ M := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hxH
  have hap : ∀ i, a i ^ p = 1 := by
    have h1 : rootDiagUnit τ (a ^ p) = 1 := by
      have hpow : rootDiagUnit τ a ^ p = rootDiagUnit τ (a ^ p) :=
        ((rootDiagUnitHom τ M).map_pow a p).symm
      rw [← hpow, ← hxp]
      exact pow_orderOf_eq_one _
    have h2 : a ^ p = 1 := rootDiagUnit_injective (h1.trans rootDiagUnit_one.symm)
    intro i
    exact congrFun h2 i
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Mˣ, orderOf ζ = p :=
    exists_prime_orderOf_dvd_card' p hpM
  have hprim : IsPrimitiveRoot (ζ : M) p :=
    IsPrimitiveRoot.coe_units_iff.2 (IsPrimitiveRoot.iff_orderOf.2 hζ)
  have hexp : ∀ i, ∃ n : ℕ, a i = ζ ^ n := fun i => by
    have hi : ((a i : Mˣ) : M) ^ p = 1 := by
      rw [← Units.val_pow_eq_pow_val, hap i, Units.val_one]
    obtain ⟨n, -, hn⟩ := hprim.eq_pow_of_pow_eq_one hi
    exact ⟨n, Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hn.symm)⟩
  choose v hv using hexp
  set z : Fin τ.rank → ZMod p := fun i => (v i : ZMod p) with hz
  have hreg' : ∀ α : Fin τ.rank → ℤ, IsRoot τ α → charVal z α ≠ 0 := by
    intro α hα h0
    refine hreg a rfl α hα ?_
    have h1 : rootChar a (0 : Fin τ.rank → ℤ) = 1 := by simp [rootChar]
    rw [← h1, rootChar_eq_rootChar_iff hζ v a hv]
    simpa [charVal] using h0
  have hstab : dualWeylStabilizer z = ⊥ := dualWeylStabilizer_eq_bot_of_regular hord z hreg'
  have hW : ∀ w ∈ rootCharStabilizer a, w = 1 := by
    intro w hw
    have hmem : w ∈ dualWeylStabilizer z := fun y =>
      ((rootChar_eq_rootChar_iff hζ v a hv (w • y) y).1 (hw y))
    rw [hstab] at hmem
    exact Subgroup.mem_bot.1 hmem
  have hker : rootCharKernel a = ∅ := Set.eq_empty_of_forall_notMem fun α ⟨hα, h1⟩ =>
    hreg a rfl α hα h1
  have hX : toralCentralizer τ M a = torusGroup τ M := by
    have h := (Chevalley_toral_centralizer_Bruhat_factors τ M a).2.2.2
    have h0 : rootSpan τ M (∅ : Set (Fin τ.rank → ℤ)) = ⊥ := by simp [rootSpan]
    have h1 : Subgroup.closure
        ((fun w => canonicalRep (coxeterSystem τ) M w) '' rootCharStabilizer a) = ⊥ := by
      rw [eq_bot_iff, Subgroup.closure_le]
      rintro _ ⟨w, hw, rfl⟩
      simp only [SetLike.mem_coe, Subgroup.mem_bot]
      rw [hW w hw]
      exact canonicalRep_one (coxeterSystem τ) M
    rw [h, hker, h0, h1, sup_bot_eq, sup_bot_eq]
  exact hX

theorem E_regular_large_prime_toral_centralizer (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (M : Type) [Field M] [Finite M] {p : ℕ} (hp : p.Prime) (hp7 : 7 < p)
    (hpM : p ∣ Nat.card Mˣ) {x : ModGL τ M} (hxH : x ∈ torusGroup τ M) (hxp : orderOf x = p)
    (hreg : ∀ a : Fin τ.rank → Mˣ, x = rootDiagUnit τ a →
      ∀ α : Fin τ.rank → ℤ, IsRoot τ α → rootChar a α ≠ 1) :
    adjointGroup τ M ⊓ Subgroup.centralizer {x} = torusGroup τ M :=
  regular_prime_toral_centralizer τ M hp (not_dvd_card_weylGroup_E hp hp7 hτ) hpM hxH hxp hreg

theorem E6_E7_regular_large_prime_toral_centralizers (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7)
    (M : Type) [Field M] [Finite M] {p : ℕ} (hp : p.Prime) (hp7 : 7 < p)
    (hpM : p ∣ Nat.card Mˣ) {x : ModGL τ M} (hxH : x ∈ torusGroup τ M) (hxp : orderOf x = p)
    (hreg : ∀ a : Fin τ.rank → Mˣ, x = rootDiagUnit τ a →
      ∀ α : Fin τ.rank → ℤ, IsRoot τ α → rootChar a α ≠ 1) :
    adjointGroup τ M ⊓ Subgroup.centralizer {x} = torusGroup τ M :=
  E_regular_large_prime_toral_centralizer τ (by rcases hτ with h | h <;> simp [h]) M hp hp7 hpM
    hxH hxp hreg

theorem E8_regular_large_prime_toral_centralizers (M : Type) [Field M] [Finite M] {p : ℕ}
    (hp : p.Prime) (hp7 : 7 < p) (hpM : p ∣ Nat.card Mˣ) {x : ModGL Tag.E8 M}
    (hxH : x ∈ torusGroup Tag.E8 M) (hxp : orderOf x = p)
    (hreg : ∀ a : Fin Tag.E8.rank → Mˣ, x = rootDiagUnit Tag.E8 a →
      ∀ α : Fin Tag.E8.rank → ℤ, IsRoot Tag.E8 α → rootChar a α ≠ 1) :
    adjointGroup Tag.E8 M ⊓ Subgroup.centralizer {x} = torusGroup Tag.E8 M :=
  E_regular_large_prime_toral_centralizer Tag.E8 (Or.inr (Or.inr rfl)) M hp hp7 hpM hxH hxp hreg

end Regular

end CFSG.RankThree.PartOne.KE
