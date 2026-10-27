module


public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFivePhaseProps

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] noncomputable def semilinConjGL (A : GL ι K) (σ : K ≃+* K) : GL ι K →* GL ι K :=
  (MulAut.conj A).toMonoidHom.comp (Matrix.GeneralLinearGroup.map σ.toRingHom)

private noncomputable def glEnd {Ω : Type} [Field Ω] :
    GL ι Ω →* Module.End Ω (ι → Ω) :=
  (Units.coeHom (Module.End Ω (ι → Ω))).comp
    (Matrix.GeneralLinearGroup.toLin (n := ι) (R := Ω)).toMonoidHom

private lemma glEnd_injective {Ω : Type} [Field Ω] :
    Function.Injective (glEnd (ι := ι) (Ω := Ω)) := by
  intro x y h
  exact Matrix.GeneralLinearGroup.toLin.injective (Units.ext h)

private noncomputable def weightSpace {Ω V E : Type*} [Field Ω] [AddCommGroup V] [Module Ω V]
    (f : E → Module.End Ω V) (χ : E → Ω) : Submodule Ω V :=
  ⨅ x : E, (f x).eigenspace (χ x)

private lemma mem_weightSpace {Ω V E : Type*} [Field Ω] [AddCommGroup V] [Module Ω V]
    (f : E → Module.End Ω V) (χ : E → Ω) (v : V) :
    v ∈ weightSpace f χ ↔ ∀ x, f x v = χ x • v := by
  simp [weightSpace]

private lemma isSemisimple_of_pow_eq_one {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V]
    (h31 : (31 : Ω) ≠ 0) (g : Module.End Ω V) (hg : g ^ 31 = 1) : g.IsSemisimple := by
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (p := Polynomial.X ^ 31 - Polynomial.C 1) ?_ ?_
  · simpa using (Polynomial.separable_X_pow_sub_C (1 : Ω) h31 one_ne_zero).squarefree
  · simp [hg]

private noncomputable def glEndSub {Ω : Type} [Field Ω] (E : Subgroup (GL ι Ω)) :
    E →* Module.End Ω (ι → Ω) :=
  (glEnd (ι := ι) (Ω := Ω)).comp E.subtype

private lemma glEndSub_injective {Ω : Type} [Field Ω] (E : Subgroup (GL ι Ω)) :
    Function.Injective (glEndSub E) := by
  intro x y h
  exact Subtype.ext (glEnd_injective h)

private lemma weight_apply_one {Ω V E : Type*} [Field Ω] [AddCommGroup V] [Module Ω V]
    [Group E] (f : E →* Module.End Ω V) {χ : E → Ω} (hχ : weightSpace f χ ≠ ⊥) : χ 1 = 1 := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
  have h : v = χ 1 • v := by
    have := (mem_weightSpace f χ v).mp hv 1
    simpa using this
  have h' : (χ 1 - 1) • v = 0 := by rw [sub_smul, one_smul, ← h, sub_self]
  rcases smul_eq_zero.mp h' with h'' | h''
  · exact sub_eq_zero.mp h''
  · exact absurd h'' hv0

private lemma weight_apply_mul {Ω V E : Type*} [Field Ω] [AddCommGroup V] [Module Ω V]
    [Group E] (f : E →* Module.End Ω V) {χ : E → Ω} (hχ : weightSpace f χ ≠ ⊥) (x y : E) :
    χ (x * y) = χ x * χ y := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
  have hx := (mem_weightSpace f χ v).mp hv x
  have hy := (mem_weightSpace f χ v).mp hv y
  have h := (mem_weightSpace f χ v).mp hv (x * y)
  have h2 : f (x * y) v = (χ x * χ y) • v := by
    rw [map_mul, Module.End.mul_apply, hy, map_smul, hx, smul_smul, mul_comm]
  have h3 : (χ (x * y) - χ x * χ y) • v = 0 := by rw [sub_smul, ← h, ← h2, sub_self]
  rcases smul_eq_zero.mp h3 with h4 | h4
  · exact sub_eq_zero.mp h4
  · exact absurd h4 hv0

private lemma weight_apply_pow {Ω V E : Type*} [Field Ω] [AddCommGroup V] [Module Ω V]
    [Group E] (f : E →* Module.End Ω V) {χ : E → Ω} (hχ : weightSpace f χ ≠ ⊥) (x : E) (n : ℕ) :
    χ (x ^ n) = (χ x) ^ n := by
  induction n with
  | zero => simpa using weight_apply_one f hχ
  | succ n ih => rw [pow_succ, weight_apply_mul f hχ, ih, pow_succ]

private lemma weight_apply_pow_eq_one {Ω V E : Type*} [Field Ω] [AddCommGroup V] [Module Ω V]
    [Group E] (f : E →* Module.End Ω V) {χ : E → Ω} (hχ : weightSpace f χ ≠ ⊥) {x : E}
    (hx : x ^ 31 = 1) : (χ x) ^ 31 = 1 := by
  rw [← weight_apply_pow f hχ x 31, hx, weight_apply_one f hχ]

private noncomputable def smulMap {Ω : Type} [Field Ω] (σ : Ω ≃+* Ω) (v : ι → Ω) : ι → Ω :=
  fun i => σ (v i)

omit [Fintype ι] [DecidableEq ι] in
private lemma smulMap_add {Ω : Type} [Field Ω] (σ : Ω ≃+* Ω) (v w : ι → Ω) :
    smulMap σ (v + w) = smulMap σ v + smulMap σ w := by
  funext i; simp [smulMap]

omit [Fintype ι] [DecidableEq ι] in
private lemma smulMap_smul {Ω : Type} [Field Ω] (σ : Ω ≃+* Ω) (c : Ω) (v : ι → Ω) :
    smulMap σ (c • v) = σ c • smulMap σ v := by
  funext i; simp [smulMap]

omit [Fintype ι] [DecidableEq ι] in
private lemma smulMap_zero {Ω : Type} [Field Ω] (σ : Ω ≃+* Ω) :
    smulMap σ (0 : ι → Ω) = 0 := by
  funext i; simp [smulMap]

omit [Fintype ι] [DecidableEq ι] in
private lemma smulMap_injective {Ω : Type} [Field Ω] (σ : Ω ≃+* Ω) :
    Function.Injective (smulMap (ι := ι) σ) := by
  intro v w h
  funext i
  exact σ.injective (congrFun h i)

private noncomputable def semilinMap {Ω : Type} [Field Ω] (A : GL ι Ω) (σ : Ω ≃+* Ω)
    (v : ι → Ω) : ι → Ω :=
  (A : Matrix ι ι Ω) *ᵥ smulMap σ v

private lemma semilinMap_add {Ω : Type} [Field Ω] (A : GL ι Ω) (σ : Ω ≃+* Ω) (v w : ι → Ω) :
    semilinMap A σ (v + w) = semilinMap A σ v + semilinMap A σ w := by
  simp [semilinMap, smulMap_add, Matrix.mulVec_add]

private lemma semilinMap_smul {Ω : Type} [Field Ω] (A : GL ι Ω) (σ : Ω ≃+* Ω) (c : Ω)
    (v : ι → Ω) : semilinMap A σ (c • v) = σ c • semilinMap A σ v := by
  simp [semilinMap, smulMap_smul, Matrix.mulVec_smul]

private lemma semilinMap_zero {Ω : Type} [Field Ω] (A : GL ι Ω) (σ : Ω ≃+* Ω) :
    semilinMap A σ (0 : ι → Ω) = 0 := by
  simp [semilinMap, smulMap_zero]

private lemma semilinMap_injective {Ω : Type} [Field Ω] (A : GL ι Ω) (σ : Ω ≃+* Ω) :
    Function.Injective (semilinMap (ι := ι) A σ) := by
  intro v w h
  have hAinv : (A⁻¹ : Matrix ι ι Ω) * (A : Matrix ι ι Ω) = 1 := by
    simp
  have h1 : (A⁻¹ : Matrix ι ι Ω) *ᵥ semilinMap A σ v =
      (A⁻¹ : Matrix ι ι Ω) *ᵥ semilinMap A σ w := by rw [h]
  rw [semilinMap, semilinMap, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hAinv,
    Matrix.one_mulVec, Matrix.one_mulVec] at h1
  exact smulMap_injective σ h1

private lemma coe_GL_map {Ω : Type} [Field Ω] (f : Ω →+* Ω) (x : GL ι Ω) :
    ((Matrix.GeneralLinearGroup.map f x : GL ι Ω) : Matrix ι ι Ω) =
      (x : Matrix ι ι Ω).map f := by
  ext i j
  simp [Matrix.GeneralLinearGroup.map_apply]

private lemma semilinConjGL_val {Ω : Type} [Field Ω] (A : GL ι Ω) (σ : Ω ≃+* Ω)
    (x : GL ι Ω) :
    ((semilinConjGL A σ x : GL ι Ω) : Matrix ι ι Ω) =
      (A : Matrix ι ι Ω) * (x : Matrix ι ι Ω).map σ.toRingHom * (A⁻¹ : Matrix ι ι Ω) := by
  rw [semilinConjGL, MonoidHom.comp_apply]
  show ((MulAut.conj A (Matrix.GeneralLinearGroup.map σ.toRingHom x) : GL ι Ω) : Matrix ι ι Ω)
      = (A : Matrix ι ι Ω) * (x : Matrix ι ι Ω).map σ.toRingHom * (A⁻¹ : Matrix ι ι Ω)
  rw [MulAut.conj_apply]
  simp only [GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_inv, coe_GL_map]

private lemma semilinConjGL_injective {Ω : Type} [Field Ω] (A : GL ι Ω) (σ : Ω ≃+* Ω) :
    Function.Injective (semilinConjGL (ι := ι) A σ) := by
  intro x y h
  have h1 : Matrix.GeneralLinearGroup.map σ.toRingHom x =
      Matrix.GeneralLinearGroup.map σ.toRingHom y :=
    (MulAut.conj A).injective (by simpa [semilinConjGL] using h)
  have h2 : ((Matrix.GeneralLinearGroup.map σ.toRingHom x : GL ι Ω) : Matrix ι ι Ω) =
      ((Matrix.GeneralLinearGroup.map σ.toRingHom y : GL ι Ω) : Matrix ι ι Ω) := by rw [h1]
  rw [coe_GL_map, coe_GL_map] at h2
  exact Units.ext (Matrix.map_injective σ.injective h2)

private lemma semilinMap_mulVec {Ω : Type} [Field Ω] (A : GL ι Ω) (σ : Ω ≃+* Ω)
    (x : GL ι Ω) (v : ι → Ω) :
    ((semilinConjGL A σ x : GL ι Ω) : Matrix ι ι Ω) *ᵥ semilinMap A σ v =
      semilinMap A σ ((x : Matrix ι ι Ω) *ᵥ v) := by
  have hAinv : (A⁻¹ : Matrix ι ι Ω) * (A : Matrix ι ι Ω) = 1 := by
    simp
  have h2 : (A : Matrix ι ι Ω) * (x : Matrix ι ι Ω).map σ.toRingHom * (A⁻¹ : Matrix ι ι Ω) *
      (A : Matrix ι ι Ω) = (A : Matrix ι ι Ω) * (x : Matrix ι ι Ω).map σ.toRingHom := by
    rw [mul_assoc, hAinv, mul_one]
  rw [semilinConjGL_val]
  rw [semilinMap, semilinMap, Matrix.mulVec_mulVec, h2, ← Matrix.mulVec_mulVec]
  congr 1
  ext i
  show ((x : Matrix ι ι Ω).map σ.toRingHom *ᵥ smulMap σ v) i = smulMap σ ((x : Matrix ι ι Ω) *ᵥ v) i
  exact (RingHom.map_mulVec σ.toRingHom (x : Matrix ι ι Ω) v i).symm

private def restrictHom {G : Type*} [Group G] (θ : G →* G) (E : Subgroup G)
    (hθE : ∀ x ∈ E, θ x ∈ E) : E →* E where
  toFun x := ⟨θ x.1, hθE x.1 x.2⟩
  map_one' := Subtype.ext (map_one θ)
  map_mul' x y := Subtype.ext (map_mul θ x.1 y.1)

private lemma restrictHom_coe {G : Type*} [Group G] (θ : G →* G) (E : Subgroup G)
    (hθE : ∀ x ∈ E, θ x ∈ E) (x : E) :
    ((restrictHom θ E hθE x : E) : G) = θ x := rfl

private lemma restrictHom_iterate_coe {G : Type*} [Group G] (θ : G →* G) (E : Subgroup G)
    (hθE : ∀ x ∈ E, θ x ∈ E) (k : ℕ) (x : E) :
    ((restrictHom θ E hθE)^[k] x : E) = θ^[k] (x : G) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', restrictHom_coe, ih]

private lemma exists_pow_of_pow31_eq_one {Ω : Type} [Field Ω] (τ : Ω ≃+* Ω) :
    ∃ c : ℕ, ∀ ζ : Ω, ζ ^ 31 = 1 → ⇑τ ζ = ζ ^ c := by
  classical
  let f : Ω →* Ω := τ.toMulEquiv.toMonoidHom
  let μ := rootsOfUnity 31 Ω
  let τ' : μ →* μ :=
    { toFun := fun ζ => ⟨Units.map f ζ.1, by
        rw [mem_rootsOfUnity, ← map_pow, ζ.2, map_one]⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  have hτ' : ∀ ζ : μ, (((τ' ζ).1 : Ωˣ) : Ω) = ⇑τ (((ζ.1 : Ωˣ) : Ω)) := by
    intro ζ
    show ((Units.map f ζ.1 : Ωˣ) : Ω) = ⇑τ (((ζ.1 : Ωˣ) : Ω))
    rw [Units.coe_map]
    rfl
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := μ)
  have hgen : ∀ z : μ, z ∈ Subgroup.zpowers g := hg
  have hτg := hgen (τ' g)
  rw [mem_zpowers_iff_mem_range_orderOf] at hτg
  obtain ⟨c, -, hc⟩ := Finset.mem_image.mp hτg
  have hgc : τ' g = g ^ c := hc.symm
  refine ⟨c, fun ζ hζ => ?_⟩
  have hζ0 : ζ ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num)] at hζ
    exact zero_ne_one hζ
  let ζμ : μ := ⟨Units.mk0 ζ hζ0, by
    rw [mem_rootsOfUnity]
    exact Units.ext (by simpa using hζ)⟩
  have hζμ : (((ζμ.1 : Ωˣ)) : Ω) = ζ := rfl
  have hζgen := hgen ζμ
  rw [mem_zpowers_iff_mem_range_orderOf] at hζgen
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hζgen
  have hja : ζμ = g ^ j := hj.symm
  calc ⇑τ ζ = ⇑τ (((ζμ.1 : Ωˣ) : Ω)) := by rw [hζμ]
    _ = (((τ' ζμ).1 : Ωˣ) : Ω) := (hτ' ζμ).symm
    _ = ((((ζμ.1) ^ c : Ωˣ)) : Ω) := by
          rw [hja, map_pow, hgc, ← pow_mul, mul_comm, pow_mul]
          simp
    _ = ((((ζμ.1 : Ωˣ) : Ω))) ^ c := by rw [Units.val_pow_eq_pow_val]
    _ = ζ ^ c := by rw [hζμ]

private lemma factorial_dvd_24 {n : ℕ} (h : n ≤ 4) : Nat.factorial n ∣ 24 := by
  interval_cases n <;> decide

private lemma perm_pow_factorial_eq_one {α : Type*} [Fintype α] [DecidableEq α]
    (e : Equiv.Perm α) : e ^ Nat.factorial (Fintype.card α) = 1 := by
  have h : orderOf e ∣ Nat.factorial (Fintype.card α) := by
    simpa [Fintype.card_perm] using orderOf_dvd_card (x := e)
  exact orderOf_dvd_iff_pow_eq_one.mp h

private lemma perm_pow_48_eq_one_of_involution {α : Type*} [Fintype α] [DecidableEq α]
    (π ι : Equiv.Perm α) (hι : ι * ι = 1) (hcomm : π * ι = ι * π)
    (hfix : ∀ a b : α, ι a = a → ι b = b → a = b)
    (hcard : Fintype.card α ≤ 9) : π ^ 48 = 1 := by
  classical
  have hιa : ∀ a, ι (ι a) = a := by
    intro a
    have h := congrArg (fun e : Equiv.Perm α => e a) hι
    simpa using h
  have hπι : ∀ a, π (ι a) = ι (π a) := by
    intro a
    have h := congrArg (fun e : Equiv.Perm α => e a) hcomm
    simpa using h
  set blk : α → Finset α := fun a => {a, ι a} with hblk
  have hmem : ∀ a, a ∈ blk a := fun a => by simp [hblk]
  have hblk_ι : ∀ a, blk (ι a) = blk a := by
    intro a
    simp only [hblk, hιa a]
    exact (Finset.pair_comm a (ι a)).symm
  have hblk_eq : ∀ a b, a ∈ blk b → blk a = blk b := by
    intro a b hab
    simp only [hblk, Finset.mem_insert, Finset.mem_singleton] at hab
    rcases hab with rfl | rfl
    · rfl
    · exact hblk_ι b
  have hcard_two : ∀ a, ι a ≠ a → (blk a).card = 2 := by
    intro a ha
    simp only [hblk]
    rw [Finset.card_insert_of_notMem (by simpa [eq_comm] using ha)]
    simp
  have hcard_le : ∀ a, (blk a).card ≤ 2 := by
    intro a
    rcases eq_or_ne (ι a) a with h | h
    · simp only [hblk, h]
      simp
    · rw [hcard_two a h]
  set B : Finset (Finset α) := Finset.univ.image blk with hB
  have hblk_mem_B : ∀ a, blk a ∈ B := fun a =>
    Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  set P2 : Finset (Finset α) := B.filter (fun b => b.card = 2) with hP2
  have hmemP2 : ∀ b, b ∈ P2 ↔ b ∈ B ∧ b.card = 2 := by
    intro b
    simp [hP2]
  have hdisj : (P2 : Set (Finset α)).PairwiseDisjoint id := by
    intro b hb b' hb' hne
    obtain ⟨hbB, -⟩ := (hmemP2 b).mp hb
    obtain ⟨hb'B, -⟩ := (hmemP2 b').mp hb'
    obtain ⟨c, -, hc⟩ := Finset.mem_image.mp hbB
    obtain ⟨d, -, hd⟩ := Finset.mem_image.mp hb'B
    change Disjoint b b'
    rw [Finset.disjoint_left]
    intro a hab hab'
    rw [← hc] at hab
    rw [← hd] at hab'
    have h1 : b = blk a := hc.symm.trans (hblk_eq a c hab).symm
    have h2 : b' = blk a := hd.symm.trans (hblk_eq a d hab').symm
    exact hne (h1.trans h2.symm)
  have hP2card : P2.card ≤ 4 := by
    have hsum : (P2.biUnion id).card = ∑ b ∈ P2, b.card := Finset.card_biUnion hdisj
    have h2 : (P2.biUnion id).card = 2 * P2.card := by
      rw [hsum]
      have hb : ∀ b ∈ P2, b.card = 2 := fun b hb => ((hmemP2 b).mp hb).2
      rw [Finset.sum_congr rfl hb, Finset.sum_const, smul_eq_mul, mul_comm]
    have hle : (P2.biUnion id).card ≤ Fintype.card α := by
      simpa using Finset.card_le_card (Finset.subset_univ _)
    omega
  have hblk_π : ∀ a, blk (π a) = (blk a).image π := by
    intro a
    simp only [hblk]
    rw [← hπι a]
    simp
  have hP2map : ∀ b ∈ P2, b.image π ∈ P2 := by
    intro b hb
    obtain ⟨hbB, hbc⟩ := (hmemP2 b).mp hb
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hbB
    have hmem' : (blk a).image π ∈ B := by
      rw [← hblk_π a]
      exact hblk_mem_B (π a)
    have hcard' : ((blk a).image π).card = 2 := by
      rw [Finset.card_image_of_injective _ π.injective]
      exact hbc
    exact (hmemP2 _).mpr ⟨hmem', hcard'⟩
  let φ : {b // b ∈ P2} → {b // b ∈ P2} := fun b => ⟨b.1.image π, hP2map b.1 b.2⟩
  have hφinj : Function.Injective φ := by
    intro b b' h
    have h' : b.1.image π = b'.1.image π := congrArg Subtype.val h
    have h2 := congrArg (fun s : Finset α => s.image π.symm) h'
    have h3 : b.1 = b'.1 := by
      simpa [Finset.image_image] using h2
    exact Subtype.ext h3
  let eφ : Equiv.Perm {b // b ∈ P2} :=
    Equiv.ofBijective φ ⟨hφinj, Finite.injective_iff_surjective.mp hφinj⟩
  have hφ24 : eφ ^ 24 = 1 := by
    have h1 : eφ ^ Nat.factorial (Fintype.card {b // b ∈ P2}) = 1 :=
      perm_pow_factorial_eq_one eφ
    have hc : Fintype.card {b // b ∈ P2} = P2.card := Fintype.card_coe P2
    have h2 : orderOf eφ ∣ Nat.factorial (Fintype.card {b // b ∈ P2}) :=
      orderOf_dvd_iff_pow_eq_one.mpr h1
    rw [hc] at h2
    exact orderOf_dvd_iff_pow_eq_one.mp (dvd_trans h2 (factorial_dvd_24 hP2card))
  have hφ_iter : ∀ (k : ℕ) (b : {b // b ∈ P2}), (φ^[k] b).1 = (Finset.image π)^[k] b.1 := by
    intro k
    induction k with
    | zero => intro b; simp
    | succ k ih =>
      intro b
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      show (φ^[k] b).1.image π = Finset.image π ((Finset.image π)^[k] b.1)
      rw [ih b]
  have hblk_fixed : ∀ b ∈ P2, (Finset.image π)^[24] b = b := by
    intro b hb
    have h' : φ^[24] (⟨b, hb⟩ : {x // x ∈ P2}) = ⟨b, hb⟩ :=
      congrArg (fun e : Equiv.Perm {x // x ∈ P2} => e ⟨b, hb⟩) hφ24
    have h2 := hφ_iter 24 (⟨b, hb⟩ : {x // x ∈ P2})
    rw [← h2, h']
  have hblk_iter : ∀ (k : ℕ) (a : α), blk (π^[k] a) = (Finset.image π)^[k] (blk a) := by
    intro k
    induction k with
    | zero => intro a; simp
    | succ k ih =>
      intro a
      rw [Function.iterate_succ_apply', hblk_π, ih, Function.iterate_succ_apply']
  have hmain : ∀ a : α, π^[24] a = a ∨ π^[24] a = ι a := by
    intro a
    by_cases h2 : (blk a).card = 2
    · have hb : blk a ∈ P2 := (hmemP2 _).mpr ⟨hblk_mem_B a, h2⟩
      have h1 : blk (π^[24] a) = blk a := by
        rw [hblk_iter, hblk_fixed (blk a) hb]
      have hm : π^[24] a ∈ blk a := by rw [← h1]; exact hmem _
      simpa only [hblk, Finset.mem_insert, Finset.mem_singleton] using hm
    · have h1 : (blk a).card = 1 := by
        have hle := hcard_le a
        have hpos : 0 < (blk a).card := Finset.card_pos.mpr ⟨a, hmem a⟩
        omega
      have hia : ι a = a := by
        by_contra hne
        rw [hcard_two a hne] at h1
        exact absurd h1 (by norm_num)
      have hpa : π a = a := by
        have hfix' : ι (π a) = π a := by rw [← hπι a, hia]
        exact hfix (π a) a hfix' hia
      have hiter : ∀ k : ℕ, π^[k] a = a := by
        intro k
        induction k with
        | zero => rfl
        | succ k ih => rw [Function.iterate_succ_apply', ih, hpa]
      exact Or.inl (hiter 24)
  have hπk_ι : ∀ (k : ℕ) (a : α), π^[k] (ι a) = ι (π^[k] a) := by
    intro k
    induction k with
    | zero => intro a; rfl
    | succ k ih =>
      intro a
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', hπι]
  refine Equiv.ext fun a => ?_
  have h48 : π^[48] a = a := by
    rcases hmain a with h | h
    · rw [show (48 : ℕ) = 24 + 24 from rfl, Function.iterate_add_apply, h, h]
    · rw [show (48 : ℕ) = 24 + 24 from rfl, Function.iterate_add_apply, h, hπk_ι 24 a, h,
        hιa a]
  exact h48

private theorem weylFive_weights_algClosed {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (h31 : (31 : Ω) ≠ 0) (A : GL ι Ω) (σ : Ω ≃+* Ω) (E : Subgroup (GL ι Ω)) [Finite E]
    (hE : ∀ x ∈ E, x ^ 31 = 1) (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hθE : ∀ x ∈ E, semilinConjGL A σ x ∈ E)
    (hdim : Fintype.card ι ≤ 4 ∨ (Fintype.card ι ≤ 9 ∧ ∃ J : Matrix ι ι Ω, IsUnit J.det ∧
      ∀ x ∈ E, (x : Matrix ι ι Ω)ᵀ * J * x = J)) :
    ∃ c : ℕ, ∀ x ∈ E, (semilinConjGL A σ)^[48] x = x ^ c := by
  classical
  have hpowE : ∀ x : E, x ^ 31 = 1 := fun x => by
    apply Subtype.ext
    simpa using hE x.1 x.2
  let f : E →* Module.End Ω (ι → Ω) := glEndSub E
  have hpow : ∀ x : E, f x ^ 31 = 1 := by
    intro x
    rw [← map_pow, hpowE x, map_one]
  have hcomm : ∀ x y : E, Commute (f x) (f y) := by
    intro x y
    show f x * f y = f y * f x
    rw [← map_mul, ← map_mul, show x * y = y * x from Subtype.ext (hEc x.1 x.2 y.1 y.2)]
  have hss : ∀ x : E, (f x).IsSemisimple := fun x => isSemisimple_of_pow_eq_one h31 _ (hpow x)
  have hmaxeq : ∀ x : E, (f x).maxGenEigenspace = (f x).eigenspace := fun x =>
    funext fun μ => (hss x).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ
  have hspanmax : ⨆ χ : E → Ω, ⨅ x : E, (f x).maxGenEigenspace (χ x) = ⊤ := by
    refine Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      (f := fun x : E => f x) (fun x y _ => hcomm x y) (fun x => ?_)
    have h1 : ⨆ μ : Ω, (f x).eigenspace μ = ⊤ := (hss x).iSup_eigenspace_eq_top
    simpa only [hmaxeq x] using h1
  have hfun : (fun χ : E → Ω => weightSpace f χ) =
      (fun χ : E → Ω => ⨅ x : E, (f x).maxGenEigenspace (χ x)) := by
    funext χ
    exact iInf_congr fun x => (congrFun (hmaxeq x) (χ x)).symm
  have hspan : ⨆ χ : E → Ω, weightSpace f χ = ⊤ := by
    rw [hfun]
    exact hspanmax
  have hmaps : ∀ i j : E, ∀ μ : Ω,
      Set.MapsTo (f i) ((f j).maxGenEigenspace μ) ((f j).maxGenEigenspace μ) :=
    fun i j μ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) μ
  have hindmax : iSupIndep (fun χ : E → Ω => ⨅ x : E, (f x).maxGenEigenspace (χ x)) :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (f := fun x : E => f x) hmaps
  have hind : iSupIndep (weightSpace f) := by
    change iSupIndep (fun χ : E → Ω => weightSpace f χ)
    rw [hfun]
    exact hindmax
  let X := {χ : E → Ω // weightSpace f χ ≠ ⊥}
  let : Fintype X := hind.fintypeNeBotOfFiniteDimensional
  have hXcard : Fintype.card X ≤ Fintype.card ι := by
    have h1 : Fintype.card X ≤ Module.finrank Ω (ι → Ω) := hind.subtype_ne_bot_le_finrank
    rwa [Module.finrank_fintype_fun_eq_card] at h1
  have hspanX : ⨆ χ : X, weightSpace f χ.1 = ⊤ := by
    rw [← hspan]
    refine le_antisymm (iSup_le fun χ => le_iSup (fun χ : E → Ω => weightSpace f χ) χ.1)
      (iSup_le fun χ => ?_)
    by_cases h : weightSpace f χ ≠ ⊥
    · exact le_iSup (fun χ : X => weightSpace f χ.1) ⟨χ, h⟩
    · rw [not_not.mp h]; exact bot_le
  have hchar_one : ∀ χ : X, χ.1 1 = 1 := fun χ => weight_apply_one f χ.2
  have hchar_mul : ∀ (χ : X) (x y : E), χ.1 (x * y) = χ.1 x * χ.1 y :=
    fun χ => weight_apply_mul f χ.2
  have hchar_pow : ∀ (χ : X) (x : E), (χ.1 x) ^ 31 = 1 :=
    fun χ x => weight_apply_pow_eq_one f χ.2 (hpowE x)
  let θ : GL ι Ω →* GL ι Ω := semilinConjGL A σ
  have hθ_inj : Function.Injective θ := semilinConjGL_injective A σ
  let θE : E →* E := restrictHom θ E hθE
  have hθE_coe : ∀ x : E, ((θE x : E) : GL ι Ω) = θ x := fun x => rfl
  have hθE_inj : Function.Injective θE := by
    intro x y h
    refine Subtype.ext (hθ_inj ?_)
    rw [← hθE_coe x, ← hθE_coe y, h]
  let e : E ≃* E := MulEquiv.ofBijective θE ⟨hθE_inj, Finite.injective_iff_surjective.mp hθE_inj⟩
  have he_coe : ∀ x : E, ((e x : E) : GL ι Ω) = θ x := fun x => hθE_coe x
  let π : (E → Ω) → (E → Ω) := fun χ y => σ (χ (e.symm y))
  let T : (ι → Ω) → (ι → Ω) := semilinMap A σ
  have hT_add : ∀ v w : ι → Ω, T (v + w) = T v + T w := fun v w => semilinMap_add A σ v w
  have hT_zero : T 0 = 0 := semilinMap_zero A σ
  have hT_smul : ∀ (c : Ω) (v : ι → Ω), T (c • v) = σ c • T v :=
    fun c v => semilinMap_smul A σ c v
  have hT_inj : Function.Injective T := semilinMap_injective A σ
  have hAinv : (A : Matrix ι ι Ω) * (A⁻¹ : Matrix ι ι Ω) = 1 := by
    simp
  have hT_surj : Function.Surjective T := by
    intro w
    refine ⟨fun i => σ.symm (((A⁻¹ : Matrix ι ι Ω) *ᵥ w) i), ?_⟩
    show (A : Matrix ι ι Ω) *ᵥ smulMap σ (fun i => σ.symm ((A⁻¹ *ᵥ w) i)) = w
    have h1 : smulMap σ (fun i => σ.symm ((A⁻¹ *ᵥ w) i)) = (A⁻¹ : Matrix ι ι Ω) *ᵥ w := by
      funext i
      exact σ.apply_symm_apply _
    rw [h1, Matrix.mulVec_mulVec, hAinv, Matrix.one_mulVec]
  have hT_iter_add : ∀ (k : ℕ) (v w : ι → Ω), T^[k] (v + w) = T^[k] v + T^[k] w := by
    intro k
    induction k with
    | zero => intro v w; rfl
    | succ k ih =>
      intro v w
      have h1 : T^[Nat.succ k] (v + w) = T (T^[k] (v + w)) :=
        Function.iterate_succ_apply' T k (v + w)
      have h2 : T^[Nat.succ k] v = T (T^[k] v) := Function.iterate_succ_apply' T k v
      have h3 : T^[Nat.succ k] w = T (T^[k] w) := Function.iterate_succ_apply' T k w
      rw [h1, h2, h3, ih, hT_add]
  have hT_iter_zero : ∀ k : ℕ, T^[k] (0 : ι → Ω) = 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, hT_zero]
  have hT_iter_smul : ∀ (k : ℕ) (c : Ω) (v : ι → Ω), T^[k] (c • v) = (σ^[k] c) • T^[k] v := by
    intro k
    induction k with
    | zero => intro c v; rfl
    | succ k ih =>
      intro c v
      have h1 : T^[Nat.succ k] (c • v) = T (T^[k] (c • v)) :=
        Function.iterate_succ_apply' T k (c • v)
      have h2 : (⇑σ)^[Nat.succ k] c = σ ((⇑σ)^[k] c) := Function.iterate_succ_apply' (⇑σ) k c
      have h3 : T^[Nat.succ k] v = T (T^[k] v) := Function.iterate_succ_apply' T k v
      rw [h1, h2, h3, ih, hT_smul]
  have hT_comm : ∀ (x : E) (v : ι → Ω), T (f x v) = f (θE x) (T v) := by
    intro x v
    show semilinMap A σ (((x : GL ι Ω) : Matrix ι ι Ω) *ᵥ v) =
      ((θ x : GL ι Ω) : Matrix ι ι Ω) *ᵥ semilinMap A σ v
    exact (semilinMap_mulVec A σ (x : GL ι Ω) v).symm
  have hT_iter_comm : ∀ (k : ℕ) (x : E) (v : ι → Ω), T^[k] (f x v) = f (θE^[k] x) (T^[k] v) := by
    intro k
    induction k with
    | zero => intro x v; rfl
    | succ k ih =>
      intro x v
      have h1 : T^[Nat.succ k] (f x v) = T (T^[k] (f x v)) :=
        Function.iterate_succ_apply' T k (f x v)
      have h2 : (⇑θE)^[Nat.succ k] x = θE ((⇑θE)^[k] x) :=
        Function.iterate_succ_apply' (⇑θE) k x
      have h3 : T^[Nat.succ k] v = T (T^[k] v) := Function.iterate_succ_apply' T k v
      rw [h1, h2, h3, ih, hT_comm]
  have hT_mem_W : ∀ (χ : E → Ω) (v : ι → Ω), v ∈ weightSpace f χ → T v ∈ weightSpace f (π χ) := by
    intro χ v hv
    rw [mem_weightSpace] at hv ⊢
    intro y
    have hy : θE (e.symm y) = y := by
      show e (e.symm y) = y
      exact e.apply_symm_apply y
    show f y (T v) = π χ y • T v
    calc f y (T v) = f (θE (e.symm y)) (T v) := by rw [hy]
      _ = T (f (e.symm y) v) := (hT_comm (e.symm y) v).symm
      _ = T (χ (e.symm y) • v) := by rw [hv]
      _ = σ (χ (e.symm y)) • T v := hT_smul _ _
  have hT_iter_mem : ∀ (k : ℕ) (χ : E → Ω) (v : ι → Ω), v ∈ weightSpace f χ →
      T^[k] v ∈ weightSpace f (π^[k] χ) := by
    intro k
    induction k with
    | zero => intro χ v hv; simpa using hv
    | succ k ih =>
      intro χ v hv
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact hT_mem_W (π^[k] χ) (T^[k] v) (ih χ v hv)
  have hπ_mem : ∀ χ : X, weightSpace f (π χ.1) ≠ ⊥ := by
    intro χ hbot
    apply χ.2
    rw [eq_bot_iff]
    intro v hv
    have hTv : T v ∈ weightSpace f (π χ.1) := hT_mem_W χ.1 v hv
    rw [hbot] at hTv
    have h0 : T v = T 0 := by rw [hT_zero]; exact hTv
    exact hT_inj h0
  let πX : X → X := fun χ => ⟨π χ.1, hπ_mem χ⟩
  have hπX_coe : ∀ χ : X, (πX χ).1 = π χ.1 := fun χ => rfl
  have hπ_inj : Function.Injective π := by
    intro χ χ' h
    funext y
    have h' : σ (χ (e.symm (e y))) = σ (χ' (e.symm (e y))) := by
      have := congrFun h (e y)
      simpa [π] using this
    simpa using σ.injective h'
  have hπX_inj : Function.Injective πX := by
    intro χ χ' h
    exact Subtype.ext (hπ_inj (congrArg Subtype.val h))
  let eπ : Equiv.Perm X :=
    Equiv.ofBijective πX ⟨hπX_inj, Finite.injective_iff_surjective.mp hπX_inj⟩
  have heπ_coe : ∀ χ : X, ((eπ χ : X) : E → Ω) = π χ.1 := fun χ => rfl
  have heπ_iter : ∀ (k : ℕ) (χ : X), ((eπ^[k] χ : X) : E → Ω) = π^[k] χ.1 := by
    intro k
    induction k with
    | zero => intro χ; rfl
    | succ k ih =>
      intro χ
      have h1 : eπ^[Nat.succ k] χ = eπ (eπ^[k] χ) := Function.iterate_succ_apply' (⇑eπ) k χ
      have h2 : π^[Nat.succ k] χ.1 = π (π^[k] χ.1) := Function.iterate_succ_apply' π k χ.1
      rw [h1, h2, heπ_coe, ih]
  have hπ48 : ∀ χ : X, π^[48] χ.1 = χ.1 := by
    have h48 : eπ ^ 48 = 1 := by
      rcases hdim with h4 | ⟨h9, J, hJdet, hJinv⟩
      · have hcard : Fintype.card X ≤ 4 := le_trans hXcard h4
        have h24 : eπ ^ 24 = 1 := by
          have h1 := perm_pow_factorial_eq_one eπ
          have hfac : Nat.factorial (Fintype.card X) ∣ 24 := factorial_dvd_24 hcard
          exact orderOf_dvd_iff_pow_eq_one.mp
            (dvd_trans (orderOf_dvd_iff_pow_eq_one.mpr h1) hfac)
        rw [show (48 : ℕ) = 24 + 24 from rfl, pow_add, h24, one_mul]
      ·
        let χinv : (E → Ω) → (E → Ω) := fun χ y => (χ y)⁻¹
        have hπ_inv : ∀ χ : E → Ω, π (χinv χ) = χinv (π χ) := by
          intro χ
          funext y
          show σ ((χ (e.symm y))⁻¹) = (σ (χ (e.symm y)))⁻¹
          exact map_inv₀ σ _
        have hdot : ∀ (M : Matrix ι ι Ω) (a b : ι → Ω), (M *ᵥ a) ⬝ᵥ b = a ⬝ᵥ (Mᵀ *ᵥ b) := by
          intro M a b
          rw [Matrix.dotProduct_mulVec a Mᵀ b, Matrix.vecMul_transpose]
        have hinv_mem : ∀ χ : X, weightSpace f (χinv χ.1) ≠ ⊥ := by
          intro χ
          obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot χ.2
          have hne : ∃ w : ι → Ω, v ⬝ᵥ (J *ᵥ w) ≠ 0 := by
            obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
              by_contra h
              push Not at h
              exact hv0 (funext h)
            have hJsurj : Function.Surjective J.mulVec := by
              rw [Matrix.mulVec_surjective_iff_isUnit]
              rwa [Matrix.isUnit_iff_isUnit_det]
            obtain ⟨w, hw⟩ := hJsurj (Pi.single i 1)
            refine ⟨w, ?_⟩
            rw [hw, dotProduct_single_one]
            simpa using hi
          obtain ⟨w, hw⟩ := hne
          have hdecomp : ∃ (ψ : X) (w' : ι → Ω),
              w' ∈ weightSpace f ψ.1 ∧ v ⬝ᵥ (J *ᵥ w') ≠ 0 := by
            have hkey : ∀ u : ι → Ω, u ∈ ⨆ ψ : X, weightSpace f ψ.1 →
                (v ⬝ᵥ (J *ᵥ u) ≠ 0 → ∃ (ψ : X) (w' : ι → Ω),
                  w' ∈ weightSpace f ψ.1 ∧ v ⬝ᵥ (J *ᵥ w') ≠ 0) := by
              intro u hu
              refine Submodule.iSup_induction (motive := fun x : ι → Ω =>
                v ⬝ᵥ (J *ᵥ x) ≠ 0 → ∃ (ψ : X) (w' : ι → Ω),
                  w' ∈ weightSpace f ψ.1 ∧ v ⬝ᵥ (J *ᵥ w') ≠ 0)
                (p := fun ψ : X => weightSpace f ψ.1) hu ?_ ?_ ?_
              · intro ψ u' hu' hne
                exact ⟨ψ, u', hu', hne⟩
              · intro h
                exact absurd h (by simp)
              · intro a b ha hb hne
                by_cases h : v ⬝ᵥ (J *ᵥ a) = 0
                · refine hb (fun hb0 => hne ?_)
                  rw [Matrix.mulVec_add, dotProduct_add, h, hb0, add_zero]
                · exact ha h
            exact hkey w (by rw [hspanX]; trivial) hw
          obtain ⟨ψ, w', hw', hne'⟩ := hdecomp
          have hform : ∀ x : E, χ.1 x * ψ.1 x = 1 := by
            intro x
            have hvx : ((x : GL ι Ω) : Matrix ι ι Ω) *ᵥ v = χ.1 x • v :=
              (mem_weightSpace f χ.1 v).mp hv x
            have hwx : ((x : GL ι Ω) : Matrix ι ι Ω) *ᵥ w' = ψ.1 x • w' :=
              (mem_weightSpace f ψ.1 w').mp hw' x
            have hkey : (χ.1 x * ψ.1 x) * (v ⬝ᵥ (J *ᵥ w')) = v ⬝ᵥ (J *ᵥ w') := by
              calc (χ.1 x * ψ.1 x) * (v ⬝ᵥ (J *ᵥ w'))
                  = (χ.1 x • v) ⬝ᵥ (J *ᵥ (ψ.1 x • w')) := by
                      rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
                        smul_smul, smul_eq_mul]
                _ = (((x : GL ι Ω) : Matrix ι ι Ω) *ᵥ v) ⬝ᵥ
                      (J *ᵥ (((x : GL ι Ω) : Matrix ι ι Ω) *ᵥ w')) := by rw [← hvx, ← hwx]
                _ = v ⬝ᵥ ((((x : GL ι Ω) : Matrix ι ι Ω))ᵀ *ᵥ
                      (J *ᵥ (((x : GL ι Ω) : Matrix ι ι Ω) *ᵥ w'))) := hdot _ _ _
                _ = v ⬝ᵥ (((((x : GL ι Ω) : Matrix ι ι Ω))ᵀ * J *
                      ((x : GL ι Ω) : Matrix ι ι Ω)) *ᵥ w') := by
                      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
                _ = v ⬝ᵥ (J *ᵥ w') := by rw [hJinv x x.2]
            have h2 : (χ.1 x * ψ.1 x) * (v ⬝ᵥ (J *ᵥ w')) =
                1 * (v ⬝ᵥ (J *ᵥ w')) := by rw [one_mul]; exact hkey
            exact mul_right_cancel₀ hne' h2
          have hχψ : χinv χ.1 = ψ.1 := by
            funext y
            show (χ.1 y)⁻¹ = ψ.1 y
            exact inv_eq_of_mul_eq_one_right (hform y)
          rw [hχψ]
          exact ψ.2
        let ιπ : X → X := fun χ => ⟨χinv χ.1, hinv_mem χ⟩
        have hιπ_val : ∀ χ : X, (ιπ χ).1 = χinv χ.1 := fun χ => rfl
        have hιπ_invol : Function.Involutive ιπ := by
          intro χ
          apply Subtype.ext
          funext y
          show ((χinv χ.1 y)⁻¹) = χ.1 y
          simp [χinv]
        have hιπ_inj : Function.Injective ιπ := hιπ_invol.injective
        let eι : Equiv.Perm X :=
          Equiv.ofBijective ιπ ⟨hιπ_inj, Finite.injective_iff_surjective.mp hιπ_inj⟩
        have heι_coe : ∀ χ : X, ((eι χ : X) : E → Ω) = χinv χ.1 := fun χ => rfl
        have hι : eι * eι = 1 := by
          apply Equiv.ext
          intro χ
          show eι (eι χ) = χ
          exact hιπ_invol χ
        have hcomm : eπ * eι = eι * eπ := by
          apply Equiv.ext
          intro χ
          apply Subtype.ext
          show (eπ (eι χ) : X).1 = (eι (eπ χ) : X).1
          show π (χinv χ.1) = χinv (π χ.1)
          exact hπ_inv χ.1
        have hfix : ∀ a b : X, eι a = a → eι b = b → a = b := by
          intro a b ha hb
          have hfix1 : ∀ c : X, eι c = c → c.1 = 1 := by
            intro c hc
            funext y
            have hy : (c.1 y)⁻¹ = c.1 y := by
              have h := congrFun (congrArg Subtype.val hc) y
              rwa [show (eι c).1 y = (c.1 y)⁻¹ from rfl] at h
            have hp : (c.1 y) ^ 31 = 1 := hchar_pow c y
            have hne : c.1 y ≠ 0 := by
              intro h0
              rw [h0, zero_pow (by norm_num)] at hp
              exact zero_ne_one hp
            have hc2 : c.1 y * c.1 y = 1 := by
              nth_rewrite 2 [← hy]
              exact mul_inv_cancel₀ hne
            have h31 : (c.1 y) ^ 31 = c.1 y := by
              have h2 : (c.1 y) ^ 31 = (c.1 y) ^ (2 * 15 + 1) := by norm_num
              rw [h2, pow_succ, pow_mul, pow_two, hc2, one_pow, one_mul]
            rw [h31] at hp
            exact hp
          exact Subtype.ext ((hfix1 a ha).trans (hfix1 b hb).symm)
        exact perm_pow_48_eq_one_of_involution eπ eι hι hcomm hfix (le_trans hXcard h9)
    intro χ
    have h : eπ^[48] χ = χ := by
      have h1 := congrArg (fun e : Equiv.Perm X => e χ) h48
      exact h1
    calc π^[48] χ.1 = ((eπ^[48] χ : X) : E → Ω) := (heπ_iter 48 χ).symm
      _ = χ.1 := by rw [h]
  obtain ⟨c₁, hc₁⟩ := exists_pow_of_pow31_eq_one σ
  have hc_iter : ∀ (k : ℕ) (ζ : Ω), ζ ^ 31 = 1 → σ^[k] ζ = ζ ^ (c₁ ^ k) := by
    intro k
    induction k with
    | zero =>
      intro ζ hζ
      rw [Function.iterate_zero_apply, pow_zero, pow_one]
    | succ k ih =>
      intro ζ hζ
      rw [Function.iterate_succ_apply', ih ζ hζ, map_pow, hc₁ ζ hζ, ← pow_mul, ← pow_succ']
  let c : ℕ := c₁ ^ 48
  refine ⟨c, ?_⟩
  obtain ⟨U, hU⟩ : ∃ U : (ι → Ω) → (ι → Ω), U = T^[48] := ⟨T^[48], rfl⟩
  have hU_add : ∀ a b : ι → Ω, U (a + b) = U a + U b := by
    intro a b
    rw [hU]
    exact hT_iter_add 48 a b
  have hU_zero : U 0 = 0 := by rw [hU]; exact hT_iter_zero 48
  have hU_smul : ∀ (d : Ω) (v : ι → Ω), U (d • v) = (σ^[48] d) • U v := by
    intro d v
    rw [hU]
    exact hT_iter_smul 48 d v
  have hU_comm : ∀ (x : E) (v : ι → Ω), U (f x v) = f (θE^[48] x) (U v) := by
    intro x v
    rw [hU]
    exact hT_iter_comm 48 x v
  have hU_mem : ∀ (χ : X) (v : ι → Ω), v ∈ weightSpace f χ.1 → U v ∈ weightSpace f χ.1 := by
    intro χ v hv
    rw [hU]
    have h1 := hT_iter_mem 48 χ.1 v hv
    rwa [hπ48 χ] at h1
  have hU_surj : Function.Surjective U := by
    rw [hU]
    exact Function.Surjective.iterate hT_surj 48
  have hfin : ∀ x : E, f (θE^[48] x) = f (x ^ c) := by
    intro x
    refine LinearMap.ext fun v => ?_
    obtain ⟨w, hw⟩ := hU_surj v
    rw [← hw]
    have hkey : ∀ w : ι → Ω, w ∈ ⨆ χ : X, weightSpace f χ.1 →
        f (θE^[48] x) (U w) = f (x ^ c) (U w) := by
      intro w hw
      refine Submodule.iSup_induction (motive := fun z : ι → Ω =>
        f (θE^[48] x) (U z) = f (x ^ c) (U z))
        (p := fun χ : X => weightSpace f χ.1) hw ?_ ?_ ?_
      · intro χ u hu
        have hTu : U u ∈ weightSpace f χ.1 := hU_mem χ u hu
        have h2 : f (θE^[48] x) (U u) = U (f x u) := (hU_comm x u).symm
        have h3 : f x u = χ.1 x • u := (mem_weightSpace f χ.1 u).mp hu x
        have h4 : U (χ.1 x • u) = (σ^[48] (χ.1 x)) • U u := hU_smul (χ.1 x) u
        calc f (θE^[48] x) (U u) = U (f x u) := h2
          _ = U (χ.1 x • u) := by rw [h3]
          _ = (σ^[48] (χ.1 x)) • U u := h4
          _ = (χ.1 x) ^ c • U u := by rw [hc_iter 48 (χ.1 x) (hchar_pow χ x)]
          _ = χ.1 (x ^ c) • U u := by rw [weight_apply_pow f χ.2 x c]
          _ = f (x ^ c) (U u) := ((mem_weightSpace f χ.1 (U u)).mp hTu (x ^ c)).symm
      · rw [hU_zero, map_zero, map_zero]
      · intro a b ha hb
        rw [hU_add, map_add, map_add, ha, hb]
    exact hkey w (by rw [hspanX]; trivial)
  intro x hx
  have h1 : f (θE^[48] ⟨x, hx⟩) = f (⟨x, hx⟩ ^ c) := hfin ⟨x, hx⟩
  have h2 : θE^[48] ⟨x, hx⟩ = ⟨x, hx⟩ ^ c := glEndSub_injective E h1
  have h3 := restrictHom_iterate_coe θ E hθE 48 ⟨x, hx⟩
  rw [← h3, h2]
  exact Subgroup.coe_pow ..

private lemma map_semilinConjGL {Ω : Type} [Field Ω] (f : K →+* Ω) (σ : K ≃+* K)
    (σ' : Ω ≃+* Ω) (hσ : ∀ k : K, σ' (f k) = f (σ k)) (A : GL ι K) (x : GL ι K) :
    Matrix.GeneralLinearGroup.map f (semilinConjGL A σ x) =
      semilinConjGL (Matrix.GeneralLinearGroup.map f A) σ' (Matrix.GeneralLinearGroup.map f x) := by
  have hstep : semilinConjGL A σ x =
      A * Matrix.GeneralLinearGroup.map σ.toRingHom x * A⁻¹ := by
    rw [semilinConjGL, MonoidHom.comp_apply]
    show ((MulAut.conj A) (Matrix.GeneralLinearGroup.map σ.toRingHom x) : GL ι K) = _
    rw [MulAut.conj_apply]
  have hstep' : semilinConjGL (Matrix.GeneralLinearGroup.map f A) σ'
      (Matrix.GeneralLinearGroup.map f x) =
      Matrix.GeneralLinearGroup.map f A *
        Matrix.GeneralLinearGroup.map σ'.toRingHom (Matrix.GeneralLinearGroup.map f x) *
        (Matrix.GeneralLinearGroup.map f A)⁻¹ := by
    rw [semilinConjGL, MonoidHom.comp_apply]
    show ((MulAut.conj (Matrix.GeneralLinearGroup.map f A))
      (Matrix.GeneralLinearGroup.map σ'.toRingHom (Matrix.GeneralLinearGroup.map f x)) : GL ι Ω) = _
    rw [MulAut.conj_apply]
  have hcomp : f.comp σ.toRingHom = σ'.toRingHom.comp f := RingHom.ext fun k => (hσ k).symm
  have hkey : Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.map σ.toRingHom x) =
      Matrix.GeneralLinearGroup.map σ'.toRingHom (Matrix.GeneralLinearGroup.map f x) := by
    rw [← Matrix.GeneralLinearGroup.map_comp_apply (f := σ.toRingHom) (g := f),
      ← Matrix.GeneralLinearGroup.map_comp (f := σ.toRingHom) (g := f), hcomp,
      Matrix.GeneralLinearGroup.map_comp (f := f) (g := σ'.toRingHom),
      Matrix.GeneralLinearGroup.map_comp_apply (f := f) (g := σ'.toRingHom)]
  rw [hstep, hstep']
  rw [map_mul, map_mul, map_inv, hkey]

theorem weylFive_weights [Finite K] (hK : ringChar K ≠ 31) (A : GL ι K) (σ : K ≃+* K)
    (E : Subgroup (GL ι K)) (hE : ∀ x ∈ E, x ^ 31 = 1) (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hθE : ∀ x ∈ E, semilinConjGL A σ x ∈ E)
    (hdim : Fintype.card ι ≤ 4 ∨ (Fintype.card ι ≤ 9 ∧ ∃ J : Matrix ι ι K, IsUnit J.det ∧
      ∀ x ∈ E, (x : Matrix ι ι K)ᵀ * J * x = J)) :
    ∃ c : ℕ, ∀ x ∈ E, (semilinConjGL A σ)^[48] x = x ^ c := by
  classical
  let φ : GL ι K →* GL ι (AlgebraicClosure K) :=
    Matrix.GeneralLinearGroup.map (algebraMap K (AlgebraicClosure K))
  have hφ_inj : Function.Injective φ := by
    intro x y h
    refine Units.ext (Matrix.map_injective
      (FaithfulSMul.algebraMap_injective (R := K) (A := AlgebraicClosure K)) ?_)
    exact congrArg (fun g : GL ι (AlgebraicClosure K) => (g : Matrix ι ι (AlgebraicClosure K))) h
  let σ' : AlgebraicClosure K ≃+* AlgebraicClosure K :=
    IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K) σ
  have hσ' : ∀ k : K, σ' (algebraMap K (AlgebraicClosure K) k) =
      algebraMap K (AlgebraicClosure K) (σ k) := fun k =>
    IsAlgClosure.equivOfEquiv_algebraMap (AlgebraicClosure K) (AlgebraicClosure K) σ k
  have h31 : (31 : AlgebraicClosure K) ≠ 0 := by
    have : CharP K (ringChar K) := inferInstance
    have : CharP (AlgebraicClosure K) (ringChar K) := inferInstance
    intro h
    have hdvd : ringChar K ∣ 31 :=
      (CharP.cast_eq_zero_iff (AlgebraicClosure K) (ringChar K) 31).mp h
    rcases (by norm_num : Nat.Prime 31).eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · exact CharP.ringChar_ne_one h1
    · exact hK h1
  have hE' : ∀ x ∈ E.map φ, x ^ 31 = 1 := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [← map_pow, hE y hy, map_one]
  have hEc' : ∀ x ∈ E.map φ, ∀ y ∈ E.map φ, x * y = y * x := by
    intro x hx y hy
    rw [Subgroup.mem_map] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    rw [← map_mul, ← map_mul, hEc a ha b hb]
  have hθE' : ∀ x ∈ E.map φ, semilinConjGL (φ A) σ' x ∈ E.map φ := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [← map_semilinConjGL (algebraMap K (AlgebraicClosure K)) σ σ' hσ' A y]
    exact Subgroup.mem_map_of_mem φ (hθE y hy)
  have hdim' : Fintype.card ι ≤ 4 ∨ (Fintype.card ι ≤ 9 ∧ ∃ J' : Matrix ι ι (AlgebraicClosure K),
      IsUnit J'.det ∧ ∀ x ∈ E.map φ,
        (x : Matrix ι ι (AlgebraicClosure K))ᵀ * J' * x = J') := by
    rcases hdim with h4 | ⟨h9, J, hJdet, hJinv⟩
    · exact Or.inl h4
    · refine Or.inr ⟨h9, J.map (algebraMap K (AlgebraicClosure K)), ?_, ?_⟩
      · have hJM : J.map (algebraMap K (AlgebraicClosure K)) =
            (algebraMap K (AlgebraicClosure K)).mapMatrix J := rfl
        rw [hJM, ← RingHom.map_det]
        exact hJdet.map (algebraMap K (AlgebraicClosure K))
      · intro x hx
        rw [Subgroup.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        calc ((y : Matrix ι ι K).map (algebraMap K (AlgebraicClosure K)))ᵀ *
              J.map (algebraMap K (AlgebraicClosure K)) *
              (y : Matrix ι ι K).map (algebraMap K (AlgebraicClosure K))
            = ((y : Matrix ι ι K)ᵀ).map (algebraMap K (AlgebraicClosure K)) *
              J.map (algebraMap K (AlgebraicClosure K)) *
              (y : Matrix ι ι K).map (algebraMap K (AlgebraicClosure K)) := by
                rw [Matrix.transpose_map]
          _ = ((y : Matrix ι ι K)ᵀ * J * y).map (algebraMap K (AlgebraicClosure K)) := by
                rw [Matrix.map_mul, Matrix.map_mul]
          _ = J.map (algebraMap K (AlgebraicClosure K)) := by rw [hJinv y hy]
  have : Finite ↥(E.map φ) :=
    Finite.of_surjective (Subgroup.equivMapOfInjective E φ hφ_inj)
      (Subgroup.equivMapOfInjective E φ hφ_inj).surjective
  obtain ⟨c, hc⟩ := weylFive_weights_algClosed (ι := ι) (Ω := AlgebraicClosure K) h31
    (φ A) σ' (E.map φ) hE' hEc' hθE' hdim'
  refine ⟨c, ?_⟩
  intro x hx
  have hx' : φ x ∈ E.map φ := Subgroup.mem_map_of_mem φ hx
  have h1 := hc (φ x) hx'
  have hiter : ∀ k : ℕ, (semilinConjGL (φ A) σ')^[k] (φ x) =
      φ ((semilinConjGL A σ)^[k] x) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      have h1 : (semilinConjGL (φ A) σ')^[Nat.succ k] (φ x) =
          semilinConjGL (φ A) σ' ((semilinConjGL (φ A) σ')^[k] (φ x)) :=
        Function.iterate_succ_apply' _ k _
      have h2 : (semilinConjGL A σ)^[Nat.succ k] x =
          semilinConjGL A σ ((semilinConjGL A σ)^[k] x) :=
        Function.iterate_succ_apply' _ k _
      rw [h1, h2, ih, ← map_semilinConjGL (algebraMap K (AlgebraicClosure K)) σ σ' hσ' A
        ((semilinConjGL A σ)^[k] x)]
  have h2 : (semilinConjGL (φ A) σ')^[48] (φ x) = φ ((semilinConjGL A σ)^[48] x) := hiter 48
  rw [h2] at h1
  have h3 : (φ x) ^ c = φ (x ^ c) := (map_pow φ x c).symm
  rw [h3] at h1
  exact hφ_inj h1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
