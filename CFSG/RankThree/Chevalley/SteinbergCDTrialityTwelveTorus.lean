module

public import CFSG.RankThree.Chevalley.G2CyclotomicTori
public import CFSG.LieType.Chevalley.TrialityFullAmbientFixedGroup
public import CFSG.LieType.Chevalley.ParabolicRadicalSelfCentralizing
public import CFSG.RankThree.Lattice.SteinbergBITrialityCoxeter
public import CFSG.RankThree.Chevalley.SteinbergBID4RegularCentralizer
public import CFSG.RankThree.Chevalley.SteinbergBIRootSL2Tools

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.Lattice
open scoped Matrix

theorem twelve_add_iff {A : Type*} [AddCommGroup A] (q : ℤ) (x₀ x₁ x₂ x₃ : A) :
    (q • x₂ = x₀ ∧ q • x₀ + q • x₂ + q • x₃ = x₁ ∧ -(q • x₂ + q • x₃) = x₂ ∧
      q • x₁ + q • x₂ + q • x₃ = x₃) ↔
    (x₁ = q ^ 3 • x₀ ∧ x₂ = (q - q ^ 3) • x₀ ∧ x₃ = (q ^ 3 + q ^ 2 - q - 1) • x₀ ∧
      (q ^ 4 - q ^ 2 + 1) • x₀ = 0) := by
  constructor
  · rintro ⟨e0, e1, e2, e3⟩
    have h2 : (q ^ 4 - q ^ 2 + 1) • x₂ = 0 := by
      linear_combination (norm := module) (q - 1) • e2 + q • e3 + q ^ 2 • (e1 + e2 + q • e0)
    have h0 : (q ^ 4 - q ^ 2 + 1) • x₀ = 0 := by
      linear_combination (norm := module) q • h2 - (q ^ 4 - q ^ 2 + 1) • e0
    refine ⟨?_, ?_, ?_, h0⟩
    · linear_combination (norm := module) -h2 - (e1 + e2 + q • e0) + q ^ 3 • e0
    · linear_combination (norm := module) h2 + (q - q ^ 3) • e0
    · linear_combination (norm := module)
        -h2 - q • (e1 + e2 + q • e0) - (e3 + e2) + (q ^ 3 + q ^ 2 - q - 1) • e0
  · rintro ⟨h1, h2, h3, h0⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · linear_combination (norm := module) q • h2 - h0
    · linear_combination (norm := module) q • h2 + q • h3 - h1
    · linear_combination (norm := module) -(q + 1) • h2 - q • h3
    · linear_combination (norm := module) q • h1 + q • h2 + (q - 1) • h3 + h0

section Index

theorem sum_D4 {M : Type*} [AddCommMonoid M] (f : Fin TwistTag.D4.tag.rank → M) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 :=
  Fin.sum_univ_four f

theorem prod_D4 {M : Type*} [CommMonoid M] (f : Fin TwistTag.D4.tag.rank → M) :
    ∏ i, f i = f 0 * f 1 * f 2 * f 3 :=
  Fin.prod_univ_four f

theorem fin_D4_eq_iff {M : Type*} (x y : Fin TwistTag.D4.tag.rank → M) :
    x = y ↔ x 0 = y 0 ∧ x 1 = y 1 ∧ x 2 = y 2 ∧ x 3 = y 3 := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rintro ⟨h0, h1, h2, h3⟩
    funext j
    fin_cases j
    exacts [h0, h1, h2, h3]

@[expose] def twelveW : Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ :=
  trialityCoxeter

theorem trialityCoxeter_mulVec (v : Fin 4 → ℤ) :
    trialityCoxeter *ᵥ v = ![v 2 - v 3, v 0, v 0 + v 1 - v 3, v 1] := by
  rw [triality_twisted_Coxeter_unimodular_root_orbits.1]
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> ring

theorem twelveW_mulVec (v : Fin TwistTag.D4.tag.rank → ℤ) :
    (twelveW *ᵥ v) 0 = v 2 - v 3 ∧ (twelveW *ᵥ v) 1 = v 0 ∧
      (twelveW *ᵥ v) 2 = v 0 + v 1 - v 3 ∧ (twelveW *ᵥ v) 3 = v 1 := by
  have h := trialityCoxeter_mulVec v
  exact ⟨congrFun h 0, congrFun h 1, congrFun h 2, congrFun h 3⟩

end Index

section Tuples

variable {L : Type} [Field L]

@[expose] def twelveExp (q : ℤ) : Fin TwistTag.D4.tag.rank → ℤ :=
  ![1, q ^ 3, q - q ^ 3, q ^ 3 + q ^ 2 - q - 1]

theorem twelveExp_values (q : ℤ) : twelveExp q 0 = 1 ∧ twelveExp q 1 = q ^ 3 ∧
    twelveExp q 2 = q - q ^ 3 ∧ twelveExp q 3 = q ^ 3 + q ^ 2 - q - 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

@[expose] def twelveTuple (q : ℤ) : Lˣ →* (Fin TwistTag.D4.tag.rank → Lˣ) where
  toFun b i := b ^ twelveExp q i
  map_one' := by
    funext i
    simp
  map_mul' b b' := by
    funext i
    simp [mul_zpow]

theorem twelveTuple_apply (q : ℤ) (b : Lˣ) (i : Fin TwistTag.D4.tag.rank) :
    twelveTuple q b i = b ^ twelveExp q i := rfl

theorem twelveTuple_zero (q : ℤ) (b : Lˣ) : twelveTuple q b 0 = b := by
  rw [twelveTuple_apply, (twelveExp_values q).1, zpow_one]

theorem rootChar_twelveTuple (q : ℤ) (b : Lˣ) (v : Fin TwistTag.D4.tag.rank → ℤ) :
    rootChar (twelveTuple q b) v = b ^ (∑ i, twelveExp q i * v i) := by
  rw [rootChar]
  simp only [twelveTuple_apply, ← _root_.zpow_mul]
  exact CFSG.LieType.Chevalley.prod_zpow_eq_zpow_sum _ _ _

theorem twelveExp_dot_mulVec (q : ℤ) (v : Fin TwistTag.D4.tag.rank → ℤ) :
    ∑ i, twelveExp q i * (twelveW *ᵥ v) i =
      q * ∑ i, twelveExp q i * v i + (q ^ 4 - q ^ 2 + 1) * (-v 1 + v 2 - v 3) := by
  obtain ⟨w0, w1, w2, w3⟩ := twelveW_mulVec v
  obtain ⟨m0, m1, m2, m3⟩ := twelveExp_values q
  rw [sum_D4, sum_D4, w0, w1, w2, w3, m0, m1, m2, m3]
  ring

theorem rootChar_twelveTuple_mulVec (q : ℕ) {b : Lˣ}
    (hb : b ^ ((q : ℤ) ^ 4 - (q : ℤ) ^ 2 + 1) = 1) (v : Fin TwistTag.D4.tag.rank → ℤ) :
    rootChar (twelveTuple q b) (twelveW *ᵥ v) = rootChar (twelveTuple q b) v ^ q := by
  rw [rootChar_twelveTuple, rootChar_twelveTuple, twelveExp_dot_mulVec, zpow_add,
    _root_.zpow_mul _ ((q : ℤ) ^ 4 - (q : ℤ) ^ 2 + 1), hb, one_zpow, mul_one, ← zpow_natCast,
    ← _root_.zpow_mul, mul_comm]

end Tuples

section Twist

variable {L : Type} [Field L]

theorem perm_symm_D4_values : TwistTag.D4.perm.symm 0 = 3 ∧ TwistTag.D4.perm.symm 1 = 0 ∧
    TwistTag.D4.perm.symm 2 = 2 ∧ TwistTag.D4.perm.symm 3 = 1 := by
  decide

theorem cartan_D4_values : (TwistTag.D4.tag.cartan 0 0 = 2 ∧ TwistTag.D4.tag.cartan 0 1 = 0 ∧
    TwistTag.D4.tag.cartan 0 2 = -1 ∧ TwistTag.D4.tag.cartan 0 3 = 0) ∧
    (TwistTag.D4.tag.cartan 2 0 = -1 ∧ TwistTag.D4.tag.cartan 2 1 = -1 ∧
    TwistTag.D4.tag.cartan 2 2 = 2 ∧ TwistTag.D4.tag.cartan 2 3 = -1) := by
  decide

variable (L) in
abbrev trialityTwistN : ModGL TwistTag.D4.tag L :=
  weylElt TwistTag.D4.tag L 2 1 * weylElt TwistTag.D4.tag L 0 1

variable (L) in
abbrev trialityFrob (F : L →+* L) : ModGL TwistTag.D4.tag L →* ModGL TwistTag.D4.tag L :=
  (MulAut.conj (diagramMap TwistTag.D4 L)).toMonoidHom.comp (Units.map (entrywiseHom F))

theorem trialityFrob_apply (F : L →+* L) (g : ModGL TwistTag.D4.tag L) :
    trialityFrob L F g =
      diagramMap TwistTag.D4 L * Units.map (entrywiseHom F) g * (diagramMap TwistTag.D4 L)⁻¹ :=
  rfl

@[expose] def twelveTwistTuple (q : ℕ) (c : Fin TwistTag.D4.tag.rank → Lˣ) :
    Fin TwistTag.D4.tag.rank → Lˣ :=
  ![c 2 ^ q, c 0 ^ q * c 2 ^ q * c 3 ^ q, (c 2 ^ q * c 3 ^ q)⁻¹, c 1 ^ q * c 2 ^ q * c 3 ^ q]

theorem twelveTwistTuple_values (q : ℕ) (c : Fin TwistTag.D4.tag.rank → Lˣ) :
    twelveTwistTuple q c 0 = c 2 ^ q ∧ twelveTwistTuple q c 1 = c 0 ^ q * c 2 ^ q * c 3 ^ q ∧
      twelveTwistTuple q c 2 = (c 2 ^ q * c 3 ^ q)⁻¹ ∧
      twelveTwistTuple q c 3 = c 1 ^ q * c 2 ^ q * c 3 ^ q :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem trialityTwist_conj_rootDiagUnit (F : L →+* L) {q : ℕ} (hF : ∀ c, F c = c ^ q)
    (c : Fin TwistTag.D4.tag.rank → Lˣ) :
    trialityTwistN L * trialityFrob L F (rootDiagUnit TwistTag.D4.tag c) * (trialityTwistN L)⁻¹ =
      rootDiagUnit TwistTag.D4.tag (twelveTwistTuple q c) := by
  rw [trialityFrob_apply, entrywise_frob_rootDiagUnit F hF, diagramMap_mul_rootDiagUnit,
    mul_inv_cancel_right, mul_inv_rev,
    show ∀ x y z w : ModGL TwistTag.D4.tag L, x * y * z * (w * x⁻¹) = x * (y * z * w) * x⁻¹
      from fun x y z w => by group, weylElt_conj_rootDiagUnit, weylElt_conj_rootDiagUnit]
  congr 1
  obtain ⟨h0, h1, h2, h3⟩ := perm_symm_D4_values
  obtain ⟨⟨a00, a01, a02, a03⟩, ⟨a20, a21, a22, a23⟩⟩ := cartan_D4_values
  obtain ⟨t0, t1, t2, t3⟩ := twelveTwistTuple_values q c
  refine (fin_D4_eq_iff _ _).2 ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Pi.pow_apply, h0, h1, h2, h3, a00, a01, a02, a03, a20, a21, a22, a23, t0, t1, t2,
      t3] <;>
    apply Additive.ofMul.injective <;>
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow] <;>
    module

theorem trialityTwist_rootDiagUnit_eq_iff (F : L →+* L) {q : ℕ} (hF : ∀ c, F c = c ^ q)
    (c : Fin TwistTag.D4.tag.rank → Lˣ) :
    trialityTwistN L * trialityFrob L F (rootDiagUnit TwistTag.D4.tag c) * (trialityTwistN L)⁻¹ =
        rootDiagUnit TwistTag.D4.tag c ↔
      c = twelveTuple q (c 0) ∧ c 0 ^ ((q : ℤ) ^ 4 - (q : ℤ) ^ 2 + 1) = 1 := by
  rw [trialityTwist_conj_rootDiagUnit F hF, rootDiagUnit_injective.eq_iff, eq_comm,
    fin_D4_eq_iff]
  obtain ⟨t0, t1, t2, t3⟩ := twelveTwistTuple_values q c
  rw [t0, t1, t2, t3]
  obtain ⟨m0, m1, m2, m3⟩ := twelveExp_values (q : ℤ)
  have hsys := twelve_add_iff (q : ℤ) (Additive.ofMul (c 0)) (Additive.ofMul (c 1))
    (Additive.ofMul (c 2)) (Additive.ofMul (c 3))
  have htup : c = twelveTuple q (c 0) ↔ c 1 = c 0 ^ ((q : ℤ) ^ 3) ∧
      c 2 = c 0 ^ ((q : ℤ) - (q : ℤ) ^ 3) ∧ c 3 = c 0 ^ ((q : ℤ) ^ 3 + (q : ℤ) ^ 2 - q - 1) := by
    constructor
    · intro h
      refine ⟨?_, ?_, ?_⟩
      · rw [← m1, ← twelveTuple_apply]
        exact congrFun h 1
      · rw [← m2, ← twelveTuple_apply]
        exact congrFun h 2
      · rw [← m3, ← twelveTuple_apply]
        exact congrFun h 3
    · rintro ⟨h1, h2, h3⟩
      refine (fin_D4_eq_iff _ _).2 ⟨(twelveTuple_zero _ _).symm, ?_, ?_, ?_⟩
      · rw [twelveTuple_apply, m1]
        exact h1
      · rw [twelveTuple_apply, m2]
        exact h2
      · rw [twelveTuple_apply, m3]
        exact h3
  rw [htup]
  constructor
  · rintro ⟨e0, e1, e2, e3⟩
    have e0' := congrArg Additive.ofMul e0
    have e1' := congrArg Additive.ofMul e1
    have e2' := congrArg Additive.ofMul e2
    have e3' := congrArg Additive.ofMul e3
    simp only [ofMul_mul, ofMul_inv, ofMul_pow, ← natCast_zsmul] at e0' e1' e2' e3'
    obtain ⟨h1, h2, h3, h0⟩ := hsys.1 ⟨e0'.symm, e1'.symm, e2'.symm, e3'.symm⟩
    refine ⟨⟨Additive.ofMul.injective (by rw [ofMul_zpow, h1]),
      Additive.ofMul.injective (by rw [ofMul_zpow, h2]),
      Additive.ofMul.injective (by rw [ofMul_zpow, h3])⟩,
      Additive.ofMul.injective (by rw [ofMul_zpow, h0, ofMul_one])⟩
  · rintro ⟨⟨h1, h2, h3⟩, h0⟩
    obtain ⟨e0, e1, e2, e3⟩ := hsys.2 ⟨by rw [h1, ofMul_zpow], by rw [h2, ofMul_zpow],
      by rw [h3, ofMul_zpow], by rw [← ofMul_zpow, h0, ofMul_one]⟩
    refine ⟨Additive.ofMul.injective ?_, Additive.ofMul.injective ?_,
      Additive.ofMul.injective ?_, Additive.ofMul.injective ?_⟩ <;>
      simp only [ofMul_mul, ofMul_inv, ofMul_pow, ← natCast_zsmul]
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact e3.symm

end Twist

section Torus

variable {L : Type} [Field L]

variable (L) in
@[expose] def twelveTorus (q d : ℕ) : Subgroup (ModGL TwistTag.D4.tag L) :=
  (rootsOfUnity d L).map ((rootDiagUnitHom TwistTag.D4.tag L).comp (twelveTuple q))

theorem injective_twelveTorus_map (q : ℕ) :
    Function.Injective ((rootDiagUnitHom TwistTag.D4.tag L).comp (twelveTuple (L := L) q)) := by
  intro b b' h
  have h' : twelveTuple q b = twelveTuple q b' := rootDiagUnit_injective h
  have := congrFun h' 0
  rwa [twelveTuple_zero, twelveTuple_zero] at this

theorem rootDiagUnit_mem_twelveTorus_iff (q d : ℕ) (c : Fin TwistTag.D4.tag.rank → Lˣ) :
    rootDiagUnit TwistTag.D4.tag c ∈ twelveTorus L q d ↔ c = twelveTuple q (c 0) ∧ c 0 ^ d = 1 := by
  constructor
  · rintro ⟨b, hb, h⟩
    have hc : twelveTuple q b = c := rootDiagUnit_injective h
    have hb0 : c 0 = b := by rw [← hc, twelveTuple_zero]
    rw [hb0]
    exact ⟨hc.symm, (mem_rootsOfUnity d b).1 hb⟩
  · rintro ⟨hc, hd⟩
    refine ⟨c 0, (mem_rootsOfUnity d _).2 hd, ?_⟩
    change rootDiagUnit TwistTag.D4.tag (twelveTuple q (c 0)) = rootDiagUnit TwistTag.D4.tag c
    rw [← hc]

theorem twelveTorus_le_torusGroup [IsAlgClosed L] (q d : ℕ) :
    twelveTorus L q d ≤ torusGroup TwistTag.D4.tag L := by
  rintro _ ⟨b, -, rfl⟩
  obtain ⟨-, t, ht⟩ := exceptional_Lang_adjoint_diagonal_lift TwistTag.D4.tag L (twelveTuple q b)
  change rootDiagUnit TwistTag.D4.tag (twelveTuple q b) ∈ torusGroup TwistTag.D4.tag L
  rw [ht]
  refine list_prod_mem fun x hx => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  exact Subgroup.subset_closure ⟨(j, t j), rfl⟩

theorem torusGroup_le_adjointGroup_triality :
    torusGroup TwistTag.D4.tag L ≤ adjointGroup TwistTag.D4.tag L := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨⟨i, t⟩, rfl⟩
  exact torusElt_mem_adjointGroup i t

theorem twelve_rootChar_ne_one (q : ℕ) {b : Lˣ} (hb : b ^ ((q : ℤ) ^ 4 - (q : ℤ) ^ 2 + 1) = 1)
    (hb1 : b ≠ 1) (α : Fin TwistTag.D4.tag.rank → ℤ) (hα : IsRoot TwistTag.D4.tag α) :
    rootChar (twelveTuple q b) α ≠ 1 := by
  intro h1
  have hpow : ∀ j : ℕ, rootChar (twelveTuple q b) ((twelveW ^ j) *ᵥ α) = 1 := by
    intro j
    induction j with
    | zero => rwa [pow_zero, Matrix.one_mulVec]
    | succ j ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, rootChar_twelveTuple_mulVec q hb, ih, one_pow]
  let S : AddSubgroup (Fin 4 → ℤ) :=
    { carrier := {v | rootChar (twelveTuple q b) v = 1}
      add_mem' := fun {u v} hu hv => by
        have hu' : rootChar (twelveTuple q b) u = 1 := hu
        have hv' : rootChar (twelveTuple q b) v = 1 := hv
        exact (rootChar_add (twelveTuple q b) u v).trans (by rw [hu', hv', one_mul])
      zero_mem' := rootChar_zero _
      neg_mem' := fun {v} hv => by
        have hv' : rootChar (twelveTuple q b) v = 1 := hv
        exact (rootChar_neg' (twelveTuple q b) v).trans (by rw [hv', inv_one]) }
  have hspan := (triality_twisted_Coxeter_unimodular_root_orbits.2.2.2.2.2.2.2.2.2 α hα).1.2
  have hle : Submodule.span ℤ (Set.range fun j : Fin 4 => (trialityCoxeter ^ (j : ℕ)) *ᵥ α) ≤
      S.toIntSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hpow j
  rw [hspan] at hle
  have h0 : rootChar (twelveTuple q b) (Pi.single (0 : Fin TwistTag.D4.tag.rank) 1) = 1 :=
    hle (Submodule.mem_top (x := (Pi.single (0 : Fin 4) 1 : Fin 4 → ℤ)))
  rw [rootChar_single, twelveTuple_zero] at h0
  exact hb1 h0

end Torus

theorem centralizer_le_comap_conj_twisted {τ : Tag} {L : Type} [Field L] {C : Type*} [Group C]
    (ι : C →* ModGL τ L) (Φ : ModGL τ L →* ModGL τ L) {n g : ModGL τ L}
    (hgG : g ∈ adjointGroup τ L) (hFg : Φ g = g * n)
    (hrange : ι.range = adjointGroup τ L ⊓ Φ.eqLocus (MonoidHom.id _))
    {T₀ : Subgroup (ModGL τ L)}
    (hchar : ∀ u ∈ torusGroup τ L, (n * Φ u * n⁻¹ = u ↔ u ∈ T₀))
    {t : C} {c : Fin τ.rank → Lˣ} (hct : g * rootDiagUnit τ c * g⁻¹ = ι t)
    (hX : toralCentralizer τ L c = torusGroup τ L) :
    Subgroup.centralizer {t} ≤ (T₀.map (MulAut.conj g).toMonoidHom).comap ι := by
  intro y hy
  have hyt : t * y = y * t := Subgroup.mem_centralizer_iff.1 hy t rfl
  have hyF : ι y ∈ ι.range := ⟨y, rfl⟩
  rw [hrange] at hyF
  obtain ⟨hyG, hyFix⟩ := Subgroup.mem_inf.1 hyF
  have hyFix' : Φ (ι y) = ι y := hyFix
  obtain ⟨u, hu⟩ : ∃ u, u = g⁻¹ * ι y * g := ⟨_, rfl⟩
  have huG : u ∈ adjointGroup τ L := hu ▸ mul_mem (mul_mem (inv_mem hgG) hyG) hgG
  have hdc : rootDiagUnit τ c = g⁻¹ * ι t * g := by
    rw [← hct]
    group
  have huc : u ∈ Subgroup.centralizer {rootDiagUnit τ c} := by
    rw [Subgroup.mem_centralizer_singleton_iff, hdc, hu]
    have hιyt : ι t * ι y = ι y * ι t := by rw [← map_mul, hyt, map_mul]
    calc g⁻¹ * ι y * g * (g⁻¹ * ι t * g) = g⁻¹ * (ι y * ι t) * g := by group
      _ = g⁻¹ * (ι t * ι y) * g := by rw [hιyt]
      _ = g⁻¹ * ι t * g * (g⁻¹ * ι y * g) := by group
  have huH : u ∈ torusGroup τ L := by
    rw [← hX]
    exact Subgroup.mem_inf.2 ⟨huG, huc⟩
  have h2 : g * u * g⁻¹ = ι y := by
    rw [hu]
    group
  have hufix : n * Φ u * n⁻¹ = u := by
    have h1 : Φ (g * u * g⁻¹) = g * (n * Φ u * n⁻¹) * g⁻¹ := by
      rw [map_mul, map_mul, map_inv, hFg]
      group
    rw [h2, hyFix', ← h2] at h1
    simpa using h1.symm
  exact ⟨u, (hchar u huH).1 hufix, by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact h2⟩

theorem twelve_cast (q : ℕ) : ((q ^ 4 - q ^ 2 + 1 : ℕ) : ℤ) = (q : ℤ) ^ 4 - (q : ℤ) ^ 2 + 1 := by
  have h : q ^ 2 ≤ q ^ 4 := by
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · simp
    · exact Nat.pow_le_pow_right hq (by norm_num)
  push_cast [Nat.cast_sub h]
  ring

theorem twelve_core {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    ∃ T : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), IsCyclic T ∧
      Nat.card T = (ℓ ^ f) ^ 4 - (ℓ ^ f) ^ 2 + 1 ∧
      ∀ p : ℕ, p.Prime → 3 < p → p ∣ (ℓ ^ f) ^ 4 - (ℓ ^ f) ^ 2 + 1 →
        ∀ t ∈ T, orderOf t = p → Subgroup.centralizer {t} = T := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Fintype K := Fintype.ofFinite K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hK3 : Nat.card K = ℓ ^ (f * 3) := by rw [hK, pow_mul]
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ (by omega) hK3
  set q := ℓ ^ f with hq
  set d := q ^ 4 - q ^ 2 + 1 with hd
  have hdZ : (d : ℤ) = (q : ℤ) ^ 4 - (q : ℤ) ^ 2 + 1 := twelve_cast q
  let L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  set F : L →+* L := iterateFrobenius L ℓ f with hFdef
  have hF : ∀ c : L, F c = c ^ q := fun c => by rw [hFdef, iterateFrobenius_def]
  obtain ⟨-, hfix, -, -, -⟩ := triality_both_field_orientations_simple_full_ambient_fixed_group ℓ f
    hℓ hf K hK L 1 (Or.inl rfl) σ.toRingHom (fun c => by rw [pow_one]; exact hσ c) F hF
  obtain ⟨S, hS, hLang⟩ :=
    (exceptional_all_characteristic_field_Lang_surjectivity ℓ L f hf).2 TwistTag.D4 1
  have hnG : trialityTwistN L ∈ adjointGroup TwistTag.D4.tag L :=
    mul_mem (weylElt_mem_adjointGroup 2 1) (weylElt_mem_adjointGroup 0 1)
  obtain ⟨g₀, hg₀⟩ := hLang ⟨trialityTwistN L, hnG⟩
  set g : ModGL TwistTag.D4.tag L := (g₀ : ModGL TwistTag.D4.tag L) with hgdef
  have hgG : g ∈ adjointGroup TwistTag.D4.tag L := g₀.2
  have hFg : trialityFrob L F g = g * trialityTwistN L := by
    have h := congrArg Subtype.val hg₀
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
    rw [hS, zpow_one] at h
    rw [trialityFrob_apply, h, mul_inv_cancel_left]
  set T₀ := twelveTorus L q d with hT₀
  have hT₀H : T₀ ≤ torusGroup TwistTag.D4.tag L := twelveTorus_le_torusGroup q d
  have hHG := torusGroup_le_adjointGroup_triality (L := L)
  have hHcomm := (triangular_borel_structure.{0, 0} TwistTag.D4.tag L).1
  have hchar : ∀ u ∈ torusGroup TwistTag.D4.tag L,
      (trialityTwistN L * trialityFrob L F u * (trialityTwistN L)⁻¹ = u ↔ u ∈ T₀) := by
    intro u hu
    obtain ⟨c, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hu
    rw [trialityTwist_rootDiagUnit_eq_iff F hF, rootDiagUnit_mem_twelveTorus_iff, ← hdZ,
      zpow_natCast]
  have hqK : ((q : ℕ) : K) = 0 := by
    rw [hq, Nat.cast_pow, CharP.cast_eq_zero, zero_pow (by omega)]
  have hdK : (d : K) = 1 := by
    have h := congrArg (Int.cast : ℤ → K) hdZ
    push_cast at h
    rw [h, hqK]
    ring
  have : NeZero (d : K) := ⟨by rw [hdK]; exact one_ne_zero⟩
  have : NeZero d := ⟨fun h0 => by simp [h0] at hdK⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.prim (M := L) (n := d)
  have hcardT₀ : Nat.card T₀ = d := by
    rw [hT₀, twelveTorus, Subgroup.card_map_of_injective (injective_twelveTorus_map q),
      hζ.card_rootsOfUnity]
  have hcycT₀ : IsCyclic T₀ :=
    isCyclic_of_surjective _
      (((rootDiagUnitHom TwistTag.D4.tag L).comp (twelveTuple q)).subgroupMap_surjective
        (rootsOfUnity d L))
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC
  obtain ⟨ι, hι⟩ : ∃ ι : C →* ModGL TwistTag.D4.tag L,
      ι = (baseChangeGL (algebraMap K L)).comp C.subtype := ⟨_, rfl⟩
  have hιinj : Function.Injective ι := by
    rw [hι]
    exact (baseChangeGL_injective (τ := TwistTag.D4.tag) (algebraMap K L)).comp
      Subtype.val_injective
  have hrange : ι.range = adjointGroup TwistTag.D4.tag L ⊓
      (trialityFrob L F).eqLocus (MonoidHom.id _) := by
    rw [hι, MonoidHom.range_comp, Subgroup.range_subtype]
    refine SetLike.coe_injective ?_
    rw [← hfix]
    ext x
    simp only [pow_one, Set.mem_ofPred_eq, SetLike.mem_coe, Subgroup.mem_inf]
    rfl
  have hconjF : ∀ u : ModGL TwistTag.D4.tag L, trialityFrob L F (g * u * g⁻¹) =
      g * (trialityTwistN L * trialityFrob L F u * (trialityTwistN L)⁻¹) * g⁻¹ := fun u => by
    rw [map_mul, map_mul, map_inv, hFg]
    group
  set Tc := T₀.map (MulAut.conj g).toMonoidHom with hTc
  have hTcι : Tc ≤ ι.range := by
    rintro _ ⟨u, hu, rfl⟩
    rw [hrange]
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hgG (hHG (hT₀H hu))) (inv_mem hgG), ?_⟩
    change trialityFrob L F (g * u * g⁻¹) = g * u * g⁻¹
    rw [hconjF, (hchar u (hT₀H hu)).2 hu]
  set T := Tc.comap ι with hT
  have eT : T ≃* T₀ :=
    ((Subgroup.equivMapOfInjective T ι hιinj).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hTcι))).trans
      (Subgroup.equivMapOfInjective T₀ (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).symm
  have hcardT : Nat.card T = d := by rw [Nat.card_congr eT.toEquiv, hcardT₀]
  have hcycT : IsCyclic T := isCyclic_of_injective eT.toMonoidHom eT.injective
  have hTcomm : ∀ y ∈ T, ∀ z ∈ T, y * z = z * y := by
    intro y hy z hz
    apply hιinj
    obtain ⟨u, hu, hyu⟩ := hy
    obtain ⟨u', hu', hzu⟩ := hz
    rw [map_mul, map_mul, ← hyu, ← hzu]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hc := hHcomm u (hT₀H hu) u' (hT₀H hu')
    calc g * u * g⁻¹ * (g * u' * g⁻¹) = g * (u * u') * g⁻¹ := by group
      _ = g * (u' * u) * g⁻¹ := by rw [hc]
      _ = g * u' * g⁻¹ * (g * u * g⁻¹) := by group
  refine ⟨T, hcycT, hcardT, fun p hp hp3 hpd t ht hto => ?_⟩
  have ht' := ht
  obtain ⟨h, hh, hht⟩ := ht
  obtain ⟨c, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hT₀H hh)
  have hoc : orderOf (rootDiagUnit TwistTag.D4.tag c) = p := by
    rw [← orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
        (rootDiagUnit TwistTag.D4.tag c), hht, orderOf_injective ι hιinj t, hto]
  obtain ⟨hc, hcd⟩ := (rootDiagUnit_mem_twelveTorus_iff q d c).1 hh
  have hc1 : c 0 ≠ 1 := fun h1 => by
    rw [hc, h1, map_one, rootDiagUnit_one, orderOf_one] at hoc
    exact hp.one_lt.ne hoc
  have hcd' : c 0 ^ ((q : ℤ) ^ 4 - (q : ℤ) ^ 2 + 1) = 1 := by rw [← hdZ, zpow_natCast, hcd]
  have hreg : ∀ α : Fin Tag.D4.rank → ℤ, IsRoot Tag.D4 α → rootChar c α ≠ 1 := by
    intro α hα
    rw [hc]
    exact twelve_rootChar_ne_one q hcd' hc1 α hα
  have hpq : ¬ p ∣ q := by
    intro hpq
    have h1 : p ∣ q ^ 2 * (q ^ 2 - 1) := dvd_mul_of_dvd_left (dvd_pow hpq two_ne_zero) _
    have h2 : d = q ^ 2 * (q ^ 2 - 1) + 1 := by
      rw [hd, Nat.mul_sub_one, ← pow_add]
    have h3 : p ∣ 1 := (Nat.dvd_add_right h1).1 (h2 ▸ hpd)
    exact hp.one_lt.ne' (Nat.dvd_one.1 h3)
  have hpL : ringChar L ≠ p := by
    rw [ringChar.eq L ℓ]
    intro hℓp
    exact hpq (hℓp ▸ dvd_pow_self ℓ (by omega))
  have hX : toralCentralizer TwistTag.D4.tag L c = torusGroup TwistTag.D4.tag L := by
    obtain ⟨-, hiff⟩ := D4_odd_prime_regular_root_character_centralizer L p hp (by omega) hpL c
      hoc hreg
    ext y
    rw [toralCentralizer, Subgroup.mem_inf, ← conj_eq_iff_mem_centralizer]
    exact hiff y
  refine le_antisymm (centralizer_le_comap_conj_twisted ι (trialityFrob L F) hgG hFg hrange hchar
    hht hX) fun y hy => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst hz
  exact hTcomm z ht' y hy

theorem not_dvd_index_twelveTorus {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hp : p.Prime)
    (hp3 : 3 < p) (hpd : p ∣ (ℓ ^ f) ^ 4 - (ℓ ^ f) ^ 2 + 1)
    (T : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hT : Nat.card T = (ℓ ^ f) ^ 4 - (ℓ ^ f) ^ 2 + 1) : ¬ p ∣ T.index := by
  have hcardC := (triality_both_orientations_exact_finite_order ℓ f hℓ hf K hK 1 (Or.inl rfl)
    σ.toRingHom (fun c => by rw [pow_one]; exact hσ c)).1
  set q := ℓ ^ f with hq
  have hq1 : 1 ≤ q := Nat.one_le_pow _ _ hℓ.pos
  have hcard := T.card_mul_index
  rw [hT, hcardC] at hcard
  have hdZ : ((q ^ 4 - q ^ 2 + 1 : ℕ) : ℤ) = (q : ℤ) ^ 4 - (q : ℤ) ^ 2 + 1 := twelve_cast q
  have hcardZ : ((q : ℤ) ^ 4 - (q : ℤ) ^ 2 + 1) * T.index =
      (q : ℤ) ^ 12 * ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 6 - 1) * ((q : ℤ) ^ 8 + (q : ℤ) ^ 4 + 1) := by
    have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq1
    have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
    have h := congrArg (Nat.cast : ℕ → ℤ) hcard
    rw [Nat.cast_mul, hdZ] at h
    rw [h]
    push_cast [Nat.cast_sub h6, Nat.cast_sub h2]
    ring
  have hd0 : (q : ℤ) ^ 4 - (q : ℤ) ^ 2 + 1 ≠ 0 := by
    have : (1 : ℤ) ≤ q := by exact_mod_cast hq1
    nlinarith
  have hidx : (T.index : ℤ) = (q : ℤ) ^ 12 * ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 6 - 1) *
      ((q : ℤ) ^ 4 + (q : ℤ) ^ 2 + 1) := by
    apply mul_left_cancel₀ hd0
    rw [hcardZ]
    ring
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  obtain ⟨Q, hQ⟩ : ∃ Q : ℤ, Q = (q : ℤ) := ⟨_, rfl⟩
  have hpd' : (p : ℤ) ∣ Q ^ 4 - Q ^ 2 + 1 := by
    rw [hQ, ← hdZ]
    exact_mod_cast hpd
  intro hdvd
  have hpi : (p : ℤ) ∣ Q ^ 12 * (Q ^ 2 - 1) * (Q ^ 6 - 1) * (Q ^ 4 + Q ^ 2 + 1) := by
    rw [hQ, ← hidx]
    exact_mod_cast hdvd
  have hp1 : ¬ (p : ℤ) ∣ 1 := hpZ.not_dvd_one
  have hp2 : ¬ (p : ℤ) ∣ 2 := fun h => by
    have := Int.le_of_dvd (by norm_num) h
    omega
  have hqp : ¬ (p : ℤ) ∣ Q := fun h => hp1 (by
    have h' := dvd_sub hpd' (dvd_mul_of_dvd_left h (Q ^ 3 - Q))
    rwa [show Q ^ 4 - Q ^ 2 + 1 - Q * (Q ^ 3 - Q) = 1 by ring] at h')
  rcases hpZ.dvd_or_dvd hpi with h | h
  · rcases hpZ.dvd_or_dvd h with h | h
    · rcases hpZ.dvd_or_dvd h with h | h
      · exact hqp (hpZ.dvd_of_dvd_pow h)
      · exact hp1 (by
          have h' := dvd_sub hpd' (dvd_mul_of_dvd_right h (Q ^ 2))
          rwa [show Q ^ 4 - Q ^ 2 + 1 - Q ^ 2 * (Q ^ 2 - 1) = 1 by ring] at h')
    · exact hp2 (by
        have h6 : (p : ℤ) ∣ Q ^ 6 + 1 := by
          rw [show Q ^ 6 + 1 = (Q ^ 2 + 1) * (Q ^ 4 - Q ^ 2 + 1) by ring]
          exact dvd_mul_of_dvd_right hpd' _
        have h' := dvd_sub h6 h
        rwa [show Q ^ 6 + 1 - (Q ^ 6 - 1) = 2 by ring] at h')
  · have h2q : (p : ℤ) ∣ 2 * Q ^ 2 := by
      have h' := dvd_sub h hpd'
      rwa [show Q ^ 4 + Q ^ 2 + 1 - (Q ^ 4 - Q ^ 2 + 1) = 2 * Q ^ 2 by ring] at h'
    rcases hpZ.dvd_or_dvd h2q with h | h
    · exact hp2 h
    · exact hqp (hpZ.dvd_of_dvd_pow h)

theorem triality_cyclotomic_twelve_torus_and_prime_centralizers {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    ∃ T : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), IsCyclic T ∧
      Nat.card T = (ℓ ^ f) ^ 4 - (ℓ ^ f) ^ 2 + 1 ∧
      ∀ p : ℕ, p.Prime → 3 < p → p ∣ (ℓ ^ f) ^ 4 - (ℓ ^ f) ^ 2 + 1 →
        (∃ S : Sylow p (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
          (S : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ≤ T) ∧
        (∀ P : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), IsPGroup p P →
          IsCyclic P) ∧
        ∀ x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, orderOf x = p →
          ∃ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, g * x * g⁻¹ ∈ T ∧
            Subgroup.centralizer {g * x * g⁻¹} = T ∧
            IsCyclic (Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K
              σ.toRingHom))) ∧
            Odd (Nat.card (Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K
              σ.toRingHom)))) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Finite (Module.End K (RootModule TwistTag.D4.tag K)) := Module.finite_of_finite K
  obtain ⟨T, hcyc, hcard, hcent⟩ := twelve_core hℓ hf K hK σ hσ
  set q := ℓ ^ f with hq
  have hdodd : Odd (q ^ 4 - q ^ 2 + 1) := by
    have h2 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right (Nat.one_le_pow _ _ hℓ.pos) (by norm_num)
    have hev : Even (q ^ 4 - q ^ 2) := by
      have : q ^ 4 - q ^ 2 = q ^ 2 * (q ^ 2 - 1) := by rw [Nat.mul_sub_one, ← pow_add]
      rw [this]
      exact Nat.even_mul_pred_self _
    exact hev.add_one
  refine ⟨T, hcyc, hcard, fun p hp hp3 hpd => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  have hidx := not_dvd_index_twelveTorus hℓ hf hK σ hσ hp hp3 hpd T hcard
  have hconjT : ∀ P : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), IsPGroup p P →
      ∃ g, P.map (MulAut.conj g).toMonoidHom ≤ T := fun P hP =>
    exists_conj_map_le_of_not_dvd_index hidx hP
  refine ⟨?_, fun P hP => ?_, fun x hx => ?_⟩
  · obtain ⟨S₀⟩ : Nonempty (Sylow p T) := inferInstance
    have hS : IsPGroup p ((S₀ : Subgroup T).map T.subtype) := S₀.isPGroup'.map T.subtype
    have hSi : ¬ p ∣ ((S₀ : Subgroup T).map T.subtype).index := by
      rw [Subgroup.index_map_subtype]
      exact fun h => ((Fact.out : p.Prime).dvd_mul.1 h).elim S₀.not_dvd_index hidx
    exact ⟨hS.toSylow hSi, by
      rw [IsPGroup.toSylow_coe]
      exact Subgroup.map_subtype_le _⟩
  · obtain ⟨g, hg⟩ := hconjT P hP
    exact isCyclic_of_injective
      (MonoidHom.codRestrict ((MulAut.conj g).toMonoidHom.comp P.subtype) T
        fun y => hg ⟨y, y.2, rfl⟩)
      fun y z h => Subtype.ext ((MulAut.conj g).injective (congrArg Subtype.val h))
  · have hPx : IsPGroup p (Subgroup.zpowers x) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
    obtain ⟨g, hg⟩ := hconjT _ hPx
    have hxT : g * x * g⁻¹ ∈ T := hg ⟨x, Subgroup.mem_zpowers x, rfl⟩
    have hto : orderOf (g * x * g⁻¹) = p := by
      rw [← MulAut.conj_apply, ← MulEquiv.coe_toMonoidHom,
        orderOf_injective _ (MulAut.conj g).injective x, hx]
    have hcT := hcent p hp hp3 hpd _ hxT hto
    have hmap : (Subgroup.centralizer {x}).map (MulAut.conj g).toMonoidHom = T := by
      rw [map_conj_centralizer_singleton_eq, hcT]
    have e : Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ≃*
        T :=
      (Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective).trans
        (MulEquiv.subgroupCongr hmap)
    exact ⟨g, hxT, hcT, isCyclic_of_injective e.toMonoidHom e.injective,
      by rw [Nat.card_congr e.toEquiv, hcard]; exact hdodd⟩

end CFSG.RankThree.Chevalley
