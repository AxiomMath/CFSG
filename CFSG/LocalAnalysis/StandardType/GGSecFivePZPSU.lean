module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePZKnown
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalUField
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitFieldSUDelta
public import CFSG.LocalAnalysis.StandardType.GGSecFivePZOrderNine
public import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoCommon
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019UniOuter
public import CFSG.ClassicalGroups.UnitaryFlag.GramSURootGen

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU mem_unitarySU_iff gramSU unitarySU_eq_gramSU
  unitaryPSUEquiv gramSU_one_eq_SUid normOneScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LieType.Chevalley (fixSubfield)
open CFSG.RankThree.Classical (fixSubfield_unitaryFieldData fixSubfield_unitaryFieldData_bar
  dvd_and_card_fixSubfield_unitary subfieldPSU subfieldPSU_injective range_subfieldPSU_le
  isSimpleGroup_primeFormP_one isPerfect_gramSU_one card_normOneScalars_one)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

namespace PZPSU

section Quot

variable {U G P : Type*} [Group U] [Group G] [Group P]

theorem exists_centerQuot_hom (hU : commutator U = ⊤) (φ : U →* G)
    (hker : φ.ker ≤ Subgroup.center U) (πU : U →* P) (hπ : Function.Surjective πU)
    (hπk : πU.ker = Subgroup.center U) :
    ∃ ρ : ↥φ.range →* P, Function.Surjective ρ ∧ ρ.ker = Subgroup.center ↥φ.range ∧
      ∀ s, ρ (φ.rangeRestrict s) = πU s := by
  classical
  let e := QuotientGroup.quotientKerEquivOfSurjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hle : φ.rangeRestrict.ker ≤ πU.ker := by
    rw [MonoidHom.ker_rangeRestrict, hπk]
    exact hker
  let ρ : ↥φ.range →* P := (QuotientGroup.lift _ πU hle).comp e.symm.toMonoidHom
  have hρ : ∀ s, ρ (φ.rangeRestrict s) = πU s := fun s => by
    have h1 : e.symm (φ.rangeRestrict s) = (s : U ⧸ φ.rangeRestrict.ker) :=
      (MulEquiv.symm_apply_eq _).mpr rfl
    simp only [ρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1, QuotientGroup.lift_mk]
  refine ⟨ρ, fun p => ?_, ?_, hρ⟩
  · obtain ⟨s, rfl⟩ := hπ p
    exact ⟨_, hρ s⟩
  · ext g
    obtain ⟨s, rfl⟩ := φ.rangeRestrict_surjective g
    rw [MonoidHom.mem_ker, hρ, ← MonoidHom.mem_ker, hπk]
    constructor
    · intro hs
      rw [Subgroup.mem_center_iff]
      intro g'
      obtain ⟨s', rfl⟩ := φ.rangeRestrict_surjective g'
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hs s']
    · exact InnerDiagA.mem_center_of_rangeRestrict_mem_center hU φ hker

end Quot

section Beta

variable {U G P : Type*} [Group U] [Group G] [Group P]

theorem exists_beta (hU : commutator U = ⊤) (φ : U →* G) (hker : φ.ker ≤ Subgroup.center U)
    (πU : U →* P) (hπ : Function.Surjective πU) (hπk : πU.ker = Subgroup.center U) {x : G}
    (hxN : x ∈ Subgroup.normalizer (φ.range : Set G)) :
    ∃ (ρ : ↥φ.range →* P) (β : MulAut P), Function.Surjective ρ ∧
      ρ.ker = Subgroup.center ↥φ.range ∧ (∀ s, ρ (φ.rangeRestrict s) = πU s) ∧
      ∀ g h : ↥φ.range, (h : G) = x * g * x⁻¹ → ρ h = β (ρ g) := by
  classical
  obtain ⟨ρ, hρs, hρk, hρ⟩ := exists_centerQuot_hom hU φ hker πU hπ hπk
  let a : MulAut ↥φ.range := φ.range.normalizerMonoidHom ⟨x, hxN⟩
  have ha : ∀ g, ((a g : ↥φ.range) : G) = x * g * x⁻¹ := fun g => rfl
  have hZ : (Subgroup.center ↥φ.range).map a.toMonoidHom = Subgroup.center ↥φ.range :=
    Subgroup.characteristic_iff_map_eq.1 inferInstance a
  let eS := (QuotientGroup.quotientMulEquivOfEq hρk).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective ρ hρs)
  have heS : ∀ g, eS (QuotientGroup.mk g) = ρ g := fun g => rfl
  let αS : MulAut (↥φ.range ⧸ Subgroup.center ↥φ.range) := QuotientGroup.congr _ _ a hZ
  refine ⟨ρ, MulAut.congr eS αS, hρs, hρk, hρ, fun g h hgh => ?_⟩
  have hah : a g = h := Subtype.ext ((ha g).trans hgh.symm)
  have h1 : eS.symm (ρ g) = QuotientGroup.mk g := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  show ρ h = eS (αS (eS.symm (ρ g)))
  rw [h1, ← heS, show αS (QuotientGroup.mk g) = QuotientGroup.mk (a g) from
    QuotientGroup.congr_mk _ _ _ _ g, hah]

theorem pow_three_eq_one_of_conj {S : Type*} [Group S] {G₀ : Subgroup G} {x : G}
    (hx3 : x ^ 3 = 1) (hxN : x ∈ Subgroup.normalizer (G₀ : Set G)) (π : ↥G₀ →* S)
    (hπ : Function.Surjective π) (α : MulAut S)
    (hα : ∀ g h : ↥G₀, (h : G) = x * g * x⁻¹ → π h = α (π g)) : α ^ 3 = 1 := by
  have hmem : ∀ g : ↥G₀, x * (g : G) * x⁻¹ ∈ G₀ := fun g =>
    (Subgroup.mem_normalizer_iff.mp hxN g).mp g.2
  have hc : ∀ g : ↥G₀, π ⟨x * g * x⁻¹, hmem g⟩ = α (π g) := fun g => hα g _ rfl
  refine MulEquiv.ext fun s => ?_
  obtain ⟨g, rfl⟩ := hπ s
  have hg : (⟨x * (⟨x * (⟨x * g * x⁻¹, hmem g⟩ : ↥G₀) * x⁻¹, hmem _⟩ : ↥G₀) * x⁻¹, hmem _⟩ :
      ↥G₀) = g := Subtype.ext (by
    change x * (x * (x * (g : G) * x⁻¹) * x⁻¹) * x⁻¹ = g
    calc x * (x * (x * (g : G) * x⁻¹) * x⁻¹) * x⁻¹ = x * x * x * g * (x * x * x)⁻¹ := by group
      _ = g := by rw [← pow_three', hx3, one_mul, inv_one, mul_one])
  rw [pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply, ← hc, ← hc, ← hc, hg,
    MulAut.one_apply]

end Beta

section ConjU

variable {F : Type} [Field F] {f n : ℕ}

theorem unitarySU_eq_gramSU_one (h : UnitaryFieldData 2 f F) :
    unitarySU 2 f F n = gramSU h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
  rw [Units.val_one]
  exact unitarySU_eq_gramSU h n

@[expose] noncomputable def conjUnitary (h : UnitaryFieldData 2 f F)
    (A : primeFormUnitary h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :
    ↥(unitarySU 2 f F n) →* ↥(unitarySU 2 f F n) where
  toFun s := ⟨A * s * (A : GL (Fin n) F)⁻¹,
    (SetLike.ext_iff.mp (unitarySU_eq_gramSU_one h) _).mpr
      (conj_mem_gramSU h _ A.2 ((SetLike.ext_iff.mp (unitarySU_eq_gramSU_one h) _).mp s.2))⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem coe_conjUnitary (h : UnitaryFieldData 2 f F)
    (A : primeFormUnitary h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
    (s : ↥(unitarySU 2 f F n)) :
    ((conjUnitary h A s : ↥(unitarySU 2 f F n)) : GL (Fin n) F) = A * s * (A : GL (Fin n) F)⁻¹ :=
  rfl

theorem primeFormConjHom_projP (h : UnitaryFieldData 2 f F) (hn1 : 1 ≤ n)
    (A : primeFormUnitary h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
    (s : ↥(unitarySU 2 f F n)) :
    primeFormConjHom h _ A (OrdPFieldSU.projP h hn1 s) =
      OrdPFieldSU.projP h hn1 (conjUnitary h A s) := by
  rw [OrdPFieldSU.projP_apply h hn1 s (OrdPFieldSU.mem_gramSU_one h s), primeFormConjHom_mk,
    OrdPFieldSU.projP_apply h hn1 _ (OrdPFieldSU.mem_gramSU_one h _)]
  rfl

theorem conj_eq_of_conjHom {G : Type*} [Group G] (h : UnitaryFieldData 2 f F) (hn1 : 1 ≤ n)
    (hUperf : commutator ↥(unitarySU 2 f F n) = ⊤) (φ : ↥(unitarySU 2 f F n) →* G)
    (hπk : (OrdPFieldSU.projP h hn1).ker = Subgroup.center ↥(unitarySU 2 f F n)) {x : G}
    (hxN : x ∈ Subgroup.normalizer (φ.range : Set G))
    (A : primeFormUnitary h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
    (hβ : ∀ s s', φ s' = x * φ s * x⁻¹ →
      primeFormConjHom h _ A (OrdPFieldSU.projP h hn1 s) = OrdPFieldSU.projP h hn1 s')
    (s : ↥(unitarySU 2 f F n)) : x * φ s * x⁻¹ = φ (conjUnitary h A s) := by
  have hmem : ∀ s, x * φ s * x⁻¹ ∈ φ.range := fun s =>
    (Subgroup.mem_normalizer_iff.mp hxN (φ s)).mp ⟨s, rfl⟩
  let M : ↥(unitarySU 2 f F n) →* ↥φ.range :=
    { toFun := fun s => ⟨x * φ s * x⁻¹, hmem s⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hMN : φ.rangeRestrict.comp (conjUnitary h A) = M := by
    refine TypeA.eq_of_inv_mul_mem_center hUperf _ _ fun s => ?_
    obtain ⟨s', hs'⟩ := hmem s
    have h1 := hβ s s' hs'
    rw [primeFormConjHom_projP] at h1
    have h2 : (conjUnitary h A s)⁻¹ * s' ∈ Subgroup.center ↥(unitarySU 2 f F n) := by
      rw [← hπk, MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
    have h3 : (φ.rangeRestrict.comp (conjUnitary h A) s)⁻¹ * M s =
        φ.rangeRestrict ((conjUnitary h A s)⁻¹ * s') := by
      apply Subtype.ext
      simp only [MonoidHom.comp_apply, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv,
        MonoidHom.coe_rangeRestrict, M, MonoidHom.coe_mk, OneHom.coe_mk, hs']
    rw [h3, Subgroup.mem_center_iff]
    intro g
    obtain ⟨t, rfl⟩ := φ.rangeRestrict_surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp h2 t]
  have := congrArg (fun F' => ((F' s : ↥φ.range) : G)) hMN
  exact this.symm

end ConjU

section Frob

variable {F : Type} [Field F] [Finite F]

private theorem exists_pow_eight_ne (hF : Nat.card F = 64) : ∃ c : F, c ^ 8 ≠ c := by
  classical
  by_contra hcon
  push Not at hcon
  let _ := Fintype.ofFinite F
  have hp := FiniteField.X_pow_card_sub_X_ne_zero F (p := 8) (by norm_num)
  have hsub : (Finset.univ : Finset F).val ⊆
      (Polynomial.X ^ 8 - Polynomial.X : Polynomial F).roots := fun c _ => by
    rw [Polynomial.mem_roots hp, Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, hcon c, sub_self]
  have h1 := Polynomial.card_le_degree_of_subset_roots hsub
  rw [FiniteField.X_pow_card_sub_X_natDegree_eq F (p := 8) (by norm_num), Finset.card_univ,
    ← Nat.card_eq_fintype_card, hF] at h1
  omega

theorem frob_of_orderOf_eq_three [CharP F 2] (hF : Nat.card F = 64) {θ : F ≃+* F}
    (hθ : orderOf θ = 3) : (∀ c, θ c = c ^ 4) ∨ ∀ c, θ c = c ^ 16 := by
  classical
  let _ : Algebra (ZMod 2) F := ZMod.algebra F 2
  let θa : F ≃ₐ[ZMod 2] F :=
    { θ with
      commutes' := fun r => congrArg (fun g => g r)
        (RingHom.ext_zmod (θ.toRingHom.comp (algebraMap (ZMod 2) F)) (algebraMap (ZMod 2) F)) }
  obtain ⟨i, hi⟩ := FiniteField.exists_forall_apply_eq_pow (ZMod 2) 2 F θa
  have h2 : Nat.card (ZMod 2) = 2 := by simp
  have h64 : ∀ c : F, c ^ 64 = c := fun c => by
    let _ := Fintype.ofFinite F
    have hc : Fintype.card F = 64 := by rw [← Nat.card_eq_fintype_card, hF]
    rw [← hc]
    exact FiniteField.pow_card c
  have hred : ∀ q r (c : F), c ^ 2 ^ (r + 6 * q) = c ^ 2 ^ r := by
    intro q
    induction q with
    | zero => intro r c; simp
    | succ q ih =>
      intro r c
      rw [show r + 6 * (q + 1) = r + 6 * q + 6 by ring, pow_add, pow_mul, ih,
        show (2 : ℕ) ^ 6 = 64 by norm_num, h64]
  obtain ⟨r, hr6, hθr⟩ : ∃ r < 6, ∀ c, θ c = c ^ 2 ^ r := by
    refine ⟨i % 6, Nat.mod_lt _ (by norm_num), fun c => ?_⟩
    have hc := hi c
    rw [h2] at hc
    rw [show θ c = θa c from rfl, hc, ← hred (i / 6) (i % 6) c, Nat.mod_add_div]
  have hθ1 : θ ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hθ
    omega
  have hθ3 : ∀ c, θ (θ (θ c)) = c := fun c => by
    have h3 : θ ^ 3 = 1 := hθ ▸ pow_orderOf_eq_one θ
    have hc := DFunLike.congr_fun h3 c
    rwa [pow_succ, pow_succ, pow_one, RingAut.mul_apply, RingAut.mul_apply] at hc
  have hpow : ∀ (k : ℕ) (c : F), c ^ (64 * k) = c ^ k := fun k c => by rw [pow_mul, h64]
  have hodd : (∀ c : F, c ^ 8 = c) → False := fun h8 => by
    obtain ⟨c, hc⟩ := exists_pow_eight_ne hF
    exact hc (h8 c)
  interval_cases r
  · exact absurd (RingEquiv.ext fun c => by rw [hθr c]; simp) hθ1
  · exfalso
    refine hodd fun c => ?_
    have hc := hθ3 c
    rw [hθr, hθr, hθr, ← pow_mul, ← pow_mul] at hc
    norm_num at hc
    exact hc
  · exact Or.inl fun c => by rw [hθr]; norm_num
  · exfalso
    refine hodd fun c => ?_
    have hc := hθ3 c
    rw [hθr, hθr, hθr, ← pow_mul, ← pow_mul] at hc
    norm_num at hc
    rwa [show (512 : ℕ) = 64 * 8 by norm_num, hpow] at hc
  · exact Or.inr fun c => by rw [hθr]; norm_num
  · exfalso
    refine hodd fun c => ?_
    have hc := hθ3 c
    rw [hθr, hθr, hθr, ← pow_mul, ← pow_mul] at hc
    norm_num at hc
    rwa [show (32768 : ℕ) = 64 * (64 * 8) by norm_num, hpow, hpow] at hc

end Frob

section Fix

variable {F : Type} [Field F] [Finite F] {f n : ℕ}

theorem exists_fixed_subfield_component (h : UnitaryFieldData 2 f F) (hn : 4 ≤ n)
    {σ : F ≃+* F} (hσ : orderOf σ = 3)
    (H : primeFormUnitary h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
    {β : MulAut (primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))}
    (hβ : β = primeFormConjHom h _ H *
      primeFormFieldHom h (isPrimeFormGram_one (K := F) (n := n)) σ *
        (primeFormConjHom h _ H)⁻¹) :
    ∃ T₀ : Subgroup (primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)),
      (∀ t ∈ T₀, β t = t) ∧ IsSimpleGroup ↥T₀ ∧ ⁅T₀, T₀⁆ = T₀ ∧
      (∀ P : Subgroup (primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)),
        (∀ c ∈ P, β c = c) → ⁅P, P⁆ = P → P ≤ T₀) ∧ LieModel ↥T₀ .PSU n 2 (f / 3) := by
  classical
  subst hβ
  have hn3 : 3 ≤ n := by omega
  have hq₀ : ¬(n = 3 ∧ 2 ^ (f / 3) = 2) := fun h' => by omega
  have h₀ := fixSubfield_unitaryFieldData h Nat.prime_three (by norm_num) hσ
  have hbar := fixSubfield_unitaryFieldData_bar h Nat.prime_three (by norm_num) hσ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup (primeFormP h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (fixSubfield σ))) := isSimpleGroup_primeFormP_one h₀ hn3 hq₀
  have : Group.IsPerfect (gramSU h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (fixSubfield σ))) := isPerfect_gramSU_one h₀ hn3 hq₀
  have hperf₀ : commutator (primeFormP h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (fixSubfield σ))) = ⊤ :=
    (Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _)).commutator_eq_top
  set cH := primeFormConjHom h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) H with hcH
  set fσ := primeFormFieldHom h (isPrimeFormGram_one (K := F) (n := n)) σ with hfσ
  set j := subfieldPSU h h₀ hbar n with hj
  have hinv : ∀ z, cH⁻¹ (cH z) = z := fun z => by
    rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  have hinv' : ∀ z, cH (cH⁻¹ z) = z := fun z => by
    rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  let k := cH.toMonoidHom.comp j
  have hkinj : Function.Injective k :=
    cH.injective.comp (subfieldPSU_injective h h₀ hbar n (by omega))
  refine ⟨k.range, ?_, (MonoidHom.ofInjective hkinj).symm.isSimpleGroup, ?_, ?_, ?_⟩
  · rintro _ ⟨y, rfl⟩
    have hfix : fσ (j y) = j y := range_subfieldPSU_le h n h₀ hbar ⟨y, rfl⟩
    change cH (fσ (cH⁻¹ (cH (j y)))) = cH (j y)
    rw [hinv, hfix]
  · rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def, hperf₀]
  · intro P hP hPP c hc
    have hle : P.map (cH⁻¹).toMonoidHom ≤ fixSubgroup fσ := by
      rintro _ ⟨d, hd, rfl⟩
      rw [mem_fixSubgroup]
      have e := hP d hd
      rw [MulAut.mul_apply, MulAut.mul_apply] at e
      have e' := congrArg (fun z => cH⁻¹ z) e
      simp only [hinv] at e'
      exact e'
    have hmem : cH⁻¹ c ∈ ⁅P.map (cH⁻¹).toMonoidHom, P.map (cH⁻¹).toMonoidHom⁆ := by
      rw [← Subgroup.map_commutator, hPP]
      exact ⟨c, hc, rfl⟩
    obtain ⟨y, hy⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.S2019.commutator_fixSubgroup_primeFormFieldHom_le h n h₀ hbar
        (Subgroup.commutator_mono hle hle hmem)
    exact ⟨y, by
      change cH (j y) = c
      rw [hy, hinv']⟩
  · obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h₀
      (isPrimeFormGram_one (K := fixSubfield σ) (n := n))
    have hadm : StatedLieAdmissible .PSU n 2 (f / 3) :=
      ⟨h₀.prime, h₀.one_le, hn3, fun hc => hq₀ ⟨(Prod.mk.inj hc).1, (Prod.mk.inj hc).2⟩⟩
    exact (LieModel.classical_iff (by decide)).mpr ⟨hadm, fixSubfield σ, inferInstance,
      inferInstance, h₀.card_eq_sq,
      ⟨(MonoidHom.ofInjective hkinj).symm.trans (eP.trans (unitaryPSUEquiv h₀ (by omega)))⟩⟩

end Fix

section Chart

variable {F : Type} [Field F] {f n : ℕ}

theorem exists_frobenius_chart (h : UnitaryFieldData 2 f F)
    (hZ : normOneScalars h (gramSU h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) n = ⊥)
    {G : Type*} [Group G] {G₀ : Subgroup G}
    (ρ : ↥G₀ →* primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
    (hρ : Function.Bijective ρ) {x : G} (θ : F ≃+* F)
    (H : primeFormUnitary h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
    (β : MulAut (primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)))
    (hβH : β = primeFormConjHom h _ H *
      primeFormFieldHom h (isPrimeFormGram_one (K := F) (n := n)) θ *
        (primeFormConjHom h _ H)⁻¹)
    (hβ : ∀ g g' : ↥G₀, (g' : G) = x * g * x⁻¹ → ρ g' = β (ρ g)) :
    ∃ Θ : ↥G₀ ≃* ↥(SUid h.barEquiv n), ∀ (g : ↥G₀) (hg : x * (g : G) * x⁻¹ ∈ G₀),
      ((Θ ⟨x * g * x⁻¹, hg⟩ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        ((Θ g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map θ := by
  classical
  have hmkinj : Function.Injective (QuotientGroup.mk'
      (normOneScalars h (gramSU h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) n)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
    exact hZ
  obtain ⟨Θ₁, hΘ₁⟩ : ∃ Θ₁ : ↥G₀ ≃* gramSU h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F),
      ∀ g, ((Θ₁ g : gramSU h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :
        primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) = ρ g :=
    ⟨(MulEquiv.ofBijective ρ hρ).trans
        (MulEquiv.ofBijective _ ⟨hmkinj, QuotientGroup.mk'_surjective _⟩).symm,
      fun g => (MulEquiv.ofBijective _ ⟨hmkinj, QuotientGroup.mk'_surjective _⟩).apply_symm_apply
        (ρ g)⟩
  have hkey : ∀ (g : ↥G₀) (hg : x * (g : G) * x⁻¹ ∈ G₀),
      Θ₁ ⟨x * g * x⁻¹, hg⟩ = primeFormConjSU h _ H
        (primeFormFieldSU h (isPrimeFormGram_one (K := F) (n := n)) θ
          (primeFormConjSU h _ H⁻¹ (Θ₁ g))) := by
    intro g hg
    apply hmkinj
    change ((Θ₁ ⟨x * g * x⁻¹, hg⟩ : gramSU h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :
        primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) =
      ((primeFormConjSU h _ H (primeFormFieldSU h (isPrimeFormGram_one (K := F) (n := n)) θ
        (primeFormConjSU h _ H⁻¹ (Θ₁ g))) :
          gramSU h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :
            primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
    rw [hΘ₁, hβ g ⟨x * g * x⁻¹, hg⟩ rfl, ← hΘ₁ g, hβH, MulAut.mul_apply, MulAut.mul_apply,
      ← map_inv]
    change primeFormConjAut h _ H (primeFormFieldAut h (isPrimeFormGram_one (K := F) (n := n)) θ
      (primeFormConjAut h _ H⁻¹ ((Θ₁ g : gramSU h ((1 : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F)) : primeFormP h ((1 : GL (Fin n) F) :
          Matrix (Fin n) (Fin n) F)))) = _
    rw [primeFormConjAut_mk, primeFormFieldAut_mk, primeFormConjAut_mk]
  refine ⟨Θ₁.trans ((primeFormConjSU h _ H⁻¹).trans
    (MulEquiv.subgroupCongr (gramSU_one_eq_SUid h n))), fun g hg => ?_⟩
  rw [← coe_glAut]
  congr 1
  change (H : GL (Fin n) F)⁻¹ * (Θ₁ ⟨x * g * x⁻¹, hg⟩ : GL (Fin n) F) * ((H : GL (Fin n) F)⁻¹)⁻¹ =
    glAut θ ((H : GL (Fin n) F)⁻¹ * (Θ₁ g : GL (Fin n) F) * ((H : GL (Fin n) F)⁻¹)⁻¹)
  rw [hkey g hg]
  change (H : GL (Fin n) F)⁻¹ * ((H : GL (Fin n) F) * glAut θ ((H : GL (Fin n) F)⁻¹ *
      (Θ₁ g : GL (Fin n) F) * ((H : GL (Fin n) F)⁻¹)⁻¹) * (H : GL (Fin n) F)⁻¹) *
        ((H : GL (Fin n) F)⁻¹)⁻¹ =
    glAut θ ((H : GL (Fin n) F)⁻¹ * (Θ₁ g : GL (Fin n) F) * ((H : GL (Fin n) F)⁻¹)⁻¹)
  group

end Chart

section Main


theorem ggPsiInnerDiag_x_pz_su {G : Type} [Group G] [Finite G] {B Bs L D J : Subgroup G}
    {x : G} {m : ℕ} (hm : 5 ≤ m) (h3 : 3 ∣ m + 1) (hcfg : GGConfig 3 B Bs x L D J)
    (hNT : GGNoTransvection 3 Bs) (hPZ : GGSecFivePZData (ggG0 3 B x L D J) Bs L x m)
    {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
    (ψ : SU (unitaryInvolution F 2 f) n →* G)
    (hpres : GGPresentsG0 (ggG0 3 B x L D J) (rootDatum hF n) .PSU n f ψ) :
    GGPsiInnerDiag (rootDatum hF n) ψ x := by
  classical
  obtain ⟨⟨hadm, hrk⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
  have hrk' : 2 ≤ n / 2 := hrk
  have hn : 4 ≤ n := by omega
  have hf : 1 ≤ f := hadm.2.1
  have hn1 : 1 ≤ n := by omega
  have hn3 : 3 ≤ n := by omega
  have : NeZero n := ⟨by omega⟩
  have hq : ¬(n = 3 ∧ 2 ^ f = 2) := fun h' => by omega
  have hnq : (n, 2 ^ f) ≠ (3, 2) := fun h' => by
    have := congrArg Prod.fst h'
    simp only at this
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : UnitaryFieldData 2 f F := ⟨Nat.prime_two, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  obtain ⟨-, hBsEA, hxBs, -, -⟩ := hcfg.tableB_facts
  have hL := hcfg.isComponentOf_ggG0_inf
  have hxN : x ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) := hPZ.2.2.2.1 hxBs
  obtain ⟨P₀, hP₀⟩ := exists_wittMatrix hF n
  set φ := SURep.ggFrameU hF ψ P₀ hP₀ with hφ
  have hrφ' : φ.range = ψ.range := SURep.range_ggFrameU hF ψ P₀ hP₀
  generalize ggG0 3 B x L D J = G₀ at hPZ hL hxN hrange
  have hrφ : φ.range = G₀ := hrφ'.trans hrange
  subst hrφ
  have hkerφ : φ.ker ≤ Subgroup.center ↥(unitarySU 2 f F n) :=
    SURep.ker_ggFrameU_le hF ψ P₀ hP₀ hker
  have hUperf : commutator ↥(unitarySU 2 f F n) = ⊤ :=
    (CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hF hn3 hnq).commutator_eq_top
  set πU := OrdPFieldSU.projP h hn1 with hπU
  have hπk : πU.ker = Subgroup.center ↥(unitarySU 2 f F n) := by
    ext s
    rw [MonoidHom.mem_ker, hπU, OrdPFieldSU.projP_eq_one_iff,
      (isQuasisimple_statedSU_of_card hF hn3 hnq).2]
    exact Iff.rfl
  obtain ⟨ρ, β, hρs, hρk, hρ, hβ⟩ := exists_beta hUperf φ hkerφ πU
    (OrdPFieldSU.projP_surjective h hn1) hπk hxN
  have hC1 : IsPrimeFormGram (1 : GL (Fin n) F) := isPrimeFormGram_one
  obtain ⟨⟨A, θ⟩, hAθ⟩ := primeFormPsi_surjective h hC1 hn3 hq β
  rw [primeFormPsi_apply] at hAθ
  by_cases hθ1 : θ = 1
  ·
    subst hθ1
    rw [map_one, mul_one] at hAθ
    have hβA : ∀ s s', φ s' = x * φ s * x⁻¹ → primeFormConjHom h _ A (πU s) = πU s' := by
      intro s s' hss'
      rw [← hρ s, ← hρ s', hAθ]
      exact (hβ (φ.rangeRestrict s) (φ.rangeRestrict s') hss').symm
    have hconj := conj_eq_of_conjHom h hn1 hUperf φ hπk hxN A hβA
    refine OrdPFieldNsUD.ggPsiInnerDiag_of_frame_conj hF h hn hP₀ (A⁻¹).2 fun s s' hs' => ?_
    have e : conjUnitary h A s' = s := Subtype.ext (by
      rw [coe_conjUnitary, hs', InvMemClass.coe_inv]
      group)
    rw [← hφ, ← e, ← hconj s']
    group
  ·
    exfalso
    have hβ3 : β ^ 3 = 1 := pow_three_eq_one_of_conj (hBsEA.2 x hxBs) hxN ρ hρs β hβ
    obtain ⟨hθo, H, hH⟩ := RecipeFieldSpU.primeForm_conj_of_pow_eq_one h hn3 hq Nat.prime_three
      (by norm_num) A θ hθ1 (by rw [hAθ]; exact hβ3)
    have hβH : β = primeFormConjHom h _ H *
        primeFormFieldHom h (isPrimeFormGram_one (K := F) (n := n)) θ *
          (primeFormConjHom h _ H)⁻¹ := by
      rw [← hAθ]
      exact hH
    obtain ⟨T₀, hT₀α, hT₀, hT₀p, hperf, hT⟩ := exists_fixed_subfield_component h hn hθo H hβH
    obtain ⟨-, hnm, hf3⟩ := eq_psu_of_isComponentOf_fix_pz (by omega) hPZ hxN ρ hρs hρk.le β
      hβ hL hT₀α hT₀ hT₀p hperf hT
    have hf3' : f = 3 := by
      obtain ⟨k, hk⟩ := (dvd_and_card_fixSubfield_unitary h Nat.prime_three (by norm_num) hθo).1
      omega
    subst hf3' hnm
    have hF64 : Nat.card F = 64 := by
      rw [hF]
      norm_num
    have hcop : Nat.gcd n (2 ^ 3 + 1) = 1 := by
      have h3n : Nat.Coprime n 3 :=
        Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega))
      simpa using Nat.Coprime.pow_right 2 h3n
    have hZ : normOneScalars h (gramSU h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) n =
        ⊥ := by
      rw [← Subgroup.card_eq_one, card_normOneScalars_one h hn1, hcop]
    have hπinj : Function.Injective πU := by
      rw [injective_iff_map_eq_one]
      intro s hs
      rw [hπU, OrdPFieldSU.projP_apply h hn1 s (OrdPFieldSU.mem_gramSU_one h s),
        QuotientGroup.eq_one_iff, hZ, Subgroup.mem_bot] at hs
      exact Subtype.ext (congrArg (fun t : gramSU h ((1 : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) => (t : GL (Fin n) F)) hs)
    have hρinj : Function.Injective ρ := by
      rw [← MonoidHom.ker_eq_bot_iff, hρk, eq_bot_iff]
      intro z hz
      obtain ⟨s, rfl⟩ := φ.rangeRestrict_surjective z
      have hs := InnerDiagA.mem_center_of_rangeRestrict_mem_center hUperf φ hkerφ hz
      rw [← hπk, MonoidHom.mem_ker] at hs
      rw [Subgroup.mem_bot, hπinj (hs.trans (map_one πU).symm), map_one]
    obtain ⟨Θ, hΘx⟩ := exists_frobenius_chart h hZ ρ ⟨hρinj, hρs⟩ θ H β hβH hβ
    exact PZOrderNine.false_of_frobenius_orderNine_chart_of_card hF64 (σ := h.barEquiv)
      (fun c => by rw [h.barEquiv_apply, h.bar_apply]; norm_num) (by omega) Θ
      (frob_of_orderOf_eq_three hF64 hθo) hxN hΘx hBsEA hNT hxBs (E := Bs ⊓ L) inf_le_left
      hPZ.2.2.1.1.le (inf_le_right.trans (hL.1.trans inf_le_left)) hPZ.2.1.2

end Main

section Tag

theorem ggPsiInnerDiag_x_pz_PSU {G : Type} [Group G] [Finite G] {B Bs L D J : Subgroup G}
    {x : G} {m : ℕ} (hm : 5 ≤ m) (h3 : 3 ∣ m + 1) (hcfg : GGConfig 3 B Bs x L D J)
    (hNT : GGNoTransvection 3 Bs) (hPZ : GGSecFivePZData (ggG0 3 B x L D J) Bs L x m)
    {n f : ℕ} (ψ : (ggU .PSU n f).K →* G)
    (hpres : GGPresentsG0 (ggG0 3 B x L D J) (ggU .PSU n f).D .PSU n f ψ) :
    GGPsiInnerDiag (ggU .PSU n f).D ψ x := by
  by_cases hf : 1 ≤ f
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have e : ggU .PSU n f =
        ⟨SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
          rootDatum (card_galoisField_two_mul 2 f hf) n⟩ := by
      simp only [ggU, lieUniversal, hf, ↓reduceDIte]
    revert ψ
    rw [e]
    intro ψ hpres
    exact ggPsiInnerDiag_x_pz_su hm h3 hcfg hNT hPZ (card_galoisField_two_mul 2 f hf) ψ hpres
  · exact absurd hpres.1.1.2.1 hf

end Tag

end PZPSU

end CFSG.StandardType
