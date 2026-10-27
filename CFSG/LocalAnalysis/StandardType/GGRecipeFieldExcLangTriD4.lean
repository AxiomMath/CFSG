module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangReeF4
public import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm
public import CFSG.LieType.Chevalley.EvenDiagramFixedAmbientCentralizer
public import CFSG.LieType.Chevalley.DiagramCoordinateFixedStructure
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LieType.Chevalley.EvenCartanRootDiagonals
public import CFSG.LieType.Chevalley.TwistedE6NormalFormActors

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace RecipeExcLang

set_option linter.unusedSectionVars false


section Iterate

variable (t : TwistTag) {L : Type} [Field L]

theorem units_map_entrywiseHom_id (g : ModGL t.tag L) :
    Units.map (entrywiseHom (RingHom.id L)) g = g :=
  Units.ext (entrywise_id _)

theorem units_map_entrywiseHom_diagramMap_pow (Fr : L →+* L) (k : ℕ) :
    Units.map (entrywiseHom Fr) (diagramMap t L ^ k) = diagramMap t L ^ k := by
  rw [map_pow, units_map_entrywiseHom_diagramMap]

theorem exists_lang_twist [IsAlgClosed L] [CharP L 2] {e : ℕ} (he : 1 ≤ e) (j : ℕ) :
    ∃ S : MulAut (adjointGroup t.tag L), (∀ x : adjointGroup t.tag L, ∃ h, x = h⁻¹ * S h) ∧
      ∀ (k : ℕ) (g : adjointGroup t.tag L), (((S ^ k) g : adjointGroup t.tag L) :
        ModGL t.tag L) = diagramMap t L ^ (j * k) *
          Units.map (entrywiseHom ((iterateFrobenius L 2 e) ^ k)) g *
            (diagramMap t L ^ (j * k))⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS, hLang⟩ :=
    (CFSG.LieType.AlgebraicGroups.exceptional_all_characteristic_field_Lang_surjectivity 2 L e
      he).2 t (j : ℤ)
  refine ⟨S, hLang, fun k => ?_⟩
  induction k with
  | zero =>
    intro g
    rw [pow_zero, MulAut.one_apply, mul_zero, pow_zero, pow_zero, RingHom.one_def,
      units_map_entrywiseHom_id]
    group
  | succ k ih =>
    intro g
    rw [pow_succ', MulAut.mul_apply, hS, ih, zpow_natCast, map_mul, map_mul, map_inv,
      units_map_entrywiseHom_diagramMap_pow, units_map_entrywiseHom_comp,
      pow_succ' (iterateFrobenius L 2 e), RingHom.mul_def, mul_add, mul_one, pow_add]
    group

end Iterate

section D4

variable {K : Type} [Field K] [Finite K]

theorem ringEquiv_cube_eq_D4 {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ n)) (c : K) : σ (σ (σ c)) = c := by
  have : Fintype K := Fintype.ofFinite K
  rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul, show 2 ^ n * (2 ^ n * 2 ^ n) = (2 ^ n) ^ 3 by ring,
    ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]

theorem mem_range_of_twist_fixed_D4 {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (L : Type) [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    {h : ModGL TwistTag.D4.tag L} (hh : h ∈ adjointGroup TwistTag.D4.tag L)
    (hF : twistHom TwistTag.D4 L Fr h = h) :
    ∃ g ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      baseChangeGL (algebraMap K L) g = h := by
  have hK3 : Nat.card K = 2 ^ (n * 3) := by rw [hK, ← pow_mul]
  have : CharP K 2 := charP_two_of_card hK3
  have h3 := Function.iterate_fixed hF 3
  rw [CFSG.LieType.Chevalley.twistHom_iterate] at h3
  have hP3 : diagramMap TwistTag.D4 L ^ 3 = 1 := diagramMap_pow_order TwistTag.D4 L
  rw [hP3, one_mul, inv_one, mul_one] at h3
  have hFr3 : ∀ c : L, (Fr ^ 3) c = c ^ Nat.card K := fun c => by
    rw [RingHom.coe_pow]
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq, hFr]
    rw [← pow_mul, ← pow_mul, hK]
    ring
  obtain ⟨a, u, ⟨j, hj, rfl⟩, hu⟩ :=
    exists_rootDiagUnit_mul_of_frobenius_fixed TwistTag.D4.tag (Fr ^ 3) hFr3 hh h3
  have hT := (even_power_two_Cartan_root_diagonals_inner TwistTag.D4.tag
    (Or.inr (Or.inr (Or.inl rfl))) K (ringChar.eq K 2)).1 a
  have hle : torusGroup TwistTag.D4.tag K ≤ adjointGroup TwistTag.D4.tag K :=
    (Subgroup.closure_le _).2 fun _ ⟨q, hq⟩ => hq ▸ torusElt_mem_adjointGroup q.1 q.2
  have hgC : rootDiagUnit TwistTag.D4.tag a * j ∈ adjointGroup TwistTag.D4.tag K :=
    mul_mem (hle hT) hj
  have hι : baseChangeGL (algebraMap K L) (rootDiagUnit TwistTag.D4.tag a * j) = h := by
    rw [map_mul, hu]
  have hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L) :=
    RingHom.ext fun c => by
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hσ, hFr,
        map_pow]
  have hFg : twistHom TwistTag.D4 K σ.toRingHom (rootDiagUnit TwistTag.D4.tag a * j) =
      rootDiagUnit TwistTag.D4.tag a * j := by
    apply baseChangeGL_injective (algebraMap K L)
    rw [← twistHom_baseChangeGL (algebraMap K L) hcomm, hι, hF]
  obtain ⟨hTC, -⟩ := even_triality_fixed_group_eq_root_group K (ringChar.eq K 2) σ
    (ringEquiv_cube_eq_D4 hK σ hσ)
  refine ⟨rootDiagUnit TwistTag.D4.tag a * j, ?_, hι⟩
  rw [← hTC]
  exact ⟨hgC, hFg⟩

theorem entrywise_mem_twistedFixedGroup_D4 (σ δ : K ≃+* K) {X : ModGL TwistTag.D4.tag K}
    (hX : X ∈ twistedFixedGroup TwistTag.D4 K σ.toRingHom) :
    Units.map (entrywiseHom δ.toRingHom) X ∈ twistedFixedGroup TwistTag.D4 K σ.toRingHom := by
  obtain ⟨hC, hF⟩ := hX
  refine ⟨entrywise_mem_adjointGroup δ hC, ?_⟩
  change twistHom TwistTag.D4 K σ.toRingHom (Units.map (entrywiseHom δ.toRingHom) X) =
    Units.map (entrywiseHom δ.toRingHom) X
  have hF' : twistHom TwistTag.D4 K σ.toRingHom X = X := hF
  have hδσ : δ.toRingHom.comp σ.toRingHom = σ.toRingHom.comp δ.toRingHom := by
    have h := ringEquiv_mul_comm_of_finite δ σ
    exact congrArg RingEquiv.toRingHom h
  conv_rhs => rw [← hF']
  rw [twistHom_apply, twistHom_apply, map_mul, map_mul, map_inv,
    units_map_entrywiseHom_diagramMap, units_map_entrywiseHom_comp,
    units_map_entrywiseHom_comp, hδσ]

theorem diagramMap_pow_conj_D4 {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ n)) (j : ℕ) {X : ModGL TwistTag.D4.tag K}
    (hX : X ∈ twistedFixedGroup TwistTag.D4 K σ.toRingHom) :
    diagramMap TwistTag.D4 K ^ j * X * (diagramMap TwistTag.D4 K ^ j)⁻¹ =
      Units.map (entrywiseHom (σ ^ (2 * j)).toRingHom) X := by
  have hσ3 : (σ ^ 2).toRingHom.comp σ.toRingHom = RingHom.id K := RingHom.ext fun c => by
    change (σ ^ 2) (σ c) = c
    rw [pow_two]
    exact ringEquiv_cube_eq_D4 hK σ hσ c
  have hone : ∀ {Y : ModGL TwistTag.D4.tag K},
      Y ∈ twistedFixedGroup TwistTag.D4 K σ.toRingHom →
      diagramMap TwistTag.D4 K * Y * (diagramMap TwistTag.D4 K)⁻¹ =
        Units.map (entrywiseHom (σ ^ 2).toRingHom) Y := by
    intro Y hY
    have hF : twistHom TwistTag.D4 K σ.toRingHom Y = Y := hY.2
    conv_rhs => rw [← hF]
    rw [twistHom_apply, map_mul, map_mul, map_inv, units_map_entrywiseHom_diagramMap,
      units_map_entrywiseHom_comp, hσ3, units_map_entrywiseHom_id]
  induction j generalizing X with
  | zero =>
    rw [pow_zero, one_mul, inv_one, mul_one, mul_zero, pow_zero]
    exact (units_map_entrywiseHom_id TwistTag.D4 X).symm
  | succ j ih =>
    have e1 : diagramMap TwistTag.D4 K ^ (j + 1) * X * (diagramMap TwistTag.D4 K ^ (j + 1))⁻¹ =
        diagramMap TwistTag.D4 K * (diagramMap TwistTag.D4 K ^ j * X *
          (diagramMap TwistTag.D4 K ^ j)⁻¹) * (diagramMap TwistTag.D4 K)⁻¹ := by
      rw [pow_succ']
      group
    rw [e1, ih hX, hone (entrywise_mem_twistedFixedGroup_D4 σ _ hX),
      units_map_entrywiseHom_comp]
    congr 2
    rw [show 2 * (j + 1) = 2 + 2 * j by ring, pow_add]
    rfl

theorem ringEquiv_pow_sq_apply {φ : K ≃+* K} (hφ : ∀ c, φ c = c ^ 2) (k : ℕ) (c : K) :
    (φ ^ k) c = c ^ (2 ^ k) := by
  rw [ringEquiv_pow_apply]
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', ih, hφ, ← pow_mul, pow_succ]

theorem exists_conj_eq_fieldActor_D4_frob {n p e j : ℕ} (hK : Nat.card K = (2 ^ n) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (φ : K ≃+* K) (hφ : ∀ c, φ c = c ^ 2)
    (hp : 1 ≤ p) (he : 1 ≤ e) (hep : e * p = n) (hjp : j * p % 3 = 1)
    (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hx : (MulAut.conj x * fieldActor σ (σ ^ (2 * j) * φ ^ e)) ^ p = 1) :
    ∃ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      MulAut.conj g * (MulAut.conj x * fieldActor σ (σ ^ (2 * j) * φ ^ e)) *
        (MulAut.conj g)⁻¹ = fieldActor σ (σ ^ (2 * j) * φ ^ e) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hK3 : Nat.card K = 2 ^ (n * 3) := by rw [hK, ← pow_mul]
  have : CharP K 2 := charP_two_of_card hK3
  set L := AlgebraicClosure K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  set τ₀ := σ ^ (2 * j) * φ ^ e with hτ₀
  have hσφ : σ = φ ^ n := RingEquiv.ext fun c => by rw [hσ, ringEquiv_pow_sq_apply hφ]
  have hφ3n : φ ^ (3 * n) = 1 := RingEquiv.ext fun c => by
    rw [ringEquiv_pow_sq_apply hφ, RingAut.one_apply, show 2 ^ (3 * n) = (2 ^ n) ^ 3 by ring,
      ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hτφ : τ₀ = φ ^ (n * (2 * j) + e) := by rw [hτ₀, hσφ, ← pow_mul, pow_add]
  have hτp : τ₀ ^ p = 1 := by
    obtain ⟨k, hk⟩ : 3 ∣ 2 * (j * p) + 1 := by omega
    have hm : (n * (2 * j) + e) * p = 3 * n * k := by
      calc (n * (2 * j) + e) * p = n * (2 * (j * p) + 1) := by rw [← hep]; ring
        _ = 3 * n * k := by rw [hk]; ring
    rw [hτφ, ← pow_mul, hm, pow_mul, hφ3n, one_pow]
  obtain ⟨S, hLang, hSk⟩ := exists_lang_twist TwistTag.D4 (L := L) he j
  have hCadj : ∀ {c : ModGL TwistTag.D4.tag K},
      c ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom → c ∈ adjointGroup TwistTag.D4.tag K :=
    fun hc => (graphFixedRootGroup_le TwistTag.D4 K σ.toRingHom hc).1
  let ι : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →* adjointGroup TwistTag.D4.tag L :=
    ((baseChangeGL (algebraMap K L)).comp
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype).codRestrict _ fun c =>
        baseChangeGL_mem_adjointGroup (algebraMap K L) (hCadj c.2)
  have hι : ∀ c : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (ι c : ModGL TwistTag.D4.tag L) = baseChangeGL (algebraMap K L) c := fun _ => rfl
  have hιinj : Function.Injective ι := fun a b hab =>
    Subtype.ext (baseChangeGL_injective (algebraMap K L) (congrArg Subtype.val hab))
  have hFrc : (iterateFrobenius L 2 e).comp (algebraMap K L) =
      (algebraMap K L).comp (φ ^ e).toRingHom := by
    ext c
    rw [RingHom.comp_apply, RingHom.comp_apply, iterateFrobenius_def]
    change (algebraMap K L c) ^ 2 ^ e = algebraMap K L ((φ ^ e) c)
    rw [ringEquiv_pow_sq_apply hφ, map_pow]
  have heF₀ : ∀ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      ι (fieldActor σ τ₀ g) = S (ι g) := by
    intro g
    have hS1 := hSk 1 (ι g)
    rw [pow_one, pow_one, mul_one] at hS1
    have hX : Units.map (entrywiseHom (φ ^ e).toRingHom) (g : ModGL TwistTag.D4.tag K) ∈
        twistedFixedGroup TwistTag.D4 K σ.toRingHom :=
      entrywise_mem_twistedFixedGroup_D4 σ (φ ^ e) (graphFixedRootGroup_le _ _ _ g.2)
    have h1 : Units.map (entrywiseHom (iterateFrobenius L 2 e))
        (baseChangeGL (algebraMap K L) (g : ModGL TwistTag.D4.tag K)) =
          baseChangeGL (algebraMap K L)
            (Units.map (entrywiseHom (φ ^ e).toRingHom) (g : ModGL TwistTag.D4.tag K)) := by
      rw [units_map_entrywiseHom_eq_baseChangeGL, units_map_entrywiseHom_eq_baseChangeGL,
        baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, hFrc]
    have h2 : diagramMap TwistTag.D4 L ^ j =
        baseChangeGL (algebraMap K L) (diagramMap TwistTag.D4 K ^ j) := by
      rw [map_pow, baseChangeGL_diagramMap]
    apply Subtype.ext
    rw [hS1, hι, hι, coe_fieldActor, h1, h2, ← map_inv, ← map_mul, ← map_mul,
      diagramMap_pow_conj_D4 hK σ hσ j hX, units_map_entrywiseHom_comp]
    rfl
  have hP : diagramMap TwistTag.D4 L ^ (j * p) = diagramMap TwistTag.D4 L := by
    have h1 : j * p = 3 * (j * p / 3) + 1 := by omega
    rw [h1, pow_add, pow_mul, show (3 : ℕ) = TwistTag.D4.order from rfl,
      diagramMap_pow_order, one_pow, one_mul, pow_one]
  have hFrn : (iterateFrobenius L 2 e) ^ p = iterateFrobenius L 2 n := RingHom.ext fun c => by
    rw [RingHom.coe_pow, iterateFrobenius_def]
    have hit : ∀ k : ℕ, (⇑(iterateFrobenius L 2 e))^[k] c = c ^ ((2 ^ e) ^ k) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Function.iterate_succ_apply', ih, iterateFrobenius_def, pow_succ, pow_mul]
    rw [hit, ← pow_mul, hep]
  have hmem : ∀ h : adjointGroup TwistTag.D4.tag L, (S ^ p) h = h → h ∈ ι.range := by
    intro h hh
    have hfix : twistHom TwistTag.D4 L (iterateFrobenius L 2 n) h = h := by
      rw [twistHom_apply, ← hFrn, ← hP, ← hSk p h, hh]
    obtain ⟨g, hg, hgι⟩ := mem_range_of_twist_fixed_D4 hK σ hσ L (iterateFrobenius L 2 n)
      (fun c => by rw [iterateFrobenius_def]) h.2 hfix
    exact ⟨⟨g, hg⟩, Subtype.ext hgι⟩
  have hF₀p : fieldActor (t := TwistTag.D4) σ τ₀ ^ p = 1 := by
    rw [← fieldActorHom_apply (t := TwistTag.D4), ← map_pow, hτp, map_one]
  exact CFSG.RankThree.PartOne.KE.exists_inner_conj_eq_of_lang
    (exceptional_fixed_center_trivial TwistTag.D4 K σ) (fieldActor σ τ₀) hp hF₀p S hLang ι
    hιinj heF₀ hmem x hx

theorem exists_conj_eq_fieldActor_D4 {n p : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (hp : p.Prime) (hp3 : p ≠ 3) (δ : K ≃+* K)
    (hδ : orderOf δ = p) (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hx : (MulAut.conj x * fieldActor σ δ) ^ p = 1) :
    ∃ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      MulAut.conj g * (MulAut.conj x * fieldActor σ δ) * (MulAut.conj g)⁻¹ = fieldActor σ δ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have hK3 : Nat.card K = 2 ^ (3 * n) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨φ, hφ, hφord, hφtop, hcardAut, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega) hK3
  have hcyc : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.2 ⟨φ, hφtop⟩
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  have hp3n : p ∣ 3 * n := by
    rw [← hδ, ← hcardAut]
    exact orderOf_dvd_natCard δ
  have hpn : p ∣ n := ((Nat.coprime_primes hp Nat.prime_three).2 hp3).dvd_of_dvd_mul_left hp3n
  set e := n / p with he
  have hep : e * p = n := Nat.div_mul_cancel hpn
  have he1 : 1 ≤ e := Nat.div_pos (Nat.le_of_dvd (by omega) hpn) hp.pos
  have hen : e < n := Nat.div_lt_self (by omega) hp.one_lt
  have hp0 : p % 3 ≠ 0 := fun h0 =>
    hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.dvd_of_mod_eq_zero h0)).symm
  have hjp : p % 3 * p % 3 = 1 := by
    rw [Nat.mul_mod, Nat.mod_mod]
    have h1 : p % 3 = 1 ∨ p % 3 = 2 := by omega
    rcases h1 with h1 | h1 <;> rw [h1]
  set j := p % 3 with hj
  set τ₀ := σ ^ (2 * j) * φ ^ e with hτ₀
  have hσφ : σ = φ ^ n := RingEquiv.ext fun c => by rw [hσ, ringEquiv_pow_sq_apply hφ]
  have hφ3n : φ ^ (3 * n) = 1 := by rw [← hφord]; exact pow_orderOf_eq_one φ
  have hτφ : τ₀ = φ ^ (n * (2 * j) + e) := by rw [hτ₀, hσφ, ← pow_mul, pow_add]
  have hτp : τ₀ ^ p = 1 := by
    obtain ⟨k, hk⟩ : 3 ∣ 2 * (j * p) + 1 := by omega
    have hm : (n * (2 * j) + e) * p = 3 * n * k := by
      calc (n * (2 * j) + e) * p = n * (2 * (j * p) + 1) := by rw [← hep]; ring
        _ = 3 * n * k := by rw [hk]; ring
    rw [hτφ, ← pow_mul, hm, pow_mul, hφ3n, one_pow]
  have hτ1 : τ₀ ≠ 1 := by
    intro h1
    rw [hτφ] at h1
    have hdvd := orderOf_dvd_of_pow_eq_one h1
    rw [hφord] at hdvd
    have hne : n ∣ e := (Nat.dvd_add_right (dvd_mul_right n (2 * j))).1
      ((dvd_mul_left n 3).trans hdvd)
    exact absurd (Nat.le_of_dvd he1 hne) (by omega)
  have hτord : orderOf τ₀ = p := orderOf_eq_prime hτp hτ1
  have hzz : Subgroup.zpowers τ₀ = Subgroup.zpowers δ :=
    (IsCyclic.subgroup_eq_iff_card_eq).2 (by rw [Nat.card_zpowers, Nat.card_zpowers, hτord, hδ])
  obtain ⟨r, hr⟩ : ∃ r : ℕ, δ ^ r = τ₀ := by
    have h : τ₀ ∈ Subgroup.zpowers δ := hzz ▸ Subgroup.mem_zpowers τ₀
    rw [← mem_powers_iff_mem_zpowers] at h
    exact h
  obtain ⟨r', hr'⟩ : ∃ r' : ℕ, τ₀ ^ r' = δ := by
    have h : δ ∈ Subgroup.zpowers τ₀ := hzz ▸ Subgroup.mem_zpowers δ
    rw [← mem_powers_iff_mem_zpowers] at h
    exact h
  set x' := ((List.range r).map fun i => (fieldActor (t := TwistTag.D4) σ δ ^ i) x).prod
    with hx'
  have hβr : (MulAut.conj x * fieldActor σ δ) ^ r = MulAut.conj x' * fieldActor σ τ₀ := by
    rw [CFSG.RankThree.PartOne.KE.conj_mul_pow_aut, ← fieldActorHom_apply (t := TwistTag.D4),
      ← map_pow, hr]
    rfl
  have hβrp : (MulAut.conj x' * fieldActor σ τ₀) ^ p = 1 := by
    rw [← hβr, ← pow_mul, mul_comm, pow_mul, hx, one_pow]
  obtain ⟨g, hg⟩ := exists_conj_eq_fieldActor_D4_frob hK σ hσ φ hφ hp.one_lt.le he1 hep hjp x'
    hβrp
  rw [← hτ₀] at hg
  have hrr : (MulAut.conj x * fieldActor σ δ) ^ (r * r') = MulAut.conj x * fieldActor σ δ := by
    have hσrr : δ ^ (r * r') = δ ^ 1 := by rw [pow_mul, hr, hr', pow_one]
    rw [pow_eq_pow_iff_modEq, hδ] at hσrr
    have hdvd : orderOf (MulAut.conj x * fieldActor σ δ) ∣ p := orderOf_dvd_of_pow_eq_one hx
    have h2 := Nat.ModEq.of_dvd hdvd hσrr
    rw [← pow_eq_pow_iff_modEq, pow_one] at h2
    exact h2
  refine ⟨g, ?_⟩
  rw [← hrr, pow_mul, hβr, ← conj_pow, hg, ← fieldActorHom_apply (t := TwistTag.D4), ← map_pow,
    hr', fieldActorHom_apply]

end D4

end RecipeExcLang

end CFSG.StandardType
