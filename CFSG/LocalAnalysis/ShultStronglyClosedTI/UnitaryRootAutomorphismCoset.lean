module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphismAut

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open scoped Pointwise commutatorElement

universe u

variable {K : Type u} [Field K] (J : HermitianForm 3 K) {V : Type*} [Group V]
  (φ : hermitianUnipotentCoord J ≃* V)

@[expose] def fieldInvolution : MulAut V :=
  (φ.symm.trans (rootTau J)).trans φ

theorem symm_fieldInvolution_apply (v : V) :
    φ.symm (fieldInvolution J φ v) = rootTau J (φ.symm v) :=
  φ.symm_apply_apply _

theorem fieldInvolution_mul_self : fieldInvolution J φ * fieldInvolution J φ = 1 :=
  MulEquiv.ext fun v => φ.symm.injective (by
    rw [MulAut.mul_apply, symm_fieldInvolution_apply, symm_fieldInvolution_apply, MulAut.one_apply,
      ← MulAut.mul_apply, rootTau_mul_self, MulAut.one_apply])

variable {G : Type*} [Group G] (ι : V →* G) (t : G)

@[expose] def rootCenterIn : Subgroup G :=
  (rootCenter J φ).map ι

@[expose] def involutionCoset : Set G :=
  t • (rootCenterIn J φ ι : Set G)

@[expose] def involutionCosetNormalizer : Subgroup V :=
  (Subgroup.normalizer (involutionCoset J φ ι t)).comap ι

@[expose] def involutionCosetHull : Subgroup G :=
  (involutionCosetNormalizer J φ ι t).map ι ⊔ Subgroup.zpowers t

@[expose] def involutionCosets : Set (Set G) :=
  {S | ∃ x ∈ involutionCosetNormalizer J φ ι t, S = (t * ι x) • (rootCenterIn J φ ι : Set G)}

section Hypotheses

variable {J φ ι t}
variable (hι : Function.Injective ι) (ht : t ^ 2 = 1)
  (htι : ∀ v, t * ι v * t⁻¹ = ι (fieldInvolution J φ v))
include hι ht htι

omit hι htι in
theorem inv_eq_self_of_sq : t⁻¹ = t :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_two, ht])

omit hι in
theorem mul_eq_mul_fieldInvolution (v : V) : ι v * t = t * ι (fieldInvolution J φ v) := by
  rw [← htι, inv_eq_self_of_sq ht, ← mul_assoc, ← mul_assoc, ← pow_two, ht, one_mul]

omit hι in
theorem conj_mul_eq (v x : V) :
    ι v * (t * ι x) * (ι v)⁻¹ = t * ι (fieldInvolution J φ v * x * v⁻¹) := by
  rw [← mul_assoc, mul_eq_mul_fieldInvolution ht htι, map_mul, map_mul, map_inv]
  group

omit ht htι in
theorem smul_rootCenterIn_eq_iff (x y : V) :
    (t * ι x) • (rootCenterIn J φ ι : Set G) = (t * ι y) • (rootCenterIn J φ ι : Set G) ↔
      (φ.symm x).1.1 = (φ.symm y).1.1 := by
  rw [leftCoset_eq_iff, mul_inv_rev, mul_assoc, inv_mul_cancel_left, ← map_inv, ← map_mul,
    rootCenterIn, Subgroup.mem_map_iff_mem hι, mem_rootCenter, map_mul, map_inv, fst_mul, fst_inv,
    neg_add_eq_zero]

omit hι ht htι in
variable (φ) in
theorem conj_image_rootCenterIn (v : V) :
    MulAut.conj (ι v) '' (rootCenterIn J φ ι : Set G) = rootCenterIn J φ ι := by
  refine Set.EqOn.image_eq_self fun e he => ?_
  obtain ⟨e, he, rfl⟩ := he
  have hcomm : φ.symm (v * e * v⁻¹) = φ.symm e := by
    rw [map_mul, map_mul, map_inv, mul_assoc, mul_comm_of_fst_eq_zero J (z := φ.symm e) he,
      mul_inv_cancel_left]
  rw [MulAut.conj_apply, id, ← map_inv, ← map_mul, ← map_mul, φ.symm.injective hcomm]

omit hι in
theorem conj_image_smul (v x : V) :
    MulAut.conj (ι v) '' ((t * ι x) • (rootCenterIn J φ ι : Set G)) =
      (t * ι (fieldInvolution J φ v * x * v⁻¹)) • (rootCenterIn J φ ι : Set G) := by
  rw [Set.image_smul_distrib, conj_image_rootCenterIn, MulAut.conj_apply, conj_mul_eq ht htι]

omit hι ht htι in
theorem fst_fieldInvolution_mul (v x : V) :
    (φ.symm (fieldInvolution J φ v * x * v⁻¹)).1.1 =
      J.conj (φ.symm v).1.1 + (φ.symm x).1.1 - (φ.symm v).1.1 := by
  rw [map_mul, map_mul, map_inv, fst_mul, fst_mul, fst_inv, symm_fieldInvolution_apply,
    fst_rootTau]
  ring

omit hι ht htι in
variable (φ ι t) in
theorem involutionCoset_eq :
    involutionCoset J φ ι t = (t * ι 1) • (rootCenterIn J φ ι : Set G) := by
  rw [map_one, mul_one]
  rfl

theorem mem_involutionCosetNormalizer (v : V) :
    v ∈ involutionCosetNormalizer J φ ι t ↔ J.conj (φ.symm v).1.1 = (φ.symm v).1.1 := by
  rw [involutionCosetNormalizer, Subgroup.mem_comap, Subgroup.mem_normalizer_iff_conj_image_eq,
    involutionCoset_eq,
    conj_image_smul ht htι, smul_rootCenterIn_eq_iff hι, fst_fieldInvolution_mul, map_one, fst_one,
    add_zero, sub_eq_zero]

theorem involutionCosetNormalizer_mul_comm {x y : V} (hx : x ∈ involutionCosetNormalizer J φ ι t)
    (hy : y ∈ involutionCosetNormalizer J φ ι t) : x * y = y * x := by
  rw [mem_involutionCosetNormalizer hι ht htι] at hx hy
  refine φ.symm.injective (coord_ext ?_ ?_)
  · rw [map_mul, map_mul, fst_mul, fst_mul, add_comm]
  · rw [map_mul, map_mul, snd_mul, snd_mul, hx, hy]
    ring

section CharTwo

variable [CharP K 2]

omit hι ht htι in
variable (φ) in
theorem orderOf_eq_two_iff_mem_rootCenter (v : V) :
    orderOf v = 2 ↔ v ∈ rootCenter J φ ∧ v ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [orderOf_eq_prime_iff, mem_rootCenter, ← pow_two_eq_one_iff J, ← map_pow,
    MulEquiv.map_eq_one_iff]

theorem fieldInvolution_eq_inv {x : V} (hx : x ∈ involutionCosetNormalizer J φ ι t) :
    fieldInvolution J φ x = x⁻¹ := by
  rw [mem_involutionCosetNormalizer hι ht htι] at hx
  refine φ.symm.injective (coord_ext ?_ ?_)
  · rw [symm_fieldInvolution_apply, fst_rootTau, map_inv, fst_inv, hx, CharTwo.neg_eq]
  · rw [symm_fieldInvolution_apply, snd_rootTau, map_inv, snd_inv]

theorem conj_eq_inv {x : V} (hx : x ∈ involutionCosetNormalizer J φ ι t) :
    t * ι x * t⁻¹ = ι x⁻¹ := by
  rw [htι, fieldInvolution_eq_inv hι ht htι hx]

theorem mem_involutionCosetHull_iff (g : G) :
    g ∈ involutionCosetHull J φ ι t ↔
      ∃ x ∈ involutionCosetNormalizer J φ ι t, g = ι x ∨ g = t * ι x := by
  set U := involutionCosetNormalizer J φ ι t
  have htx : ∀ x ∈ U, ι x * t = t * ι x⁻¹ := fun x hx => by
    rw [mul_eq_mul_fieldInvolution ht htι, fieldInvolution_eq_inv hι ht htι hx]
  let S : Subgroup G :=
    { carrier := {g | ∃ x ∈ U, g = ι x ∨ g = t * ι x}
      one_mem' := ⟨1, U.one_mem, Or.inl (map_one ι).symm⟩
      mul_mem' := by
        rintro _ _ ⟨x, hx, rfl | rfl⟩ ⟨y, hy, rfl | rfl⟩
        · exact ⟨x * y, U.mul_mem hx hy, Or.inl (map_mul ι x y).symm⟩
        · refine ⟨x⁻¹ * y, U.mul_mem (U.inv_mem hx) hy, Or.inr ?_⟩
          rw [← mul_assoc, htx x hx, mul_assoc, ← map_mul]
        · exact ⟨x * y, U.mul_mem hx hy, Or.inr (by rw [mul_assoc, ← map_mul])⟩
        · refine ⟨x⁻¹ * y, U.mul_mem (U.inv_mem hx) hy, Or.inl ?_⟩
          rw [mul_assoc, ← mul_assoc (ι x), htx x hx, ← mul_assoc, ← mul_assoc, ← pow_two, ht,
            one_mul, ← map_mul]
      inv_mem' := by
        rintro _ ⟨x, hx, rfl | rfl⟩
        · exact ⟨x⁻¹, U.inv_mem hx, Or.inl (map_inv ι x).symm⟩
        · refine ⟨x, hx, Or.inr ?_⟩
          rw [mul_inv_rev, inv_eq_self_of_sq ht, ← map_inv, htx _ (U.inv_mem hx), inv_inv] }
  constructor
  · intro hg
    have hle : involutionCosetHull J φ ι t ≤ S := by
      refine sup_le ?_ (Subgroup.zpowers_le.mpr ⟨1, U.one_mem, Or.inr (by rw [map_one, mul_one])⟩)
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, hx, Or.inl rfl⟩
    exact hle hg
  · rintro ⟨x, hx, rfl | rfl⟩
    · exact Subgroup.mem_sup_left (Subgroup.mem_map_of_mem ι hx)
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
        (Subgroup.mem_sup_left (Subgroup.mem_map_of_mem ι hx))

theorem mul_pow_two_eq_one {x : V} (hx : x ∈ involutionCosetNormalizer J φ ι t) :
    (t * ι x) ^ 2 = 1 := by
  rw [pow_two, mul_assoc, ← mul_assoc (ι x), mul_eq_mul_fieldInvolution ht htι,
    fieldInvolution_eq_inv hι ht htι hx, ← mul_assoc, ← mul_assoc, ← pow_two, ht, one_mul,
    ← map_mul, inv_mul_cancel, map_one]

theorem sq_mem_rootCenterIn {g : G} (hg : g ∈ involutionCosetHull J φ ι t) :
    g ^ 2 ∈ rootCenterIn J φ ι := by
  obtain ⟨x, hx, rfl | rfl⟩ := (mem_involutionCosetHull_iff hι ht htι g).mp hg
  · rw [← map_pow]
    exact Subgroup.mem_map_of_mem ι (by
      rw [mem_rootCenter, map_pow]
      exact fst_pow_two J _)
  · rw [mul_pow_two_eq_one hι ht htι hx]
    exact Subgroup.one_mem _

theorem pow_four_eq_one_of_mem_hull {g : G} (hg : g ∈ involutionCosetHull J φ ι t) :
    g ^ 4 = 1 := by
  obtain ⟨e, he, he'⟩ := sq_mem_rootCenterIn hι ht htι hg
  have he2 : e ^ 2 = 1 := φ.symm.injective (by
    rw [map_pow, map_one]
    exact pow_two_eq_one_of_fst_eq_zero J he)
  rw [show 4 = 2 * 2 by rfl, pow_mul, ← he', ← map_pow, he2, map_one]

theorem le_normalizer_involutionCosetHull :
    ι.range ⊔ Subgroup.zpowers t ≤ Subgroup.normalizer (involutionCosetHull J φ ι t : Set G) := by
  set W := involutionCosetHull J φ ι t
  have hmem := mem_involutionCosetHull_iff hι ht htι
  have hconj : ∀ (v : V), ∀ g ∈ W, ι v * g * (ι v)⁻¹ ∈ W := by
    intro v g hg
    obtain ⟨x, hx, rfl | rfl⟩ := (hmem g).mp hg
    · refine (hmem _).mpr ⟨v * x * v⁻¹, ?_, Or.inl (by rw [map_mul, map_mul, map_inv])⟩
      rw [mem_involutionCosetNormalizer hι ht htι] at hx ⊢
      rwa [map_mul, map_mul, map_inv, fst_mul, fst_mul, fst_inv, add_neg_cancel_comm]
    · refine (hmem _).mpr ⟨fieldInvolution J φ v * x * v⁻¹, ?_, Or.inr (conj_mul_eq ht htι v x)⟩
      rw [mem_involutionCosetNormalizer hι ht htι] at hx ⊢
      rw [fst_fieldInvolution_mul, map_sub, map_add, J.conj_involutive, hx, CharTwo.sub_eq_add,
        CharTwo.sub_eq_add]
      ring
  refine sup_le ?_ (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer
    ((hmem t).mpr ⟨1, Subgroup.one_mem _, Or.inr (by rw [map_one, mul_one])⟩)))
  rintro _ ⟨v, rfl⟩
  refine Subgroup.mem_normalizer_iff.mpr fun g => ⟨hconj v g, fun hg => ?_⟩
  have h := hconj v⁻¹ _ hg
  rwa [map_inv, inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, mul_assoc,
    inv_mul_cancel, mul_one] at h

end CharTwo

section Card

variable [Finite K] [CharP K 2] (q : ℕ) (hcard : Nat.card K = q ^ 2)
  (hfixed : Nat.card {x : K // J.conj x = x} = q)
include hcard hfixed

omit ht htι in
variable (φ ι t) in
theorem notMem_range (ht : t ^ 2 = 1) (htι : ∀ v, t * ι v * t⁻¹ = ι (fieldInvolution J φ v)) :
    t ∉ ι.range := by
  rintro ⟨w, rfl⟩
  obtain ⟨ξ, hξ⟩ := exists_conj_ne J q hcard hfixed
  obtain ⟨z, hz⟩ := exists_fst_eq J q hcard hfixed ξ
  have h := htι (φ z)
  rw [← map_inv, ← map_mul, ← map_mul] at h
  have h' := congrArg (fun v => (φ.symm v).1.1) (hι h)
  simp only [map_mul, map_inv, fst_mul, fst_inv, symm_fieldInvolution_apply, fst_rootTau,
    MulEquiv.symm_apply_apply, hz] at h'
  exact hξ (by linear_combination -h')

theorem card_involutionCosetNormalizer :
    Nat.card (involutionCosetNormalizer J φ ι t) = q ^ 2 := by
  have hq : 0 < q := pos_of_card_eq_sq q hcard
  let F : Subgroup (Multiplicative K) := (unitaryCoverFixedField J).toAddSubgroup.toSubgroup
  have hF : Nat.card F = q :=
    (Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd fun _ => Iff.rfl)).trans
      (card_fixedField J hfixed)
  have hFidx : F.index = q := by
    have h := F.card_mul_index
    rw [hF, Nat.card_congr Multiplicative.toAdd, hcard, pow_two] at h
    exact Nat.eq_of_mul_eq_mul_left hq h
  have hU : involutionCosetNormalizer J φ ι t = F.comap (rootFst J φ) := by
    ext v
    rw [mem_involutionCosetNormalizer hι ht htι]
    exact Iff.rfl
  have hUidx : (involutionCosetNormalizer J φ ι t).index = q := by
    rw [hU, Subgroup.index_comap_of_surjective _
      ((root_structure J φ q hcard hfixed).2.2.2.2.1), hFidx]
  have h := (involutionCosetNormalizer J φ ι t).card_mul_index
  rw [hUidx, (root_structure J φ q hcard hfixed).1, pow_succ] at h
  exact Nat.eq_of_mul_eq_mul_right hq h

theorem exponent_involutionCosetNormalizer :
    Monoid.exponent (involutionCosetNormalizer J φ ι t) = 4 := by
  obtain ⟨z, hz⟩ := exists_fst_eq J q hcard hfixed 1
  have ho : φ z ∈ involutionCosetNormalizer J φ ι t := by
    rw [mem_involutionCosetNormalizer hι ht htι, MulEquiv.symm_apply_apply, hz, map_one]
  have h4 : Monoid.exponent (involutionCosetNormalizer J φ ι t) ∣ 4 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => Subtype.ext (φ.symm.injective (by
      rw [Subgroup.coe_pow, map_pow, pow_four_eq_one, Subgroup.coe_one, map_one]))
  have h2 : ¬ Monoid.exponent (involutionCosetNormalizer J φ ι t) ∣ 2 := fun h => by
    have h' := congrArg (fun x : involutionCosetNormalizer J φ ι t => φ.symm (x : V))
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp h ⟨φ z, ho⟩)
    simp only [Subgroup.coe_pow, map_pow, MulEquiv.symm_apply_apply, Subgroup.coe_one,
      map_one, pow_two_eq_one_iff, hz] at h'
    exact one_ne_zero h'
  have hle := Nat.le_of_dvd (by norm_num) h4
  interval_cases h : Monoid.exponent (involutionCosetNormalizer J φ ι t) <;> simp_all

theorem sq_involutionCosetNormalizer :
    {v : V | ∃ x ∈ involutionCosetNormalizer J φ ι t, x ^ 2 = v} = rootCenter J φ := by
  ext v
  constructor
  · rintro ⟨x, -, rfl⟩
    rw [SetLike.mem_coe, mem_rootCenter, map_pow]
    exact fst_pow_two J _
  · intro hv
    have hv' : (φ.symm v).1.1 = 0 := hv
    have hb := conj_snd_of_fst_eq_zero J hv'
    obtain ⟨r, hr⟩ := isSquare_of_charTwo' (φ.symm v).1.2
    have hr' : J.conj r = r := by
      have h₂ : (2 : K) = 0 := CharTwo.two_eq_zero
      have hsq : (J.conj r - r) ^ 2 = 0 := by
        have h := congrArg J.conj hr
        rw [hb, map_mul] at h
        linear_combination -h - hr + ((φ.symm v).1.2 - r * J.conj r) * h₂
      exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq)
    obtain ⟨w, hw⟩ := exists_fst_eq J q hcard hfixed r
    refine ⟨φ w, ?_, φ.symm.injective (coord_ext ?_ ?_)⟩
    · rw [mem_involutionCosetNormalizer hι ht htι, MulEquiv.symm_apply_apply, hw, hr']
    · rw [map_pow, MulEquiv.symm_apply_apply, fst_pow_two, hv']
    · rw [map_pow, MulEquiv.symm_apply_apply, snd_pow_two, hw, hr', hr]

theorem card_involutionCosetHull : Nat.card (involutionCosetHull J φ ι t) = 2 * q ^ 2 := by
  set U := involutionCosetNormalizer J φ ι t
  have hnot := notMem_range φ ι t hι q hcard hfixed ht htι
  have hmem := mem_involutionCosetHull_iff hι ht htι
  let F : U ⊕ U → involutionCosetHull J φ ι t :=
    Sum.elim (fun x => ⟨ι x, (hmem _).mpr ⟨x, x.2, Or.inl rfl⟩⟩)
      fun x => ⟨t * ι x, (hmem _).mpr ⟨x, x.2, Or.inr rfl⟩⟩
  have hF : Function.Bijective F := by
    refine ⟨?_, ?_⟩
    · rintro (x | x) (y | y) h <;> simp only [F, Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq] at h
      · exact congrArg Sum.inl (Subtype.ext (hι h))
      · exact (hnot ⟨x * (y : V)⁻¹, by rw [map_mul, map_inv, h, mul_inv_cancel_right]⟩).elim
      · exact (hnot ⟨y * (x : V)⁻¹, by rw [map_mul, map_inv, ← h, mul_inv_cancel_right]⟩).elim
      · exact congrArg Sum.inr (Subtype.ext (hι (mul_left_cancel h)))
    · rintro ⟨g, hg⟩
      obtain ⟨x, hx, rfl | rfl⟩ := (hmem g).mp hg
      · exact ⟨Sum.inl ⟨x, hx⟩, rfl⟩
      · exact ⟨Sum.inr ⟨x, hx⟩, rfl⟩
  have : Finite V := Finite.of_equiv _ φ.toEquiv
  rw [← Nat.card_congr (Equiv.ofBijective F hF), Nat.card_sum,
    card_involutionCosetNormalizer hι ht htι q hcard hfixed, two_mul]

theorem frattini_involutionCosetHull :
    frattini (involutionCosetHull J φ ι t) =
      (rootCenterIn J φ ι).subgroupOf (involutionCosetHull J φ ι t) := by
  set W := involutionCosetHull J φ ι t
  have : Finite W := Nat.finite_of_card_ne_zero (by
    rw [card_involutionCosetHull hι ht htι q hcard hfixed]
    exact mul_ne_zero two_ne_zero (pow_ne_zero 2 (pos_of_card_eq_sq q hcard).ne'))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 W) := ⟨fun w => ⟨2, Subtype.ext (by
    rw [Subgroup.coe_pow, show 2 ^ 2 = 4 by norm_num, pow_four_eq_one_of_mem_hull hι ht htι w.2,
      Subgroup.coe_one])⟩⟩
  have hsq : ∀ w : W, w ^ 2 ∈ (rootCenterIn J φ ι).subgroupOf W := fun w =>
    Subgroup.mem_subgroupOf.mpr (by
      rw [Subgroup.coe_pow]
      exact sq_mem_rootCenterIn hι ht htι w.2)
  rw [CFSG.frattini_eq_closure_commutator_union_powers (p := 2)]
  refine le_antisymm ((Subgroup.closure_le _).mpr ?_) fun e he => ?_
  · rintro x (hx | ⟨w, rfl⟩)
    · have hle : commutator W ≤ (rootCenterIn J φ ι).subgroupOf W :=
        Subgroup.commutator_le.mpr fun a _ b _ => by
          have hab : ⁅a, b⁆ = a ^ 2 * (a⁻¹ * b) ^ 2 * b⁻¹ ^ 2 := by
            rw [commutatorElement_def, pow_two, pow_two, pow_two]
            group
          rw [hab]
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hsq a) (hsq _)) (hsq _)
      exact hle hx
    · exact hsq w
  · obtain ⟨v, hv, hve⟩ := Subgroup.mem_subgroupOf.mp he
    rw [← sq_involutionCosetNormalizer hι ht htι q hcard hfixed] at hv
    obtain ⟨x, hx, rfl⟩ := hv
    have hxW : ι x ∈ W := (mem_involutionCosetHull_iff hι ht htι _).mpr ⟨x, hx, Or.inl rfl⟩
    refine Subgroup.subset_closure (Or.inr ⟨⟨ι x, hxW⟩, Subtype.ext ?_⟩)
    rw [Subgroup.coe_pow, ← map_pow, hve]

theorem involutionCosets_conj_transitive :
    ∀ S ∈ involutionCosets J φ ι t, ∀ S' ∈ involutionCosets J φ ι t,
      ∃ v : V, MulAut.conj (ι v) '' S = S' := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [mem_involutionCosetNormalizer hι ht htι] at hx hy
  have hd : J.conj ((φ.symm y).1.1 - (φ.symm x).1.1) = (φ.symm y).1.1 - (φ.symm x).1.1 := by
    rw [map_sub, hx, hy]
  obtain ⟨c, hc⟩ := exists_trace_eq J q hcard hfixed hd
  obtain ⟨z, hz⟩ := exists_fst_eq J q hcard hfixed c
  refine ⟨φ z, ?_⟩
  rw [conj_image_smul ht htι, smul_rootCenterIn_eq_iff hι, fst_fieldInvolution_mul,
    MulEquiv.symm_apply_apply, hz]
  have h₂ : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination hc - c * h₂

theorem involutionCosets_not_fixed :
    ∀ S ∈ involutionCosets J φ ι t, ∃ v : V, MulAut.conj (ι v) '' S ≠ S := by
  rintro _ ⟨x, -, rfl⟩
  obtain ⟨ξ, hξ⟩ := exists_conj_ne J q hcard hfixed
  obtain ⟨z, hz⟩ := exists_fst_eq J q hcard hfixed ξ
  refine ⟨φ z, ?_⟩
  rw [conj_image_smul ht htι, Ne, smul_rootCenterIn_eq_iff hι, fst_fieldInvolution_mul,
    MulEquiv.symm_apply_apply, hz]
  exact fun h => hξ (by linear_combination h)

theorem conj_orbit_eq_involutionCosets :
    {S | ∃ v : V, S = MulAut.conj (ι v) '' involutionCoset J φ ι t} =
      involutionCosets J φ ι t := by
  have hΓ : involutionCoset J φ ι t ∈ involutionCosets J φ ι t :=
    ⟨1, Subgroup.one_mem _, involutionCoset_eq φ ι t⟩
  ext S
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨fieldInvolution J φ v * 1 * v⁻¹, ?_, ?_⟩
    · rw [mem_involutionCosetNormalizer hι ht htι, fst_fieldInvolution_mul, map_one, fst_one,
        add_zero, map_sub, J.conj_involutive, CharTwo.sub_eq_add, CharTwo.sub_eq_add, add_comm]
    · rw [involutionCoset_eq, conj_image_smul ht htι]
  · intro hS
    obtain ⟨v, hv⟩ := involutionCosets_conj_transitive hι ht htι q hcard hfixed _ hΓ S hS
    exact ⟨v, hv.symm⟩

theorem ncard_involutionCosets : (involutionCosets J φ ι t).ncard = q := by
  have hsec : ∀ a : unitaryCoverFixedField J, ∃ x : V, (φ.symm x).1.1 = a := fun a => by
    obtain ⟨z, hz⟩ := exists_fst_eq J q hcard hfixed a
    exact ⟨φ z, by rw [MulEquiv.symm_apply_apply, hz]⟩
  choose sec hsec using hsec
  have hU : ∀ a, sec a ∈ involutionCosetNormalizer J φ ι t := fun a => by
    rw [mem_involutionCosetNormalizer hι ht htι, hsec]
    exact a.2
  have hrange : involutionCosets J φ ι t =
      Set.range fun a => (t * ι (sec a)) • (rootCenterIn J φ ι : Set G) := by
    ext S
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨(φ.symm x).1.1, (mem_involutionCosetNormalizer hι ht htι x).mp hx⟩, ?_⟩
      rw [smul_rootCenterIn_eq_iff hι, hsec]
    · rintro ⟨a, rfl⟩
      exact ⟨sec a, hU a, rfl⟩
  rw [hrange, Set.ncard_range_of_injective, card_fixedField J hfixed]
  intro a b h
  exact Subtype.ext (by rwa [smul_rootCenterIn_eq_iff hι, hsec, hsec] at h)

end Card

end Hypotheses

end CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism
