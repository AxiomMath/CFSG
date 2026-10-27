module

public import CFSG.Walter.W67.Interface

public section

namespace CFSG.Walter.W67

open Finset

namespace Free

section Module

variable {M : Type*} [AddCommGroup M]

abbrev kerE (T : Module.End ℤ M) : AddSubgroup M := T.toAddMonoidHom.ker

abbrev rangeE (T : Module.End ℤ M) : AddSubgroup M := T.toAddMonoidHom.range

theorem card_kerE_mul_card_rangeE (T : Module.End ℤ M) :
    Nat.card (kerE T) * Nat.card (rangeE T) = Nat.card M := by
  rw [← AddSubgroup.index_ker, AddSubgroup.card_mul_index]

variable [Finite M]

theorem card_kerE_pow_succ_le (T : Module.End ℤ M) (j : ℕ) :
    Nat.card (kerE (T ^ (j + 1))) ≤ Nat.card (kerE (T ^ j)) * Nat.card (kerE T) := by
  set K := kerE (T ^ (j + 1))
  let f : K →+ M := (T ^ j).toAddMonoidHom.comp K.subtype
  have h1 : Nat.card f.ker * Nat.card f.range = Nat.card K := by
    rw [← AddSubgroup.index_ker, AddSubgroup.card_mul_index]
  have h2 : Nat.card f.ker ≤ Nat.card (kerE (T ^ j)) := by
    refine Nat.card_le_card_of_injective (fun k => ⟨(k : K), k.2⟩) ?_
    intro a b hab
    have h := congrArg (fun z : kerE (T ^ j) => (z : M)) hab
    exact Subtype.ext (Subtype.ext h)
  have h3 : f.range ≤ kerE T := by
    rintro _ ⟨k, rfl⟩
    have hk : (T ^ (j + 1)) (k : M) = 0 := k.2
    change T ((T ^ j) (k : M)) = 0
    rw [pow_succ', Module.End.mul_apply] at hk
    exact hk
  calc Nat.card K = Nat.card f.ker * Nat.card f.range := h1.symm
    _ ≤ Nat.card (kerE (T ^ j)) * Nat.card (kerE T) :=
      Nat.mul_le_mul h2 (AddSubgroup.card_le_of_le h3)

theorem card_kerE_pow_le (T : Module.End ℤ M) (j : ℕ) :
    Nat.card (kerE (T ^ j)) ≤ Nat.card (kerE T) ^ j := by
  induction j with
  | zero =>
    have : kerE (T ^ 0) = ⊥ := by
      ext x
      simp [kerE]
    rw [this, AddSubgroup.card_bot, pow_zero]
  | succ j ih =>
    calc Nat.card (kerE (T ^ (j + 1))) ≤ Nat.card (kerE (T ^ j)) * Nat.card (kerE T) :=
          card_kerE_pow_succ_le T j
      _ ≤ Nat.card (kerE T) ^ j * Nat.card (kerE T) := Nat.mul_le_mul_right _ ih
      _ = Nat.card (kerE T) ^ (j + 1) := (pow_succ _ _).symm

omit [Finite M] in
theorem geom_sum_eq_sub_one_pow {p : ℕ} [hp : Fact p.Prime] {R : Type*} [Ring R] [CharP R p]
    (g : R) (a : ℕ) : ∑ i ∈ range (p ^ a), g ^ i = (g - 1) ^ (p ^ a - 1) := by
  have hpoly : ∑ i ∈ range (p ^ a), (Polynomial.X : Polynomial (ZMod p)) ^ i =
      (Polynomial.X - 1) ^ (p ^ a - 1) := by
    have hne : (Polynomial.X - 1 : Polynomial (ZMod p)) ≠ 0 := Polynomial.X_sub_C_ne_zero 1
    apply mul_right_cancel₀ hne
    rw [geom_sum_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.out.pos),
      sub_pow_char_pow, one_pow]
  let φ : Polynomial (ZMod p) →+* R :=
    Polynomial.eval₂RingHom' (ZMod.castHom (dvd_refl p) R) g (fun a => by
      rw [ZMod.castHom_apply, ZMod.cast_eq_val]
      exact Nat.cast_commute _ _)
  have := congrArg φ hpoly
  simpa [φ, map_sum, map_pow, map_sub] using this

omit [Finite M] in
theorem charP_end {p : ℕ} [hp : Fact p.Prime] [Nontrivial M] (hM : ∀ m : M, p • m = 0) :
    CharP (Module.End ℤ M) p := by
  refine ⟨fun n => ⟨fun hn => ?_, fun hn => ?_⟩⟩
  · obtain ⟨m, hm⟩ := exists_ne (0 : M)
    have h1 : n • m = 0 := by
      have := LinearMap.congr_fun hn m
      simpa using this
    rw [← addOrderOf_eq_prime (hM m) hm]
    exact addOrderOf_dvd_of_nsmul_eq_zero h1
  · obtain ⟨k, rfl⟩ := hn
    ext m
    simp [mul_comm p k, hM]

theorem exists_eq_sub_of_geom_sum_eq_zero {p : ℕ} [hp : Fact p.Prime] (hM : ∀ m : M, p • m = 0)
    (g : Module.End ℤ M) (a : ℕ) (hg : g ^ (p ^ a) = 1)
    (hcount : Nat.card (kerE (g - 1)) ^ (p ^ a) = Nat.card M)
    (v : M) (hv : (∑ i ∈ range (p ^ a), g ^ i) v = 0) : ∃ w, v = g w - w := by
  rcases subsingleton_or_nontrivial M with hM1 | hM1
  · exact ⟨0, Subsingleton.elim _ _⟩
  have := charP_end hM
  set n := p ^ a with hn
  have hn1 : 1 ≤ n := Nat.one_le_pow _ _ hp.out.pos
  set T := g - 1 with hT
  set N := ∑ i ∈ range n, g ^ i with hN
  have hNT : N = T ^ (n - 1) := geom_sum_eq_sub_one_pow g a
  have hle : rangeE T ≤ kerE N := by
    rintro _ ⟨w, rfl⟩
    change N (T w) = 0
    rw [← Module.End.mul_apply, hN, hT, geom_sum_mul, hg, sub_self]
    rfl
  have hfilt := card_kerE_pow_le T (n - 1)
  rw [← hNT] at hfilt
  have hN1 := card_kerE_mul_card_rangeE N
  have hT1 := card_kerE_mul_card_rangeE T
  have hpos : 0 < Nat.card (kerE T) ^ (n - 1) := by
    have : 0 < Nat.card (kerE T) := Nat.card_pos
    positivity
  have hrN : Nat.card (kerE T) ≤ Nat.card (rangeE N) := by
    have h1 : Nat.card (kerE T) ^ (n - 1) * Nat.card (kerE T) ≤
        Nat.card (kerE T) ^ (n - 1) * Nat.card (rangeE N) := by
      calc Nat.card (kerE T) ^ (n - 1) * Nat.card (kerE T) = Nat.card (kerE T) ^ n := by
            rw [← pow_succ, Nat.sub_add_cancel hn1]
        _ = Nat.card M := hcount
        _ = Nat.card (kerE N) * Nat.card (rangeE N) := hN1.symm
        _ ≤ Nat.card (kerE T) ^ (n - 1) * Nat.card (rangeE N) :=
          Nat.mul_le_mul_right _ hfilt
    exact Nat.le_of_mul_le_mul_left h1 hpos
  have hkN : Nat.card (kerE N) ≤ Nat.card (rangeE T) := by
    have hpos' : 0 < Nat.card (kerE T) := Nat.card_pos
    have : Nat.card (kerE N) * Nat.card (kerE T) ≤ Nat.card (rangeE T) * Nat.card (kerE T) := by
      calc Nat.card (kerE N) * Nat.card (kerE T) ≤ Nat.card (kerE N) * Nat.card (rangeE N) :=
            Nat.mul_le_mul_left _ hrN
        _ = Nat.card (kerE T) * Nat.card (rangeE T) := hN1.trans hT1.symm
        _ = Nat.card (rangeE T) * Nat.card (kerE T) := mul_comm _ _
    exact Nat.le_of_mul_le_mul_right this hpos'
  have heq : rangeE T = kerE N := AddSubgroup.eq_of_le_of_card_ge hle hkN
  have hvN : v ∈ kerE N := hv
  rw [← heq] at hvN
  obtain ⟨w, hw⟩ := hvN
  refine ⟨w, ?_⟩
  rw [← hw]
  change T w = g w - w
  rw [hT, LinearMap.sub_apply, Module.End.one_apply]

variable {X : Type*} [Group X]

omit [Finite M] in
@[expose] def fixAdd (ρ : X →* Module.End ℤ M) (Y : Subgroup X) : AddSubgroup M where
  carrier := {m | ∀ y ∈ Y, ρ y m = m}
  add_mem' {a b} ha hb y hy := by rw [map_add, ha y hy, hb y hy]
  zero_mem' y _ := map_zero _
  neg_mem' {a} ha y hy := by rw [map_neg, ha y hy]

omit [Finite M] in
theorem mem_fixAdd {ρ : X →* Module.End ℤ M} {Y : Subgroup X} {m : M} :
    m ∈ fixAdd ρ Y ↔ ∀ y ∈ Y, ρ y m = m := Iff.rfl

omit [Finite M] in
theorem cocycle_one (ρ : X →* Module.End ℤ M) {c : X → M}
    (hc : ∀ x y, c (x * y) = c x + ρ x (c y)) : c 1 = 0 := by
  have := hc 1 1
  rw [one_mul, map_one, Module.End.one_apply] at this
  exact (add_eq_left.mp this.symm)

omit [Finite M] in
theorem cocycle_pow (ρ : X →* Module.End ℤ M) {c : X → M}
    (hc : ∀ x y, c (x * y) = c x + ρ x (c y)) (h : X) (i : ℕ) :
    c (h ^ i) = (∑ j ∈ range i, ρ h ^ j) (c h) := by
  induction i with
  | zero => simp [cocycle_one ρ hc]
  | succ i ih =>
    rw [pow_succ, hc, ih, sum_range_succ, LinearMap.add_apply, map_pow]

omit [Finite M] in
theorem coboundary_pow (g : Module.End ℤ M) (i : ℕ) (w : M) :
    (∑ j ∈ range i, g ^ j) (g w - w) = (g ^ i) w - w := by
  have := LinearMap.congr_fun (geom_sum_mul g i) w
  simpa [Module.End.mul_apply] using this

theorem h1_eq_zero {p : ℕ} [hp : Fact p.Prime] [Finite X] [IsCyclic X]
    (ρ : X →* Module.End ℤ M) (hM : ∀ m : M, p • m = 0)
    (hcount : ∀ Y : Subgroup X, Nat.card (fixAdd ρ Y) ^ Nat.card Y = Nat.card M)
    (c : X → M) (hc : ∀ x y, c (x * y) = c x + ρ x (c y)) :
    ∃ w : M, ∀ x, c x = ρ x w - w := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := X)
  have hgn : orderOf g = Nat.card X := orderOf_eq_card_of_forall_mem_zpowers hg
  have hn0 : Nat.card X ≠ 0 := Nat.card_pos.ne'
  obtain ⟨a, m, hpm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hp.out.ne_one
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hnm
    exact hn0 hnm
  have hpa0 : p ^ a ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  set h := g ^ m with hhdef
  have hh : orderOf h = p ^ a := by
    rw [orderOf_pow_of_dvd hm0 (by rw [hgn, hnm]; exact dvd_mul_left _ _), hgn, hnm,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  set u := g ^ (p ^ a) with hudef
  have hu : orderOf u = m := by
    rw [orderOf_pow_of_dvd hpa0 (by rw [hgn, hnm]; exact dvd_mul_right _ _), hgn, hnm,
      Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hpa0)]
  have hfixh : fixAdd ρ (Subgroup.zpowers h) = kerE (ρ h - 1) := by
    ext v
    constructor
    · intro hv
      have := hv h (Subgroup.mem_zpowers h)
      change (ρ h - 1) v = 0
      rw [LinearMap.sub_apply, this, Module.End.one_apply, sub_self]
    · intro hv y hy
      have hv' : ρ h v = v := by
        have : (ρ h - 1) v = 0 := hv
        rwa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at this
      have hpow : ∀ i : ℕ, (ρ h ^ i) v = v := by
        intro i
        induction i with
        | zero => simp
        | succ i ih => rw [pow_succ, Module.End.mul_apply, hv', ih]
      obtain ⟨i, rfl⟩ := mem_powers_iff_mem_zpowers.mpr hy
      rw [map_pow]
      exact hpow i
  have hcount_h : Nat.card (kerE (ρ h - 1)) ^ (p ^ a) = Nat.card M := by
    rw [← hfixh, ← hh, ← Nat.card_zpowers]
    exact hcount _
  have hρh : ρ h ^ (p ^ a) = 1 := by rw [← map_pow, ← hh, pow_orderOf_eq_one, map_one]
  have hv : (∑ i ∈ range (p ^ a), ρ h ^ i) (c h) = 0 := by
    rw [← cocycle_pow ρ hc, ← hh, pow_orderOf_eq_one, cocycle_one ρ hc]
  obtain ⟨w, hw⟩ := exists_eq_sub_of_geom_sum_eq_zero hM (ρ h) a hρh hcount_h (c h) hv
  have hci : ∀ i : ℕ, c (h ^ i) = ρ (h ^ i) w - w := by
    intro i
    rw [cocycle_pow ρ hc, hw, coboundary_pow, ← map_pow]
  set c' : X → M := fun x => c x - (ρ x w - w) with hc'def
  have hc' : ∀ x y, c' (x * y) = c' x + ρ x (c' y) := by
    intro x y
    simp only [c', hc, map_mul, Module.End.mul_apply, map_sub]
    abel
  have hc'P : ∀ y ∈ Subgroup.zpowers h, c' y = 0 := by
    intro y hy
    obtain ⟨i, rfl⟩ := mem_powers_iff_mem_zpowers.mpr hy
    simp [c', hci]
  have hright : ∀ x, ∀ y ∈ Subgroup.zpowers h, c' (x * y) = c' x := by
    intro x y hy
    rw [hc', hc'P y hy, map_zero, add_zero]
  set Q := Subgroup.zpowers u with hQ
  let : Fintype Q := Fintype.ofFinite Q
  have hQcard : Fintype.card Q = m := by rw [Fintype.card_eq_nat_card, Nat.card_zpowers, hu]
  set S : M := ∑ z : Q, c' (z : X) with hSdef
  have hcop : Nat.Coprime (p ^ a) m :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpm)
  have hdecomp : ∀ x : X, ∃ y ∈ Subgroup.zpowers h, ∃ z ∈ Q, x = y * z := by
    intro x
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
    have hb := Nat.gcd_eq_gcd_ab (p ^ a) m
    rw [hcop, Nat.cast_one] at hb
    refine ⟨h ^ (Nat.gcdB (p ^ a) m * k), Subgroup.zpow_mem _ (Subgroup.mem_zpowers h) _,
      u ^ (Nat.gcdA (p ^ a) m * k), Subgroup.zpow_mem _ (Subgroup.mem_zpowers u) _, ?_⟩
    rw [hhdef, hudef, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add]
    congr 1
    calc k = (((p ^ a : ℕ) : ℤ) * Nat.gcdA (p ^ a) m + (m : ℤ) * Nat.gcdB (p ^ a) m) * k := by
          rw [← hb, one_mul]
      _ = _ := by ring
  have hS : ∀ x : X, ρ x S = S - m • c' x := by
    intro x
    obtain ⟨y, hy, z₀, hz₀, rfl⟩ := hdecomp x
    rw [hSdef, map_sum]
    have hz : ∀ z : Q, ρ (y * z₀) (c' z) = c' (z₀ * z) - c' (y * z₀) := by
      intro z
      have h1 := hc' (y * z₀) z
      have h2 : y * z₀ * (z : X) = z₀ * z * y := by
        rw [mul_assoc, mul_comm' y]
      rw [h2, hright _ y hy] at h1
      rw [h1]
      abel
    simp_rw [hz, sum_sub_distrib, sum_const, card_univ, hQcard]
    congr 1
    exact Fintype.sum_equiv (Equiv.mulLeft ⟨z₀, hz₀⟩) _ _ (fun z => rfl)
  obtain ⟨m', -, hm'⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpm).symm hp.out.one_lt
  have hmm' : ∀ v : M, (m * m') • v = v := by
    intro v
    rw [← Nat.div_add_mod (m * m') p, hm', add_nsmul, one_nsmul, mul_nsmul, hM, nsmul_zero,
      zero_add]
  refine ⟨w + -(m' • S), fun x => ?_⟩
  have h1 : c x = c' x + (ρ x w - w) := by simp [c']
  rw [h1, map_add, map_neg, map_nsmul, hS x, nsmul_sub, ← mul_nsmul, hmm']
  abel

end Module

section Factor

variable {X N : Type*} [Group X] [Group N] [MulDistribMulAction X N]

@[reducible, expose] def factorCommGroup (A B : Subgroup N) [(B.subgroupOf A).Normal]
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b * a⁻¹ * b⁻¹ ∈ B) : CommGroup (A ⧸ B.subgroupOf A) :=
  { (inferInstance : Group (A ⧸ B.subgroupOf A)) with
    mul_comm := by
      rintro ⟨a⟩ ⟨b⟩
      change (QuotientGroup.mk (a * b) : A ⧸ B.subgroupOf A) = QuotientGroup.mk (b * a)
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have := hcomm _ (A.inv_mem b.2) _ (A.inv_mem a.2)
      simpa [mul_assoc] using this }

@[expose] def actSub (A : Subgroup N) (hA : ∀ x : X, ∀ a ∈ A, x • a ∈ A) (x : X) : A →* A where
  toFun a := ⟨x • (a : N), hA x a a.2⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [smul_mul']

@[expose] def actQuot (A B : Subgroup N) [(B.subgroupOf A).Normal]
    (hA : ∀ x : X, ∀ a ∈ A, x • a ∈ A) (hB : ∀ x : X, ∀ b ∈ B, x • b ∈ B) (x : X) :
    A ⧸ B.subgroupOf A →* A ⧸ B.subgroupOf A :=
  QuotientGroup.map _ _ (actSub A hA x) (by
    intro a ha
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact hB x a ha)

variable (A B : Subgroup N) [(B.subgroupOf A).Normal]
  (hA : ∀ x : X, ∀ a ∈ A, x • a ∈ A) (hB : ∀ x : X, ∀ b ∈ B, x • b ∈ B)

theorem actQuot_mk (x : X) (a : A) :
    actQuot A B hA hB x (a : A ⧸ B.subgroupOf A) = ((⟨x • (a : N), hA x a a.2⟩ : A) :
      A ⧸ B.subgroupOf A) := rfl

theorem actQuot_one : actQuot A B hA hB 1 = MonoidHom.id _ := by
  ext a
  simp [actQuot_mk]

theorem actQuot_mul (x y : X) :
    actQuot A B hA hB (x * y) = (actQuot A B hA hB x).comp (actQuot A B hA hB y) := by
  ext a
  simp [actQuot_mk, mul_smul]

@[expose] def factorRep (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b * a⁻¹ * b⁻¹ ∈ B) :
    letI := factorCommGroup A B hcomm
    X →* Module.End ℤ (Additive (A ⧸ B.subgroupOf A)) :=
  letI := factorCommGroup A B hcomm
  { toFun := fun x => (MonoidHom.toAdditive (actQuot A B hA hB x)).toIntLinearMap
    map_one' := by
      ext a
      simp [actQuot_one]
    map_mul' := fun x y => by
      ext a
      simp [actQuot_mul] }

theorem factorRep_apply (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b * a⁻¹ * b⁻¹ ∈ B) (x : X) (a : A) :
    letI := factorCommGroup A B hcomm
    factorRep A B hA hB hcomm x (Additive.ofMul (a : A ⧸ B.subgroupOf A)) =
      Additive.ofMul ((⟨x • (a : N), hA x a a.2⟩ : A) : A ⧸ B.subgroupOf A) := rfl

@[expose] def fixQuot (Y : Subgroup X) : Subgroup (A ⧸ B.subgroupOf A) where
  carrier := {q | ∀ y ∈ Y, actQuot A B hA hB y q = q}
  mul_mem' {a b} ha hb y hy := by rw [map_mul, ha y hy, hb y hy]
  one_mem' y _ := map_one _
  inv_mem' {a} ha y hy := by rw [map_inv, ha y hy]

theorem mk_mem_fixQuot_iff (Y : Subgroup X) (a : A) :
    (a : A ⧸ B.subgroupOf A) ∈ fixQuot A B hA hB Y ↔ ∀ y ∈ Y, (a : N)⁻¹ * (y • (a : N)) ∈ B := by
  change (∀ y ∈ Y, _ = _) ↔ _
  refine forall₂_congr fun y _ => ?_
  rw [actQuot_mk, eq_comm, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  rfl

theorem card_fixAdd (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b * a⁻¹ * b⁻¹ ∈ B) (Y : Subgroup X) :
    letI := factorCommGroup A B hcomm
    Nat.card (fixAdd (factorRep A B hA hB hcomm) Y) = Nat.card (fixQuot A B hA hB Y) := by
  let := factorCommGroup A B hcomm
  refine Nat.card_congr
    { toFun := fun m => ⟨Additive.toMul (m : Additive (A ⧸ B.subgroupOf A)), fun y hy => ?_⟩
      invFun := fun q => ⟨Additive.ofMul (q : A ⧸ B.subgroupOf A), fun y hy => ?_⟩
      left_inv := fun m => rfl
      right_inv := fun q => rfl }
  · exact m.2 y hy
  · exact q.2 y hy

theorem card_relFix [Finite N] (hBA : B ≤ A) (Y : Subgroup X) :
    (relFix Y A B).ncard = Nat.card (fixQuot A B hA hB Y) * Nat.card B := by
  classical
  set B' := B.subgroupOf A
  set S : Subgroup A := (fixQuot A B hA hB Y).comap (QuotientGroup.mk' B')
  have hset : relFix Y A B = (A.subtype : A → N) '' (S : Set A) := by
    ext n
    constructor
    · rintro ⟨hnA, hn⟩
      refine ⟨⟨n, hnA⟩, ?_, rfl⟩
      change ((⟨n, hnA⟩ : A) : A ⧸ B') ∈ fixQuot A B hA hB Y
      rw [mk_mem_fixQuot_iff]
      exact hn
    · rintro ⟨a, ha, rfl⟩
      refine ⟨a.2, ?_⟩
      have ha' : ((a : A) : A ⧸ B') ∈ fixQuot A B hA hB Y := ha
      rw [mk_mem_fixQuot_iff] at ha'
      exact ha'
  rw [hset, Set.ncard_image_of_injective _ A.subtype_injective, ← Nat.card_coe_set_eq]
  change Nat.card S = _
  have hsurj : Function.Surjective (QuotientGroup.mk' B') := QuotientGroup.mk'_surjective B'
  have hidx : S.index = (fixQuot A B hA hB Y).index := Subgroup.index_comap_of_surjective _ hsurj
  have h1 := S.card_mul_index
  have h2 := (fixQuot A B hA hB Y).card_mul_index
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup B'
  have hB' : Nat.card B' = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBA).toEquiv
  rw [hidx] at h1
  rw [hB'] at h3
  have hpos : 0 < (fixQuot A B hA hB Y).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h1, h3, ← h2]
  ring

theorem card_fixQuot_pow [Finite X] [Finite N] (hBA : B ≤ A) (Y : Subgroup X)
    (hfree : (relFix Y A B).ncard ^ Nat.card Y = Nat.card A * Nat.card B ^ (Nat.card Y - 1)) :
    Nat.card (fixQuot A B hA hB Y) ^ Nat.card Y = Nat.card (A ⧸ B.subgroupOf A) := by
  rw [card_relFix A B hA hB hBA, mul_pow] at hfree
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (B.subgroupOf A)
  have hB' : Nat.card (B.subgroupOf A) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBA).toEquiv
  rw [hB'] at h3
  have hY : 1 ≤ Nat.card Y := Nat.card_pos
  have hpos : 0 < Nat.card B ^ Nat.card Y := by
    have : 0 < Nat.card B := Nat.card_pos
    positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [hfree, h3, mul_assoc, ← pow_succ', Nat.sub_add_cancel hY]

include hA hB in
theorem factor_h1 {p : ℕ} [hp : Fact p.Prime] [Finite X] [IsCyclic X] [Finite N] (hBA : B ≤ A)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b * a⁻¹ * b⁻¹ ∈ B) (helem : ∀ a ∈ A, a ^ p ∈ B)
    (hfree : ∀ Y : Subgroup X, (relFix Y A B).ncard ^ Nat.card Y =
        Nat.card A * Nat.card B ^ (Nat.card Y - 1))
    (c : X → N) (hcA : ∀ x, c x ∈ A) (hc : ∀ x y, c (x * y) = c x * x • c y) :
    ∃ m ∈ A, ∀ x, m⁻¹ * c x * (x • m) ∈ B := by
  let := factorCommGroup A B hcomm
  have hM : ∀ m : Additive (A ⧸ B.subgroupOf A), p • m = 0 := by
    intro m
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (Additive.toMul m)
    rw [← ofMul_toMul m, ← ha, ← ofMul_pow, ← QuotientGroup.mk_pow]
    change Additive.ofMul (_ : A ⧸ B.subgroupOf A) = Additive.ofMul 1
    congr 1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_pow]
    exact helem _ a.2
  have hcount : ∀ Y : Subgroup X, Nat.card (fixAdd (factorRep A B hA hB hcomm) Y) ^ Nat.card Y =
      Nat.card (Additive (A ⧸ B.subgroupOf A)) := by
    intro Y
    rw [card_fixAdd A B hA hB hcomm Y, Nat.card_congr Additive.toMul]
    exact card_fixQuot_pow A B hA hB hBA Y (hfree Y)
  let cbar : X → Additive (A ⧸ B.subgroupOf A) := fun x =>
    Additive.ofMul ((⟨c x, hcA x⟩ : A) : A ⧸ B.subgroupOf A)
  have hcbar : ∀ x y, cbar (x * y) = cbar x + factorRep A B hA hB hcomm x (cbar y) := by
    intro x y
    simp only [cbar]
    rw [factorRep_apply, ← ofMul_mul, ← QuotientGroup.mk_mul]
    congr 2
    ext
    exact hc x y
  obtain ⟨w, hw⟩ := h1_eq_zero (factorRep A B hA hB hcomm) hM hcount cbar hcbar
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (Additive.toMul w)
  refine ⟨(a : N)⁻¹, A.inv_mem a.2, fun x => ?_⟩
  have hwx := hw x
  rw [← ofMul_toMul w, ← ha] at hwx
  have hwx' : ((⟨c x, hcA x⟩ : A) : A ⧸ B.subgroupOf A) =
      ((⟨x • (a : N), hA x a a.2⟩ : A) : A ⧸ B.subgroupOf A) / (a : A ⧸ B.subgroupOf A) := hwx
  have hmem : (⟨(a : N) * c x * (x • (a : N))⁻¹, A.mul_mem (A.mul_mem a.2 (hcA x))
      (A.inv_mem (hA x a a.2))⟩ : A) ∈ B.subgroupOf A := by
    rw [← QuotientGroup.eq_one_iff]
    have : ((⟨(a : N) * c x * (x • (a : N))⁻¹, A.mul_mem (A.mul_mem a.2 (hcA x))
        (A.inv_mem (hA x a a.2))⟩ : A) : A ⧸ B.subgroupOf A) =
        (a : A ⧸ B.subgroupOf A) * ((⟨c x, hcA x⟩ : A) : A ⧸ B.subgroupOf A) *
          ((⟨x • (a : N), hA x a a.2⟩ : A) : A ⧸ B.subgroupOf A)⁻¹ := rfl
    rw [this, hwx', div_eq_mul_inv,
      mul_comm (((⟨x • (a : N), hA x a a.2⟩ : A) : A ⧸ B.subgroupOf A)), mul_assoc, mul_assoc,
      mul_inv_cancel_left, mul_inv_cancel]
  rw [Subgroup.mem_subgroupOf] at hmem
  simpa [smul_inv'] using hmem

end Factor

section Lift

variable {X N : Type*} [Group X] [Group N] [MulDistribMulAction X N]

theorem lift_fixed (Nser : ℕ → Subgroup N) (k : ℕ) (hk : Nser k = ⊥)
    (hanti : ∀ i, Nser (i + 1) ≤ Nser i)
    (H1 : ∀ j < k, ∀ c : X → N, (∀ x, c x ∈ Nser j) → (∀ x y, c (x * y) = c x * x • c y) →
      ∃ m ∈ Nser j, ∀ x, m⁻¹ * c x * (x • m) ∈ Nser (j + 1))
    {i : ℕ} (hi : i < k) {n : N} (hn : n ∈ Nser i)
    (hfix : ∀ x : X, n⁻¹ * (x • n) ∈ Nser (i + 1)) :
    ∃ a ∈ Nser i, (∀ x : X, x • a = a) ∧ n⁻¹ * a ∈ Nser (i + 1) := by
  have hmono : Antitone Nser := antitone_nat_of_succ_le hanti
  have key : ∀ d, i + 1 + d ≤ k → ∃ a ∈ Nser i, n⁻¹ * a ∈ Nser (i + 1) ∧
      ∀ x : X, a⁻¹ * (x • a) ∈ Nser (i + 1 + d) := by
    intro d
    induction d with
    | zero => intro _; exact ⟨n, hn, by simp, by simpa using hfix⟩
    | succ d ih =>
      intro hd
      obtain ⟨a, haN, hna, hax⟩ := ih (by omega)
      have hj : i + 1 + d < k := by omega
      obtain ⟨m, hm, hmx⟩ := H1 (i + 1 + d) hj (fun x => a⁻¹ * (x • a)) hax (by
        intro x y
        rw [smul_mul', smul_inv', mul_smul]
        group)
      have hmi : m ∈ Nser i := hmono (by omega) hm
      have hmi1 : m ∈ Nser (i + 1) := hmono (by omega) hm
      refine ⟨a * m, mul_mem haN hmi, ?_, fun x => ?_⟩
      · rw [← mul_assoc]
        exact mul_mem hna hmi1
      · have := hmx x
        rw [show i + 1 + (d + 1) = i + 1 + d + 1 by omega, smul_mul', mul_inv_rev]
        simpa [mul_assoc] using this
  obtain ⟨a, haN, hna, hax⟩ := key (k - (i + 1)) (by omega)
  refine ⟨a, haN, fun x => ?_, hna⟩
  have := hax x
  rw [show i + 1 + (k - (i + 1)) = k by omega, hk, Subgroup.mem_bot] at this
  exact (inv_mul_eq_one.mp this).symm

@[expose] def fixSub (A : Subgroup N) : Subgroup N where
  carrier := {n | n ∈ A ∧ ∀ x : X, x • n = n}
  mul_mem' {a b} ha hb := ⟨mul_mem ha.1 hb.1, fun x => by rw [smul_mul', ha.2 x, hb.2 x]⟩
  one_mem' := ⟨one_mem _, fun x => smul_one x⟩
  inv_mem' {a} ha := ⟨inv_mem ha.1, fun x => by rw [smul_inv', ha.2 x]⟩

theorem card_fixSub (A B : Subgroup N) [(B.subgroupOf A).Normal] (hBA : B ≤ A)
    (hA : ∀ x : X, ∀ a ∈ A, x • a ∈ A) (hB : ∀ x : X, ∀ b ∈ B, x • b ∈ B)
    (hlift : ∀ n ∈ A, (∀ x : X, n⁻¹ * (x • n) ∈ B) →
      ∃ a ∈ A, (∀ x : X, x • a = a) ∧ n⁻¹ * a ∈ B) :
    Nat.card (fixSub (X := X) A) =
      Nat.card (fixQuot A B hA hB ⊤) * Nat.card (fixSub (X := X) B) := by
  let ψ : fixSub (X := X) A →* A ⧸ B.subgroupOf A :=
    (QuotientGroup.mk' (B.subgroupOf A)).comp (Subgroup.inclusion fun _ h => h.1)
  have hψ : ∀ f : fixSub (X := X) A, ψ f = ((⟨f, f.2.1⟩ : A) : A ⧸ B.subgroupOf A) :=
    fun _ => rfl
  have hrange : ψ.range = fixQuot A B hA hB ⊤ := by
    apply le_antisymm
    · rintro _ ⟨f, rfl⟩
      rw [hψ, mk_mem_fixQuot_iff]
      intro y _
      rw [f.2.2 y, inv_mul_cancel]
      exact one_mem _
    · intro q hq
      obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
      rw [mk_mem_fixQuot_iff] at hq
      obtain ⟨a, ha, hax, hna⟩ := hlift n n.2 (fun x => hq x (Subgroup.mem_top x))
      refine ⟨⟨a, ha, hax⟩, ?_⟩
      rw [hψ]
      apply QuotientGroup.eq.mpr
      rw [Subgroup.mem_subgroupOf]
      have := B.inv_mem hna
      simpa using this
  have hker : Nat.card ψ.ker = Nat.card (fixSub (X := X) B) := by
    refine Nat.card_congr
      { toFun := fun f => ⟨f.1, ?_, f.1.2.2⟩
        invFun := fun b => ⟨⟨b, hBA b.2.1, b.2.2⟩, ?_⟩
        left_inv := fun f => rfl
        right_inv := fun b => rfl }
    · have hf := f.2
      rw [MonoidHom.mem_ker, hψ, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hf
      exact hf
    · rw [MonoidHom.mem_ker, hψ, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact b.2.1
  rw [← Subgroup.card_ker_mul_card_range ψ, hker, hrange, mul_comm]

end Lift

end Free

theorem lemma_5_5 :
    ∀ {p : ℕ} [Fact p.Prime] {X N : Type} [Group X] [Finite X] [IsCyclic X] [Group N] [Finite N]
      [MulDistribMulAction X N], IsPGroup p N → ∀ (k : ℕ) (Nser : ℕ → Subgroup N), Nser 0 = ⊤ →
      Nser k = ⊥ → (∀ i, Nser (i + 1) ≤ Nser i) → (∀ i, ⁅(⊤ : Subgroup N), Nser i⁆ ≤ Nser (i + 1)) →
      (∀ i, ∀ x : X, ∀ n ∈ Nser i, x • n ∈ Nser i) → (∀ i, ∀ n ∈ Nser i, n ^ p ∈ Nser (i + 1)) →
      (∀ i < k, ∀ Y : Subgroup X,
        (relFix Y (Nser i) (Nser (i + 1))).ncard ^ Nat.card Y =
          Nat.card (Nser i) * Nat.card (Nser (i + 1)) ^ (Nat.card Y - 1)) →
      (∀ i < k, relFix (⊤ : Subgroup X) (Nser i) (Nser (i + 1)) =
        {n | ∃ a ∈ Nser i, (∀ x : X, x • a = a) ∧ ∃ b ∈ Nser (i + 1), n = a * b}) ∧
      {n : N | ∀ x : X, x • n = n}.ncard ^ Nat.card X = Nat.card N := by
  intro p _ X N _ _ _ _ _ _ _hN k Nser h1 hk hanti hcentral hinv helem hfree
  classical
  have hcomm_mem : ∀ i, ∀ g : N, ∀ n ∈ Nser i, g * n * g⁻¹ * n⁻¹ ∈ Nser (i + 1) := by
    intro i g n hn
    apply hcentral i
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) hn
  have hnormal : ∀ i, (Nser i).Normal := by
    intro i
    constructor
    intro n hn g
    have h2 : g * n * g⁻¹ = (g * n * g⁻¹ * n⁻¹) * n := by group
    rw [h2]
    exact mul_mem (hanti i (hcomm_mem i g n hn)) hn
  have H1 : ∀ j < k, ∀ c : X → N, (∀ x, c x ∈ Nser j) → (∀ x y, c (x * y) = c x * x • c y) →
      ∃ m ∈ Nser j, ∀ x, m⁻¹ * c x * (x • m) ∈ Nser (j + 1) := by
    intro j hj c hcA hc
    have := (hnormal (j + 1)).subgroupOf (Nser j)
    exact Free.factor_h1 (Nser j) (Nser (j + 1)) (hinv j) (hinv (j + 1)) (hanti j)
      (fun a _ b hb => hcomm_mem j a b hb) (helem j) (hfree j hj) c hcA hc
  have hlift : ∀ i < k, ∀ n ∈ Nser i, (∀ x : X, n⁻¹ * (x • n) ∈ Nser (i + 1)) →
      ∃ a ∈ Nser i, (∀ x : X, x • a = a) ∧ n⁻¹ * a ∈ Nser (i + 1) :=
    fun i hi n hn hfix => Free.lift_fixed Nser k hk hanti H1 hi hn hfix
  refine ⟨fun i hi => ?_, ?_⟩
  · ext n
    constructor
    · rintro ⟨hn, hfix⟩
      obtain ⟨a, ha, hax, hna⟩ :=
        hlift i hi n hn (fun x => hfix x (Subgroup.mem_top x))
      refine ⟨a, ha, hax, a⁻¹ * n, ?_, by group⟩
      have := (Nser (i + 1)).inv_mem hna
      simpa using this
    · rintro ⟨a, ha, hax, b, hb, rfl⟩
      refine ⟨mul_mem ha (hanti i hb), fun x _ => ?_⟩
      rw [smul_mul', hax x, mul_inv_rev]
      have : b⁻¹ * a⁻¹ * (a * x • b) = b⁻¹ * (x • b) := by group
      rw [this]
      exact mul_mem ((Nser (i + 1)).inv_mem hb) (hinv (i + 1) x b hb)
  ·
    have hcount : ∀ d, d ≤ k →
        Nat.card (Free.fixSub (X := X) (Nser (k - d))) ^ Nat.card X = Nat.card (Nser (k - d)) := by
      intro d
      induction d with
      | zero =>
        intro _
        have hbot : Free.fixSub (X := X) (Nser k) = ⊥ := by
          ext n
          constructor
          · rintro ⟨hn, -⟩
            rw [hk] at hn
            exact hn
          · intro hn
            rw [Subgroup.mem_bot] at hn
            rw [hn]
            exact one_mem _
        rw [Nat.sub_zero, hbot, hk, Subgroup.card_bot, one_pow]
      | succ d ih =>
        intro hd
        set i := k - (d + 1) with hidef
        have hi : i < k := by omega
        have hi1 : i + 1 = k - d := by omega
        have := (hnormal (i + 1)).subgroupOf (Nser i)
        have hc := Free.card_fixSub (X := X) (Nser i) (Nser (i + 1)) (hanti i) (hinv i)
          (hinv (i + 1)) (hlift i hi)
        have hq := Free.card_fixQuot_pow (Nser i) (Nser (i + 1)) (hinv i) (hinv (i + 1))
          (hanti i) ⊤ (hfree i hi ⊤)
        have hL := Subgroup.card_eq_card_quotient_mul_card_subgroup ((Nser (i + 1)).subgroupOf
          (Nser i))
        have hB' : Nat.card ((Nser (i + 1)).subgroupOf (Nser i)) = Nat.card (Nser (i + 1)) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hanti i)).toEquiv
        rw [Subgroup.card_top] at hq
        rw [hc, mul_pow, hq, hL, hB', hi1, ih (by omega)]
    have h0 := hcount k le_rfl
    rw [Nat.sub_self, h1, Subgroup.card_top] at h0
    rw [← h0, ← Nat.card_coe_set_eq]
    congr 1
    refine Nat.card_congr (Equiv.subtypeEquivRight fun n => ?_)
    change (∀ x : X, x • n = n) ↔ n ∈ (⊤ : Subgroup N) ∧ ∀ x : X, x • n = n
    simp

end CFSG.Walter.W67
