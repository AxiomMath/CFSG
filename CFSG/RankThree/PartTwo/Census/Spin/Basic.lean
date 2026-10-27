module

public import TauCeti.GroupTheory.DerivedCentralQuotient
public import TauCeti.Algebra.Lie.Presentation.Serre
public import TauCeti.Algebra.Lie.Sl2.SquareZero

public section

namespace CFSG.RankThree.PartTwo.Census.Spin

open TauCeti

variable {M : Type*} [Group M] (H : Subgroup M)

theorem map_subtype_commutator : (commutator H).map H.subtype = ⁅H, H⁆ := by
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

noncomputable def commutatorEquiv : ↥(commutator H) ≃* ↥⁅H, H⁆ :=
  (Subgroup.equivMapOfInjective (commutator H) H.subtype Subtype.val_injective).trans
    (MulEquiv.subgroupCongr (map_subtype_commutator H))

noncomputable def toQuotient : ↥⁅H, H⁆ →* DerivedCentralQuotient H :=
  (QuotientGroup.mk' _).comp (commutatorEquiv H).symm.toMonoidHom

theorem toQuotient_eq_one_iff (x : ↥⁅H, H⁆) :
    toQuotient H x = 1 ↔ ∀ y : ↥⁅H, H⁆, x * y = y * x := by
  rw [toQuotient, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_center_iff, MulEquiv.coe_toMonoidHom]
  constructor
  · intro h y
    have h2 := congrArg (commutatorEquiv H) (h ((commutatorEquiv H).symm y))
    simp only [map_mul, MulEquiv.apply_symm_apply] at h2
    exact h2.symm
  · intro h z
    apply (commutatorEquiv H).injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact (h _).symm

theorem toQuotient_surjective : Function.Surjective (toQuotient H) := by
  intro z
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ z
  exact ⟨commutatorEquiv H y, by simp [toQuotient]⟩

variable {H}

theorem exists_quotient_witness {p k : ℕ} {E P : Subgroup M}
    (hE : IsMulCommutative E) (hEp : ∀ x ∈ E, x ^ p = 1) (hc : Nat.card E = p ^ k)
    (hED : E ≤ ⁅H, H⁆) (hPD : P ≤ ⁅H, H⁆) (hP2 : IsPGroup 2 P)
    (hEz : ∀ x ∈ E, (∀ y ∈ ⁅H, H⁆, x * y = y * x) → x = 1)
    (hPz : ∃ x ∈ P, ∃ y ∈ ⁅H, H⁆, x * y ≠ y * x)
    (hEP : ∀ e ∈ E, ∀ x ∈ P, e * x * e⁻¹ ∈ P) :
    ∃ E' P' : Subgroup (DerivedCentralQuotient H), IsMulCommutative E' ∧
      (∀ x ∈ E', x ^ p = 1) ∧ Nat.card E' = p ^ k ∧ P' ≠ ⊥ ∧ IsPGroup 2 P' ∧
      E' ≤ Subgroup.normalizer (P' : Set (DerivedCentralQuotient H)) := by
  set D := ⁅H, H⁆
  set π := toQuotient H
  have hcen : ∀ a : D, π a = 1 ↔ ∀ y ∈ D, (a : M) * y = y * a := by
    intro a
    rw [toQuotient_eq_one_iff]
    constructor
    · intro h y hy
      exact congrArg Subtype.val (h ⟨y, hy⟩)
    · intro h y
      exact Subtype.ext (h y y.2)
  refine ⟨(E.subgroupOf D).map π, (P.subgroupOf D).map π, ⟨⟨fun a b => ?_⟩⟩, ?_, ?_, ?_, ?_,
    ?_⟩
  · obtain ⟨a', ha', ha⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨b', hb', hb⟩ := Subgroup.mem_map.mp b.2
    have hab : (a' : M) * b' = b' * a' :=
      congrArg Subtype.val (hE.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩)
    apply Subtype.ext
    change (a : DerivedCentralQuotient H) * b = b * a
    rw [← ha, ← hb, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hab
  · intro x hx
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow]
    have : x' ^ p = 1 := Subtype.ext (by simpa using hEp _ hx')
    rw [this, map_one]
  · rw [← hc]
    have hinj : Set.InjOn π (E.subgroupOf D) := by
      intro a ha b hb hab
      have h1 : π (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
      have h3 : ((a⁻¹ * b : D) : M) = 1 :=
        hEz _ (E.mul_mem (E.inv_mem ha) hb) ((hcen _).mp h1)
      exact inv_mul_eq_one.mp (Subtype.ext h3)
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hED).toEquiv]
    exact (Nat.card_image_of_injOn hinj).trans rfl
  · obtain ⟨x, hx, y, hy, hxy⟩ := hPz
    intro hbot
    have hmem : π ⟨x, hPD hx⟩ ∈ (P.subgroupOf D).map π := ⟨⟨x, hPD hx⟩, hx, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hxy ((hcen _).mp hmem y hy)
  · exact (hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPD).symm).map π
  · rintro _ ⟨e, he, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨e * x * e⁻¹, hEP _ he _ hx, by simp⟩
    · rintro ⟨x, hx, hxz⟩
      refine ⟨e⁻¹ * x * e, ?_, ?_⟩
      · simpa [Subgroup.mem_subgroupOf] using hEP _ (E.inv_mem he) _ hx
      · rw [map_mul, map_mul, hxz, map_inv]
        group

theorem exists_quotient_witness_of_commute {p k : ℕ} {E : Subgroup M} {t : M}
    (hE : IsMulCommutative E) (hEp : ∀ x ∈ E, x ^ p = 1) (hc : Nat.card E = p ^ k)
    (hED : E ≤ ⁅H, H⁆) (htD : t ∈ ⁅H, H⁆) (ht2 : t ^ 2 = 1)
    (hEz : ∀ x ∈ E, (∀ y ∈ ⁅H, H⁆, x * y = y * x) → x = 1)
    (htz : ∃ y ∈ ⁅H, H⁆, t * y ≠ y * t)
    (hEt : ∀ e ∈ E, e * t = t * e) :
    ∃ E' P' : Subgroup (DerivedCentralQuotient H), IsMulCommutative E' ∧
      (∀ x ∈ E', x ^ p = 1) ∧ Nat.card E' = p ^ k ∧ P' ≠ ⊥ ∧ IsPGroup 2 P' ∧
      E' ≤ Subgroup.normalizer (P' : Set (DerivedCentralQuotient H)) := by
  refine exists_quotient_witness hE hEp hc hED (P := Subgroup.zpowers t)
    ((Subgroup.zpowers_le).mpr htD) ?_ hEz ⟨t, Subgroup.mem_zpowers t, htz⟩ ?_
  · refine IsPGroup.of_card (n := 1) ?_
    have hle : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one ht2
    have hne : orderOf t ≠ 1 := by
      rw [Ne, orderOf_eq_one_iff]
      rintro rfl
      obtain ⟨y, -, hy⟩ := htz
      exact hy (by simp)
    rw [Nat.card_zpowers, pow_one]
    rcases (Nat.dvd_prime Nat.prime_two).mp hle with h | h
    · exact absurd h hne
    · exact h
  · intro e he x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hc' : Commute e (t ^ n) := ((Commute.zpow_right (hEt e he) n))
    rw [hc'.eq, mul_assoc, mul_inv_cancel, mul_one]
    exact Subgroup.zpow_mem_zpowers t n

end CFSG.RankThree.PartTwo.Census.Spin

namespace CFSG.RankThree.PartTwo.Census.Spin

open Matrix

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {M : AddSubgroup V} {η : Type*} [Fintype η]
  (b : Module.Basis η ℤ M)

@[expose] def HasIntMatrix (T : Module.End ℚ V) (X : Matrix η η ℤ) : Prop :=
  ∀ s, T (b s : V) = ∑ r, X r s • (b r : V)

variable {b}

namespace HasIntMatrix

theorem unique {T : Module.End ℚ V} {X X' : Matrix η η ℤ} (h : HasIntMatrix b T X)
    (h' : HasIntMatrix b T X') : X = X' := by
  classical
  ext r s
  have hs := (h s).symm.trans (h' s)
  have hM : ∑ r, X r s • b r = ∑ r, X' r s • b r := by
    apply Subtype.ext
    simpa only [AddSubmonoidClass.coe_finsetSum, AddSubgroup.coe_zsmul] using hs
  have := congrArg (fun x => b.repr x r) hM
  simpa [map_sum, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_apply] using this

theorem mul [DecidableEq η] {T T' : Module.End ℚ V} {X X' : Matrix η η ℤ} (h : HasIntMatrix b T X)
    (h' : HasIntMatrix b T' X') : HasIntMatrix b (T * T') (X * X') := by
  intro s
  rw [Module.End.mul_apply, h' s, map_sum]
  have e1 : ∀ k, T (X' k s • (b k : V)) = ∑ r, (X r k * X' k s) • (b r : V) := by
    intro k
    rw [map_zsmul, h k, Finset.smul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [smul_smul, mul_comm]
  simp only [e1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Matrix.mul_apply, Finset.sum_smul]

theorem add {T T' : Module.End ℚ V} {X X' : Matrix η η ℤ} (h : HasIntMatrix b T X)
    (h' : HasIntMatrix b T' X') : HasIntMatrix b (T + T') (X + X') := by
  intro s
  rw [LinearMap.add_apply, h s, h' s, ← Finset.sum_add_distrib]
  simp only [Matrix.add_apply, add_smul]

theorem sub {T T' : Module.End ℚ V} {X X' : Matrix η η ℤ} (h : HasIntMatrix b T X)
    (h' : HasIntMatrix b T' X') : HasIntMatrix b (T - T') (X - X') := by
  intro s
  rw [LinearMap.sub_apply, h s, h' s, ← Finset.sum_sub_distrib]
  simp only [Matrix.sub_apply, sub_smul]

theorem one [DecidableEq η] : HasIntMatrix b (1 : Module.End ℚ V) (1 : Matrix η η ℤ) := by
  intro s
  rw [Module.End.one_apply, Finset.sum_eq_single s]
  · simp
  · intro r _ hr
    simp [Matrix.one_apply_ne hr]
  · simp

theorem zero : HasIntMatrix b (0 : Module.End ℚ V) (0 : Matrix η η ℤ) := by
  intro s
  simp

end HasIntMatrix

end CFSG.RankThree.PartTwo.Census.Spin

namespace CFSG.RankThree.PartTwo.Census.Spin

open Matrix

variable {R : Type*} [CommRing R] {N : Type*} [Fintype N] [DecidableEq N]

structure SqZeroPair (E F : Matrix N N R) : Prop where
  ee : E * E = 0
  ff : F * F = 0
  efe : E * F * E = E
  fef : F * E * F = F

namespace SqZeroPair

@[expose] def φ (E F : Matrix N N R) (a b c d : R) : Matrix N N R :=
  a • (E * F) + b • E + c • F + d • (F * E) + (1 - E * F - F * E)

variable {E F : Matrix N N R}

section Algebra

variable (h : SqZeroPair E F)
include h

omit [DecidableEq N] in
theorem e_mul_e_mul (X : Matrix N N R) : E * (E * X) = 0 := by
  rw [← mul_assoc, h.ee, zero_mul]

omit [DecidableEq N] in
theorem f_mul_f_mul (X : Matrix N N R) : F * (F * X) = 0 := by rw [← mul_assoc, h.ff, zero_mul]

omit [DecidableEq N] in
theorem efe' : E * (F * E) = E := by rw [← mul_assoc, h.efe]

omit [DecidableEq N] in
theorem fef' : F * (E * F) = F := by rw [← mul_assoc, h.fef]

omit [DecidableEq N] in
theorem efe_mul (X : Matrix N N R) : E * (F * (E * X)) = E * X := by
  rw [← mul_assoc, ← mul_assoc, h.efe]

omit [DecidableEq N] in
theorem fef_mul (X : Matrix N N R) : F * (E * (F * X)) = F * X := by
  rw [← mul_assoc, ← mul_assoc, h.fef]

theorem φ_mul (a b c d a' b' c' d' : R) :
    φ E F a b c d * φ E F a' b' c' d' =
      φ E F (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [φ, add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul,
    mul_one, mul_assoc, e_mul_e_mul h, f_mul_f_mul h, efe' h, fef' h, h.ee, h.ff, smul_zero,
    mul_zero]
  module

end Algebra

theorem φ_one_zero_zero_one : φ E F (1 : R) 0 0 1 = 1 := by
  simp only [φ, one_smul, zero_smul, add_zero]
  abel

theorem φ_upper (u : R) : φ E F 1 u 0 1 = 1 + u • E := by
  simp only [φ, one_smul, zero_smul, add_zero]
  abel

theorem φ_lower (v : R) : φ E F 1 0 v 1 = 1 + v • F := by
  simp only [φ, one_smul, zero_smul, add_zero]
  abel

@[expose] def φm (E F : Matrix N N R) (g : Matrix (Fin 2) (Fin 2) R) : Matrix N N R :=
  φ E F (g 0 0) (g 0 1) (g 1 0) (g 1 1)

@[expose] def φHom (h : SqZeroPair E F) : Matrix (Fin 2) (Fin 2) R →* Matrix N N R where
  toFun := φm E F
  map_one' := by
    change φ E F ((1 : Matrix (Fin 2) (Fin 2) R) 0 0) ((1 : Matrix (Fin 2) (Fin 2) R) 0 1)
      ((1 : Matrix (Fin 2) (Fin 2) R) 1 0) ((1 : Matrix (Fin 2) (Fin 2) R) 1 1) = 1
    rw [one_apply_eq, one_apply_eq, one_apply_ne (by decide), one_apply_ne (by decide)]
    exact φ_one_zero_zero_one
  map_mul' g g' := by
    change φ E F _ _ _ _ = φ E F _ _ _ _ * φ E F _ _ _ _
    rw [φ_mul h]
    simp only [mul_apply, Fin.sum_univ_two]

theorem φHom_apply (h : SqZeroPair E F) (g : Matrix (Fin 2) (Fin 2) R) :
    h.φHom g = φ E F (g 0 0) (g 0 1) (g 1 0) (g 1 1) :=
  rfl

@[expose] def ψ (h : SqZeroPair E F) : SpecialLinearGroup (Fin 2) R →* GL N R :=
  (Units.map h.φHom).comp SpecialLinearGroup.toGL

theorem coe_ψ (h : SqZeroPair E F) (g : SpecialLinearGroup (Fin 2) R) :
    ((h.ψ g : GL N R) : Matrix N N R) =
      φ E F ((g : Matrix (Fin 2) (Fin 2) R) 0 0) ((g : Matrix (Fin 2) (Fin 2) R) 0 1)
        ((g : Matrix (Fin 2) (Fin 2) R) 1 0) ((g : Matrix (Fin 2) (Fin 2) R) 1 1) :=
  rfl

theorem commute_φ {X : Matrix N N R} (hE : Commute E X) (hF : Commute F X) (a b c d : R) :
    Commute (φ E F a b c d) X := by
  have hEF : Commute (E * F) X := hE.mul_left hF
  have hFE : Commute (F * E) X := hF.mul_left hE
  unfold φ
  exact ((((((hEF.smul_left a).add_left (hE.smul_left b)).add_left (hF.smul_left c)).add_left
    (hFE.smul_left d)).add_left ((((Commute.one_left X).sub_left hEF).sub_left hFE))))

theorem commute_φ_φ {E' F' : Matrix N N R} (h1 : Commute E E') (h2 : Commute E F')
    (h3 : Commute F E') (h4 : Commute F F') (a b c d a' b' c' d' : R) :
    Commute (φ E F a b c d) (φ E' F' a' b' c' d') := by
  have hE : Commute E (φ E' F' a' b' c' d') := (commute_φ h1.symm h2.symm a' b' c' d').symm
  have hF : Commute F (φ E' F' a' b' c' d') := (commute_φ h3.symm h4.symm a' b' c' d').symm
  exact commute_φ hE hF a b c d

theorem φ_injective {K : Type*} [Field K] {E F : Matrix N N K} (h : SqZeroPair E F)
    (hE : E ≠ 0) {a b c d a' b' c' d' : K}
    (hφ : φ E F a b c d = φ E F a' b' c' d') : a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have hF : F ≠ 0 := by
    rintro rfl
    apply hE
    rw [← h.efe, mul_zero, zero_mul]
  have hEF : E * F ≠ 0 := by
    intro h0
    apply hE
    rw [← h.efe, h0, zero_mul]
  have hFE : F * E ≠ 0 := by
    intro h0
    apply hE
    rw [← h.efe, mul_assoc, h0, mul_zero]
  have key : ∀ x y z w : K, φ E F x y z w = x • (E * F) + y • E + z • F + w • (F * E) +
      (1 - E * F - F * E) := fun _ _ _ _ => rfl
  have hdiff : (a - a') • (E * F) + (b - b') • E + (c - c') • F + (d - d') • (F * E) = 0 := by
    have := congrArg (fun X => X - φ E F a' b' c' d') hφ
    simp only [sub_self, key] at this
    rw [← this]
    module
  have p1 := congrArg (fun X => F * X * E) hdiff
  have p2 := congrArg (fun X => F * X * F) hdiff
  have p3 := congrArg (fun X => E * X * E) hdiff
  have p4 := congrArg (fun X => E * X * F) hdiff
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_assoc, e_mul_e_mul h,
    f_mul_f_mul h, efe' h, fef' h, h.ee, h.ff, smul_zero, mul_zero, zero_mul,
    add_zero, zero_add] at p1 p2 p3 p4
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact sub_eq_zero.mp ((smul_eq_zero.mp p1).resolve_right hFE)
  · exact sub_eq_zero.mp ((smul_eq_zero.mp p2).resolve_right hF)
  · exact sub_eq_zero.mp ((smul_eq_zero.mp p3).resolve_right hE)
  · exact sub_eq_zero.mp ((smul_eq_zero.mp p4).resolve_right hEF)

end SqZeroPair

end CFSG.RankThree.PartTwo.Census.Spin


namespace CFSG.RankThree.PartTwo.Census.Spin

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : Type*} [Fintype N] [DecidableEq N]

structure IntRootData (CM : Matrix ι ι ℤ) (X Y : ι → Matrix N N ℤ) (wt : N → ι → ℤ) : Prop where
  sqZero : ∀ i, SqZeroPair (X i) (Y i)
  commute_XY : ∀ i j, i ≠ j → Commute (X i) (Y j)
  commute_XX : ∀ i j, CM i j = 0 → Commute (X i) (X j)
  commute_YY : ∀ i j, CM i j = 0 → Commute (Y i) (Y j)
  XY : ∀ i, X i * Y i = diagonal fun a => if wt a i = 1 then 1 else 0
  YX : ∀ i, Y i * X i = diagonal fun a => if wt a i = -1 then 1 else 0
  wt_cases : ∀ a i, wt a i = -1 ∨ wt a i = 0 ∨ wt a i = 1
  wt_one : ∀ i, ∃ a, wt a i = 1
  serre_XX : ∀ i j, CM i j = -1 → X i * X j * X i = 0
  serre_YY : ∀ i j, CM i j = -1 → Y i * Y j * Y i = 0

theorem lie_eq_zero_of_ad_pow {L : Type*} [LieRing L] [LieAlgebra ℚ L] {a b : L} {k : ℕ}
    (h : ((LieAlgebra.ad ℚ L a) ^ k) ⁅a, b⁆ = 0) (hk : k = 0) : ⁅a, b⁆ = 0 := by
  subst hk
  simpa using h

theorem lie_lie_eq_zero_of_ad_pow {L : Type*} [LieRing L] [LieAlgebra ℚ L] {a b : L} {k : ℕ}
    (h : ((LieAlgebra.ad ℚ L a) ^ k) ⁅a, b⁆ = 0) (hk : k = 1) : ⁅a, ⁅a, b⁆⁆ = 0 := by
  subst hk
  simpa using h

section OfRat

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {M : AddSubgroup V}
  (b : Module.Basis N ℤ M) {CM : Matrix ι ι ℤ} {E F H : ι → Module.End ℚ V}
  {X Y : ι → Matrix N N ℤ} {wt : N → ι → ℤ}

omit [Fintype ι] [DecidableEq ι] in
theorem IntRootData.ofRat (hS : TauCeti.IsSerreSystem ℚ CM H E F) (hdiag : ∀ i, CM i i = 2)
    (hE2 : ∀ i, E i * E i = 0) (hF2 : ∀ i, F i * F i = 0)
    (hX : ∀ i, HasIntMatrix b (E i) (X i)) (hY : ∀ i, HasIntMatrix b (F i) (Y i))
    (hwt : ∀ a i, H i (b a : V) = ((wt a i : ℤ) : ℚ) • (b a : V))
    (hwt1 : ∀ i, ∃ a, wt a i = 1) : IntRootData CM X Y wt := by
  have hEF : ∀ i, E i * F i - F i * E i = H i := fun i => by
    have h := hS.lie_E_F_self i
    rwa [LieRing.of_associative_ring_bracket] at h
  have hHE : ∀ i, H i * E i - E i * H i = 2 • E i := fun i => by
    have h := hS.lie_H_E i i
    rw [LieRing.of_associative_ring_bracket, hdiag] at h
    rw [h, ofNat_zsmul]
  have hHF : ∀ i, H i * F i - F i * H i = -(2 • F i) := fun i => by
    have h := hS.lie_H_F i i
    rw [LieRing.of_associative_ring_bracket, hdiag] at h
    rw [h, ofNat_zsmul]
  have hEFE : ∀ i, E i * F i * E i = E i := fun i =>
    TauCeti.Sl2.e_mul_f_mul_e_of_mul_self_eq_zero (hE2 i) (hEF i) (hHE i)
  have hFEF : ∀ i, F i * E i * F i = F i := fun i =>
    TauCeti.Sl2.f_mul_e_mul_f_of_mul_self_eq_zero (hF2 i) (hEF i) (hHF i)
  have hne : ∀ a, (b a : V) ≠ 0 := fun a h0 => b.ne_zero a (Subtype.ext h0)
  have hcase : ∀ a i, (wt a i = 1 ∧ (E i * F i) (b a : V) = b a ∧ (F i * E i) (b a : V) = 0) ∨
      (wt a i = 0 ∧ (E i * F i) (b a : V) = 0 ∧ (F i * E i) (b a : V) = 0) ∨
      (wt a i = -1 ∧ (E i * F i) (b a : V) = 0 ∧ (F i * E i) (b a : V) = b a) := fun a i =>
    TauCeti.Sl2.mul_apply_of_eq_intCast_smul (hE2 i) (hF2 i) (hEFE i) (hFEF i) (hEF i)
      (hwt a i) (hne a)
  have hdiagEF : ∀ i, HasIntMatrix b (E i * F i)
      (diagonal fun a => if wt a i = 1 then 1 else 0) := fun i a => by
    rw [Finset.sum_eq_single a (fun r _ hr => by simp [diagonal_apply_ne _ hr])
      (fun h => absurd (Finset.mem_univ a) h), diagonal_apply_eq]
    rcases hcase a i with ⟨hm, hP, -⟩ | ⟨hm, hP, -⟩ | ⟨hm, hP, -⟩
    · rw [hP, ite_eq_left hm, one_smul]
    · rw [hP, ite_eq_right (by omega), zero_smul]
    · rw [hP, ite_eq_right (by omega), zero_smul]
  have hdiagFE : ∀ i, HasIntMatrix b (F i * E i)
      (diagonal fun a => if wt a i = -1 then 1 else 0) := fun i a => by
    rw [Finset.sum_eq_single a (fun r _ hr => by simp [diagonal_apply_ne _ hr])
      (fun h => absurd (Finset.mem_univ a) h), diagonal_apply_eq]
    rcases hcase a i with ⟨hm, -, hQ⟩ | ⟨hm, -, hQ⟩ | ⟨hm, -, hQ⟩
    · rw [hQ, ite_eq_right (by omega), zero_smul]
    · rw [hQ, ite_eq_right (by omega), zero_smul]
    · rw [hQ, ite_eq_left hm, one_smul]
  refine
    { sqZero := fun i => ⟨?_, ?_, ?_, ?_⟩
      commute_XY := fun i j hij => ?_
      commute_XX := fun i j hij => ?_
      commute_YY := fun i j hij => ?_
      XY := fun i => ((hX i).mul (hY i)).unique (hdiagEF i)
      YX := fun i => ((hY i).mul (hX i)).unique (hdiagFE i)
      wt_cases := fun a i => by
        rcases hcase a i with ⟨hm, -⟩ | ⟨hm, -⟩ | ⟨hm, -⟩ <;> omega
      wt_one := hwt1
      serre_XX := fun i j hij => ?_
      serre_YY := fun i j hij => ?_ }
  · have h := (hX i).mul (hX i)
    rw [hE2] at h
    exact h.unique HasIntMatrix.zero
  · have h := (hY i).mul (hY i)
    rw [hF2] at h
    exact h.unique HasIntMatrix.zero
  · have h := ((hX i).mul (hY i)).mul (hX i)
    rw [hEFE] at h
    exact h.unique (hX i)
  · have h := ((hY i).mul (hX i)).mul (hY i)
    rw [hFEF] at h
    exact h.unique (hY i)
  · have h0 := hS.lie_E_F_of_ne i j hij
    rw [LieRing.of_associative_ring_bracket] at h0
    have h := (hX i).mul (hY j)
    rw [sub_eq_zero.mp h0] at h
    exact h.unique ((hY j).mul (hX i))
  · have h0 := lie_eq_zero_of_ad_pow (hS.ad_pow_lie_E_E i j) (by rw [hij]; rfl)
    rw [LieRing.of_associative_ring_bracket] at h0
    have h := (hX i).mul (hX j)
    rw [sub_eq_zero.mp h0] at h
    exact h.unique ((hX j).mul (hX i))
  · have h0 := lie_eq_zero_of_ad_pow (hS.ad_pow_lie_F_F i j) (by rw [hij]; rfl)
    rw [LieRing.of_associative_ring_bracket] at h0
    have h := (hY i).mul (hY j)
    rw [sub_eq_zero.mp h0] at h
    exact h.unique ((hY j).mul (hY i))
  · have h0 := lie_lie_eq_zero_of_ad_pow (hS.ad_pow_lie_E_E i j) (by rw [hij]; rfl)
    simp only [LieRing.of_associative_ring_bracket] at h0
    have h1 : E i * E j * E i = 0 := by
      have h2 : E i * (E i * E j - E j * E i) - (E i * E j - E j * E i) * E i =
          -(2 : ℚ) • (E i * E j * E i) := by
        rw [mul_sub, sub_mul, ← mul_assoc, hE2, zero_mul, mul_assoc (E j), hE2, mul_zero]
        rw [← mul_assoc]
        module
      rw [h2] at h0
      exact (smul_eq_zero.mp h0).resolve_left (by norm_num)
    have h := ((hX i).mul (hX j)).mul (hX i)
    rw [h1] at h
    exact h.unique HasIntMatrix.zero
  · have h0 := lie_lie_eq_zero_of_ad_pow (hS.ad_pow_lie_F_F i j) (by rw [hij]; rfl)
    simp only [LieRing.of_associative_ring_bracket] at h0
    have h1 : F i * F j * F i = 0 := by
      have h2 : F i * (F i * F j - F j * F i) - (F i * F j - F j * F i) * F i =
          -(2 : ℚ) • (F i * F j * F i) := by
        rw [mul_sub, sub_mul, ← mul_assoc, hF2, zero_mul, mul_assoc (F j), hF2, mul_zero]
        rw [← mul_assoc]
        module
      rw [h2] at h0
      exact (smul_eq_zero.mp h0).resolve_left (by norm_num)
    have h := ((hY i).mul (hY j)).mul (hY i)
    rw [h1] at h
    exact h.unique HasIntMatrix.zero

end OfRat

end CFSG.RankThree.PartTwo.Census.Spin

namespace CFSG.RankThree.PartTwo.Census.Spin

open Matrix

structure RootData (K : Type*) [Field K] (N : Type*) [Fintype N] [DecidableEq N]
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  CM : Matrix ι ι ℤ
  E : ι → Matrix N N K
  F : ι → Matrix N N K
  sqZero : ∀ i, SqZeroPair (E i) (F i)
  E_ne_zero : ∀ i, E i ≠ 0
  commute_EF : ∀ i j, i ≠ j → Commute (E i) (F j)
  commute_EE : ∀ i j, CM i j = 0 → Commute (E i) (E j)
  commute_FF : ∀ i j, CM i j = 0 → Commute (F i) (F j)
  G : Subgroup (GL N K)
  root : ι ⊕ ι → Multiplicative K →* G
  coe_root_inl : ∀ i u,
    ((root (.inl i) u : GL N K) : Matrix N N K) = 1 + Multiplicative.toAdd u • E i
  coe_root_inr : ∀ i u,
    ((root (.inr i) u : GL N K) : Matrix N N K) = 1 + Multiplicative.toAdd u • F i
  torus : (ι → Kˣ) →* G
  coe_torus_single : ∀ i (c : Kˣ),
    ((torus (Pi.mulSingle i c) : GL N K) : Matrix N N K) =
      SqZeroPair.φ (E i) (F i) c 0 0 (c⁻¹ : Kˣ)
  torus_conj_inl : ∀ (s : ι → Kˣ) i u,
    torus s * root (.inl i) u * (torus s)⁻¹ =
      root (.inl i) (Multiplicative.ofAdd (((∏ j, s j ^ CM j i : Kˣ) : K) *
        Multiplicative.toAdd u))
  torus_conj_inr : ∀ (s : ι → Kˣ) i u,
    torus s * root (.inr i) u * (torus s)⁻¹ =
      root (.inr i) (Multiplicative.ofAdd ((((∏ j, s j ^ CM j i)⁻¹ : Kˣ) : K) *
        Multiplicative.toAdd u))

namespace RootData

variable {K : Type*} [Field K] {N : Type*} [Fintype N] [DecidableEq N]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (R : RootData K N ι)

@[expose] def x (i : ι) (u : K) : R.G := R.root (.inl i) (Multiplicative.ofAdd u)

@[expose] def y (i : ι) (u : K) : R.G := R.root (.inr i) (Multiplicative.ofAdd u)

@[expose] def h (i : ι) (c : Kˣ) : R.G := R.torus (Pi.mulSingle i c)

@[expose] def mat (g : R.G) : Matrix N N K := ((g : GL N K) : Matrix N N K)

theorem mat_mul (g g' : R.G) : R.mat (g * g') = R.mat g * R.mat g' := rfl

theorem mat_one : R.mat 1 = 1 := rfl

theorem mat_injective : Function.Injective R.mat := fun _ _ h => Subtype.ext (Units.ext h)

theorem mat_x (i : ι) (u : K) : R.mat (R.x i u) = SqZeroPair.φ (R.E i) (R.F i) 1 u 0 1 := by
  rw [mat, x, R.coe_root_inl, toAdd_ofAdd, SqZeroPair.φ_upper]

theorem mat_y (i : ι) (u : K) : R.mat (R.y i u) = SqZeroPair.φ (R.E i) (R.F i) 1 0 u 1 := by
  rw [mat, y, R.coe_root_inr, toAdd_ofAdd, SqZeroPair.φ_lower]

theorem mat_h (i : ι) (c : Kˣ) :
    R.mat (R.h i c) = SqZeroPair.φ (R.E i) (R.F i) c 0 0 (c⁻¹ : Kˣ) :=
  R.coe_torus_single i c

theorem x_add (i : ι) (u v : K) : R.x i (u + v) = R.x i u * R.x i v := by
  rw [x, x, x, ofAdd_add, map_mul]

theorem y_add (i : ι) (u v : K) : R.y i (u + v) = R.y i u * R.y i v := by
  rw [y, y, y, ofAdd_add, map_mul]

theorem x_zero (i : ι) : R.x i 0 = 1 := by rw [x, ofAdd_zero, map_one]

theorem y_zero (i : ι) : R.y i 0 = 1 := by rw [y, ofAdd_zero, map_one]

theorem x_injective (i : ι) : Function.Injective (R.x i) := by
  intro u v huv
  have h := congrArg R.mat huv
  rw [mat, mat, x, x, R.coe_root_inl, R.coe_root_inl, toAdd_ofAdd, toAdd_ofAdd,
    add_right_inj] at h
  by_contra hne
  apply R.E_ne_zero i
  have : (u - v) • R.E i = 0 := by rw [sub_smul, h, sub_self]
  exact (smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)

theorem y_injective (i : ι) : Function.Injective (R.y i) := by
  have hF : R.F i ≠ 0 := by
    intro h0
    apply R.E_ne_zero i
    rw [← (R.sqZero i).efe, h0, mul_zero, zero_mul]
  intro u v huv
  have h := congrArg R.mat huv
  rw [mat, mat, y, y, R.coe_root_inr, R.coe_root_inr, toAdd_ofAdd, toAdd_ofAdd,
    add_right_inj] at h
  by_contra hne
  apply hF
  have : (u - v) • R.F i = 0 := by rw [sub_smul, h, sub_self]
  exact (smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)

theorem commute_of_mat {g g' : R.G} (h : Commute (R.mat g) (R.mat g')) : Commute g g' :=
  R.mat_injective (by rw [mat_mul, mat_mul]; exact h.eq)

theorem commute_one_add_smul {A B : Matrix N N K} (hAB : Commute A B) (u v : K) :
    Commute (1 + u • A) (1 + v • B) :=
  (Commute.one_left _).add_left
    ((Commute.one_right _).add_right ((hAB.smul_left u).smul_right v))

theorem commute_x_y {i j : ι} (hij : i ≠ j) (u v : K) : Commute (R.x i u) (R.y j v) := by
  apply R.commute_of_mat
  rw [mat, mat, x, y, R.coe_root_inl, R.coe_root_inr, toAdd_ofAdd, toAdd_ofAdd]
  exact commute_one_add_smul (R.commute_EF i j hij) u v

theorem commute_x_x {i j : ι} (hij : R.CM i j = 0) (u v : K) : Commute (R.x i u) (R.x j v) := by
  apply R.commute_of_mat
  rw [mat, mat, x, x, R.coe_root_inl, R.coe_root_inl, toAdd_ofAdd, toAdd_ofAdd]
  exact commute_one_add_smul (R.commute_EE i j hij) u v

theorem commute_y_y {i j : ι} (hij : R.CM i j = 0) (u v : K) : Commute (R.y i u) (R.y j v) := by
  apply R.commute_of_mat
  rw [mat, mat, y, y, R.coe_root_inr, R.coe_root_inr, toAdd_ofAdd, toAdd_ofAdd]
  exact commute_one_add_smul (R.commute_FF i j hij) u v

end RootData

section OfInt

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : Type*} [Fintype N] [DecidableEq N]

abbrev intMap (K : Type*) [Field K] (Z : Matrix N N ℤ) : Matrix N N K := Z.map (Int.cast : ℤ → K)

omit [DecidableEq N] in
theorem intMap_mul (K : Type*) [Field K] (Z W : Matrix N N ℤ) :
    intMap K (Z * W) = intMap K Z * intMap K W := by
  change (Z * W).map (Int.castRingHom K) = Z.map (Int.castRingHom K) * W.map (Int.castRingHom K)
  exact Matrix.map_mul

omit [Fintype N] [DecidableEq N] in
theorem intMap_zero (K : Type*) [Field K] : intMap (N := N) K 0 = 0 :=
  Matrix.map_zero _ Int.cast_zero

theorem units_zpow_eq_of_cases {K : Type*} [Field K] {c : Kˣ} {w : ℤ}
    (hw : w = -1 ∨ w = 0 ∨ w = 1) :
    ((c ^ w : Kˣ) : K) =
      (c : K) * (if w = 1 then 1 else 0) + ((c⁻¹ : Kˣ) : K) * (if w = -1 then 1 else 0) +
        (1 - (if w = 1 then 1 else 0) - (if w = -1 then 1 else 0)) := by
  rcases hw with rfl | rfl | rfl <;> simp

variable {K : Type*} [Field K] {CM : Matrix ι ι ℤ} {X Y : ι → Matrix N N ℤ} {wt : N → ι → ℤ}

@[expose] noncomputable def RootData.ofInt (hI : IntRootData CM X Y wt) (G : Subgroup (GL N K))
    (root : ι ⊕ ι → Multiplicative K →* G) (torus : (ι → Kˣ) →* G)
    (coe_root_inl : ∀ i u, ((root (.inl i) u : GL N K) : Matrix N N K) =
      1 + Multiplicative.toAdd u • intMap K (X i))
    (coe_root_inr : ∀ i u, ((root (.inr i) u : GL N K) : Matrix N N K) =
      1 + Multiplicative.toAdd u • intMap K (Y i))
    (coe_torus : ∀ s, ((torus s : GL N K) : Matrix N N K) =
      diagonal fun a => ((∏ j, s j ^ wt a j : Kˣ) : K))
    (torus_conj_inl : ∀ (s : ι → Kˣ) i u,
      torus s * root (.inl i) u * (torus s)⁻¹ =
        root (.inl i) (Multiplicative.ofAdd (((∏ j, s j ^ CM j i : Kˣ) : K) *
          Multiplicative.toAdd u)))
    (torus_conj_inr : ∀ (s : ι → Kˣ) i u,
      torus s * root (.inr i) u * (torus s)⁻¹ =
        root (.inr i) (Multiplicative.ofAdd ((((∏ j, s j ^ CM j i)⁻¹ : Kˣ) : K) *
          Multiplicative.toAdd u))) :
    RootData K N ι where
  CM := CM
  E i := intMap K (X i)
  F i := intMap K (Y i)
  sqZero i :=
    { ee := by rw [← intMap_mul, (hI.sqZero i).ee, intMap_zero]
      ff := by rw [← intMap_mul, (hI.sqZero i).ff, intMap_zero]
      efe := by rw [← intMap_mul, ← intMap_mul, (hI.sqZero i).efe]
      fef := by rw [← intMap_mul, ← intMap_mul, (hI.sqZero i).fef] }
  E_ne_zero i := by
    obtain ⟨a, ha⟩ := hI.wt_one i
    intro h0
    have h1 : (X i * Y i) a a = 1 := by
      rw [hI.XY, diagonal_apply_eq]
      exact ite_eq_left ha
    have h2 : intMap K (X i * Y i) a a = 1 := by
      change (((X i * Y i) a a : ℤ) : K) = 1
      rw [h1, Int.cast_one]
    rw [intMap_mul, h0, zero_mul] at h2
    exact zero_ne_one h2
  commute_EF i j hij := by
    change intMap K _ * intMap K _ = intMap K _ * intMap K _
    rw [← intMap_mul, ← intMap_mul, (hI.commute_XY i j hij).eq]
  commute_EE i j hij := by
    change intMap K _ * intMap K _ = intMap K _ * intMap K _
    rw [← intMap_mul, ← intMap_mul, (hI.commute_XX i j hij).eq]
  commute_FF i j hij := by
    change intMap K _ * intMap K _ = intMap K _ * intMap K _
    rw [← intMap_mul, ← intMap_mul, (hI.commute_YY i j hij).eq]
  G := G
  root := root
  coe_root_inl := coe_root_inl
  coe_root_inr := coe_root_inr
  torus := torus
  coe_torus_single i c := by
    rw [coe_torus, SqZeroPair.φ, ← intMap_mul, ← intMap_mul, hI.XY, hI.YX]
    ext a a'
    by_cases haa : a = a'
    · subst haa
      have hprod : (∏ j, (Pi.mulSingle i c : ι → Kˣ) j ^ wt a j : Kˣ) = c ^ wt a i := by
        rw [Finset.prod_eq_single i
          (fun j _ hj => by rw [Pi.mulSingle_eq_of_ne hj, _root_.one_zpow])
          (fun h => absurd (Finset.mem_univ i) h), Pi.mulSingle_eq_same]
      rw [diagonal_apply_eq, hprod, units_zpow_eq_of_cases (hI.wt_cases a i)]
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply_eq,
        Matrix.map_apply, diagonal_apply_eq, smul_eq_mul, zero_mul, add_zero]
      split_ifs <;> simp
    · simp [diagonal_apply_ne _ haa, Matrix.one_apply_ne haa]
  torus_conj_inl := torus_conj_inl
  torus_conj_inr := torus_conj_inr

theorem RootData.ofInt_E (hI : IntRootData CM X Y wt) (G : Subgroup (GL N K))
    (root : ι ⊕ ι → Multiplicative K →* G) (torus : (ι → Kˣ) →* G) (h1 h2 h3 h4 h5) (i : ι) :
    (RootData.ofInt hI G root torus h1 h2 h3 h4 h5).E i = intMap K (X i) :=
  rfl

end OfInt

end CFSG.RankThree.PartTwo.Census.Spin
