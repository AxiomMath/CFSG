module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeBlock
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalEndNode
public import CFSG.RankThree.PartOne.KF.UnitaryDiag
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits

public section

namespace CFSG.StandardType

namespace TableBUE

open CFSG.Assembly

section Abstract

variable {H R : Type*} [Group H] [Group R] (π : H →* R)

theorem centralizer_map_eq_of_noTorsion (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center H) {p : ℕ} (hnp : ∀ z ∈ π.ker, z ^ p = 1 → z = 1)
    {t : H} (ht : t ^ p = 1) :
    Subgroup.centralizer {π t} = (Subgroup.centralizer {t}).map π := by
  apply le_antisymm
  · intro r hr
    obtain ⟨g, rfl⟩ := hπ r
    rw [Subgroup.mem_centralizer_singleton_iff] at hr
    set z := g * t * g⁻¹ * t⁻¹ with hz
    have hzk : z ∈ π.ker := by
      rw [MonoidHom.mem_ker, hz, map_mul, map_mul, map_mul, map_inv, map_inv]
      calc π g * π t * (π g)⁻¹ * (π t)⁻¹ = π t * π g * (π g)⁻¹ * (π t)⁻¹ := by rw [← hr]
        _ = 1 := by group
    have hzc := Subgroup.mem_center_iff.mp (hker hzk)
    have hgt : g * t * g⁻¹ = z * t := by rw [hz]; group
    have hzp : z ^ p = 1 := by
      have h1 : (g * t * g⁻¹) ^ p = 1 := by
        rw [show g * t * g⁻¹ = MulAut.conj g t from rfl, ← map_pow, ht, map_one]
      rw [hgt, (Commute.mul_pow (hzc t).symm), ht, mul_one] at h1
      exact h1
    have hz1 := hnp z hzk hzp
    refine ⟨g, Subgroup.mem_centralizer_singleton_iff.mpr ?_, rfl⟩
    rw [hz1, one_mul] at hgt
    calc g * t = g * t * g⁻¹ * g := by group
      _ = t * g := by rw [hgt]
  · rintro _ ⟨g, hg, rfl⟩
    have hg' := Subgroup.mem_centralizer_singleton_iff.mp hg
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hg']

theorem isEndNode_map_of_cover (hker : π.ker ≤ Subgroup.center H) {A : Subgroup H}
    (hinj : ∀ y ∈ A, π y = 1 → y = 1) {t : H} (htA : t ∈ A) (ht1 : t ≠ 1) {J : Subgroup H}
    (hJq : CFSG.IsQuasisimple J) (hJC : J ≤ Subgroup.centralizer {t})
    (hcomm : ∀ g ∈ Subgroup.centralizer {t}, ∀ g' ∈ Subgroup.centralizer {t},
      g * g' * g⁻¹ * g'⁻¹ ∈ J)
    (hC : Subgroup.centralizer {π t} = (Subgroup.centralizer {t}).map π)
    (hcent : ∀ y ∈ A, (∀ j ∈ J, y * j = j * y) ↔ y ∈ Subgroup.zpowers t) :
    TableBOrth.IsEndNode (A.map π) (π t) := by
  have hJq' : CFSG.IsQuasisimple (J.map π) := by
    have h := CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_range hJq (π.comp J.subtype)
      (by
        intro x hx
        rw [Subgroup.mem_center_iff]
        intro y
        exact Subtype.ext (Subgroup.mem_center_iff.mp (hker hx) y))
    rwa [MonoidHom.range_comp, Subgroup.range_subtype] at h
  have hJperf : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.1 hJq.1
  obtain ⟨hlayer, hcomp⟩ := TableBSymp.largeEvenLayer_eq_of_commutator_mem
    (H := Subgroup.centralizer {π t}) (D := J.map π)
    (by rw [hC]; exact Subgroup.map_mono hJC)
    (by
      rw [hC]
      rintro _ ⟨g, hg, rfl⟩ _ ⟨g', hg', rfl⟩
      refine ⟨g * g' * g⁻¹ * g'⁻¹, hcomm g hg g' hg', ?_⟩
      simp only [map_mul, map_inv])
    hJq'
  refine ⟨⟨t, htA, rfl⟩, fun h1 => ht1 (hinj t htA h1), hlayer ▸ hcomp, ?_⟩
  rintro _ ⟨y, hyA, rfl⟩
  rw [hlayer]
  constructor
  · intro hy
    have hyJ : ∀ j ∈ J, y * j = j * y := by
      intro j hj
      have hc : ∀ k ∈ J, y * k * y⁻¹ * k⁻¹ ∈ Subgroup.center H := by
        intro k hk
        apply hker
        rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
          hy (π k) ⟨k, hk, rfl⟩]
        group
      rw [← hJperf] at hj
      exact TableBSymp.commute_of_mem_commutator hc hj
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ((hcent y hyA).mp hyJ)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [map_zpow]⟩
  · intro hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hyk : y = t ^ k := by
      have h1 : y * (t ^ k)⁻¹ = 1 := hinj _ (A.mul_mem hyA (A.inv_mem (A.zpow_mem htA k)))
        (by rw [map_mul, map_inv, map_zpow, hk, mul_inv_cancel])
      exact mul_inv_eq_one.mp h1
    have hyJ := (hcent y hyA).mpr (hyk ▸ Subgroup.zpow_mem_zpowers t k)
    rintro _ ⟨j, hj, rfl⟩
    rw [← map_mul, ← map_mul, hyJ j hj]

variable [Finite H]

theorem exists_lift_of_noTorsion (hπ : Function.Surjective π) {p : ℕ} (hp : p.Prime)
    (hnp : ∀ z ∈ π.ker, z ^ p = 1 → z = 1) {Ab : Subgroup R} (hAb : IsElemAbelian p Ab) :
    ∃ A : Subgroup H, A.map π = Ab ∧ (∀ y ∈ A, π y = 1 → y = 1) ∧ IsElemAbelian p A ∧
      Nat.card A = Nat.card Ab := by
  classical
  have := Fact.mk hp
  have : Finite R := Finite.of_surjective π hπ
  set P := Ab.comap π with hP
  obtain ⟨Q⟩ := (Sylow.nonempty : Nonempty (Sylow p ↥P))
  set A : Subgroup H := (Q : Subgroup ↥P).map P.subtype with hA
  have hApow : ∀ y ∈ A, ∃ k : ℕ, y ^ p ^ k = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨k, hk⟩ := Q.isPGroup' ⟨y, hy⟩
    exact ⟨k, by
      have := congrArg (fun z : ↥(Q : Subgroup ↥P) => ((z : ↥P) : H)) hk
      simpa using this⟩
  have hinj : ∀ y ∈ A, π y = 1 → y = 1 := by
    intro y hy hy1
    obtain ⟨k, hk⟩ := hApow y hy
    induction k generalizing y with
    | zero => simpa using hk
    | succ k ih =>
      have h1 : y ^ p ^ k = 1 := hnp _ (by rw [MonoidHom.mem_ker, map_pow, hy1, one_pow])
        (by rw [← pow_mul, ← pow_succ, hk])
      exact ih y hy hy1 h1
  have hAP : A.map π ≤ Ab := by
    rintro _ ⟨_, ⟨y, -, rfl⟩, rfl⟩
    exact y.2
  have hAbp : IsPGroup p Ab := fun a => ⟨1, by rw [pow_one]; exact Subtype.ext (hAb.2 a a.2)⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hAbp
  have hkerp : ¬ p ∣ Nat.card π.ker := by
    intro hdvd
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have h1 : (z : H) = 1 := hnp z z.2 (by
      have := pow_orderOf_eq_one z
      rw [hz] at this
      exact congrArg Subtype.val this)
    have : z = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hz
    exact hp.one_lt.ne hz
  set f : ↥P →* R := π.comp P.subtype with hf
  have hfr : f.range = Ab := by
    ext r
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hr
      obtain ⟨g, rfl⟩ := hπ r
      exact ⟨⟨g, hr⟩, rfl⟩
  have hfk : Nat.card f.ker = Nat.card π.ker := by
    refine Nat.card_congr ⟨fun z => ⟨(z : ↥P), z.2⟩, fun z => ⟨⟨z, ?_⟩, z.2⟩, fun _ => rfl,
      fun _ => rfl⟩
    show π z ∈ Ab
    rw [MonoidHom.mem_ker.mp z.2]
    exact Ab.one_mem
  have hPcard : Nat.card ↥P = p ^ a * Nat.card π.ker := by
    rw [← Subgroup.card_ker_mul_card_range f, hfr, hfk, ha, mul_comm]
  have hQcard : Nat.card (Q : Subgroup ↥P) = p ^ a := by
    rw [Sylow.card_eq_multiplicity, hPcard, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero)
      (Nat.card_pos (α := π.ker)).ne', Finsupp.add_apply, Nat.Prime.factorization_pow hp,
      Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hkerp, add_zero]
  have hAcard : Nat.card A = p ^ a := by
    rw [hA, Nat.card_congr
      ((Q : Subgroup ↥P).equivMapOfInjective _ P.subtype_injective).toEquiv.symm, hQcard]
  have hinj' : Function.Injective (π.comp A.subtype) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    exact Subtype.ext (hinj y y.2 hy)
  have hmapcard : Nat.card (A.map π) = Nat.card A := by
    rw [show A.map π = (π.comp A.subtype).range by
      rw [MonoidHom.range_comp, Subgroup.range_subtype],
      Nat.card_congr (MonoidHom.ofInjective hinj').toEquiv.symm]
  have hmap : A.map π = Ab :=
    Subgroup.eq_of_le_of_card_ge hAP (by rw [hmapcard, hAcard, ha])
  refine ⟨A, hmap, hinj, ⟨⟨⟨?_⟩⟩, ?_⟩, by rw [hAcard, ha]⟩
  · rintro ⟨x, hx⟩ ⟨y, hy⟩
    apply Subtype.ext
    show x * y = y * x
    have h1 : x * y * x⁻¹ * y⁻¹ = 1 := hinj _ (A.mul_mem (A.mul_mem (A.mul_mem hx hy)
      (A.inv_mem hx)) (A.inv_mem hy)) (by
        have hc := TableB.IsElemAbelian.comm hAb (hmap ▸ ⟨x, hx, rfl⟩ : π x ∈ Ab)
          (hmap ▸ ⟨y, hy, rfl⟩ : π y ∈ Ab)
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
        group)
    calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = y * x := by rw [h1, one_mul]
  · intro x hx
    exact hinj _ (A.pow_mem hx p) (by
      rw [map_pow]
      exact hAb.2 _ (hmap ▸ ⟨x, hx, rfl⟩))

end Abstract

section Unitary

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.SectionRank.OddCover

variable {K : Type} [Field K] {n d : ℕ} (h : UnitaryFieldData 2 n K)

include h in
theorem unitarySU_le_primeFormUnitary :
    unitarySU 2 n K d ≤ primeFormUnitary h (idGram K d) := by
  intro g hg
  rw [mem_primeFormUnitary, idGram, Units.val_one, Matrix.mul_one]
  exact ((mem_unitarySU_iff h).mp hg).2

include h in
theorem mem_unitarySU_of_mem_primeFormUnitary {g : GL (Fin d) K}
    (hg : g ∈ primeFormUnitary h (idGram K d)) (hdet : (g : Matrix (Fin d) (Fin d) K).det = 1) :
    g ∈ unitarySU 2 n K d := by
  rw [unitarySU_eq_gramSU h, mem_gramSU_iff_unitary]
  exact ⟨hg, hdet⟩

@[expose] noncomputable def conjSU (P : GL (Fin d) K) (hP : P ∈ primeFormUnitary h (idGram K d)) :
    ↥(unitarySU 2 n K d) ≃* ↥(unitarySU 2 n K d) where
  toFun x := ⟨P⁻¹ * x * P, mem_unitarySU_of_mem_primeFormUnitary h
    ((primeFormUnitary h (idGram K d)).mul_mem ((primeFormUnitary h (idGram K d)).mul_mem
      ((primeFormUnitary h (idGram K d)).inv_mem hP) (unitarySU_le_primeFormUnitary h x.2)) hP)
    (by
      rw [Units.val_mul, Units.val_mul, det_mul, det_mul, ((mem_unitarySU_iff h).mp x.2).1,
        mul_one, ← det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, det_one])⟩
  invFun x := ⟨P * x * P⁻¹, mem_unitarySU_of_mem_primeFormUnitary h
    ((primeFormUnitary h (idGram K d)).mul_mem ((primeFormUnitary h (idGram K d)).mul_mem
      hP (unitarySU_le_primeFormUnitary h x.2)) ((primeFormUnitary h (idGram K d)).inv_mem hP))
    (by
      rw [Units.val_mul, Units.val_mul, det_mul, det_mul, ((mem_unitarySU_iff h).mp x.2).1,
        mul_one, ← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one])⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem coe_conjSU (P : GL (Fin d) K) (hP : P ∈ primeFormUnitary h (idGram K d))
    (x : ↥(unitarySU 2 n K d)) : ((conjSU h P hP x : ↥(unitarySU 2 n K d)) : GL (Fin d) K) =
      P⁻¹ * x * P :=
  rfl

abbrev suScalars (n d : ℕ) (K : Type) [Field K] : Subgroup ↥(unitarySU 2 n K d) :=
  (LargeEvenScalars (Fin d) K).subgroupOf (unitarySU 2 n K d)

theorem map_conjSU_suScalars (P : GL (Fin d) K) (hP : P ∈ primeFormUnitary h (idGram K d)) :
    (suScalars n d K).map (conjSU h P hP : ↥(unitarySU 2 n K d) →* ↥(unitarySU 2 n K d)) =
      suScalars n d K := by
  have key : ∀ x : ↥(unitarySU 2 n K d), x ∈ suScalars n d K → conjSU h P hP x = x := by
    intro x hx
    rw [Subgroup.mem_subgroupOf, largeEvenScalars_def,
      ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at hx
    apply Subtype.ext
    rw [coe_conjSU, mul_assoc, ← (Subgroup.mem_center_iff.mp hx P), ← mul_assoc,
      inv_mul_cancel, one_mul]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change (conjSU h P hP) y ∈ suScalars n d K
    rw [key y hy]
    exact hy
  · intro hx
    exact ⟨x, hx, key x hx⟩

@[expose] noncomputable def conjProj (P : GL (Fin d) K)
    (hP : P ∈ primeFormUnitary h (idGram K d)) :
    LargeEvenProj (unitarySU 2 n K d) ≃* LargeEvenProj (unitarySU 2 n K d) :=
  QuotientGroup.congr _ _ (conjSU h P hP) (map_conjSU_suScalars h P hP)

theorem conjProj_mk (P : GL (Fin d) K) (hP : P ∈ primeFormUnitary h (idGram K d))
    (x : ↥(unitarySU 2 n K d)) :
    conjProj h P hP (LargeEvenProjMk _ x) = LargeEvenProjMk _ (conjSU h P hP x) :=
  QuotientGroup.congr_mk _ _ _ _ x

include h in
theorem eq_one_of_mem_suScalars {p : ℕ} (hp : p.Prime) (hpd : ¬ p ∣ d)
    {z : ↥(unitarySU 2 n K d)} (hz : z ∈ (LargeEvenProjMk (unitarySU 2 n K d)).ker)
    (hzp : z ^ p = 1) : z = 1 := by
  have hz' : z ∈ suScalars n d K := by
    rw [LargeEvenProjMk, QuotientGroup.ker_mk'] at hz
    exact hz
  rw [Subgroup.mem_subgroupOf] at hz'
  obtain ⟨c, hc⟩ := hz'
  have hdet := ((mem_unitarySU_iff h).mp z.2).1
  rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
  have hcd : c ^ d = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hdet, Units.val_one])
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hpd (dvd_zero p)
  have : NeZero d := ⟨hd0⟩
  have hcp : c ^ p = 1 := by
    have h1 : ((z ^ p : ↥(unitarySU 2 n K d)) : GL (Fin d) K) = 1 := by rw [hzp]; rfl
    rw [Subgroup.coe_pow, ← hc, ← map_pow] at h1
    have h2 := congrArg (fun g : GL (Fin d) K => (g : Matrix (Fin d) (Fin d) K)) h1
    have h3 := congrFun (congrFun h2 0) 0
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Units.val_one, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h3
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h3)
  have hgcd : Nat.gcd d p = 1 := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd)
  have hc1 : c = 1 := by
    have := pow_gcd_eq_one.mpr ⟨hcd, hcp⟩
    rwa [hgcd, pow_one] at this
  apply Subtype.ext
  rw [← hc, hc1, map_one]
  rfl

theorem exists_diagHom_of_isDiag {g : GL (Fin d) K} (hg : (g : Matrix (Fin d) (Fin d) K).IsDiag) :
    ∃ σ : Fin d → Kˣ, g = diagHom d σ := by
  have hne : ∀ i, (g : Matrix (Fin d) (Fin d) K) i i ≠ 0 := by
    intro i hi
    have h1 : ((g * g⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i = 1 := by
      rw [mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
    rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i
      (fun k _ hk => by rw [hg (Ne.symm hk), zero_mul]) (fun h' => absurd (Finset.mem_univ i) h'),
      hi, zero_mul] at h1
    exact zero_ne_one h1
  refine ⟨fun i => Units.mk0 _ (hne i), Units.ext ?_⟩
  ext i j
  rw [coe_diagHom]
  by_cases hij : i = j
  · subst hij
    simp
  · rw [hg hij, Matrix.diagonal_apply_ne _ hij]

include h in
theorem exists_conj_diag {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    {A : Subgroup ↥(unitarySU 2 n K d)} (hA : IsElemAbelian p A) :
    ∃ (P : GL (Fin d) K) (hP : P ∈ primeFormUnitary h (idGram K d)), ∀ x ∈ A,
      ∃ σ : Fin d → Kˣ,
        ((conjSU h P hP x : ↥(unitarySU 2 n K d)) : GL (Fin d) K) = diagHom d σ := by
  set ι := Subgroup.inclusion (unitarySU_le_primeFormUnitary (d := d) h) with hι
  obtain ⟨P, hPd⟩ := CFSG.RankThree.PartOne.KFU.exists_unitary_conj_diag h hp hpq (A.map ι)
    (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, TableB.IsElemAbelian.comm hA ha hb])
    (by
      rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hA.2 a ha, map_one])
  refine ⟨P, P.2, fun x hx => exists_diagHom_of_isDiag ?_⟩
  have := hPd (ι x) ⟨x, hx, rfl⟩
  simpa [coe_conjSU, hι] using this

end Unitary

end TableBUE

end CFSG.StandardType
