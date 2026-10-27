module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ya
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22y
import CFSG.LinearAlgebra.SteinbergBQEvenSL2OddCyclic
import CFSG.Quasithin.SteinbergOuterPrimeControl
import CFSG.RankThree.PartOne.CTP.SeitzL2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open scoped Pointwise

namespace P22y

section AutL2

theorem exists_equiv_sl2 {X : Type} [Group X] {n : ℕ} (h : IsL2Ev X n) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ n ∧
      Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  exact ⟨F, inferInstance, inferInstance, charP_two_of_card hF, hF,
    ⟨e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm⟩⟩

noncomputable def psl2EquivSl2 (F : Type) [Field F] [CharP F 2] :
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) F ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
  (QuotientGroup.quotientMulEquivOfEq center_sl2_eq_bot).trans QuotientGroup.quotientBot

theorem isCyclic_of_isPGroup_of_isL2Ev {X : Type} [Group X] {n : ℕ} (h : IsL2Ev X n) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (P : Subgroup X) (hP : IsPGroup p P) : IsCyclic P := by
  obtain ⟨F, _, _, _, _, ⟨e⟩⟩ := exists_equiv_sl2 h
  haveI : Fact p.Prime := ⟨hp⟩
  have hc := CFSG.LinearAlgebra.even_SL2_odd_prime_subgroups_cyclic hp2 (P.map e.toMonoidHom)
    (hP.map _)
  exact isCyclic_of_injective (P.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom
    (P.equivMapOfInjective e.toMonoidHom e.injective).injective

theorem conj_injective_of_center_eq_bot {X : Type} [Group X] (hZ : Subgroup.center X = ⊥) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  intro a b hab
  have hc : a⁻¹ * b ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := congrArg (fun α : MulAut X => α g) hab
    simp only [MulAut.conj_apply] at h1
    calc g * (a⁻¹ * b) = a⁻¹ * (a * g * a⁻¹) * b := by group
      _ = a⁻¹ * (b * g * b⁻¹) * b := by rw [h1]
      _ = a⁻¹ * b * g := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact inv_mul_eq_one.1 hc

theorem isCyclic_range_inf_inner {X : Type} [Group X] {n : ℕ} (h : IsL2Ev X n) {P : Type} [Group P]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hexp : ∀ x : P, x ^ p = 1) (φ : P →* MulAut X) :
    IsCyclic ↥(φ.range ⊓ (MulAut.conj : X →* MulAut X).range) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hZ := center_eq_bot_of_isL2Ev h
  have hinj := conj_injective_of_center_eq_bot hZ
  set B : Subgroup X := (φ.range ⊓ (MulAut.conj : X →* MulAut X).range).comap MulAut.conj with hB
  have hBp : IsPGroup p B := by
    intro b
    refine ⟨1, ?_⟩
    obtain ⟨y, hy⟩ := b.2.1
    have h1 : MulAut.conj ((b : X) ^ p) = 1 := by
      rw [map_pow, ← hy, ← map_pow, hexp, map_one]
    have h2 : (b : X) ^ p = 1 := hinj (h1.trans (map_one _).symm)
    rw [pow_one]
    exact Subtype.ext h2
  haveI := isCyclic_of_isPGroup_of_isL2Ev h hp hp2 B hBp
  have hmap : B.map (MulAut.conj : X →* MulAut X) = φ.range ⊓ (MulAut.conj : X →* MulAut X).range :=
    Subgroup.map_comap_eq_self inf_le_right
  rw [← hmap]
  exact isCyclic_of_surjective ((MulAut.conj : X →* MulAut X).subgroupMap B)
    ((MulAut.conj : X →* MulAut X).subgroupMap_surjective B)

theorem exists_equiv_psl2 {X : Type} [Group X] {n : ℕ} (h : IsL2Ev X n) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ n ∧
      Nonempty (X ≃* CFSG.GorensteinWalter.PSL2 F) := by
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := exists_equiv_sl2 h
  exact ⟨F, inferInstance, inferInstance, inferInstance, hF, ⟨e.trans (psl2EquivSl2 F).symm⟩⟩

theorem isCyclic_outer_of_isL2Ev {X : Type} [Group X] {n : ℕ} (h : IsL2Ev X n) :
    IsCyclic (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) := by
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := exists_equiv_psl2 h
  have hev : Even (Nat.card F) := by
    rw [hF]
    exact (Nat.even_pow.2 ⟨even_two, by have := one_le_of_card hF; omega⟩)
  haveI := CFSG.Quasithin.OuterPrimeControl.outer_psl2_isCyclic F (Or.inl hev)
  exact isCyclic_of_surjective
    (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).symm.toMonoidHom
    (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).symm.surjective

theorem exists_pow_eq_of_isCyclic {C : Type} [Group C] [Finite C] [IsCyclic C] {p : ℕ} (hp : p.Prime)
    {a b : C} (ha : a ^ p = 1) (ha1 : a ≠ 1) (hb : b ^ p = 1) : ∃ k : ℕ, a ^ k = b := by
  haveI : Fact p.Prime := ⟨hp⟩
  letI : CommGroup C := IsCyclic.commGroup
  set K : Subgroup C := Subgroup.closure {a, b} with hK
  have hexp : ∀ x ∈ K, x ^ p = 1 := by
    intro x hx
    have hle : K ≤ (powMonoidHom p : C →* C).ker := by
      rw [hK, Subgroup.closure_le]
      rintro y (rfl | rfl)
      · exact ha
      · exact hb
    exact hle hx
  have hKcard : Nat.card K ∣ p := by
    rw [← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (hexp x x.2)
  have haK : a ∈ K := Subgroup.subset_closure (Set.mem_insert a _)
  have hbK : b ∈ K := Subgroup.subset_closure (Set.mem_insert_of_mem a rfl)
  have hord : orderOf a = p := orderOf_eq_prime ha ha1
  have hzp : Subgroup.zpowers a = K := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 haK) ?_
    rw [Nat.card_zpowers, hord]
    exact Nat.le_of_dvd hp.pos hKcard
  have hbz : b ∈ Subgroup.zpowers a := hzp ▸ hbK
  obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers).2 hbz
  exact ⟨k, hk⟩

theorem exists_pow_mul_mem_inner {X : Type} [Group X] [Finite X] {n : ℕ} (h : IsL2Ev X n) {p : ℕ}
    (hp : p.Prime) {x y : MulAut X} (hx : x ^ p = 1) (hy : y ^ p = 1)
    (hxi : x ∉ (MulAut.conj : X →* MulAut X).range) :
    ∃ k : ℕ, x ^ k * y ∈ (MulAut.conj : X →* MulAut X).range := by
  haveI := isCyclic_outer_of_isL2Ev h
  set π : MulAut X →* CFSG.ComponentClassification.OuterAutomorphisms.Outer X :=
    QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner X) with hπ
  have hker : ∀ z : MulAut X, π z = 1 ↔ z ∈ (MulAut.conj : X →* MulAut X).range := fun z => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rfl
  have hx1 : π x ≠ 1 := fun h1 => hxi ((hker x).1 h1)
  obtain ⟨k, hk⟩ := exists_pow_eq_of_isCyclic hp (a := π x) (b := π y)
    (by rw [← map_pow, hx, map_one]) hx1 (by rw [← map_pow, hy, map_one])
  refine ⟨(p - 1) * k, (hker _).1 ?_⟩
  rw [map_mul, map_pow, ← hk, ← pow_add, show (p - 1) * k + k = p * k by
    have := hp.one_lt
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel this.le], pow_mul, ← map_pow, hx,
    map_one, one_pow]

theorem exists_sylow_fixed_of_equiv {X Y : Type} [Group X] [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]
    (e : X ≃* Y) (z : MulAut X) (ω' : Sylow p Y) (hω' : MulAut.congr e z • ω' = ω') :
    ∃ ω : Sylow p X, z • ω = ω := by
  have hf : Function.Surjective e.symm.toMonoidHom := fun x =>
    ⟨e x, by rw [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]⟩
  refine ⟨ω'.mapSurjective hf, ?_⟩
  apply Sylow.ext
  rw [Sylow.pointwise_smul_def]
  change z • (ω' : Subgroup Y).map e.symm.toMonoidHom = (ω' : Subgroup Y).map e.symm.toMonoidHom
  have hω'' : ∀ y : Y, y ∈ (ω' : Subgroup Y) ↔ ∃ t ∈ (ω' : Subgroup Y), MulAut.congr e z t = y := by
    intro y
    have := Subgroup.ext_iff.1 (congrArg (fun P : Sylow p Y => (P : Subgroup Y)) hω') y
    rw [Sylow.pointwise_smul_def, Subgroup.mem_smul_pointwise_iff_exists] at this
    simpa [MulAut.smul_def] using this.symm
  ext x
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨s, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨MulAut.congr e z t, (hω'' _).2 ⟨t, ht, rfl⟩, ?_⟩
    simp [MulAut.smul_def, MulAut.congr_apply]
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨t', ht', rfl⟩ := (hω'' t).1 ht
    refine ⟨e.symm t', ⟨t', ht', rfl⟩, ?_⟩
    simp [MulAut.smul_def, MulAut.congr_apply]

theorem exists_sylow_fixed {X : Type} [Group X] [Finite X] {n : ℕ} (h : IsL2Ev X n) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (z : MulAut X) (hz : orderOf z = p)
    (hzi : z ∉ (MulAut.conj : X →* MulAut X).range) : ∃ ω : Sylow 2 X, z • ω = ω := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := exists_equiv_psl2 h
  set z' : MulAut (CFSG.GorensteinWalter.PSL2 F) := MulAut.congr e z with hz'
  have hz'o : orderOf z' = p := by
    rw [hz', MulEquiv.orderOf_eq, hz]
  have hz'i : ∀ g, z' ≠ MulAut.conj g := by
    intro g hg
    apply hzi
    refine ⟨e.symm g, MulEquiv.ext fun x => ?_⟩
    have h1 : e (z x) = g * e x * g⁻¹ := by
      have := congrArg (fun α : MulAut (CFSG.GorensteinWalter.PSL2 F) => α (e x)) hg
      simpa [hz', MulAut.congr_apply, MulAut.conj_apply] using this
    rw [MulAut.conj_apply]
    apply e.injective
    rw [map_mul, map_mul, map_inv, e.apply_symm_apply, h1]
  obtain ⟨τ, β, -, hτ⟩ := CFSG.RankThree.PartOne.CTP.exists_conj_fieldAut hp (hp.odd_of_ne_two hp2)
    ⟨hz'o, hz'i⟩
  set Sinf : Sylow 2 (CFSG.GorensteinWalter.PSL2 F) :=
    CFSG.GorensteinWalter.psl2ProjectiveLineEquivSylow F hF
      (CFSG.GorensteinWalter.psl2ProjectiveInfinity F) with hS
  have hfS : CFSG.GorensteinWalter.psl2FieldAut F τ • Sinf = Sinf := by
    have h1 := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_projectiveLine_infinity F hF τ
    rw [CFSG.GorensteinWalter.psl2MulAutProjectiveLine_apply] at h1
    have h2 := congrArg (CFSG.GorensteinWalter.psl2ProjectiveLineEquivSylow F hF) h1
    rwa [Equiv.apply_symm_apply] at h2
  refine exists_sylow_fixed_of_equiv e z (β • Sinf) ?_
  rw [← hz', hτ, mul_smul, mul_smul, inv_smul_smul, hfS]

theorem exists_sylow_index_le {X : Type} [Group X] [Finite X] {n : ℕ} (h : IsL2Ev X n) {P : Type} [Group P]
    [Finite P] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hexp : ∀ x : P, x ^ p = 1)
    (hPab : ∀ x y : P, x * y = y * x) (φ : P →* MulAut X) :
    ∃ ω : Sylow 2 X, ((MulAction.stabilizer (MulAut X) ω).comap φ).index ≤ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hrp : ∀ x ∈ φ.range, x ^ p = 1 := by
    rintro _ ⟨y, rfl⟩
    rw [← map_pow, hexp, map_one]
  refine uc22p22y_exists_fixed_index_le hp hexp hPab φ _ (isCyclic_range_inf_inner h hp hp2 hexp φ)
    (fun x hx y hy hxi => exists_pow_mul_mem_inner h hp (hrp x hx) (hrp y hy) hxi) ?_
  intro z hz hzi
  have hz1 : z ≠ 1 := fun h1 => hzi (h1 ▸ Subgroup.one_mem _)
  exact exists_sylow_fixed h hp hp2 z (orderOf_eq_prime (hrp z hz) hz1) hzi

theorem exists_sylow_fixed_of_not_dvd {X : Type} [Group X] [Finite X] {n : ℕ} (h : IsL2Ev X n)
    {P : Type} [Group P] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hexp : ∀ x : P, x ^ p = 1)
    (hpX : ¬ p ∣ Nat.card X) (φ : P →* MulAut X) : ∃ ω : Sylow 2 X, ∀ x : P, φ x • ω = ω := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hZ := center_eq_bot_of_isL2Ev h
  have hinj := conj_injective_of_center_eq_bot hZ
  have hrp : ∀ x : P, φ x ^ p = 1 := fun x => by rw [← map_pow, hexp, map_one]
  have hinn : ∀ x : P, φ x ∈ (MulAut.conj : X →* MulAut X).range → φ x = 1 := by
    rintro x ⟨g, hg⟩
    have h1 : MulAut.conj (g ^ p) = 1 := by rw [map_pow, hg, hrp]
    have h2 : g ^ p = 1 := hinj (h1.trans (map_one _).symm)
    have h3 : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one h2
    have h4 : orderOf g ∣ Nat.card X := orderOf_dvd_natCard g
    rcases (Nat.dvd_prime hp).1 h3 with h5 | h5
    · rw [orderOf_eq_one_iff] at h5
      rw [← hg, h5, map_one]
    · exact absurd (h5 ▸ h4) hpX
  by_cases hall : ∀ x : P, φ x = 1
  · obtain ⟨ω⟩ := (inferInstance : Nonempty (Sylow 2 X))
    exact ⟨ω, fun x => by rw [hall x, one_smul]⟩
  · push Not at hall
    obtain ⟨x₀, hx₀⟩ := hall
    have hx₀i : φ x₀ ∉ (MulAut.conj : X →* MulAut X).range := fun hi => hx₀ (hinn x₀ hi)
    obtain ⟨ω, hω⟩ := exists_sylow_fixed h hp hp2 (φ x₀) (orderOf_eq_prime (hrp x₀) hx₀) hx₀i
    refine ⟨ω, fun y => ?_⟩
    obtain ⟨k, hk⟩ := exists_pow_mul_mem_inner h hp (hrp x₀) (hrp y) hx₀i
    have hk' : φ (x₀ ^ k * y) = 1 := by
      apply hinn
      rwa [map_mul, map_pow]
    have hy : φ y = (φ x₀ ^ k)⁻¹ := by
      rw [map_mul, map_pow] at hk'
      exact eq_inv_of_mul_eq_one_right hk'
    have hpow : ∀ j : ℕ, φ x₀ ^ j • ω = ω := by
      intro j
      induction j with
      | zero => rw [pow_zero, one_smul]
      | succ j ih => rw [pow_succ, mul_smul, hω, ih]
    rw [hy, inv_smul_eq_iff, hpow]

end AutL2

end P22y

end CFSG.LocalAnalysis.UniquenessCase.UC22
