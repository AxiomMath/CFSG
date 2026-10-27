module

public import CFSG.RankThree.Classical.SteinbergCFProjectiveTwoAutomorphisms

public section

namespace CFSG.RankThree.PartOne

open Matrix Matrix.ProjGenLinGroup CFSG.RankThree.Classical
open scoped MatrixGroups

universe u

theorem commute_of_comm_with_commutator {G : Type*} [Group G] {a u : G} {n m : ℕ}
    (hn : a ^ n = 1) (hcop : Nat.Coprime n m) (hm : (a * u * a⁻¹ * u⁻¹) ^ m = 1)
    (hac : Commute a (a * u * a⁻¹ * u⁻¹)) : a * u = u * a := by
  have hau : a * u * a⁻¹ = (a * u * a⁻¹ * u⁻¹) * u := by group
  generalize a * u * a⁻¹ * u⁻¹ = c at hm hac hau
  have hj : ∀ j : ℕ, a ^ j * u * (a ^ j)⁻¹ = c ^ j * u := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hcj : a * c ^ j * a⁻¹ = c ^ j := by
        rw [mul_inv_eq_iff_eq_mul]
        exact (hac.pow_right j).eq
      calc a ^ (j + 1) * u * (a ^ (j + 1))⁻¹ = a * (a ^ j * u * (a ^ j)⁻¹) * a⁻¹ := by group
        _ = a * (c ^ j * u) * a⁻¹ := by rw [ih]
        _ = (a * c ^ j * a⁻¹) * (a * u * a⁻¹) := by group
        _ = c ^ j * (c * u) := by rw [hcj, hau]
        _ = c ^ (j + 1) * u := by rw [pow_succ, mul_assoc]
  have h1 : c ^ n * u = u := by
    have := hj n
    rw [hn, inv_one, one_mul, mul_one] at this
    exact this.symm
  have h2 : c ^ n = 1 := mul_eq_right.mp h1
  have h3 : c = 1 := by
    have := (pow_gcd_eq_one (a := c)).2 ⟨h2, hm⟩
    rwa [hcop, pow_one] at this
  have h4 : a * u * a⁻¹ = u := by rw [hau, h3, one_mul]
  calc a * u = a * u * a⁻¹ * a := by group
    _ = u * a := by rw [h4]

theorem commute_of_central_commutator {G : Type*} [Group G] {a u : G} {n m : ℕ}
    (hn : a ^ n = 1) (hu : u ^ m = 1) (hcop : Nat.Coprime n m)
    (hac : Commute a (a * u * a⁻¹ * u⁻¹)) (huc : Commute u (a * u * a⁻¹ * u⁻¹)) :
    a * u = u * a := by
  refine commute_of_comm_with_commutator hn hcop ?_ hac
  have hau : a * u * a⁻¹ = (a * u * a⁻¹ * u⁻¹) * u := by group
  have h1 : (a * u * a⁻¹) ^ m = 1 := by
    rw [conj_pow, hu, mul_one, mul_inv_cancel]
  rw [hau] at h1
  rwa [huc.symm.mul_pow m, hu, mul_one] at h1


variable {k : Type u} [Field k]

@[expose] noncomputable def toPGL : SL(2, k) →* PGL(2, k) :=
  (mk : GL (Fin 2) k →* PGL(2, k)).comp Matrix.SpecialLinearGroup.toGL

theorem toPGL_eq_one_iff {A : SL(2, k)} : toPGL A = 1 ↔ A ∈ Subgroup.center SL(2, k) :=
  (QuotientGroup.eq_one_iff _).trans (Matrix.SpecialLinearGroup.toGL_mem_center_iff A)

theorem liftOfSurjective_apply' {G H K : Type*} [Group G] [Group H] [Group K] (f : G →* H)
    (hf : Function.Surjective f) (g : G →* K) (hg : f.ker ≤ g.ker) (x : G) :
    (MonoidHom.liftOfSurjective f hf ⟨g, hg⟩) (f x) = g x := by
  simp [MonoidHom.liftOfSurjective]

theorem exists_pgl_hom {G : Type*} [Group G] (μ : SL(2, k) × SL(2, k) →* G)
    (hμ : ∀ z ∈ μ.ker, z.1 ∈ Subgroup.center SL(2, k) ∧ z.2 ∈ Subgroup.center SL(2, k)) :
    ∃ ν : μ.range →* PGL(2, k) × PGL(2, k),
      (∀ z, ν (μ.rangeRestrict z) = (toPGL z.1, toPGL z.2)) ∧
      ∀ x ∈ ν.ker, x ∈ Subgroup.center μ.range := by
  let f : SL(2, k) × SL(2, k) →* PGL(2, k) × PGL(2, k) := toPGL.prodMap toPGL
  have hf : μ.rangeRestrict.ker ≤ f.ker := by
    intro z hz
    rw [MonoidHom.ker_rangeRestrict] at hz
    obtain ⟨h1, h2⟩ := hμ z hz
    exact Prod.ext (toPGL_eq_one_iff.mpr h1) (toPGL_eq_one_iff.mpr h2)
  refine ⟨MonoidHom.liftOfSurjective μ.rangeRestrict μ.rangeRestrict_surjective ⟨f, hf⟩, ?_, ?_⟩
  · intro z
    exact liftOfSurjective_apply' μ.rangeRestrict μ.rangeRestrict_surjective f hf z
  · intro x hx
    obtain ⟨z, rfl⟩ := μ.rangeRestrict_surjective x
    have h := liftOfSurjective_apply' μ.rangeRestrict μ.rangeRestrict_surjective f hf z
    rw [MonoidHom.mem_ker, h] at hx
    obtain ⟨hx1, hx2⟩ := Prod.ext_iff.mp hx
    have c1 := toPGL_eq_one_iff.mp hx1
    have c2 := toPGL_eq_one_iff.mp hx2
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨w, rfl⟩ := μ.rangeRestrict_surjective y
    rw [← map_mul, ← map_mul]
    congr 1
    refine Prod.ext ?_ ?_
    · exact (Subgroup.mem_center_iff.mp c1 w.1)
    · exact (Subgroup.mem_center_iff.mp c2 w.2)

theorem pgl_centralizes_of_normalizes {H : Type*} [Group H] (hk : ringChar k ≠ 2)
    (ψ : H →* PGL(2, k)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {P U : Subgroup H} [Finite U]
    (hPp : IsPGroup p P) (hU : IsPGroup 2 U) (hPU : ∀ a ∈ P, ∀ u ∈ U, a * u * a⁻¹ ∈ U) :
    ∀ a ∈ P, ∀ u ∈ U, ψ a * ψ u = ψ u * ψ a := by
  set Q : Subgroup PGL(2, k) := U.map ψ with hQ
  have hQ2 : IsPGroup 2 Q := hU.map ψ
  have : Finite Q := Finite.of_surjective (fun u : U => (⟨ψ u, u, u.2, rfl⟩ : Q))
    (by rintro ⟨_, u, hu, rfl⟩; exact ⟨⟨u, hu⟩, rfl⟩)
  have hnorm : P.map ψ ≤ Subgroup.normalizer (Q : Set PGL(2, k)) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨a * u * a⁻¹, hPU a ha u hu, by simp [map_mul]⟩
    · rintro ⟨u, hu, hu'⟩
      refine ⟨a⁻¹ * u * a, ?_, ?_⟩
      · simpa using hPU a⁻¹ (P.inv_mem ha) u hu
      · have : ψ a * q * (ψ a)⁻¹ = ψ u := hu'.symm
        have h2 : q = (ψ a)⁻¹ * ψ u * ψ a := by rw [← this]; group
        rw [h2]
        simp [map_mul, map_inv]
  have hPm : IsPGroup p (P.map ψ) := hPp.map ψ
  let φ : (P.map ψ) →* MulAut Q :=
    (Subgroup.normalizerMonoidHom Q).comp (Subgroup.inclusion hnorm)
  intro a ha u hu
  have h1 := (odd_projective_linear_two_subgroup_automorphisms_no_large_primes k hk Q hQ2).2 p hp
    hp3 (P.map ψ) hPm φ ⟨ψ a, a, ha, rfl⟩
  have h2 := congrArg (fun e : MulAut Q => (e ⟨ψ u, u, hu, rfl⟩ : Q).1) h1
  simp only [φ, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
    MulAut.one_apply, Subgroup.inclusion] at h2
  have h3 : ψ a * ψ u * (ψ a)⁻¹ = ψ u := h2
  calc ψ a * ψ u = ψ a * ψ u * (ψ a)⁻¹ * ψ a := by group
    _ = ψ u * ψ a := by rw [h3]


theorem sl2sq_largePrime {G : Type*} [Group G] (hk : ringChar k ≠ 2)
    (μ : SL(2, k) × SL(2, k) →* G)
    (hμ : ∀ z ∈ μ.ker, z.1 ∈ Subgroup.center SL(2, k) ∧ z.2 ∈ Subgroup.center SL(2, k))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {P U : Subgroup G} [Finite U] (hP : P ≤ μ.range)
    (hU : U ≤ μ.range) (hPp : IsPGroup p P) (hU2 : IsPGroup 2 U)
    (hPU : ∀ a ∈ P, ∀ u ∈ U, a * u * a⁻¹ ∈ U) : ∀ a ∈ P, ∀ u ∈ U, a * u = u * a := by
  obtain ⟨ν, hν, hνc⟩ := exists_pgl_hom μ hμ
  let P' : Subgroup μ.range := P.subgroupOf μ.range
  let U' : Subgroup μ.range := U.subgroupOf μ.range
  have : Finite U' := Finite.of_injective (Subgroup.subgroupOfEquivOfLe hU).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hU).injective
  have hP'p : IsPGroup p P' :=
    hPp.of_injective (Subgroup.subgroupOfEquivOfLe hP).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hP).injective
  have hU'2 : IsPGroup 2 U' :=
    hU2.of_injective (Subgroup.subgroupOfEquivOfLe hU).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hU).injective
  have hPU' : ∀ a ∈ P', ∀ u ∈ U', a * u * a⁻¹ ∈ U' := fun a ha u hu => by
    rw [Subgroup.mem_subgroupOf] at ha hu ⊢
    simpa using hPU _ ha _ hu
  have c1 := pgl_centralizes_of_normalizes hk ((MonoidHom.fst _ _).comp ν) hp hp3 hP'p hU'2 hPU'
  have c2 := pgl_centralizes_of_normalizes hk ((MonoidHom.snd _ _).comp ν) hp hp3 hP'p hU'2 hPU'
  intro a ha u hu
  let a' : μ.range := ⟨a, hP ha⟩
  let u' : μ.range := ⟨u, hU hu⟩
  have ha' : a' ∈ P' := Subgroup.mem_subgroupOf.mpr ha
  have hu' : u' ∈ U' := Subgroup.mem_subgroupOf.mpr hu
  have h1 := c1 a' ha' u' hu'
  have h2 := c2 a' ha' u' hu'
  have hcomm : ν (a' * u' * a'⁻¹ * u'⁻¹) = 1 := by
    refine Prod.ext ?_ ?_
    · simp only [map_mul, map_inv, Prod.fst_mul, Prod.fst_inv, Prod.fst_one]
      simp only [MonoidHom.comp_apply, MonoidHom.coe_fst] at h1
      rw [h1]
      group
    · simp only [map_mul, map_inv, Prod.snd_mul, Prod.snd_inv, Prod.snd_one]
      simp only [MonoidHom.comp_apply, MonoidHom.coe_snd] at h2
      rw [h2]
      group
  have hc := hνc _ hcomm
  have hac : Commute a (a * u * a⁻¹ * u⁻¹) :=
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hc a')
  have huc : Commute u (a * u * a⁻¹ * u⁻¹) :=
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hc u')
  obtain ⟨i, hi⟩ := hPp ⟨a, ha⟩
  obtain ⟨j, hj⟩ := hU2 ⟨u, hu⟩
  have hai : a ^ (p ^ i) = 1 := by
    have := congrArg Subtype.val hi
    simpa using this
  have huj : u ^ (2 ^ j) = 1 := by
    have := congrArg Subtype.val hj
    simpa using this
  have hcop : Nat.Coprime (p ^ i) (2 ^ j) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega))
  exact commute_of_central_commutator hai huj hcop hac huc

theorem xlevel_largePrime {M : Type*} [Group M] (hk : ringChar k ≠ 2) (X : Subgroup M)
    (μ : SL(2, k) × SL(2, k) →* M)
    (hμ : ∀ z ∈ μ.ker, z.1 ∈ Subgroup.center SL(2, k) ∧ z.2 ∈ Subgroup.center SL(2, k))
    (hSn : ∀ g ∈ X, ∀ s ∈ μ.range, g * s * g⁻¹ ∈ μ.range) (hsq : ∀ g ∈ X, g ^ 2 ∈ μ.range)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {P U : Subgroup M} [Finite U] (hPX : P ≤ X)
    (hUX : U ≤ X) (hPp : IsPGroup p P) (hU2 : IsPGroup 2 U)
    (hPU : ∀ a ∈ P, ∀ u ∈ U, a * u * a⁻¹ ∈ U) : ∀ a ∈ P, ∀ u ∈ U, a * u = u * a := by
  have hPS : ∀ a ∈ P, a ∈ μ.range := by
    intro a ha
    obtain ⟨i, hi⟩ := hPp ⟨a, ha⟩
    have hai : a ^ (p ^ i) = 1 := by simpa using congrArg Subtype.val hi
    have hodd : Odd (p ^ i) := (hp.odd_of_ne_two (by omega)).pow
    obtain ⟨r, hr⟩ := hodd
    have h2 : a = (a ^ 2) ^ (r + 1) := by
      calc a = a ^ (p ^ i) * a := by rw [hai, one_mul]
        _ = a ^ (2 * r + 1 + 1) := by rw [← pow_succ, hr]
        _ = (a ^ 2) ^ (r + 1) := by rw [← pow_mul]; congr 1
    rw [h2]
    exact Subgroup.pow_mem _ (hsq a (hPX ha)) _
  set U0 : Subgroup M := U ⊓ μ.range with hU0
  have hU0le : U0 ≤ μ.range := inf_le_right
  have hU02 : IsPGroup 2 U0 := hU2.to_le inf_le_left
  have hPU0 : ∀ a ∈ P, ∀ u ∈ U0, a * u * a⁻¹ ∈ U0 := fun a ha u hu =>
    ⟨hPU a ha u hu.1,
      μ.range.mul_mem (μ.range.mul_mem (hPS a ha) hu.2) (μ.range.inv_mem (hPS a ha))⟩
  have : Finite U0 := Finite.of_injective (Subgroup.inclusion (inf_le_left : U0 ≤ U))
    (Subgroup.inclusion_injective _)
  have hcomm0 := sl2sq_largePrime hk μ hμ hp hp3 (fun a ha => hPS a ha) hU0le hPp hU02 hPU0
  intro a ha u hu
  have hcU : a * u * a⁻¹ * u⁻¹ ∈ U := U.mul_mem (hPU a ha u hu) (U.inv_mem hu)
  have hcS : a * u * a⁻¹ * u⁻¹ ∈ μ.range := by
    have h1 : u * a⁻¹ * u⁻¹ ∈ μ.range := hSn u (hUX hu) _ (μ.range.inv_mem (hPS a ha))
    have : a * u * a⁻¹ * u⁻¹ = a * (u * a⁻¹ * u⁻¹) := by group
    rw [this]
    exact μ.range.mul_mem (hPS a ha) h1
  have hc0 : a * u * a⁻¹ * u⁻¹ ∈ U0 := ⟨hcU, hcS⟩
  have hac : Commute a (a * u * a⁻¹ * u⁻¹) := hcomm0 a ha _ hc0
  obtain ⟨i, hi⟩ := hPp ⟨a, ha⟩
  have hai : a ^ (p ^ i) = 1 := by simpa using congrArg Subtype.val hi
  obtain ⟨j, hj⟩ := hU2 ⟨_, hcU⟩
  have hcj : (a * u * a⁻¹ * u⁻¹) ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
  have hcop : Nat.Coprime (p ^ i) (2 ^ j) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega))
  exact commute_of_comm_with_commutator hai hcop hcj hac

end CFSG.RankThree.PartOne
