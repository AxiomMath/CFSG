module

public import CFSG.RankThree.OddKernel.OddLift

public section

namespace CFSG.RankThree.GF2n.Stroth80

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
private theorem eq_one_of_pow_two_pow_eq_one_of_odd {N : Subgroup X} (hN : Odd (Nat.card N))
    {z : X} (hz : z ∈ N) {k : ℕ} (h : z ^ 2 ^ k = 1) : z = 1 :=
  orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hN)) (orderOf_dvd_of_pow_eq_one h)
    (Subgroup.orderOf_dvd_natCard N hz))

omit [Finite X] in
theorem commute_of_mk_commute_of_odd_center (hZ : Odd (Nat.card (Subgroup.center X))) {g t : X}
    (ht : t ^ 2 = 1)
    (h : (g : X ⧸ Subgroup.center X) * t = (t : X ⧸ Subgroup.center X) * g) : g * t = t * g := by
  set c := g * t * g⁻¹ * t⁻¹ with hcdef
  have hc : c ∈ Subgroup.center X := by
    rw [← QuotientGroup.eq_one_iff]
    simp only [hcdef, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [h]
    group
  have hct : c * t = t * c := (Subgroup.mem_center_iff.mp hc t).symm
  have h1 : g * t * g⁻¹ = c * t := by
    rw [hcdef]
    group
  have h2 : c ^ 2 = 1 := by
    have e : (c * t) * (c * t) = c ^ 2 * t ^ 2 := by
      calc (c * t) * (c * t) = c * (t * c) * t := by group
        _ = c * (c * t) * t := by rw [hct]
        _ = c ^ 2 * t ^ 2 := by rw [sq, sq]; group
    have e2 : (c * t) * (c * t) = 1 := by
      rw [← h1]
      calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
        _ = 1 := by rw [← sq, ht, mul_one, mul_inv_cancel]
    rw [e, ht, mul_one] at e2
    exact e2
  have h3 : c = 1 := eq_one_of_pow_two_pow_eq_one_of_odd hZ hc (k := 1) (by simpa using h2)
  calc g * t = c * (t * g) := by rw [hcdef]; group
    _ = t * g := by rw [h3, one_mul]

omit [Finite X] in
private theorem exists_lift_pow_two_pow_eq_one_of_odd {N : Subgroup X} [N.Normal]
    (hN : Odd (Nat.card N)) {s : X ⧸ N} {k : ℕ} (hs : s ^ 2 ^ k = 1) :
    ∃ g : X, (g : X ⧸ N) = s ∧ g ^ 2 ^ k = 1 := by
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective s
  rcases Nat.lt_or_ge 1 (2 ^ k) with hk | hk
  · obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime
      (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hN)).symm hk
    refine ⟨g₀ ^ (Nat.card N * u), ?_, ?_⟩
    · rw [QuotientGroup.mk_pow, pow_eq_pow_mod _ hs, hu, pow_one]
    · have hw : g₀ ^ 2 ^ k ∈ N := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hs]
      have hw' : (g₀ ^ 2 ^ k) ^ Nat.card N = 1 :=
        orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard N hw)
      calc (g₀ ^ (Nat.card N * u)) ^ 2 ^ k = ((g₀ ^ 2 ^ k) ^ Nat.card N) ^ u := by
            simp only [← pow_mul]
            ring_nf
        _ = 1 := by rw [hw', one_pow]
  · have h1 : 2 ^ k = 1 := le_antisymm hk Nat.one_le_two_pow
    rw [h1, pow_one] at hs
    exact ⟨1, by rw [QuotientGroup.mk_one, hs], by rw [one_pow]⟩

private theorem exists_isPGroup_map_eq_of_odd_center (hZ : Odd (Nat.card (Subgroup.center X)))
    {R : Subgroup (X ⧸ Subgroup.center X)} (hR : IsPGroup 2 R) :
    ∃ R' : Subgroup X, IsPGroup 2 R' ∧ R'.map (QuotientGroup.mk' (Subgroup.center X)) = R ∧
      ∀ g : X, (∃ k : ℕ, g ^ 2 ^ k = 1) → (g : X ⧸ Subgroup.center X) ∈ R → g ∈ R' := by
  obtain ⟨A, hA, hAR, -⟩ := CFSG.RankThree.OddKernel.exists_two_subgroup_map_eq
    (QuotientGroup.mk' (Subgroup.center X)) (QuotientGroup.mk'_surjective _)
    (by rwa [QuotientGroup.ker_mk']) R hR
  refine ⟨A, hA, hAR, fun g ⟨k, hk⟩ hgR => ?_⟩
  rw [← hAR] at hgR
  obtain ⟨b, hbA, hb⟩ := Subgroup.mem_map.mp hgR
  have hz : b⁻¹ * g ∈ Subgroup.center X := QuotientGroup.eq.mp hb
  obtain ⟨j, hj⟩ := hA ⟨b, hbA⟩
  have hbj : b ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hcomm : Commute b (b⁻¹ * g) := Subgroup.mem_center_iff.mp hz b
  have hpow : (b⁻¹ * g) ^ 2 ^ (j + k) = 1 := by
    have e : g ^ 2 ^ (j + k) = b ^ 2 ^ (j + k) * (b⁻¹ * g) ^ 2 ^ (j + k) := by
      rw [← hcomm.mul_pow, mul_inv_cancel_left]
    have hg1 : g ^ 2 ^ (j + k) = 1 := by
      rw [add_comm, pow_add, pow_mul, hk, one_pow]
    have hb1 : b ^ 2 ^ (j + k) = 1 := by
      rw [pow_add, pow_mul, hbj, one_pow]
    rw [hg1, hb1, one_mul] at e
    exact e.symm
  have h1 : b⁻¹ * g = 1 := eq_one_of_pow_two_pow_eq_one_of_odd hZ hz hpow
  rw [inv_mul_eq_one] at h1
  exact h1 ▸ hbA

theorem exists_lift_radical_of_odd_center (hZ : Odd (Nat.card (Subgroup.center X))) {t : X}
    (ht : t ^ 2 = 1) {S : Set (X ⧸ Subgroup.center X)} {P R : Subgroup (X ⧸ Subgroup.center X)}
    (hS : ∀ s ∈ S, ∃ k : ℕ, s ^ 2 ^ k = 1) (hPS : Subgroup.closure S = P)
    (hPt : P ≤ Subgroup.centralizer {(t : X ⧸ Subgroup.center X)}) (hRP : R ≤ P)
    (hRn : ∀ p ∈ P, ∀ r ∈ R, p * r * p⁻¹ ∈ R) (hR : IsPGroup 2 R) :
    ∃ (S' : Set X) (P' R' : Subgroup X), (∀ s ∈ S', ∃ k : ℕ, s ^ 2 ^ k = 1) ∧
      Subgroup.closure S' = P' ∧ P'.map (QuotientGroup.mk' (Subgroup.center X)) = P ∧
      R'.map (QuotientGroup.mk' (Subgroup.center X)) = R ∧ P' ≤ Subgroup.centralizer {t} ∧
      R' ≤ P' ∧ (∀ p ∈ P', ∀ r ∈ R', p * r * p⁻¹ ∈ R') ∧ IsPGroup 2 R' := by
  obtain ⟨R', hR', hR'R, hmem⟩ := exists_isPGroup_map_eq_of_odd_center hZ hR
  let S' : Set X := {g | (g : X ⧸ Subgroup.center X) ∈ P ∧ ∃ k : ℕ, g ^ 2 ^ k = 1}
  have hP'P : Subgroup.closure S' ≤ P.comap (QuotientGroup.mk' (Subgroup.center X)) :=
    (Subgroup.closure_le _).mpr fun g hg => hg.1
  refine ⟨S', Subgroup.closure S', R', fun s hs => hs.2, rfl, ?_, hR'R, ?_, ?_, ?_, hR'⟩
  · refine le_antisymm (Subgroup.map_le_iff_le_comap.mpr hP'P) ?_
    rw [← hPS, MonoidHom.map_closure]
    refine Subgroup.closure_mono fun s hs => ?_
    obtain ⟨k, hk⟩ := hS s hs
    obtain ⟨g, hg, hgk⟩ := exists_lift_pow_two_pow_eq_one_of_odd hZ hk
    refine ⟨g, ⟨?_, k, hgk⟩, hg⟩
    rw [hg, ← hPS]
    exact Subgroup.subset_closure hs
  · refine (Subgroup.closure_le _).mpr fun g hg => ?_
    refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have h1 := Subgroup.mem_centralizer_iff.mp (hPt hg.1) _ (Set.mem_singleton _)
    exact (commute_of_mk_commute_of_odd_center hZ ht h1.symm).symm
  · intro r hr
    refine Subgroup.subset_closure ⟨hRP ?_, ?_⟩
    · rw [← hR'R]
      exact Subgroup.mem_map_of_mem _ hr
    · obtain ⟨k, hk⟩ := hR' ⟨r, hr⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  · intro p hp r hr
    refine hmem _ ?_ ?_
    · obtain ⟨k, hk⟩ := hR' ⟨r, hr⟩
      refine ⟨k, ?_⟩
      rw [conj_pow, show r ^ 2 ^ k = 1 by simpa using congrArg Subtype.val hk, mul_one,
        mul_inv_cancel]
    · have hrR : (r : X ⧸ Subgroup.center X) ∈ R := by
        rw [← hR'R]
        exact Subgroup.mem_map_of_mem _ hr
      have h1 := hRn _ (hP'P hp) _ hrR
      rw [QuotientGroup.mk'_apply] at h1
      simpa only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] using h1

end CFSG.RankThree.GF2n.Stroth80
