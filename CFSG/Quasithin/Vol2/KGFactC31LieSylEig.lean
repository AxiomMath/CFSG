module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.KGC31

section Eigen

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
variable {Λ : Type*} {G : Type*} [Group G]

theorem conj_inv_mem_of_mem_normalizer {R : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (R : Set G)) {x : G} (hx : x ∈ R) : g⁻¹ * x * g ∈ R :=
  (Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * x * g)).2 (by
    rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group])

theorem conj_mem_of_mem_normalizer {R : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (R : Set G)) {x : G} (hx : x ∈ R) : g * x * g⁻¹ ∈ R :=
  (Subgroup.mem_normalizer_iff.1 hg x).1 hx

theorem eigen_repr_apply [Fintype Λ] {b : Module.Basis Λ K V} {ρ : G →* Module.End K V}
    {R : Subgroup G} {χ : Λ → G → K} (hχ : ∀ x ∈ R, ∀ i, ρ x (b i) = χ i x • b i) {v : V}
    {x : G} (hx : x ∈ R) (j : Λ) : b.repr (ρ x v) j = χ j x * b.repr v j := by
  have hsum : ρ x v = ∑ k, (b.repr v k * χ k x) • b k := by
    conv_lhs => rw [← b.sum_repr v]
    simp only [map_sum, map_smul, hχ x hx, smul_smul]
  rw [hsum, map_sum, Finsupp.finset_sum_apply]
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
    smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp [mul_comm]
  · intro k _ hk
    simp [Ne.symm hk]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem eigen_support [Fintype Λ] {b : Module.Basis Λ K V} {ρ : G →* Module.End K V}
    {R : Subgroup G} {χ : Λ → G → K} (hχ : ∀ x ∈ R, ∀ i, ρ x (b i) = χ i x • b i)
    {ψ : G → K} {v : V}
    (hv : ∀ x ∈ R, ρ x v = ψ x • v) {i : Λ} (hi : b.repr v i ≠ 0) :
    ∀ x ∈ R, χ i x = ψ x := by
  intro x hx
  have h2 : b.repr (ρ x v) i = b.repr (ψ x • v) i := by rw [hv x hx]
  rw [eigen_repr_apply hχ hx i, map_smul, Finsupp.smul_apply, smul_eq_mul] at h2
  exact mul_right_cancel₀ hi h2

theorem eigen_inv_apply (ρ : G →* Module.End K V) (u : G) (w : V) :
    ρ u⁻¹ (ρ u w) = w := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

theorem eigen_conj_vec {b : Module.Basis Λ K V} {ρ : G →* Module.End K V} {R : Subgroup G}
    {χ : Λ → G → K} (hχ : ∀ x ∈ R, ∀ i, ρ x (b i) = χ i x • b i) {u : G}
    (hu : u ∈ Subgroup.normalizer (R : Set G)) (i : Λ) (x : G) (hx : x ∈ R) :
    ρ x (ρ u (b i)) = χ i (u⁻¹ * x * u) • ρ u (b i) := by
  have e1 : ρ (x * u) (b i) = ρ x (ρ u (b i)) := by rw [map_mul, Module.End.mul_apply]
  have e2 : ρ (u * (u⁻¹ * x * u)) (b i) = ρ u (ρ (u⁻¹ * x * u) (b i)) := by
    rw [map_mul, Module.End.mul_apply]
  have e3 : x * u = u * (u⁻¹ * x * u) := by group
  rw [← e1, e3, e2, hχ _ (conj_inv_mem_of_mem_normalizer hu hx) i, map_smul]

theorem eigen_conj_vec_ne_zero {b : Module.Basis Λ K V} (ρ : G →* Module.End K V) (u : G) (i : Λ) :
    ρ u (b i) ≠ 0 := by
  intro h
  have h1 := eigen_inv_apply ρ u (b i)
  rw [h, map_zero] at h1
  exact b.ne_zero i h1.symm

theorem eigen_conj_exists [Fintype Λ] {b : Module.Basis Λ K V} {ρ : G →* Module.End K V}
    {R : Subgroup G} {χ : Λ → G → K} (hχ : ∀ x ∈ R, ∀ i, ρ x (b i) = χ i x • b i) {u : G}
    (hu : u ∈ Subgroup.normalizer (R : Set G)) (i : Λ) :
    ∃ j, ∀ x ∈ R, χ j x = χ i (u⁻¹ * x * u) := by
  have hne := eigen_conj_vec_ne_zero (b := b) ρ u i
  obtain ⟨j, hj⟩ : ∃ j, b.repr (ρ u (b i)) j ≠ 0 := by
    by_contra hcon
    apply hne
    exact b.forall_coord_eq_zero_iff.1 (fun j => by simpa using not_exists.1 hcon j)
  exact ⟨j, eigen_support hχ (fun x hx => eigen_conj_vec hχ hu i x hx) hj⟩

theorem eigen_mem_centralizer_of_char {b : Module.Basis Λ K V} {ρ : G →* Module.End K V}
    (hρ : Function.Injective ρ) {R : Subgroup G} {χ : Λ → G → K}
    (hχ : ∀ x ∈ R, ∀ i, ρ x (b i) = χ i x • b i) {u : G}
    (hu : u ∈ Subgroup.normalizer (R : Set G))
    (hc : ∀ i, ∀ y ∈ R, χ i (u⁻¹ * y * u) = χ i y) :
    u ∈ Subgroup.centralizer (R : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hz : u⁻¹ * y * u ∈ R := conj_inv_mem_of_mem_normalizer hu hy
  have hzy : u⁻¹ * y * u = y := by
    apply hρ
    apply b.ext
    intro i
    rw [hχ _ hz i, hχ y hy i, hc i y hy]
  calc y * u = u * (u⁻¹ * y * u) := by group
    _ = u * y := by rw [hzy]

theorem eigen_pow_mem_centralizer [Fintype Λ] {b : Module.Basis Λ K V} {ρ : G →* Module.End K V}
    (hρ : Function.Injective ρ) {R : Subgroup G} {χ : Λ → G → K}
    (hχ : ∀ x ∈ R, ∀ i, ρ x (b i) = χ i x • b i) {u : G}
    (hu : u ∈ Subgroup.normalizer (R : Set G)) :
    u ^ (Fintype.card Λ).factorial ∈ Subgroup.centralizer (R : Set G) := by
  classical
  have hpow : ∀ k : ℕ, ∀ y ∈ R, (u ^ k)⁻¹ * y * u ^ k ∈ R := fun k y hy =>
    conj_inv_mem_of_mem_normalizer (pow_mem hu k) hy
  choose φ hφ using fun i => eigen_conj_exists hχ hu i
  have hit : ∀ k : ℕ, ∀ i, ∀ x ∈ R, χ ((φ^[k]) i) x = χ i ((u ^ k)⁻¹ * x * u ^ k) := by
    intro k
    induction k with
    | zero => intro i x _; simp
    | succ k ih =>
      intro i x hx
      rw [Function.iterate_succ_apply, ih (φ i) x hx, hφ i _ (hpow k x hx)]
      congr 1
      rw [pow_succ]
      group
  let tr : Λ → G → K := fun j x => if x ∈ R then χ j x else 0
  have hT : (Finset.univ.image tr).card ≤ Fintype.card Λ := by
    calc (Finset.univ.image tr).card ≤ (Finset.univ : Finset Λ).card := Finset.card_image_le
      _ = Fintype.card Λ := Finset.card_univ
  have key : ∀ (i : Λ) (a c : ℕ), a < c → (∀ x ∈ R, χ ((φ^[a]) i) x = χ ((φ^[c]) i) x) →
      ∃ m, 0 < m ∧ m ≤ c ∧ ∀ y ∈ R, χ i y = χ i ((u ^ m)⁻¹ * y * u ^ m) := by
    intro i a c hac heq
    obtain ⟨m, rfl⟩ : ∃ m, c = a + m := ⟨c - a, by omega⟩
    refine ⟨m, by omega, by omega, fun y hy => ?_⟩
    have hx : (u ^ a) * y * (u ^ a)⁻¹ ∈ R := conj_mem_of_mem_normalizer (pow_mem hu a) hy
    have h1 := heq _ hx
    rw [hit a i _ hx, hit (a + m) i _ hx] at h1
    have e1 : (u ^ a)⁻¹ * (u ^ a * y * (u ^ a)⁻¹) * u ^ a = y := by group
    have e2 : (u ^ (a + m))⁻¹ * (u ^ a * y * (u ^ a)⁻¹) * u ^ (a + m)
        = (u ^ m)⁻¹ * y * u ^ m := by
      rw [pow_add]
      group
    rw [e1, e2] at h1
    exact h1
  have hper : ∀ i, ∃ m, 0 < m ∧ m ≤ Fintype.card Λ ∧
      ∀ y ∈ R, χ i y = χ i ((u ^ m)⁻¹ * y * u ^ m) := by
    intro i
    obtain ⟨a, ha, c, hc, hne, hf⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := Finset.range (Fintype.card Λ + 1)) (t := Finset.univ.image tr)
      (f := fun k => tr ((φ^[k]) i)) (by rw [Finset.card_range]; omega)
      (fun k _ => Finset.mem_image_of_mem _ (Finset.mem_univ _))
    have ha' := Finset.mem_range.1 ha
    have hc' := Finset.mem_range.1 hc
    have hfa : ∀ x ∈ R, χ ((φ^[a]) i) x = χ ((φ^[c]) i) x := by
      intro x hx
      have := congrFun hf x
      simpa [tr, hx] using this
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · obtain ⟨m, hm0, hmc, hm⟩ := key i a c h hfa
      exact ⟨m, hm0, by omega, hm⟩
    · obtain ⟨m, hm0, hmc, hm⟩ := key i c a h (fun x hx => (hfa x hx).symm)
      exact ⟨m, hm0, by omega, hm⟩
  have hall : ∀ i, ∀ y ∈ R,
      χ i ((u ^ (Fintype.card Λ).factorial)⁻¹ * y * u ^ (Fintype.card Λ).factorial) = χ i y := by
    intro i y hy
    obtain ⟨m, hm0, hmle, hm⟩ := hper i
    obtain ⟨t, ht⟩ := Nat.dvd_factorial hm0 hmle
    have hj : ∀ j : ℕ, ∀ z ∈ R, χ ((φ^[m * j]) i) z = χ i z := by
      intro j
      induction j with
      | zero => intro z _; simp
      | succ j ih =>
        intro z hz
        rw [show m * (j + 1) = m + m * j by ring, Function.iterate_add_apply, hit m _ z hz,
          ih _ (hpow m z hz)]
        exact (hm z hz).symm
    have h1 : χ ((φ^[(Fintype.card Λ).factorial]) i) y = χ i y := by
      rw [ht]
      exact hj t y hy
    rw [hit (Fintype.card Λ).factorial i y hy] at h1
    exact h1
  exact eigen_mem_centralizer_of_char hρ hχ (pow_mem hu _) hall

end Eigen

end CFSG.Quasithin.KGC31

end
