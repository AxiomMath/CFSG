module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Perm
public import CFSG.RankThree.PartOne.S15K.CentralCover

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem exists_commute_involution_of_conj_transitive {G : Type} [Group G] [Finite G]
    {Y : Subgroup G} {a : G} {r : ℕ} (hr : r.Prime) (har : a ^ r = 1)
    (haY : ∀ y ∈ Y, a * y * a⁻¹ ∈ Y) (hrY : ¬ r ∣ Nat.card Y) {t₀ : G} (ht₀Y : t₀ ∈ Y)
    (ht₀ : t₀ ^ 2 = 1) (ht₀1 : t₀ ≠ 1)
    (hcl : ∀ t ∈ Y, t ^ 2 = 1 → t ≠ 1 → ∃ y ∈ Y, y * t₀ * y⁻¹ = t) :
    ∃ t ∈ Y, t ^ 2 = 1 ∧ t ≠ 1 ∧ a * t = t * a := by
  have : Fact r.Prime := ⟨hr⟩
  have hpow : ∀ k : ℕ, ∀ y ∈ Y, a ^ k * y * (a ^ k)⁻¹ ∈ Y := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy
      have := haY _ (ih y hy)
      rw [pow_succ', mul_inv_rev]
      simpa [mul_assoc] using this
  have hT : IsPGroup r (Subgroup.zpowers a) := by
    have hdvd : orderOf a ∣ r := orderOf_dvd_of_pow_eq_one har
    rcases (Nat.dvd_prime hr).mp hdvd with h1 | h1
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h1, pow_one])
  have hX : ∀ τ ∈ Subgroup.zpowers a, ∀ x ∈ {y : G | ∃ g ∈ Y, y = g * t₀ * g⁻¹},
      τ * x * τ⁻¹ ∈ {y : G | ∃ g ∈ Y, y = g * t₀ * g⁻¹} := by
    intro τ hτ x hx
    obtain ⟨g, hg, rfl⟩ := hx
    classical
    obtain ⟨k, -, hk⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hτ)
    have hk' : a ^ k = τ := hk
    subst hk'
    have hmem : a ^ k * (g * t₀ * g⁻¹) * (a ^ k)⁻¹ ∈ Y :=
      hpow k _ (Y.mul_mem (Y.mul_mem hg ht₀Y) (Y.inv_mem hg))
    have h2 : (a ^ k * (g * t₀ * g⁻¹) * (a ^ k)⁻¹) ^ 2 = 1 := by
      rw [conj_pow, conj_pow, ht₀, mul_one, mul_inv_cancel, mul_one, mul_inv_cancel]
    have h1 : a ^ k * (g * t₀ * g⁻¹) * (a ^ k)⁻¹ ≠ 1 := by
      intro he
      apply ht₀1
      rwa [conj_eq_one_iff, conj_eq_one_iff] at he
    obtain ⟨y, hy, hyeq⟩ := hcl _ hmem h2 h1
    exact ⟨y, hy, hyeq.symm⟩
  have hcard : ¬ r ∣ Nat.card ↥{y : G | ∃ g ∈ Y, y = g * t₀ * g⁻¹} := by
    rw [Nat.card_coe_set_eq]
    intro hdvd
    apply hrY
    rw [c23_card_eq_ncard_orbit_mul Y t₀]
    exact Dvd.dvd.mul_right hdvd _
  obtain ⟨x, ⟨g, hg, rfl⟩, hfix⟩ := c23_exists_fixed_conj hT hX hcard
  refine ⟨g * t₀ * g⁻¹, Y.mul_mem (Y.mul_mem hg ht₀Y) (Y.inv_mem hg), ?_, ?_, ?_⟩
  · rw [conj_pow, ht₀, mul_one, mul_inv_cancel]
  · intro h1
    apply ht₀1
    rwa [conj_eq_one_iff] at h1
  · have := hfix a (Subgroup.mem_zpowers a)
    calc a * (g * t₀ * g⁻¹) = a * (g * t₀ * g⁻¹) * a⁻¹ * a := by group
      _ = (g * t₀ * g⁻¹) * a := by rw [this]

theorem le_centralizer_of_central_cover {G X : Type} [Group G] [Finite G] [Group X]
    (φ : G →* X) (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center G) {r : ℕ}
    (hr : r.Prime) (hrker : ¬ r ∣ Nat.card φ.ker)
    (hM : ∀ (a : G) (Q : Subgroup G), a ^ r = 1 → Group.IsPerfect Q → ¬ r ∣ Nat.card Q →
      a ∈ Subgroup.normalizer (Q : Set G) → a ∈ Subgroup.centralizer (Q : Set G))
    {A P : Subgroup X} (hA : Nat.card A = r) (hP : ⁅P, P⁆ = P) (hrP : ¬ r ∣ Nat.card P)
    (hAP : A ≤ Subgroup.normalizer (P : Set X)) : A ≤ Subgroup.centralizer (P : Set X) := by
  intro x hx
  have hxr : x ^ r = 1 := by
    have h0 := pow_card_eq_one' (G := A) (x := ⟨x, hx⟩)
    rw [hA] at h0
    simpa using congrArg Subtype.val h0
  have hcop : Nat.Coprime (Nat.card φ.ker) r :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hr).mpr hrker)
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hr.one_lt
  obtain ⟨g, hg⟩ := hφ x
  have hφa : φ (g ^ (Nat.card φ.ker * u)) = x := by
    rw [map_pow, hg, ← Nat.mod_add_div (Nat.card φ.ker * u) r, pow_add, pow_mul, hxr, one_pow,
      mul_one, hu, pow_one]
  have har : (g ^ (Nat.card φ.ker * u)) ^ r = 1 := by
    have hgr : g ^ r ∈ φ.ker := by rw [MonoidHom.mem_ker, map_pow, hg, hxr]
    have hgrs : (g ^ r) ^ Nat.card φ.ker = 1 := by
      have h0 := pow_card_eq_one' (G := φ.ker) (x := ⟨g ^ r, hgr⟩)
      simpa using congrArg Subtype.val h0
    rw [← pow_mul, show Nat.card φ.ker * u * r = r * Nat.card φ.ker * u by ring, pow_mul,
      pow_mul, hgrs, one_pow]
  set a := g ^ (Nat.card φ.ker * u) with ha
  set C := P.comap φ with hC
  set Q : Subgroup G := ⁅C, C⁆ with hQ
  have hQperf : Group.IsPerfect Q :=
    Subgroup.isPerfect_iff.mpr (CFSG.RankThree.PartOne.S15K.commutator_comap_perfect hφ hker hP)
  have hQmap : Q.map φ = P := CFSG.RankThree.PartOne.S15K.map_commutator_comap hφ hP
  have hrQ : ¬ r ∣ Nat.card Q := by
    intro hdvd
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Q) r hdvd
    have hyr : orderOf (y : G) = r := by rw [Subgroup.orderOf_coe]; exact hy
    have hφy : φ y ∈ P := by
      rw [← hQmap]
      exact Subgroup.mem_map_of_mem φ y.2
    have hdvd' : orderOf (φ y) ∣ r := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← map_pow, ← hyr, pow_orderOf_eq_one, map_one]
    rcases (Nat.dvd_prime hr).mp hdvd' with h1 | h1
    · have hyk : (y : G) ∈ φ.ker := by
        rw [MonoidHom.mem_ker]
        exact orderOf_eq_one_iff.mp h1
      exact hrker (hyr ▸ Subgroup.orderOf_dvd_natCard φ.ker hyk)
    · exact hrP (h1 ▸ Subgroup.orderOf_dvd_natCard P hφy)
  have hCnorm : C.map (MulAut.conj a).toMonoidHom ≤ C := by
    rintro _ ⟨c, hc, rfl⟩
    change φ (a * c * a⁻¹) ∈ P
    rw [map_mul, map_mul, map_inv, hφa]
    exact (Subgroup.mem_normalizer_iff.mp (hAP hx) (φ c)).mp hc
  have haQ : a ∈ Subgroup.normalizer (Q : Set G) := by
    apply Subgroup.mem_normalizer_fintype
    intro y hy
    have hmap : Q.map (MulAut.conj a).toMonoidHom ≤ Q := by
      rw [hQ, Subgroup.map_commutator]
      exact Subgroup.commutator_mono hCnorm hCnorm
    exact hmap (Subgroup.mem_map_of_mem _ hy)
  have hcent := hM a Q har hQperf hrQ haQ
  rw [Subgroup.mem_centralizer_iff]
  intro p hp
  rw [← hQmap] at hp
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hp
  have hya := (Subgroup.mem_centralizer_iff.mp hcent) y hy
  rw [← hφa, ← map_mul, ← map_mul, hya]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
