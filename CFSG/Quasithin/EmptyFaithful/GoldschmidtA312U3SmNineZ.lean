module

public import CFSG.RankThree.SubgroupLists.LinearTwoFamily

public section

namespace CFSG.Quasithin.A312U3

open Matrix CFSG.Assembly.LowTwoRank CFSG.RankThree.SubgroupLists CFSG.RepresentationTheory

theorem linear_two_three_K {K : Type} [Field K] [Finite K] (h3 : (3 : K) ≠ 0)
    {H : Subgroup (GL (Fin 3) K)}
    (hscal : ∀ M : Matrix (Fin 3) (Fin 3) K,
      (∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K) * M = M * x) → ∃ c : K, M = Matrix.scalar (Fin 3) c)
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hZ : Nat.card (Subgroup.center H) ∣ 3) {f : ℕ} (hf : 1 ≤ f) (hq3 : 3 ^ f ≠ 3)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3 ^ f)
    (e : (H ⧸ Subgroup.center H) ≃* StatedProj (StatedSL 2 F)) :
    f = 2 ∧ Nat.card (Subgroup.center H) = 3 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP F 3 := CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_three hF
  have hf2 : 2 ≤ f := by
    by_contra h
    push Not at h
    interval_cases f
    exact hq3 rfl
  set e' := toPSL2 e with he'
  set π := QuotientGroup.mk' (Subgroup.center H) with hπ
  set U := (rootGroupPSL2 F).map e'.symm.toMonoidHom with hUdef
  have hUcomm : ∀ y ∈ U, ∀ z ∈ U, y * z = z * y := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, rootGroupPSL2_comm hy hz]
  have hUexp : ∀ y ∈ U, y ^ 3 = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_pow, rootGroupPSL2_pow hy, map_one]
  have hUcard : Nat.card U = 3 ^ f := by
    rw [hUdef, Subgroup.card_map_of_injective e'.symm.injective, card_rootGroupPSL2, hF]
  set Ũ := U.comap π with hŨ
  have hŨcard : Nat.card Ũ = 3 ^ f * Nat.card (Subgroup.center H) := by
    have h1 := Subgroup.card_mul_index Ũ
    have h2 := Subgroup.card_mul_index U
    have h3 : Ũ.index = U.index :=
      Subgroup.index_comap_of_surjective U (QuotientGroup.mk'_surjective _)
    have h4 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center H)
    have hi : 0 < U.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    rw [h3, h4, ← h2] at h1
    rw [← hUcard]
    apply Nat.eq_of_mul_eq_mul_right hi
    rw [h1]
    ring
  set R := Ũ.map H.subtype with hR
  have hRcard : Nat.card R = Nat.card Ũ := Subgroup.card_map_of_injective H.subtype_injective
  have hcenscal : ∀ z ∈ Subgroup.center H, ∃ c : K,
      ((z : GL (Fin 3) (K)) : Matrix (Fin 3) (Fin 3) (K)) = Matrix.scalar (Fin 3) c := by
    intro z hz
    apply hscal
    intro y hy
    have := congrArg (fun g : H => ((g : GL (Fin 3) (K)) : Matrix (Fin 3) (Fin 3) (K)))
      (Subgroup.mem_center_iff.mp hz ⟨y, hy⟩)
    simpa using this
  have hcomm_mem : ∀ y ∈ Ũ, ∀ z ∈ Ũ, y * z * y⁻¹ * z⁻¹ ∈ Subgroup.center H := by
    intro y hy z hz
    apply (QuotientGroup.eq_one_iff _).mp
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv]
    have hc := hUcomm _ (Subgroup.mem_comap.mp hy) _ (Subgroup.mem_comap.mp hz)
    change (y : H ⧸ Subgroup.center H) * z = z * y at hc
    rw [hc]
    group
  have hcube_mem : ∀ y ∈ Ũ, y ^ 3 ∈ Subgroup.center H := by
    intro y hy
    apply (QuotientGroup.eq_one_iff _).mp
    rw [QuotientGroup.mk_pow]
    exact hUexp _ (Subgroup.mem_comap.mp hy)
  have hRdet : ∀ a ∈ R, (a : Matrix (Fin 3) (Fin 3) (K)).det = 1 := by
    rintro _ ⟨a, -, rfl⟩
    exact hdet _ a.2
  have hRcomm : ∀ a ∈ R, ∀ b ∈ R, ∃ c : K,
      ((a * b * a⁻¹ * b⁻¹ : GL (Fin 3) (K)) : Matrix (Fin 3) (Fin 3) (K)) =
        Matrix.scalar (Fin 3) c := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    exact hcenscal _ (hcomm_mem y hy z hz)
  have hRcube : ∀ a ∈ R, ∃ c : K,
      ((a ^ 3 : GL (Fin 3) (K)) : Matrix (Fin 3) (Fin 3) (K)) =
        Matrix.scalar (Fin 3) c := by
    rintro _ ⟨y, hy, rfl⟩
    exact hcenscal _ (hcube_mem y hy)
  have hRle := card_le_twentyseven_of_scalar_commutators h3 R hRdet hRcomm hRcube
  rw [hRcard, hŨcard] at hRle
  rcases (Nat.dvd_prime Nat.prime_three).mp hZ with hZ1 | hZ3
  ·
    exfalso
    have hZbot : Subgroup.center H = ⊥ := Subgroup.card_eq_one.mp hZ1
    have hRcomm' : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
      rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
      have h1 := hcomm_mem y hy z hz
      rw [hZbot, Subgroup.mem_bot] at h1
      have h2 : y * z = z * y := by
        calc y * z = y * z * y⁻¹ * z⁻¹ * (z * y) := by group
          _ = z * y := by rw [h1, one_mul]
      exact congrArg Subtype.val h2
    have hRexp : ∀ a ∈ R, a ^ 3 = 1 := by
      rintro _ ⟨y, hy, rfl⟩
      have h1 := hcube_mem y hy
      rw [hZbot, Subgroup.mem_bot] at h1
      change (y : GL (Fin 3) (K)) ^ 3 = 1
      rw [← Subgroup.coe_pow, h1, Subgroup.coe_one]
    have hR9 := card_le_sq_of_elementary (r := 3) (by exact_mod_cast h3) R hRcomm' hRexp hRdet
    rw [hRcard, hŨcard, hZ1, mul_one] at hR9
    have hf2' : f = 2 := le_antisymm ((Nat.pow_le_pow_iff_right (by norm_num)).mp hR9) hf2
    obtain ⟨a, haR, ha1, c, hac⟩ := exists_scalar_of_card_eq_nine h3 R hRcomm' hRexp hRdet
      (by rw [hRcard, hŨcard, hZ1, mul_one, hf2']; norm_num)
    obtain ⟨y, -, rfl⟩ := haR
    have hyc : y ∈ Subgroup.center H := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact commute_of_coe_eq_scalar hac (g : GL (Fin 3) (K))
    rw [hZbot, Subgroup.mem_bot] at hyc
    exact ha1 (by rw [hyc]; rfl)
  ·
    rw [hZ3] at hRle
    have h9 : 3 ^ f ≤ 3 ^ 2 := by omega
    exact ⟨le_antisymm ((Nat.pow_le_pow_iff_right (by norm_num)).mp h9) hf2, hZ3⟩

end CFSG.Quasithin.A312U3
