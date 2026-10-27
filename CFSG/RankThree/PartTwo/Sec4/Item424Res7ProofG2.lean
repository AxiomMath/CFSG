module

public import CFSG.RankThree.PartTwo.Sec4.Item4Res7ProofPairing
public import CFSG.RankThree.PartTwo.Sec4.Item424Res7ProofLin
public import CFSG.RankThree.PartTwo.Sec4.Item424Res7ProofDih
public import CFSG.RankThree.PartTwo.Sec11.Item1118Res2ProofG2
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof
public import CFSG.RankThree.PartTwo.Sec21.Item211Res5ProofG2Data

public section

namespace CFSG.RankThree.PartTwo.Sec4.Res424Seven

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof (g2ShortSL2 g2LongSL2 g2Short_commute_g2Long)
open CFSG.RankThree.PartTwo.Sec21.Item211Res5Proof (g2RhoA g2RhoV g2RhoA_injective
  g2RhoV_injective g2RhoA_comm mem_range_g2RhoA_iff mem_range_g2RhoV_iff)

section Roots

variable {K : Type} [Field K]

theorem sq_add_add_one_of_cube {μ : K} (h3 : μ ^ 3 = 1) (h1 : μ ≠ 1) : μ ^ 2 + μ + 1 = 0 := by
  have h : (μ - 1) * (μ ^ 2 + μ + 1) = 0 := by linear_combination h3
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr h1)

theorem cube_root_cases {μ x : K} (hμ : μ ^ 2 + μ + 1 = 0) (hx : x ^ 3 = 1) :
    x = 1 ∨ x = μ ∨ x = μ ^ 2 := by
  have h : (x - 1) * (x - μ) * (x - μ ^ 2) = 0 := by
    linear_combination hx + (-x ^ 2 + μ * x - μ + 1) * hμ
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h))

theorem three_ne_zero_of_ringChar (h : ringChar K ≠ 3) : (3 : K) ≠ 0 := by
  intro h3
  have hdvd : ringChar K ∣ 3 := (ringChar.spec K 3).mp (by exact_mod_cast h3)
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
  · exact CharP.ringChar_ne_one h1
  · exact h h1

end Roots

section Conj

variable {G : Type*} [Group G]

theorem eq_of_conj_eq {m x y : G} (h : m * x * m⁻¹ = m * y * m⁻¹) : x = y := by
  calc x = m⁻¹ * (m * x * m⁻¹) * m := by group
    _ = m⁻¹ * (m * y * m⁻¹) * m := by rw [h]
    _ = y := by group

end Conj

section Blocks


variable {K : Type} [Field K] [Finite K]

theorem exists_inv_long (h3 : (3 : K) ≠ 0) {c' d' : adjointGroup .G2 K}
    (hcM : c' ∈ g2LongSL2 K) (hdS : d' ∈ g2ShortSL2 K) (hc3 : c' ^ 3 = 1) (hc1 : c' ≠ 1) :
    ∃ n : adjointGroup .G2 K, n * c' * n⁻¹ = c'⁻¹ ∧ n * d' * n⁻¹ = d' := by
  obtain ⟨A, rfl⟩ := mem_range_g2RhoA_iff.mpr hcM
  obtain ⟨B, rfl⟩ := mem_range_g2RhoV_iff.mpr hdS
  have hA3 : A ^ 3 = 1 := g2RhoA_injective (by rw [map_pow, hc3, map_one])
  have hA1 : A ≠ 1 := fun h => hc1 (by rw [h, map_one])
  obtain ⟨N, hN⟩ := exists_conj_eq_inv_sl2 h3 hA3 hA1
  refine ⟨g2RhoA K N, ?_, ?_⟩
  · rw [show g2RhoA K N * g2RhoA K A * (g2RhoA K N)⁻¹ = g2RhoA K (N * A * N⁻¹) by
      simp only [map_mul, map_inv], hN, map_inv]
  · rw [g2RhoA_comm, mul_inv_cancel_right]

theorem exists_inv_short (h3 : (3 : K) ≠ 0) {c' d' : adjointGroup .G2 K}
    (hcM : c' ∈ g2LongSL2 K) (hdS : d' ∈ g2ShortSL2 K) (hd3 : d' ^ 3 = 1) (hd1 : d' ≠ 1) :
    ∃ n : adjointGroup .G2 K, n * c' * n⁻¹ = c' ∧ n * d' * n⁻¹ = d'⁻¹ := by
  obtain ⟨A, rfl⟩ := mem_range_g2RhoA_iff.mpr hcM
  obtain ⟨B, rfl⟩ := mem_range_g2RhoV_iff.mpr hdS
  have hB3 : B ^ 3 = 1 := g2RhoV_injective (by rw [map_pow, hd3, map_one])
  have hB1 : B ≠ 1 := fun h => hd1 (by rw [h, map_one])
  obtain ⟨N, hN⟩ := exists_conj_eq_inv_sl2 h3 hB3 hB1
  refine ⟨g2RhoV K N, ?_, ?_⟩
  · rw [← g2RhoA_comm, mul_inv_cancel_right]
  · rw [show g2RhoV K N * g2RhoV K B * (g2RhoV K N)⁻¹ = g2RhoV K (N * B * N⁻¹) by
      simp only [map_mul, map_inv], hN, map_inv]

end Blocks

section Split


variable {K : Type} [Field K] [Finite K]

theorem exists_rot_split (h31 : 3 ∣ Nat.card K - 1) {c' d' : adjointGroup .G2 K}
    (hcM : c' ∈ g2LongSL2 K) (hdS : d' ∈ g2ShortSL2 K) (hc3 : c' ^ 3 = 1) (hd3 : d' ^ 3 = 1)
    (hd1 : d' ≠ 1) (hcd : c' ∉ Subgroup.zpowers d') :
    ∃ g : adjointGroup .G2 K, g * d' * g⁻¹ = d' ∧
      (g * c' * g⁻¹ = d' * c' ∨ g * c' * g⁻¹ = d' ^ 2 * c') := by
  obtain ⟨m, φ, hφinj, hφd, hdφ⟩ :=
    Sec11.Item1118Res2Proof.exists_a2_model_of_short h31 hdS hd3 hd1
  have hdc : d' * c' = c' * d' := g2Short_commute_g2Long hdS hcM
  obtain ⟨Z, hZ⟩ := hdφ (m * d' * m⁻¹) rfl
  obtain ⟨Y, hY⟩ := hdφ (m * c' * m⁻¹) (by
    calc m * c' * m⁻¹ * (m * d' * m⁻¹) = m * (c' * d') * m⁻¹ := by group
      _ = m * (d' * c') * m⁻¹ := by rw [hdc]
      _ = m * d' * m⁻¹ * (m * c' * m⁻¹) := by group)
  have hZc : Z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin (2 + 1)) K) := by
    rw [Subgroup.mem_center_iff]
    intro W
    apply hφinj
    rw [map_mul, map_mul, hZ]
    exact hφd W
  obtain ⟨μ, hμ3, hμZ⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hZc
  have hμ3' : μ ^ 3 = 1 := by simpa using hμ3
  have hpow : ∀ k : ℕ, ((Z ^ k : Matrix.SpecialLinearGroup (Fin (2 + 1)) K) :
      Matrix (Fin (2 + 1)) (Fin (2 + 1)) K) = Matrix.scalar (Fin (2 + 1)) (μ ^ k) := fun k => by
    rw [Matrix.SpecialLinearGroup.coe_pow, ← hμZ, map_pow]
  have hμ1 : μ ≠ 1 := by
    rintro rfl
    apply hd1
    have hZ1 : Z = 1 := Subtype.ext (by rw [← hμZ, map_one]; rfl)
    apply eq_of_conj_eq (m := m)
    rw [← hZ, hZ1, map_one]
    group
  have hω := sq_add_add_one_of_cube hμ3' hμ1
  have hY3 : Y ^ 3 = 1 := hφinj (by rw [map_pow, hY, conj_pow, hc3, mul_one, mul_inv_cancel,
    map_one])
  have hYZ : ∀ k : ℕ, Y ≠ Z ^ k := by
    intro k hk
    apply hcd
    have h1 : m * c' * m⁻¹ = m * d' ^ k * m⁻¹ := by rw [← hY, hk, map_pow, hZ, conj_pow]
    rw [eq_of_conj_eq h1]
    exact pow_mem (Subgroup.mem_zpowers d') k
  have hYns : ∀ ν : K, (Y : Matrix (Fin (2 + 1)) (Fin (2 + 1)) K) ≠
      Matrix.scalar (Fin (2 + 1)) ν := by
    intro ν hν
    have hν3 : ν ^ 3 = 1 := by
      have h := Y.det_coe
      rw [hν, Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_const] at h
      exact h
    rcases cube_root_cases hω hν3 with rfl | rfl | rfl
    · exact hYZ 0 (Subtype.ext (by rw [hν, hpow, pow_zero]))
    · exact hYZ 1 (Subtype.ext (by rw [hν, hpow, pow_one]))
    · exact hYZ 2 (Subtype.ext (by rw [hν, hpow]))
  obtain ⟨G, l, hl3, hl1, hG⟩ := exists_rot_sl3 hω hμ1 hY3 hYns
  have hk : ∀ k : ℕ, l = μ ^ k → G * Y * G⁻¹ = Z ^ k * Y := by
    intro k hlk
    have h1 : G * Y = Z ^ k * (Y * G) := by
      apply Subtype.ext
      rw [hG]
      simp only [Matrix.SpecialLinearGroup.coe_mul]
      rw [← Matrix.SpecialLinearGroup.coe_mul, hpow, ← hlk, Matrix.scalar_apply,
        Matrix.smul_eq_diagonal_mul]
    rw [h1]
    group
  have hgd : (m⁻¹ * φ G * m) * d' * (m⁻¹ * φ G * m)⁻¹ = d' := by
    calc (m⁻¹ * φ G * m) * d' * (m⁻¹ * φ G * m)⁻¹ =
        m⁻¹ * (φ G * (m * d' * m⁻¹)) * (φ G)⁻¹ * m := by group
      _ = m⁻¹ * ((m * d' * m⁻¹) * φ G) * (φ G)⁻¹ * m := by rw [hφd G]
      _ = d' := by group
  have hgc : ∀ k : ℕ, l = μ ^ k →
      (m⁻¹ * φ G * m) * c' * (m⁻¹ * φ G * m)⁻¹ = d' ^ k * c' := by
    intro k hlk
    have h1 : φ G * (m * c' * m⁻¹) * (φ G)⁻¹ = (m * d' * m⁻¹) ^ k * (m * c' * m⁻¹) := by
      rw [← hY, ← hZ, ← map_inv, ← map_mul, ← map_mul, hk k hlk, map_mul, map_pow]
    calc (m⁻¹ * φ G * m) * c' * (m⁻¹ * φ G * m)⁻¹ =
        m⁻¹ * (φ G * (m * c' * m⁻¹) * (φ G)⁻¹) * m := by group
      _ = m⁻¹ * ((m * d' * m⁻¹) ^ k * (m * c' * m⁻¹)) * m := by rw [h1]
      _ = m⁻¹ * (m * d' ^ k * m⁻¹ * (m * c' * m⁻¹)) * m := by rw [conj_pow]
      _ = d' ^ k * c' := by group
  refine ⟨m⁻¹ * φ G * m, hgd, ?_⟩
  rcases (cube_root_cases hω hl3).resolve_left hl1 with hl | hl
  · left
    rw [hgc 1 (by rw [hl, pow_one]), pow_one]
  · right
    exact hgc 2 hl

end Split

section NonSplit


open CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary in
theorem exists_rot_nonsplit {K : Type} [Field K] [Finite K] (h3 : 3 ∣ Nat.card K + 1)
    (hK4 : 4 ≤ Nat.card K) {c' d' : adjointGroup .G2 K} (hcM : c' ∈ g2LongSL2 K)
    (hdS : d' ∈ g2ShortSL2 K) (hc3 : c' ^ 3 = 1) (hd3 : d' ^ 3 = 1) (hd1 : d' ≠ 1)
    (hcd : c' ∉ Subgroup.zpowers d') :
    ∃ g : adjointGroup .G2 K, g * d' * g⁻¹ = d' ∧
      (g * c' * g⁻¹ = d' * c' ∨ g * c' * g⁻¹ = d' ^ 2 * c') := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  obtain ⟨n, -, hcard⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  obtain ⟨L, _, _, _, -, hdeg, -⟩ := Sec11.KS11Lie4Proof.exists_quadratic_ext' K
  have : CharP L (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K L).injective (ringChar K)
  obtain ⟨ψ⟩ := Sec11.KS11Lie7Proof.nonempty_centralizer_mulEquiv_statedSU hK h3 hdeg hdS hd3 hd1
  have hL : Nat.card L = (ringChar K ^ (n : ℕ)) ^ 2 := by
    rw [Sec11.KS11Lie4Proof.natCard_quadratic hdeg, hK]
  have hq2 : (3, ringChar K ^ (n : ℕ)) ≠ (3, 2) := by
    intro h
    have h2 := (Prod.mk.inj h).2
    rw [hK, h2] at hK4
    omega
  have hcen := (isQuasisimple_statedSU_of_card hL (le_refl 3) hq2).2
  set q := ringChar K ^ (n : ℕ) with hqdef
  set σ := unitaryInvolution L (ringChar K) n with hσdef
  have hdc : d' * c' = c' * d' := g2Short_commute_g2Long hdS hcM
  set dd : Subgroup.centralizer ({d'} : Set (adjointGroup .G2 K)) :=
    ⟨d', Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ with hdd
  set cc : Subgroup.centralizer ({d'} : Set (adjointGroup .G2 K)) :=
    ⟨c', Subgroup.mem_centralizer_singleton_iff.mpr hdc.symm⟩ with hcc
  have hZcen : ψ dd ∈ Subgroup.center (StatedSU 3 q L) := by
    rw [Subgroup.mem_center_iff]
    intro Y
    obtain ⟨y, rfl⟩ := ψ.surjective Y
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp y.2
  rw [hcen] at hZcen
  obtain ⟨u, hu⟩ := Subgroup.mem_subgroupOf.mp hZcen
  set μ : L := (u : L) with hμdef
  have hZmat : (((ψ dd : StatedSU 3 q L) : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
      Matrix.scalar (Fin 3) μ := by
    rw [← hu, Matrix.GeneralLinearGroup.coe_scalar]
  have hpow : ∀ k : ℕ, ((((ψ dd) ^ k : StatedSU 3 q L) : GL (Fin 3) L) :
      Matrix (Fin 3) (Fin 3) L) = Matrix.scalar (Fin 3) (μ ^ k) := fun k => by
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hZmat, map_pow]
  have hμ3 : μ ^ 3 = 1 := by
    have h := det_eq_one_of_mem_statedSU (ψ dd).2
    rw [hZmat, Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_const] at h
    exact h
  have hμ1 : μ ≠ 1 := by
    intro h1
    apply hd1
    have h2 : ψ dd = 1 := Subtype.ext (Units.ext (by rw [hZmat, h1, map_one]; rfl))
    have h3' : dd = 1 := ψ.injective (by rw [h2, map_one])
    exact congrArg Subtype.val h3'
  have hω := sq_add_add_one_of_cube hμ3 hμ1
  set X₀ := ψ cc with hX₀
  have hX₀3 : X₀ ^ 3 = 1 := by
    rw [hX₀, ← map_pow]
    have : cc ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hc3)
    rw [this, map_one]
  have hmem : ((X₀ : StatedSU 3 q L) : GL (Fin 3) L) ∈ SUid σ 3 := by
    rw [hσdef, SUid_eq_statedSU hL 3]
    exact X₀.2
  obtain ⟨hdet, hU⟩ := hmem
  have hX3 : (((X₀ : StatedSU 3 q L) : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, hX₀3]
    rfl
  have hXZ : ∀ k : ℕ, X₀ ≠ (ψ dd) ^ k := by
    intro k hk
    apply hcd
    have h1 : cc = dd ^ k := ψ.injective (by rw [← hX₀, hk, map_pow])
    have h2 : c' = d' ^ k := by
      have := congrArg Subtype.val h1
      rwa [Subgroup.coe_pow] at this
    rw [h2]
    exact pow_mem (Subgroup.mem_zpowers d') k
  have hXns : ∀ ν : L, (((X₀ : StatedSU 3 q L) : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) ≠
      Matrix.scalar (Fin 3) ν := by
    intro ν hν
    have hν3 : ν ^ 3 = 1 := by
      have h := hdet
      rw [hν, Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_const] at h
      exact h
    rcases cube_root_cases hω hν3 with rfl | rfl | rfl
    · exact hXZ 0 (Subtype.ext (Units.ext (by rw [hν, hpow, pow_zero])))
    · exact hXZ 1 (Subtype.ext (Units.ext (by rw [hν, hpow, pow_one])))
    · exact hXZ 2 (Subtype.ext (Units.ext (by rw [hν, hpow])))
  have hσσ : ∀ x, σ (σ x) = x := unitaryInvolution_involutive hL
  have hnorm : ∀ c : L, c ≠ 0 → σ c = c → ∃ a, σ a * a = c := fun c hc0 hcσ =>
    CFSG.ClassicalGroups.Unitary.exists_norm_eq_of_fixed hL hcσ hc0
  have hσ3 : ∀ x : L, x ^ 3 = 1 → σ x * x = 1 := by
    intro x hx
    obtain ⟨t, ht⟩ : 3 ∣ q + 1 := by rw [← hK]; exact h3
    rw [hσdef, unitaryInvolution_apply, ← pow_succ, ← hqdef, ht, pow_mul, hx, one_pow]
  obtain ⟨G, hGdet, hGU, l, hl3, hl1, hGX⟩ :=
    exists_rot_unitary σ hσσ hnorm hσ3 hω hμ1 hdet hU hX3 hXns
  set Gu : GL (Fin 3) L := Matrix.GeneralLinearGroup.mkOfDetNeZero G
    (by rw [hGdet]; exact one_ne_zero) with hGu
  have hGmem : Gu ∈ StatedSU 3 q L := by
    rw [hqdef, ← SUid_eq_statedSU hL 3]
    exact ⟨hGdet, hGU⟩
  set Gs : StatedSU 3 q L := ⟨Gu, hGmem⟩ with hGs
  have hk : ∀ k : ℕ, l = μ ^ k → Gs * X₀ * Gs⁻¹ = (ψ dd) ^ k * X₀ := by
    intro k hlk
    have h1 : Gs * X₀ = (ψ dd) ^ k * (X₀ * Gs) := by
      apply Subtype.ext
      apply Units.ext
      simp only [Subgroup.coe_mul, Units.val_mul]
      rw [← Units.val_mul, ← Subgroup.coe_mul, hpow, ← hlk, Matrix.scalar_apply,
        ← Matrix.smul_eq_diagonal_mul]
      exact hGX
    rw [h1]
    group
  set gc := ψ.symm Gs with hgc
  have hgcd : (gc : adjointGroup .G2 K) * d' * (gc : adjointGroup .G2 K)⁻¹ = d' := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp gc.2, mul_inv_cancel_right]
  have hgcc : ∀ k : ℕ, l = μ ^ k →
      (gc : adjointGroup .G2 K) * c' * (gc : adjointGroup .G2 K)⁻¹ = d' ^ k * c' := by
    intro k hlk
    have h1 : gc * cc * gc⁻¹ = dd ^ k * cc := ψ.injective (by
      rw [map_mul, map_mul, map_inv, map_mul, map_pow, hgc, MulEquiv.apply_symm_apply, ← hX₀,
        hk k hlk])
    have h2 := congrArg Subtype.val h1
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow] using h2
  refine ⟨gc, hgcd, ?_⟩
  rcases (cube_root_cases hω hl3).resolve_left hl1 with hl | hl
  · left
    rw [hgcc 1 (by rw [hl, pow_one]), pow_one]
  · right
    exact hgcc 2 hl

end NonSplit

section Main


theorem k424PairingG2_holds : K424PairingG2 := by
  intro X _ _ K _ _ hK3 hK4 hXE D c d J h
  obtain ⟨E⟩ := hXE
  have hDe := h.maximal.prop
  have hc3 : c ^ 3 = 1 := hDe.2 c h.c_mem
  have hd3 : d ^ 3 = 1 := hDe.2 d h.d_mem
  have hc1 : c ≠ 1 := h.c_ne_one
  have hd1 : d ≠ 1 := by
    rintro rfl
    exact h.d_not_mem (Subgroup.one_mem _)
  have hJ : J ∈ thetaComponentsIn (Item426.fixSub (MulAut.conj c)) := by
    rw [Item424Res2.fixSub_conj_eq_centralizer_singleton]
    exact h.mem_thetaComponentsIn
  have hEc3 : E c ^ 3 = 1 := by rw [← map_pow, hc3, map_one]
  have hEc1 : E c ≠ 1 := fun h1 => hc1 (E.injective (h1.trans (map_one E).symm))
  obtain ⟨g₀, hg₀⟩ := Sec11.KS11Lie7Proof.g2ThreeConjSL2_holds K hK3 hK4 (E c) hEc3 hEc1
  set e : X ≃* adjointGroup .G2 K := E.trans (MulAut.conj g₀) with he
  have hmem : e c ∈ g2ShortSL2 K ∨ e c ∈ g2LongSL2 K := hg₀
  obtain ⟨hcM, hB⟩ := Sec11.KS11Lie4Proof.threeBAt_g2 Sec11.KS11Lie7Proof.g2ThreeACent_holds
    Sec11.KS11Lie4Proof.g2ThreeBCent_holds hK3 hK4 e hc3 hc1 hmem hJ h.isType424
  have hJS := hB.eq hJ
  have hdS : e d ∈ g2ShortSL2 K := by
    have h1 := h.d_mem_K
    rw [hJS] at h1
    exact h1
  have h3K : (3 : K) ≠ 0 := three_ne_zero_of_ringChar hK3
  have hec3 : e c ^ 3 = 1 := by rw [← map_pow, hc3, map_one]
  have hed3 : e d ^ 3 = 1 := by rw [← map_pow, hd3, map_one]
  have hec1 : e c ≠ 1 := fun h1 => hc1 (e.injective (h1.trans (map_one e).symm))
  have hed1 : e d ≠ 1 := fun h1 => hd1 (e.injective (h1.trans (map_one e).symm))
  have hecd : e c ∉ Subgroup.zpowers (e d) := by
    rintro ⟨k, hk⟩
    apply c_not_mem_zpowers_of_config h
    refine ⟨k, e.injective ?_⟩
    rw [map_zpow]
    exact hk
  obtain ⟨n₁, hn₁c, hn₁d⟩ := exists_inv_long h3K hcM hdS hec3 hec1
  obtain ⟨n₂, hn₂c, hn₂d⟩ := exists_inv_short h3K hcM hdS hed3 hed1
  obtain ⟨g, hgd, hgc⟩ : ∃ g : adjointGroup .G2 K, g * e d * g⁻¹ = e d ∧
      (g * e c * g⁻¹ = e d * e c ∨ g * e c * g⁻¹ = e d ^ 2 * e c) := by
    have h3q := Sec11.Item1118Res2Proof.not_three_dvd_card hK3
    have hK1 : 1 ≤ Nat.card K := Nat.card_pos
    rcases (by omega : Nat.card K % 3 = 1 ∨ Nat.card K % 3 = 2) with hq | hq
    · exact exists_rot_split (by omega) hcM hdS hec3 hed3 hed1 hecd
    · exact exists_rot_nonsplit (by omega) hK4 hcM hdS hec3 hed3 hed1 hecd
  have hconj : ∀ x y : X, x * y * x⁻¹ = e.symm (e x * e y * (e x)⁻¹) := fun x y => by
    simp only [map_mul, map_inv, MulEquiv.symm_apply_apply]
  refine nonempty_autIn_dihedral_of_elements h (n₁ := e.symm n₁) (n₂ := e.symm n₂)
    (g := e.symm g) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hconj, MulEquiv.apply_symm_apply, hn₁c, ← map_inv, MulEquiv.symm_apply_apply]
  · rw [hconj, MulEquiv.apply_symm_apply, hn₁d, MulEquiv.symm_apply_apply]
  · rw [hconj, MulEquiv.apply_symm_apply, hn₂c, MulEquiv.symm_apply_apply]
  · rw [hconj, MulEquiv.apply_symm_apply, hn₂d, ← map_inv, MulEquiv.symm_apply_apply]
  · rw [hconj, MulEquiv.apply_symm_apply, hgd, MulEquiv.symm_apply_apply]
  · rcases hgc with hgc | hgc
    · left
      rw [hconj, MulEquiv.apply_symm_apply, hgc, ← map_mul, MulEquiv.symm_apply_apply]
    · right
      rw [hconj, MulEquiv.apply_symm_apply, hgc, ← map_pow, ← map_mul,
        MulEquiv.symm_apply_apply]

theorem k424PairingLie_of_d4 (hD : K424PairingD4) : K424PairingLie :=
  k424PairingLie_of k424PairingG2_holds hD

end Main

end CFSG.RankThree.PartTwo.Sec4.Res424Seven
