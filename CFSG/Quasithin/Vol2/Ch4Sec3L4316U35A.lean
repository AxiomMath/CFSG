module

public import CFSG.Quasithin.Vol2.Ch4Sec3L4316Y

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank Vol2.KGNat Vol2.Ch11.SecS.C11P9A
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uMat uSL coe_uSL uSL_mul uSL_inv uSL_zero
  uSL_injective)
open scoped MatrixGroups Matrix Pointwise

namespace SL3Pt

variable {F : Type} [Field F]

theorem blk_one : blk (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk]

theorem blk_mul (g h : Matrix (Fin 2) (Fin 2) F) : blk (g * h) = blk g * blk h := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

theorem blk_pow (g : Matrix (Fin 2) (Fin 2) F) (n : ℕ) : blk (g ^ n) = blk g ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, blk_one]
  | succ n ih => rw [pow_succ, pow_succ, blk_mul, ih]

theorem vecMul_blk (g : Matrix (Fin 2) (Fin 2) F) :
    (![1, 0, 0] : Fin 3 → F) ᵥ* blk g = ![1, 0, 0] := by
  funext i
  fin_cases i <;> simp [blk, Matrix.vecMul, dotProduct, Fin.sum_univ_three]

theorem exists_orderOf_eq_five [Fintype F] [CharP F 2] (hF : Fintype.card F = 4) :
    ∃ g : SL(2, F), orderOf g = 5 := by
  classical
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hU : Fintype.card Fˣ = 3 := by rw [Fintype.card_units, hF]
  have : Nontrivial Fˣ := Fintype.one_lt_card_iff_nontrivial.mp (by rw [hU]; norm_num)
  obtain ⟨u, hu⟩ := exists_ne (1 : Fˣ)
  have hu3 : u ^ 3 = 1 := by rw [← hU]; exact pow_card_eq_one
  set ω : F := (u : F) with hω
  have hω1 : ω ≠ 1 := fun h => hu (Units.ext h)
  have hω3 : ω ^ 3 = 1 := by
    have := congrArg Units.val hu3
    simpa using this
  have hωq : ω ^ 2 + ω + 1 = 0 := by
    have hfac : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hω3
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd (sub_eq_zero.mp h) hω1
    · exact h
  set M : Matrix (Fin 2) (Fin 2) F := !![0, 1; 1, ω] with hM
  have hdet : M.det = 1 := by
    rw [hM, Matrix.det_fin_two_of]
    linear_combination -h2
  set g : SL(2, F) := ⟨M, hdet⟩ with hg
  have hM2 : M * M = !![1, ω; ω, ω] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hM, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination hωq - ω * h2
  have hM4 : M * M * (M * M) = !![ω, 1; 1, 0] := by
    rw [hM2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination hωq - ω * h2
    · linear_combination hωq - h2
    · linear_combination hωq - h2
    · linear_combination ω ^ 2 * h2
  have hM5 : M * M * (M * M) * M = 1 := by
    rw [hM4]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hM, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination ω * h2
  have hg5 : g ^ 5 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    show M ^ 5 = 1
    rw [show M ^ 5 = M * M * (M * M) * M by
      rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_one]
      noncomm_ring]
    exact hM5
  have hg1 : g ≠ 1 := by
    intro h
    have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp [hg, hM] at this
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact ⟨g, orderOf_eq_prime hg5 hg1⟩

end SL3Pt

variable {G : Type} [Group G] [Finite G]

namespace Setting4315

variable {T M L : Subgroup G} {n : ℕ} {I H K : Subgroup G} {t : G} {m : ℕ} {F : Type} [Field F]
  [Fintype F] {α : ↥K →* ↥(StatedSL 3 F)} {β : ↥(u4311 I K) →* Multiplicative (Fin 3 → F)}
  {W' : Submodule F (Fin 3 → F)} {ZS K₂ R₂ : Subgroup G} {μ : Fˣ} {y : G} {KZ : Subgroup G}
variable (s : Setting4315 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y KZ)
include s

theorem zpow_y_mem_normalizer_R₂ (j : ℤ) : y ^ j ∈ Subgroup.normalizer (R₂ : Set G) := by
  have key : ∀ (i : ℤ) {r : G}, r ∈ R₂ → y ^ i * r * (y ^ i)⁻¹ ∈ R₂ := by
    intro i r hr
    obtain ⟨a, b, hab⟩ := SL3Pt.mem_radE0_iff.mp (s.α_mem_radE0 hr)
    have hyK : y ^ i ∈ K := Subgroup.zpow_mem _ s.y_mem i
    have hmem : y ^ i * r * (y ^ i)⁻¹ ∈ K :=
      K.mul_mem (K.mul_mem hyK (s.R₂_le_K hr)) (K.inv_mem hyK)
    refine s.mem_R₂_of hmem ?_
    have e : (⟨y ^ i * r * (y ^ i)⁻¹, hmem⟩ : ↥K) =
        ⟨y ^ i, hyK⟩ * ⟨r, s.R₂_le_K hr⟩ * (⟨y ^ i, hyK⟩ : ↥K)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, s.α_zpow, hab, ← map_inv, ← map_mul, ← map_mul,
      SL3Pt.tor_conj_uSL]
    exact SL3Pt.mem_radE0_iff.mpr ⟨_, _, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro r
  refine ⟨key j, fun h => ?_⟩
  have := key (-j) h
  simpa [zpow_neg, mul_assoc] using this

theorem false_of_star_R₂_inf_eq_bot (h135 : AsC135Three) (hR : L2RankOneSylowFact)
    (hC : LemmaC53C56Six) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (hinf : s.star R₂ ⊓ s.star KZ = ⊥) (hcard : Nat.card ↥(s.star R₂) = 2) :
    False := by
  have hKR : ∀ k ∈ K₂, k ∈ R₂ → k ∈ s.C₀ := by
    intro k hk hkR
    have h1 : s.rho.rangeRestrict ⟨k, s.K₂_le_G₀ hk⟩ ∈ s.star R₂ ⊓ s.star KZ :=
      ⟨⟨⟨k, s.K₂_le_G₀ hk⟩, hkR, rfl⟩, ⟨⟨k, s.K₂_le_G₀ hk⟩, s.K₂_le_KZ hk, rfl⟩⟩
    rw [hinf, Subgroup.mem_bot] at h1
    exact s.mem_C₀_of_rho_eq_one _ (congrArg Subtype.val h1)
  have hQR := s.q4311_le_R₂ h135 hR hC h37 h38 h39
  have hQG : q4311 I K ≤ s.G₀ := hQR.trans s.R₂_le_G₀
  have hfix : ∀ w : ↥s.rho.range,
      w ∈ Subgroup.normalizer ((s.star R₂ : Subgroup ↥s.rho.range) : Set ↥s.rho.range) →
      ∀ r ∈ s.star R₂, w * r * w⁻¹ = r := by
    intro w hw r hr
    by_cases hr1 : r = 1
    · rw [hr1, mul_one, mul_inv_cancel]
    have hwr : w * r * w⁻¹ ∈ s.star R₂ := (Subgroup.mem_normalizer_iff.mp hw r).mp hr
    have hwr1 : w * r * w⁻¹ ≠ 1 := by
      intro h
      apply hr1
      calc r = w⁻¹ * (w * r * w⁻¹) * w := by group
        _ = 1 := by rw [h]; group
    obtain ⟨u, -, hu⟩ := (Nat.card_eq_two_iff' (1 : ↥(s.star R₂))).mp hcard
    have h1 := hu ⟨r, hr⟩ (fun h => hr1 (congrArg Subtype.val h))
    have h2 := hu ⟨_, hwr⟩ (fun h => hwr1 (congrArg Subtype.val h))
    exact congrArg Subtype.val (h2.trans h1.symm)
  have hQC : q4311 I K ≤ s.C₀ := by
    rw [s.q4311_eq_commutator, Subgroup.commutator_le]
    intro q hq z hz
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hzG : y ^ j ∈ s.G₀ := Subgroup.zpow_mem _ s.y_mem_G₀ j
    have hqG : q ∈ s.G₀ := hQG hq
    have hw : s.rho.rangeRestrict ⟨y ^ j, hzG⟩ ∈
        Subgroup.normalizer ((s.star R₂ : Subgroup ↥s.rho.range) : Set ↥s.rho.range) := by
      rw [s.mem_normalizer_star_iff]
      exact s.rho_mem_normalizer_map hzG (s.zpow_y_mem_normalizer_R₂ j)
    have hr : s.rho.rangeRestrict ⟨q, hqG⟩ ∈ s.star R₂ := ⟨⟨q, hqG⟩, hQR hq, rfl⟩
    have h1 := hfix _ hw _ hr
    have h2 := mul_inv_eq_iff_eq_mul.mp h1
    have hcomm : s.rho.rangeRestrict (⟨q, hqG⟩ * ⟨y ^ j, hzG⟩ * (⟨q, hqG⟩ : ↥s.G₀)⁻¹ *
        (⟨y ^ j, hzG⟩ : ↥s.G₀)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h2]
      group
    rw [commutatorElement_def]
    exact s.mem_C₀_of_rho_eq_one (g := q * y ^ j * q⁻¹ * (y ^ j)⁻¹) _ (congrArg Subtype.val hcomm)
  have hR₂C : R₂ ≤ s.C₀ := by
    intro r hr
    have hst : α ⟨r, s.R₂_le_K hr⟩ ∈ stE0 F := SL3Pt.radE0_le_stE0 (s.α_mem_radE0 hr)
    obtain ⟨k, hk⟩ := s.αK₂_surjective ⟨_, hst⟩
    have hkα : α ⟨k, s.K₂_le_K k.2⟩ = α ⟨r, s.R₂_le_K hr⟩ := by
      have := congrArg Subtype.val hk
      rw [s.coe_αK₂] at this
      exact this
    have hkR : (k : G) ∈ R₂ :=
      s.mem_R₂_of (s.K₂_le_K k.2) (by rw [hkα]; exact s.α_mem_radE0 hr)
    have hkC := hKR k k.2 hkR
    have hmem : (k : G)⁻¹ * r ∈ K := K.mul_mem (K.inv_mem (s.K₂_le_K k.2)) (s.R₂_le_K hr)
    have hq : (k : G)⁻¹ * r ∈ q4311 I K := by
      rw [s.mem_q4311_iff h135 hR hC h37 h38 h39 hmem]
      have e : (⟨(k : G)⁻¹ * r, hmem⟩ : ↥K) =
          (⟨k, s.K₂_le_K k.2⟩ : ↥K)⁻¹ * ⟨r, s.R₂_le_K hr⟩ := rfl
      rw [e, map_mul, map_inv, hkα, inv_mul_cancel]
    have e : r = (k : G) * ((k : G)⁻¹ * r) := by group
    rw [e]
    exact Subgroup.mul_mem _ hkC (hQC hq)
  apply s.star_R₂_ne_bot h135 hR hC h36 h37 h38 h39
  rw [eq_bot_iff]
  rintro _ ⟨g, hg, rfl⟩
  rw [Subgroup.mem_bot]
  exact s.rangeRestrict_eq_one (hR₂C hg)

theorem exists_k₁ (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hm : m = 2) :
    ∃ k₁ ∈ K₂, orderOf k₁ = 5 ∧ ∃ hk : k₁ ∈ K,
      (![1, 0, 0] : Fin 3 → F) ᵥ* (((α ⟨k₁, hk⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = ![1, 0, 0] := by
  classical
  have : CharP F 2 := s.charP
  have hF4 : Fintype.card F = 4 := by rw [s.card_F, hm]; norm_num
  obtain ⟨g, hg⟩ := SL3Pt.exists_orderOf_eq_five hF4
  have hy3 : orderOf y = 3 := by rw [s.orderOf_y, hm]; norm_num
  obtain ⟨k, hk, -, hkα, -⟩ := s.exists_levi_lift Nat.prime_three (by norm_num)
    (Subgroup.mem_zpowers y) hy3 g
  have hkK : k ∈ K := s.K₂_le_K hk
  have hαpow : ∀ n : ℕ, (((α ⟨k ^ n, K.pow_mem hkK n⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = SL3Pt.blk (((g ^ n : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) := by
    intro n
    have e : (⟨k ^ n, K.pow_mem hkK n⟩ : ↥K) = (⟨k, hkK⟩ : ↥K) ^ n := rfl
    rw [e, map_pow, Matrix.SpecialLinearGroup.coe_pow, SL3Pt.blk_pow]
    simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val]
    rw [hkα]
  have hg5 : g ^ 5 = 1 := by
    rw [← hg]
    exact pow_orderOf_eq_one g
  have hk5 : k ^ 5 ∈ q4311 I K := by
    rw [s.mem_q4311_iff h135 hR hC h37 h38 h39 (K.pow_mem hkK 5)]
    apply Subtype.ext
    apply Units.ext
    rw [hαpow 5, hg5, Matrix.SpecialLinearGroup.coe_one, SL3Pt.blk_one]
    rfl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨a, ha⟩ := (isPGroup_q4311 I K) ⟨_, hk5⟩
  have ha' : (k ^ 5) ^ 2 ^ a = 1 := congrArg Subtype.val ha
  have hp5 : (k ^ 2 ^ a) ^ 5 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, ha']
  have hne : k ^ 2 ^ a ≠ 1 := by
    intro h1
    have h2 := hαpow (2 ^ a)
    rw [show (⟨k ^ 2 ^ a, K.pow_mem hkK _⟩ : ↥K) = 1 from Subtype.ext h1, map_one] at h2
    have h2' : SL3Pt.blk (((g ^ 2 ^ a : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) = 1 := by
      rw [← h2]
      rfl
    have h3 : g ^ 2 ^ a = 1 := by
      apply Subtype.ext
      have := congrArg lev h2'
      rw [SL3Pt.lev_blk] at this
      rw [this]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [lev, Matrix.one_apply]
    have h4 := orderOf_dvd_of_pow_eq_one h3
    rw [hg] at h4
    have : (5 : ℕ) ∣ 2 ^ a := h4
    have h6 := (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 5) Nat.prime_two).mp
      ((Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) this))
    omega
  refine ⟨k ^ 2 ^ a, K₂.pow_mem hk _, orderOf_eq_prime hp5 hne, K.pow_mem hkK _, ?_⟩
  rw [hαpow]
  exact SL3Pt.vecMul_blk _

end Setting4315

end CFSG.Quasithin.H13.Ch4
