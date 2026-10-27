module

public import CFSG.Quasithin.Vol2.Ch4Sec3L4312
public import CFSG.Quasithin.Vol2.Ch4Sec3L4311Q

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank CFSG.Blueprint L436 Vol2.KGNat
open scoped MatrixGroups commutatorElement Matrix

namespace SL3Pt

variable {F : Type} [Field F]

@[expose] def blk (g : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  !![1, 0, 0; 0, g 0 0, g 0 1; 0, g 1 0, g 1 1]

theorem det_blk (g : Matrix (Fin 2) (Fin 2) F) : (blk g).det = g.det := by
  rw [Matrix.det_fin_three, Matrix.det_fin_two]
  simp [blk]

theorem lev_blk (g : Matrix (Fin 2) (Fin 2) F) : lev (blk g) = g := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem blk_mulVec_e0 (g : Matrix (Fin 2) (Fin 2) F) : blk g *ᵥ ![1, 0, 0] = ![1, 0, 0] := by
  funext i
  fin_cases i <;> simp [blk, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem torMat_mul_blk (μ : Fˣ) (g : Matrix (Fin 2) (Fin 2) F) :
    torMat μ * blk g = blk g * torMat μ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torMat, blk, Matrix.mul_apply, Matrix.diagonal_apply, mul_comm]

theorem eq_blk_lev {B : Matrix (Fin 3) (Fin 3) F} (h00 : B 0 0 = 1) (h10 : B 1 0 = 0)
    (h20 : B 2 0 = 0) (h01 : B 0 1 = 0) (h02 : B 0 2 = 0) : B = blk (lev B) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk, lev, h00, h10, h20, h01, h02]

@[expose] def blkSL (g : SL(2, F)) : Matrix.SpecialLinearGroup (Fin 3) F :=
  ⟨blk (g : Matrix (Fin 2) (Fin 2) F), by rw [det_blk, g.2]⟩

theorem blkSL_mem_stabE0 (g : SL(2, F)) : blkSL g ∈ stabE0 F :=
  mem_stabE0.mpr (blk_mulVec_e0 _)

theorem tor_mul_blkSL (μ : Fˣ) (g : SL(2, F)) : tor μ * blkSL g = blkSL g * tor μ :=
  Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_tor]
    exact torMat_mul_blk μ _)

theorem mul_row0_eq_zero {A B : Matrix (Fin 3) (Fin 3) F} (ha1 : A 0 1 = 0) (ha2 : A 0 2 = 0)
    (hb1 : B 0 1 = 0) (hb2 : B 0 2 = 0) : (A * B) 0 1 = 0 ∧ (A * B) 0 2 = 0 := by
  constructor <;> simp [Matrix.mul_apply, Fin.sum_univ_three, ha1, ha2, hb1, hb2]

theorem blk_row0 (g : Matrix (Fin 2) (Fin 2) F) : blk g 0 1 = 0 ∧ blk g 0 2 = 0 := by
  constructor <;> rfl

end SL3Pt

variable {G : Type} [Group G] [Finite G]

namespace Setting4311

variable {T M L : Subgroup G} {n : ℕ} {I H K : Subgroup G} {t : G} {m : ℕ} {F : Type} [Field F]
  [Fintype F] {α : ↥K →* ↥(StatedSL 3 F)} {β : ↥(u4311 I K) →* Multiplicative (Fin 3 → F)}
  {W' : Submodule F (Fin 3 → F)} {ZS K₂ R₂ : Subgroup G} {μ : Fˣ} {y : G}
variable (s : Setting4311 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y)
include s

theorem levi_coe (k : ↥K₂) : ((s.levi k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
    lev (((α ⟨k, s.K₂_le_K k.2⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) := by
  show ((leviHom F ((stE0Equiv F) (s.αK₂ k)) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = _
  rw [leviHom_coe, coe_stE0Equiv, s.coe_αK₂]

theorem α_entries {k : G} (hk : k ∈ K₂) :
    (((α ⟨k, s.K₂_le_K hk⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0 = 1 ∧
      (((α ⟨k, s.K₂_le_K hk⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 0 =
        0 ∧
      (((α ⟨k, s.K₂_le_K hk⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 0 =
        0 := by
  have h := (mem_stE0 _).mp (s.α_mem_stE0 hk)
  refine ⟨?_, ?_, ?_⟩
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using congrFun h 0
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using congrFun h 1
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using congrFun h 2

theorem exists_levi_lift {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {y' : G}
    (hy' : y' ∈ Subgroup.zpowers y) (hy'o : orderOf y' = p) (g : SL(2, F)) :
    ∃ k : G, ∃ hk : k ∈ K₂, y' * k = k * y' ∧
      (((α ⟨k, s.K₂_le_K hk⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        SL3Pt.blk (g : Matrix (Fin 2) (Fin 2) F) ∧ s.levi ⟨k, hk⟩ = g := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB : specialLinearGroupEquivStatedSL 3 F (SL3Pt.blkSL g) ∈ stE0 F :=
    ⟨_, SL3Pt.blkSL_mem_stabE0 g, rfl⟩
  rw [← s.K₂_map] at hB
  obtain ⟨⟨k₀, hk₀K⟩, hk₀, hαk₀⟩ := hB
  have hk₀' : k₀ ∈ K₂ := hk₀
  set B := K₂ ⊓ pCoreOf 2 K with hBdef
  have hX : IsPGroup p ↥(Subgroup.zpowers y') :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hy'o, pow_one])
  have hBc : ¬ p ∣ Nat.card ↥B := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp ((pCoreOf_isPGroup 2 K).to_le
      (inf_le_right : B ≤ pCoreOf 2 K))
    rw [hk]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  have hy'K : y' ∈ K := s.Y_le_K hy'
  have hXB : Subgroup.zpowers y' ≤ Subgroup.normalizer (B : Set G) := by
    rw [Subgroup.zpowers_le]
    exact mem_normalizer_inf (s.Y_le_normalizer_K₂ hy')
      (le_normalizer_pCoreOf 2 K hy'K)
  have ha : ∀ x ∈ Subgroup.zpowers y', k₀⁻¹ * (x * k₀ * x⁻¹) ∈ B := by
    intro x hx
    have hxY : x ∈ Subgroup.zpowers y := (Subgroup.zpowers_le.mpr hy') hx
    have hxK : x ∈ K := s.Y_le_K hxY
    have hxk : x * k₀ * x⁻¹ ∈ K₂ :=
      (Subgroup.mem_normalizer_iff.mp (s.Y_le_normalizer_K₂ hxY) k₀).mp hk₀'
    have hwK : k₀⁻¹ * (x * k₀ * x⁻¹) ∈ K :=
      K.mul_mem (K.inv_mem hk₀K) (K.mul_mem (K.mul_mem hxK hk₀K) (K.inv_mem hxK))
    refine ⟨K₂.mul_mem (K₂.inv_mem hk₀') hxk, ?_⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxY
    have hα1 : α ⟨k₀⁻¹ * (y ^ i * k₀ * (y ^ i)⁻¹), hwK⟩ = 1 := by
      have e : (⟨k₀⁻¹ * (y ^ i * k₀ * (y ^ i)⁻¹), hwK⟩ : ↥K) =
          (⟨k₀, hk₀K⟩ : ↥K)⁻¹ * ((⟨y ^ i, hxK⟩ : ↥K) * ⟨k₀, hk₀K⟩ * (⟨y ^ i, hxK⟩ : ↥K)⁻¹) := rfl
      have hcomm : specialLinearGroupEquivStatedSL 3 F (SL3Pt.tor (μ ^ i)) *
          specialLinearGroupEquivStatedSL 3 F (SL3Pt.blkSL g) =
          specialLinearGroupEquivStatedSL 3 F (SL3Pt.blkSL g) *
            specialLinearGroupEquivStatedSL 3 F (SL3Pt.tor (μ ^ i)) := by
        rw [← map_mul, ← map_mul, SL3Pt.tor_mul_blkSL]
      rw [e, map_mul, map_inv, map_mul, map_mul, map_inv, hαk₀, s.α_zpow, hcomm]
      group
    have hker : (⟨k₀⁻¹ * (y ^ i * k₀ * (y ^ i)⁻¹), hwK⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := by
      rw [← s.modO2.2]
      exact hα1
    exact (mem_pCoreOf_iff' _).mpr hker
  obtain ⟨b, hb, hfix⟩ := exists_mul_fixed_of_isPGroup hX hBc hXB ha
  have hkK₂ : k₀ * b ∈ K₂ := K₂.mul_mem hk₀' hb.1
  have hαb : α ⟨k₀ * b, s.K₂_le_K hkK₂⟩ = α ⟨k₀, hk₀K⟩ := by
    have hbK : b ∈ K := s.K₂_le_K hb.1
    have hb1 : α ⟨b, hbK⟩ = 1 := by
      have : (⟨b, hbK⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := (mem_pCoreOf_iff' _).mp hb.2
      rw [← s.modO2.2] at this
      exact this
    have e : (⟨k₀ * b, s.K₂_le_K hkK₂⟩ : ↥K) = ⟨k₀, hk₀K⟩ * ⟨b, hbK⟩ := rfl
    rw [e, map_mul, hb1, mul_one]
  have hmat : (((α ⟨k₀ * b, s.K₂_le_K hkK₂⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = SL3Pt.blk (g : Matrix (Fin 2) (Fin 2) F) := by
    rw [hαb, hαk₀, specialLinearGroupEquivStatedSL_coe]
    rfl
  refine ⟨k₀ * b, hkK₂, ?_, hmat, ?_⟩
  · have h1 := hfix y' (Subgroup.mem_zpowers y')
    calc y' * (k₀ * b) = y' * (k₀ * b) * y'⁻¹ * y' := by group
      _ = k₀ * b * y' := by rw [h1]
  · apply Subtype.ext
    rw [s.levi_coe]
    show lev (((α ⟨k₀ * b, s.K₂_le_K hkK₂⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = _
    rw [hmat, SL3Pt.lev_blk]

theorem eq_one_of_levi_eq_one (h135 : AsC135Three) (hR : L2RankOneSylowFact)
    (hC : LemmaC53C56Six) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) {y' : G}
    (hy' : y' ∈ Subgroup.zpowers y) (hy'1 : y' ≠ 1) {k : G} (hk : k ∈ K₂)
    (hc : y' * k = k * y')
    (h01 : (((α ⟨k, s.K₂_le_K hk⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) 0 1 = 0)
    (h02 : (((α ⟨k, s.K₂_le_K hk⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) 0 2 = 0)
    (hl : s.levi ⟨k, hk⟩ = 1) : k = 1 := by
  obtain ⟨h00, h10, h20⟩ := s.α_entries hk
  have hlev : lev (((α ⟨k, s.K₂_le_K hk⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = 1 := by
    have h := s.levi_coe ⟨k, hk⟩
    rw [hl, Matrix.SpecialLinearGroup.coe_one] at h
    exact h.symm
  have hM := SL3Pt.eq_blk_lev h00 h10 h20 h01 h02
  rw [hlev] at hM
  have hα1 : α ⟨k, s.K₂_le_K hk⟩ = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [hM]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [SL3Pt.blk]
  have hkO : k ∈ pCoreOf 2 K := by
    have : (⟨k, s.K₂_le_K hk⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := by
      rw [← s.modO2.2]
      exact hα1
    exact (mem_pCoreOf_iff' _).mpr this
  rw [s.pCoreOf_K_eq h135 hR hC h37 h38 h39] at hkO
  have hfix : y' * k * y'⁻¹ = k := by rw [hc, mul_inv_cancel_right]
  have hkU : k ∈ u4311 I K := s.Y_fpf_Q hy' hy'1 hkO (by
    rw [hfix, mul_inv_cancel]
    exact Subgroup.one_mem _)
  exact s.Y_fpf_U hy' hy'1 hkU hfix

omit [Finite G] [Fintype F] s in
theorem α_mat_mul {k k' : G} (hk : k ∈ K) (hk' : k' ∈ K) :
    (((α ⟨k * k', K.mul_mem hk hk'⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) =
      (((α ⟨k, hk⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        (((α ⟨k', hk'⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  have e : (⟨k * k', K.mul_mem hk hk'⟩ : ↥K) = ⟨k, hk⟩ * ⟨k', hk'⟩ := rfl
  rw [e, map_mul]
  rfl

theorem sq_eq_one_of_unipotent (h135 : AsC135Three) (hR : L2RankOneSylowFact)
    (hC : LemmaC53C56Six) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) {y' : G}
    (hy' : y' ∈ Subgroup.zpowers y) (hy'1 : y' ≠ 1) {k : G} (hk : k ∈ K₂)
    (hc : y' * k = k * y')
    (h01 : (((α ⟨k, s.K₂_le_K hk⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) 0 1 = 0)
    (h02 : (((α ⟨k, s.K₂_le_K hk⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) 0 2 = 0)
    {c : F} (hl : ((s.levi ⟨k, hk⟩ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, c; 0, 1]) :
    k ^ 2 = 1 := by
  have : CharP F 2 := s.charP
  have hk2 : k * k ∈ K₂ := K₂.mul_mem hk hk
  have hm := α_mat_mul (α := α) (s.K₂_le_K hk) (s.K₂_le_K hk)
  have hrow := SL3Pt.mul_row0_eq_zero h01 h02 h01 h02
  rw [pow_two]
  refine s.eq_one_of_levi_eq_one h135 hR hC h37 h38 h39 hy' hy'1 hk2 ?_ ?_ ?_ ?_
  · calc y' * (k * k) = (y' * k) * k := (mul_assoc _ _ _).symm
      _ = (k * y') * k := by rw [hc]
      _ = k * (y' * k) := mul_assoc _ _ _
      _ = k * (k * y') := by rw [hc]
      _ = k * k * y' := (mul_assoc _ _ _).symm
  · rw [show (⟨k * k, s.K₂_le_K hk2⟩ : ↥K) = ⟨k * k, K.mul_mem (s.K₂_le_K hk) (s.K₂_le_K hk)⟩
      from rfl, hm]
    exact hrow.1
  · rw [show (⟨k * k, s.K₂_le_K hk2⟩ : ↥K) = ⟨k * k, K.mul_mem (s.K₂_le_K hk) (s.K₂_le_K hk)⟩
      from rfl, hm]
    exact hrow.2
  · have e : (⟨k * k, hk2⟩ : ↥K₂) = ⟨k, hk⟩ * ⟨k, hk⟩ := rfl
    apply Subtype.ext
    rw [e, map_mul, Matrix.SpecialLinearGroup.coe_mul, hl, Matrix.SpecialLinearGroup.coe_one]
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ← two_mul, h2]

theorem KZ_quasisimple (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) {KZ : Subgroup G}
    (hKZ : KZ ∈ cComp (Subgroup.centralizer (ZS : Set G))) (hK₂ : K₂ ≤ KZ) :
    CFSG.IsQuasisimple (↥KZ ⧸ CFSG.pCore 2 ↥KZ) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := s.charP
  have hyp := s.sk.base.hyp
  have hH : pCoreOf 2 (Subgroup.normalizer (ZS : Set G)) ≠ ⊥ := s.inH_GZ.2
  have hKZ' := cComp_normalizer hKZ
  have hstrong := lemma_1_2_1_four_strong hyp.qtke hyp.simple hyp.nonabelian h36 hH hKZ'
  obtain ⟨e⟩ := modO2_mulEquiv hKZ'
  have hqs : CFSG.IsQuasisimple ↥(modO2Image (Subgroup.normalizer (ZS : Set G)) KZ) →
      CFSG.IsQuasisimple (↥KZ ⧸ CFSG.pCore 2 ↥KZ) := fun h =>
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm h
  have hcase : A36Case3 ↥(modO2Image (Subgroup.normalizer (ZS : Set G)) KZ) ∨
      A36Case4 ↥(modO2Image (Subgroup.normalizer (ZS : Set G)) KZ) → False := by
    intro h34
    obtain ⟨r, hr, h5, χ₀, -, hχ₀ker⟩ := exists_sl2_surjection_of_case34 h34
    have hr2 : r ≠ 2 := by omega
    have hFodd : Odd (Nat.card ↥χ₀.ker) := by
      rw [hχ₀ker, hstrong.2.1.1]
      exact A312.odd_card_oddCore _
    obtain ⟨ψ, -, hψker⟩ := exists_modO2_surjection hKZ'
    let f : ↥K₂ →* Matrix.SpecialLinearGroup (Fin 2) (ZMod r) :=
      χ₀.comp (ψ.comp (Subgroup.inclusion hK₂))
    have hker : ∀ k : ↥K₂, k ^ 2 = 1 → f k = 1 → s.levi k = 1 := by
      intro k hk2 hk
      set w := ψ (Subgroup.inclusion hK₂ k) with hw
      have hwk : w ∈ χ₀.ker := hk
      have hw2 : w ^ 2 = 1 := by rw [hw, ← map_pow, ← map_pow, hk2, map_one, map_one]
      have hwo : orderOf w = 1 := by
        have h1 : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one hw2
        have h2 : Odd (orderOf w) := Odd.of_dvd_nat hFodd (by
          have := Subgroup.orderOf_dvd_natCard χ₀.ker hwk
          exact this)
        rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
        · exact h
        · rw [h] at h2
          exact absurd h2 (by decide)
      have hw1 : Subgroup.inclusion hK₂ k ∈ ψ.ker := orderOf_eq_one_iff.mp hwo
      rw [hψker] at hw1
      have hvO : (k : G) ∈ pCoreOf 2 KZ := by
        exact ⟨_, hw1, rfl⟩
      have hle : K₂ ⊓ pCoreOf 2 KZ ≤ pCoreOf 2 K₂ := by
        refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
          ((pCoreOf_isPGroup 2 KZ).to_le inf_le_right)
        intro g hg
        exact mem_normalizer_inf (Subgroup.le_normalizer hg)
          (le_normalizer_pCoreOf 2 KZ (hK₂ hg))
      have hkO := hle ⟨k.2, hvO⟩
      rw [← MonoidHom.mem_ker, s.ker_levi]
      exact (mem_pCoreOf_iff' k).mp hkO
    have hcardF : 2 < (Finset.univ.erase (0 : F)).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, s.card_F]
      have : 4 ≤ 2 ^ m :=
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) s.two_le
      omega
    obtain ⟨c₁, hc₁, c₂, hc₂, hc₁₂⟩ :=
      Finset.one_lt_card.mp (by omega : 1 < (Finset.univ.erase (0 : F)).card)
    rw [Finset.mem_erase] at hc₁ hc₂
    obtain ⟨p, hp, hp2, hpn⟩ := s.exists_odd_prime_dvd
    obtain ⟨y', hy', hy'o⟩ := s.exists_elt_Y hpn
    have hy'1 : y' ≠ 1 := fun h => by
      rw [h, orderOf_one] at hy'o
      exact hp.one_lt.ne hy'o
    let u : F → SL(2, F) := fun c => ⟨!![1, c; 0, 1], by simp [Matrix.det_fin_two]⟩
    have hu1 : ∀ c : F, u c = 1 → c = 0 := fun c h => by
      have := congrFun (congrFun (congrArg Subtype.val h) 0) 1
      simpa [u] using this
    obtain ⟨k₁, hk₁, hk₁c, hk₁m, hk₁l⟩ := s.exists_levi_lift hp hp2 hy' hy'o (u c₁)
    obtain ⟨k₂, hk₂, hk₂c, hk₂m, hk₂l⟩ := s.exists_levi_lift hp hp2 hy' hy'o (u c₂)
    have hk₁₂ : k₁ * k₂ ∈ K₂ := K₂.mul_mem hk₁ hk₂
    have hm₁₂ := α_mat_mul (α := α) (s.K₂_le_K hk₁) (s.K₂_le_K hk₂)
    have hrow₁ := SL3Pt.blk_row0 ((u c₁ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)
    have hrow₂ := SL3Pt.blk_row0 ((u c₂ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)
    have hrow : _ := SL3Pt.mul_row0_eq_zero (hk₁m ▸ hrow₁.1) (hk₁m ▸ hrow₁.2) (hk₂m ▸ hrow₂.1)
      (hk₂m ▸ hrow₂.2)
    have hsq₁ : (⟨k₁, hk₁⟩ : ↥K₂) ^ 2 = 1 := Subtype.ext (by
      simpa using s.sq_eq_one_of_unipotent h135 hR hC h37 h38 h39 hy' hy'1 hk₁ hk₁c
        (hk₁m ▸ hrow₁.1) (hk₁m ▸ hrow₁.2) (c := c₁) (by rw [hk₁l]))
    have hsq₂ : (⟨k₂, hk₂⟩ : ↥K₂) ^ 2 = 1 := Subtype.ext (by
      simpa using s.sq_eq_one_of_unipotent h135 hR hC h37 h38 h39 hy' hy'1 hk₂ hk₂c
        (hk₂m ▸ hrow₂.1) (hk₂m ▸ hrow₂.2) (c := c₂) (by rw [hk₂l]))
    have hl₁₂ : ((s.levi ⟨k₁ * k₂, hk₁₂⟩ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
        !![1, c₁ + c₂; 0, 1] := by
      have e : (⟨k₁ * k₂, hk₁₂⟩ : ↥K₂) = ⟨k₁, hk₁⟩ * ⟨k₂, hk₂⟩ := rfl
      rw [e, map_mul, Matrix.SpecialLinearGroup.coe_mul, hk₁l, hk₂l]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [u, Matrix.mul_apply, Fin.sum_univ_two, add_comm]
    have hsq₁₂ : (⟨k₁ * k₂, hk₁₂⟩ : ↥K₂) ^ 2 = 1 := Subtype.ext (by
      have hc12 : y' * (k₁ * k₂) = k₁ * k₂ * y' := by
        calc y' * (k₁ * k₂) = (y' * k₁) * k₂ := by group
          _ = k₁ * (y' * k₂) := by rw [hk₁c, mul_assoc]
          _ = k₁ * k₂ * y' := by rw [hk₂c, mul_assoc]
      have h01 : (((α ⟨k₁ * k₂, s.K₂_le_K hk₁₂⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) 0 1 = 0 := by
        rw [show (⟨k₁ * k₂, s.K₂_le_K hk₁₂⟩ : ↥K) =
          ⟨k₁ * k₂, K.mul_mem (s.K₂_le_K hk₁) (s.K₂_le_K hk₂)⟩ from rfl, hm₁₂]
        exact hrow.1
      have h02 : (((α ⟨k₁ * k₂, s.K₂_le_K hk₁₂⟩ : ↥(StatedSL 3 F)) : GL (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) 0 2 = 0 := by
        rw [show (⟨k₁ * k₂, s.K₂_le_K hk₁₂⟩ : ↥K) =
          ⟨k₁ * k₂, K.mul_mem (s.K₂_le_K hk₁) (s.K₂_le_K hk₂)⟩ from rfl, hm₁₂]
        exact hrow.2
      simpa using s.sq_eq_one_of_unipotent h135 hR hC h37 h38 h39 hy' hy'1 hk₁₂ hc12 h01 h02
        hl₁₂)
    have hf₁ : f ⟨k₁, hk₁⟩ ≠ 1 := fun h => hc₁.1 (hu1 c₁ (by
      rw [← hk₁l]
      exact hker _ hsq₁ h))
    have hf₂ : f ⟨k₂, hk₂⟩ ≠ 1 := fun h => hc₂.1 (hu1 c₂ (by
      rw [← hk₂l]
      exact hker _ hsq₂ h))
    have hm₁ := sl2_coe_eq_neg_one_of_sq hr hr2 (f ⟨k₁, hk₁⟩)
      (by rw [← map_pow, hsq₁, map_one]) hf₁
    have hm₂ := sl2_coe_eq_neg_one_of_sq hr hr2 (f ⟨k₂, hk₂⟩)
      (by rw [← map_pow, hsq₂, map_one]) hf₂
    have hf₁₂ : f ⟨k₁ * k₂, hk₁₂⟩ = 1 := by
      have e : (⟨k₁ * k₂, hk₁₂⟩ : ↥K₂) = ⟨k₁, hk₁⟩ * ⟨k₂, hk₂⟩ := rfl
      apply Subtype.ext
      rw [e, map_mul, Matrix.SpecialLinearGroup.coe_mul, hm₁, hm₂,
        Matrix.SpecialLinearGroup.coe_one, neg_mul_neg, mul_one]
    have hl1 := hker _ hsq₁₂ hf₁₂
    have h0 : c₁ + c₂ = 0 := by
      have := congrFun (congrFun (congrArg Subtype.val hl1) 0) 1
      rw [hl₁₂] at this
      simpa using this
    exact hc₁₂ (by
      have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
      calc c₁ = c₁ + (c₁ + c₂) := by rw [h0, add_zero]
        _ = c₂ + 2 * c₁ := by ring
        _ = c₂ := by rw [h2, zero_mul, add_zero])
  rcases hstrong.1 with ⟨hc, -⟩ | ⟨hc, -⟩ | h3 | h4
  · exact hqs hc.1
  · exact hqs hc.1
  · exact (hcase (Or.inl h3)).elim
  · exact (hcase (Or.inr h4)).elim

end Setting4311

end CFSG.Quasithin.H13.Ch4
