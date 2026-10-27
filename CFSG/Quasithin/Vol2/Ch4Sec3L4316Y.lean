module

public import CFSG.Quasithin.Vol2.Ch4Sec3L4316Star

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

theorem mem_radE0_iff {x : ↥(StatedSL 3 F)} :
    x ∈ radE0 F ↔ ∃ a b : F, x = specialLinearGroupEquivStatedSL 3 F (uSL a b 0) := by
  constructor
  · rintro ⟨B, hB, rfl⟩
    obtain ⟨a, b, rfl⟩ := mem_rad1_iff_uSL.mp hB
    exact ⟨a, b, rfl⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨uSL a b 0, mem_rad1_iff_uSL.mpr ⟨a, b, rfl⟩, rfl⟩

theorem tor_conj_uSL (μ : Fˣ) (a b : F) :
    tor μ * uSL a b 0 * (tor μ)⁻¹ =
      uSL (((μ⁻¹ : Fˣ) : F) ^ 3 * a) (((μ⁻¹ : Fˣ) : F) ^ 3 * b) 0 := by
  rw [← map_inv]
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_tor, coe_tor,
    coe_uSL, coe_uSL]
  fin_cases i <;> fin_cases j <;>
    simp [torMat, uMat, Matrix.mul_apply, Matrix.diagonal_apply] <;> ring

theorem blkSL_mul_uSL (g : SL(2, F)) :
    blkSL g * uSL ((g : Matrix (Fin 2) (Fin 2) F) 0 0) ((g : Matrix (Fin 2) (Fin 2) F) 0 1) 0 =
      uSL 1 0 0 * blkSL g := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_uSL]
  fin_cases i <;> fin_cases j <;> simp [blkSL, blk, uMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem exists_blkSL_conj {a b : F} (hab : a ≠ 0 ∨ b ≠ 0) :
    ∃ g : SL(2, F), blkSL g * uSL a b 0 * (blkSL g)⁻¹ = uSL 1 0 0 := by
  have key : ∀ g : SL(2, F), (g : Matrix (Fin 2) (Fin 2) F) 0 0 = a →
      (g : Matrix (Fin 2) (Fin 2) F) 0 1 = b → blkSL g * uSL a b 0 * (blkSL g)⁻¹ = uSL 1 0 0 := by
    intro g h0 h1
    rw [mul_inv_eq_iff_eq_mul, ← h0, ← h1]
    exact blkSL_mul_uSL g
  by_cases ha : a = 0
  · have hb : b ≠ 0 := hab.resolve_left (not_not.mpr ha)
    refine ⟨⟨!![0, b; -b⁻¹, 0], ?_⟩, key _ ?_ rfl⟩
    · simp [Matrix.det_fin_two, hb]
    · simp [ha]
  · refine ⟨⟨!![a, b; 0, a⁻¹], ?_⟩, key _ rfl rfl⟩
    simp [Matrix.det_fin_two, ha]

theorem exists_stabE0_conj {a b c d : F} (hab : a ≠ 0 ∨ b ≠ 0) (hcd : c ≠ 0 ∨ d ≠ 0) :
    ∃ B ∈ stabE0 F, B * uSL a b 0 * B⁻¹ = uSL c d 0 := by
  obtain ⟨g₁, h₁⟩ := exists_blkSL_conj hab
  obtain ⟨g₂, h₂⟩ := exists_blkSL_conj hcd
  refine ⟨(blkSL g₂)⁻¹ * blkSL g₁,
    mul_mem (inv_mem (blkSL_mem_stabE0 g₂)) (blkSL_mem_stabE0 g₁), ?_⟩
  calc (blkSL g₂)⁻¹ * blkSL g₁ * uSL a b 0 * ((blkSL g₂)⁻¹ * blkSL g₁)⁻¹
      = (blkSL g₂)⁻¹ * (blkSL g₁ * uSL a b 0 * (blkSL g₁)⁻¹) * blkSL g₂ := by group
    _ = (blkSL g₂)⁻¹ * (blkSL g₂ * uSL c d 0 * (blkSL g₂)⁻¹) * blkSL g₂ := by rw [h₁, h₂]
    _ = uSL c d 0 := by group

end SL3Pt

variable {G : Type} [Group G] [Finite G]

namespace Setting4315

variable {T M L : Subgroup G} {n : ℕ} {I H K : Subgroup G} {t : G} {m : ℕ} {F : Type} [Field F]
  [Fintype F] {α : ↥K →* ↥(StatedSL 3 F)} {β : ↥(u4311 I K) →* Multiplicative (Fin 3 → F)}
  {W' : Submodule F (Fin 3 → F)} {ZS K₂ R₂ : Subgroup G} {μ : Fˣ} {y : G} {KZ : Subgroup G}
variable (s : Setting4315 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y KZ)
include s

theorem mem_q4311_iff (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) {k : G} (hk : k ∈ K) :
    k ∈ q4311 I K ↔ α ⟨k, hk⟩ = 1 := by
  rw [← s.pCoreOf_K_eq h135 hR hC h37 h38 h39]
  have := mem_pCoreOf_iff' (⟨k, hk⟩ : ↥K)
  rw [← s.modO2.2, MonoidHom.mem_ker] at this
  exact this

theorem R₂_le_K : R₂ ≤ K := by
  rw [s.R₂_eq_P₀]
  exact Subgroup.map_subtype_le _

theorem α_mem_radE0 {r : G} (hr : r ∈ R₂) : α ⟨r, s.R₂_le_K hr⟩ ∈ radE0 F := by
  have hr' : r ∈ ((radE0 F).comap α).map K.subtype := s.R₂_eq_P₀ ▸ hr
  obtain ⟨_, h⟩ := Setting4311.mem_P₀.mp hr'
  exact h

theorem mem_R₂_of {k : G} (hk : k ∈ K) (h : α ⟨k, hk⟩ ∈ radE0 F) : k ∈ R₂ := by
  rw [s.R₂_eq_P₀]
  exact Setting4311.mem_P₀.mpr ⟨hk, h⟩

theorem q4311_le_R₂ (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) : q4311 I K ≤ R₂ := by
  rw [← s.pCoreOf_K_eq h135 hR hC h37 h38 h39, s.R₂_eq_P₀]
  exact s.pCoreOf_K_le_P₀

theorem rangeRestrict_eq_one {g : ↥s.G₀} (hg : (g : G) ∈ s.C₀) : s.rho.rangeRestrict g = 1 :=
  Subtype.ext (s.rho_eq_one_of_mem_C₀ g.2 hg)

theorem exists_conj_R₂ (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) {r r₂ : G} (hr : r ∈ R₂)
    (hrQ : r ∉ q4311 I K) (hr₂ : r₂ ∈ R₂) :
    r₂ ∈ q4311 I K ∨ ∃ k ∈ K₂, (k * r * k⁻¹)⁻¹ * r₂ ∈ q4311 I K := by
  obtain ⟨a, b, hab⟩ := SL3Pt.mem_radE0_iff.mp (s.α_mem_radE0 hr)
  obtain ⟨c, d, hcd⟩ := SL3Pt.mem_radE0_iff.mp (s.α_mem_radE0 hr₂)
  have hab0 : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    push Not at h
    apply hrQ
    rw [s.mem_q4311_iff h135 hR hC h37 h38 h39 (s.R₂_le_K hr), hab, h.1, h.2, uSL_zero, map_one]
  by_cases hcd0 : c = 0 ∧ d = 0
  · left
    rw [s.mem_q4311_iff h135 hR hC h37 h38 h39 (s.R₂_le_K hr₂), hcd, hcd0.1, hcd0.2, uSL_zero,
      map_one]
  · right
    have hcd0' : c ≠ 0 ∨ d ≠ 0 := by
      by_contra h
      push Not at h
      exact hcd0 h
    obtain ⟨B, hB, hBe⟩ := SL3Pt.exists_stabE0_conj hab0 hcd0'
    obtain ⟨k, hk⟩ := s.αK₂_surjective ⟨specialLinearGroupEquivStatedSL 3 F B, B, hB, rfl⟩
    have hkα : α ⟨k, s.K₂_le_K k.2⟩ = specialLinearGroupEquivStatedSL 3 F B := by
      have := congrArg Subtype.val hk
      rw [s.coe_αK₂] at this
      exact this
    refine ⟨k, k.2, ?_⟩
    have hkK : (k : G) ∈ K := s.K₂_le_K k.2
    have hmem : ((k : G) * r * (k : G)⁻¹)⁻¹ * r₂ ∈ K :=
      K.mul_mem (K.inv_mem (K.mul_mem (K.mul_mem hkK (s.R₂_le_K hr)) (K.inv_mem hkK)))
        (s.R₂_le_K hr₂)
    rw [s.mem_q4311_iff h135 hR hC h37 h38 h39 hmem]
    have h1 : (⟨((k : G) * r * (k : G)⁻¹)⁻¹ * r₂, hmem⟩ : ↥K) =
        ((⟨k, hkK⟩ : ↥K) * ⟨r, s.R₂_le_K hr⟩ * (⟨k, hkK⟩ : ↥K)⁻¹)⁻¹ *
          ⟨r₂, s.R₂_le_K hr₂⟩ := rfl
    have key : (B * uSL a b 0 * B⁻¹)⁻¹ * uSL c d 0 = 1 := by rw [hBe, inv_mul_cancel]
    have := congrArg (specialLinearGroupEquivStatedSL 3 F) key
    simp only [map_mul, map_inv, map_one] at this
    rw [h1]
    simp only [map_mul, map_inv, hkα, hab, hcd]
    exact this

theorem rangeRestrict_mem_pCoreOf {h : ↥s.G₀} (hh : (h : G) ∈ pCoreOf 2 K₂) :
    s.rho.rangeRestrict h ∈ pCoreOf 2 (s.star K₂) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hhK : (h : G) ∈ K₂ := pCoreOf_le 2 K₂ hh
  set f := s.starHom s.K₂_le_G₀ with hf
  have hfs := s.starHom_surjective s.K₂_le_G₀
  have hn : ((CFSG.pCore 2 ↥K₂).map f).Normal :=
    (CFSG.pCore_normal : (CFSG.pCore 2 ↥K₂).Normal).map _ hfs
  have hp : IsPGroup 2 ↥((CFSG.pCore 2 ↥K₂).map f) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥K₂)).map _
  have hle : (CFSG.pCore 2 ↥K₂).map f ≤ CFSG.pCore 2 ↥(s.star K₂) := le_sSup ⟨hn, hp⟩
  have h1 : (⟨h, hhK⟩ : ↥K₂) ∈ CFSG.pCore 2 ↥K₂ := (mem_pCoreOf_iff' _).mp hh
  have h2 := hle ⟨_, h1, rfl⟩
  exact (mem_pCoreOf_iff' (f ⟨h, hhK⟩)).mpr h2

theorem q4311_le_C₀ (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hy : y ∈ s.C₀) :
    q4311 I K ≤ s.C₀ := by
  have hQG : q4311 I K ≤ s.G₀ := (s.q4311_le_R₂ h135 hR hC h37 h38 h39).trans s.R₂_le_G₀
  rw [s.q4311_eq_commutator, Subgroup.commutator_le]
  intro q hq z hz
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hyj : y ^ j ∈ s.C₀ := Subgroup.zpow_mem _ hy j
  rw [commutatorElement_def]
  refine Subgroup.mul_mem _ ?_ (Subgroup.inv_mem _ hyj)
  exact (Subgroup.mem_normalizer_iff.mp (s.le_normalizer_C₀ (hQG hq)) _).mp hyj

theorem R₂_le_C₀_of_three_le (h135 : AsC135Three) (hR : L2RankOneSylowFact)
    (hC : LemmaC53C56Six) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hy : y ∈ s.C₀) (hm : 3 ≤ m) : R₂ ≤ s.C₀ := by
  have hQ := s.q4311_le_C₀ h135 hR hC h37 h38 h39 hy
  intro r hr
  obtain ⟨a, b, hab⟩ := SL3Pt.mem_radE0_iff.mp (s.α_mem_radE0 hr)
  set ν : F := ((μ⁻¹ : Fˣ) : F) ^ 3 with hν
  have hν1 : ν ≠ 1 := by
    intro h
    have h3 : μ⁻¹ ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h)
    have h3' : μ ^ 3 = 1 := by
      rw [inv_pow, inv_eq_one] at h3
      exact h3
    have hdvd := orderOf_dvd_of_pow_eq_one h3'
    rw [s.μ_order] at hdvd
    have h1 : 2 ^ m - 1 ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
    have h2 : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  have hc : (1 - ν) ≠ 0 := sub_ne_zero.mpr (Ne.symm hν1)
  set a' := a / (1 - ν) with ha'
  set b' := b / (1 - ν) with hb'
  obtain ⟨k', hk'⟩ := s.modO2.1 (specialLinearGroupEquivStatedSL 3 F (uSL a' b' 0))
  have hr' : (k' : G) ∈ R₂ :=
    s.mem_R₂_of k'.2 (by rw [hk']; exact SL3Pt.mem_radE0_iff.mpr ⟨_, _, rfl⟩)
  have hk'G : (k' : G) ∈ s.G₀ := s.R₂_le_G₀ hr'
  have hcomm : (k' : G) * y * (k' : G)⁻¹ * y⁻¹ ∈ s.C₀ :=
    Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (s.le_normalizer_C₀ hk'G) y).mp hy)
      (Subgroup.inv_mem _ hy)
  have key : (uSL a b 0)⁻¹ *
      (uSL a' b' 0 * SL3Pt.tor μ * (uSL a' b' 0)⁻¹ * (SL3Pt.tor μ)⁻¹) = 1 := by
    have h1 : SL3Pt.tor μ * (uSL a' b' 0)⁻¹ * (SL3Pt.tor μ)⁻¹ = uSL (ν * -a') (ν * -b') 0 := by
      rw [uSL_inv, show a' * 0 - b' = -b' by ring, neg_zero, SL3Pt.tor_conj_uSL]
    have h2 : uSL a' b' 0 * uSL (ν * -a') (ν * -b') 0 = uSL a b 0 := by
      rw [uSL_mul, show a' + ν * -a' = a by rw [ha']; field_simp; ring,
        show b' + ν * -b' + a' * 0 = b by rw [hb']; field_simp; ring, add_zero]
    calc (uSL a b 0)⁻¹ * (uSL a' b' 0 * SL3Pt.tor μ * (uSL a' b' 0)⁻¹ * (SL3Pt.tor μ)⁻¹)
        = (uSL a b 0)⁻¹ * (uSL a' b' 0 * (SL3Pt.tor μ * (uSL a' b' 0)⁻¹ * (SL3Pt.tor μ)⁻¹)) := by
          group
      _ = 1 := by rw [h1, h2, inv_mul_cancel]
  have hrK : r ∈ K := s.R₂_le_K hr
  have hmem : r⁻¹ * ((k' : G) * y * (k' : G)⁻¹ * y⁻¹) ∈ K :=
    K.mul_mem (K.inv_mem hrK) (K.mul_mem (K.mul_mem (K.mul_mem k'.2 s.y_mem) (K.inv_mem k'.2))
      (K.inv_mem s.y_mem))
  have hα : α ⟨r⁻¹ * ((k' : G) * y * (k' : G)⁻¹ * y⁻¹), hmem⟩ = 1 := by
    have h1 : (⟨r⁻¹ * ((k' : G) * y * (k' : G)⁻¹ * y⁻¹), hmem⟩ : ↥K) =
        (⟨r, hrK⟩ : ↥K)⁻¹ * (k' * ⟨y, s.y_mem⟩ * k'⁻¹ * (⟨y, s.y_mem⟩ : ↥K)⁻¹) := rfl
    have := congrArg (specialLinearGroupEquivStatedSL 3 F) key
    simp only [map_mul, map_inv, map_one] at this
    rw [h1]
    simp only [map_mul, map_inv, hk', s.α_y]
    rw [show (⟨r, hrK⟩ : ↥K) = ⟨r, s.R₂_le_K hr⟩ from rfl, hab]
    exact this
  have hq : r⁻¹ * ((k' : G) * y * (k' : G)⁻¹ * y⁻¹) ∈ s.C₀ :=
    hQ ((s.mem_q4311_iff h135 hR hC h37 h38 h39 hmem).mpr hα)
  have e : r = ((k' : G) * y * (k' : G)⁻¹ * y⁻¹) *
      (r⁻¹ * ((k' : G) * y * (k' : G)⁻¹ * y⁻¹))⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ hcomm (Subgroup.inv_mem _ hq)

theorem false_of_three_le (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hy : y ∈ s.C₀)
    (hm : 3 ≤ m) : False := by
  have hR₂C := s.R₂_le_C₀_of_three_le h135 hR hC h37 h38 h39 hy hm
  apply s.star_R₂_ne_bot h135 hR hC h36 h37 h38 h39
  rw [eq_bot_iff]
  rintro _ ⟨g, hg, rfl⟩
  rw [Subgroup.mem_bot]
  exact s.rangeRestrict_eq_one (hR₂C hg)

theorem mem_q4311_of_mem_C₀ (h135 : AsC135Three) (hR : L2RankOneSylowFact)
    (hC : LemmaC53C56Six) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (hy : y ∈ s.C₀) {r : G} (hr : r ∈ R₂) (hrC : r ∈ s.C₀) :
    r ∈ q4311 I K := by
  by_contra hrQ
  have hQ := s.q4311_le_C₀ h135 hR hC h37 h38 h39 hy
  have hR₂C : R₂ ≤ s.C₀ := by
    intro r₂ hr₂
    rcases s.exists_conj_R₂ h135 hR hC h37 h38 h39 hr hrQ hr₂ with h | ⟨k, hk, hq⟩
    · exact hQ h
    · have hkG : k ∈ s.G₀ := s.K₂_le_G₀ hk
      have h1 : k * r * k⁻¹ ∈ s.C₀ :=
        (Subgroup.mem_normalizer_iff.mp (s.le_normalizer_C₀ hkG) r).mp hrC
      have e : r₂ = (k * r * k⁻¹) * ((k * r * k⁻¹)⁻¹ * r₂) := by group
      rw [e]
      exact Subgroup.mul_mem _ h1 (hQ hq)
  apply s.star_R₂_ne_bot h135 hR hC h36 h37 h38 h39
  rw [eq_bot_iff]
  rintro _ ⟨g, hg, rfl⟩
  rw [Subgroup.mem_bot]
  exact s.rangeRestrict_eq_one (hR₂C hg)

theorem isElemAbelian_star_R₂ (h135 : AsC135Three) (hR : L2RankOneSylowFact)
    (hC : LemmaC53C56Six) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hQ : q4311 I K ≤ s.C₀) : IsElemAbelian 2 (s.star R₂) := by
  have : CharP F 2 := s.charP
  refine ⟨⟨⟨fun x x' => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨_, g, hg, rfl⟩ := x
    obtain ⟨_, g', hg', rfl⟩ := x'
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    obtain ⟨a, b, hab⟩ := SL3Pt.mem_radE0_iff.mp (s.α_mem_radE0 (r := (g : G)) hg)
    obtain ⟨a', b', hab'⟩ := SL3Pt.mem_radE0_iff.mp (s.α_mem_radE0 (r := (g' : G)) hg')
    have hmem : (g : G) * g' * (g : G)⁻¹ * (g' : G)⁻¹ ∈ K :=
      K.mul_mem (K.mul_mem (K.mul_mem (s.R₂_le_K hg) (s.R₂_le_K hg')) (K.inv_mem (s.R₂_le_K hg)))
        (K.inv_mem (s.R₂_le_K hg'))
    have hcQ : (g : G) * g' * (g : G)⁻¹ * (g' : G)⁻¹ ∈ q4311 I K := by
      rw [s.mem_q4311_iff h135 hR hC h37 h38 h39 hmem]
      have h1 : (⟨(g : G) * g' * (g : G)⁻¹ * (g' : G)⁻¹, hmem⟩ : ↥K) =
          ⟨g, s.R₂_le_K hg⟩ * ⟨g', s.R₂_le_K hg'⟩ * (⟨g, s.R₂_le_K hg⟩ : ↥K)⁻¹ *
            (⟨g', s.R₂_le_K hg'⟩ : ↥K)⁻¹ := rfl
      have key : uSL a b 0 * uSL a' b' 0 * (uSL a b 0)⁻¹ * (uSL a' b' 0)⁻¹ = 1 := by
        have hc : uSL a b 0 * uSL a' b' 0 = uSL a' b' 0 * uSL a b 0 := by
          rw [uSL_mul, uSL_mul]
          congr 1 <;> ring
        rw [hc]
        group
      have := congrArg (specialLinearGroupEquivStatedSL 3 F) key
      simp only [map_mul, map_inv, map_one] at this
      rw [h1]
      simp only [map_mul, map_inv, hab, hab']
      exact this
    have hcomm := s.rangeRestrict_eq_one (g := g * g' * g⁻¹ * g'⁻¹) (hQ (by simpa using hcQ))
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at hcomm
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hcomm)
  · obtain ⟨g, hg, rfl⟩ := hx
    obtain ⟨a, b, hab⟩ := SL3Pt.mem_radE0_iff.mp (s.α_mem_radE0 (r := (g : G)) hg)
    have hmem : (g : G) ^ 2 ∈ K := K.pow_mem (s.R₂_le_K hg) 2
    have hsQ : (g : G) ^ 2 ∈ q4311 I K := by
      rw [s.mem_q4311_iff h135 hR hC h37 h38 h39 hmem]
      have h1 : (⟨(g : G) ^ 2, hmem⟩ : ↥K) = (⟨g, s.R₂_le_K hg⟩ : ↥K) ^ 2 := rfl
      rw [h1, map_pow]
      exact SL3Pt.sq_eq_one_of_mem_radE0 (s.α_mem_radE0 hg)
    rw [← map_pow]
    exact s.rangeRestrict_eq_one (hQ (by simpa using hsQ))

theorem card_star_R₂ (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hy : y ∈ s.C₀)
    (hm : m = 2) : Nat.card ↥(s.star R₂) = 2 ^ 4 := by
  have hQ := s.q4311_le_C₀ h135 hR hC h37 h38 h39 hy
  set φ₁ := s.starHom s.R₂_le_G₀ with hφ₁def
  have hφ₁ := s.starHom_surjective s.R₂_le_G₀
  let φ₂ : ↥R₂ →* ↥(radE0 F) := (α.comp (Subgroup.inclusion s.R₂_le_K)).codRestrict (radE0 F)
    fun r => s.α_mem_radE0 r.2
  have hφ₂ : Function.Surjective φ₂ := by
    rintro ⟨x, hx⟩
    obtain ⟨k, hk⟩ := s.modO2.1 x
    have hkR : (k : G) ∈ R₂ :=
      s.mem_R₂_of k.2 (by rw [show (⟨(k : G), k.2⟩ : ↥K) = k from rfl, hk]; exact hx)
    exact ⟨⟨k, hkR⟩, Subtype.ext hk⟩
  have hker : φ₁.ker = φ₂.ker := by
    ext r
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : s.rho ⟨r, s.R₂_le_G₀ r.2⟩ = 1 :=
        congrArg (fun w : ↥(s.star R₂) => ((w : ↥s.rho.range) : MulAut (ModO2 KZ))) h
      have hrQ := s.mem_q4311_of_mem_C₀ h135 hR hC h36 h37 h38 h39 hy r.2
        (s.mem_C₀_of_rho_eq_one _ h1)
      exact Subtype.ext ((s.mem_q4311_iff h135 hR hC h37 h38 h39 (s.R₂_le_K r.2)).mp hrQ)
    · intro h
      have h1 : α ⟨r, s.R₂_le_K r.2⟩ = 1 := congrArg Subtype.val h
      have hrQ := (s.mem_q4311_iff h135 hR hC h37 h38 h39 (s.R₂_le_K r.2)).mpr h1
      exact Subtype.ext (s.rangeRestrict_eq_one (g := ⟨r, s.R₂_le_G₀ r.2⟩) (hQ hrQ))
  have e1 := QuotientGroup.quotientKerEquivOfSurjective φ₁ hφ₁
  have e2 := QuotientGroup.quotientKerEquivOfSurjective φ₂ hφ₂
  have e3 := QuotientGroup.quotientMulEquivOfEq hker
  rw [← Nat.card_congr e1.toEquiv, Nat.card_congr e3.toEquiv, Nat.card_congr e2.toEquiv]
  have hbij : Function.Bijective (fun p : F × F =>
      (⟨specialLinearGroupEquivStatedSL 3 F (uSL p.1 p.2 0),
        SL3Pt.mem_radE0_iff.mpr ⟨p.1, p.2, rfl⟩⟩ : ↥(radE0 F))) := by
    constructor
    · intro p p' h
      have h1 := (specialLinearGroupEquivStatedSL 3 F).injective (congrArg Subtype.val h)
      obtain ⟨h2, h3, -⟩ := uSL_injective h1
      exact Prod.ext h2 h3
    · rintro ⟨x, hx⟩
      obtain ⟨a, b, rfl⟩ := SL3Pt.mem_radE0_iff.mp hx
      exact ⟨(a, b), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_prod]
  simp only [Nat.card_eq_fintype_card, s.card_F, hm]
  norm_num

theorem star_R₂_irreducible (h135 : AsC135Three) (hR : L2RankOneSylowFact)
    (hC : LemmaC53C56Six) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hQ : q4311 I K ≤ s.C₀) (R' : Subgroup ↥s.rho.range) (hR' : R' ≤ s.star R₂)
    (hKR' : s.star K₂ ≤ Subgroup.normalizer (R' : Set ↥s.rho.range)) :
    R' = ⊥ ∨ R' = s.star R₂ := by
  by_cases hbot : R' = ⊥
  · exact Or.inl hbot
  right
  apply le_antisymm hR'
  obtain ⟨⟨x, hxR'⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  obtain ⟨g, hg, rfl⟩ := hR' hxR'
  have hgQ : (g : G) ∉ q4311 I K := by
    intro h
    apply hx1
    exact Subtype.ext (s.rangeRestrict_eq_one (hQ h))
  intro z hz
  obtain ⟨g₂, hg₂, rfl⟩ := hz
  rcases s.exists_conj_R₂ h135 hR hC h37 h38 h39 (r := (g : G)) (r₂ := (g₂ : G)) hg hgQ hg₂ with
    h | ⟨k, hk, hq⟩
  · rw [s.rangeRestrict_eq_one (hQ h)]
    exact R'.one_mem
  · set kk : ↥s.G₀ := ⟨k, s.K₂_le_G₀ hk⟩ with hkk
    have hq' : (((kk * g * kk⁻¹)⁻¹ * g₂ : ↥s.G₀) : G) ∈ q4311 I K := by
      simpa [hkk] using hq
    have e2 : s.rho.rangeRestrict g₂ = s.rho.rangeRestrict kk * s.rho.rangeRestrict g *
        (s.rho.rangeRestrict kk)⁻¹ * s.rho.rangeRestrict ((kk * g * kk⁻¹)⁻¹ * g₂) := by
      rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
      congr 1
      group
    rw [e2, s.rangeRestrict_eq_one (hQ hq'), mul_one]
    have hkk' : s.rho.rangeRestrict kk ∈ s.star K₂ := ⟨kk, hk, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hKR' hkk') _).mp hxR'

theorem false_of_two (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hy : y ∈ s.C₀)
    (hm : m = 2)
    (hE : ¬ (IsElemAbelian 2 (s.star R₂) ∧ Nat.card ↥(s.star R₂) = 2 ^ 4 ∧
      ∀ R' : Subgroup ↥s.rho.range, R' ≤ s.star R₂ →
        s.star K₂ ≤ Subgroup.normalizer (R' : Set ↥s.rho.range) → R' = ⊥ ∨ R' = s.star R₂)) :
    False := by
  have hQ := s.q4311_le_C₀ h135 hR hC h37 h38 h39 hy
  exact hE ⟨s.isElemAbelian_star_R₂ h135 hR hC h37 h38 h39 hQ,
    s.card_star_R₂ h135 hR hC h36 h37 h38 h39 hy hm,
    fun R' h1 h2 => s.star_R₂_irreducible h135 hR hC h37 h38 h39 hQ R' h1 h2⟩

theorem false_of_rho_y_eq_one (h135 : AsC135Three) (hR : L2RankOneSylowFact)
    (hC : LemmaC53C56Six) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (hy1 : s.rho ⟨y, s.y_mem_G₀⟩ = 1)
    (hE : m = 2 → ¬ (IsElemAbelian 2 (s.star R₂) ∧ Nat.card ↥(s.star R₂) = 2 ^ 4 ∧
      ∀ R' : Subgroup ↥s.rho.range, R' ≤ s.star R₂ →
        s.star K₂ ≤ Subgroup.normalizer (R' : Set ↥s.rho.range) → R' = ⊥ ∨ R' = s.star R₂)) :
    False := by
  have hy := s.mem_C₀_of_rho_eq_one s.y_mem_G₀ hy1
  rcases Nat.lt_or_ge m 3 with h | h
  · have hm : m = 2 := by
      have := s.two_le
      omega
    exact s.false_of_two h135 hR hC h36 h37 h38 h39 hy hm (hE hm)
  · exact s.false_of_three_le h135 hR hC h36 h37 h38 h39 hy h

end Setting4315

end CFSG.Quasithin.H13.Ch4
