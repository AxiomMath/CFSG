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

theorem blkSL_mul_uSL_mul (g : SL(2, F)) (a b : F) :
    blkSL g * uSL (a * (g : Matrix (Fin 2) (Fin 2) F) 0 0 + b * (g : Matrix (Fin 2) (Fin 2) F) 1 0)
      (a * (g : Matrix (Fin 2) (Fin 2) F) 0 1 + b * (g : Matrix (Fin 2) (Fin 2) F) 1 1) 0 =
      uSL a b 0 * blkSL g := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_uSL]
  fin_cases i <;> fin_cases j <;> simp [blkSL, blk, uMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem eq_zero_of_commute_blkSL [CharP F 2] {a b : F}
    (h : ∀ g : SL(2, F), blkSL g * uSL a b 0 = uSL a b 0 * blkSL g) : a = 0 ∧ b = 0 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have key : ∀ g : SL(2, F), a = a * (g : Matrix (Fin 2) (Fin 2) F) 0 0 +
      b * (g : Matrix (Fin 2) (Fin 2) F) 1 0 ∧
      b = a * (g : Matrix (Fin 2) (Fin 2) F) 0 1 + b * (g : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    intro g
    have h1 := (blkSL_mul_uSL_mul g a b).trans (h g).symm
    obtain ⟨e1, e2, -⟩ := uSL_injective (mul_left_cancel h1)
    exact ⟨e1.symm, e2.symm⟩
  have hu := (key ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩).2
  have hl := (key ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩).1
  simp at hu hl
  exact ⟨hu, hl⟩

end SL3Pt

variable {G : Type} [Group G] [Finite G]

namespace Setting4315

variable {T M L : Subgroup G} {n : ℕ} {I H K : Subgroup G} {t : G} {m : ℕ} {F : Type} [Field F]
  [Fintype F] {α : ↥K →* ↥(StatedSL 3 F)} {β : ↥(u4311 I K) →* Multiplicative (Fin 3 → F)}
  {W' : Submodule F (Fin 3 → F)} {ZS K₂ R₂ : Subgroup G} {μ : Fˣ} {y : G} {KZ : Subgroup G}
variable (s : Setting4315 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y KZ)
include s

theorem pCoreOf_K₂_le_R₂ : pCoreOf 2 K₂ ≤ R₂ := by
  rw [s.R₂_eq_P₀]
  exact s.pCoreOf_K₂_le_P₀

theorem commutator_mem_D {r k : G}
    (hr : r ∈ R₂ ⊓ Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G))
    (hk : k ∈ K₂ ⊓ Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G)) :
    k * r * k⁻¹ * r⁻¹ ∈
      pCoreOf 2 K₂ ⊓ Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRK : R₂ ⊓ K₂ ≤ pCoreOf 2 K₂ :=
    le_pCoreOf_of_le_normalizer 2 inf_le_right
      (fun _ hk => mem_normalizer_inf (s.le_normalizer_R₂ (Subgroup.mem_sup_left hk))
        (Subgroup.le_normalizer hk)) (s.isPGroup_R₂.to_le inf_le_left)
  have hkR : k ∈ Subgroup.normalizer (R₂ : Set G) := s.le_normalizer_R₂ (Subgroup.mem_sup_left hk.1)
  have hrK : r ∈ Subgroup.normalizer (K₂ : Set G) := s.R₂_le_normalizer_K₂ hr.1
  refine ⟨hRK ⟨R₂.mul_mem ((Subgroup.mem_normalizer_iff.mp hkR r).mp hr.1) (R₂.inv_mem hr.1), ?_⟩,
    ?_⟩
  · have e : k * r * k⁻¹ * r⁻¹ = k * (r * k⁻¹ * r⁻¹) := by group
    rw [e]
    exact K₂.mul_mem hk.1 ((Subgroup.mem_normalizer_iff.mp hrK k⁻¹).mp (K₂.inv_mem hk.1))
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hk.2 hr.2)
      (Subgroup.inv_mem _ hk.2)) (Subgroup.inv_mem _ hr.2)

theorem eq_of_α_eq_of_mem_D (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) {d d' : G}
    (hd : d ∈ pCoreOf 2 K₂ ⊓ Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G))
    (hd' : d' ∈ pCoreOf 2 K₂ ⊓ Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G))
    (hdK : d ∈ K) (hd'K : d' ∈ K) (h : α ⟨d, hdK⟩ = α ⟨d', hd'K⟩) : d = d' := by
  have hmem : d⁻¹ * d' ∈ K := K.mul_mem (K.inv_mem hdK) hd'K
  have hq : d⁻¹ * d' ∈ q4311 I K := by
    rw [s.mem_q4311_iff h135 hR hC h37 h38 h39 hmem]
    have e : (⟨d⁻¹ * d', hmem⟩ : ↥K) = (⟨d, hdK⟩ : ↥K)⁻¹ * ⟨d', hd'K⟩ := rfl
    rw [e, map_mul, map_inv, h, inv_mul_cancel]
  have hc : d⁻¹ * d' ∈ Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hd.2) hd'.2
  have h1 : d⁻¹ * d' ∈ q4311 I K ⊓ Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) :
      Set G) := ⟨hq, hc⟩
  rw [s.q4311_inf_centralizer_Y, Subgroup.mem_bot] at h1
  exact (inv_mul_eq_one.mp h1)

theorem exists_levi_lift_X (hm : m = 2) (g : SL(2, F)) :
    ∃ k ∈ K₂ ⊓ Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G),
      ∃ hk : k ∈ K, α ⟨k, hk⟩ = specialLinearGroupEquivStatedSL 3 F (SL3Pt.blkSL g) := by
  have hy3 : orderOf y = 3 := by rw [s.orderOf_y, hm]; norm_num
  obtain ⟨k, hk, hyk, hkα, -⟩ := s.exists_levi_lift Nat.prime_three (by norm_num)
    (Subgroup.mem_zpowers y) hy3 g
  refine ⟨k, ⟨hk, ?_⟩, s.K₂_le_K hk, ?_⟩
  · refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ((Commute.zpow_left hyk j)).eq
  · apply Subtype.ext
    apply Units.ext
    rw [hkα]
    rfl

theorem eq_one_of_fixed_D (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hm : m = 2) {d : G}
    (hd : d ∈ pCoreOf 2 K₂ ⊓ Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G))
    (hfix : ∀ k ∈ K₂ ⊓ Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G),
      k * d * k⁻¹ = d) : d = 1 := by
  have : CharP F 2 := s.charP
  have hdR : d ∈ R₂ := s.pCoreOf_K₂_le_R₂ hd.1
  obtain ⟨a, b, hab⟩ := SL3Pt.mem_radE0_iff.mp (s.α_mem_radE0 hdR)
  have hcomm : ∀ g : SL(2, F), SL3Pt.blkSL g * uSL a b 0 = uSL a b 0 * SL3Pt.blkSL g := by
    intro g
    obtain ⟨k, hkX, hkK, hkα⟩ := s.exists_levi_lift_X hm g
    have h1 := hfix k hkX
    have hmem : k * d * k⁻¹ ∈ K := K.mul_mem (K.mul_mem hkK (s.R₂_le_K hdR)) (K.inv_mem hkK)
    have h2 : α ⟨k * d * k⁻¹, hmem⟩ = α ⟨d, s.R₂_le_K hdR⟩ := by
      congr 1
      exact Subtype.ext h1
    have e : (⟨k * d * k⁻¹, hmem⟩ : ↥K) = ⟨k, hkK⟩ * ⟨d, s.R₂_le_K hdR⟩ * (⟨k, hkK⟩ : ↥K)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hkα, hab, ← map_inv, ← map_mul, ← map_mul] at h2
    have h3 := (specialLinearGroupEquivStatedSL 3 F).injective h2
    rw [mul_inv_eq_iff_eq_mul] at h3
    exact h3
  obtain ⟨ha, hb⟩ := SL3Pt.eq_zero_of_commute_blkSL hcomm
  have hd1 : α ⟨d, s.R₂_le_K hdR⟩ = α ⟨1, K.one_mem⟩ := by
    rw [hab, ha, hb, uSL_zero, map_one]
    exact (map_one α).symm
  exact s.eq_of_α_eq_of_mem_D h135 hR hC h37 h38 h39 hd
    ⟨(pCoreOf 2 K₂).one_mem, Subgroup.one_mem _⟩ _ _ hd1

theorem D_irred (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hm : m = 2) (J : Subgroup G)
    (hJ : J ≤ pCoreOf 2 K₂ ⊓ Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G))
    (hJn : K₂ ⊓ Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G) ≤
      Subgroup.normalizer (J : Set G)) :
    J = ⊥ ∨
      J = pCoreOf 2 K₂ ⊓ Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G) := by
  by_cases hbot : J = ⊥
  · exact Or.inl hbot
  right
  apply le_antisymm hJ
  obtain ⟨⟨d, hdJ⟩, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
  have hdD := hJ hdJ
  have hdR : d ∈ R₂ := s.pCoreOf_K₂_le_R₂ hdD.1
  obtain ⟨a, b, hab⟩ := SL3Pt.mem_radE0_iff.mp (s.α_mem_radE0 hdR)
  have hab0 : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    push Not at h
    apply hd1'
    have hd1 : α ⟨d, s.R₂_le_K hdR⟩ = α ⟨1, K.one_mem⟩ := by
      rw [hab, h.1, h.2, uSL_zero, map_one]
      exact (map_one α).symm
    exact s.eq_of_α_eq_of_mem_D h135 hR hC h37 h38 h39 hdD
      ⟨(pCoreOf 2 K₂).one_mem, Subgroup.one_mem _⟩ _ _ hd1
  intro d' hd'D
  have hd'R : d' ∈ R₂ := s.pCoreOf_K₂_le_R₂ hd'D.1
  obtain ⟨c, c₂, hce⟩ := SL3Pt.mem_radE0_iff.mp (s.α_mem_radE0 hd'R)
  by_cases hce0 : c = 0 ∧ c₂ = 0
  · have hd'1 : α ⟨d', s.R₂_le_K hd'R⟩ = α ⟨1, K.one_mem⟩ := by
      rw [hce, hce0.1, hce0.2, uSL_zero, map_one]
      exact (map_one α).symm
    rw [s.eq_of_α_eq_of_mem_D h135 hR hC h37 h38 h39 hd'D
      ⟨(pCoreOf 2 K₂).one_mem, Subgroup.one_mem _⟩ _ _ hd'1]
    exact J.one_mem
  have hce0' : c ≠ 0 ∨ c₂ ≠ 0 := by
    by_contra h
    push Not at h
    exact hce0 h
  obtain ⟨g₁, h₁⟩ := SL3Pt.exists_blkSL_conj hab0
  obtain ⟨g₂, h₂⟩ := SL3Pt.exists_blkSL_conj hce0'
  obtain ⟨k₁, hk₁X, hk₁K, hk₁α⟩ := s.exists_levi_lift_X hm g₁
  obtain ⟨k₂, hk₂X, hk₂K, hk₂α⟩ := s.exists_levi_lift_X hm g₂
  set k := k₂⁻¹ * k₁ with hk
  have hkX : k ∈ K₂ ⊓ Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hk₂X) hk₁X
  have hkK : k ∈ K := K.mul_mem (K.inv_mem hk₂K) hk₁K
  have hkdD : k * d * k⁻¹ ∈
      pCoreOf 2 K₂ ⊓ Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G) := by
    refine ⟨?_, Subgroup.mul_mem _ (Subgroup.mul_mem _ hkX.2 hdD.2) (Subgroup.inv_mem _ hkX.2)⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hn := normalizer_le_normalizer_pCoreOf 2 K₂ (Subgroup.le_normalizer hkX.1)
    exact (Subgroup.mem_normalizer_iff.mp hn d).mp hdD.1
  have hmem : k * d * k⁻¹ ∈ K := K.mul_mem (K.mul_mem hkK (s.R₂_le_K hdR)) (K.inv_mem hkK)
  have hα : α ⟨k * d * k⁻¹, hmem⟩ = α ⟨d', s.R₂_le_K hd'R⟩ := by
    have e : (⟨k * d * k⁻¹, hmem⟩ : ↥K) =
        ((⟨k₂, hk₂K⟩ : ↥K)⁻¹ * ⟨k₁, hk₁K⟩) * ⟨d, s.R₂_le_K hdR⟩ *
          ((⟨k₂, hk₂K⟩ : ↥K)⁻¹ * ⟨k₁, hk₁K⟩)⁻¹ := rfl
    have key : ((SL3Pt.blkSL g₂)⁻¹ * SL3Pt.blkSL g₁) * uSL a b 0 *
        ((SL3Pt.blkSL g₂)⁻¹ * SL3Pt.blkSL g₁)⁻¹ = uSL c c₂ 0 := by
      calc ((SL3Pt.blkSL g₂)⁻¹ * SL3Pt.blkSL g₁) * uSL a b 0 *
          ((SL3Pt.blkSL g₂)⁻¹ * SL3Pt.blkSL g₁)⁻¹
          = (SL3Pt.blkSL g₂)⁻¹ * (SL3Pt.blkSL g₁ * uSL a b 0 * (SL3Pt.blkSL g₁)⁻¹) *
              SL3Pt.blkSL g₂ := by group
        _ = (SL3Pt.blkSL g₂)⁻¹ * (SL3Pt.blkSL g₂ * uSL c c₂ 0 * (SL3Pt.blkSL g₂)⁻¹) *
              SL3Pt.blkSL g₂ := by rw [h₁, h₂]
        _ = uSL c c₂ 0 := by group
    rw [e, hce]
    simp only [map_mul, map_inv, hk₁α, hk₂α, hab]
    rw [← key]
    simp only [map_mul, map_inv]
  have heq := s.eq_of_α_eq_of_mem_D h135 hR hC h37 h38 h39 hkdD hd'D hmem _ hα
  rw [← heq]
  exact (Subgroup.mem_normalizer_iff.mp (hJn hkX) d).mp hdJ

end Setting4315

end CFSG.Quasithin.H13.Ch4
