module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowU3Char3List
public import CFSG.RankThree.PartTwo.Sec4.Item49Small

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.RankThree.PartTwo.Sec4.Item434CharThree CFSG.LieType.Universal.Unitary
open CFSG.SectionRank.OddCover (heisSU coe_heisSU coe_heisSU_inv SU_ext hSU hSU_conj_heisSU
  heis_mul)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive
  exists_add_unitaryInvolution_eq)
open CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThree (Real3)
open CFSG.Assembly.RankThreeEven (projSU)
open Matrix
open U3Char3

namespace U3Char3

theorem real3_of_sylow_witness {S : Type} [Group S] [Finite S] (n : ℕ) (Q : Subgroup S)
    (hQ : Nat.card Q = 3 ^ n) (hS : ¬ 3 ^ (n + 1) ∣ Nat.card S)
    (hw : ∀ q ∈ Q, ∃ t : S, t * q * t⁻¹ = q⁻¹) : Real3 S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro g hg
  by_cases h1 : g = 1
  · exact ⟨1, by simp [h1]⟩
  · obtain ⟨h, hh⟩ := CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.exists_conj_mem_of_orderOf_prime_sylow
      3 n Q hQ hS (orderOf_eq_prime hg h1)
    obtain ⟨t, ht⟩ := hw _ hh
    refine ⟨h * t * h⁻¹, ?_⟩
    calc h * t * h⁻¹ * g * (h * t * h⁻¹)⁻¹ = h * (t * (h⁻¹ * g * h) * t⁻¹) * h⁻¹ := by group
      _ = g⁻¹ := by rw [ht]; group

section Invert

variable {F : Type} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c)

theorem heisSU_conj_heisSU (a₁ b₁ c d : F) (h₁ : b₁ + σ b₁ + σ a₁ * a₁ = 0)
    (hcd : d + σ d + σ c * c = 0)
    (h' : d + c * σ a₁ - a₁ * σ c + σ (d + c * σ a₁ - a₁ * σ c) + σ c * c = 0) :
    heisSU hσ a₁ b₁ h₁ * heisSU hσ c d hcd * (heisSU hσ a₁ b₁ h₁)⁻¹ =
      heisSU hσ c (d + c * σ a₁ - a₁ * σ c) h' := by
  apply SU_ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_heisSU_inv, coe_heisSU, coe_heisSU, coe_heisSU, heis_mul, heis_mul]
  congr 1
  · ring
  · simp only [map_neg, hσ]
    ring

variable [CharP F 3]

theorem exists_inverter_heisSU_of_ne_zero (hτ : ∀ x : F, σ x = x → ∃ c, c + σ c = x) {a b : F}
    (hab : b + σ b + σ a * a = 0) (ha : a ≠ 0) :
    ∃ t : SU σ 3, t * heisSU hσ a b hab * t⁻¹ = (heisSU hσ a b hab)⁻¹ := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq F 3]; norm_num)
  have hσa : σ a ≠ 0 := (map_ne_zero σ).mpr ha
  obtain ⟨v, hv⟩ : ∃ v : F, v = -2 * b - a * σ a := ⟨_, rfl⟩
  have hσv : σ v = -v := by
    rw [hv]
    simp only [map_sub, map_mul, map_neg, map_ofNat, hσ]
    linear_combination (-2) * hab
  obtain ⟨a₁, ha₁⟩ : ∃ a₁ : F, a₁ = v / (2 * σ a) := ⟨_, rfl⟩
  have key : a₁ * σ a - a * σ a₁ = v := by
    rw [ha₁, map_div₀, map_mul, hσv, hσ, map_ofNat]
    field_simp
    ring
  have htr : σ (-(σ a₁ * a₁)) = -(σ a₁ * a₁) := by rw [map_neg, map_mul, hσ, mul_comm]
  obtain ⟨b₁, hb₁⟩ := hτ _ htr
  have hu : b₁ + σ b₁ + σ a₁ * a₁ = 0 := by linear_combination hb₁
  have hab' : b + σ b + σ (-a) * -a = 0 := by
    rw [map_neg]
    linear_combination hab
  have hinv : -b - a * σ a + σ (-b - a * σ a) + σ (-a) * -a = 0 := by
    rw [map_sub, map_neg, map_mul, map_neg, hσ]
    linear_combination -hab
  have hcd' : b + -a * σ a₁ - a₁ * σ (-a) + σ (b + -a * σ a₁ - a₁ * σ (-a)) + σ (-a) * -a = 0 := by
    simp only [map_add, map_sub, map_mul, map_neg, hσ]
    linear_combination hab
  refine ⟨heisSU hσ a₁ b₁ hu * hSU, ?_⟩
  have e1 : heisSU hσ a₁ b₁ hu * hSU * heisSU hσ a b hab * (heisSU hσ a₁ b₁ hu * hSU)⁻¹ =
      heisSU hσ a₁ b₁ hu * (hSU * heisSU hσ a b hab * hSU⁻¹) * (heisSU hσ a₁ b₁ hu)⁻¹ := by
    group
  rw [e1, hSU_conj_heisSU hσ a b hab hab', heisSU_conj_heisSU hσ a₁ b₁ (-a) b hu hab' hcd',
    heisSU_inv_eq' hσ a b hab hinv]
  apply SU_ext
  rw [coe_heisSU, coe_heisSU]
  congr 1
  simp only [map_neg]
  linear_combination key + hv

theorem exists_inverter_heisSU_of_eq_zero {t : F} (ht : t ≠ 0) (htn : t * σ t = -1) {b : F}
    (hab : b + σ b + σ 0 * 0 = 0) :
    ∃ g : SU σ 3, g * heisSU hσ 0 b hab * g⁻¹ = (heisSU hσ 0 b hab)⁻¹ := by
  have hs : σ t ≠ 0 := (map_ne_zero σ).mpr ht
  have hab' : b * (t * σ t) + σ (b * (t * σ t)) + σ (0 * t ^ 2 / σ t) * (0 * t ^ 2 / σ t) = 0 := by
    rw [htn]
    simp only [zero_mul, zero_div, map_zero, mul_zero, add_zero, map_mul, map_neg, map_one,
      mul_neg, mul_one]
    simp only [map_zero, zero_mul, add_zero, mul_zero] at hab
    linear_combination -hab
  have hinv : -b - 0 * σ 0 + σ (-b - 0 * σ 0) + σ (-0) * -0 = 0 := by
    simp only [map_zero, zero_mul, sub_zero, map_neg, neg_zero, mul_zero, add_zero]
    simp only [map_zero, zero_mul, add_zero, mul_zero] at hab
    linear_combination -hab
  refine ⟨torusU hσ ht, ?_⟩
  rw [mul_inv_eq_iff_eq_mul, torusU_mul_heisSU hσ ht 0 b hab hab', heisSU_inv_eq' hσ 0 b hab hinv]
  congr 1
  apply SU_ext
  rw [coe_heisSU, coe_heisSU]
  congr 1
  · simp
  · rw [htn]
    simp

theorem exists_inverter_of_mem_heisU (hτ : ∀ x : F, σ x = x → ∃ c, c + σ c = x)
    (hn : ∃ t : F, t ≠ 0 ∧ t * σ t = -1) {q : SU σ 3} (hq : q ∈ heisU hσ) :
    ∃ t : SU σ 3, t * q * t⁻¹ = q⁻¹ := by
  obtain ⟨a, b, hab, hm⟩ := hq
  obtain rfl : q = heisSU hσ a b hab := SU_ext hm
  by_cases ha : a = 0
  · subst ha
    obtain ⟨t, ht, htn⟩ := hn
    exact exists_inverter_heisSU_of_eq_zero hσ ht htn hab
  · exact exists_inverter_heisSU_of_ne_zero hσ hτ hab ha

end Invert

end U3Char3

namespace U3Char3

theorem exists_norm_eq_neg_one_gf_nine :
    ∃ t : GaloisField 3 (2 * 1), t ≠ 0 ∧
      t * unitaryInvolution (GaloisField 3 (2 * 1)) 3 1 t = -1 := by
  have hF : Nat.card (GaloisField 3 (2 * 1)) = 9 := by
    rw [card_galois_two_mul one_ne_zero]
    norm_num
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (GaloisField 3 (2 * 1))ˣ)
  have hord : orderOf g = 8 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hF]
  have h8 : g ^ 8 = 1 := hord ▸ pow_orderOf_eq_one g
  have h4 : g ^ 4 ≠ 1 := fun h => by
    have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h)
    omega
  have h4' : (g : GaloisField 3 (2 * 1)) ^ 4 = -1 := by
    have hsq : ((g : GaloisField 3 (2 * 1)) ^ 4) * ((g : GaloisField 3 (2 * 1)) ^ 4) = 1 := by
      have := congrArg Units.val h8
      rw [Units.val_pow_eq_pow_val, Units.val_one] at this
      rw [← pow_add]
      exact this
    rcases mul_self_eq_one_iff.mp hsq with h | h
    · exact absurd (Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])) h4
    · exact h
  refine ⟨g, g.ne_zero, ?_⟩
  rw [CFSG.LieType.BorelTits.unitaryInvolution_apply]
  calc (g : GaloisField 3 (2 * 1)) * (g : GaloisField 3 (2 * 1)) ^ 3 ^ 1
      = (g : GaloisField 3 (2 * 1)) ^ 4 := by norm_num [← pow_succ']
    _ = -1 := h4'

end U3Char3

theorem real3_SU_three_one : Real3 (SU (unitaryInvolution (GaloisField 3 (2 * 1)) 3 1) 3) := by
  have hF : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 := card_galois_two_mul one_ne_zero
  refine real3_of_sylow_witness (3 * 1) (heisU (unitaryInvolution_involutive hF))
    (by rw [card_heisU hF]; norm_num) (not_three_pow_succ_dvd_card_SU_three one_ne_zero) ?_
  intro q hq
  exact exists_inverter_of_mem_heisU (unitaryInvolution_involutive hF)
    (fun x hx => exists_add_unitaryInvolution_eq hF hx) exists_norm_eq_neg_one_gf_nine hq

theorem real3_projSU_three_one : Real3 (projSU 3 3 1) :=
  Real3.of_mulEquiv (suEquivProjSU one_ne_zero).symm real3_SU_three_one

theorem noCover3_projSU_three_one : NoCover3 (projSU 3 3 1) := by
  intro L _ _ hq hZ ⟨φ⟩
  haveI : Group.IsPerfect L := hq.1
  have hF : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 := card_galois_two_mul one_ne_zero
  let eSt : SU (unitaryInvolution (GaloisField 3 (2 * 1)) 3 1) 3 ≃*
      CFSG.Open.StatedSU 3 3 (GaloisField 3 (2 * 1)) :=
    (equivStatedSU hF 3).trans (MulEquiv.subgroupCongr (by rw [pow_one]))
  let ψ : L ⧸ Subgroup.center L ≃* CFSG.Open.StatedSU 3 3 (GaloisField 3 (2 * 1)) :=
    φ.trans ((suEquivProjSU one_ne_zero).symm.trans eSt)
  set π : L →* CFSG.Open.StatedSU 3 3 (GaloisField 3 (2 * 1)) :=
    ψ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L)) with hπ
  have hsurj : Function.Surjective π := by
    intro y
    obtain ⟨q, rfl⟩ := ψ.surjective y
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨l, rfl⟩
  have hker : π.ker = Subgroup.center L := by
    ext l
    simp only [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      QuotientGroup.mk'_apply]
    rw [map_eq_one_iff ψ ψ.injective, QuotientGroup.eq_one_iff]
  have hodd : Odd (Nat.card π.ker) := by
    rw [hker]
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZ
    rw [hn]
    exact Odd.pow (by decide)
  rw [← hker]
  exact CFSG.SectionRank.OddCover.prime_classical_three_perfect_odd_extension_trivial
    Nat.prime_three (by norm_num) (ε := -1)
    (Or.inr ⟨rfl, by rw [hF]; norm_num, rfl⟩) π hsurj hker.le hodd

theorem listRow_projSU_three_one : ListRow (projSU 3 3 1) := fun _ _ _ =>
  Or.inr (Or.inl ⟨Or.inr ⟨MulEquiv.refl _⟩, real3_projSU_three_one, noCover3_projSU_three_one⟩)

theorem outerRow_projSU_three_one : OuterRow (projSU 3 3 1) :=
  outerRow_of_not_three_dvd_outer
    (CFSG.RankThree.PartTwo.Sec4.Item49Small.not_three_dvd_card_outer_projSU (n := 3) (e := 1)
      (by norm_num) (by norm_num) (by norm_num))

end CFSG.RankThree.PartTwo.Sec4.RonanK432
