module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix.Gamma
public import CFSG.GH74.GLS.IVK.Defs
import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Core
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFooteGen
import CFSG.LocalAnalysis.ComponentClassification.FooteLitGeneration
import CFSG.GF2Type.Aschbacher1976Common.DihedralRank
import CFSG.GroupTheory.ABGLocalTools.SL2FieldAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix

open CFSG.GH74.GLS.IVK CFSG.Open Subgroup

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K]

private theorem mulAut_conj_mul_conj (α : MulAut K) (x : K) :
    α * MulAut.conj x * α⁻¹ = MulAut.conj (α x) := by
  ext y
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

private theorem conj_mem_gammaRk_of_commute {m : ℕ} {A Y D : Subgroup (MulAut K)}
    (hY : innAut K ≤ Y) (hDA : D ≤ A) (hD : 2 ^ m ≤ Nat.card D) {x : K}
    (hx : ∀ d ∈ D, MulAut.conj x * d = d * MulAut.conj x) : MulAut.conj x ∈ gammaRk m A Y := by
  refine inf_normalizer_le_gammaRk hDA hD (Subgroup.mem_inf.mpr ⟨hY ⟨x, rfl⟩, ?_⟩)
  exact Subgroup.centralizer_le_normalizer (D : Set (MulAut K))
    (Subgroup.mem_centralizer_iff.mpr fun d hd => (hx d hd).symm)

private theorem conj_mem_gammaRk_one_of_commute {A Y : Subgroup (MulAut K)} (hY : innAut K ≤ Y)
    {γ : MulAut K} (hγA : γ ∈ A) (hγ2 : γ ^ 2 = 1) (hγ1 : γ ≠ 1) {x : K}
    (hx : MulAut.conj x * γ = γ * MulAut.conj x) : MulAut.conj x ∈ gammaRk 1 A Y := by
  have hcard : 2 ^ 1 ≤ Nat.card (Subgroup.zpowers γ) := by
    rw [Nat.card_zpowers, orderOf_eq_prime hγ2 hγ1]
    norm_num
  refine conj_mem_gammaRk_of_commute hY (Subgroup.zpowers_le.mpr hγA) hcard fun d hd => ?_
  have h1 : γ ∈ Subgroup.centralizer ({MulAut.conj x} : Set (MulAut K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hx.symm
  have h2 : d ∈ Subgroup.centralizer ({MulAut.conj x} : Set (MulAut K)) :=
    (Subgroup.zpowers_le.mpr h1) hd
  exact (Subgroup.mem_centralizer_singleton_iff.mp h2).symm

private theorem conj_mem_gammaRk_one_of_fixed {A Y : Subgroup (MulAut K)} (hY : innAut K ≤ Y)
    {γ : MulAut K} (hγA : γ ∈ A) (hγ2 : γ ^ 2 = 1) (hγ1 : γ ≠ 1) {x : K} (hx : γ x = x) :
    MulAut.conj x ∈ gammaRk 1 A Y := by
  refine conj_mem_gammaRk_one_of_commute hY hγA hγ2 hγ1 ?_
  have h0 : γ * MulAut.conj x * γ⁻¹ = MulAut.conj x := by
    rw [mulAut_conj_mul_conj, hx]
  calc MulAut.conj x * γ = (γ * MulAut.conj x * γ⁻¹) * γ := by rw [h0]
    _ = γ * MulAut.conj x := by group

private theorem mem_gammaRk_of_mem {m : ℕ} {A Y : Subgroup (MulAut K)} (hAY : A ≤ Y)
    (hA2 : 2 ^ m ≤ Nat.card A) {γ : MulAut K} (hγA : γ ∈ A) : γ ∈ gammaRk m A Y :=
  inf_normalizer_le_gammaRk le_rfl hA2 (Subgroup.mem_inf.mpr ⟨hAY hγA, Subgroup.le_normalizer hγA⟩)

private theorem exists_two_ne_one {A : Subgroup (MulAut K)} (hA : IsElemAbelian 2 A)
    (h2 : 2 < Nat.card A) :
    ∃ α β : MulAut K, α ∈ A ∧ β ∈ A ∧ α ^ 2 = 1 ∧ β ^ 2 = 1 ∧ α ≠ 1 ∧ β ≠ 1 ∧ α ≠ β := by
  classical
  have hne : A ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at h2
    omega
  obtain ⟨α, hαA, hα1⟩ : ∃ x ∈ A, x ≠ 1 := by
    by_contra h
    push Not at h
    exact hne (Subgroup.eq_bot_iff_forall A |>.mpr h)
  have hα2 : α ^ 2 = 1 := hA.2 α hαA
  have hcard : Nat.card (Subgroup.zpowers α) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hα2 hα1]
  have hne' : Subgroup.zpowers α ≠ A := by
    intro h
    have : Nat.card A = 2 := by rw [← h, hcard]
    omega
  obtain ⟨β, hβA, hβnot⟩ :=
    (SetLike.lt_iff_le_and_exists.mp (lt_of_le_of_ne (Subgroup.zpowers_le.mpr hαA) hne')).2
  refine ⟨α, β, hαA, hβA, hα2, hA.2 β hβA, hα1, ?_, ?_⟩
  · intro hβ1
    exact hβnot (hβ1 ▸ Subgroup.one_mem (Subgroup.zpowers α))
  · intro hβα
    exact hβnot (hβα ▸ Subgroup.mem_zpowers α)

private theorem center_eq_bot_of_mulEquiv_L2 (e : K ≃* L2 F) :
    Subgroup.center K = ⊥ := by
  have h1 : Subgroup.center (CFSG.GorensteinWalter.PSL2 F) = ⊥ :=
    CFSG.GorensteinWalter.psl2_center_eq_bot F
  have h2 : Subgroup.map (e.trans (L2.equivPSL F) : K →* CFSG.GorensteinWalter.PSL2 F)
      (Subgroup.center K) = ⊥ := by
    rw [Subgroup.map_center_eq, h1]
  have h3 : Subgroup.map (e.trans (L2.equivPSL F) : K →* CFSG.GorensteinWalter.PSL2 F)
      (Subgroup.center K) =
      Subgroup.map (e.trans (L2.equivPSL F) : K →* CFSG.GorensteinWalter.PSL2 F) ⊥ := by
    rw [h2, Subgroup.map_bot]
  exact Subgroup.map_injective (e.trans (L2.equivPSL F)).injective h3

private theorem psl2_card_large {q n : ℕ} (hq : Odd q) (hq11 : 11 ≤ q)
    (hn : n = q * (q ^ 2 - 1) / 2) : 660 ≤ n ∧ n ≠ 2520 := by
  subst hn
  have hq120 : 120 ≤ q ^ 2 - 1 := by
    have h : 11 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq11 2
    have h121 : (121 : ℕ) ≤ q ^ 2 := by norm_num at h ⊢; exact h
    omega
  have h2dvd : 2 ∣ q * (q ^ 2 - 1) :=
    dvd_mul_of_dvd_right (dvd_trans (by norm_num) (Nat.eight_dvd_sq_sub_one_of_odd hq)) q
  constructor
  · have h1 : 660 ≤ q * (q ^ 2 - 1) / 2 := by
      have h3 : 1320 / 2 ≤ q * (q ^ 2 - 1) / 2 :=
        Nat.div_le_div_right (Nat.mul_le_mul hq11 hq120)
      rw [show (1320 : ℕ) / 2 = 660 by norm_num] at h3
      exact h3
    exact h1
  · intro h2520
    have hq2 : q * (q ^ 2 - 1) = 5040 := by
      have h := Nat.mul_div_cancel' h2dvd
      rw [h2520] at h
      omega
    have hq42 : q ≤ 42 := by
      have h := Nat.mul_le_mul_left q hq120
      omega
    interval_cases q <;> norm_num at hq2

private theorem not_isSmallDihedralSimple_of_L2 (hF : L2Field F) (h9 : 9 < Nat.card F)
    (e : K ≃* L2 F) :
    ¬ CFSG.ComponentClassification.AschbacherKnownGroup.IsSmallDihedralSimple K := by
  classical
  intro hsmall
  have hsmall' : CFSG.ComponentClassification.AschbacherKnownGroup.IsSmallDihedralSimple
      (CFSG.GorensteinWalter.PSL2 F) := by
    rcases hsmall with ⟨⟨e7⟩⟩ | ⟨p, f, hpf, hadm, K', hK'fld, hK'fin, hK'card, ⟨eK'⟩⟩
    · exact Or.inl ⟨(e.trans (L2.equivPSL F)).symm.trans e7⟩
    · exact Or.inr ⟨p, f, hpf, hadm, K', hK'fld, hK'fin, hK'card,
        ⟨(e.trans (L2.equivPSL F)).symm.trans eK'⟩⟩
  have hqodd : Odd (Nat.card F) := hF.1
  have hq11 : 11 ≤ Nat.card F := by
    rcases hqodd with ⟨k, hk⟩
    omega
  have hformula : Nat.card (CFSG.GorensteinWalter.PSL2 F) =
      Nat.card F * (Nat.card F ^ 2 - 1) / 2 :=
    CFSG.GorensteinWalter.psl2_card_formula F
      (CFSG.ABGLocalTools.isOddPrimePower_card_of_odd hqodd)
  have hlarge := psl2_card_large hqodd hq11 hformula
  rcases hsmall' with ⟨⟨e7⟩⟩ | ⟨p, f, hpf, hadm, K', hK'fld, hK'fin, hK'card, ⟨eK'⟩⟩
  · have h2520 : Nat.card (CFSG.GorensteinWalter.PSL2 F) = 2520 := by
      rw [Nat.card_congr e7.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      norm_num
    exact hlarge.2 h2520
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hpf
    have hp : p.Prime := hadm.1
    have hf : 1 ≤ f := hadm.2.1
    have hpodd : Odd p := by
      have h1 : Odd (p ^ f) := by
        rcases hpf with h | h | h <;> rw [h] <;> norm_num
      exact Odd.of_dvd_nat h1 (dvd_pow_self p (by omega))
    have hp2 : p ≠ 2 := by
      intro h
      rw [h] at hpodd
      exact (Nat.not_odd_iff_even.mpr even_two) hpodd
    have hoddK' : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K') := by
      rw [hK'card]
      exact ⟨p, f, hp, hpodd, hf, rfl⟩
    have hle : Nat.card (CFSG.GorensteinWalter.PSL2 K') ≤ 360 := by
      rw [CFSG.GorensteinWalter.psl2_card_formula K' hoddK', hK'card]
      rcases hpf with h | h | h <;> rw [h] <;> norm_num
    have heq : Nat.card (CFSG.GorensteinWalter.PSL2 F) =
        Nat.card (CFSG.GorensteinWalter.PSL2 K') := by
      rw [Nat.card_congr eK'.toEquiv, Nat.card_congr (L2.equivPSL K').toEquiv]
    omega

private theorem isElemAbelian_comap_conj {A : Subgroup (MulAut K)}
    (hconjinj : Function.Injective (MulAut.conj : K →* MulAut K)) (hA : IsElemAbelian 2 A) :
    IsElemAbelian 2 (A.comap (MulAut.conj : K →* MulAut K)) := by
  refine ⟨isMulCommutative_iff.mpr ?_, ?_⟩
  · intro x y
    have hx : MulAut.conj (x : K) ∈ A := x.2
    have hy : MulAut.conj (y : K) ∈ A := y.2
    have hc : MulAut.conj (x : K) * MulAut.conj (y : K) =
        MulAut.conj (y : K) * MulAut.conj (x : K) :=
      congrArg Subtype.val (isMulCommutative_iff.mp hA.1 ⟨MulAut.conj (x : K), hx⟩
        ⟨MulAut.conj (y : K), hy⟩)
    refine Subtype.ext ?_
    apply hconjinj
    simp only [Subgroup.coe_mul, map_mul]
    exact hc
  · intro x hx
    have h2 : MulAut.conj x ^ 2 = 1 := hA.2 _ hx
    apply hconjinj
    rw [map_pow, map_one, h2]

private theorem hasDihedralSylowTwo_of_mulEquiv_L2 (hF : L2Field F) (e : K ≃* L2 F) :
    CFSG.ComponentClassification.AschbacherKnownGroup.HasDihedralSylowTwo K := by
  have hgw := CFSG.GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F
    (CFSG.ABGLocalTools.isOddPrimePower_card_of_odd hF.1)
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 (CFSG.GorensteinWalter.PSL2 F)))
  obtain ⟨m, hm, ⟨d⟩⟩ := hgw S
  have h1 : CFSG.ComponentClassification.AschbacherKnownGroup.HasDihedralSylowTwo
      (CFSG.GorensteinWalter.PSL2 F) := ⟨S, m + 1, by omega, ⟨by simpa using d⟩⟩
  exact CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.hasDihedralSylowTwo_of_mulEquiv
    (e.trans (L2.equivPSL F)).symm h1


private theorem innAut_le_gammaRk_one_of_four_group_generation {A : Subgroup (MulAut K)}
    (hA2 : 2 ≤ Nat.card A) {α β : MulAut K}
    (hαA : α ∈ A) (hβA : β ∈ A) (hα2 : α ^ 2 = 1) (hβ2 : β ^ 2 = 1) (hα1 : α ≠ 1)
    (hβ1 : β ≠ 1) (hαβ : α * β = β * α) (hαβne : α ≠ β)
    (hgen : ∀ H : Subgroup K,
      (∀ γ ∈ ({α, β, α * β} : Set (MulAut K)), ∀ x ∈ H, γ x ∈ H) →
      (∀ γ ∈ ({α, β, α * β} : Set (MulAut K)), ∀ x : K, γ x = x → Odd (orderOf x) → x ∈ H) →
      (∀ γ ∈ ({α, β, α * β} : Set (MulAut K)), ∀ t : K, t ^ 2 = 1 → t ≠ 1 →
        γ = MulAut.conj t → ∀ y : K, t ∈ Subgroup.zpowers y → y ∈ H) →
      H = ⊤) :
    innAut K ≤ gammaRk 1 A (innAut K ⊔ A) := by
  classical
  set Y : Subgroup (MulAut K) := innAut K ⊔ A with hYdef
  have hIY : innAut K ≤ Y := by rw [hYdef]; exact le_sup_left
  have hAY : A ≤ Y := by rw [hYdef]; exact le_sup_right
  have hβsq : β * β = 1 := by rw [← pow_two]; exact hβ2
  have hαβ1 : α * β ≠ 1 := by
    intro h
    apply hαβne
    calc α = α * (β * β) := by rw [hβsq, mul_one]
      _ = (α * β) * β := by group
      _ = β := by rw [h]; exact one_mul β
  have hαβ2 : (α * β) ^ 2 = 1 := by
    have h1 : (α * β) * (α * β) = α ^ 2 * β ^ 2 := by
      calc (α * β) * (α * β) = α * (β * α) * β := by group
        _ = α * (α * β) * β := by rw [hαβ]
        _ = α ^ 2 * β ^ 2 := by rw [pow_two, pow_two]; group
    rw [pow_two, h1, hα2, hβ2, one_mul]
  have hset : ∀ γ ∈ ({α, β, α * β} : Set (MulAut K)), γ ∈ A ∧ γ ^ 2 = 1 ∧ γ ≠ 1 := by
    intro γ hγ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hγ
    rcases hγ with rfl | rfl | rfl
    · exact ⟨hαA, hα2, hα1⟩
    · exact ⟨hβA, hβ2, hβ1⟩
    · exact ⟨A.mul_mem hαA hβA, hαβ2, hαβ1⟩
  set H : Subgroup K := (gammaRk 1 A Y).comap (MulAut.conj : K →* MulAut K) with hHdef
  have hinv : ∀ γ ∈ ({α, β, α * β} : Set (MulAut K)), ∀ x ∈ H, γ x ∈ H := by
    intro γ hγ x hx
    have hγG : γ ∈ gammaRk 1 A Y :=
      mem_gammaRk_of_mem hAY (by simpa using hA2) (hset γ hγ).1
    simp only [hHdef, Subgroup.mem_comap] at hx ⊢
    rw [← mulAut_conj_mul_conj γ x]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hγG hx) (Subgroup.inv_mem _ hγG)
  have hP1 : ∀ γ ∈ ({α, β, α * β} : Set (MulAut K)), ∀ x : K, γ x = x →
      Odd (orderOf x) → x ∈ H := by
    intro γ hγ x hx _
    obtain ⟨hγA, hγ2, hγ1⟩ := hset γ hγ
    simp only [hHdef, Subgroup.mem_comap]
    exact conj_mem_gammaRk_one_of_fixed hIY hγA hγ2 hγ1 hx
  have hP2 : ∀ γ ∈ ({α, β, α * β} : Set (MulAut K)), ∀ t : K, t ^ 2 = 1 → t ≠ 1 →
      γ = MulAut.conj t → ∀ y : K, t ∈ Subgroup.zpowers y → y ∈ H := by
    intro γ hγ t _ _ hγt y hy
    obtain ⟨hγA, hγ2, hγ1⟩ := hset γ hγ
    simp only [hHdef, Subgroup.mem_comap]
    refine conj_mem_gammaRk_one_of_commute hIY hγA hγ2 hγ1 ?_
    have hyt : y * t = t * y := by
      have : IsMulCommutative ↥(Subgroup.zpowers y) := Subgroup.zpowers_isMulCommutative y
      exact (Subgroup.mem_centralizer_iff.mp
        (Subgroup.le_centralizer (Subgroup.zpowers y) (Subgroup.mem_zpowers y)) t hy).symm
    rw [hγt, ← map_mul, ← map_mul, hyt]
  have hHtop : H = ⊤ := hgen H hinv hP1 hP2
  rw [innAut, ← Subgroup.map_top (MulAut.conj : K →* MulAut K), Subgroup.map_le_iff_le_comap]
  rw [← hHdef, hHtop]

theorem innAut_le_gammaRk_one_of_card_four (hF : L2Field F) (h9 : 9 < Nat.card F)
    (e : K ≃* L2 F) {A : Subgroup (MulAut K)}
    (hA : IsElemAbelian 2 A) (h4 : Nat.card A = 4) :
    innAut K ≤ gammaRk 1 A (innAut K ⊔ A) := by
  classical
  have : Finite K := Finite.of_injective (e : K → L2 F) e.injective
  have hdih : CFSG.ComponentClassification.AschbacherKnownGroup.HasDihedralSylowTwo K :=
    hasDihedralSylowTwo_of_mulEquiv_L2 hF e
  obtain ⟨f, hf, hq⟩ := CFSG.ABGLocalTools.card_eq_ringChar_pow (F := F)
  have hp : Nat.Prime (ringChar F) := CFSG.ABGLocalTools.ringChar_prime
  have hoddF : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    CFSG.ABGLocalTools.isOddPrimePower_card_of_odd hF.1
  have : IsSimpleGroup (CFSG.GorensteinWalter.PSL2 F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (Nat.succ_le_of_lt hF.2)
  have : IsSimpleGroup K := (e.trans (L2.equivPSL F)).isSimpleGroup
  obtain ⟨α, β, hαA, hβA, hα2, hβ2, hα1, hβ1, hαβne⟩ :=
    exists_two_ne_one hA (by omega)
  have hαβ : α * β = β * α :=
    congrArg Subtype.val (isMulCommutative_iff.mp hA.1 ⟨α, hαA⟩ ⟨β, hβA⟩)
  refine innAut_le_gammaRk_one_of_four_group_generation (by omega) hαA hβA hα2 hβ2
    hα1 hβ1 hαβ hαβne ?_
  intro H hinv hP1 hP2
  rcases CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.fourGroupGeneration_psl2
    hdih (p := ringChar F) (f := f) hp hq hoddF hF.2 (e.trans (L2.equivPSL F))
    hαβ hα2 hβ2 hα1 hβ1 hαβne H hinv hP1 hP2 with h | ⟨hsmall, -⟩
  · exact h
  · exact absurd hsmall (not_isSmallDihedralSimple_of_L2 hF h9 e)


theorem innAut_le_gammaRk_one_of_card_eight (hF : L2Field F) (e : K ≃* L2 F)
    {A : Subgroup (MulAut K)} (hA : IsElemAbelian 2 A)
    (h8 : Nat.card A = 8) :
    innAut K ≤ gammaRk 1 A (innAut K ⊔ A) := by
  classical
  have : Finite K := Finite.of_injective (e : K → L2 F) e.injective
  have hcenter : Subgroup.center K = ⊥ := center_eq_bot_of_mulEquiv_L2 e
  have hconjinj : Function.Injective (MulAut.conj : K →* MulAut K) :=
    CFSG.ComponentClassification.FooteLit.injective_mulAut_conj hcenter
  have hdih : CFSG.ComponentClassification.AschbacherKnownGroup.HasDihedralSylowTwo K :=
    hasDihedralSylowTwo_of_mulEquiv_L2 hF e
  have hEel : IsElemAbelian 2 (A.comap (MulAut.conj : K →* MulAut K)) :=
    isElemAbelian_comap_conj hconjinj hA
  have hmap : (A.comap (MulAut.conj : K →* MulAut K)).map (MulAut.conj : K →* MulAut K) =
      A ⊓ innAut K := by
    rw [Subgroup.map_comap_eq, innAut, inf_comm]
  have hcardE : Nat.card (A.comap (MulAut.conj : K →* MulAut K)) = Nat.card ↥(A ⊓ innAut K) := by
    rw [← hmap, Subgroup.card_map_of_injective hconjinj]
  have hle4 : Nat.card ↥(A ⊓ innAut K) ≤ 4 := by
    rw [← hcardE]
    exact CFSG.GF2Type.Aschbacher1976Common.card_le_four_of_dihedral_or_semidihedral
      (Or.inl hdih) hEel
  have hnotle : ¬ A ≤ innAut K := by
    intro hAle
    have h1 : A ⊓ innAut K = A := inf_eq_left.mpr hAle
    have h2 : Nat.card ↥(A ⊓ innAut K) = 8 := by rw [h1, h8]
    omega
  obtain ⟨α, hαA, hαout⟩ := SetLike.not_le_iff_exists.mp hnotle
  have hα1 : α ≠ 1 := fun h => hαout (h ▸ Subgroup.one_mem (innAut K))
  have hα2 : α ^ 2 = 1 := hA.2 α hαA
  obtain ⟨f, hf, hq⟩ := CFSG.ABGLocalTools.card_eq_ringChar_pow (F := F)
  have hp : Nat.Prime (ringChar F) := CFSG.ABGLocalTools.ringChar_prime
  have hoddF : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    CFSG.ABGLocalTools.isOddPrimePower_card_of_odd hF.1
  have : IsSimpleGroup (CFSG.GorensteinWalter.PSL2 F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (Nat.succ_le_of_lt hF.2)
  have : IsSimpleGroup K := (e.trans (L2.equivPSL F)).isSimpleGroup
  have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val (isMulCommutative_iff.mp hA.1 ⟨x, hx⟩ ⟨y, hy⟩)
  have hcardα : Nat.card (Subgroup.zpowers α) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hα2 hα1]
  have hne' : Subgroup.zpowers α ≠ A := by
    intro h
    rw [h, h8] at hcardα
    omega
  obtain ⟨β, hβA, hβnot⟩ :=
    (SetLike.lt_iff_le_and_exists.mp (lt_of_le_of_ne (Subgroup.zpowers_le.mpr hαA) hne')).2
  have hβ1 : β ≠ 1 := fun h => hβnot (h ▸ Subgroup.one_mem (Subgroup.zpowers α))
  have hβ2 : β ^ 2 = 1 := hA.2 β hβA
  have hαβ : α * β = β * α := hcommA α hαA β hβA
  have hαβne : α ≠ β := fun h => hβnot (h ▸ Subgroup.mem_zpowers α)
  refine innAut_le_gammaRk_one_of_four_group_generation (by omega) hαA hβA hα2 hβ2
    hα1 hβ1 hαβ hαβne ?_
  intro H hinv hP1 hP2
  rcases CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.fourGroupGeneration_psl2
    hdih (p := ringChar F) (f := f) hp hq hoddF hF.2 (e.trans (L2.equivPSL F))
    hαβ hα2 hβ2 hα1 hβ1 hαβne H hinv hP1 hP2 with h | ⟨-, ⟨a, b, ha, hb⟩⟩
  · exact h
  · rw [ha] at hαout
    exact absurd (MonoidHom.mem_range.mpr ⟨a, rfl⟩) hαout

private theorem lieModel_psl2_of_mulEquiv (e : K ≃* L2 F) {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hcard : Nat.card F = p ^ f) (h3 : 3 < p ^ f) :
    CFSG.Blueprint.LieModel K .PSL 2 p f := by
  refine Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], ?_⟩
  refine ⟨⟨hp, hf, le_rfl, ?_, ?_⟩, F, inferInstance, inferInstance, hcard, ⟨e⟩⟩
  · intro h
    have h2 : p ^ f = 2 := congrArg Prod.snd h
    omega
  · intro h
    have h2 : p ^ f = 3 := congrArg Prod.snd h
    omega

theorem innAut_le_gammaRk_two_of_card_eight (hF : L2Field F) (h9 : 9 < Nat.card F)
    (e : K ≃* L2 F)
    {A : Subgroup (MulAut K)} (hA : IsElemAbelian 2 A)
    (h8 : Nat.card A = 8) :
    innAut K ≤ gammaRk 2 A (innAut K ⊔ A) := by
  classical
  have : Finite K := Finite.of_injective (e : K → L2 F) e.injective
  obtain ⟨f, hf, hq⟩ := CFSG.ABGLocalTools.card_eq_ringChar_pow (F := F)
  have hp : Nat.Prime (ringChar F) := CFSG.ABGLocalTools.ringChar_prime
  have hpodd : Odd (ringChar F) := by
    have h1 : Odd (ringChar F ^ f) := by rw [← hq]; exact hF.1
    exact Odd.of_dvd_nat h1 (dvd_pow_self (ringChar F) (by omega))
  have hp2 : ringChar F ≠ 2 := by
    intro h
    rw [h] at hpodd
    exact (Nat.not_odd_iff_even.mpr even_two) hpodd
  have hpf9 : ringChar F ^ f ≠ 9 := by rw [← hq]; omega
  have hL : CFSG.Blueprint.LieModel K .PSL 2 (ringChar F) f :=
    lieModel_psl2_of_mulEquiv e hp hf hq (by rw [← hq]; omega)
  have hAsq : ∀ x ∈ A, x * x = 1 := fun x hx => by rw [← pow_two]; exact hA.2 x hx
  have hgen := CFSG.ComponentClassification.AutL2Facts.foote47FourgroupGeneration_psl2
    hp hp2 hf hpf9 hL A ⟨A, le_rfl, hAsq, h8⟩
  set Y : Subgroup (MulAut K) := innAut K ⊔ A with hYdef
  have hIY : innAut K ≤ Y := by rw [hYdef]; exact le_sup_left
  have hAY : A ≤ Y := by rw [hYdef]; exact le_sup_right
  set H : Subgroup K := (gammaRk 2 A Y).comap (MulAut.conj : K →* MulAut K) with hHdef
  have hHtop : H = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine iSup_le fun W => iSup_le fun hWk => iSup_le fun hWT => ?_
    intro x hx
    obtain ⟨F₀, hWF₀, hF₀A, -, hF₀8⟩ := hWT
    have hWA : W ≤ A := hWF₀.trans hF₀A
    have hW4 : 2 ^ 2 ≤ Nat.card ↥W := by rw [hWk.card_four]; norm_num
    have hfix : ∀ w ∈ W, w x = x := by
      intro w hw
      have h1 := hx
      rw [Subgroup.mem_iInf] at h1
      exact Subgroup.mem_iInf.mp (h1 w) hw
    simp only [hHdef, Subgroup.mem_comap]
    refine conj_mem_gammaRk_of_commute hIY hWA hW4 fun d hd => ?_
    have h0 : d * MulAut.conj x * d⁻¹ = MulAut.conj x := by
      rw [mulAut_conj_mul_conj, hfix d hd]
    calc MulAut.conj x * d = (d * MulAut.conj x * d⁻¹) * d := by rw [h0]
      _ = d * MulAut.conj x := by group
  rw [innAut, ← Subgroup.map_top (MulAut.conj : K →* MulAut K), Subgroup.map_le_iff_le_comap]
  rw [← hHdef, hHtop]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix
