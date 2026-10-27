module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootGroups
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderLinearBorel
public import Mathlib.LinearAlgebra.Projectivization.Cardinality

public section

namespace CFSG.Walter

open scoped MatrixGroups

section CharTwo

variable {K : Type*} [Field K] [CharP K 2]

theorem sl2_center_eq_bot_of_charTwo :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨c, hc, hcA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have hc1 : c = 1 := CharTwo.sq_injective (by simpa using hc)
  rw [Subgroup.mem_bot]
  ext i j
  rw [← hcA, hc1]
  simp [Matrix.one_apply]

theorem sl2_inv_eq_self_of_diag_eq (B : Matrix.SpecialLinearGroup (Fin 2) K)
    (h : B 0 0 = B 1 1) : B⁻¹ = B := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CharTwo.neg_eq, h]

theorem sl2_mul_self_eq_one_of_commute {A B : Matrix.SpecialLinearGroup (Fin 2) K}
    (hA1 : A ≠ 1) (hA2 : A * A = 1) (hAB : A * B = B * A) : B * B = 1 := by
  have hAinv : A⁻¹ = A := inv_eq_of_mul_eq_one_right hA2
  have hdiag : A 0 0 = A 1 1 := by
    have h := congrArg (fun C : Matrix.SpecialLinearGroup (Fin 2) K => C 0 0) hAinv
    simp only [Matrix.SpecialLinearGroup.SL2_inv_expl, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.empty_val', Matrix.cons_val_fin_one] at h
    exact h.symm
  have hoff : A 0 1 ≠ 0 ∨ A 1 0 ≠ 0 := by
    by_contra h
    push Not at h
    apply hA1
    have hdet : A 0 0 * A 1 1 = 1 := by
      have := A.2
      rw [Matrix.det_fin_two, h.1, h.2] at this
      simpa using this
    rw [← hdiag] at hdet
    have ha : A 0 0 = 1 := CharTwo.sq_injective (by simpa [sq] using hdet)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, ← hdiag, h.1, h.2]
  have h01 := congrArg (fun C : Matrix.SpecialLinearGroup (Fin 2) K => C 0 1) hAB
  have h10 := congrArg (fun C : Matrix.SpecialLinearGroup (Fin 2) K => C 1 0) hAB
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] at h01 h10
  rw [← hdiag] at h01 h10
  have hB : B 0 0 = B 1 1 := by
    rcases hoff with h | h
    · have : A 0 1 * B 1 1 = A 0 1 * B 0 0 := by linear_combination h01
      exact (mul_left_cancel₀ h this).symm
    · have : A 1 0 * B 0 0 = A 1 0 * B 1 1 := by linear_combination h10
      exact mul_left_cancel₀ h this
  calc B * B = B⁻¹ * B := by rw [sl2_inv_eq_self_of_diag_eq B hB]
    _ = 1 := inv_mul_cancel B

noncomputable def psl2MulEquivSL2OfCharTwo :
    PSL(2, K) ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
  (QuotientGroup.quotientMulEquivOfEq sl2_center_eq_bot_of_charTwo).trans
    QuotientGroup.quotientBot

theorem psl2_sq_eq_one_of_mem_centralizer_of_charTwo {t x : PSL(2, K)} (ht : orderOf t = 2)
    (hx : x ∈ Subgroup.centralizer ({t} : Set PSL(2, K))) : x ^ 2 = 1 := by
  set e := psl2MulEquivSL2OfCharTwo (K := K)
  have ht1 : e t ≠ 1 := by
    intro h
    rw [map_eq_one_iff _ e.injective] at h
    rw [h, orderOf_one] at ht
    omega
  have ht2 : e t * e t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht] at h
    rw [← map_mul, ← pow_two, h, map_one]
  have hcomm : e t * e x = e x * e t := by
    rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_singleton_iff.mp hx).symm]
  apply e.injective
  rw [map_pow, map_one, pow_two]
  exact sl2_mul_self_eq_one_of_commute ht1 ht2 hcomm

theorem psl2_centralizer_isPGroup_of_charTwo {t : PSL(2, K)} (ht : orderOf t = 2) :
    IsPGroup 2 (Subgroup.centralizer ({t} : Set PSL(2, K))) := fun x =>
  ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact psl2_sq_eq_one_of_mem_centralizer_of_charTwo ht x.2)⟩

end CharTwo

section Even

variable {f : ℕ}

theorem psl2_even_card (hf : f ≠ 0) :
    Nat.card PSL(2, GaloisField 2 f) = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
  rw [Nat.card_congr (psl2MulEquivSL2OfCharTwo (K := GaloisField 2 f)).toEquiv,
    GorensteinWalter.sl2_card_formula, GaloisField.card 2 f hf]

theorem psl2_even_card_sylow (hf : f ≠ 0) :
    Nat.card (Sylow 2 PSL(2, GaloisField 2 f)) = 2 ^ f + 1 := by
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f hf
  rw [← Nat.card_congr (GorensteinWalter.psl2ProjectiveLineEquivSylow _ hK),
    GorensteinWalter.PSL2ProjectiveLine,
    Projectivization.card_of_finrank_two _ _ (by simp), hK]

theorem psl2_even_card_normalizer_sylow_two (hf : f ≠ 0) (U : Sylow 2 PSL(2, GaloisField 2 f)) :
    Nat.card (Subgroup.normalizer ((U : Subgroup PSL(2, GaloisField 2 f)) :
      Set PSL(2, GaloisField 2 f))) = 2 ^ f * (2 ^ f - 1) := by
  have h := (Subgroup.normalizer ((U : Subgroup PSL(2, GaloisField 2 f)) :
    Set PSL(2, GaloisField 2 f))).index_mul_card
  have hidx : Nat.card (Sylow 2 PSL(2, GaloisField 2 f)) = (Subgroup.normalizer
      ((U : Subgroup PSL(2, GaloisField 2 f)) : Set PSL(2, GaloisField 2 f))).index :=
    U.card_eq_index_normalizer
  rw [← hidx, psl2_even_card_sylow hf, psl2_even_card hf] at h
  have hq : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
    rw [← Nat.sq_sub_sq, one_pow]
  rw [this] at h
  have h' : (2 ^ f + 1) * Nat.card (Subgroup.normalizer ((U : Subgroup PSL(2, GaloisField 2 f)) :
      Set PSL(2, GaloisField 2 f))) = (2 ^ f + 1) * (2 ^ f * (2 ^ f - 1)) := by
    rw [h]
    ring
  exact Nat.eq_of_mul_eq_mul_left (by omega) h'

theorem psl2_even_sylow_two (hf : 2 ≤ f) (U : Sylow 2 PSL(2, GaloisField 2 f)) :
    IsElementaryAbelian 2 (U : Subgroup PSL(2, GaloisField 2 f)) ∧
      Nat.card (U : Subgroup PSL(2, GaloisField 2 f)) = 2 ^ f := by
  obtain ⟨-, -, hZexp, hZcard, hUcard⟩ := CFSG.Open.bender_psl2_borel_full f hf U
  rw [pow_one] at hUcard
  set Ug := (U : Subgroup PSL(2, GaloisField 2 f))
  have hZ : Subgroup.center Ug = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (hZcard.trans hUcard.symm)
  have hcomm : IsMulCommutative Ug := ⟨⟨fun a b =>
    (Subgroup.mem_center_iff.mp (hZ ▸ Subgroup.mem_top b) a)⟩⟩
  refine ⟨{ toIsMulCommutative := hcomm, exponent_dvd_p := ?_ }, hUcard⟩
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  intro g
  exact hZexp g (hZ ▸ Subgroup.mem_top g)

theorem psl2_even_normalizer_sylow_two (hf : 2 ≤ f) (U : Sylow 2 PSL(2, GaloisField 2 f)) :
    ∃ D : Subgroup PSL(2, GaloisField 2 f), IsCyclic D ∧ Nat.card D = 2 ^ f - 1 ∧
      (U : Subgroup PSL(2, GaloisField 2 f)) ⊓ D = ⊥ ∧
      (U : Subgroup PSL(2, GaloisField 2 f)) ⊔ D = Subgroup.normalizer
        ((U : Subgroup PSL(2, GaloisField 2 f)) : Set PSL(2, GaloisField 2 f)) ∧
      ∀ x ∈ (U : Subgroup PSL(2, GaloisField 2 f)), x ≠ 1 →
        ∀ y ∈ (U : Subgroup PSL(2, GaloisField 2 f)), y ≠ 1 →
          ∃! d : D, (d : PSL(2, GaloisField 2 f)) * x * (d : PSL(2, GaloisField 2 f))⁻¹ = y := by
  classical
  set L := PSL(2, GaloisField 2 f)
  set Ug := (U : Subgroup L) with hUg
  obtain ⟨-, ⟨D, hDcyc, hDodd, hUD, hsup⟩, -, -, -⟩ := CFSG.Open.bender_psl2_borel_full f hf U
  obtain ⟨hUel, hUcard⟩ := psl2_even_sylow_two hf U
  have hN := psl2_even_card_normalizer_sylow_two (by omega) U
  have hDN : D ≤ Subgroup.normalizer (Ug : Set L) := hsup ▸ le_sup_right
  have hq : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  set T : Set L := {u | u ∈ Ug ∧ u ≠ 1} with hT
  have hTcard : Nat.card T = 2 ^ f - 1 := by
    have : T = (Ug : Set L) \ {1} := by ext; simp [hT]
    rw [Nat.card_coe_set_eq, this, Set.ncard_sdiff_singleton_of_mem (Ug.one_mem),
      ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hUcard]
  have hfree : ∀ x ∈ Ug, x ≠ 1 → ∀ d ∈ D, d * x * d⁻¹ = x → d = 1 := by
    intro x hx hx1 d hd hdx
    have hxo : orderOf x = 2 :=
      orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := Ug) x hx) hx1
    have hdC : d ∈ Subgroup.centralizer ({x} : Set L) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc d * x = (d * x * d⁻¹) * d := by group
        _ = x * d := by rw [hdx]
    have hd2 := psl2_sq_eq_one_of_mem_centralizer_of_charTwo hxo hdC
    have hdodd : Odd (orderOf d) := Odd.of_dvd_nat hDodd (Subgroup.orderOf_dvd_natCard D hd)
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hd2) with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at hdodd
      exact absurd hdodd (by decide)
  let φ : ∀ x ∈ Ug, x ≠ 1 → D → T := fun x hx hx1 d =>
    ⟨d * x * (d : L)⁻¹, Subgroup.mem_normalizer_iff.mp (hDN d.2) x |>.mp hx, fun h => hx1 (by
      calc x = (d : L)⁻¹ * (d * x * (d : L)⁻¹) * d := by group
        _ = 1 := by rw [h]; group)⟩
  have hφinj : ∀ x (hx : x ∈ Ug) (hx1 : x ≠ 1), Function.Injective (φ x hx hx1) := by
    intro x hx hx1 d₁ d₂ h
    have h' : (d₁ : L) * x * (d₁ : L)⁻¹ = d₂ * x * (d₂ : L)⁻¹ := congrArg Subtype.val h
    have h1 := hfree x hx hx1 ((d₂ : L)⁻¹ * d₁) (D.mul_mem (D.inv_mem d₂.2) d₁.2) (by
      calc (d₂ : L)⁻¹ * d₁ * x * ((d₂ : L)⁻¹ * d₁)⁻¹
          = (d₂ : L)⁻¹ * ((d₁ : L) * x * (d₁ : L)⁻¹) * d₂ := by group
        _ = x := by rw [h']; group)
    apply Subtype.ext
    rw [inv_mul_eq_one] at h1
    exact h1.symm
  obtain ⟨x0, hx0, hx01⟩ : ∃ x0 ∈ Ug, x0 ≠ 1 := by
    by_contra h
    push Not at h
    have : Ug = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr h
    have hUcard' : Nat.card Ug = 2 ^ f := hUcard
    rw [this, Subgroup.card_bot] at hUcard'
    omega
  have hDle : Nat.card D ≤ 2 ^ f - 1 :=
    hTcard ▸ Nat.card_le_card_of_injective _ (hφinj x0 hx0 hx01)
  have hDge : 2 ^ f - 1 ≤ Nat.card D := by
    have h1 : Nat.card (Subgroup.normalizer (Ug : Set L)) ≤ Nat.card Ug * Nat.card D := by
      rw [← hsup]
      change Nat.card ((Ug ⊔ D : Subgroup L) : Set L) ≤ _
      rw [Subgroup.coe_mul_of_right_le_normalizer_left Ug D hDN]
      exact Set.natCard_mul_le
    rw [hN, hUcard] at h1
    exact Nat.le_of_mul_le_mul_left h1 (by omega)
  have hDcard : Nat.card D = 2 ^ f - 1 := le_antisymm hDle hDge
  refine ⟨D, hDcyc, hDcard, hUD, hsup, fun x hx hx1 y hy hy1 => ?_⟩
  have hbij : Function.Bijective (φ x hx hx1) :=
    (hφinj x hx hx1).bijective_of_nat_card_le (by rw [hTcard, hDcard])
  obtain ⟨d, hd⟩ := hbij.2 ⟨y, hy, hy1⟩
  refine ⟨d, congrArg Subtype.val hd, fun d' hd' => hφinj x hx hx1 ?_⟩
  rw [hd]
  exact Subtype.ext hd'

theorem psl2_even_centralizer_involution (hf : 2 ≤ f) (U : Sylow 2 PSL(2, GaloisField 2 f))
    {t : PSL(2, GaloisField 2 f)} (htU : t ∈ (U : Subgroup PSL(2, GaloisField 2 f)))
    (ht : t ≠ 1) :
    Subgroup.centralizer ({t} : Set PSL(2, GaloisField 2 f)) = U := by
  obtain ⟨hUel, -⟩ := psl2_even_sylow_two hf U
  have hto : orderOf t = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 2)
      (A := (U : Subgroup PSL(2, GaloisField 2 f))) t htU) ht
  refine U.is_maximal' (psl2_centralizer_isPGroup_of_charTwo hto) fun u hu => ?_
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact congrArg Subtype.val (hUel.toIsMulCommutative.is_comm.comm ⟨u, hu⟩ ⟨t, htU⟩)

theorem psl2_even_isConj_of_orderOf_eq_two (hf : 2 ≤ f) {x y : PSL(2, GaloisField 2 f)}
    (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y := by
  have hxp : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  have hyp : IsPGroup 2 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  obtain ⟨Sx, hSx⟩ := hxp.exists_le_sylow
  obtain ⟨Sy, hSy⟩ := hyp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq PSL(2, GaloisField 2 f) Sx Sy
  have hxS : x ∈ (Sx : Subgroup PSL(2, GaloisField 2 f)) := hSx (Subgroup.mem_zpowers x)
  have hyS : y ∈ ((g • Sx : Sylow 2 PSL(2, GaloisField 2 f)) :
      Subgroup PSL(2, GaloisField 2 f)) := hg ▸ hSy (Subgroup.mem_zpowers y)
  have hy' : g⁻¹ * y * g ∈ (Sx : Subgroup PSL(2, GaloisField 2 f)) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hyS
    simpa [MulAut.smul_def, MulAut.conj_apply] using hyS
  have hx1 : x ≠ 1 := by rintro rfl; simp at hx
  have hy1 : g⁻¹ * y * g ≠ 1 := by
    intro h
    apply (show y ≠ 1 by rintro rfl; simp at hy)
    calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  obtain ⟨D, -, -, -, -, hreg⟩ := psl2_even_normalizer_sylow_two hf Sx
  obtain ⟨d, hd, -⟩ := hreg x hxS hx1 _ hy' hy1
  set dd : PSL(2, GaloisField 2 f) := (d : PSL(2, GaloisField 2 f)) with hdd
  refine isConj_iff.mpr ⟨g * dd, ?_⟩
  calc g * dd * x * (g * dd)⁻¹ = g * (dd * x * dd⁻¹) * g⁻¹ := by group
    _ = g * (g⁻¹ * y * g) * g⁻¹ := by rw [hd]
    _ = y := by group

end Even

end CFSG.Walter
