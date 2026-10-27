module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKSymplectic
public import CFSG.LocalAnalysis.WeakClosure81.SevenKUnitary
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenCls
import CFSG.OddTranspositions.PartFour.Fourteen.OrthE5
import CFSG.OddTranspositions.PartFour.SpLineCount
import CFSG.ClassicalGroups.Alternating.I4SpInvolBlock
import CFSG.OddTranspositions.PartFour.Fourteen.UnitaryShapeRigid
import CFSG.OddTranspositions.PartFour.UnitaryClass
import CFSG.GroupTheory.SwapMulOrder
import CFSG.LocalAnalysis.WeakClosure81.SpUFixFactSpPerp
import CFSG.LocalAnalysis.WeakClosure81.SpUFixFactUPerp
public import CFSG.ClassicalGroups.Alternating.PointRadicalFixedCard
public import CFSG.Fischer.Classification.Unitary.Model
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenSymplectic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Glue
public import CFSG.Timmesfeld.Orders.Classical
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.WeakClosure81.CoreRadical

open CFSG.Open CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.OddTranspositions.PartFour
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ClassicalGroups.Unitary QuadraticMap
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary
open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpFull
open CFSG.ClassicalGroups.Alternating

variable {Y : Type} [Group Y] {t : Y}

private theorem spUFixGspHomSp_spTransvection (k : ℕ) (F : Type) [Field F]
    (u : Fin k ⊕ Fin k → F) (c : F) :
    spUFixGspHomSp k F (spTransvection u c) = Tsp spForm_isAlt u c := by
  apply Subtype.ext
  exact spLin_spTransvection u c

private theorem orderOf_spTransvection_mul_mem_one {k : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) {a b : Fin k ⊕ Fin k → F} {c : F} (hc : c ≠ 0) :
    orderOf (spTransvection a c * spTransvection b c) ∈ ({1, 2, 3} : Set ℕ) := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 :=
    CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (f := 1) (by simpa using hF)
  have hc1 : c = 1 := by
    rcases EvenCatalog.eq_zero_or_eq_one_of_card_eq_two hF c with h | h
    · exact absurd h hc
    · exact h
  subst hc1
  have hsq : ∀ u : Fin k ⊕ Fin k → F, spTransvection u (1 : F) * spTransvection u 1 = 1 := by
    intro u
    apply spUFixGspHomSp_injective
    rw [map_mul, map_one]
    simp only [spUFixGspHomSp_spTransvection, Tsp_mul_self]
  by_cases hzero : spForm k F a b = 0
  · have hcomm : Commute (spTransvection a 1) (spTransvection b 1) := by
      apply spUFixGspHomSp_injective
      rw [map_mul, map_mul]
      simp only [spUFixGspHomSp_spTransvection]
      exact Tsp_comm spForm_isAlt hzero 1 1
    have h2 : (spTransvection a 1 * spTransvection b 1) ^ 2 = 1 :=
      CFSG.Fischer.Classification.Unitary.mul_sq_eq_one_of_commute (hsq a) (hsq b) hcomm.eq
    have hdvd := orderOf_dvd_of_pow_eq_one h2
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · rw [h]; simp
    · rw [h]; simp
  · have hB1 : spForm k F a b = 1 := by
      rcases EvenCatalog.eq_zero_or_eq_one_of_card_eq_two hF (spForm k F a b) with h | h
      · exact absurd h hzero
      · exact h
    have h1 : orderOf (spUFixGspHomSp k F (spTransvection a 1 * spTransvection b 1)) = 3 := by
      have hT := orderOf_Tsp_mul_Tsp (spForm_isAlt (r := k) (K := F)) (a := a) (b := b)
        (by rw [hB1]; exact one_ne_zero)
      rw [hB1] at hT
      simpa [map_mul, spUFixGspHomSp_spTransvection] using hT
    have hord : orderOf (spTransvection a 1 * spTransvection b 1) =
        orderOf (spUFixGspHomSp k F (spTransvection a 1 * spTransvection b 1)) :=
      (orderOf_injective (spUFixGspHomSp k F) spUFixGspHomSp_injective
        (spTransvection a 1 * spTransvection b 1)).symm
    rw [hord, h1]
    simp

private theorem suTv_mul_self_one {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} {m : ℕ}
    (hσ : IsUnitaryInvolution σ) {a : Fin m → F} (ha : herm σ a a = 0)
    (h1 : (1 : F) + σ 1 = 0) : suTv hσ a 1 * suTv hσ a 1 = 1 := by
  apply ext_smul
  intro v
  rw [spUFix_suTv_mul_apply hσ ha ha h1 h1, one_smul]
  simp only [ha, mul_zero, add_zero, one_mul, zero_mul]
  rw [add_assoc, ← add_smul, CharTwo.add_self_eq_zero (herm σ a v), zero_smul, add_zero]

private theorem suTv_mul_comm_of_herm_eq_zero {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}
    (hσ : IsUnitaryInvolution σ) {a b : Fin m → F} (ha : herm σ a a = 0)
    (hb : herm σ b b = 0) (h1 : (1 : F) + σ 1 = 0) (hab : herm σ a b = 0) :
    suTv hσ a 1 * suTv hσ b 1 = suTv hσ b 1 * suTv hσ a 1 := by
  have hba : herm σ b a = 0 := herm_eq_zero_comm σ hσ.invol hab
  apply ext_smul
  intro v
  rw [mul_smul, mul_smul, suTv_smul hσ hb h1, suTv_smul hσ ha h1,
    suTv_smul hσ ha h1, suTv_smul hσ hb h1]
  simp [herm_add_right, herm_smul_right, hab, hba]
  abel

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

private theorem suTv_mul_ne_one {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} {m : ℕ}
    (hσ : IsUnitaryInvolution σ) {a b : Fin m → F} (ha : herm σ a a = 0)
    (hb : herm σ b b = 0) (h1 : (1 : F) + σ 1 = 0) {γ : F}
    (hγ : herm σ a b = γ) (hγ0 : γ ≠ 0) :
    suTv hσ a 1 * suTv hσ b 1 ≠ 1 := by
  intro h
  have hza : (suTv hσ a 1 * suTv hσ b 1) • a = a := by rw [h, one_smul]
  have hba : herm σ b a = σ γ := by
    rw [← hγ, herm_conj σ hσ.invol]
  have hstep : (suTv hσ a 1 * suTv hσ b 1) • a =
      a + (σ γ) • b + (σ γ * γ) • a := by
    rw [mul_smul, suTv_smul hσ hb h1, suTv_smul hσ ha h1]
    simp [herm_add_right, herm_smul_right, ha, hγ, hba]
  rw [hza] at hstep
  have hsum : (σ γ) • b + (σ γ * γ) • a = 0 := by
    have h' : a + ((σ γ) • b + (σ γ * γ) • a) = a + 0 := by
      rw [add_zero]
      simpa [add_assoc] using hstep.symm
    exact add_left_cancel h'
  have hσγ : σ γ ≠ 0 := fun h0 => hγ0 (σ.injective (by rw [h0, map_zero]))
  have hb0 : b + γ • a = 0 := by
    have := congrArg (fun w => (σ γ)⁻¹ • w) hsum
    have hcoef : (σ γ)⁻¹ * (σ γ * γ) = γ := by
      rw [← mul_assoc, inv_mul_cancel₀ hσγ, one_mul]
    have hcoefb : (σ γ)⁻¹ * σ γ = 1 := inv_mul_cancel₀ hσγ
    simpa [smul_add, smul_smul, hcoef, hcoefb] using this
  have hb_eq : b = γ • a := by
    have hneg : b = -(γ • a) := eq_neg_of_add_eq_zero_left hb0
    rw [← neg_smul, CharTwo.neg_eq] at hneg
    exact hneg
  apply hγ0
  rw [← hγ, hb_eq, herm_smul_right, ha, mul_zero]

private theorem orderOf_suTv_mul_mem_of_card_four {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2 ^ 2) (hσ : IsUnitaryInvolution (unitaryInvolution F 2 1))
    {m : ℕ} {a b : Fin m → F}
    (ha : herm (unitaryInvolution F 2 1) a a = 0)
    (hb : herm (unitaryInvolution F 2 1) b b = 0) :
    orderOf (suTv hσ a 1 * suTv hσ b 1) ∈ ({1, 2, 3} : Set ℕ) := by
  let : Fintype F := Fintype.ofFinite F
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : (1 : F) + unitaryInvolution F 2 1 1 = 0 := by
    rw [map_one]
    exact CharTwo.add_self_eq_zero 1
  have hcard : Fintype.card F = 4 := by
    rw [← Nat.card_eq_fintype_card]
    norm_num at hF ⊢
    exact hF
  by_cases hzero : herm (unitaryInvolution F 2 1) a b = 0
  · have hcomm := suTv_mul_comm_of_herm_eq_zero hσ ha hb h1 hzero
    have h2 : (suTv hσ a 1 * suTv hσ b 1) ^ 2 = 1 :=
      CFSG.Fischer.Classification.Unitary.mul_sq_eq_one_of_commute
        (suTv_mul_self_one hσ ha h1) (suTv_mul_self_one hσ hb h1) hcomm
    have hdvd := orderOf_dvd_of_pow_eq_one h2
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · rw [h]; simp
    · rw [h]; simp
  · set γ : F := herm (unitaryInvolution F 2 1) a b with hγdef
    have hγ : herm (unitaryInvolution F 2 1) a b = γ := rfl
    have hγ0 : γ ≠ 0 := by rw [hγdef]; exact hzero
    have hσγ : unitaryInvolution F 2 1 γ = γ ^ 2 := by
      have := CFSG.LieType.BorelTits.unitaryInvolution_apply (K := F) 2 1 γ
      simpa using this
    have hγ3 : γ ^ 3 = 1 := by
      have := FiniteField.pow_card_sub_one_eq_one (K := F) γ hγ0
      rwa [hcard] at this
    have hnorm : γ * unitaryInvolution F 2 1 γ = 1 := by
      rw [hσγ]
      calc γ * γ ^ 2 = γ ^ 3 := by ring
        _ = 1 := hγ3
    have hLd : (1 : F) * γ * unitaryInvolution F 2 1 γ = 1 := by simpa using hnorm
    have hcube : (suTv hσ a 1 * suTv hσ b 1) ^ 3 = 1 :=
      spUFix_suTv_mul_pow_three hσ ha hb h1 h1 hLd
    have hne : suTv hσ a 1 *
        suTv hσ b 1 ≠ 1 :=
      suTv_mul_ne_one hσ ha hb h1 hγ hγ0
    have h3 : orderOf (suTv hσ a 1 * suTv hσ b 1) = 3 :=
      orderOf_eq_prime hcube hne
    rw [h3]; simp

theorem threeTransp_of_isOrthReflection_one (hZ : Subgroup.center Y = ⊥) {m : ℕ}
    (h : IsOrthReflection Y m 1 t) :
    ∀ d e : Y, IsConj t d → IsConj t e → orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ) := by
  obtain ⟨K, hKfield, hKfintype, hKchar, Q, ψ, v, hcard, hQ, hψ, hrange, hv, hψt,
    hrefl⟩ := exists_symmetry_model_of_isOrthReflection hZ h
  let : Field K := hKfield
  let : Fintype K := hKfintype
  let : CharP K 2 := hKchar
  have hK2 : Fintype.card K = 2 := by simpa using hcard
  have hKnat : Nat.card K = 2 := Nat.card_eq_fintype_card.trans hK2
  have hplane : orderOf (planeMat (1 : K)) = 3 := by
    obtain ⟨γ, hγ0, hγord⟩ := exists_planeMat_orderOf (K := K)
    have hγ1 : γ = 1 := by
      rcases EvenCatalog.eq_zero_or_eq_one_of_card_eq_two hKnat γ with h | h
      · exact absurd h hγ0
      · exact h
    rw [hγ1, hKnat] at hγord
    omega
  intro d e hd he
  obtain ⟨x, hx, hψd⟩ := exists_vec_of_isConj hrange hv hψt hd
  obtain ⟨y, hy, hψe⟩ := exists_vec_of_isConj hrange hv hψt he
  have hord : orderOf (d * e) = orderOf (ψ d * ψ e) := by
    rw [← map_mul]
    exact (orderOf_injective ψ hψ (d * e)).symm
  rw [hord, hψd, hψe]
  by_cases hcomm : Commute d e
  · have hcomm' : Commute (symmetryGL Q x) (symmetryGL Q y) := by
      rw [← hψd, ← hψe]
      exact hcomm.map ψ
    have h2 : (symmetryGL Q x * symmetryGL Q y) ^ 2 = 1 :=
      CFSG.Fischer.Classification.Unitary.mul_sq_eq_one_of_commute
        (symmetryGL_mul_self Q x) (symmetryGL_mul_self Q y) hcomm'.eq
    have hdvd := orderOf_dvd_of_pow_eq_one h2
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · rw [h]; simp
    · rw [h]; simp
  · have hxy : polar Q x y ≠ 0 := fun h0 =>
      hcomm ((commute_iff_of_symmetryGL hQ hψ hx hy hψd hψe).mpr h0)
    have hγ : polar Q x y = 1 := by
      rcases EvenCatalog.eq_zero_or_eq_one_of_card_eq_two hKnat (polar Q x y) with h | h
      · exact absurd h hxy
      · exact h
    have hm : orderOf (symmetryGL Q x * symmetryGL Q y) = orderOf (planeMat (1 : K)) :=
      orderOf_eq_orderOf_iff.2 (pow_symmetryGL_mul_eq_one_iff hx hy one_ne_zero hγ)
    rw [hm, hplane]
    simp

theorem threeTransp_of_isSymTransposition (hO : fusionOddCore Y = ⊥) {n : ℕ}
    (h : IsSymTransposition Y n t) :
    ∀ d e : Y, IsConj t d → IsConj t e → orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ) := by
  obtain ⟨e, heswap⟩ := h
  let ψ : Y ≃* Y ⧸ fusionOddCore Y :=
    (QuotientGroup.quotientBot (G := Y)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hO.symm)
  have hψ : ∀ x : Y, ψ x = QuotientGroup.mk x := by intro x; simp [ψ]
  let φ : Y ≃* Equiv.Perm (Fin n) := ψ.trans e
  have hφt : (φ t).IsSwap := by simpa [φ, hψ] using heswap
  intro d e hd he
  have hd' : (φ d).IsSwap := by
    obtain ⟨g, hg⟩ := isConj_iff.1 (MonoidHom.map_isConj φ.toMonoidHom hd)
    have hgd : φ d = g * φ t * g⁻¹ := hg.symm
    rw [hgd]
    obtain ⟨a, b, hab, hsw⟩ := hφt
    rw [hsw]
    exact ⟨g a, g b, g.injective.ne hab, by rw [Equiv.swap_apply_apply]⟩
  have he' : (φ e).IsSwap := by
    obtain ⟨g, hg⟩ := isConj_iff.1 (MonoidHom.map_isConj φ.toMonoidHom he)
    have hge : φ e = g * φ t * g⁻¹ := hg.symm
    rw [hge]
    obtain ⟨a, b, hab, hsw⟩ := hφt
    rw [hsw]
    exact ⟨g a, g b, g.injective.ne hab, by rw [Equiv.swap_apply_apply]⟩
  have hord : orderOf (d * e) = orderOf (φ d * φ e) := by
    rw [← map_mul]
    exact (orderOf_injective φ.toMonoidHom φ.injective (d * e)).symm
  rw [hord]
  exact CFSG.GroupTheory.orderOf_mul_mem_of_isSwap hd' he'

theorem false_of_isOrth63Reflection (hZ : Subgroup.center Y = ⊥) (h : IsOrth63Reflection Y t) :
    False := by
  obtain ⟨F, _hF, _hFin, _hcard, b, c, _hbc, N, _hN1, _hN2, φ, _hφ, hker, hkerle, r, _hr,
    _hrk, _hφt⟩ := h
  have hbot : φ.ker = ⊥ := le_bot_iff.mp (hkerle.trans (le_of_eq hZ))
  rw [hbot] at hker
  simp at hker

theorem threeTransp_of_isSymplecticTransvection_one (hZ : Subgroup.center Y = ⊥) {m : ℕ}
    (h : IsSymplecticTransvection Y m 1 t) :
    ∀ d e : Y, IsConj t d → IsConj t e → orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ) := by
  obtain ⟨k, hm, F, hFfield, hFfin, hFcard, e, he⟩ := h
  let : Field F := hFfield
  let : Finite F := hFfin
  let φ : Y ≃* ↥(StatedSp k F) :=
    (CFSG.QuasithinUnique.Ch1.mulEquivQuotientOfCenterEqBot hZ).trans e
  have hφt : φ t = e (QuotientGroup.mk t) := by
    simp [φ, CFSG.QuasithinUnique.Ch1.mulEquivQuotientOfCenterEqBot_apply]
  obtain ⟨a₀, c, ha₀, hc, htrans⟩ := borel86_spn_eq_spTransvection he
  have hφtrans : φ t = spTransvection a₀ c := by rw [hφt, htrans]
  have hF2 : Nat.card F = 2 := by simpa using hFcard
  intro d ee hd hee
  have hd' : IsConj (spTransvection a₀ c) (φ d) := by
    have h' : IsConj (φ t) (φ d) := MonoidHom.map_isConj φ.toMonoidHom hd
    rwa [hφtrans] at h'
  have he' : IsConj (spTransvection a₀ c) (φ ee) := by
    have h' : IsConj (φ t) (φ ee) := MonoidHom.map_isConj φ.toMonoidHom hee
    rwa [hφtrans] at h'
  have hd'' : φ d ∈ {x | IsConj (spTransvection a₀ c) x} := hd'
  rw [setOf_isConj_spTransvection ha₀ c] at hd''
  have he'' : φ ee ∈ {x | IsConj (spTransvection a₀ c) x} := he'
  rw [setOf_isConj_spTransvection ha₀ c] at he''
  obtain ⟨b, hb, hφd⟩ := hd''
  obtain ⟨b', hb', hφe⟩ := he''
  have hord : orderOf (d * ee) = orderOf (φ d * φ ee) := by
    rw [← map_mul]
    exact (orderOf_injective φ.toMonoidHom φ.injective (d * ee)).symm
  rw [hord, hφd, hφe]
  exact orderOf_spTransvection_mul_mem_one hF2 hc

theorem threeTransp_of_isUnitaryTransvection_one (hZ : Subgroup.center Y = ⊥) {m : ℕ}
    (h : IsUnitaryTransvection Y m 1 t) :
    ∀ d e : Y, IsConj t d → IsConj t e → orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ) := by
  obtain ⟨K, hKfield, hKfinite, hKchar, hKcard, φ, e₀, he₀0, he₀, hφt⟩ :=
    exists_mulEquiv_of_isUnitaryTransvection hZ h
  let : Field K := hKfield
  let : Finite K := hKfinite
  let : CharP K 2 := hKchar
  have hσ : IsUnitaryInvolution (unitaryInvolution K 2 1) :=
    isUnitaryInvolution_unitaryInvolution (K := K) (p := 2) (f := 1) (by simpa using hKcard)
  have hm2 : 2 ≤ m := suConf_two_le he₀0 he₀
  rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | hm3
  · exact threeTransp_of_isSymplecticTransvection_one hZ
      (isSymplecticTransvection_of_isUnitaryTransvection_two h)
  intro d e hd he
  have hd' : IsConj (kFactsSuProjTv hKcard m e₀ 1) (φ d) := by
    have h' : IsConj (φ t) (φ d) := MonoidHom.map_isConj φ.toMonoidHom hd
    rwa [hφt] at h'
  have he' : IsConj (kFactsSuProjTv hKcard m e₀ 1) (φ e) := by
    have h' : IsConj (φ t) (φ e) := MonoidHom.map_isConj φ.toMonoidHom he
    rwa [hφt] at h'
  have hdmem : φ d ∈ {y | ∃ c, c ≠ 0 ∧ herm (unitaryInvolution K 2 1) c c = 0 ∧
      y = kFactsSuProjTv hKcard m c 1} := by
    rw [← setOf_isConj_kFactsSuProjTv hKcard hm3 he₀0 he₀]
    exact hd'
  have hemem : φ e ∈ {y | ∃ c, c ≠ 0 ∧ herm (unitaryInvolution K 2 1) c c = 0 ∧
      y = kFactsSuProjTv hKcard m c 1} := by
    rw [← setOf_isConj_kFactsSuProjTv hKcard hm3 he₀0 he₀]
    exact he'
  obtain ⟨c, hc0, hc, hφd⟩ := hdmem
  obtain ⟨c', hc'0, hc', hφe⟩ := hemem
  let D : ↥(SUid (unitaryInvolution K 2 1) m) := suTv hσ c 1
  let E : ↥(SUid (unitaryInvolution K 2 1) m) := suTv hσ c' 1
  have hφd' : φ d = kFactsSuProj hKcard m D := by rw [hφd]; rfl
  have hφe' : φ e = kFactsSuProj hKcard m E := by rw [hφe]; rfl
  have hord : orderOf (d * e) = orderOf (φ d * φ e) := by
    rw [← map_mul]
    exact (orderOf_injective φ.toMonoidHom φ.injective (d * e)).symm
  rw [hord, hφd', hφe', ← map_mul]
  have hDE : orderOf (D * E) ∈ ({1, 2, 3} : Set ℕ) :=
    orderOf_suTv_mul_mem_of_card_four hKcard hσ hc hc'
  have hdvd : orderOf (kFactsSuProj hKcard m (D * E)) ∣ orderOf (D * E) :=
    orderOf_map_dvd (kFactsSuProj hKcard m) (D * E)
  rcases hDE with h | h | h
  · rw [h] at hdvd
    have h1 := Nat.dvd_one.mp hdvd
    rw [h1]; simp
  · rw [h] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h1 <;> rw [h1] <;> simp
  · rw [h] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h1 <;> rw [h1] <;> simp

end CFSG.LocalAnalysis.WeakClosure81.CoreRadical
