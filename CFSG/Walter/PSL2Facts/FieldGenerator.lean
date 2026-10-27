module

public import CFSG.Walter.PSL2Facts.TwoGroupBorel
public import CFSG.Quasithin.Background.F918Z4bAut

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter CFSG.ASVolI CFSG.SeitzReduction.LinearPilot
open CFSG.Quasithin CFSG.GroupTheory CFSG.ComponentClassification.CatalogueSchreierLinearTwo

variable {K : Type} [Field K] [Finite K]

theorem psl2FieldPart_eq_autFieldPart : psl2FieldPart K = CFSG.Quasithin.autFieldPart K := rfl

private theorem zpowers_psl2FieldPart_eq_top {a : ℕ} (hK : Nat.card K = 2 ^ a)
    {σ₀ : K ≃+* K} (hσ₀ : orderOf σ₀ = a) : Subgroup.zpowers σ₀ = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (RingAut K) :=
    Finite.of_injective (fun e : RingAut K => (e : K → K))
      (fun _ _ h => RingEquiv.ext (congrFun h))
  obtain ⟨hAut, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K hK
  refine Subgroup.eq_top_of_card_eq (H := Subgroup.zpowers σ₀) ?_
  rw [Nat.card_zpowers, hσ₀, hAut]

theorem orderOf_psl2FieldPart_eq_of_pow_not_inner {a e : ℕ} (hK : Nat.card K = 2 ^ a)
    (ha : a = 2 ^ e) (he : 1 ≤ e) {θ₀ : MulAut (PSL2 K)}
    (hout : ∀ x : PSL2 K, θ₀ ^ (2 ^ (e - 1)) ≠ MulAut.conj x) :
    orderOf (psl2FieldPart K θ₀) = a := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (by
    rw [← Nat.card_eq_fintype_card]; exact hK)
  haveI : Finite (RingAut K) :=
    Finite.of_injective (fun e : RingAut K => (e : K → K))
      (fun _ _ h => RingEquiv.ext (congrFun h))
  obtain ⟨hAut, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K hK
  set σ₀ : K ≃+* K := psl2FieldPart K θ₀
  have hdvd : orderOf σ₀ ∣ a := by rw [← hAut]; exact orderOf_dvd_natCard σ₀
  have hnotdvd : ¬ orderOf σ₀ ∣ 2 ^ (e - 1) := by
    intro hd
    have hσpow : σ₀ ^ (2 ^ (e - 1)) = 1 :=
      (orderOf_dvd_iff_pow_eq_one).mp hd
    have hfield : psl2FieldPart K (θ₀ ^ (2 ^ (e - 1))) = 1 := by
      rw [map_pow]
      exact hσpow
    rw [psl2FieldPart_eq_autFieldPart] at hfield
    obtain ⟨x, hx⟩ := CFSG.Quasithin.exists_conj_of_autFieldPart_eq_one hfield
    exact hout x hx
  rw [ha] at hdvd
  rcases (Nat.dvd_prime_pow Nat.prime_two).mp hdvd with ⟨i, hi, hpow⟩
  have hie : i = e := by
    by_contra hne
    have hilt : i < e := lt_of_le_of_ne hi hne
    apply hnotdvd
    rw [hpow]
    exact Nat.pow_dvd_pow 2 (by omega)
  rw [hpow, hie, ← ha]

theorem eq_one_of_ringAut_fixed_of_orderOf_eq_card {a : ℕ}
    (hK : Nat.card K = 2 ^ a) {σ : K ≃+* K} (hσ : orderOf σ = a) {lam : Kˣ}
    (hlam : σ (lam : K) = (lam : K)) : lam = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (by
    rw [← Nat.card_eq_fintype_card]; exact hK)
  let R := FixedPoints.subfield (Subgroup.zpowers σ) K
  have hmem : (lam : K) ∈ R := (mem_fixedSubfield_iff σ (lam : K)).mpr hlam
  have hcard : Nat.card R = 2 := by
    have h := CFSG.Semidihedral.FixedFieldData.fixedSubfield_card 2 a K hK
      (Subgroup.zpowers σ)
    rw [Nat.card_zpowers, hσ,
      Nat.div_self (by rw [← hσ]; exact orderOf_pos σ)] at h
    simpa using h
  have hunits : Nat.card Rˣ = 1 := by rw [Nat.card_units, hcard]
  haveI : Subsingleton Rˣ := (Nat.card_eq_one_iff_unique.mp hunits).1
  let xR : R := ⟨(lam : K), hmem⟩
  have hx0 : xR ≠ 0 := by
    intro h0
    exact lam.ne_zero (congrArg Subtype.val h0)
  let uR : Rˣ := Units.mk0 xR hx0
  have huR : uR = 1 := Subsingleton.elim _ _
  have hx1 : xR = 1 := by
    have := congrArg (fun u : Rˣ => (u : R)) huR
    simpa [uR] using this
  exact Units.ext (congrArg Subtype.val hx1)

private theorem fieldAut_factors_mul_inv_eq
    {θ : MulAut (PSL2 K)} {h u d u' d' : PSL2 K} {σ : K ≃+* K}
    (hd : d ∈ burnsideAut_psl2Diag K) (hd' : d' ∈ burnsideAut_psl2Diag K)
    (hfac : θ = MulAut.conj u * (MulAut.conj d * psl2FieldAut K σ))
    (hh : h = u' * d') :
    θ h * h⁻¹ = (u * (d * psl2FieldAut K σ u' * d⁻¹)) *
      (psl2FieldAut K σ d' * d'⁻¹) * ((d' * u⁻¹ * d'⁻¹) * u'⁻¹) := by
  have hσd'D : psl2FieldAut K σ d' ∈ burnsideAut_psl2Diag K := by
    have h := Subgroup.mem_map_of_mem (psl2FieldAut K σ).toMonoidHom hd'
    rwa [burnsideAut_map_psl2FieldAut_diag σ] at h
  have hcomm : d * psl2FieldAut K σ d' = psl2FieldAut K σ d' * d :=
    burnsideAut_psl2Diag_comm hd hσd'D
  have hstep : d * (psl2FieldAut K σ u' * psl2FieldAut K σ d') * d⁻¹ =
      d * psl2FieldAut K σ u' * d⁻¹ * psl2FieldAut K σ d' := by
    have h' : psl2FieldAut K σ d' * d⁻¹ = d⁻¹ * psl2FieldAut K σ d' := by
      calc psl2FieldAut K σ d' * d⁻¹ = d⁻¹ * (d * psl2FieldAut K σ d') * d⁻¹ := by
            group
        _ = d⁻¹ * (psl2FieldAut K σ d' * d) * d⁻¹ := by rw [hcomm]
        _ = d⁻¹ * psl2FieldAut K σ d' := by group
    calc d * (psl2FieldAut K σ u' * psl2FieldAut K σ d') * d⁻¹ =
        d * psl2FieldAut K σ u' * (psl2FieldAut K σ d' * d⁻¹) := by group
      _ = d * psl2FieldAut K σ u' * (d⁻¹ * psl2FieldAut K σ d') := by rw [h']
      _ = d * psl2FieldAut K σ u' * d⁻¹ * psl2FieldAut K σ d' := by group
  rw [hfac, hh]
  rw [MulAut.mul_apply, MulAut.mul_apply]
  rw [map_mul (psl2FieldAut K σ) u' d', MulAut.conj_apply, MulAut.conj_apply]
  rw [hstep]
  group

private theorem fieldAut_diag_mul_inv_mem_upper_of_factors
    {θ : MulAut (PSL2 K)} {h u d u' d' : PSL2 K} {σ : K ≃+* K}
    (hu : u ∈ psl2UpperUnipotentSubgroup K)
    (hd : d ∈ burnsideAut_psl2Diag K)
    (hu' : u' ∈ psl2UpperUnipotentSubgroup K)
    (hd' : d' ∈ burnsideAut_psl2Diag K)
    (hfac : θ = MulAut.conj u * (MulAut.conj d * psl2FieldAut K σ))
    (hh : h = u' * d')
    (hcent : θ h * h⁻¹ ∈ psl2UpperUnipotentSubgroup K) :
    psl2FieldAut K σ d' * d'⁻¹ ∈ psl2UpperUnipotentSubgroup K := by
  let U := psl2UpperUnipotentSubgroup K
  have hσu' : psl2FieldAut K σ u' ∈ U := by
    change psl2FieldAut K σ u' ∈ psl2UpperUnipotentSubgroup K
    rw [← burnsideAut_map_psl2FieldAut_upper σ]
    exact Subgroup.mem_map_of_mem _ hu'
  have hdN : d ∈ Subgroup.normalizer (U : Set (PSL2 K)) := by
    rw [psl2UpperUnipotent_normalizer_eq_borel]
    exact burnsideAut_psl2Diag_le_borel hd
  have hA : u * (d * psl2FieldAut K σ u' * d⁻¹) ∈ U :=
    Subgroup.mul_mem _ hu ((Subgroup.mem_normalizer_iff.mp hdN _).1 hσu')
  have hd'N : d' ∈ Subgroup.normalizer (U : Set (PSL2 K)) := by
    rw [psl2UpperUnipotent_normalizer_eq_borel]
    exact burnsideAut_psl2Diag_le_borel hd'
  have hB : (d' * u⁻¹ * d'⁻¹) * u'⁻¹ ∈ U :=
    Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hd'N _).1 (Subgroup.inv_mem _ hu))
      (Subgroup.inv_mem _ hu')
  have hEq := fieldAut_factors_mul_inv_eq hd hd' hfac hh
  have hEq' : psl2FieldAut K σ d' * d'⁻¹ =
      (u * (d * psl2FieldAut K σ u' * d⁻¹))⁻¹ * (θ h * h⁻¹) *
        ((d' * u⁻¹ * d'⁻¹) * u'⁻¹)⁻¹ := by
    rw [hEq]
    group
  rw [hEq']
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hA) hcent)
    (Subgroup.inv_mem _ hB)

private theorem fieldAut_diag_eq_of_mul_inv_mem_upper {a : ℕ}
    (hK : Nat.card K = 2 ^ a) (ha1 : 1 ≤ a) {σ : K ≃+* K} {d' : PSL2 K}
    (hd' : d' ∈ burnsideAut_psl2Diag K)
    (h : psl2FieldAut K σ d' * d'⁻¹ ∈ psl2UpperUnipotentSubgroup K) :
    psl2FieldAut K σ d' = d' := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (by
    rw [← Nat.card_eq_fintype_card]; exact hK)
  let U := psl2UpperUnipotentSubgroup K
  let D := burnsideAut_psl2Diag K
  have hσd'D : psl2FieldAut K σ d' ∈ D := by
    have hmem := Subgroup.mem_map_of_mem (psl2FieldAut K σ).toMonoidHom hd'
    rwa [burnsideAut_map_psl2FieldAut_diag σ] at hmem
  have hU2 : IsPGroup 2 U := by
    change IsPGroup 2 (psl2UpperUnipotentSubgroup K)
    obtain ⟨Q, hQ⟩ := psl2UpperUnipotent_isSylow K hK
    rw [← hQ]
    exact Q.isPGroup'
  have hDodd : Odd (Nat.card D) := burnsideAut_card_psl2Diag_odd ha1 hK
  have hbt : U ⊓ D = ⊥ := inf_eq_bot_of_isPGroup_two_of_odd hU2 hDodd
  have hmem : psl2FieldAut K σ d' * d'⁻¹ ∈ U ⊓ D :=
    ⟨h, Subgroup.mul_mem _ hσd'D (Subgroup.inv_mem _ hd')⟩
  rw [hbt] at hmem
  exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hmem)

private theorem eq_one_of_fieldAut_diag_fixed {a : ℕ} (hK : Nat.card K = 2 ^ a)
    {σ : K ≃+* K} (hσ : orderOf σ = a) {lam : Kˣ}
    (h : psl2FieldAut K σ (psl2QuotientMap K (burnsideAut_sl2DiagHom K lam)) =
      psl2QuotientMap K (burnsideAut_sl2DiagHom K lam)) :
    lam = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (by
    rw [← Nat.card_eq_fintype_card]; exact hK)
  have hfixlam : σ (lam : K) = (lam : K) := by
    rw [burnsideAut_psl2FieldAut_diag σ lam] at h
    have h' := psl2QuotientMap_injective_of_charTwo (K := K) h
    have h'' := burnsideAut_sl2DiagHom_injective K h'
    simpa using congrArg Units.val h''
  exact eq_one_of_ringAut_fixed_of_orderOf_eq_card hK hσ hfixlam

private theorem mem_upper_of_normalizes_fieldPart {a : ℕ} (hK : Nat.card K = 2 ^ a)
    (ha1 : 1 ≤ a) {θ : MulAut (PSL2 K)}
    (hθU : (psl2UpperUnipotentSubgroup K).map θ.toMonoidHom =
      psl2UpperUnipotentSubgroup K)
    {σ₀ : K ≃+* K} (hσ₀ : orderOf σ₀ = a)
    (hθσ : psl2FieldPart K θ = σ₀) {h : PSL2 K}
    (hhN : h ∈ Subgroup.normalizer
      ((psl2UpperUnipotentSubgroup K) : Set (PSL2 K)))
    (hcent : θ h * h⁻¹ ∈ psl2UpperUnipotentSubgroup K) :
    h ∈ psl2UpperUnipotentSubgroup K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (by
    rw [← Nat.card_eq_fintype_card]; exact hK)
  let U := psl2UpperUnipotentSubgroup K
  have hhB : h ∈ psl2Borel K := by
    rw [← psl2UpperUnipotent_normalizer_eq_borel]
    exact hhN
  obtain ⟨u', d', hu', hd', hud'⟩ := exists_mul_mem_upper_diag_of_mem_borel hhB
  obtain ⟨u, d, σ, hu, hd, hfac⟩ := exists_factorization_of_normalizes_upper hK hθU
  have hσθ : psl2FieldPart K θ = σ := by
    rw [hfac, map_mul, map_mul, psl2FieldPart_conj, psl2FieldPart_conj,
      psl2FieldPart_psl2FieldAut, one_mul, one_mul]
  have hσσ₀ : σ = σ₀ := by rw [← hσθ, hθσ]
  have hcent' : psl2FieldAut K σ d' * d'⁻¹ ∈ U :=
    fieldAut_diag_mul_inv_mem_upper_of_factors hu hd hu' hd' hfac hud'.symm hcent
  have hfix : psl2FieldAut K σ d' = d' :=
    fieldAut_diag_eq_of_mul_inv_mem_upper hK ha1 hd' hcent'
  rw [hσσ₀] at hfix
  obtain ⟨lam, rfl⟩ := MonoidHom.mem_range.mp hd'
  have hlam1 : lam = 1 := eq_one_of_fieldAut_diag_fixed hK hσ₀ hfix
  have hd1 : ((psl2QuotientMap K).comp (burnsideAut_sl2DiagHom K)) lam = 1 := by
    change psl2QuotientMap K (burnsideAut_sl2DiagHom K lam) = 1
    rw [hlam1]
    simp
  rw [← hud', hd1, mul_one]
  exact hu'

theorem psl2_fieldGen {a : ℕ} (hK : Nat.card K = 2 ^ a)
    (θ₀ : MulAut (PSL2 K)) (hσ₀ : orderOf (psl2FieldPart K θ₀) = a) :
    ∀ θ : MulAut (PSL2 K), ∃ j : ℕ, ∃ x : PSL2 K, θ = θ₀ ^ j * MulAut.conj x := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (by
    rw [← Nat.card_eq_fintype_card]; exact hK)
  haveI : Finite (RingAut K) :=
    Finite.of_injective (fun e : RingAut K => (e : K → K))
      (fun _ _ h => RingEquiv.ext (congrFun h))
  intro θ
  have hmem : psl2FieldPart K θ ∈ Subgroup.zpowers (psl2FieldPart K θ₀) := by
    rw [zpowers_psl2FieldPart_eq_top hK hσ₀]
    exact Subgroup.mem_top _
  have hmem' : psl2FieldPart K θ ∈
      (Finset.range (orderOf (psl2FieldPart K θ₀))).image
        ((psl2FieldPart K θ₀) ^ ·) :=
    (isOfFinOrder_of_finite (psl2FieldPart K θ₀)).mem_zpowers_iff_mem_range_orderOf.mp hmem
  rw [Finset.mem_image] at hmem'
  obtain ⟨j, -, hj⟩ := hmem'
  let ψ : MulAut (PSL2 K) := (θ₀ ^ j)⁻¹ * θ
  have hfield : psl2FieldPart K ψ = 1 := by
    change psl2FieldPart K ((θ₀ ^ j)⁻¹ * θ) = 1
    rw [map_mul, map_inv, map_pow, hj]
    exact inv_mul_cancel _
  rw [psl2FieldPart_eq_autFieldPart] at hfield
  obtain ⟨x, hx⟩ := CFSG.Quasithin.exists_conj_of_autFieldPart_eq_one hfield
  refine ⟨j, x, ?_⟩
  calc θ = θ₀ ^ j * ((θ₀ ^ j)⁻¹ * θ) := by group
    _ = θ₀ ^ j * MulAut.conj x := by
      change θ₀ ^ j * ψ = θ₀ ^ j * MulAut.conj x
      rw [hx]

private theorem conj_mem_normalizer_upper {S : Sylow 2 (PSL2 K)} {h₁ h : PSL2 K}
    (hh₁U : (psl2UpperUnipotentSubgroup K).map (MulAut.conj h₁).toMonoidHom =
      (S : Subgroup (PSL2 K)))
    (hhN : h ∈ Subgroup.normalizer ((S : Subgroup (PSL2 K)) : Set (PSL2 K))) :
    (MulAut.conj h₁)⁻¹ h ∈ Subgroup.normalizer
      ((psl2UpperUnipotentSubgroup K) : Set (PSL2 K)) := by
  let cinv : MulAut (PSL2 K) := (MulAut.conj h₁)⁻¹
  have hSmapInv : (S : Subgroup (PSL2 K)).map cinv.toMonoidHom =
      psl2UpperUnipotentSubgroup K := by
    rw [← hh₁U, Subgroup.map_map]
    have hcomp : cinv.toMonoidHom.comp (MulAut.conj h₁).toMonoidHom =
        MonoidHom.id (PSL2 K) := by
      ext x
      simp [cinv]
    rw [hcomp, Subgroup.map_id]
  have hmem := Subgroup.mem_map_of_mem cinv.toMonoidHom hhN
  have hnormmap : (Subgroup.normalizer
        ((S : Subgroup (PSL2 K)) : Set (PSL2 K))).map cinv.toMonoidHom =
      Subgroup.normalizer ((S : Subgroup (PSL2 K)).map cinv.toMonoidHom :
        Set (PSL2 K)) :=
    Subgroup.map_equiv_normalizer_eq (S : Subgroup (PSL2 K)) cinv
  rw [hnormmap, hSmapInv] at hmem
  exact hmem

private theorem conj_cent_mem_upper {S : Sylow 2 (PSL2 K)} {θ₀ : MulAut (PSL2 K)}
    {h₁ h : PSL2 K}
    (hh₁U : (psl2UpperUnipotentSubgroup K).map (MulAut.conj h₁).toMonoidHom =
      (S : Subgroup (PSL2 K)))
    (hcent : θ₀ h * h⁻¹ ∈ (S : Subgroup (PSL2 K))) :
    ((MulAut.conj h₁)⁻¹ * θ₀ * MulAut.conj h₁) ((MulAut.conj h₁)⁻¹ h) *
      ((MulAut.conj h₁)⁻¹ h)⁻¹ ∈ psl2UpperUnipotentSubgroup K := by
  let θ₁ : MulAut (PSL2 K) := (MulAut.conj h₁)⁻¹ * θ₀ * MulAut.conj h₁
  let h' : PSL2 K := (MulAut.conj h₁)⁻¹ h
  have hconjh' : MulAut.conj h₁ h' = h := by
    change MulAut.conj h₁ ((MulAut.conj h₁)⁻¹ h) = h
    rw [MulAut.inv_def, MulEquiv.apply_symm_apply]
  have hθ₁ : θ₁ h' = (MulAut.conj h₁)⁻¹ (θ₀ (MulAut.conj h₁ h')) := by
    simp only [θ₁, MulAut.mul_apply]
  have h1 : MulAut.conj h₁ (θ₁ h') = θ₀ h := by
    rw [hθ₁, hconjh']
    change MulAut.conj h₁ ((MulAut.conj h₁)⁻¹ (θ₀ h)) = θ₀ h
    rw [MulAut.inv_def, MulEquiv.apply_symm_apply]
  have h2 : MulAut.conj h₁ (h'⁻¹) = h⁻¹ := by
    rw [map_inv, hconjh']
  have hconj : MulAut.conj h₁ (θ₁ h' * h'⁻¹) = θ₀ h * h⁻¹ := by
    rw [map_mul, h1, h2]
  have hS : MulAut.conj h₁ (θ₁ h' * h'⁻¹) ∈ (S : Subgroup (PSL2 K)) := by
    rw [hconj]
    exact hcent
  have hmap : MulAut.conj h₁ (θ₁ h' * h'⁻¹) ∈
      (psl2UpperUnipotentSubgroup K).map (MulAut.conj h₁).toMonoidHom := by
    rw [hh₁U]
    exact hS
  obtain ⟨z, hz, hzEq⟩ := Subgroup.mem_map.mp hmap
  have hz' : z = θ₁ h' * h'⁻¹ := (MulAut.conj h₁).injective hzEq
  rw [← hz']
  exact hz

private theorem mem_sylow_of_conj_mem_upper {a : ℕ} (hK : Nat.card K = 2 ^ a)
    (ha1 : 1 ≤ a) {θ₀ : MulAut (PSL2 K)}
    (hσ₀ : orderOf (psl2FieldPart K θ₀) = a)
    {S : Sylow 2 (PSL2 K)}
    (hθ₀S : ∀ x ∈ (S : Subgroup (PSL2 K)), θ₀ x ∈ (S : Subgroup (PSL2 K)))
    {h₁ h : PSL2 K}
    (hh₁U : (psl2UpperUnipotentSubgroup K).map (MulAut.conj h₁).toMonoidHom =
      (S : Subgroup (PSL2 K)))
    (hhN : h ∈ Subgroup.normalizer ((S : Subgroup (PSL2 K)) : Set (PSL2 K)))
    (hcent : θ₀ h * h⁻¹ ∈ (S : Subgroup (PSL2 K))) :
    h ∈ (S : Subgroup (PSL2 K)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (by
    rw [← Nat.card_eq_fintype_card]; exact hK)
  let θ₁ : MulAut (PSL2 K) := (MulAut.conj h₁)⁻¹ * θ₀ * MulAut.conj h₁
  let h' : PSL2 K := (MulAut.conj h₁)⁻¹ h
  have hθ₁U : (psl2UpperUnipotentSubgroup K).map θ₁.toMonoidHom =
      psl2UpperUnipotentSubgroup K := conj_theta_maps_upper hh₁U hθ₀S
  have hθ₁σ : psl2FieldPart K θ₁ = psl2FieldPart K θ₀ := by
    simp only [θ₁, map_mul, map_inv, psl2FieldPart_conj, inv_one, one_mul, mul_one]
  have hh'N : h' ∈ Subgroup.normalizer
      ((psl2UpperUnipotentSubgroup K) : Set (PSL2 K)) :=
    conj_mem_normalizer_upper hh₁U hhN
  have hcent' : θ₁ h' * h'⁻¹ ∈ psl2UpperUnipotentSubgroup K :=
    conj_cent_mem_upper hh₁U hcent
  have hUp : h' ∈ psl2UpperUnipotentSubgroup K :=
    mem_upper_of_normalizes_fieldPart hK ha1 hθ₁U hσ₀ hθ₁σ hh'N hcent'
  have hh'S : MulAut.conj h₁ h' ∈ (S : Subgroup (PSL2 K)) := by
    rw [← hh₁U]
    exact Subgroup.mem_map_of_mem _ hUp
  have hconjh' : MulAut.conj h₁ h' = h := by
    change MulAut.conj h₁ ((MulAut.conj h₁)⁻¹ h) = h
    rw [MulAut.inv_def, MulEquiv.apply_symm_apply]
  rwa [hconjh'] at hh'S

theorem psl2_normalizer_fieldGen {a : ℕ} (hK : Nat.card K = 2 ^ a) (ha1 : 1 ≤ a)
    (θ₀ : MulAut (PSL2 K)) (hσ₀ : orderOf (psl2FieldPart K θ₀) = a)
    (S : Sylow 2 (PSL2 K))
    (hθ₀S : ∀ x ∈ (S : Subgroup (PSL2 K)), θ₀ x ∈ (S : Subgroup (PSL2 K))) :
    ∀ h ∈ Subgroup.normalizer ((S : Subgroup (PSL2 K)) : Set (PSL2 K)),
      θ₀ h * h⁻¹ ∈ (S : Subgroup (PSL2 K)) → h ∈ (S : Subgroup (PSL2 K)) := by
  intro h hhN hcent
  obtain ⟨h₁, hh₁U⟩ := exists_conj_upper_of_sylow hK S
  exact mem_sylow_of_conj_mem_upper hK ha1 hσ₀ hθ₀S hh₁U hhN hcent

end CFSG.Walter
