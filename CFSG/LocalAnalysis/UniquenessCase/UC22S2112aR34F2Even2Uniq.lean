module

public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLie
import CFSG.LocalAnalysis.UniquenessCase.UC22FunCountAmbient
import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitAmbient
import CFSG.LocalAnalysis.UniquenessCase.UC6N588D3
public import CFSG.ClassicalInvolution.RouteD.TypeABridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Phan Matrix Module CFSG.ClassicalInvolution.Generic
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open scoped MatrixGroups

private theorem uc22s2112r34_uniq_regular {K : Type} [Field K] {p : ℕ} [CharP K p]
    (hp : p.Prime) (h2 : (2 : K) ≠ 0) {n : ℕ} {hn : 2 ≤ n} {L : Subgroup SL(n, K)}
    {i : SL(n, K)} (h : IsLongRootSL2 hn L i) {a : SL(n, K)} (haL : a ∈ L) (ha1 : a ≠ 1)
    {r : ℕ} (hr : r.Prime) (hrp : r ≠ p) (har : a ^ r = 1)
    {v : Fin n → K} (hv : v ∈ minusSpace i)
    (hav : (a : Matrix (Fin n) (Fin n) K) *ᵥ v = v) : v = 0 := by
  obtain ⟨g, hL, rfl⟩ := h
  have haL' : a ∈ (rootSL2 K hn).map (MulAut.conj g).toMonoidHom := hL ▸ haL
  obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp haL'
  have ha1' : x ≠ 1 := by
    intro hx1
    apply ha1
    rw [← hxa, hx1, map_one]
  have har' : x ^ r = 1 := by
    have h1 : (MulAut.conj g).toMonoidHom (x ^ r) = (MulAut.conj g).toMonoidHom 1 := by
      rw [map_pow, hxa, har, map_one]
    exact (MulAut.conj g).injective h1
  obtain ⟨A, rfl⟩ := hx
  have hA1 : A ≠ 1 := by
    intro hA
    apply ha1'
    rw [hA, map_one]
  have hAr : A ^ r = 1 := by
    apply blockSL_injective (K := K) (m := n) (k := 2) (i := 0) (by omega)
    rw [map_pow, har', map_one]
  set u : Fin n → K := ((g⁻¹ : SL(n, K)) : Matrix (Fin n) (Fin n) K) *ᵥ v with hu
  have hvu : (g : Matrix (Fin n) (Fin n) K) *ᵥ u = v := by
    rw [hu, Matrix.mulVec_mulVec, coe_mul_coe_inv, Matrix.one_mulVec]
  have hinj : Function.Injective (fun w : Fin n → K => (g : Matrix (Fin n) (Fin n) K) *ᵥ w) := by
    intro y z hyz
    have h := congrArg (fun t => ((g⁻¹ : SL(n, K)) : Matrix (Fin n) (Fin n) K) *ᵥ t) hyz
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, coe_inv_mul_coe, Matrix.one_mulVec,
      Matrix.one_mulVec] at h
    exact h
  have huV : u ∈ eigSpace (negBlock K n 0) (-1) := by
    rw [mem_eigSpace_neg_one]
    apply hinj
    have hv1 : (g : Matrix (Fin n) (Fin n) K) *ᵥ ((negBlock K n 0) *ᵥ u) = -v := by
      have h := hv
      rw [minusSpace, mem_eigSpace_neg_one] at h
      rw [show ((g * rootInv K hn * g⁻¹ : SL(n, K)) : Matrix (Fin n) (Fin n) K) =
          (g : Matrix (Fin n) (Fin n) K) * negBlock K n 0 *
            ((g⁻¹ : SL(n, K)) : Matrix (Fin n) (Fin n) K) by
        simp only [Matrix.SpecialLinearGroup.coe_mul, coe_rootInv]] at h
      rwa [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hu] at h
    change (g : Matrix (Fin n) (Fin n) K) *ᵥ ((negBlock K n 0) *ᵥ u) =
      (g : Matrix (Fin n) (Fin n) K) *ᵥ (-u)
    rw [hv1, Matrix.mulVec_neg, hvu]
  have huV' : u ∈ LinearMap.range (Matrix.mulVecLin (blockSel K n 2 0)) := by
    rwa [← eigSpace_negBlock_neg_one h2 (by omega : 0 + 2 ≤ n)]
  obtain ⟨w, hw⟩ := LinearMap.mem_range.mp huV'
  rw [Matrix.mulVecLin_apply] at hw
  have hav' : (blockMat n 0 (A : Matrix (Fin 2) (Fin 2) K)) *ᵥ u = u := by
    apply hinj
    have hcoe : ((a : SL(n, K)) : Matrix (Fin n) (Fin n) K) =
        (g : Matrix (Fin n) (Fin n) K) * blockMat n 0 (A : Matrix (Fin 2) (Fin 2) K) *
          ((g⁻¹ : SL(n, K)) : Matrix (Fin n) (Fin n) K) := by
      rw [← hxa]
      simp [MulAut.conj_apply, Matrix.SpecialLinearGroup.coe_mul, coe_blockSL]
    have h : (g : Matrix (Fin n) (Fin n) K) *ᵥ
        ((blockMat n 0 (A : Matrix (Fin 2) (Fin 2) K)) *ᵥ u) = v := by
      have h1 : ((a : SL(n, K)) : Matrix (Fin n) (Fin n) K) *ᵥ v = v := hav
      rw [hcoe, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hu] at h1
      exact h1
    change (g : Matrix (Fin n) (Fin n) K) *ᵥ
      ((blockMat n 0 (A : Matrix (Fin 2) (Fin 2) K)) *ᵥ u) =
      (g : Matrix (Fin n) (Fin n) K) *ᵥ u
    rw [h, hvu]
  have hAw : (A : Matrix (Fin 2) (Fin 2) K) *ᵥ w = w := by
    ext x
    have h1 := blockMat_mulVec_blockIdx (F := K) (h := (by omega : 0 + 2 ≤ n))
      (A : Matrix (Fin 2) (Fin 2) K) u x
    rw [hav'] at h1
    have hu_idx : ∀ y : Fin 2, u (blockIdx 0 (by omega : 0 + 2 ≤ n) y) = w y := by
      intro y
      rw [← hw, blockSel_mulVec, dite_eq_left (by simp only [blockIdx_val]; omega)]
      congr 1
      exact Fin.ext (by simp [blockIdx_val])
    rw [show (fun y => u (blockIdx 0 (by omega : 0 + 2 ≤ n) y)) = w from funext hu_idx] at h1
    rw [← h1, hu_idx x]
  by_cases hw0 : w = 0
  · rw [hw0, Matrix.mulVec_zero] at hw
    rw [← hvu, ← hw]
    simp
  · exfalso
    have hpow : A ^ p = 1 :=
      CFSG.Wreathed.OriginalAllPrime.V4InputsW.pow_char_eq_one_of_mulVec_eq hw0 hAw
    have hcop : Nat.Coprime p r := (Nat.coprime_primes hp hr).mpr (Ne.symm hrp)
    have horder : orderOf A = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hpow)
        (orderOf_dvd_of_pow_eq_one hAr)
    exact hA1 (orderOf_eq_one_iff.mp horder)

theorem uc22s2112r34_isLongRootSL2_eq_of_mem {K : Type} [Field K] {p : ℕ} [CharP K p]
    (hp : p.Prime) (h2 : (2 : K) ≠ 0) {n : ℕ} {hn : 2 ≤ n} {L L' : Subgroup SL(n, K)}
    {i i' : SL(n, K)} (h : IsLongRootSL2 hn L i) (h' : IsLongRootSL2 hn L' i')
    {a : SL(n, K)} (haL : a ∈ L) (haL' : a ∈ L') (ha1 : a ≠ 1) {r : ℕ} (hr : r.Prime)
    (hrp : r ≠ p) (har : a ^ r = 1) : L = L' := by
  have hW : ∀ v : Fin n → K, v ∈ fixSpace i ↔ (a : Matrix (Fin n) (Fin n) K) *ᵥ v = v := by
    intro v
    constructor
    · intro hv
      exact ((h.mem_iff_vec h2).mp haL).1 v hv
    · intro hav
      have hvsup : v ∈ minusSpace i ⊔ fixSpace i := by
        rw [(h.isCompl h2).sup_eq_top]
        exact Submodule.mem_top
      obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Submodule.mem_sup.mp hvsup
      have ha2 : (a : Matrix (Fin n) (Fin n) K) *ᵥ v₂ = v₂ :=
        ((h.mem_iff_vec h2).mp haL).1 v₂ hv₂
      have ha1v : (a : Matrix (Fin n) (Fin n) K) *ᵥ v₁ = v₁ := by
        rw [Matrix.mulVec_add, ha2] at hav
        exact add_right_cancel hav
      rw [uc22s2112r34_uniq_regular hp h2 h haL ha1 hr hrp har hv₁ ha1v]
      simpa using hv₂
  have hW' : ∀ v : Fin n → K, v ∈ fixSpace i' ↔ (a : Matrix (Fin n) (Fin n) K) *ᵥ v = v := by
    intro v
    constructor
    · intro hv
      exact ((h'.mem_iff_vec h2).mp haL').1 v hv
    · intro hav
      have hvsup : v ∈ minusSpace i' ⊔ fixSpace i' := by
        rw [(h'.isCompl h2).sup_eq_top]
        exact Submodule.mem_top
      obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Submodule.mem_sup.mp hvsup
      have ha2 : (a : Matrix (Fin n) (Fin n) K) *ᵥ v₂ = v₂ :=
        ((h'.mem_iff_vec h2).mp haL').1 v₂ hv₂
      have ha1v : (a : Matrix (Fin n) (Fin n) K) *ᵥ v₁ = v₁ := by
        rw [Matrix.mulVec_add, ha2] at hav
        exact add_right_cancel hav
      rw [uc22s2112r34_uniq_regular hp h2 h' haL' ha1 hr hrp har hv₁ ha1v]
      simpa using hv₂
  have hfix : fixSpace i = fixSpace i' := by
    apply Submodule.ext
    intro v
    rw [hW v, hW' v]
  have hminus : minusSpace i = minusSpace i' := by
    have hV : minusSpace i =
        LinearMap.range (Matrix.mulVecLin ((a : Matrix (Fin n) (Fin n) K) - 1)) := by
      have hrange : LinearMap.range (Matrix.mulVecLin ((a : Matrix (Fin n) (Fin n) K) - 1)) ≤
          minusSpace i := by
        rintro v ⟨w, rfl⟩
        have hw : w ∈ minusSpace i ⊔ fixSpace i := by
          rw [(h.isCompl h2).sup_eq_top]
          exact Submodule.mem_top
        obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.mp hw
        have ha2 : (a : Matrix (Fin n) (Fin n) K) *ᵥ w₂ = w₂ :=
          ((h.mem_iff_vec h2).mp haL).1 w₂ hw₂
        have ha1 : (a : Matrix (Fin n) (Fin n) K) *ᵥ w₁ ∈ minusSpace i :=
          ((h.mem_iff_vec h2).mp haL).2 w₁ hw₁
        have hcalc : Matrix.mulVecLin ((a : Matrix (Fin n) (Fin n) K) - 1) (w₁ + w₂) =
            (a : Matrix (Fin n) (Fin n) K) *ᵥ w₁ - w₁ := by
          rw [Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.mulVec_add, ha2,
            Matrix.one_mulVec]
          abel
        rw [hcalc]
        exact sub_mem ha1 hw₁
      have hker : LinearMap.ker (Matrix.mulVecLin ((a : Matrix (Fin n) (Fin n) K) - 1)) =
          fixSpace i := by
        ext v
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec,
          sub_eq_zero]
        exact (hW v).symm
      have hdimW : finrank K (fixSpace i) = n - 2 := by
        have h1 := Submodule.finrank_add_eq_of_isCompl (h.isCompl h2)
        rw [h.finrank_minusSpace h2, Module.finrank_fin_fun] at h1
        omega
      have hrank := LinearMap.finrank_range_add_finrank_ker
        (Matrix.mulVecLin ((a : Matrix (Fin n) (Fin n) K) - 1))
      rw [hker, hdimW, Module.finrank_fin_fun] at hrank
      have hdimrange : finrank K
          (LinearMap.range (Matrix.mulVecLin ((a : Matrix (Fin n) (Fin n) K) - 1))) = 2 := by
        omega
      symm
      exact Submodule.eq_of_le_of_finrank_eq hrange (by rw [hdimrange, h.finrank_minusSpace h2])
    have hV' : minusSpace i' =
        LinearMap.range (Matrix.mulVecLin ((a : Matrix (Fin n) (Fin n) K) - 1)) := by
      have hrange : LinearMap.range (Matrix.mulVecLin ((a : Matrix (Fin n) (Fin n) K) - 1)) ≤
          minusSpace i' := by
        rintro v ⟨w, rfl⟩
        have hw : w ∈ minusSpace i' ⊔ fixSpace i' := by
          rw [(h'.isCompl h2).sup_eq_top]
          exact Submodule.mem_top
        obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.mp hw
        have ha2 : (a : Matrix (Fin n) (Fin n) K) *ᵥ w₂ = w₂ :=
          ((h'.mem_iff_vec h2).mp haL').1 w₂ hw₂
        have ha1 : (a : Matrix (Fin n) (Fin n) K) *ᵥ w₁ ∈ minusSpace i' :=
          ((h'.mem_iff_vec h2).mp haL').2 w₁ hw₁
        have hcalc : Matrix.mulVecLin ((a : Matrix (Fin n) (Fin n) K) - 1) (w₁ + w₂) =
            (a : Matrix (Fin n) (Fin n) K) *ᵥ w₁ - w₁ := by
          rw [Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.mulVec_add, ha2,
            Matrix.one_mulVec]
          abel
        rw [hcalc]
        exact sub_mem ha1 hw₁
      have hker : LinearMap.ker (Matrix.mulVecLin ((a : Matrix (Fin n) (Fin n) K) - 1)) =
          fixSpace i' := by
        ext v
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec,
          sub_eq_zero]
        exact (hW' v).symm
      have hdimW : finrank K (fixSpace i') = n - 2 := by
        have h1 := Submodule.finrank_add_eq_of_isCompl (h'.isCompl h2)
        rw [h'.finrank_minusSpace h2, Module.finrank_fin_fun] at h1
        omega
      have hrank := LinearMap.finrank_range_add_finrank_ker
        (Matrix.mulVecLin ((a : Matrix (Fin n) (Fin n) K) - 1))
      rw [hker, hdimW, Module.finrank_fin_fun] at hrank
      have hdimrange : finrank K
          (LinearMap.range (Matrix.mulVecLin ((a : Matrix (Fin n) (Fin n) K) - 1))) = 2 := by
        omega
      symm
      exact Submodule.eq_of_le_of_finrank_eq hrange (by rw [hdimrange, h'.finrank_minusSpace h2])
    rw [hV, hV']
  apply Subgroup.ext
  intro x
  rw [h.mem_iff_vec h2, h'.mem_iff_vec h2, hfix, hminus]

private theorem uc22s2112r34_uniq_ordA_ne_one {q n : ℕ} (hq : 3 ≤ q) (hodd : Odd q)
    (hn : 4 ≤ n) : ordA (n - 1) q ≠ ordA 1 q := by
  have hdvd : q ^ 2 ∣ ordA (n - 1) q := by
    let C : ℕ := ∏ j ∈ Finset.Icc 2 n, (q ^ j - 1)
    let d : ℕ := Nat.gcd n (q - 1)
    have hdvdC : d ∣ C := by
      have h1 : d ∣ q - 1 := Nat.gcd_dvd_right _ _
      have h2 : q - 1 ∣ q ^ 2 - 1 := by
        simpa using Nat.sub_one_dvd_pow_sub_one q 2
      have h3 : q ^ 2 - 1 ∣ C := by
        show q ^ 2 - 1 ∣ ∏ j ∈ Finset.Icc 2 n, (q ^ j - 1)
        exact Finset.dvd_prod_of_mem (fun j => q ^ j - 1)
          (by simp only [Finset.mem_Icc]; omega)
      exact h1.trans (h2.trans h3)
    have hdvdnum : d ∣ q ^ ((n - 1) * n / 2) * C :=
      dvd_mul_of_dvd_right hdvdC _
    have hmul : ordA (n - 1) q * d = q ^ ((n - 1) * n / 2) * C := by
      rw [CFSG.Open.ordA]
      simp only [Nat.sub_add_cancel (by omega : 1 ≤ n)]
      exact Nat.div_mul_cancel hdvdnum
    have hexp : 2 ≤ (n - 1) * n / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
      have h : 2 * 2 ≤ (n - 1) * n := by
        have hn3 : 3 ≤ n - 1 := by omega
        calc 2 * 2 = 4 := by norm_num
          _ ≤ 3 * 4 := by norm_num
          _ ≤ (n - 1) * n := Nat.mul_le_mul hn3 (by omega)
      omega
    have hdvdq : q ^ 2 ∣ q ^ ((n - 1) * n / 2) := Nat.pow_dvd_pow q hexp
    have hdvdnum2 : q ^ 2 ∣ q ^ ((n - 1) * n / 2) * C :=
      hdvdq.trans (dvd_mul_right _ _)
    have hcopq : Nat.Coprime q (q - 1) := by
      rw [Nat.coprime_iff_gcd_eq_one]
      have hd : Nat.gcd q (q - 1) ∣ q - (q - 1) :=
        Nat.dvd_sub (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
      rw [show q - (q - 1) = 1 by omega] at hd
      exact Nat.dvd_one.mp hd
    have hcop : Nat.Coprime (q ^ 2) d :=
      (hcopq.pow_left 2).of_dvd_right (Nat.gcd_dvd_right _ _)
    have hdiv : q ^ 2 ∣ ordA (n - 1) q * d := by
      rw [hmul]
      exact hdvdnum2
    exact Nat.Coprime.dvd_of_dvd_mul_right hcop hdiv
  have hnot : ¬ q ^ 2 ∣ ordA 1 q := by
    have htwo : 2 * ordA 1 q = q * (q ^ 2 - 1) :=
      CFSG.LocalAnalysis.UniquenessCase.UC6.N588.two_mul_ordA_one hodd
    intro h
    have h1 : q ^ 2 ∣ q * (q ^ 2 - 1) := by
      have h2 := h.mul_right 2
      rwa [mul_comm (ordA 1 q) 2, htwo] at h2
    have h1' : q * q ∣ q * (q ^ 2 - 1) := by
      rwa [show q * q = q ^ 2 from (pow_two q).symm]
    have h2 : q ∣ q ^ 2 - 1 :=
      Nat.dvd_of_mul_dvd_mul_left (k := q) (by omega) h1'
    have h3 : q ∣ 1 := by
      have hq2dvd : q ∣ q ^ 2 := dvd_pow_self q (by norm_num : 2 ≠ 0)
      have h4 := Nat.dvd_sub hq2dvd h2
      have hq2pos : 1 ≤ q ^ 2 := Nat.one_le_pow 2 q (by omega)
      rwa [Nat.sub_sub_eq_min, min_eq_right hq2pos] at h4
    have := Nat.dvd_one.mp h3
    omega
  intro heq
  exact hnot (heq ▸ hdvd)


private theorem uc22s2112r34_eq_of_mem_inf_psl_aux {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] {n p f : ℕ} [fact : Fact p.Prime]
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : 4 ≤ n)
    (hadm : StatedLieAdmissible .PSL n p f) (hX : CFSG.Blueprint.LieModel X .PSL n p f)
    {K K' : Subgroup X} (hK : IsFundamentalOver (p ^ f) K) (hK' : IsFundamentalOver (p ^ f) K')
    {x : X} (hxK : x ∈ K) (hxK' : x ∈ K') (hxr : (orderOf x).Prime) (hx2 : orderOf x ≠ 2)
    (hxp : orderOf x ≠ p) : K = K' := by
  classical
  obtain ⟨ψ, hψ, hker⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    .PSL n p f hp hp2 (by trivial) hadm X hX
  have hZ : Subgroup.center X = ⊥ :=
    CFSG.ComponentClassification.RankTwoOddLie.center_eq_bot_of_simple
      (exists_noncommuting_of_isFundamentalOver hK)
  have hL2 : ¬ IsL2Over17 (X ⧸ Subgroup.center X) (p ^ f) := by
    intro hL2
    obtain ⟨r, f', hr, hr2, hq, hf', hm2⟩ := hL2
    have hcardX : Nat.card X = ordA (n - 1) (p ^ f) :=
      CFSG.GH74.card_of_lieModel_PSL (by omega) hX
    have hcardQ : Nat.card (X ⧸ Subgroup.center X) = ordA (2 - 1) (r ^ f') :=
      CFSG.GH74.card_of_lieModel_PSL (by omega) hm2
    have heq : ordA (n - 1) (p ^ f) = ordA 1 (p ^ f) := by
      calc ordA (n - 1) (p ^ f) = Nat.card X := hcardX.symm
        _ = Nat.card (X ⧸ Subgroup.center X) := by
            rw [hZ]
            exact (Nat.card_congr QuotientGroup.quotientBot.toEquiv).symm
        _ = ordA (2 - 1) (r ^ f') := hcardQ
        _ = ordA 1 (r ^ f') := by norm_num
        _ = ordA 1 (p ^ f) := by rw [← hq]
    have hf : 1 ≤ f := hadm.2.1
    have hq3 : 3 ≤ p ^ f := by
      have hp3 : 3 ≤ p := by
        have := hp.two_le
        omega
      exact hp3.trans (Nat.le_self_pow (by omega : f ≠ 0) p)
    exact uc22s2112r34_uniq_ordA_ne_one hq3 ((hp.odd_of_ne_two hp2).pow) hn heq
  obtain ⟨R, hR, hRK, hRk⟩ := exists_mem_fundamentalSubgroups_of_isFundamentalOver_general
    hp hp2 hadm hX (by trivial) (by simp; omega) hL2 ψ hψ hker hK
  obtain ⟨R', hR', hR'K, hR'k⟩ := exists_mem_fundamentalSubgroups_of_isFundamentalOver_general
    hp hp2 hadm hX (by trivial) (by simp; omega) hL2 ψ hψ hker hK'
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hRlong : R ∈ longRootSet (K := GaloisField p f) (by omega : 2 ≤ m + 1) := by
    refine CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset
      (m := m) (F := GaloisField p f) (by omega : 2 ≤ m + 1) ?_
    change R ∈ fundamentalSubgroups .PSL
      (CFSG.LieType.Universal.SpecialLinear.rootDatum m (GaloisField p f)) at hR
    exact hR
  have hR'long : R' ∈ longRootSet (K := GaloisField p f) (by omega : 2 ≤ m + 1) := by
    refine CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset
      (m := m) (F := GaloisField p f) (by omega : 2 ≤ m + 1) ?_
    change R' ∈ fundamentalSubgroups .PSL
      (CFSG.LieType.Universal.SpecialLinear.rootDatum m (GaloisField p f)) at hR'
    exact hR'
  obtain ⟨i, hi⟩ := hRlong
  obtain ⟨i', hi'⟩ := hR'long
  obtain ⟨a, haR, hψa⟩ := Subgroup.mem_map.mp (hRK ▸ hxK)
  obtain ⟨b, hbR, hψb⟩ := Subgroup.mem_map.mp (hR'K ▸ hxK')
  let a' : SL(m + 1, GaloisField p f) := a
  let b' : SL(m + 1, GaloisField p f) := b
  let ψ' : SL(m + 1, GaloisField p f) →* X := ψ
  have hψa' : ψ' a' = x := hψa
  have hψb' : ψ' b' = x := hψb
  set r : ℕ := orderOf x with hr
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.RouteD.two_ne_zero_galoisField hp2
  have ha_order : orderOf a = r := by
    refine Nat.dvd_antisymm ?_ ?_
    · apply orderOf_dvd_of_pow_eq_one
      have hmem : a ^ r ∈ R ⊓ ψ.ker := by
        refine ⟨R.pow_mem haR r, ?_⟩
        show ψ (a ^ r) = 1
        rw [map_pow, hψa, hr, pow_orderOf_eq_one]
      rw [hRk] at hmem
      exact Subgroup.mem_bot.mp hmem
    · rw [hr, ← hψa]
      exact orderOf_map_dvd ψ a
  have hb_order : orderOf b = r := by
    refine Nat.dvd_antisymm ?_ ?_
    · apply orderOf_dvd_of_pow_eq_one
      have hmem : b ^ r ∈ R' ⊓ ψ.ker := by
        refine ⟨R'.pow_mem hbR r, ?_⟩
        show ψ (b ^ r) = 1
        rw [map_pow, hψb, hr, pow_orderOf_eq_one]
      rw [hR'k] at hmem
      exact Subgroup.mem_bot.mp hmem
    · rw [hr, ← hψb]
      exact orderOf_map_dvd ψ b
  have ha1 : a ≠ 1 := by
    intro h1
    have h1' : r = 1 := by rw [← ha_order, h1, orderOf_one]
    exact hxr.ne_one h1'
  have har : a ^ r = 1 := by rw [← ha_order, pow_orderOf_eq_one]
  have hbr : b ^ r = 1 := by rw [← hb_order, pow_orderOf_eq_one]
  have ha1' : a' ≠ 1 := ha1
  have har' : a' ^ r = 1 := har
  have hbr' : b' ^ r = 1 := hbr
  let ζ : SL(m + 1, GaloisField p f) := a' * b'⁻¹
  have hζker : ζ ∈ ψ'.ker := by
    show ψ' (a' * b'⁻¹) = 1
    rw [map_mul, map_inv, hψa', hψb', mul_inv_cancel]
  have hζcenter : ζ ∈ Subgroup.center SL(m + 1, GaloisField p f) := hker hζker
  obtain ⟨ω, hω, hζmat⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hζcenter
  have hζr : ζ ^ r = 1 := by
    have hcomm : Commute ζ b' := (Subgroup.mem_center_iff.mp hζcenter b').symm
    have h1 : (ζ * b') ^ r = ζ ^ r * b' ^ r := hcomm.mul_pow r
    have hζb : ζ * b' = a' := by
      show a' * b'⁻¹ * b' = a'
      group
    rw [hζb, har', hbr', mul_one] at h1
    exact h1.symm
  have hζ1 : ζ = 1 := by
    by_cases h4 : m + 1 = 4
    · have hω4 : ω ^ 4 = 1 := by
        have := hω
        rw [h4] at this
        simpa using this
      have hζ4 : ζ ^ 4 = 1 := by
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, ← hζmat,
          ← map_pow, hω4, map_one]
      have hcop : Nat.Coprime 4 r := by
        have h2r : Nat.Coprime 2 r := (Nat.coprime_primes Nat.prime_two hxr).mpr (by omega)
        simpa using h2r.pow_left 2
      exact (pow_eq_one_iff_of_coprime hcop).mp ⟨hζ4, hζr⟩
    · have hm5 : 5 ≤ m + 1 := by omega
      have hdimW : finrank (GaloisField p f) (fixSpace i) = (m + 1) - 2 := by
        have h1 := Submodule.finrank_add_eq_of_isCompl (hi.isCompl h2)
        rw [hi.finrank_minusSpace h2, Module.finrank_fin_fun] at h1
        omega
      have hdimW' : finrank (GaloisField p f) (fixSpace i') = (m + 1) - 2 := by
        have h1 := Submodule.finrank_add_eq_of_isCompl (hi'.isCompl h2)
        rw [hi'.finrank_minusSpace h2, Module.finrank_fin_fun] at h1
        omega
      have hdiminf : 0 < finrank (GaloisField p f)
          ((fixSpace i ⊓ fixSpace i') : Submodule (GaloisField p f)
            (Fin (m + 1) → GaloisField p f)) := by
        have h1 := Submodule.finrank_sup_add_finrank_inf_eq
          (fixSpace i : Submodule (GaloisField p f) (Fin (m + 1) → GaloisField p f))
          (fixSpace i' : Submodule (GaloisField p f) (Fin (m + 1) → GaloisField p f))
        have hsup : finrank (GaloisField p f)
            ((fixSpace i ⊔ fixSpace i') : Submodule (GaloisField p f)
              (Fin (m + 1) → GaloisField p f)) ≤ m + 1 := by
          calc finrank (GaloisField p f)
                ((fixSpace i ⊔ fixSpace i') : Submodule (GaloisField p f)
                  (Fin (m + 1) → GaloisField p f))
              ≤ finrank (GaloisField p f) (Fin (m + 1) → GaloisField p f) :=
                Submodule.finrank_le _
            _ = m + 1 := Module.finrank_fin_fun _
        rw [hdimW, hdimW'] at h1
        omega
      have hne : ((fixSpace i ⊓ fixSpace i') : Submodule (GaloisField p f)
            (Fin (m + 1) → GaloisField p f)) ≠ ⊥ := by
        intro hbot
        rw [hbot] at hdiminf
        simp at hdiminf
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      have hva : (a' : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField p f)) *ᵥ v = v :=
        ((hi.mem_iff_vec h2).mp haR).1 v hv.1
      have hvb : (b' : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField p f)) *ᵥ v = v :=
        ((hi'.mem_iff_vec h2).mp hbR).1 v hv.2
      have hωv : ω • v = v := by
        have hζb : ζ * b' = a' := by
          show a' * b'⁻¹ * b' = a'
          group
        have h1 : (a' : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField p f)) *ᵥ v =
            (ζ : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField p f)) *ᵥ v := by
          rw [← hζb, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hvb]
        rw [hva] at h1
        have h2 : (ζ : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField p f)) *ᵥ v = v :=
          h1.symm
        rw [← hζmat] at h2
        have h3 : (Matrix.scalar (Fin (m + 1)) ω) *ᵥ v = ω • v := by
          rw [← Matrix.smul_eq_mulVec]
          exact Matrix.Module.scalar_smul ω v
        rw [h3] at h2
        exact h2
      have hω1 : ω = 1 := by
        have hzero : (ω - 1) • v = 0 := by
          rw [sub_smul, one_smul, hωv, sub_self]
        have := (smul_eq_zero.mp hzero).resolve_right hv0
        exact sub_eq_zero.mp this
      apply Subtype.ext
      rw [← hζmat, hω1, map_one, Matrix.SpecialLinearGroup.coe_one]
  have hab : a' = b' := by
    have h : a' * b'⁻¹ = 1 := hζ1
    calc a' = a' * b'⁻¹ * b' := by group
      _ = b' := by rw [h, one_mul]
  have haR' : a' ∈ R := haR
  have hbR' : b' ∈ R' := hbR
  have hbR'a : a' ∈ R' := hab.symm ▸ hbR'
  have hR_eq : R = R' :=
    uc22s2112r34_isLongRootSL2_eq_of_mem (K := GaloisField p f) (p := p) (n := m + 1)
      (hn := by omega) hp h2 hi hi' haR' hbR'a ha1' hxr hxp har'
  rw [hRK, hR'K, hR_eq]

theorem uc22s2112r34_eq_of_mem_inf_psl {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 4 ≤ n)
    (hadm : StatedLieAdmissible .PSL n p f) (hX : CFSG.Blueprint.LieModel X .PSL n p f)
    {K K' : Subgroup X} (hK : IsFundamentalOver (p ^ f) K) (hK' : IsFundamentalOver (p ^ f) K')
    {x : X} (hxK : x ∈ K) (hxK' : x ∈ K') (hxr : (orderOf x).Prime) (hx2 : orderOf x ≠ 2)
    (hxp : orderOf x ≠ p) : K = K' :=
  uc22s2112r34_eq_of_mem_inf_psl_aux (fact := ⟨hp⟩) hp hp2 hn hadm hX hK hK' hxK hxK' hxr hx2 hxp

end CFSG.LocalAnalysis.UniquenessCase.UC22
