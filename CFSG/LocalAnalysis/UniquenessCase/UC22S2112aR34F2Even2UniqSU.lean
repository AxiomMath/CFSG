module

public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLie
import CFSG.ClassicalInvolution.Q3.Q3URClose
import CFSG.GH74.Orders.LieType
import CFSG.LocalAnalysis.UniquenessCase.UC6N588D3
import CFSG.Timmesfeld.Orders.Distinct
import CFSG.LocalAnalysis.UniquenessCase.UC22FunCountAmbient
public import CFSG.ClassicalInvolution.RouteD.TypeULocal
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan Matrix Module
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open scoped MatrixGroups

private theorem uc22s2112r34_uniqsu_fix_eq_zero_of_mem
    {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}
    {hn : 2 ≤ n} {L : Subgroup (Su K p f n)} {i : Su K p f n}
    (hp2 : p ≠ 2) (h : IsLongRootSU2 K p f hn L i) {a : Su K p f n} (haL : a ∈ L)
    (ha1 : a ≠ 1) {r : ℕ} (hr : r.Prime) (hrp : r ≠ p) (har : a ^ r = 1)
    {v : Fin n → K} (hv : v ∈ minusSpaceSU i) (hav : suMat a *ᵥ v = v) : v = 0 := by
  obtain ⟨g, hL, rfl⟩ := h
  have haL' : a ∈ (rootSU2 K p f hn).map (MulAut.conj g).toMonoidHom := hL ▸ haL
  obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp haL'
  obtain ⟨A, rfl⟩ := MonoidHom.mem_range.mp hx
  have ha_eq : a = g * blockEmb K p f n 2 0 (by omega) A * g⁻¹ := by
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hxa.symm
  have ha1' : A ≠ 1 := by
    intro hA
    apply ha1
    rw [ha_eq, hA, map_one, mul_one, mul_inv_cancel]
  have hconj : ∀ m : ℕ, (g * blockEmb K p f n 2 0 (by omega) A * g⁻¹) ^ m =
      g * blockEmb K p f n 2 0 (by omega) (A ^ m) * g⁻¹ := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ, ih, pow_succ, map_mul]
        group
  have hAr : A ^ r = 1 := by
    apply blockEmb_injective (K := K) (p := p) (f := f) (m := n) (k := 2) (i := 0)
      (by omega)
    rw [map_one]
    have h1 : g * blockEmb K p f n 2 0 (by omega) (A ^ r) * g⁻¹ = 1 := by
      rw [← hconj r, ← ha_eq]
      exact har
    calc blockEmb K p f n 2 0 (by omega) (A ^ r) =
          g⁻¹ * (g * blockEmb K p f n 2 0 (by omega) (A ^ r) * g⁻¹) * g := by group
      _ = g⁻¹ * 1 * g := by rw [h1]
      _ = 1 := by group
  set u : Fin n → K := suMat g⁻¹ *ᵥ v with hu
  have hvu : suMat g *ᵥ u = v := by
    rw [hu, Matrix.mulVec_mulVec, suMat_mul_suMat_inv, Matrix.one_mulVec]
  have hcoe : suMat a = suMat g * blockMat n 0 (suMat A) * suMat g⁻¹ := by
    rw [ha_eq, suMat_mul, suMat_mul, suMat_blockEmb]
  have hinj : Function.Injective (fun w : Fin n → K => suMat g *ᵥ w) := by
    intro y z hyz
    have h := congrArg (fun t => suMat g⁻¹ *ᵥ t) hyz
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, suMat_inv_mul_suMat,
      Matrix.one_mulVec, Matrix.one_mulVec] at h
    exact h
  have hfix_u : blockMat n 0 (suMat A) *ᵥ u = u := by
    apply hinj
    calc suMat g *ᵥ (blockMat n 0 (suMat A) *ᵥ u)
        = (suMat g * blockMat n 0 (suMat A)) *ᵥ u :=
          Matrix.mulVec_mulVec u (suMat g) (blockMat n 0 (suMat A))
      _ = (suMat a * suMat g) *ᵥ u := by
          rw [show suMat g * blockMat n 0 (suMat A) = suMat a * suMat g by
            rw [hcoe, Matrix.mul_assoc, Matrix.mul_assoc, suMat_inv_mul_suMat,
              Matrix.mul_one]]
      _ = suMat a *ᵥ (suMat g *ᵥ u) :=
          (Matrix.mulVec_mulVec u (suMat a) (suMat g)).symm
      _ = suMat a *ᵥ v := by rw [hvu]
      _ = v := hav
      _ = suMat g *ᵥ u := hvu.symm
  have hv' : v ∈ eigSpace (suMat g * negBlock K n 0 * suMat g⁻¹) (-1) := by
    simpa only [minusSpaceSU, suMat_mul, suMat_rootInvSU] using hv
  have huV : u ∈ eigSpace (negBlock K n 0) (-1) := by
    have hmap := eigSpace_conj_aux (suMat_mul_suMat_inv g) (suMat_inv_mul_suMat g)
      (negBlock K n 0) (-1)
    rw [hmap] at hv'
    obtain ⟨m, hm, rfl⟩ := Submodule.mem_map.mp hv'
    simpa only [hu, Matrix.toLin'_apply, Matrix.mulVec_mulVec, suMat_inv_mul_suMat,
      Matrix.one_mulVec] using hm
  have hu_range : u ∈ LinearMap.range (Matrix.mulVecLin (blockSel K n 2 0)) := by
    rwa [← eigSpace_negBlock_neg_one (K := K) (n := n)
      (two_ne_zero_of_charP_ne_two (K := K) hp2) (j := 0) (by omega : 0 + 2 ≤ n)]
  obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hu_range
  rw [Matrix.mulVecLin_apply] at hw
  have hAw : suMat A *ᵥ w = w := by
    ext x
    have h1 := blockMat_mulVec_blockIdx (F := K) (h := (by omega : 0 + 2 ≤ n))
      (suMat A) u x
    rw [hfix_u] at h1
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
    have hpow : (suToSL (CFSG.LieType.BorelTits.unitaryInvolution K p f) 2 A) ^ p = 1 :=
      CFSG.Wreathed.OriginalAllPrime.V4InputsW.pow_char_eq_one_of_mulVec_eq hw0 hAw
    have hAp : A ^ p = 1 := suToSL_injective (by rw [map_pow, hpow, map_one])
    have hcop : Nat.Coprime p r :=
      (Nat.coprime_primes Fact.out hr).mpr (Ne.symm hrp)
    have horder : orderOf A = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hAp)
        (orderOf_dvd_of_pow_eq_one hAr)
    exact ha1' (orderOf_eq_one_iff.mp horder)

private theorem uc22s2112r34_uniqsu_fixSet_eq_fixSpace
    {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
    (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) {n : ℕ} {hn : 2 ≤ n}
    {L : Subgroup (Su K p f n)} {i : Su K p f n} (h : IsLongRootSU2 K p f hn L i)
    {a : Su K p f n} (haL : a ∈ L) (ha1 : a ≠ 1) {r : ℕ} (hr : r.Prime) (hrp : r ≠ p)
    (har : a ^ r = 1) :
    {v : Fin n → K | suMat a *ᵥ v = v} = fixSpaceSU i := by
  ext v
  constructor
  · intro hv
    change suMat a *ᵥ v = v at hv
    have hvsup : v ∈ minusSpaceSU i ⊔ fixSpaceSU i := by
      rw [(h.isCompl hp2).sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨m, hm, w, hw, rfl⟩ := Submodule.mem_sup.mp hvsup
    have haw : suMat a *ᵥ w = w := by
      have := (h.mem_iff_fix hK hp2).mp haL w hw
      simpa only [suMat_smul] using this
    have ham : suMat a *ᵥ m = m := by
      rw [Matrix.mulVec_add, haw] at hv
      exact add_right_cancel hv
    have hm0 : m = 0 :=
      uc22s2112r34_uniqsu_fix_eq_zero_of_mem hp2 h haL ha1 hr hrp har hm ham
    rw [hm0, zero_add]
    exact hw
  · intro hv
    change suMat a *ᵥ v = v
    have := (h.mem_iff_fix hK hp2).mp haL v hv
    simpa only [suMat_smul] using this

theorem uc22s2112r34_isLongRootSU2_eq_of_mem {K : Type} [Field K] [Finite K] {p f : ℕ}
    [Fact p.Prime] [CharP K p] (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) {n : ℕ}
    {hn : 2 ≤ n} {L L' : Subgroup (Su K p f n)} {i i' : Su K p f n}
    (h : IsLongRootSU2 K p f hn L i) (h' : IsLongRootSU2 K p f hn L' i')
    {a : Su K p f n} (haL : a ∈ L) (haL' : a ∈ L') (ha1 : a ≠ 1) {r : ℕ} (hr : r.Prime)
    (hrp : r ≠ p) (har : a ^ r = 1) : L = L' := by
  have hfix := uc22s2112r34_uniqsu_fixSet_eq_fixSpace hK hp2 h haL ha1 hr hrp har
  have hfix' := uc22s2112r34_uniqsu_fixSet_eq_fixSpace hK hp2 h' haL' ha1 hr hrp har
  have hW : fixSpaceSU i = fixSpaceSU i' := by
    apply Submodule.ext
    intro v
    change v ∈ (fixSpaceSU i : Set (Fin n → K)) ↔
      v ∈ (fixSpaceSU i' : Set (Fin n → K))
    rw [← hfix, ← hfix']
  apply le_antisymm
  · intro x hx
    rw [h.mem_iff_fix hK hp2] at hx
    rw [h'.mem_iff_fix hK hp2]
    rwa [hW] at hx
  · intro x hx
    rw [h'.mem_iff_fix hK hp2] at hx
    rw [h.mem_iff_fix hK hp2]
    rwa [← hW] at hx

private theorem uc22s2112r34_uniqsu_ord_ne_one {q n : ℕ} (hq : 3 ≤ q) (hodd : Odd q)
    (hn : 4 ≤ n) : ordTwistedA (n - 1) q ≠ ordA 1 q := by
  have hdvd : q ^ 2 ∣ ordTwistedA (n - 1) q := by
    let C : ℕ := ∏ j ∈ Finset.Icc 2 n, (q ^ j - (-1 : ℤ) ^ j).toNat
    let d : ℕ := Nat.gcd n (q + 1)
    have hterm : (q ^ 2 - (-1 : ℤ) ^ 2).toNat = q ^ 2 - 1 := by
      simpa using
        CFSG.Timmesfeld.Orders.toNat_pow_sub_neg_one_pow_of_even (q := q) (i := 2)
          (by omega) even_two
    have hdvdC : d ∣ C := by
      have h1 : d ∣ q + 1 := Nat.gcd_dvd_right _ _
      have h2 : q + 1 ∣ q ^ 2 - 1 := by
        have h : q ^ 2 - 1 = (q + 1) * (q - 1) := by
          simpa using Nat.sq_sub_sq q 1
        rw [h]
        exact dvd_mul_right _ _
      have h3 : q ^ 2 - 1 ∣ C := by
        rw [← hterm]
        exact Finset.dvd_prod_of_mem (fun j => (q ^ j - (-1 : ℤ) ^ j).toNat)
          (by simp only [Finset.mem_Icc]; omega)
      exact h1.trans (h2.trans h3)
    have hdvdnum : d ∣ q ^ ((n - 1) * n / 2) * C :=
      dvd_mul_of_dvd_right hdvdC _
    have hmul : ordTwistedA (n - 1) q * d = q ^ ((n - 1) * n / 2) * C := by
      rw [CFSG.Open.ordTwistedA]
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
    have hcopq : Nat.Coprime q (q + 1) := by
      rw [Nat.coprime_iff_gcd_eq_one]
      have hd : Nat.gcd q (q + 1) ∣ (q + 1) - q :=
        Nat.dvd_sub (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)
      rw [show q + 1 - q = 1 by omega] at hd
      exact Nat.dvd_one.mp hd
    have hcop : Nat.Coprime (q ^ 2) d :=
      (hcopq.pow_left 2).of_dvd_right (Nat.gcd_dvd_right _ _)
    have hdiv : q ^ 2 ∣ ordTwistedA (n - 1) q * d := by
      rw [hmul]
      exact hdvdq.trans (dvd_mul_right _ _)
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


private theorem uc22s2112r34_uniqsu_eq_of_mem_inf_psu_aux {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] {n p f : ℕ} [fact : Fact p.Prime]
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : 4 ≤ n)
    (hadm : StatedLieAdmissible .PSU n p f) (hX : CFSG.Blueprint.LieModel X .PSU n p f)
    {K K' : Subgroup X} (hK : IsFundamentalOver (p ^ f) K) (hK' : IsFundamentalOver (p ^ f) K')
    {x : X} (hxK : x ∈ K) (hxK' : x ∈ K') (hxr : (orderOf x).Prime) (hx2 : orderOf x ≠ 2)
    (hxp : orderOf x ≠ p) : K = K' := by
  classical
  obtain ⟨ψ, hψ, hker⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    .PSU n p f Fact.out hp2 (by trivial) hadm X hX
  have hf : 1 ≤ f := hadm.2.1
  have hq3 : 3 ≤ p ^ f := by
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    exact hp3.trans (Nat.le_self_pow (by omega : f ≠ 0) p)
  have hoddq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hL2 : ¬ IsL2Over17 (X ⧸ Subgroup.center X) (p ^ f) := by
    intro hL2
    obtain ⟨r, f', hr, hr2, hq, hf', hm2⟩ := hL2
    have hcardX : Nat.card X = ordTwistedA (n - 1) (p ^ f) :=
      CFSG.GH74.card_of_lieModel_PSU (by omega) hp2 hX
    have hcardQ : Nat.card (X ⧸ Subgroup.center X) = ordA 1 (r ^ f') := by
      simpa using CFSG.GH74.card_of_lieModel_PSL (n := 2) (p := r) (f := f')
        (by norm_num) hm2
    have hZbot : Subgroup.center X = ⊥ := by
      rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center X) with hbot | htop
      · exact hbot
      · exfalso
        have hsub : Subsingleton (X ⧸ Subgroup.center X) := by
          rw [htop]
          exact QuotientGroup.subsingleton_quotient_top
        have hcard1 : Nat.card (X ⧸ Subgroup.center X) = 1 :=
          Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨(1 : X ⧸ Subgroup.center X)⟩⟩
        have hq1 : ordA 1 (r ^ f') = 1 := by
          rw [← hcardQ, hcard1]
        have hr3 : 3 ≤ r := by
          have := hr.two_le
          omega
        have hq3' : 3 ≤ r ^ f' :=
          hr3.trans (Nat.le_self_pow (by omega : f' ≠ 0) r)
        have htwo : 2 * ordA 1 (r ^ f') = r ^ f' * ((r ^ f') ^ 2 - 1) :=
          CFSG.LocalAnalysis.UniquenessCase.UC6.N588.two_mul_ordA_one
            ((hr.odd_of_ne_two hr2).pow)
        have h2 : 2 = r ^ f' * ((r ^ f') ^ 2 - 1) := by
          rw [← htwo, hq1, mul_one]
        have h9 : 9 ≤ (r ^ f') ^ 2 := by
          calc 9 = 3 ^ 2 := by norm_num
            _ ≤ (r ^ f') ^ 2 := Nat.pow_le_pow_left hq3' 2
        have hq2pos : 8 ≤ (r ^ f') ^ 2 - 1 := by omega
        have hprod : 24 ≤ r ^ f' * ((r ^ f') ^ 2 - 1) := by
          calc 24 = 3 * 8 := by norm_num
            _ ≤ r ^ f' * ((r ^ f') ^ 2 - 1) := Nat.mul_le_mul hq3' hq2pos
        omega
    have heq : ordTwistedA (n - 1) (p ^ f) = ordA 1 (p ^ f) := by
      calc ordTwistedA (n - 1) (p ^ f) = Nat.card X := hcardX.symm
        _ = Nat.card (X ⧸ Subgroup.center X) := by
            rw [hZbot]
            exact (Nat.card_congr (QuotientGroup.quotientBot (G := X)).toEquiv).symm
        _ = ordA 1 (r ^ f') := hcardQ
        _ = ordA 1 (p ^ f) := by rw [← hq]
    exact uc22s2112r34_uniqsu_ord_ne_one hq3 hoddq hn heq
  obtain ⟨R, hR, hRK, hRker⟩ :=
    exists_mem_fundamentalSubgroups_of_isFundamentalOver_general Fact.out hp2 hadm hX
      (by trivial) (by simp) hL2 ψ hψ hker hK
  obtain ⟨R', hR', hR'K, hR'ker⟩ :=
    exists_mem_fundamentalSubgroups_of_isFundamentalOver_general Fact.out hp2 hadm hX
      (by trivial) (by simp) hL2 ψ hψ hker hK'
  let F := GaloisField p (2 * f)
  have hFcard : Nat.card F = (p ^ f) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul p f hf
  have hqne2 : p ^ f ≠ 2 :=
    CFSG.ClassicalInvolution.Models.prime_pow_ne_two_of_ne_two hp2 f
  obtain ⟨e, he⟩ := CFSG.ClassicalInvolution.RouteD.psu_model_equiv hp2 hadm
  let L : Subgroup (Su F p f n) := R.map e.toMonoidHom
  let L' : Subgroup (Su F p f n) := R'.map e.toMonoidHom
  obtain ⟨i, hi⟩ := (he R).mp hR
  obtain ⟨i', hi'⟩ := (he R').mp hR'
  have hxKmap : x ∈ R.map ψ := by rw [← hRK]; exact hxK
  have hxK'map : x ∈ R'.map ψ := by rw [← hR'K]; exact hxK'
  obtain ⟨a, haR, hψa⟩ := Subgroup.mem_map.mp hxKmap
  obtain ⟨b, hbR, hψb⟩ := Subgroup.mem_map.mp hxK'map
  have ha_r : a ^ orderOf x = 1 := by
    have hmem : a ^ orderOf x ∈ R ⊓ ψ.ker := by
      refine ⟨pow_mem haR _, ?_⟩
      change ψ (a ^ orderOf x) = 1
      rw [map_pow, hψa, pow_orderOf_eq_one]
    rw [hRker] at hmem
    simpa using hmem
  have hb_r : b ^ orderOf x = 1 := by
    have hmem : b ^ orderOf x ∈ R' ⊓ ψ.ker := by
      refine ⟨pow_mem hbR _, ?_⟩
      change ψ (b ^ orderOf x) = 1
      rw [map_pow, hψb, pow_orderOf_eq_one]
    rw [hR'ker] at hmem
    simpa using hmem
  have ha1 : a ≠ 1 := by
    intro ha
    have hx1 : x = 1 := by rw [← hψa, ha, map_one]
    exact hxr.ne_one (by rw [hx1, orderOf_one])
  let ζ := a * b⁻¹
  have hζker : ζ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker]
    change ψ (a * b⁻¹) = 1
    rw [map_mul, map_inv, hψa, hψb, mul_inv_cancel]
  have hζcenter := hker hζker
  have hζcomm : Commute ζ b := (Subgroup.mem_center_iff.mp hζcenter b).symm
  have haeq : a = ζ * b := by
    change a = (a * b⁻¹) * b
    group
  have hζpow : ζ ^ orderOf x = 1 := by
    have h1 : a ^ orderOf x = (ζ ^ orderOf x) * (b ^ orderOf x) := by
      rw [haeq]
      exact hζcomm.mul_pow (orderOf x)
    rw [ha_r, hb_r, mul_one] at h1
    exact h1.symm
  have hζcenterSu : e ζ ∈ Subgroup.center (Su F p f n) := by
    rw [← Subgroup.map_center_eq e]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hζcenter
  obtain ⟨c, hc⟩ :=
    CFSG.ClassicalInvolution.Q3.Q3W.exists_scalar_of_mem_center_su3
      (K := F) (p := p) (f := f) hFcard hqne2 (by omega : 3 ≤ n) hζcenterSu
  have hζsmul : ∀ m : ℕ, suMat ((e ζ) ^ m) = (suMat (e ζ)) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, pow_succ, suMat_mul, ih]
  have hc_r : c ^ orderOf x = 1 := by
    have hmap : (e ζ) ^ orderOf x = 1 := by rw [← map_pow, hζpow, map_one]
    have h := congrArg (fun z : Su F p f n => suMat z) hmap
    rw [hζsmul (orderOf x), hc, suMat_one,
      ← map_pow (Matrix.scalar (Fin n)) c (orderOf x)] at h
    have h0 := congrFun (congrFun h ⟨0, by omega⟩) ⟨0, by omega⟩
    simpa using h0
  have hζ1_of_c1 : c = 1 → ζ = 1 := by
    intro hc1
    have hζ1Su : e ζ = 1 := by
      apply suMat_injective
      rw [hc, hc1, suMat_one]
      exact map_one (Matrix.scalar (Fin n))
    exact e.injective (by simpa using hζ1Su)
  have hodd : Odd (orderOf x) := hxr.odd_of_ne_two hx2
  have hab : a = b := by
    by_cases hn4 : n = 4
    · have hc4 : c ^ 4 = 1 := by
        have h := det_suMat (e ζ)
        rw [hc] at h
        rw [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const,
          Finset.card_univ, Fintype.card_fin] at h
        simpa [hn4] using h
      have hcop : Nat.Coprime 4 (orderOf x) := by
        have h2r : Nat.Coprime 2 (orderOf x) :=
          (Nat.coprime_primes Nat.prime_two hxr).mpr (by omega)
        simpa using h2r.pow_left 2
      have hc1 : c = 1 :=
        (pow_eq_one_iff_of_coprime hcop).mp ⟨hc4, hc_r⟩
      have hζ1 : ζ = 1 := hζ1_of_c1 hc1
      have h : a * b⁻¹ = 1 := hζ1
      exact mul_inv_eq_one.mp h
    · have hn5 : 5 ≤ n := by omega
      have h2F : (2 : F) ≠ 0 :=
        CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField (2 * f) hp2
      have hdimW : finrank F (fixSpaceSU i) = n - 2 := by
        have h1 := Submodule.finrank_add_eq_of_isCompl (hi.isCompl hp2)
        have h2 : finrank F (minusSpaceSU i) = 2 := hi.finrank_minusSpaceSU h2F
        have h3 : finrank F (Fin n → F) = n := Module.finrank_fin_fun _
        dsimp only [F] at *
        omega
      have hdimW' : finrank F (fixSpaceSU i') = n - 2 := by
        have h1 := Submodule.finrank_add_eq_of_isCompl (hi'.isCompl hp2)
        have h2 : finrank F (minusSpaceSU i') = 2 := hi'.finrank_minusSpaceSU h2F
        have h3 : finrank F (Fin n → F) = n := Module.finrank_fin_fun _
        dsimp only [F] at *
        omega
      have hdiminf : 0 < finrank F
          ((fixSpaceSU i ⊓ fixSpaceSU i') : Submodule F (Fin n → F)) := by
        have h1 := Submodule.finrank_sup_add_finrank_inf_eq
          (fixSpaceSU i : Submodule F (Fin n → F))
          (fixSpaceSU i' : Submodule F (Fin n → F))
        have hsup : finrank F
            ((fixSpaceSU i ⊔ fixSpaceSU i') : Submodule F (Fin n → F)) ≤ n := by
          calc finrank F ((fixSpaceSU i ⊔ fixSpaceSU i') : Submodule F (Fin n → F))
              ≤ finrank F (Fin n → F) := Submodule.finrank_le _
            _ = n := Module.finrank_fin_fun _
        rw [hdimW, hdimW'] at h1
        dsimp only [F] at *
        omega
      have hne : ((fixSpaceSU i ⊓ fixSpaceSU i') : Submodule F (Fin n → F)) ≠ ⊥ := by
        intro hbot
        rw [hbot] at hdiminf
        simp at hdiminf
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      have haL : e a ∈ L := Subgroup.mem_map_of_mem e.toMonoidHom haR
      have hbL' : e b ∈ L' := Subgroup.mem_map_of_mem e.toMonoidHom hbR
      have hva : suMat (e a) *ᵥ v = v := by
        have := (hi.mem_iff_fix hFcard hp2).mp haL v hv.1
        simpa only [suMat_smul] using this
      have hvb : suMat (e b) *ᵥ v = v := by
        have := (hi'.mem_iff_fix hFcard hp2).mp hbL' v hv.2
        simpa only [suMat_smul] using this
      have hea : suMat (e a) = suMat (e ζ) * suMat (e b) := by
        rw [haeq, map_mul, suMat_mul]
      have hcv : c • v = v := by
        have h1 : suMat (e a) *ᵥ v = suMat (e ζ) *ᵥ (suMat (e b) *ᵥ v) := by
          rw [hea, ← Matrix.mulVec_mulVec]
        rw [hva, hvb] at h1
        have h3 : (Matrix.scalar (Fin n) c) *ᵥ v = c • v := by
          rw [← Matrix.smul_eq_mulVec]
          exact Matrix.Module.scalar_smul c v
        rw [hc, h3] at h1
        exact h1.symm
      have hc1 : c = 1 := by
        have hzero : (c - 1) • v = 0 := by
          rw [sub_smul, one_smul, hcv, sub_self]
        have := (smul_eq_zero.mp hzero).resolve_right hv0
        exact sub_eq_zero.mp this
      have hζ1 : ζ = 1 := hζ1_of_c1 hc1
      have h : a * b⁻¹ = 1 := hζ1
      exact mul_inv_eq_one.mp h
  have haL : e a ∈ L := Subgroup.mem_map_of_mem e.toMonoidHom haR
  have hbL' : e b ∈ L' := Subgroup.mem_map_of_mem e.toMonoidHom hbR
  have haL' : e a ∈ L' := by
    rw [show e a = e b from congrArg e hab]
    exact hbL'
  have ha1Su : e a ≠ 1 := by
    intro ha1e
    apply ha1
    exact e.injective (by simpa using ha1e)
  have harSu : (e a) ^ orderOf x = 1 := by
    rw [← map_pow, ha_r, map_one]
  have hLL' : L = L' :=
    uc22s2112r34_isLongRootSU2_eq_of_mem hFcard hp2 hi hi' haL haL' ha1Su hxr hxp harSu
  have hR_eq : R = R' := Subgroup.map_injective e.injective (by simpa [L, L'] using hLL')
  rw [hRK, hR'K, hR_eq]

theorem uc22s2112r34_eq_of_mem_inf_psu {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 4 ≤ n)
    (hadm : StatedLieAdmissible .PSU n p f) (hX : CFSG.Blueprint.LieModel X .PSU n p f)
    {K K' : Subgroup X} (hK : IsFundamentalOver (p ^ f) K) (hK' : IsFundamentalOver (p ^ f) K')
    {x : X} (hxK : x ∈ K) (hxK' : x ∈ K') (hxr : (orderOf x).Prime) (hx2 : orderOf x ≠ 2)
    (hxp : orderOf x ≠ p) : K = K' :=
  uc22s2112r34_uniqsu_eq_of_mem_inf_psu_aux (fact := ⟨hp⟩) hp hp2 hn hadm hX hK hK' hxK hxK' hxr
    hx2 hxp

end CFSG.LocalAnalysis.UniquenessCase.UC22
