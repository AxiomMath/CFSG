module

public import CFSG.LieType.Ree.SuzukiBorelStructure
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiRootAutomorphismUnipotent
public import CFSG.RankThree.PartTwo.KFacts.LandazuriSeitzProof
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint CFSG.LieType.Ree CFSG.ShultStronglyClosedTI.SuzukiRootAutomorphism
open scoped commutatorElement
open CFSG.RankThree.PartTwo.KFacts.LandazuriSeitzProof
  (exists_common_eigenvector injective_mul_char)

theorem suzuki_borel_cross_char_degree_two_mul
    {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    {k : Type} [Field k] (h2 : (2 : k) ≠ 0)
    {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (rho : suzukiGroup a K →* Module.End k V) (hrho : Function.Injective rho) :
    2 * (Nat.card K - 1) ≤ Module.finrank k V := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨h2K, -, -⟩ := suzuki_frob_data a hK
  have h2x : ∀ x : K, x + x = 0 := fun x => by rw [← two_mul, h2K, zero_mul]
  have hθ0 : 2 ^ (a + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  let P : K → Module.End k V := fun b => rho (suzukiSElt a K 0 b)
  have hS_add : ∀ b c : K,
      suzukiSElt a K 0 b * suzukiSElt a K 0 c = suzukiSElt a K 0 (b + c) := by
    intro b c
    simpa [zero_pow hθ0] using suzukiSElt_mul hK (0 : K) b (0 : K) c
  have hP_mul : ∀ b c : K, P b * P c = P (b + c) := by
    intro b c
    change rho (suzukiSElt a K 0 b) * rho (suzukiSElt a K 0 c) =
      rho (suzukiSElt a K 0 (b + c))
    rw [← map_mul, hS_add]
  have hP_sq : ∀ b : K, P b * P b = 1 := by
    intro b
    rw [hP_mul b b, h2x b]
    change rho (suzukiSElt a K 0 0) = 1
    rw [suzukiSElt_zero_zero hK, map_one]
  have hP_comm : ∀ b c : K, Commute (P b) (P c) := by
    intro b c
    show P b * P c = P c * P b
    rw [hP_mul b c, hP_mul c b, add_comm]
  have hP1_ne : P 1 ≠ 1 := by
    intro h
    have hS1 : suzukiSElt a K 0 1 = 1 := hrho (h.trans (map_one rho).symm)
    rw [← suzukiSElt_zero_zero hK] at hS1
    exact one_ne_zero (suzukiSElt_inj.1 hS1).2
  have hP1_sq : ∀ w : V, P 1 (P 1 w) = w := fun w => by
    have h := congrArg (fun f : Module.End k V => f w) (hP_sq 1)
    simpa [Module.End.mul_apply] using h
  obtain ⟨v₁, hv₁⟩ : ∃ v : V, P 1 v ≠ v := by
    by_contra! h
    exact hP1_ne (LinearMap.ext h)
  have hX : ∀ b : K, ∀ x ∈ LinearMap.ker (P 1 + 1), P b x ∈ LinearMap.ker (P 1 + 1) := by
    intro b x hx
    rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply] at hx ⊢
    rw [← Module.End.mul_apply, ← (hP_comm b 1).eq, Module.End.mul_apply, ← map_add, hx,
      map_zero]
  have hv₀X : v₁ - P 1 v₁ ∈ LinearMap.ker (P 1 + 1) := by
    rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, map_sub, hP1_sq]
    abel
  have hv₀ : v₁ - P 1 v₁ ≠ 0 := sub_ne_zero.mpr hv₁.symm
  obtain ⟨v, hvX, hv0, χ, hχ⟩ :=
    exists_common_eigenvector (A := K) (K := k) (V := V) P hP_comm hP_sq
      (LinearMap.ker (P 1 + 1)) hX hv₀X hv₀ Finset.univ
  have hv : ∀ b : K, P b v = χ b • v := fun b => hχ b (Finset.mem_univ b)
  have hP0 : P 0 = 1 := by
    change rho (suzukiSElt a K 0 0) = 1
    rw [suzukiSElt_zero_zero hK, map_one]
  have hχ1 : χ 1 = -1 := by
    apply smul_left_injective k hv0
    change χ 1 • v = (-1 : k) • v
    rw [← hv, neg_one_smul]
    rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply] at hvX
    exact eq_neg_of_add_eq_zero_left hvX
  have hχ0 : χ 0 = 1 := by
    apply smul_left_injective k hv0
    change χ 0 • v = (1 : k) • v
    rw [← hv 0, hP0, Module.End.one_apply, one_smul]
  have hχadd : ∀ b c : K, χ (b + c) = χ b * χ c := by
    intro b c
    apply smul_left_injective k hv0
    change χ (b + c) • v = (χ b * χ c) • v
    rw [← hv, ← hP_mul, Module.End.mul_apply, hv, map_smul, hv, smul_smul, mul_comm]
  have hχsq : ∀ b : K, χ b * χ b = 1 := by
    intro b
    rw [← hχadd b b, h2x b, hχ0]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hpow, -, -⟩ := suzuki_frobenius_exponents a K hK
  have hsurj : Function.Surjective (fun l : Kˣ => l ^ (2 ^ (a + 1) + 1 : ℤ)) := hpow.2
  choose lam hlam using hsurj
  have hlamval : ∀ μ : Kˣ, (lam μ : K) ^ (2 ^ (a + 1) + 1) = (μ : K) := by
    intro μ
    rw [← Units.val_pow_eq_pow_val]
    congr 1
    rw [← zpow_natCast]
    exact hlam μ
  have hconj : ∀ μ : Kˣ, ∀ b : K,
      (suzukiDElt a K (lam μ))⁻¹ * suzukiSElt a K 0 b * suzukiDElt a K (lam μ) =
        suzukiSElt a K 0 ((lam μ : K) ^ (2 ^ (a + 1) + 1) * b) := by
    intro μ b
    rw [suzukiDElt_conj hK]
    simp
  let w : Kˣ → V := fun μ => rho (suzukiDElt a K (lam μ)) v
  have hw : ∀ μ : Kˣ, ∀ b : K, P b (w μ) = χ ((μ : K) * b) • w μ := by
    intro μ b
    have hcomm : suzukiSElt a K 0 b * suzukiDElt a K (lam μ) =
        suzukiDElt a K (lam μ) *
          suzukiSElt a K 0 ((lam μ : K) ^ (2 ^ (a + 1) + 1) * b) := by
      rw [← hconj μ b]
      group
    change rho (suzukiSElt a K 0 b) (rho (suzukiDElt a K (lam μ)) v) =
      χ ((μ : K) * b) • rho (suzukiDElt a K (lam μ)) v
    rw [← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply, hv, map_smul,
      hlamval μ]
  have hw0 : ∀ μ : Kˣ, w μ ≠ 0 := by
    intro μ h0
    have hleft : rho (suzukiDElt a K (lam μ))⁻¹ (w μ) = v := by
      change rho (suzukiDElt a K (lam μ))⁻¹ (rho (suzukiDElt a K (lam μ)) v) = v
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    exact hv0 (by simpa [h0] using hleft.symm)
  have hχinj : Function.Injective (fun (μ : Kˣ) (b : K) => χ ((μ : K) * b)) :=
    injective_mul_char (F := K) (K := k) (χ := χ) h2 hχadd hχsq hχ1
  let ψ : Kˣ → K → k := fun μ b => χ ((μ : K) * b)
  let W : Kˣ → Submodule k V := fun μ => ⨅ b : K, Module.End.eigenspace (P b) (ψ μ b)
  have hwW : ∀ μ, w μ ∈ W μ := by
    intro μ
    dsimp only [W]
    rw [Submodule.mem_iInf]
    intro b
    rw [Module.End.mem_eigenspace_iff]
    simpa only [ψ] using hw μ b
  have hWinv : ∀ (r : K) (μ : Kˣ), ∀ x ∈ W μ,
      rho (suzukiSElt a K r 0) x ∈ W μ := by
    intro r μ x hx
    dsimp only [W] at hx ⊢
    rw [Submodule.mem_iInf] at hx ⊢
    intro b
    have hxb : x ∈ Module.End.eigenspace (P b) (ψ μ b) := hx b
    rw [Module.End.mem_eigenspace_iff] at hxb ⊢
    calc
      P b (rho (suzukiSElt a K r 0) x)
          = rho (suzukiSElt a K 0 b) (rho (suzukiSElt a K r 0) x) := rfl
      _ = rho (suzukiSElt a K 0 b * suzukiSElt a K r 0) x := by
            rw [← Module.End.mul_apply, ← map_mul]
      _ = rho (suzukiSElt a K r 0 * suzukiSElt a K 0 b) x := by
            rw [suzukiSElt_zero_commute hK b r 0]
      _ = rho (suzukiSElt a K r 0) (rho (suzukiSElt a K 0 b) x) := by
            rw [map_mul, Module.End.mul_apply]
      _ = rho (suzukiSElt a K r 0) (ψ μ b • x) := by rw [hxb]
      _ = ψ μ b • rho (suzukiSElt a K r 0) x := by rw [map_smul]
  have hmu_mul : ∀ μ : Kˣ, (μ : K) * ((μ⁻¹ : Kˣ) : K) = 1 := by
    intro μ
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hψneg : ∀ μ : Kˣ, ψ μ ((μ⁻¹ : Kˣ) : K) = -1 := by
    intro μ
    dsimp only [ψ]
    rw [hmu_mul μ, hχ1]
  obtain ⟨h0, hh0⟩ := exists_add_pow_ne_zero (a := a) (K := K) hK ha
  have hden : h0 + h0 ^ 2 ^ (a + 1) ≠ 0 := hh0
  have hinj_rho : ∀ g : suzukiGroup a K, Function.Injective (rho g) := by
    intro g x y hxy
    have h := congrArg (fun z => rho g⁻¹ z) hxy
    simpa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] using h
  have hneg1 : (-1 : k) ≠ 1 := fun h => h2 (by linear_combination -h)
  have hdim2 : ∀ μ : Kˣ, 2 ≤ Module.finrank k (W μ) := by
    intro μ
    by_contra hlt
    have hle1 : Module.finrank k (W μ) ≤ 1 := by omega
    have hWne : W μ ≠ ⊥ := by
      intro hbot
      exact hw0 μ (by simpa [hbot] using hwW μ)
    have hfin_ne0 : Module.finrank k (W μ) ≠ 0 := by
      intro hzero
      exact hWne (Submodule.finrank_eq_zero.mp hzero)
    have hdim1 : Module.finrank k (W μ) = 1 := by omega
    let num : K := ((μ⁻¹ : Kˣ) : K)
    let t : Kˣ := Units.mk0 (num / (h0 + h0 ^ 2 ^ (a + 1)))
      (div_ne_zero (Units.ne_zero (μ⁻¹)) hden)
    let c' : K := (lam t : K)
    have hc' : c' ^ (2 ^ (a + 1) + 1) = num / (h0 + h0 ^ 2 ^ (a + 1)) := by
      dsimp only [c']
      rw [hlamval t]
      simp [t, num]
    let a' : K := h0 * c'
    have hB : a' ^ (2 ^ (a + 1)) * c' + c' ^ (2 ^ (a + 1)) * a' = num := by
      have h1 : a' ^ (2 ^ (a + 1)) * c' =
          h0 ^ (2 ^ (a + 1)) * c' ^ (2 ^ (a + 1) + 1) := by
        dsimp only [a']
        rw [mul_pow, pow_succ]
        ring
      have h2' : c' ^ (2 ^ (a + 1)) * a' = h0 * c' ^ (2 ^ (a + 1) + 1) := by
        dsimp only [a']
        rw [pow_succ]
        ring
      rw [h1, h2', hc', ← add_mul, add_comm (h0 ^ 2 ^ (a + 1)) h0,
        mul_div_cancel₀ num hden]
    let u : suzukiGroup a K := suzukiSElt a K a' 0
    let v : suzukiGroup a K := suzukiSElt a K c' 0
    have hcommU : ⁅unipotentElt a K a' 0, unipotentElt a K c' 0⁆ =
        unipotentElt a K 0 num := by
      rw [commutatorElement_unipotentElt hK, hB]
    have hcommG : ⁅u, v⁆ = suzukiSElt a K 0 num := by
      have h := congrArg (fun x : suzukiU a K => (x : suzukiGroup a K)) hcommU
      simpa [u, v, unipotentElt, commutatorElement_def] using h
    have hwR : w μ ∈ W μ := hwW μ
    have hxW : (⟨w μ, hwR⟩ : W μ) ≠ 0 := by
      intro hz
      exact hw0 μ (congrArg Subtype.val hz)
    have huW : rho u (w μ) ∈ W μ := by
      simpa only [u] using hWinv a' μ (w μ) hwR
    have hvW : rho v (w μ) ∈ W μ := by
      simpa only [v] using hWinv c' μ (w μ) hwR
    obtain ⟨cu, hcuW⟩ := exists_smul_eq_of_finrank_eq_one (K := k) (V := W μ) hdim1 hxW
      (⟨rho u (w μ), huW⟩ : W μ)
    obtain ⟨cv, hcvW⟩ := exists_smul_eq_of_finrank_eq_one (K := k) (V := W μ) hdim1 hxW
      (⟨rho v (w μ), hvW⟩ : W μ)
    have hcu : rho u (w μ) = cu • w μ := (congrArg Subtype.val hcuW).symm
    have hcv : rho v (w μ) = cv • w μ := (congrArg Subtype.val hcvW).symm
    have hcu0 : cu ≠ 0 := by
      intro hc0
      have hz : rho u (w μ) = 0 := by rw [hcu, hc0, zero_smul]
      exact hw0 μ (hinj_rho u (hz.trans (map_zero (rho u)).symm))
    have hcv0 : cv ≠ 0 := by
      intro hc0
      have hz : rho v (w μ) = 0 := by rw [hcv, hc0, zero_smul]
      exact hw0 μ (hinj_rho v (hz.trans (map_zero (rho v)).symm))
    have hvv : ∀ y : V, rho v (rho v⁻¹ y) = y := fun y => by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    have huu : ∀ y : V, rho u (rho u⁻¹ y) = y := fun y => by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    have huinv_w : rho u⁻¹ (w μ) = cu⁻¹ • w μ := by
      apply hinj_rho u
      rw [huu, map_smul, hcu, smul_smul, inv_mul_cancel₀ hcu0, one_smul]
    have hvinv_w : rho v⁻¹ (w μ) = cv⁻¹ • w μ := by
      apply hinj_rho v
      rw [hvv, map_smul, hcv, smul_smul, inv_mul_cancel₀ hcv0, one_smul]
    have hfix_order : rho (u * v * u⁻¹ * v⁻¹) (w μ) = w μ := by
      simp only [map_mul, Module.End.mul_apply]
      calc
        rho u (rho v (rho u⁻¹ (rho v⁻¹ (w μ))))
            = rho u (rho v (rho u⁻¹ (cv⁻¹ • w μ))) := by rw [hvinv_w]
        _ = rho u (rho v (cv⁻¹ • rho u⁻¹ (w μ))) := by rw [map_smul]
        _ = rho u (rho v (cv⁻¹ • (cu⁻¹ • w μ))) := by rw [huinv_w]
        _ = rho u (rho v ((cv⁻¹ * cu⁻¹) • w μ)) := by rw [smul_smul]
        _ = rho u ((cv⁻¹ * cu⁻¹) • rho v (w μ)) := by rw [map_smul]
        _ = rho u ((cv⁻¹ * cu⁻¹) • (cv • w μ)) := by rw [hcv]
        _ = rho u (((cv⁻¹ * cu⁻¹) * cv) • w μ) := by rw [smul_smul]
        _ = (((cv⁻¹ * cu⁻¹) * cv) • rho u (w μ)) := by rw [map_smul]
        _ = (((cv⁻¹ * cu⁻¹) * cv) • (cu • w μ)) := by rw [hcu]
        _ = ((((cv⁻¹ * cu⁻¹) * cv) * cu) • w μ) := by rw [smul_smul]
        _ = w μ := by
              have hscalar : (((cv⁻¹ * cu⁻¹) * cv) * cu) = (1 : k) := by
                field_simp [hcu0, hcv0]
              rw [hscalar, one_smul]
    have hfix : rho (⁅u, v⁆) (w μ) = w μ := by
      rw [commutatorElement_def]
      exact hfix_order
    have hfix2 : rho (⁅u, v⁆) (w μ) = -w μ := by
      rw [hcommG]
      change P num (w μ) = -w μ
      rw [hw μ num]
      have hψnum : χ ((μ : K) * num) = -1 := by simpa [ψ, num] using hψneg μ
      rw [hψnum, neg_one_smul]
    have hweq : w μ = -w μ := hfix.symm.trans hfix2
    have hneg : (-1 : k) = 1 := by
      apply smul_left_injective k (hw0 μ)
      change (-1 : k) • w μ = (1 : k) • w μ
      rw [neg_one_smul, one_smul]
      exact hweq.symm
    exact hneg1 hneg
  have hψinj : Function.Injective ψ := by
    intro μ ν h
    exact hχinj (by simpa only [ψ] using h)
  have hindW : iSupIndep W := by
    change iSupIndep (fun μ : Kˣ => ⨅ b : K, Module.End.eigenspace (P b) (ψ μ b))
    exact (TauCeti.iSupIndep_iInf_eigenspace P).comp hψinj
  have hsum : Module.finrank k ↥(iSup W) = ∑ μ : Kˣ, Module.finrank k (W μ) :=
    TauCeti.finrank_iSup_eq_sum_finrank_of_iSupIndep hindW
  have hsum_const : (∑ _ : Kˣ, (2 : ℕ)) = 2 * Nat.card Kˣ := by
    rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, smul_eq_mul, mul_comm]
  have hmain : 2 * Nat.card Kˣ ≤ Module.finrank k V :=
    calc
      2 * Nat.card Kˣ = ∑ _ : Kˣ, (2 : ℕ) := hsum_const.symm
      _ ≤ ∑ μ, Module.finrank k (W μ) := Finset.sum_le_sum fun μ _ => hdim2 μ
      _ = Module.finrank k ↥(iSup W) := hsum.symm
      _ ≤ Module.finrank k V := Submodule.finrank_le _
  rwa [Nat.card_units] at hmain

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
