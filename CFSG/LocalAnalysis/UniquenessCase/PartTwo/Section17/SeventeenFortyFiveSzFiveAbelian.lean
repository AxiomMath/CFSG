module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1b
public import CFSG.LocalAnalysis.SteinbergCEFrobeniusComplementFixedVector
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenNineBasic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenNineSolv

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.RankThreeUC
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenNine
open scoped commutatorElement Pointwise IsMulCommutative

variable {G : Type} [Group G] [Finite G]


theorem false_of_abelian_chief (D : Data G) {A₁ A₂ B H R : Subgroup G}
    (hA₁ : Nat.card A₁ = 31) (hA₂ : Nat.card A₂ = 31)
    (hA₁₂ : A₁ ≤ centralizer (A₂ : Set G)) (hinf : A₁ ⊓ A₂ = ⊥)
    (hB : Nat.card B = 5) (hBn₁ : B ≤ normalizer (A₁ : Set G)) (hBn₂ : B ≤ normalizer (A₂ : Set G))
    (hfpf : ∀ b ∈ B, b ≠ 1 → ∀ a ∈ A₁ ⊔ A₂, a * b = b * a → a = 1)
    (hU₁ : A₁ ∈ uniqueSet D.M) (hU₂ : A₂ ∈ uniqueSet D.M) (hUB : B ∈ uniqueSet D.M)
    (hA₁H : A₁ ≤ H) (hA₂H : A₂ ≤ H) (hBH : B ≤ H)
    (hYR : kerM D.M H < R) (hRH : R ≤ H) (hRn : H ≤ normalizer (R : Set G))
    (hmin : ∀ W : Subgroup G, kerM D.M H ≤ W → W ≤ R → H ≤ normalizer (W : Set G) →
      W = kerM D.M H ∨ W = R)
    (hHMR : H ≤ (H ⊓ D.M) ⊔ R) (hab : ⁅R, R⁆ ≤ kerM D.M H) : False := by
  classical
  let Y : Subgroup G := kerM D.M H
  have hYH : Y ≤ H := RankThreeUC.WeakClosure.kerIn_le_left D.M H
  have hYM : Y ≤ D.M := RankThreeUC.WeakClosure.kerIn_le_right D.M H
  have hYn : H ≤ normalizer (Y : Set G) := le_normalizer_kerM D.M H
  have hRinfM : R ⊓ D.M ≤ Y := by
    have hRn' : R ≤ normalizer ((R ⊓ D.M : Subgroup G) : Set G) := by
      intro x hx
      rw [mem_normalizer_iff]
      intro w
      constructor
      · intro hw
        have hw' := Subgroup.mem_inf.1 hw
        have hc : ⁅x, w⁆ ∈ Y := hab (commutator_mem_commutator hx hw'.1)
        have e : x * w * x⁻¹ = ⁅x, w⁆ * w := by rw [commutatorElement_def]; group
        rw [e]
        exact Subgroup.mem_inf.2 ⟨R.mul_mem (hYR.le hc) hw'.1, D.M.mul_mem (hYM hc) hw'.2⟩
      · intro hw
        have hw' := Subgroup.mem_inf.1 hw
        have hc : ⁅x⁻¹, x * w * x⁻¹⁆ ∈ Y :=
          hab (commutator_mem_commutator (R.inv_mem hx) hw'.1)
        have e : w = ⁅x⁻¹, x * w * x⁻¹⁆ * (x * w * x⁻¹) := by
          rw [commutatorElement_def]; group
        rw [e]
        exact Subgroup.mem_inf.2 ⟨R.mul_mem (hYR.le hc) hw'.1, D.M.mul_mem (hYM hc) hw'.2⟩
    have hHn : H ≤ normalizer ((R ⊓ D.M : Subgroup G) : Set G) := by
      refine hHMR.trans (sup_le ?_ hRn')
      exact (le_inf (inf_le_left.trans hRn) (inf_le_right.trans le_normalizer)).trans
        inf_normalizer_le_normalizer_inf
    rcases hmin (R ⊓ D.M) (le_inf hYR.le hYM) inf_le_left hHn with h | h
    · exact h.le
    · exfalso
      exact (not_le_of_gt hYR) (le_kerM_of_normal hRH hRn (inf_eq_left.1 h))
  have hfixU : ∀ (U : Subgroup G), U ∈ uniqueSet D.M → U ≤ H → ∀ x ∈ R,
      (∀ u ∈ U, ⁅x, u⁆ ∈ Y) → x ∈ Y := by
    intro U hU hUH x hxR hxU
    have hUM : U ≤ D.M := hU.1
    have hstar := hstar_of_inU D (inU_iff_mem_uniqueSet.mpr hU)
    refine hRinfM ⟨hxR, ?_⟩
    have hxinv : x⁻¹ ∈ D.M := hstar x⁻¹ fun u hu => by
      have e : x⁻¹⁻¹ * u * x⁻¹ = ⁅x, u⁆ * u := by rw [commutatorElement_def]; group
      rw [e]
      exact D.M.mul_mem (hYM (hxU u hu)) (hUM hu)
    simpa using D.M.inv_mem hxinv
  have hfixA₁ := hfixU A₁ hU₁ hA₁H
  have hfixA₂ := hfixU A₂ hU₂ hA₂H
  have hfixB := hfixU B hUB hBH
  obtain ⟨ℓ, hℓ, hchief⟩ :=
    exists_isChiefFactorUnder_of_minimal hYR hRH hYn hRn hmin hab
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hRnY : R ≤ normalizer (Y : Set G) := fun x hx =>
    Subgroup.mem_normalizer_iff.mpr fun y => by
      constructor
      · exact hchief.2.2.2.1 x hx y
      · intro hy
        have h := hchief.2.2.2.1 x⁻¹ (R.inv_mem hx) (x * y * x⁻¹) hy
        simpa [mul_assoc] using h
  haveI hNY : (Y.subgroupOf R).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYR.le).mpr hRnY
  haveI hEA : IsElementaryAbelian ℓ (R ⧸ Y.subgroupOf R) := hchief.isElementaryAbelian
  let V := Additive (R ⧸ Y.subgroupOf R)
  let ρHgrp : H →* LinearMap.GeneralLinearGroup (ZMod ℓ) V :=
    CFSG.ABGLocalTools.chiefRep (p := ℓ) hRn hYn
  let ρH : Representation (ZMod ℓ) H V := (Units.coeHom _).comp ρHgrp
  have hVnt : Nontrivial V := by
    have htop : Y.subgroupOf R ≠ ⊤ := by
      intro h
      exact (not_le_of_gt hYR) (Subgroup.subgroupOf_eq_top.mp h)
    have hnt : Nontrivial (R ⧸ Y.subgroupOf R) := QuotientGroup.nontrivial_iff.mpr htop
    exact inferInstanceAs (Nontrivial (Additive (R ⧸ Y.subgroupOf R)))
  have key : ∀ (b : H) (x : R),
      (ρHgrp b : V →ₗ[ZMod ℓ] V) (Additive.ofMul ((x : R) : R ⧸ Y.subgroupOf R)) =
        Additive.ofMul ((x : R) : R ⧸ Y.subgroupOf R) →
      ⁅(x : G), (b : G)⁆ ∈ Y := by
    intro b x hfix
    have hc : ((CFSG.ABGLocalTools.chiefConj hRn b x : R) : R ⧸ Y.subgroupOf R) =
        (x : R ⧸ Y.subgroupOf R) := by
      have h1 := hfix
      rw [CFSG.ABGLocalTools.chiefRep_apply_mk hRn hYn b x] at h1
      exact Additive.ofMul.injective h1
    have hmem : ((CFSG.ABGLocalTools.chiefConj hRn b x)⁻¹ * x : R) ∈ Y.subgroupOf R :=
      QuotientGroup.eq.1 hc
    have hmemY : (((CFSG.ABGLocalTools.chiefConj hRn b x)⁻¹ * x : R) : G) ∈ Y :=
      Subgroup.mem_subgroupOf.1 hmem
    have hconj : (x : G) *
        ((((CFSG.ABGLocalTools.chiefConj hRn b x)⁻¹ * x : R) : G)) * (x : G)⁻¹ ∈ Y :=
      hchief.2.2.2.1 (x : G) x.2 _ hmemY
    have hcomm : ⁅(x : G), (b : G)⁆ =
        (x : G) * ((((CFSG.ABGLocalTools.chiefConj hRn b x)⁻¹ * x : R) : G)) * (x : G)⁻¹ := by
      have hc' : ((CFSG.ABGLocalTools.chiefConj hRn b x : R) : G) =
          (b : G) * (x : G) * (b : G)⁻¹ := by
        simpa using CFSG.ABGLocalTools.chiefConj_apply_coe hRn b x
      rw [commutatorElement_def]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hc']
      group
    rw [hcomm]
    exact hconj
  have hℓ31 : ℓ ≠ 31 := by
    intro h31
    subst h31
    haveI : Fact (Nat.Prime 31) := ⟨by norm_num⟩
    have hA₁p : IsPGroup 31 ↥(A₁.subgroupOf H) :=
      IsPGroup.of_card (n := 1) (by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₁H).toEquiv, hA₁, pow_one])
    obtain ⟨v, hv0, hvfix⟩ :=
      Representation.exists_common_fixed_vector_of_isPGroup (k := ZMod 31) (p := 31) hA₁p
        (ρH.comp (A₁.subgroupOf H).subtype)
    obtain ⟨x, rfl⟩ := CFSG.ABGLocalTools.exists_ofMul_mk v
    have hxY : (x : G) ∈ Y := by
      refine hfixA₁ x x.2 fun a ha => ?_
      have hfixa : (ρHgrp ⟨a, hA₁H ha⟩ : V →ₗ[ZMod 31] V)
          (Additive.ofMul ((x : R) : R ⧸ Y.subgroupOf R)) =
            Additive.ofMul ((x : R) : R ⧸ Y.subgroupOf R) := by
        have h := hvfix ⟨⟨a, hA₁H ha⟩, ha⟩
        simpa [ρH] using h
      exact key ⟨a, hA₁H ha⟩ x hfixa
    have hx1 : ((x : R) : R ⧸ Y.subgroupOf R) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hxY)
    exact hv0 (by rw [hx1]; rfl)
  let K : Subgroup G := A₁ ⊔ A₂
  let L : Subgroup G := K ⊔ B
  have hA₁K : A₁ ≤ K := le_sup_left
  have hA₂K : A₂ ≤ K := le_sup_right
  have hKL : K ≤ L := le_sup_left
  have hBL : B ≤ L := le_sup_right
  have hLH : L ≤ H := sup_le (sup_le hA₁H hA₂H) hBH
  have hcomm12 : ∀ x ∈ A₁, ∀ y ∈ A₂, x * y = y * x := by
    intro x hx y hy
    exact ((Subgroup.mem_centralizer_iff.1 (hA₁₂ hx)) y hy).symm
  have hKcard : Nat.card K = 961 := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A₁ A₂ hcomm12).1
    rw [hinf, Subgroup.card_bot, mul_one, hA₁, hA₂] at h
    simpa [K] using h
  have hBnormK : B ≤ normalizer (K : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    calc K.map (MulAut.conj b).toMonoidHom
        = (A₁.map (MulAut.conj b).toMonoidHom) ⊔ (A₂.map (MulAut.conj b).toMonoidHom) := by
          simp [K, Subgroup.map_sup]
      _ = A₁ ⊔ A₂ := by
          have h1 : A₁.map (MulAut.conj b).toMonoidHom = A₁ :=
            Subgroup.mem_normalizer_iff_map_conj_eq.mp (hBn₁ hb)
          have h2 : A₂.map (MulAut.conj b).toMonoidHom = A₂ :=
            Subgroup.mem_normalizer_iff_map_conj_eq.mp (hBn₂ hb)
          rw [h1, h2]
      _ = K := rfl
  have hKB : K ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    by_contra hxne
    exact hxne (hfpf x hx.2 hxne x hx.1 rfl)
  have hLcard : Nat.card L = Nat.card K * Nat.card B := by
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := B) (K := K) hBnormK
    rw [sup_comm B K, inf_comm B K, hKB, Subgroup.card_bot, mul_one] at h
    simpa [L, mul_comm] using h
  haveI hKnL : (K.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKL).mpr (sup_le Subgroup.le_normalizer hBnormK)
  have hKR : (K.subgroupOf L).IsComplement' (B.subgroupOf L) := by
    refine Subgroup.isComplement'_of_coprime ?_ ?_
    · calc Nat.card (K.subgroupOf L) * Nat.card (B.subgroupOf L)
          = Nat.card K * Nat.card B := by
            rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv,
              Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv]
        _ = Nat.card L := hLcard.symm
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv, hKcard, hB]
      norm_num
  have hfixL : ∀ r ∈ B.subgroupOf L, r ≠ 1 →
      ∀ k ∈ K.subgroupOf L, k * r = r * k → k = 1 := by
    intro r hr hr1 k hk hkr
    have hrG : (r : G) ∈ B := Subgroup.mem_subgroupOf.1 hr
    have hkG : (k : G) ∈ K := Subgroup.mem_subgroupOf.1 hk
    have hrne : (r : G) ≠ 1 := fun h => hr1 (Subtype.ext h)
    have hkrG : (k : G) * (r : G) = (r : G) * (k : G) := by
      simpa using congrArg (fun x : L => (x : G)) hkr
    have hk1 : (k : G) = 1 := hfpf (r : G) hrG hrne (k : G) hkG hkrG
    exact Subtype.ext hk1
  let ρL : L →* LinearMap.GeneralLinearGroup (ZMod ℓ) V :=
    ρHgrp.comp (Subgroup.inclusion hLH)
  have hKF : (Nat.card ↥(K.subgroupOf L) : ZMod ℓ) ≠ 0 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv, hKcard]
    intro hzero
    rw [ZMod.natCast_eq_zero_iff] at hzero
    have hdvd := hzero
    apply hℓ31
    have hdvd' : ℓ ∣ 31 ^ 2 := by simpa using hdvd
    have h31 : ℓ ∣ 31 := Nat.Prime.dvd_of_dvd_pow hℓ hdvd'
    exact (Nat.prime_dvd_prime_iff_eq hℓ (by norm_num)).1 h31
  have hρK : ∃ k ∈ K.subgroupOf L, ρL k ≠ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x, hxR, hxY⟩ := SetLike.exists_of_lt hYR
    have hxY' : x ∈ Y := hfixA₁ x hxR fun a ha => by
      have h1 : ρHgrp ⟨a, hA₁H ha⟩ = 1 := by
        have h2 := hcon ⟨a, hA₁K.trans hKL ha⟩ (hA₁K ha)
        simpa [ρL, Subgroup.inclusion] using h2
      have h3 := (CFSG.ABGLocalTools.chiefRep_eq_one_iff hRn hYn ⟨a, hA₁H ha⟩).1 h1 x hxR
      simpa using h3
    exact hxY hxY'
  obtain ⟨v, hv0, hvfix⟩ :=
    CFSG.LocalAnalysis.frobenius_complement_fixed_vector hKR hfixL hKF ρL hρK
  obtain ⟨x, rfl⟩ := CFSG.ABGLocalTools.exists_ofMul_mk v
  have hxY : (x : G) ∈ Y := by
    refine hfixB x x.2 fun b hb => ?_
    have hfixb : (ρHgrp ⟨b, hBH hb⟩ : V →ₗ[ZMod ℓ] V)
        (Additive.ofMul ((x : R) : R ⧸ Y.subgroupOf R)) =
          Additive.ofMul ((x : R) : R ⧸ Y.subgroupOf R) := by
      have h1 := hvfix ⟨b, hBL hb⟩ hb
      simpa [ρL, Subgroup.inclusion] using h1
    exact key ⟨b, hBH hb⟩ x hfixb
  have hx1 : ((x : R) : R ⧸ Y.subgroupOf R) = 1 :=
    (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hxY)
  exact hv0 (by rw [hx1]; rfl)


end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
