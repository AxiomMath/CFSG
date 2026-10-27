module

public import CFSG.Walter.W67.W1Basic
public import CFSG.Walter.PSL2Facts.FieldAut
public import CFSG.Walter.Cited.PSL2Small
public import CFSG.Walter.ReeOrder.JT.Section2
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups
open CFSG.GorensteinWalter

section Abstract

variable {p f : ℕ} [Fact p.Prime]

theorem isOddPrimePower_galoisField (hp : Odd p) (hf : 0 < f) :
    IsOddPrimePower (Nat.card (GaloisField p f)) :=
  ⟨p, f, Fact.out, hp, hf, GaloisField.card p f hf.ne'⟩

theorem four_le_card_sylow_two_psl2 (hp : Odd p) (hf : 0 < f)
    (P : Sylow 2 PSL(2, GaloisField p f)) :
    4 ≤ Nat.card (P : Subgroup PSL(2, GaloisField p f)) := by
  obtain ⟨m, hm, ⟨e⟩⟩ :=
    psl2_odd_hasDihedralSylowTwo_model (GaloisField p f) (isOddPrimePower_galoisField hp hf) P
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  omega

theorem eq_psl2FieldAut_of_odd
    (hp : Odd p) (hf : 0 < f)
    {V0 : Subgroup PSL(2, GaloisField p f)} (hV0 : IsKleinFour V0)
    (hV0fix : ∀ τ : GaloisField p f ≃+* GaloisField p f, ∀ v ∈ V0, psl2FieldAut _ τ v = v)
    (α : MulAut PSL(2, GaloisField p f)) (hα : Odd (orderOf α)) (hαV : ∀ v ∈ V0, α v = v) :
    ∃ σ : GaloisField p f ≃+* GaloisField p f, α = psl2FieldAut _ σ := by
  classical
  set K := GaloisField p f
  have hK : Nat.card K = p ^ f := GaloisField.card p f hf.ne'
  have hK' : IsOddPrimePower (Nat.card K) := isOddPrimePower_galoisField hp hf
  have hp3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    rcases hp with ⟨k, hk⟩
    omega
  have hq3 : 3 ≤ p ^ f := hp3.trans (Nat.le_self_pow hf.ne' p)
  by_cases hq : p ^ f = 3
  ·
    refine ⟨1, ?_⟩
    rw [map_one]
    have hcard12 : Nat.card PSL(2, K) = 12 := by
      rw [psl2_card_formula K hK', hK, hq]
      norm_num
    have hsub : Subsingleton (Sylow 2 PSL(2, K)) :=
      Suzuki.subsingleton_sylow_two_of_card_twelve hcard12 fun u hu =>
        Suzuki.card_centralizer_of_card_three K hK hp hf hq hu
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hV0S : Nat.card V0 = 2 ^ (Nat.card PSL(2, K)).factorization 2 := by
      rw [hV0.card_four, hcard12, Suzuki.factorization_two_twelve]
      norm_num
    let P : Sylow 2 PSL(2, K) := Sylow.ofCard V0 hV0S
    have hPn : (P : Subgroup PSL(2, K)).Normal := Sylow.normal_of_subsingleton P
    have hV0n : V0.Normal := hPn
    have hCV0 := psl2_kleinFour_centralizer_eq_self K hK' V0 hV0
    have hc : ∀ x, x⁻¹ * α x ∈ V0 := by
      intro x
      rw [← hCV0, Subgroup.mem_centralizer_iff]
      intro v hv
      have h1 : α (x * v * x⁻¹) = x * v * x⁻¹ := hαV _ (hV0n.conj_mem v hv x)
      rw [map_mul, map_mul, map_inv, hαV v hv] at h1
      have h2 : (x⁻¹ * α x) * v * (x⁻¹ * α x)⁻¹ = v := by
        calc (x⁻¹ * α x) * v * (x⁻¹ * α x)⁻¹ = x⁻¹ * (α x * v * (α x)⁻¹) * x := by group
          _ = x⁻¹ * (x * v * x⁻¹) * x := by rw [h1]
          _ = v := by group
      calc v * (x⁻¹ * α x) = (x⁻¹ * α x) * v * (x⁻¹ * α x)⁻¹ * (x⁻¹ * α x) := by rw [h2]
        _ = (x⁻¹ * α x) * v := by group
    have hα2 : α ^ 2 = 1 := by
      ext x
      have hcx := hc x
      have hcc : (x⁻¹ * α x) * (x⁻¹ * α x) = 1 := JT.mul_self_of_isKleinFour hV0 hcx
      have hαc : α (x⁻¹ * α x) = x⁻¹ * α x := hαV _ hcx
      rw [pow_two, MulAut.mul_apply, MulAut.one_apply]
      have hax : α x = x * (x⁻¹ * α x) := by group
      calc α (α x) = α x * α (x⁻¹ * α x) := by
            conv_lhs => rw [hax]
            rw [map_mul]
        _ = x * (x⁻¹ * α x) * (x⁻¹ * α x) := by rw [hαc, ← hax]
        _ = x * ((x⁻¹ * α x) * (x⁻¹ * α x)) := by group
        _ = x := by rw [hcc, mul_one]
    have hdvd : orderOf α ∣ 2 := orderOf_dvd_of_pow_eq_one hα2
    have h1 : orderOf α = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact h
      · rw [h] at hα
        exact absurd hα (by decide)
    exact orderOf_eq_one_iff.mp h1
  have hcard : 3 < Nat.card K := by omega
  have hψinj := pGammaL2ToMulAutPSL2_injective K hK' hcard
  obtain ⟨x, hx⟩ := pGammaL2ToMulAutPSL2_surjective K hK hK' hcard α
  set g := x.left
  set σ := x.right
  have hαgσ : α = pgl2InnerAutPSL2 K hK' hcard g * psl2FieldAut K σ := by
    rw [← hx, ← SemidirectProduct.inl_left_mul_inr_right x, map_mul, pGammaL2ToMulAutPSL2_inl,
      pGammaL2ToMulAutPSL2_inr]
  let toPGL : PSL(2, K) →* PGL2 K := Matrix.ProjectiveSpecialLinearGroup.toPGL
  have htoPGL : Function.Injective toPGL := fun _ _ h =>
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective h
  have hVP : IsKleinFour (V0.map toPGL) := isKleinFour_map_of_injective V0 hV0 toPGL htoPGL
  have hgC : g ∈ Subgroup.centralizer ((V0.map toPGL : Subgroup (PGL2 K)) : Set (PGL2 K)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨v, hv, rfl⟩
    have h1 : pgl2InnerAutPSL2 K hK' hcard g v = v := by
      have h := hαV v hv
      rw [hαgσ, MulAut.mul_apply, hV0fix σ v hv] at h
      exact h
    have h2 := toPGL_pgl2InnerAutPSL2_apply K hK' hcard g v
    rw [h1] at h2
    calc toPGL v * g = (g * toPGL v * g⁻¹) * g := by rw [← h2]
      _ = g * toPGL v := by group
  rw [pgl2_kleinFour_centralizer_eq_self K hK' _ hVP] at hgC
  obtain ⟨g0, hg0V, hg0⟩ := hgC
  have hα2 : α = MulAut.conj g0 * psl2FieldAut K σ := by
    rw [hαgσ, ← hg0]
    exact congrArg (· * psl2FieldAut K σ) (pgl2InnerAutPSL2_toPGL K hK' hcard g0)
  have hfix0 : psl2FieldAut K σ g0 = g0 := hV0fix σ g0 hg0V
  have hcomm : Commute (MulAut.conj g0) (psl2FieldAut K σ) := by
    ext y
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hfix0]
  have hg02 : g0 ^ 2 = 1 := by
    rw [pow_two]
    exact JT.mul_self_of_isKleinFour hV0 hg0V
  set n := orderOf α
  have hg0n : g0 ^ n = g0 := by
    obtain ⟨j, hj⟩ := hα
    rw [hj, pow_succ, pow_mul, hg02, one_pow, one_mul]
  have hpow : α ^ n = 1 := pow_orderOf_eq_one α
  rw [hα2, hcomm.mul_pow, ← map_pow, hg0n, ← map_pow] at hpow
  have hinl : pGammaL2ToMulAutPSL2 K hK' hcard
      (SemidirectProduct.inl (toPGL g0) * SemidirectProduct.inr (σ ^ n)) =
      pGammaL2ToMulAutPSL2 K hK' hcard 1 := by
    rw [map_mul, pGammaL2ToMulAutPSL2_inl, pGammaL2ToMulAutPSL2_inr,
      pgl2InnerAutPSL2_toPGL, map_one]
    exact hpow
  have h1 := hψinj hinl
  have hleft := congrArg SemidirectProduct.left h1
  simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.left_inr,
    SemidirectProduct.right_inl, SemidirectProduct.one_left, map_one, mul_one] at hleft
  have hg01 : g0 = 1 := htoPGL (by rw [hleft, map_one])
  exact ⟨σ, by rw [hα2, hg01, map_one, one_mul]⟩

theorem eq_conj_of_sq_eq_one
    (hp : Odd p) (hf : 0 < f) (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5)
    (hq : 3 < p ^ f) {V0 : Subgroup PSL(2, GaloisField p f)} (hV0 : IsKleinFour V0)
    (hV0fix : ∀ τ : GaloisField p f ≃+* GaloisField p f, ∀ v ∈ V0, psl2FieldAut _ τ v = v)
    (α : MulAut PSL(2, GaloisField p f)) (hα : α ^ 2 = 1) (hαV : ∀ v ∈ V0, α v = v) :
    ∃ g0 ∈ V0, α = MulAut.conj g0 := by
  classical
  set K := GaloisField p f
  have hK : Nat.card K = p ^ f := GaloisField.card p f hf.ne'
  have hK' : IsOddPrimePower (Nat.card K) := isOddPrimePower_galoisField hp hf
  have hcard : 3 < Nat.card K := by rw [hK]; exact hq
  have hψinj := pGammaL2ToMulAutPSL2_injective K hK' hcard
  obtain ⟨x, hx⟩ := pGammaL2ToMulAutPSL2_surjective K hK hK' hcard α
  set g := x.left
  set σ := x.right
  have hαgσ : α = pgl2InnerAutPSL2 K hK' hcard g * psl2FieldAut K σ := by
    rw [← hx, ← SemidirectProduct.inl_left_mul_inr_right x, map_mul, pGammaL2ToMulAutPSL2_inl,
      pGammaL2ToMulAutPSL2_inr]
  let toPGL : PSL(2, K) →* PGL2 K := Matrix.ProjectiveSpecialLinearGroup.toPGL
  have htoPGL : Function.Injective toPGL := fun _ _ h =>
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective h
  have hVP : IsKleinFour (V0.map toPGL) := isKleinFour_map_of_injective V0 hV0 toPGL htoPGL
  have hgC : g ∈ Subgroup.centralizer ((V0.map toPGL : Subgroup (PGL2 K)) : Set (PGL2 K)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨v, hv, rfl⟩
    have h1 : pgl2InnerAutPSL2 K hK' hcard g v = v := by
      have h := hαV v hv
      rw [hαgσ, MulAut.mul_apply, hV0fix σ v hv] at h
      exact h
    have h2 := toPGL_pgl2InnerAutPSL2_apply K hK' hcard g v
    rw [h1] at h2
    calc toPGL v * g = (g * toPGL v * g⁻¹) * g := by rw [← h2]
      _ = g * toPGL v := by group
  rw [pgl2_kleinFour_centralizer_eq_self K hK' _ hVP] at hgC
  obtain ⟨g0, hg0V, hg0⟩ := hgC
  have hα2 : α = MulAut.conj g0 * psl2FieldAut K σ := by
    rw [hαgσ, ← hg0]
    exact congrArg (· * psl2FieldAut K σ) (pgl2InnerAutPSL2_toPGL K hK' hcard g0)
  have hfix0 : psl2FieldAut K σ g0 = g0 := hV0fix σ g0 hg0V
  have hcomm : Commute (MulAut.conj g0) (psl2FieldAut K σ) := by
    ext y
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hfix0]
  have hg02 : g0 ^ 2 = 1 := by
    rw [pow_two]
    exact JT.mul_self_of_isKleinFour hV0 hg0V
  have hpow := hα
  rw [hα2, hcomm.mul_pow, ← map_pow, hg02, map_one, one_mul, ← map_pow] at hpow
  have hσ2 : σ ^ 2 = 1 :=
    CFSG.GorensteinWalter.psl2FieldAut_injective K (by rw [hpow, map_one])
  have hσ1 : σ = 1 := by
    obtain ⟨hdvd, -⟩ := card_fixedSubfield_galoisField hf.ne' σ
    have h1 : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one hσ2
    have hfodd : Odd f := odd_of_pow_mod_eight hp h8
    have h2 : Odd (orderOf σ) := Odd.of_dvd_nat hfodd hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at h2
      exact absurd h2 (by decide)
  exact ⟨g0, hg0V, by rw [hα2, hσ1, map_one, mul_one]⟩

theorem isCyclic_ringEquiv_galoisField : IsCyclic (GaloisField p f ≃+* GaloisField p f) := by
  set F := GaloisField p f
  let e : (F ≃+* F) ≃* (F ≃ₐ[ZMod p] F) :=
    { toFun := fun σ =>
        AlgEquiv.ofRingEquiv (f := σ) (by
          intro x
          have h : (σ.toRingHom.comp (algebraMap (ZMod p) F) : ZMod p →+* F) =
              algebraMap (ZMod p) F := RingHom.ext_zmod _ _
          exact DFunLike.congr_fun h x)
      invFun := fun σ => σ.toRingEquiv
      left_inv := by intro σ; ext x; rfl
      right_inv := by intro σ; ext x; rfl
      map_mul' := by intro σ τ; ext x; rfl }
  exact e.isCyclic.mpr inferInstance

theorem psl2FieldAut_injective (hp : Odd p) (hf : 0 < f) :
    Function.Injective (psl2FieldAut (GaloisField p f)) := by
  set K := GaloisField p f
  have hK : Nat.card K = p ^ f := GaloisField.card p f hf.ne'
  have hK' : IsOddPrimePower (Nat.card K) := isOddPrimePower_galoisField hp hf
  by_cases hq : 3 < Nat.card K
  · intro σ τ h
    have h1 := pGammaL2ToMulAutPSL2_injective K hK' hq
      (a₁ := SemidirectProduct.inr σ) (a₂ := SemidirectProduct.inr τ)
      (by rw [pGammaL2ToMulAutPSL2_inr, pGammaL2ToMulAutPSL2_inr, h])
    exact SemidirectProduct.inr_injective h1
  · have hp3 : 3 ≤ p := by
      have := (Fact.out : p.Prime).two_le
      rcases hp with ⟨k, hk⟩
      omega
    have hq3 : p ^ f = 3 := by
      have : 3 ≤ p ^ f := hp3.trans (Nat.le_self_pow hf.ne' p)
      omega
    have hp3' : p = 3 := by
      have h : p ∣ 3 := hq3 ▸ dvd_pow_self p hf.ne'
      rcases (Nat.dvd_prime Nat.prime_three).mp h with h1 | h1
      · omega
      · exact h1
    have hf1 : f = 1 := by
      subst hp3'
      have : (3 : ℕ) ^ f = 3 ^ 1 := by rw [hq3, pow_one]
      exact Nat.pow_right_injective (le_refl 2 |>.trans (by norm_num : 2 ≤ 3)) this
    have : Subsingleton (K ≃+* K) :=
      Suzuki.subsingleton_ringEquiv_of_card_prime K (p := p) (by rw [hK, hf1, pow_one])
    intro σ τ _
    exact Subsingleton.elim σ τ

theorem card_dvd_four_psl2 (F : Type) [Field F] [Finite F] (hF : Nat.card F = p ^ f)
    (hp : Odd p) (hf : 0 < f) (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5)
    {W : Subgroup PSL(2, F)} (hW : IsPGroup 2 W) : Nat.card W ∣ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hW.exists_le_sylow
  rw [← psl2_sylow_two_card_eq_four F hF hp hf h8 P]
  exact Subgroup.card_dvd_of_le hP

theorem card_normalizer_kleinFour_psl2
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = p ^ f)
    (hp : Odd p) (hf : 0 < f) (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) {V : Subgroup PSL(2, K)}
    (hV : IsKleinFour V) : Nat.card (Subgroup.normalizer (V : Set PSL(2, K))) = 12 := by
  classical
  set X := PSL(2, K)
  have hK' : IsOddPrimePower (Nat.card K) := ⟨p, f, Fact.out, hp, hf, hK⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N₀ := Subgroup.normalizer (V : Set X) with hN₀
  have hVN₀ : V ≤ N₀ := Subgroup.le_normalizer
  have hCV := psl2_kleinFour_centralizer_eq_self K hK' V hV
  let := JT.conjAct N₀ V le_rfl
  let φ : N₀ →* MulAut V := MulDistribMulAction.toMulAut N₀ V
  have hker : φ.ker = V.subgroupOf N₀ := by
    ext n
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hn
      have hnC : (n : X) ∈ Subgroup.centralizer (V : Set X) := by
        refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
        have := congrArg Subtype.val (DFunLike.congr_fun hn ⟨v, hv⟩)
        change (n : X) * v * (n : X)⁻¹ = v at this
        calc v * n = ((n : X) * v * (n : X)⁻¹) * n := by rw [this]
          _ = n * v := by group
      rw [hCV] at hnC
      exact hnC
    · intro hn
      ext v
      change (n : X) * v * (n : X)⁻¹ = v
      have := hV.isMulCommutative.is_comm.comm ⟨(n : X), hn⟩ v
      have := congrArg Subtype.val this
      change (n : X) * v = v * n at this
      rw [this, mul_inv_cancel_right]
  have hcard : Nat.card N₀ = 4 * Nat.card φ.range := by
    have h1 := φ.ker.card_mul_index
    rw [Subgroup.index_ker, hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVN₀).toEquiv,
      hV.card_four] at h1
    exact h1.symm
  have hdvd6 : Nat.card φ.range ∣ 6 := by
    rw [← JT.PSL2Facts.card_mulAut_of_isKleinFour V]
    exact Subgroup.card_subgroup_dvd_card _
  have hodd : ¬ 2 ∣ Nat.card φ.range := by
    rintro ⟨k, hk⟩
    obtain ⟨W, hW⟩ := Sylow.exists_subgroup_card_pow_prime (G := N₀) 2 (n := 3)
      (by rw [hcard, hk]; exact ⟨k, by ring⟩)
    have hW2 : IsPGroup 2 (W.map N₀.subtype) := (IsPGroup.of_card hW).map N₀.subtype
    have := card_dvd_four_psl2 K hK hp hf h8 hW2
    rw [Subgroup.card_map_of_injective N₀.subtype_injective, hW] at this
    omega
  have hne1 : Nat.card φ.range ≠ 1 := by
    intro h1
    rw [h1] at hcard
    have hN₀V : N₀ = V := (Subgroup.eq_of_le_of_card_ge hVN₀ (by rw [hcard, hV.card_four])).symm
    have hfac : (Nat.card X).factorization 2 = 2 := by
      rw [psl2_card_formula K hK', hK, psl2_order_factorization_two_of_mod_eight h8]
    have hVcard : Nat.card V = 2 ^ (Nat.card X).factorization 2 := by
      rw [hfac, hV.card_four]
      norm_num
    let P : Sylow 2 X := Sylow.ofCard V hVcard
    have hPV : (P : Subgroup X) = V := rfl
    have hp3 : 3 ≤ p := by
      have := (Fact.out : p.Prime).two_le
      rcases hp with ⟨k, hk⟩
      omega
    have hq3 : 3 ≤ p ^ f := hp3.trans (Nat.le_self_pow hf.ne' p)
    by_cases hq : p ^ f = 3
    ·
      have hcard12 : Nat.card X = 12 := by
        rw [psl2_card_formula K hK', hK, hq]
        norm_num
      have hsub : Subsingleton (Sylow 2 X) :=
        Suzuki.subsingleton_sylow_two_of_card_twelve hcard12 fun u hu =>
          Suzuki.card_centralizer_of_card_three K hK hp hf hq hu
      have hVn : V.Normal := Sylow.normal_of_subsingleton P
      have htop : N₀ = ⊤ := Subgroup.normalizer_eq_top_iff.mpr hVn
      rw [htop, Subgroup.card_top, hcard12] at hcard
      omega
    have hsimple : IsSimpleGroup X :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hK]; omega)
    have hNC : Subgroup.normalizer ((P : Subgroup X) : Set X) ≤
        Subgroup.centralizer ((P : Subgroup X) : Set X) := by
      intro n hn
      have hnV : n ∈ V := by
        have hn' : n ∈ N₀ := hn
        rw [hN₀V] at hn'
        exact hn'
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      exact congrArg Subtype.val (hV.isMulCommutative.is_comm.comm ⟨m, hm⟩ ⟨n, hnV⟩)
    have hcomp := MonoidHom.ker_transferSylow_isComplement' P hNC
    have hXbig : 4 < Nat.card X := by
      rw [psl2_card_formula K hK', hK]
      have h5 : 5 ≤ p ^ f := by omega
      have : 5 * (5 ^ 2 - 1) ≤ p ^ f * ((p ^ f) ^ 2 - 1) :=
        Nat.mul_le_mul h5 (Nat.sub_le_sub_right (Nat.pow_le_pow_left h5 2) 1)
      omega
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MonoidHom.transferSylow P hNC).ker with
      hb | ht
    · have := hcomp.card_mul_card
      rw [hb, Subgroup.card_bot, one_mul, hPV, hV.card_four] at this
      omega
    · have := hcomp.card_mul_card
      rw [ht, Subgroup.card_top, hPV, hV.card_four] at this
      have hpos : 0 < Nat.card X := Nat.card_pos
      omega
  have h3 : Nat.card φ.range = 3 := by
    have hpos : 0 < Nat.card φ.range := Nat.card_pos
    have hle : Nat.card φ.range ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd6
    interval_cases h : Nat.card φ.range <;> simp_all
  rw [hcard, h3]

end Abstract

section Ambient

variable {G : Type*} [Group G] {p f : ℕ} [Fact p.Prime] {K : Subgroup G}

@[expose] noncomputable def psl2Emb (e : K ≃* PSL(2, GaloisField p f)) :
    PSL(2, GaloisField p f) →* G :=
  K.subtype.comp e.symm.toMonoidHom

namespace PSL2Sub

theorem emb_injective (e : K ≃* PSL(2, GaloisField p f)) : Function.Injective (psl2Emb e) :=
  K.subtype_injective.comp e.symm.injective

theorem emb_range (e : K ≃* PSL(2, GaloisField p f)) : (psl2Emb e).range = K := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (e.symm y).2
  · intro hx
    exact ⟨e ⟨x, hx⟩, by simp [psl2Emb]⟩

theorem emb_mem (e : K ≃* PSL(2, GaloisField p f)) (y : PSL(2, GaloisField p f)) :
    psl2Emb e y ∈ K := (e.symm y).2

theorem emb_apply (e : K ≃* PSL(2, GaloisField p f)) (x : K) : psl2Emb e (e x) = x := by
  simp [psl2Emb]

theorem exists_emb_eq (e : K ≃* PSL(2, GaloisField p f)) {x : G} (hx : x ∈ K) :
    ∃ y, psl2Emb e y = x := by
  rw [← emb_range e] at hx
  exact hx

theorem map_comap_emb (e : K ≃* PSL(2, GaloisField p f)) {X : Subgroup G} (hX : X ≤ K) :
    (X.comap (psl2Emb e)).map (psl2Emb e) = X :=
  Subgroup.map_comap_eq_self (by rw [emb_range]; exact hX)

theorem map_le (e : K ≃* PSL(2, GaloisField p f)) (X : Subgroup PSL(2, GaloisField p f)) :
    X.map (psl2Emb e) ≤ K :=
  (Subgroup.map_le_range _ _).trans (emb_range e).le

theorem card_comap_emb (e : K ≃* PSL(2, GaloisField p f)) {X : Subgroup G} (hX : X ≤ K) :
    Nat.card (X.comap (psl2Emb e)) = Nat.card X := by
  conv_rhs => rw [← map_comap_emb e hX]
  rw [Subgroup.card_map_of_injective (emb_injective e)]

theorem eq_one_of_commute (e : K ≃* PSL(2, GaloisField p f)) {x : G} (hx : x ∈ K)
    (hc : ∀ k ∈ K, x * k = k * x) : x = 1 := by
  have h : e ⟨x, hx⟩ ∈ Subgroup.center PSL(2, GaloisField p f) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply e.symm.injective
    apply Subtype.ext
    simp only [map_mul, MulEquiv.symm_apply_apply, Subgroup.coe_mul]
    exact (hc _ (e.symm y).2).symm
  rw [psl2_center_eq_bot, Subgroup.mem_bot] at h
  have := congrArg Subtype.val (e.injective (h.trans (map_one e).symm))
  exact this

theorem card_eq (e : K ≃* PSL(2, GaloisField p f)) (hp : Odd p) (hf : 0 < f) :
    Nat.card K = p ^ f * ((p ^ f) ^ 2 - 1) / 2 := by
  rw [Nat.card_congr e.toEquiv, psl2_card_formula _ (isOddPrimePower_galoisField hp hf),
    GaloisField.card p f hf.ne']

theorem card_dvd_card_sylow (e : K ≃* PSL(2, GaloisField p f)) {W : Subgroup G} (hWK : W ≤ K)
    (hW : IsPGroup 2 W) (Q : Sylow 2 PSL(2, GaloisField p f)) :
    Nat.card W ∣ Nat.card (Q : Subgroup PSL(2, GaloisField p f)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW' : IsPGroup 2 (W.comap (psl2Emb e)) :=
    hW.comap_of_injective (psl2Emb e) (emb_injective e)
  obtain ⟨P, hP⟩ := hW'.exists_le_sylow
  rw [← card_comap_emb e hWK, Sylow.card_eq_multiplicity Q, ← Sylow.card_eq_multiplicity P]
  exact Subgroup.card_dvd_of_le hP

theorem exists_sylow (e : K ≃* PSL(2, GaloisField p f)) (hp : Odd p) (hf : 0 < f) :
    ∃ P : Subgroup G, P ≤ K ∧ IsPGroup 2 P ∧ 4 ≤ Nat.card P ∧
      ∀ W : Subgroup G, W ≤ K → IsPGroup 2 W → Nat.card W ∣ Nat.card P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q⟩ : Nonempty (Sylow 2 PSL(2, GaloisField p f)) := inferInstance
  refine ⟨(Q : Subgroup PSL(2, GaloisField p f)).map (psl2Emb e), ?_, Q.isPGroup'.map _, ?_,
    fun W hWK hW => ?_⟩
  · exact map_le e _
  · rw [Subgroup.card_map_of_injective (emb_injective e)]
    exact four_le_card_sylow_two_psl2 hp hf Q
  · rw [Subgroup.card_map_of_injective (emb_injective e)]
    exact card_dvd_card_sylow e hWK hW Q

theorem mod_eight (e : K ≃* PSL(2, GaloisField p f)) (hp : Odd p) (hf : 0 < f)
    (hab : ∀ P : Subgroup G, P ≤ K → IsPGroup 2 P → IsMulCommutative P) :
    p ^ f % 8 = 3 ∨ p ^ f % 8 = 5 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P₀ : Sylow 2 PSL(2, GaloisField p f) := default
  have hPK : (P₀ : Subgroup PSL(2, GaloisField p f)).map (psl2Emb e) ≤ K := map_le e _
  have hP := hab _ hPK (P₀.isPGroup'.map _)
  have eP := (P₀ : Subgroup PSL(2, GaloisField p f)).equivMapOfInjective (psl2Emb e)
    (emb_injective e)
  have hP₀ : IsMulCommutative (P₀ : Subgroup PSL(2, GaloisField p f)) :=
    ⟨⟨fun a b => eP.injective (by rw [map_mul, map_mul]; exact hP.is_comm.comm _ _)⟩⟩
  have := JT.psl2_mod_eight_of_isMulCommutative (isOddPrimePower_galoisField hp hf) P₀ hP₀
  rwa [GaloisField.card p f hf.ne'] at this

theorem card_dvd_four (e : K ≃* PSL(2, GaloisField p f)) (hp : Odd p) (hf : 0 < f)
    (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) {W : Subgroup G} (hWK : W ≤ K)
    (hW : IsPGroup 2 W) : Nat.card W ∣ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q⟩ : Nonempty (Sylow 2 PSL(2, GaloisField p f)) := inferInstance
  have := card_dvd_card_sylow e hWK hW Q
  rwa [psl2_sylow_two_card_eq_four _ (GaloisField.card p f hf.ne') hp hf h8 Q] at this

theorem isKleinFour_comap (e : K ≃* PSL(2, GaloisField p f)) {V : Subgroup G} (hVK : V ≤ K)
    (hV : IsKleinFour V) : IsKleinFour (V.comap (psl2Emb e)) := by
  set V₀ := V.comap (psl2Emb e)
  have eV : V₀ ≃* V := (V₀.equivMapOfInjective _ (emb_injective e)).trans
    (MulEquiv.subgroupCongr (map_comap_emb e hVK))
  exact ⟨by rw [Nat.card_congr eV.toEquiv, hV.card_four],
    by rw [Monoid.exponent_eq_of_mulEquiv eV, hV.exponent_two]⟩

theorem isKleinFour_of_card (e : K ≃* PSL(2, GaloisField p f)) (hp : Odd p) (hf : 0 < f)
    (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) {V : Subgroup G} (hVK : V ≤ K)
    (hV : Nat.card V = 4) : IsKleinFour V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V₀ := V.comap (psl2Emb e)
  have hV₀ : Nat.card V₀ = 4 := (card_comap_emb e hVK).trans hV
  have hV₀S : Nat.card V₀ = 2 ^ (Nat.card PSL(2, GaloisField p f)).factorization 2 := by
    rw [hV₀, psl2_card_formula _ (isOddPrimePower_galoisField hp hf), GaloisField.card p f hf.ne',
      psl2_order_factorization_two_of_mod_eight h8]
    norm_num
  have h4 := psl2_sylow_two_isKleinFour _ (GaloisField.card p f hf.ne') hp hf h8
    (Sylow.ofCard V₀ hV₀S)
  have eV : V₀ ≃* V := (V₀.equivMapOfInjective _ (emb_injective e)).trans
    (MulEquiv.subgroupCongr (map_comap_emb e hVK))
  exact ⟨by rw [← Nat.card_congr eV.toEquiv, hV₀],
    by rw [← Monoid.exponent_eq_of_mulEquiv eV]; exact h4.exponent_two⟩

theorem inf_centralizer_eq
    (e : K ≃* PSL(2, GaloisField p f)) (hp : Odd p) (hf : 0 < f)
    {V : Subgroup G} (hVK : V ≤ K) (hV : IsKleinFour V) :
    K ⊓ Subgroup.centralizer (V : Set G) = V := by
  have h := psl2_kleinFour_centralizer_eq_self _ (isOddPrimePower_galoisField hp hf) _
    (isKleinFour_comap e hVK hV)
  have h2 := JT.map_centralizer_of_injective (psl2Emb e) (emb_injective e) (V.comap (psl2Emb e))
  rw [h, map_comap_emb e hVK, emb_range] at h2
  exact h2.symm

theorem card_inf_normalizer
    (e : K ≃* PSL(2, GaloisField p f)) (hp : Odd p) (hf : 0 < f)
    (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) {V : Subgroup G} (hVK : V ≤ K) (hV : IsKleinFour V) :
    Nat.card (K ⊓ Subgroup.normalizer (V : Set G) : Subgroup G) = 12 := by
  have h := card_normalizer_kleinFour_psl2 _ (GaloisField.card p f hf.ne') hp hf h8
    (isKleinFour_comap e hVK hV)
  have h2 := JT.map_normalizer_of_injective (psl2Emb e) (emb_injective e) (V.comap (psl2Emb e))
  rw [map_comap_emb e hVK, emb_range] at h2
  rw [← h2, Subgroup.card_map_of_injective (emb_injective e), h]

theorem exists_conj_of_card_four (e : K ≃* PSL(2, GaloisField p f)) (hp : Odd p) (hf : 0 < f)
    (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) {T T' : Subgroup G} (hTK : T ≤ K) (hT'K : T' ≤ K)
    (hT : Nat.card T = 4) (hT' : Nat.card T' = 4) :
    ∃ k ∈ K, ∀ t ∈ T', k * t * k⁻¹ ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := GaloisField p f
  have hS : ∀ X : Subgroup PSL(2, F), Nat.card X = 4 →
      Nat.card X = 2 ^ (Nat.card PSL(2, F)).factorization 2 := by
    intro X hX
    rw [hX, psl2_card_formula _ (isOddPrimePower_galoisField hp hf), GaloisField.card p f hf.ne',
      psl2_order_factorization_two_of_mod_eight h8]
    norm_num
  set T₀ := T.comap (psl2Emb e)
  set T₀' := T'.comap (psl2Emb e)
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq PSL(2, F)
    (Sylow.ofCard T₀' (hS T₀' ((card_comap_emb e hT'K).trans hT')))
    (Sylow.ofCard T₀ (hS T₀ ((card_comap_emb e hTK).trans hT)))
  have hyT : T₀'.map (MulAut.conj y).toMonoidHom = T₀ := by
    have := congrArg (fun P : Sylow 2 PSL(2, F) => (P : Subgroup PSL(2, F))) hy
    simp only [Sylow.coe_subgroup_smul, Sylow.coe_ofCard] at this
    rw [← this]
    rfl
  refine ⟨psl2Emb e y, emb_mem e y, fun t ht => ?_⟩
  obtain ⟨z, rfl⟩ := exists_emb_eq e (hT'K ht)
  have hz : z ∈ T₀' := ht
  have : y * z * y⁻¹ ∈ T₀ := by
    rw [← hyT]
    exact ⟨z, hz, rfl⟩
  have h1 : psl2Emb e y * psl2Emb e z * (psl2Emb e y)⁻¹ = psl2Emb e (y * z * y⁻¹) := by
    rw [map_mul, map_mul, map_inv]
  rw [h1]
  exact this

theorem eq_bot_of_odd (e : K ≃* PSL(2, GaloisField p f)) (hp : Odd p) (hf : 0 < f)
    {W : Subgroup G} (hWK : W ≤ K) (hWn : ∀ k ∈ K, ∀ w ∈ W, k * w * k⁻¹ ∈ W)
    (hW : Odd (Nat.card W)) : W = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := GaloisField p f
  have hK : Nat.card F = p ^ f := GaloisField.card p f hf.ne'
  have hK' : IsOddPrimePower (Nat.card F) := isOddPrimePower_galoisField hp hf
  set X := PSL(2, F)
  set W₀ := W.comap (psl2Emb e) with hW₀
  have hW₀card : Nat.card W₀ = Nat.card W := card_comap_emb e hWK
  have hW₀n : W₀.Normal := by
    refine ⟨fun w hw y => ?_⟩
    change psl2Emb e (y * w * y⁻¹) ∈ W
    rw [map_mul, map_mul, map_inv]
    exact hWn _ (emb_mem e y) _ hw
  suffices hbot : W₀ = ⊥ by
    rw [← map_comap_emb e hWK, ← hW₀, hbot, Subgroup.map_bot]
  have hp3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    rcases hp with ⟨k, hk⟩
    omega
  have hq3 : 3 ≤ p ^ f := hp3.trans (Nat.le_self_pow hf.ne' p)
  by_cases hq : p ^ f = 3
  ·
    have hcard12 : Nat.card X = 12 := by
      rw [psl2_card_formula F hK', hK, hq]
      norm_num
    have hsub : Subsingleton (Sylow 2 X) :=
      Suzuki.subsingleton_sylow_two_of_card_twelve hcard12 fun u hu =>
        Suzuki.card_centralizer_of_card_three F hK hp hf hq hu
    obtain ⟨P⟩ : Nonempty (Sylow 2 X) := inferInstance
    have hPn : (P : Subgroup X).Normal := Sylow.normal_of_subsingleton P
    have hP4 : Nat.card (P : Subgroup X) = 4 := by
      rw [P.card_eq_multiplicity, hcard12, Suzuki.factorization_two_twelve]
      norm_num
    have hdisj : W₀ ⊓ P = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      exact eq_one_of_odd_of_isPGroup P.isPGroup' hx.2
        (Odd.of_dvd_nat (hW₀card ▸ hW) (Subgroup.orderOf_dvd_natCard _ hx.1))
    have hcomm : ∀ w ∈ W₀, ∀ t ∈ (P : Subgroup X), w * t = t * w := by
      intro w hw t ht
      have h1 : w * t * w⁻¹ * t⁻¹ ∈ W₀ ⊓ P := by
        refine ⟨?_, ?_⟩
        · have : w * t * w⁻¹ * t⁻¹ = w * (t * w⁻¹ * t⁻¹) := by group
          rw [this]
          exact W₀.mul_mem hw (hW₀n.conj_mem _ (W₀.inv_mem hw) t)
        · exact (P : Subgroup X).mul_mem (hPn.conj_mem t ht w) ((P : Subgroup X).inv_mem ht)
      rw [hdisj, Subgroup.mem_bot] at h1
      calc w * t = (w * t * w⁻¹ * t⁻¹) * t * w := by group
        _ = t * w := by rw [h1, one_mul]
    by_contra hne
    obtain ⟨⟨w, hw⟩, hw1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have hw1 : w ≠ 1 := fun h1 => hw1' (Subtype.ext h1)
    have hW₀3 : Nat.card W₀ = 3 := by
      have hdvd : Nat.card W₀ ∣ 12 := hcard12 ▸ Subgroup.card_subgroup_dvd_card W₀
      have hodd : Odd (Nat.card W₀) := hW₀card ▸ hW
      have hne1 : Nat.card W₀ ≠ 1 := fun h1 => hne (Subgroup.card_eq_one.mp h1)
      have hle : Nat.card W₀ ≤ 12 := Nat.le_of_dvd (by norm_num) hdvd
      have hodd' := Nat.odd_iff.mp hodd
      interval_cases hc : Nat.card W₀ <;> first | rfl | omega
    have hW₀comm : ∀ a ∈ W₀, ∀ b ∈ W₀, a * b = b * a := by
      have : Fact (Nat.Prime (Nat.card W₀)) := ⟨by rw [hW₀3]; exact Nat.prime_three⟩
      have hcyc : IsCyclic W₀ := isCyclic_of_prime_card rfl
      intro a ha b hb
      exact congrArg Subtype.val (hcyc.commGroup.mul_comm ⟨a, ha⟩ ⟨b, hb⟩)
    have hsup : W₀ ⊔ (P : Subgroup X) = ⊤ := by
      obtain ⟨hc, -⟩ := card_sup_mul_card_inf_of_commute W₀ P hcomm
      rw [hdisj, Subgroup.card_bot, mul_one, hW₀3, hP4] at hc
      exact Subgroup.eq_top_of_card_eq _ (by rw [hc, hcard12])
    have hcen : w ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hy : y ∈ Subgroup.centralizer ({w} : Set X) := by
        have hle : W₀ ⊔ (P : Subgroup X) ≤ Subgroup.centralizer ({w} : Set X) := by
          refine sup_le (fun a ha => ?_) (fun t ht => ?_)
          · exact Subgroup.mem_centralizer_singleton_iff.mpr (hW₀comm a ha w hw)
          · exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm w hw t ht).symm
        exact hle (hsup ▸ Subgroup.mem_top y)
      exact Subgroup.mem_centralizer_singleton_iff.mp hy
    rw [psl2_center_eq_bot, Subgroup.mem_bot] at hcen
    exact hw1 hcen
  ·
    have hsimple : IsSimpleGroup X :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hK]; omega)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal W₀ with hb | ht
    · exact hb
    · exfalso
      have h2 : 2 ∣ Nat.card X := Suzuki.two_dvd_card_psl2 F hK'
      rw [← Subgroup.card_top (G := X), ← ht, hW₀card] at h2
      exact (Nat.not_even_iff_odd.mpr hW) (even_iff_two_dvd.mpr h2)

theorem le_of_normal_index_two
    [Finite G] (e : K ≃* PSL(2, GaloisField p f)) (hp : Odd p)
    (hf : 0 < f) (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) {W : Subgroup G} [hWn : W.Normal]
    (hW : W.index = 2) : K ≤ W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hPK, hP2, hP4, hPmax⟩ := exists_sylow e hp hf
  have hPcard : Nat.card P = 4 := by
    have := card_dvd_four e hp hf h8 hPK hP2
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hPV := isKleinFour_of_card e hp hf h8 hPK hPcard
  have h12 := card_inf_normalizer e hp hf h8 hPK hPV
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := (K ⊓ Subgroup.normalizer (P : Set G) :
    Subgroup G)) 3 (by rw [h12]; norm_num)
  have hz3 : orderOf (z : G) = 3 := by rw [Subgroup.orderOf_coe, hz]
  have hzC : (z : G) ∉ Subgroup.centralizer (P : Set G) := by
    intro hzC
    have : (z : G) ∈ K ⊓ Subgroup.centralizer (P : Set G) := ⟨z.2.1, hzC⟩
    rw [inf_centralizer_eq e hp hf hPK hPV] at this
    have h4 : orderOf (z : G) ∣ 4 := hPcard ▸ Subgroup.orderOf_dvd_natCard _ this
    rw [hz3] at h4
    omega
  have hzW : (z : G) ∈ W := by
    have : (z : G) = ((z : G) ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, ← hz3, pow_orderOf_eq_one,
        one_mul]
    rw [this]
    exact Subgroup.sq_mem_of_index_two hW _
  set c : P → P := fun t => ⟨(z : G) * t * (z : G)⁻¹ * (t : G)⁻¹, P.mul_mem
    ((Subgroup.mem_normalizer_iff.mp z.2.2 t).mp t.2) (P.inv_mem t.2)⟩ with hc
  have hcinj : Function.Injective c := by
    intro s t hst
    have h1 : (z : G) * s * (z : G)⁻¹ * (s : G)⁻¹ = (z : G) * t * (z : G)⁻¹ * (t : G)⁻¹ :=
      congrArg Subtype.val hst
    have hfix : (z : G) * ((t : G)⁻¹ * s) * (z : G)⁻¹ = (t : G)⁻¹ * s := by
      have hab := hPV.isMulCommutative
      have hts : (s : G)⁻¹ * (t : G) = (t : G) * (s : G)⁻¹ :=
        congrArg Subtype.val (hab.is_comm.comm (s⁻¹) t)
      calc (z : G) * ((t : G)⁻¹ * s) * (z : G)⁻¹ =
          ((z : G) * t * (z : G)⁻¹)⁻¹ * ((z : G) * s * (z : G)⁻¹) := by group
        _ = ((z : G) * t * (z : G)⁻¹ * (t : G)⁻¹ * t)⁻¹ *
            ((z : G) * s * (z : G)⁻¹ * (s : G)⁻¹ * s) := by group
        _ = ((z : G) * s * (z : G)⁻¹ * (s : G)⁻¹ * t)⁻¹ *
            ((z : G) * s * (z : G)⁻¹ * (s : G)⁻¹ * s) := by rw [h1]
        _ = (t : G)⁻¹ * s := by group
    have := JT.eq_one_of_conj_eq_of_orderOf_eq_three hPV hz3 z.2.2 hzC
      (P.mul_mem (P.inv_mem t.2) s.2) hfix
    exact Subtype.ext (inv_mul_eq_one.mp this).symm
  have hcsurj := Finite.injective_iff_surjective.mp hcinj
  have hPW : P ≤ W := by
    intro t ht
    obtain ⟨s, hs⟩ := hcsurj ⟨t, ht⟩
    have := congrArg Subtype.val hs
    change (z : G) * s * (z : G)⁻¹ * (s : G)⁻¹ = t at this
    rw [← this]
    have h1 : (s : G) * (z : G)⁻¹ * (s : G)⁻¹ ∈ W := hWn.conj_mem _ (W.inv_mem hzW) _
    have h2 : (z : G) * s * (z : G)⁻¹ * (s : G)⁻¹ =
        (z : G) * ((s : G) * (z : G)⁻¹ * (s : G)⁻¹) := by group
    rw [h2]
    exact W.mul_mem hzW h1
  have hidx : (W.subgroupOf K).index ∣ 2 := by
    have := Subgroup.relIndex_dvd_index_of_normal W K
    rwa [hW] at this
  have hodd : ¬ 2 ∣ (P.subgroupOf K).index := by
    intro h2
    have hcardK := (P.subgroupOf K).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).toEquiv, hPcard] at hcardK
    obtain ⟨k, hk⟩ := h2
    obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime (G := K) 2 (n := 3)
      (by rw [← hcardK, hk]; exact ⟨k, by ring⟩)
    have hQ2 : IsPGroup 2 (Q.map K.subtype) := (IsPGroup.of_card hQ).map _
    have := card_dvd_four e hp hf h8 (Subgroup.map_subtype_le Q) hQ2
    rw [Subgroup.card_map_of_injective K.subtype_injective, hQ] at this
    omega
  have hle : P.subgroupOf K ≤ W.subgroupOf K := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hPW (Subgroup.mem_subgroupOf.mp hx))
  have hdvd := Subgroup.index_dvd_of_le hle
  have h1 : (W.subgroupOf K).index = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hidx with h | h
    · exact h
    · exact absurd (h ▸ hdvd) hodd
  intro x hx
  have htop := Subgroup.index_eq_one.mp h1
  have hmem : (⟨x, hx⟩ : K) ∈ W.subgroupOf K := htop ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp hmem

@[expose] noncomputable def conjHom (e : K ≃* PSL(2, GaloisField p f)) :
    Subgroup.normalizer (K : Set G) →* MulAut PSL(2, GaloisField p f) :=
  (MulAut.congr e).toMonoidHom.comp
    (@MulDistribMulAction.toMulAut _ _ _ _ (JT.conjAct _ K le_rfl))

theorem emb_conjHom (e : K ≃* PSL(2, GaloisField p f)) (n : Subgroup.normalizer (K : Set G))
    (y : PSL(2, GaloisField p f)) :
    psl2Emb e (conjHom e n y) = n * psl2Emb e y * (n : G)⁻¹ := by
  simp [conjHom, psl2Emb, MulAut.congr_apply]
  rfl

theorem conjHom_eq_iff (e : K ≃* PSL(2, GaloisField p f)) (n : Subgroup.normalizer (K : Set G))
    (α : MulAut PSL(2, GaloisField p f)) :
    conjHom e n = α ↔ ∀ y, n * psl2Emb e y * (n : G)⁻¹ = psl2Emb e (α y) := by
  constructor
  · rintro rfl y
    rw [emb_conjHom]
  · intro h
    ext y
    apply emb_injective e
    rw [emb_conjHom, h]

theorem exists_coords (e : K ≃* PSL(2, GaloisField p f)) (hp : Odd p) (hf : 0 < f)
    (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) {T : Subgroup G} (hTK : T ≤ K) (hT : Nat.card T = 4) :
    ∃ (e' : K ≃* PSL(2, GaloisField p f)) (P₀ : Sylow 2 PSL(2, ZMod p)),
      T = ((P₀ : Subgroup PSL(2, ZMod p)).map
        (psl2Map (algebraMap (ZMod p) (GaloisField p f)))).map (psl2Emb e') := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := GaloisField p f
  set ι0 := psl2Map (algebraMap (ZMod p) F)
  have hp8 : p ^ 1 % 8 = 3 ∨ p ^ 1 % 8 = 5 := by
    rw [pow_one, ← pow_mod_eight_of_odd hp (odd_of_pow_mod_eight hp h8)]
    exact h8
  have hZ : Nat.card (ZMod p) = p ^ 1 := by rw [Nat.card_zmod, pow_one]
  obtain ⟨P₀⟩ : Nonempty (Sylow 2 PSL(2, ZMod p)) := inferInstance
  have hP₀ := psl2_sylow_two_card_eq_four (ZMod p) hZ hp one_pos hp8 P₀
  set V₀ := (P₀ : Subgroup PSL(2, ZMod p)).map ι0
  have hV₀ : Nat.card V₀ = 4 := by
    rw [Subgroup.card_map_of_injective (psl2Map_injective _), hP₀]
  set T₀ := T.comap (psl2Emb e)
  have hT₀ : Nat.card T₀ = 4 := (card_comap_emb e hTK).trans hT
  have hS : ∀ X : Subgroup PSL(2, F), Nat.card X = 4 →
      Nat.card X = 2 ^ (Nat.card PSL(2, F)).factorization 2 := by
    intro X hX
    rw [hX, psl2_card_formula _ (isOddPrimePower_galoisField hp hf), GaloisField.card p f hf.ne',
      psl2_order_factorization_two_of_mod_eight h8]
    norm_num
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq PSL(2, F) (Sylow.ofCard T₀ (hS T₀ hT₀))
    (Sylow.ofCard V₀ (hS V₀ hV₀))
  have hkT : T₀.map (MulAut.conj k).toMonoidHom = V₀ := by
    have := congrArg (fun P : Sylow 2 PSL(2, F) => (P : Subgroup PSL(2, F))) hk
    simp only [Sylow.coe_subgroup_smul, Sylow.coe_ofCard] at this
    rw [← this]
    rfl
  refine ⟨e.trans (MulAut.conj k), P₀, ?_⟩
  have hemb : ∀ y, psl2Emb (e.trans (MulAut.conj k)) y = psl2Emb e (k⁻¹ * y * k) := by
    intro y
    simp [psl2Emb, MulEquiv.symm_trans_apply, MulAut.conj_symm_apply]
  ext x
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := exists_emb_eq e (hTK hx)
    have hyT : y ∈ T₀ := hx
    have hy : k * y * k⁻¹ ∈ V₀ := by
      rw [← hkT]
      exact ⟨y, hyT, rfl⟩
    refine ⟨k * y * k⁻¹, hy, ?_⟩
    rw [hemb]
    congr 1
    group
  · rintro ⟨v, hv, rfl⟩
    rw [hemb]
    have hv' : v ∈ V₀ := hv
    rw [← hkT] at hv'
    obtain ⟨y, hyT, hyv⟩ := hv'
    have : k⁻¹ * v * k = y := by
      rw [← hyv]
      simp [MulAut.conj_apply]
      group
    rw [this]
    exact hyT

theorem conj_eq_fieldAut
    (e' : K ≃* PSL(2, GaloisField p f)) (hp : Odd p) (hf : 0 < f)
    {P₀ : Sylow 2 PSL(2, ZMod p)} {T : Subgroup G}
    (hT : T = ((P₀ : Subgroup PSL(2, ZMod p)).map
      (psl2Map (algebraMap (ZMod p) (GaloisField p f)))).map (psl2Emb e'))
    (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) {g : G}
    (hgK : g ∈ Subgroup.normalizer (K : Set G)) (hgT : g ∈ Subgroup.centralizer (T : Set G))
    (hg : Odd (orderOf g)) :
    ∃ σ : GaloisField p f ≃+* GaloisField p f,
      ∀ y, g * psl2Emb e' y * g⁻¹ = psl2Emb e' (psl2FieldAut _ σ y) := by
  set F := GaloisField p f
  set ι0 := psl2Map (algebraMap (ZMod p) F)
  set V₀ := (P₀ : Subgroup PSL(2, ZMod p)).map ι0
  have hp8 : p ^ 1 % 8 = 3 ∨ p ^ 1 % 8 = 5 := by
    rw [pow_one, ← pow_mod_eight_of_odd hp (odd_of_pow_mod_eight hp h8)]
    exact h8
  have hZ : Nat.card (ZMod p) = p ^ 1 := by rw [Nat.card_zmod, pow_one]
  have hV₀ : IsKleinFour V₀ := isKleinFour_map_of_injective _
    (psl2_sylow_two_isKleinFour (ZMod p) hZ hp one_pos hp8 P₀) _ (psl2Map_injective _)
  have hV₀fix : ∀ τ : F ≃+* F, ∀ v ∈ V₀, psl2FieldAut _ τ v = v := by
    rintro τ _ ⟨x, -, rfl⟩
    exact psl2FieldAut_psl2Map_zmod τ x
  set α := conjHom e' ⟨g, hgK⟩
  have hαodd : Odd (orderOf α) := by
    have h1 : orderOf α ∣ orderOf (⟨g, hgK⟩ : Subgroup.normalizer (K : Set G)) :=
      orderOf_map_dvd _ _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hg h1
  have hαV : ∀ v ∈ V₀, α v = v := by
    intro v hv
    apply emb_injective e'
    rw [emb_conjHom]
    have hvT : psl2Emb e' v ∈ T := by
      rw [hT]
      exact ⟨v, hv, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp hgT _ hvT
    change g * psl2Emb e' v * g⁻¹ = psl2Emb e' v
    rw [← this, mul_inv_cancel_right]
  obtain ⟨σ, hσ⟩ := eq_psl2FieldAut_of_odd hp hf hV₀ hV₀fix α hαodd hαV
  exact ⟨σ, (conjHom_eq_iff e' _ _).mp hσ⟩

theorem exists_fixed_three
    (e' : K ≃* PSL(2, GaloisField p f)) (hp : Odd p)
    {P₀ : Sylow 2 PSL(2, ZMod p)} {T : Subgroup G}
    (hT : T = ((P₀ : Subgroup PSL(2, ZMod p)).map
      (psl2Map (algebraMap (ZMod p) (GaloisField p f)))).map (psl2Emb e'))
    (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) :
    ∃ y : PSL(2, GaloisField p f), orderOf y = 3 ∧
      psl2Emb e' y ∈ Subgroup.normalizer (T : Set G) ∧
      ∀ σ : GaloisField p f ≃+* GaloisField p f, psl2FieldAut _ σ y = y := by
  set F := GaloisField p f
  set ι0 := psl2Map (algebraMap (ZMod p) F)
  have hp8 : p ^ 1 % 8 = 3 ∨ p ^ 1 % 8 = 5 := by
    rw [pow_one, ← pow_mod_eight_of_odd hp (odd_of_pow_mod_eight hp h8)]
    exact h8
  have hZ : Nat.card (ZMod p) = p ^ 1 := by rw [Nat.card_zmod, pow_one]
  have hP₀ := psl2_sylow_two_isKleinFour (ZMod p) hZ hp one_pos hp8 P₀
  have h12 := card_normalizer_kleinFour_psl2 (ZMod p) hZ hp one_pos hp8 hP₀
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.normalizer
    ((P₀ : Subgroup PSL(2, ZMod p)) : Set PSL(2, ZMod p))) 3 (by rw [h12]; norm_num)
  refine ⟨ι0 z, ?_, ?_, fun σ => psl2FieldAut_psl2Map_zmod σ z⟩
  · rw [orderOf_injective ι0 (psl2Map_injective _), Subgroup.orderOf_coe, hz]
  · have hzN : ι0 z ∈ Subgroup.normalizer
        (((P₀ : Subgroup PSL(2, ZMod p)).map ι0 : Subgroup PSL(2, F)) : Set PSL(2, F)) := by
      have h := JT.map_normalizer_of_injective ι0 (psl2Map_injective _)
        (P₀ : Subgroup PSL(2, ZMod p))
      have : ι0 z ∈ (Subgroup.normalizer ((P₀ : Subgroup PSL(2, ZMod p)) :
          Set PSL(2, ZMod p))).map ι0 := ⟨z, z.2, rfl⟩
      rw [h] at this
      exact this.2
    have h := JT.map_normalizer_of_injective (psl2Emb e') (emb_injective e')
      ((P₀ : Subgroup PSL(2, ZMod p)).map ι0)
    have hmem : psl2Emb e' (ι0 z) ∈ (psl2Emb e').range ⊓ Subgroup.normalizer
        ((((P₀ : Subgroup PSL(2, ZMod p)).map ι0).map (psl2Emb e') : Subgroup G) : Set G) := by
      rw [← h]
      exact ⟨ι0 z, hzN, rfl⟩
    rw [hT]
    exact hmem.2

end PSL2Sub

end Ambient

end CFSG.Walter.W67
