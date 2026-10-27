module

public import CFSG.LocalAnalysis.StandardType.GGTriD4LineWeylData
import CFSG.LocalAnalysis.StandardType.GGTriD4LineWeylStruct
import CFSG.LocalAnalysis.StandardType.GGTriD4LineWeylOuter
import CFSG.LocalAnalysis.StandardType.GGTriD4LineLocal

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private lemma mulAut_conj_mul_assoc {G : Type*} [Group G] (γ : MulAut G) (x : G) :
    γ * MulAut.conj x * γ⁻¹ = MulAut.conj (γ x) := by
  ext y
  simp [MulAut.conj_apply]

private lemma mulAut_conj_mul {G : Type*} [Group G] (γ : MulAut G) (x : G) :
    γ * MulAut.conj x = MulAut.conj (γ x) * γ := by
  rw [← mulAut_conj_mul_assoc γ x]
  group

private lemma conj_mul_pow_three {G : Type*} [Group G] (γ : MulAut G) (x : G) :
    (MulAut.conj x * γ) ^ 3 = MulAut.conj (x * γ x * ((γ ^ 2) x)) * γ ^ 3 := by
  have h1 := mulAut_conj_mul γ x
  have h2 : (MulAut.conj x * γ) ^ 2 = MulAut.conj (x * γ x) * γ ^ 2 := by
    rw [pow_two]
    calc (MulAut.conj x * γ) * (MulAut.conj x * γ)
        = MulAut.conj x * (γ * MulAut.conj x) * γ := by group
      _ = MulAut.conj x * (MulAut.conj (γ x) * γ) * γ := by rw [h1]
      _ = MulAut.conj (x * γ x) * γ ^ 2 := by
            rw [show MulAut.conj x * (MulAut.conj (γ x) * γ) * γ =
                (MulAut.conj x * MulAut.conj (γ x)) * (γ * γ) by group]
            rw [← map_mul, ← pow_two]
  have h3 : (MulAut.conj x * γ) ^ 3 =
      MulAut.conj (x * γ x) * (γ ^ 2 * MulAut.conj x) * γ := by
    rw [pow_succ, h2]
    group
  rw [h3]
  rw [show MulAut.conj (x * γ x) * (γ ^ 2 * MulAut.conj x) * γ =
      MulAut.conj (x * γ x) * (MulAut.conj ((γ ^ 2) x) * γ ^ 2) * γ by
    rw [mulAut_conj_mul (γ ^ 2) x]]
  rw [show MulAut.conj (x * γ x) * (MulAut.conj ((γ ^ 2) x) * γ ^ 2) * γ =
      MulAut.conj (x * γ x * ((γ ^ 2) x)) * γ ^ 3 by
    rw [show MulAut.conj (x * γ x) * (MulAut.conj ((γ ^ 2) x) * γ ^ 2) * γ =
        (MulAut.conj (x * γ x) * MulAut.conj ((γ ^ 2) x)) * (γ ^ 2 * γ) by group]
    rw [← map_mul, ← pow_succ γ 2]]

private lemma triD4LineSigma_inv (k K : Type) [Field k] [Field K] [Algebra k K]
    (σ : K ≃ₐ[k] K) :
    triD4LineSigma k K σ⁻¹ = (triD4LineSigma k K σ).symm := by
  ext z
  apply (triD4LineSigma k K σ).injective
  rw [← triD4LineSigma_mul_apply k K σ σ⁻¹, mul_inv_cancel, triD4LineSigma_one_apply]
  exact (MulEquiv.apply_symm_apply (triD4LineSigma k K σ) z).symm

private lemma isElemAbelian_of_mulEquiv {G H : Type*} [Group G] [Group H] {p : ℕ}
    {E : Subgroup G} {F : Subgroup H} (e : E ≃* F) (h : IsElemAbelian p E) :
    IsElemAbelian p F := by
  constructor
  · rw [isMulCommutative_iff]
    intro a b
    apply e.symm.injective
    rw [map_mul, map_mul]
    exact isMulCommutative_iff.mp h.1 (e.symm a) (e.symm b)
  · intro a ha
    have h2 : (e.symm ⟨a, ha⟩) ^ p = 1 := by
      apply Subtype.ext
      simpa using h.2 (e.symm ⟨a, ha⟩).1 (e.symm ⟨a, ha⟩).2
    have h1 : (e (e.symm ⟨a, ha⟩)) ^ p = 1 := by
      simpa using congrArg e h2
    rw [e.apply_symm_apply] at h1
    simpa using congrArg Subtype.val h1

private lemma triD4Line_conj_step_aux {n : ℕ} (hn : 2 ≤ n) (hev : Even n)
    (K : Type) [Field K] (hK : Nat.card K = (2 ^ n) ^ 3)
    (k : Type) [Field k] [Algebra k K] (hk : Nat.card k = 2 ^ n)
    (D : TriD4LineKGXData n K k) (hZ : Subgroup.center (GGTriD4R n K) = ⊥)
    (A : Subgroup (MulAut (GGTriD4R n K))) (hA : IsElemAbelian 3 A)
    (hEAcard : Nat.card (triD4LineE n K A) = 9) (hz : MulAut.conj D.z₀ ∈ A)
    (e₀ : GGTriD4R n K) (he₀ : MulAut.conj e₀ ∈ A) (hline : e₀ ∉ Subgroup.zpowers D.z₀)
    (f : MulAut (GGTriD4R n K)) (hfA : f ∈ A) (hf3 : f ^ 3 = 1)
    (hdec : ∀ a ∈ A, ∃ e ∈ triD4LineE n K A, ∃ j : ℕ, a = MulAut.conj e * f ^ j)
    (x : GGTriD4R n K) (hxX0 : x ∈ Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K)))
    (γ : MulAut (GGTriD4R n K))
    (hγX0 : ∀ y : GGTriD4R n K,
      y ∈ Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K)) →
        γ y ∈ Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K)))
    (hfx : f = MulAut.conj x * γ) (hγ3 : γ ^ 3 = 1)
    (σ' : K ≃ₐ[k] K) (hσ' : orderOf σ' = 3)
    (hΘγ : ∀ y : Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K)),
      D.Θ ⟨γ y.1, hγX0 y.1 y.2⟩ = triD4LineSigma k K σ' (D.Θ y)) :
    ∃ m : GGTriD4R n K, (∀ a ∈ A, (m * (a m)⁻¹) ^ 3 = 1 ∧
        ∀ a' ∈ A, a' (m * (a m)⁻¹) = m * (a m)⁻¹) ∧
      m * e₀ * m⁻¹ ∉ Subgroup.zpowers e₀ := by
  classical
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hn1 : 1 ≤ n := by omega
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  haveI : Fintype k := Fintype.ofFinite k
  have hdeg : Module.finrank k K = 3 := by
    have hcard := Module.card_eq_pow_finrank (K := k) (V := K)
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hk, hK] at hcard
    have h2n : 2 ≤ 2 ^ n := by
      simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hn1
    exact (Nat.pow_right_injective h2n hcard).symm
  have h3 : 3 ∣ Nat.card k - 1 := by
    rw [hk]
    have hmod : 2 ^ n % 3 = 1 := by
      rw [CFSG.Timmesfeld.ExceptionalOrders.two_pow_mod_three]
      simp [hev]
    simpa [hmod] using Nat.dvd_sub_mod (n := 3) (2 ^ n)
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val (isMulCommutative_iff.mp hA.1 ⟨a, ha⟩ ⟨b, hb⟩)
  have hEA : IsElemAbelian 3 (triD4LineE n K A) := triD4Line_E_isElemAbelian K hZ A hA
  have hinj : Function.Injective (MulAut.conj : GGTriD4R n K →* MulAut (GGTriD4R n K)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    have hc : g ∈ Subgroup.center (GGTriD4R n K) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h2 := congrArg (fun φ : MulAut (GGTriD4R n K) => φ y) (MonoidHom.mem_ker.mp hg)
      simp only [MulAut.conj_apply, MulAut.one_apply] at h2
      calc y * g = (g * y * g⁻¹) * g := by rw [h2]
        _ = g * y := by group
    rw [hZ] at hc
    exact Subgroup.mem_bot.mp hc
  have hEAle : triD4LineE n K A ≤ Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K)) := by
    intro e he
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm : MulAut.conj e * MulAut.conj D.z₀ = MulAut.conj D.z₀ * MulAut.conj e :=
      hAc (MulAut.conj e) (mem_triD4LineE.mp he) (MulAut.conj D.z₀) hz
    exact hinj (by rw [map_mul, map_mul]; exact hcomm)
  let X₀ : Subgroup (GGTriD4R n K) := Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K))
  have hz0X0 : D.z₀ ∈ X₀ := by rw [Subgroup.mem_centralizer_singleton_iff]
  let z0X0 : X₀ := ⟨D.z₀, hz0X0⟩
  have hz0X0_center : z0X0 ∈ Subgroup.center X₀ := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp y.2
  let EA0 : Subgroup X₀ := (triD4LineE n K A).subgroupOf X₀
  let E : Subgroup (TriD4LineX k K) := EA0.map D.Θ.toMonoidHom
  let zX : TriD4LineX k K := D.Θ z0X0
  let x0 : X₀ := ⟨x, hxX0⟩
  let xX : TriD4LineX k K := D.Θ x0
  have hcardEA0 : Nat.card EA0 = Nat.card (triD4LineE n K A) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEAle).toEquiv
  have hEc : Nat.card E = 9 := by
    change Nat.card (EA0.map D.Θ.toMonoidHom) = 9
    rw [Subgroup.card_map_of_injective D.Θ.injective, hcardEA0, hEAcard]
  have hEA0 : IsElemAbelian 3 EA0 :=
    isElemAbelian_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hEAle).symm hEA
  have hE : IsElemAbelian 3 E := by
    change IsElemAbelian 3 (EA0.map D.Θ.toMonoidHom)
    exact isElemAbelian_of_mulEquiv
      (Subgroup.equivMapOfInjective EA0 D.Θ.toMonoidHom D.Θ.injective) hEA0
  have hzE : zX ∈ E := by
    change D.Θ z0X0 ∈ EA0.map D.Θ.toMonoidHom
    exact Subgroup.mem_map.mpr
      ⟨z0X0, Subgroup.mem_subgroupOf.mpr (mem_triD4LineE.mpr hz), rfl⟩
  have hzXord : orderOf zX = 3 := by
    change orderOf (D.Θ.toMonoidHom z0X0) = 3
    rw [orderOf_injective D.Θ.toMonoidHom D.Θ.injective z0X0]
    rw [show orderOf z0X0 = orderOf D.z₀ from
      (orderOf_injective (Subgroup.subtype X₀) (Subgroup.subtype_injective X₀) z0X0).symm]
    exact D.orderOf_z₀
  have hzc : zX ∈ Subgroup.center (TriD4LineX k K) := by
    change D.Θ z0X0 ∈ Subgroup.center (TriD4LineX k K)
    rw [← Subgroup.map_center_eq D.Θ]
    exact Subgroup.mem_map.mpr ⟨z0X0, hz0X0_center, rfl⟩
  have hx : ∀ e ∈ E, xX * triD4LineSigma k K σ' e * xX⁻¹ = e := by
    intro e he
    obtain ⟨e', he', rfl⟩ := Subgroup.mem_map.mp he
    have he'A : e'.1 ∈ triD4LineE n K A := Subgroup.mem_subgroupOf.mp he'
    have hcomm : f * MulAut.conj e'.1 = MulAut.conj e'.1 * f :=
      hAc f hfA (MulAut.conj e'.1) (mem_triD4LineE.mp he'A)
    have hleft : f * MulAut.conj e'.1 = MulAut.conj (x * γ e'.1) * γ := by
      rw [hfx, mul_assoc, mulAut_conj_mul γ e'.1, ← mul_assoc, ← map_mul]
    have hright : MulAut.conj e'.1 * f = MulAut.conj (e'.1 * x) * γ := by
      rw [hfx, ← mul_assoc, ← map_mul]
    have hcancel : MulAut.conj (x * γ e'.1) * γ = MulAut.conj (e'.1 * x) * γ := by
      rw [← hleft, hcomm, hright]
    have hxc : x * γ e'.1 = e'.1 * x := hinj (mul_right_cancel hcancel)
    have hfix : x * γ e'.1 * x⁻¹ = e'.1 := by
      rw [hxc, mul_assoc, mul_inv_cancel, mul_one]
    calc D.Θ x0 * triD4LineSigma k K σ' (D.Θ e') * (D.Θ x0)⁻¹
        = D.Θ x0 * D.Θ ⟨γ e'.1, hγX0 e'.1 e'.2⟩ * (D.Θ x0)⁻¹ := by rw [← hΘγ e']
      _ = D.Θ (x0 * ⟨γ e'.1, hγX0 e'.1 e'.2⟩ * x0⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = D.Θ e' := by
            congr 1
            apply Subtype.ext
            simpa using hfix
  have hx3R : x * γ x * ((γ ^ 2) x) = 1 := by
    have hc3 : MulAut.conj (x * γ x * ((γ ^ 2) x)) = 1 := by
      have h := conj_mul_pow_three γ x
      rw [hfx] at hf3
      rw [h, hγ3, mul_one] at hf3
      exact hf3
    exact hinj (by rw [map_one]; exact hc3)
  have hγγ : ∀ y : X₀, γ (γ y.1) = (γ ^ 2) y.1 := by
    intro y
    rw [pow_two, MulAut.mul_apply]
  have hσ1x : triD4LineSigma k K σ' (D.Θ x0) = D.Θ (⟨γ x, hγX0 x hxX0⟩ : X₀) :=
    (hΘγ x0).symm
  have hσ2x : triD4LineSigma k K (σ' ^ 2) (D.Θ x0) =
      D.Θ (⟨γ (γ x), hγX0 (γ x) (hγX0 x hxX0)⟩ : X₀) := by
    rw [pow_two, triD4LineSigma_mul_apply, ← hΘγ x0, ← hΘγ ⟨γ x, hγX0 x hxX0⟩]
  have hx3prod : x0 * (⟨γ x, hγX0 x hxX0⟩ : X₀) *
      (⟨γ (γ x), hγX0 (γ x) (hγX0 x hxX0)⟩ : X₀) = 1 := by
    apply Subtype.ext
    change x * γ x * γ (γ x) = 1
    rw [hγγ x0]
    exact hx3R
  have hx3eq : xX * triD4LineSigma k K σ' xX * triD4LineSigma k K (σ' ^ 2) xX = 1 := by
    change D.Θ x0 * triD4LineSigma k K σ' (D.Θ x0) *
        triD4LineSigma k K (σ' ^ 2) (D.Θ x0) = 1
    rw [hσ1x, hσ2x, ← map_mul, ← map_mul, hx3prod, map_one]
  have hx3 : xX * triD4LineSigma k K σ' xX * triD4LineSigma k K (σ' ^ 2) xX ∈
      Subgroup.center (TriD4LineX k K) := by
    rw [hx3eq]
    exact Subgroup.one_mem _
  have he0E : e₀ ∈ triD4LineE n K A := mem_triD4LineE.mpr he₀
  have he0X0 : e₀ ∈ X₀ := hEAle he0E
  let e0X0 : X₀ := ⟨e₀, he0X0⟩
  have he0Eimg : D.Θ e0X0 ∈ E := by
    change D.Θ e0X0 ∈ EA0.map D.Θ.toMonoidHom
    exact Subgroup.mem_map.mpr ⟨e0X0, Subgroup.mem_subgroupOf.mpr he0E, rfl⟩
  have hline' : D.Θ e0X0 ∉ Subgroup.zpowers zX := by
    intro hmem
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h1 : z0X0 ^ j = e0X0 := by
      calc z0X0 ^ j = D.Θ.symm (D.Θ z0X0) ^ j := by rw [D.Θ.symm_apply_apply]
        _ = D.Θ.symm (zX ^ j) := by rw [← map_zpow]
        _ = D.Θ.symm (D.Θ e0X0) := by rw [hj]
        _ = e0X0 := D.Θ.symm_apply_apply e0X0
    have h2 : D.z₀ ^ j = e₀ := by
      simpa using congrArg Subtype.val h1
    exact hline (Subgroup.mem_zpowers_iff.mpr ⟨j, h2⟩)
  obtain ⟨nX, hnE, hnMove, hnComm⟩ :=
    triD4LineX_moves_line k K hdeg h3 σ' hσ' zX hzXord hzc E hE hEc hzE xX hx hx3
      (D.Θ e0X0) he0Eimg hline'
  let m0 : X₀ := D.Θ.symm nX
  let m : GGTriD4R n K := m0
  have hm : ∀ e ∈ triD4LineE n K A, m * e * m⁻¹ ∈ triD4LineE n K A := by
    intro e he
    let e0e : X₀ := ⟨e, hEAle he⟩
    have heEimg : D.Θ e0e ∈ E := by
      change D.Θ e0e ∈ EA0.map D.Θ.toMonoidHom
      exact Subgroup.mem_map.mpr ⟨e0e, Subgroup.mem_subgroupOf.mpr he, rfl⟩
    have hnorm := hnE (D.Θ e0e) heEimg
    have htheta : D.Θ (m0 * e0e * m0⁻¹) = nX * D.Θ e0e * nX⁻¹ := by
      rw [map_mul, map_mul, map_inv, D.Θ.apply_symm_apply]
    have hmem : m0 * e0e * m0⁻¹ ∈ EA0 := by
      have : D.Θ (m0 * e0e * m0⁻¹) ∈ EA0.map D.Θ.toMonoidHom := by
        rw [htheta]; exact hnorm
      obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp this
      rwa [D.Θ.injective hyeq] at hy
    simpa using Subgroup.mem_subgroupOf.mp hmem
  have hmf : m * (f m)⁻¹ ∈ triD4LineE n K A := by
    have hfm_val : f (↑m0) = x * γ (↑m0) * x⁻¹ := by
      rw [hfx, MulAut.mul_apply, MulAut.conj_apply]
    have hfm_mem : f (↑m0) ∈ X₀ := by
      rw [hfm_val]
      exact X₀.mul_mem (X₀.mul_mem hxX0 (hγX0 ↑m0 m0.2)) (X₀.inv_mem hxX0)
    let fm0 : X₀ := ⟨f (↑m0), hfm_mem⟩
    have hfm_eq : fm0 = x0 * ⟨γ (↑m0), hγX0 ↑m0 m0.2⟩ * x0⁻¹ := by
      apply Subtype.ext
      exact hfm_val
    have hfm_theta : D.Θ fm0 = xX * triD4LineSigma k K σ' nX * xX⁻¹ := by
      rw [hfm_eq, map_mul, map_mul, map_inv, hΘγ m0, D.Θ.apply_symm_apply]
    have heq : D.Θ (m0 * fm0⁻¹) = nX * (xX * triD4LineSigma k K σ' nX * xX⁻¹)⁻¹ := by
      rw [map_mul, map_inv, hfm_theta, D.Θ.apply_symm_apply]
    have hmem : m0 * fm0⁻¹ ∈ EA0 := by
      have : D.Θ (m0 * fm0⁻¹) ∈ EA0.map D.Θ.toMonoidHom := by
        rw [heq]; exact hnComm
      obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp this
      rwa [D.Θ.injective hyeq] at hy
    simpa using Subgroup.mem_subgroupOf.mp hmem
  have hmove : m * e₀ * m⁻¹ ∉ Subgroup.zpowers e₀ := by
    intro hmem
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
    apply hnMove
    have heq : D.Θ (m0 * e0X0 * m0⁻¹) = nX * D.Θ e0X0 * nX⁻¹ := by
      rw [map_mul, map_mul, map_inv, D.Θ.apply_symm_apply]
    rw [← heq, Subgroup.mem_zpowers_iff]
    refine ⟨j, ?_⟩
    rw [← map_zpow]
    congr 1
    apply Subtype.ext
    simpa using hj
  exact ⟨m, triD4Line_clause_of_gens K hZ A hA f hfA hdec m hm hmf, hmove⟩

theorem triD4Line_conj_step
    {n : ℕ} (hn : 2 ≤ n) (hev : Even n) (K : Type) [Field K] (hK : Nat.card K = (2 ^ n) ^ 3)
    (k : Type) [Field k] [Algebra k K] (hk : Nat.card k = 2 ^ n) (D : TriD4LineKGXData n K k)
    (A : Subgroup (MulAut (GGTriD4R n K))) (hA : IsElemAbelian 3 A) (h27 : 27 ≤ Nat.card A)
    (hz : MulAut.conj D.z₀ ∈ A) (e₀ : GGTriD4R n K) (he₀ : MulAut.conj e₀ ∈ A)
    (hline : e₀ ∉ Subgroup.zpowers D.z₀) :
    ∃ m : GGTriD4R n K, (∀ a ∈ A, (m * (a m)⁻¹) ^ 3 = 1 ∧
        ∀ a' ∈ A, a' (m * (a m)⁻¹) = m * (a m)⁻¹) ∧
      m * e₀ * m⁻¹ ∉ Subgroup.zpowers e₀ := by
  have hn1 : 1 ≤ n := by omega
  have hZ : Subgroup.center (GGTriD4R n K) = ⊥ := triD4Line_center_bot hn1 K hK
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val (isMulCommutative_iff.mp hA.1 ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨hEAcard, f, hfA, hfo, hf3, hdec⟩ :=
    triD4Line_A_structure hn1 hev K hK A hA h27
  obtain ⟨x, hxX0, hfx | hfx⟩ :=
    triD4Line_outer_form hn1 K hK k D A hAc hz f hfA hfo hf3
  · have hα3 : D.α ^ 3 = 1 := by
      rw [← D.orderOf_α]; exact pow_orderOf_eq_one D.α
    have hαX0 : ∀ y : GGTriD4R n K,
        y ∈ Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K)) →
          D.α y ∈ Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K)) := by
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
      rw [← D.α_z₀, ← map_mul, ← map_mul, hy]
    refine triD4Line_conj_step_aux hn hev K hK k hk D hZ A hA hEAcard hz e₀ he₀ hline
      f hfA hf3 hdec x hxX0 D.α hαX0 hfx hα3 D.σ D.orderOf_σ ?_
    intro y
    exact D.Θ_α y (hαX0 y.1 y.2)
  · have hα3 : D.α ^ 3 = 1 := by
      rw [← D.orderOf_α]; exact pow_orderOf_eq_one D.α
    have hαinv3 : (D.α⁻¹) ^ 3 = 1 := by rw [inv_pow, hα3, inv_one]
    have hαinvz : D.α⁻¹ D.z₀ = D.z₀ := by
      apply D.α.injective
      rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply, D.α_z₀]
    have hαinvX0 : ∀ y : GGTriD4R n K,
        y ∈ Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K)) →
          D.α⁻¹ y ∈ Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K)) := by
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
      rw [← hαinvz, ← map_mul, ← map_mul, hy]
    have hσinv : orderOf D.σ⁻¹ = 3 := by rw [orderOf_inv, D.orderOf_σ]
    refine triD4Line_conj_step_aux hn hev K hK k hk D hZ A hA hEAcard hz e₀ he₀ hline
      f hfA hf3 hdec x hxX0 D.α⁻¹ hαinvX0 hfx hαinv3 D.σ⁻¹ hσinv ?_
    intro y
    let y' : Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K)) :=
      ⟨D.α⁻¹ y.1, hαinvX0 y.1 y.2⟩
    have hy' : D.α y'.1 ∈ Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K)) := by
      change D.α (D.α⁻¹ y.1) ∈ Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K))
      rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
      exact y.2
    have h := D.Θ_α y' hy'
    have hyeq : (⟨D.α y'.1, hy'⟩ : Subgroup.centralizer ({D.z₀} : Set (GGTriD4R n K))) = y := by
      apply Subtype.ext
      exact D.α.apply_symm_apply y.1
    have h2 : D.Θ y = triD4LineSigma k K D.σ (D.Θ y') := by
      rw [← hyeq]; exact h
    have hstep : D.Θ y' = (triD4LineSigma k K D.σ).symm (D.Θ y) := by
      rw [h2]
      exact (MulEquiv.symm_apply_apply (triD4LineSigma k K D.σ) (D.Θ y')).symm
    rw [triD4LineSigma_inv k K D.σ]
    exact hstep

end CFSG.StandardType
