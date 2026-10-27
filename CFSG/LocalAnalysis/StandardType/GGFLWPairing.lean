module

public import CFSG.LocalAnalysis.StandardType.GGFLWTree
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l6w3_two_ne_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
    ((ZMod.natCast_eq_zero_iff 2 p).mp h))

private theorem l6w3_comm_iff_sq {G : Type*} [Group G] {s t : G} (hss : s * s = 1)
    (htt : t * t = 1) : s * t = t * s ↔ (s * t) ^ 2 = 1 := by
  have hs_inv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  constructor
  · intro h
    rw [← isSelfInv_iff_sq_eq_one, isSelfInv_iff]
    calc (s * t)⁻¹ = t⁻¹ * s⁻¹ := mul_inv_rev s t
      _ = t * s := by rw [ht_inv, hs_inv]
      _ = s * t := h.symm
  · intro h
    rw [← isSelfInv_iff_sq_eq_one, isSelfInv_iff] at h
    calc s * t = (s * t)⁻¹ := h.symm
      _ = t⁻¹ * s⁻¹ := mul_inv_rev s t
      _ = t * s := by rw [ht_inv, hs_inv]

private theorem l6w3_prod_sq_apply {p : ℕ} [Fact p.Prime] {T : Type} [AddCommGroup T]
    [Module (ZMod p) T] (r s : T ≃ₗ[ZMod p] T) (x y : T) (φ ψ : Module.Dual (ZMod p) T)
    (hr : ∀ v, r v = v - φ v • x) (hs : ∀ v, s v = v - ψ v • y)
    (hφx : φ x = 2) (hψy : ψ y = 2) (hφy : φ y = 0) :
    ∀ v, ((s * r) ^ 2) v = v - (ψ x * φ v) • y := by
  intro v
  set u : T := (s * r) v with hu
  have hu_eq : u = v - φ v • x - (ψ v - φ v * ψ x) • y := by
    rw [hu, LinearEquiv.mul_apply, hr, hs, map_sub, map_smul]
    rfl
  have hφu : φ u = -φ v := by
    rw [hu_eq]
    simp only [map_sub, map_smul, hφx, hφy, smul_zero, mul_zero, sub_zero, smul_eq_mul]
    ring
  have hψu : ψ u = -ψ v + φ v * ψ x := by
    rw [hu_eq]
    simp only [map_sub, map_smul, hψy, hφy, smul_zero, mul_zero, sub_zero, smul_eq_mul]
    ring
  have hsu : (s * r) u = u - φ u • x - (ψ u - φ u • ψ x) • y := by
    rw [LinearEquiv.mul_apply, hr, hs, map_sub, map_smul]
  have h2 : ((s * r) ^ 2) v = (s * r) u := by
    rw [pow_two, LinearEquiv.mul_apply, hu]
  rw [h2, hsu, hφu, hψu, hu_eq]
  module

private theorem l6w3_eq_of_pairing_ne {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {T : Type}
    [AddCommGroup T] [Module (ZMod p) T] {s t : T ≃ₗ[ZMod p] T} (x y : T)
    (φ ψ : Module.Dual (ZMod p) T) (hs : ∀ v, s v = v - φ v • x)
    (ht : ∀ v, t v = v - ψ v • y) (hφx : φ x = 2) (hψy : ψ y = 2)
    (hE : ∀ v, (ψ v * φ y) • x = (φ v * ψ x) • y) (hφy : φ y ≠ 0) : s = t := by
  have h2ne : (2 : ZMod p) ≠ 0 := l6w3_two_ne_zero hp2
  have hx : x ≠ 0 := fun h0 => by rw [h0, map_zero] at hφx; exact h2ne hφx.symm
  have hy : y ≠ 0 := fun h0 => by rw [h0, map_zero] at hψy; exact h2ne hψy.symm
  have hψv0 : ψ ((2⁻¹ : ZMod p) • y) = 1 := by
    rw [map_smul, hψy, smul_eq_mul, inv_mul_cancel₀ h2ne]
  have hE0 := hE ((2⁻¹ : ZMod p) • y)
  rw [hψv0, one_mul] at hE0
  have hψx : ψ x ≠ 0 := by
    intro h0
    rw [h0, mul_zero, zero_smul] at hE0
    exact hφy ((smul_eq_zero_iff_left hx).mp hE0)
  have hEx : φ y • x = (2 : ZMod p) • y := by
    have h1 := hE x
    rw [hφx] at h1
    rw [mul_comm (2 : ZMod p) (ψ x)] at h1
    rw [mul_smul, mul_smul] at h1
    exact (smul_right_inj hψx).mp h1
  have hEy : (2 : ZMod p) • x = ψ x • y := by
    have h1 := hE y
    rw [hψy] at h1
    rw [mul_comm (2 : ZMod p) (φ y)] at h1
    rw [mul_smul, mul_smul] at h1
    exact (smul_right_inj hφy).mp h1
  ext v
  rw [hs, ht]
  have hmain : φ v • x = ψ v • y := by
    have h1 : (2 : ZMod p) • (ψ v • y) = (2 : ZMod p) • (φ v • x) := by
      calc (2 : ZMod p) • (ψ v • y) = ψ v • ((2 : ZMod p) • y) := by
            rw [smul_smul, smul_smul, mul_comm (2 : ZMod p) (ψ v)]
        _ = ψ v • (φ y • x) := by rw [← hEx]
        _ = (ψ v * φ y) • x := by rw [smul_smul]
        _ = (φ v * ψ x) • y := hE v
        _ = φ v • (ψ x • y) := by rw [smul_smul]
        _ = φ v • ((2 : ZMod p) • x) := by rw [← hEy]
        _ = (2 : ZMod p) • (φ v • x) := by
            rw [smul_smul, smul_smul, mul_comm (2 : ZMod p) (φ v)]
    exact ((smul_right_inj h2ne).mp h1).symm
  rw [hmain]

private theorem l6w3_comm_pairing {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {T : Type}
    [AddCommGroup T] [Module (ZMod p) T] {s t : T ≃ₗ[ZMod p] T} (x y : T)
    (φ ψ : Module.Dual (ZMod p) T) (hs : ∀ v, s v = v - φ v • x)
    (ht : ∀ v, t v = v - ψ v • y) (hφx : φ x = 2) (hψy : ψ y = 2)
    (hst : s ≠ t) (hcomm : s * t = t * s) : φ y = 0 ∧ ψ x = 0 := by
  have hdiff : ∀ v, s (t v) - t (s v) = (ψ v * φ y) • x - (φ v * ψ x) • y := by
    intro v
    simp only [ht, hs, map_sub, map_smul]
    module
  have hE : ∀ v, (ψ v * φ y) • x = (φ v * ψ x) • y := by
    intro v
    have hv : (s * t) v = (t * s) v := congrArg (fun e : T ≃ₗ[ZMod p] T => e v) hcomm
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at hv
    have h0 : s (t v) - t (s v) = 0 := sub_eq_zero.mpr hv
    rw [hdiff v] at h0
    exact sub_eq_zero.mp h0
  constructor
  · by_contra hφy
    exact hst (l6w3_eq_of_pairing_ne hp2 x y φ ψ hs ht hφx hψy hE hφy)
  · by_contra hψx
    exact hst (l6w3_eq_of_pairing_ne hp2 y x ψ φ ht hs hψy hφx (fun v => (hE v).symm) hψx).symm

private theorem l6w3_one_sided_pow {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {T : Type} [AddCommGroup T]
    [Module (ZMod p) T] (r s : T ≃ₗ[ZMod p] T) (x y : T) (φ ψ : Module.Dual (ZMod p) T)
    (hr : ∀ v, r v = v - φ v • x) (hs : ∀ v, s v = v - ψ v • y)
    (hφx : φ x = 2) (hψy : ψ y = 2) (hφy : φ y = 0) (hψx : ψ x ≠ 0) :
    (s * r) ^ 3 ≠ 1 ∧ (s * r) ^ 4 ≠ 1 := by
  have h2ne : (2 : ZMod p) ≠ 0 := l6w3_two_ne_zero hp2
  have hy : y ≠ 0 := fun h0 => by rw [h0, map_zero] at hψy; exact h2ne hψy.symm
  have hkey : ∀ v, ((s * r) ^ 2) v = v - (ψ x * φ v) • y :=
    l6w3_prod_sq_apply r s x y φ ψ hr hs hφx hψy hφy
  have hsry : (s * r) y = -y := by
    rw [LinearEquiv.mul_apply, hr, hφy, zero_smul, sub_zero, hs, hψy]
    module
  constructor
  · intro h3
    have h1 : ((s * r) ^ 3) y = y := by rw [h3]; rfl
    have h2 : ((s * r) ^ 3) y = -y := by
      rw [pow_succ, LinearEquiv.mul_apply, hsry, hkey, map_neg, hφy]
      simp
    rw [h2] at h1
    have h3' : (2 : ZMod p) • y = 0 := by
      have : y + y = 0 := by
        have h4 : -y + y = y + y := by rw [h1]
        rw [neg_add_cancel] at h4
        exact h4.symm
      rw [two_smul]
      exact this
    exact hy ((smul_eq_zero_iff_right h2ne).mp h3')
  · intro h4
    have hφv0 : φ ((2⁻¹ : ZMod p) • x) = 1 := by
      rw [map_smul, hφx, smul_eq_mul, inv_mul_cancel₀ h2ne]
    have h4v : ((s * r) ^ 4) ((2⁻¹ : ZMod p) • x) = (2⁻¹ : ZMod p) • x := by rw [h4]; rfl
    have hpow : (s * r) ^ 4 = ((s * r) ^ 2) * ((s * r) ^ 2) := by rw [← pow_add]
    rw [hpow, LinearEquiv.mul_apply, hkey, hkey] at h4v
    simp only [map_sub, map_smul, hφy, hφv0, smul_eq_mul, mul_zero, sub_zero, mul_one] at h4v
    have h5 : ψ x • y + ψ x • y = 0 := by
      have h6 := h4v
      rw [sub_sub, sub_eq_self] at h6
      exact h6
    have h7 : ((2 : ZMod p) * ψ x) • y = 0 := by rw [two_mul, add_smul]; exact h5
    rcases smul_eq_zero.mp h7 with h8 | h8
    · rcases mul_eq_zero.mp h8 with h9 | h9
      · exact h2ne h9
      · exact hψx h9
    · exact hy h8

theorem ggFLW_pairing_edge {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {T : Type} [AddCommGroup T]
    [Module (ZMod p) T] {ι : Type} (M : CoxeterMatrix ι) (hW : GGIsWeylMatrix M)
    (Q : Subgroup (T ≃ₗ[ZMod p] T)) (f : M.Group ≃* ↥Q) (c : ι → T)
    (β : ι → Module.Dual (ZMod p) T)
    (hform : ∀ i v, ((f (M.simple i) : ↥Q) : T ≃ₗ[ZMod p] T) v = v - β i v • c i)
    (hβc : ∀ i, β i (c i) = 2)
    (hb6 : ∀ a b : ι, a ≠ b → M.M a b ≠ 6)
    (i j : ι) (hij : i ≠ j) :
    (β i (c j) = 0 ↔ M.M i j = 2) ∧ (β j (c i) = 0 ↔ M.M i j = 2) := by
  classical
  have hpprime : p.Prime := Fact.out
  set s : T ≃ₗ[ZMod p] T := ((f (M.simple i) : ↥Q) : T ≃ₗ[ZMod p] T) with hs_def
  set t : T ≃ₗ[ZMod p] T := ((f (M.simple j) : ↥Q) : T ≃ₗ[ZMod p] T) with ht_def
  have hs : ∀ v, s v = v - β i v • c i := fun v => by rw [hs_def]; exact hform i v
  have ht : ∀ v, t v = v - β j v • c j := fun v => by rw [ht_def]; exact hform j v
  have hαh : β i (c i) = 2 := hβc i
  have hβk : β j (c j) = 2 := hβc j
  have hss : s * s = 1 := by
    rw [hs_def]
    show ((f (M.simple i) : ↥Q) : T ≃ₗ[ZMod p] T) *
      ((f (M.simple i) : ↥Q) : T ≃ₗ[ZMod p] T) = 1
    rw [← Subgroup.coe_mul, ← map_mul,
      show M.simple i * M.simple i = 1 from
        CoxeterSystem.simple_mul_simple_self M.toCoxeterSystem i,
      map_one, Subgroup.coe_one]
  have htt : t * t = 1 := by
    rw [ht_def]
    show ((f (M.simple j) : ↥Q) : T ≃ₗ[ZMod p] T) *
      ((f (M.simple j) : ↥Q) : T ≃ₗ[ZMod p] T) = 1
    rw [← Subgroup.coe_mul, ← map_mul,
      show M.simple j * M.simple j = 1 from
        CoxeterSystem.simple_mul_simple_self M.toCoxeterSystem j,
      map_one, Subgroup.coe_one]
  have hord_st : orderOf (s * t) = M.M i j := by
    have hco : s * t = ((f (M.simple i) * f (M.simple j) : ↥Q) : T ≃ₗ[ZMod p] T) := by
      rw [hs_def, ht_def, Subgroup.coe_mul]
    rw [hco, Subgroup.orderOf_coe, ← map_mul, MulEquiv.orderOf_eq,
      ← CoxeterMatrix.toCoxeterSystem_simple]
    exact CoxeterSystem.orderOf_simple_mul_simple M.toCoxeterSystem i j
  have hord : orderOf (t * s) = M.M i j := by
    have h : t * s = (s * t)⁻¹ := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right htt, inv_eq_of_mul_eq_one_right hss]
    rw [h, orderOf_inv, hord_st]
  have hst_ne : s ≠ t := by
    intro hst
    have h1 : orderOf (t * s) = 1 := by rw [← hst, hss, orderOf_one]
    rw [hord] at h1
    exact M.off_diagonal i j hij h1
  have hcomm_iff : s * t = t * s ↔ M.M i j = 2 := by
    rw [l6w3_comm_iff_sq hss htt]
    constructor
    · intro h2
      have hdvd : M.M i j ∣ 2 := by
        rw [← hord_st]
        exact orderOf_dvd_iff_pow_eq_one.mpr h2
      rcases (show Nat.Prime 2 by norm_num).eq_one_or_self_of_dvd (M.M i j) hdvd with h1 | h2'
      · exact absurd h1 (M.off_diagonal i j hij)
      · exact h2'
    · intro hM2
      have hpow := pow_orderOf_eq_one (s * t)
      rwa [hord_st, hM2] at hpow
  have hAB_comm : β i (c j) = 0 ∧ β j (c i) = 0 → s * t = t * s := by
    intro hAB
    have hpoint : ∀ v, s (t v) = t (s v) := by
      intro v
      have hdiff : s (t v) - t (s v) =
          (β j v * β i (c j)) • c i - (β i v * β j (c i)) • c j := by
        simp only [ht, hs, map_sub, map_smul]
        module
      have h0 : s (t v) - t (s v) = 0 := by
        rw [hdiff, hAB.1, hAB.2, mul_zero, mul_zero, zero_smul, zero_smul, sub_zero]
      exact sub_eq_zero.mp h0
    ext v
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    exact hpoint v
  have hcomm_AB : s * t = t * s → β i (c j) = 0 ∧ β j (c i) = 0 :=
    l6w3_comm_pairing hp2 (c i) (c j) (β i) (β j) hs ht hαh hβk hst_ne
  have one_sided : ∀ (r s' : T ≃ₗ[ZMod p] T) (x y : T) (φ ψ : Module.Dual (ZMod p) T),
      (∀ v, r v = v - φ v • x) → (∀ v, s' v = v - ψ v • y) →
      φ x = 2 → ψ y = 2 → φ y = 0 → ψ x ≠ 0 →
      orderOf (s' * r) = M.M i j → M.M i j ≠ 2 → False := by
    intro r s' x y φ ψ hr hs' hφx hψy hφy hψx hord' hC
    obtain ⟨h3ne, h4ne⟩ := l6w3_one_sided_pow hp2 r s' x y φ ψ hr hs' hφx hψy hφy hψx
    have hpow := pow_orderOf_eq_one (s' * r)
    rw [hord'] at hpow
    rcases ggFLW_entries hW i j hij with h2 | h3 | h4 | h6
    · exact hC h2
    · rw [h3] at hpow; exact h3ne hpow
    · rw [h4] at hpow; exact h4ne hpow
    · exact hb6 i j hij h6
  have hnot_one_A : M.M i j ≠ 2 → β i (c j) = 0 → β j (c i) = 0 := by
    intro hC hA
    by_contra hB
    exact one_sided s t (c i) (c j) (β i) (β j) hs ht hαh hβk hA hB hord hC
  have hnot_one_B : M.M i j ≠ 2 → β j (c i) = 0 → β i (c j) = 0 := by
    intro hC hB
    by_contra hA
    exact one_sided t s (c j) (c i) (β j) (β i) ht hs hβk hαh hB hA hord_st hC
  refine ⟨?_, ?_⟩
  · constructor
    · intro hA
      by_contra hC
      exact hC (hcomm_iff.mp (hAB_comm ⟨hA, hnot_one_A hC hA⟩))
    · intro hC
      exact (hcomm_AB (hcomm_iff.mpr hC)).1
  · constructor
    · intro hB
      by_contra hC
      exact hC (hcomm_iff.mp (hAB_comm ⟨hnot_one_B hC hB, hB⟩))
    · intro hC
      exact (hcomm_AB (hcomm_iff.mpr hC)).2

end CFSG.StandardType

end
