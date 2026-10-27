module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4Seven
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4SevenEl
public import CFSG.Quasithin.H13.L32NKGSp6Norm
public import CFSG.Quasithin.H13.L32NKGSp6Darboux
public import CFSG.Quasithin.H13.L32NKGSp6Transport
public import Certificates.Certificate4157

public section

namespace CFSG.Quasithin.H13

namespace G112Seven

open CFSG.KGroups.Sp6 CFSG.Quasithin.H13.KGSp6

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem card_normalizer_le {B : LinearMap.BilinForm (ZMod 2) V}
    (halt : ∀ v, B v v = 0) (hnd : ∀ v, (∀ w, B v w = 0) → v = 0)
    (hdim : Module.finrank (ZMod 2) V = 6) {Γ : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hΓB : ∀ γ ∈ Γ, ∀ v w, B (γ v) (γ w) = B v w) {x : ↥Γ} (hx : orderOf x = 7) :
    Nat.card (Subgroup.normalizer ((Subgroup.zpowers x : Subgroup ↥Γ) : Set ↥Γ)) ≤ 42 := by
  classical
  obtain ⟨b0, hb0⟩ := exists_darboux B halt hnd hdim
  have hiso : ∀ γ ∈ Γ, phi b0 γ ∈ SpU := fun γ hγ => isIso_toMatrix b0 B hb0 (hΓB γ hγ)
  have hx7 : orderOf (phi b0 (x : V ≃ₗ[ZMod 2] V)) = 7 := by
    rw [orderOf_injective (phi b0) (phi_injective b0), Subgroup.orderOf_coe, hx]
  obtain ⟨c, hc, hmem⟩ := exists_conj_P0 Certificates.certificate4157.1 (hiso _ x.2) hx7
  set ψ : ↥Γ →* Mat6ˣ := (MulAut.conj c).toMonoidHom.comp ((phi b0).comp Γ.subtype) with hψ
  have hψapp : ∀ y : ↥Γ, ψ y = c * phi b0 (y : V ≃ₗ[ZMod 2] V) * c⁻¹ := fun y => rfl
  have hψinj : Function.Injective ψ := fun y z h => by
    rw [hψapp, hψapp, mul_left_inj, mul_right_inj] at h
    exact Subtype.ext (phi_injective b0 h)
  have hψx : Subgroup.zpowers (ψ x) = Subgroup.zpowers s0u := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 (hψapp x ▸ hmem)) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_s0u, orderOf_injective ψ hψinj, hx]
  have hs0 : s0u ∈ Subgroup.zpowers (ψ x) := hψx ▸ Subgroup.mem_zpowers s0u
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hs0
  have hmap : ∀ y ∈ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup ↥Γ) : Set ↥Γ),
      colsOf ((ψ y : Mat6ˣ) : Mat6) ∈ n0List := by
    intro y hy
    refine colsOf_mem_n0List Certificates.certificate4157.2.1
      (SpU.mul_mem (SpU.mul_mem hc (hiso _ y.2)) (SpU.inv_mem hc)) ?_
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1
      ((Subgroup.mem_normalizer_iff.1 hy x).1 (Subgroup.mem_zpowers x))
    rw [← hψx, ← hm, ← conj_zpow, ← map_inv, ← map_mul, ← map_mul, ← hk, map_zpow, ← zpow_mul]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
  have hinj : Function.Injective fun y :
      ↥(Subgroup.normalizer ((Subgroup.zpowers x : Subgroup ↥Γ) : Set ↥Γ)) =>
      (⟨colsOf ((ψ y : Mat6ˣ) : Mat6), List.mem_toFinset.2 (hmap y y.2)⟩ : ↥n0List.toFinset) :=
    fun y z h => Subtype.ext (hψinj (colsOf_injective (congrArg Subtype.val h)))
  calc Nat.card (Subgroup.normalizer ((Subgroup.zpowers x : Subgroup ↥Γ) : Set ↥Γ))
      ≤ Nat.card ↥n0List.toFinset := Nat.card_le_card_of_injective _ hinj
    _ ≤ n0List.length := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      exact List.toFinset_card_le _
    _ = 42 := n0List_length

theorem card_le_six_mul {B : LinearMap.BilinForm (ZMod 2) V}
    (halt : ∀ v, B v v = 0) (hnd : ∀ v, (∀ w, B v w = 0) → v = 0)
    (hdim : Module.finrank (ZMod 2) V = 6) {Γ : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hΓB : ∀ γ ∈ Γ, ∀ v w, B (γ v) (γ w) = B v w) (hΓ7 : (Nat.card Γ).factorization 7 = 1)
    (N : Subgroup ↥Γ) [N.Normal] (h7 : 7 ∣ Nat.card N) : Nat.card Γ ≤ 6 * Nat.card N := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hΓ0 : Nat.card Γ ≠ 0 := fun h => by rw [h] at hΓ7; simp at hΓ7
  have : Finite Γ := Nat.finite_of_card_ne_zero hΓ0
  have hN0 : Nat.card N ≠ 0 := Nat.card_pos.ne'
  have hN7 : (Nat.card N).factorization 7 = 1 := by
    refine le_antisymm ?_ ((Nat.Prime.dvd_iff_one_le_factorization (by norm_num) hN0).1 h7)
    have := (Nat.factorization_le_iff_dvd hN0 hΓ0).2 (Subgroup.card_subgroup_dvd_card N) 7
    rwa [hΓ7] at this
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := N) 7 h7
  let P : Sylow 7 ↥N := Sylow.ofCard (Subgroup.zpowers x)
    (by rw [Nat.card_zpowers, hx, hN7, pow_one])
  have hPmap : (P : Subgroup ↥N).map N.subtype = Subgroup.zpowers (x : ↥Γ) := by
    show (Subgroup.zpowers x).map N.subtype = _
    rw [MonoidHom.map_zpowers]
    rfl
  have hsup := Sylow.normalizer_sup_eq_top P
  rw [hPmap] at hsup
  set H := Subgroup.normalizer ((Subgroup.zpowers (x : ↥Γ) : Subgroup ↥Γ) : Set ↥Γ) with hH
  have hx' : orderOf (x : ↥Γ) = 7 := by rw [Subgroup.orderOf_coe, hx]
  have hH42 : Nat.card H ≤ 42 := card_normalizer_le halt hnd hdim hΓB hx'
  have hidx : N.index = N.relIndex H := by
    rw [← Subgroup.relIndex_top_right, ← hsup, Subgroup.relIndex_sup_right]
  have hPH : Subgroup.zpowers (x : ↥Γ) ≤ H := Subgroup.le_normalizer
  have hPN : Subgroup.zpowers (x : ↥Γ) ≤ N := by
    rw [Subgroup.zpowers_le]
    exact x.2
  have h7le : 7 ≤ Nat.card (N.subgroupOf H) := by
    have hle : (Subgroup.zpowers (x : ↥Γ)).subgroupOf H ≤ N.subgroupOf H := fun y hy =>
      Subgroup.mem_subgroupOf.2 (hPN (Subgroup.mem_subgroupOf.1 hy))
    calc 7 = Nat.card (Subgroup.zpowers (x : ↥Γ)) := by rw [Nat.card_zpowers, hx']
      _ = Nat.card ((Subgroup.zpowers (x : ↥Γ)).subgroupOf H) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv).symm
      _ ≤ Nat.card (N.subgroupOf H) := Subgroup.card_le_of_le hle
  have hmul := (N.subgroupOf H).card_mul_index
  have hidx6 : N.index ≤ 6 := by
    rw [hidx]
    have h1 : 7 * (N.subgroupOf H).index ≤ 42 :=
      le_trans (Nat.mul_le_mul_right _ h7le) (hmul ▸ hH42)
    show (N.subgroupOf H).index ≤ 6
    omega
  have hcm := N.card_mul_index
  rw [← hcm]
  calc Nat.card N * N.index ≤ Nat.card N * 6 := Nat.mul_le_mul_left _ hidx6
    _ = 6 * Nat.card N := mul_comm _ _

theorem factorization_seven_12096 : (12096 : ℕ).factorization 7 = 1 := by
  have h : (12096 : ℕ) = 7 * 1728 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self (by norm_num), Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem factorization_seven_6048 : (6048 : ℕ).factorization 7 = 1 := by
  have h : (6048 : ℕ) = 7 * 864 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self (by norm_num), Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

end G112Seven

open G112Seven in
theorem g112ConclSeven_holds : G112ConclSeven := by
  intro V _ _ _ B Γ v₁ W X X₀ hG _ N hN h7
  have hcard : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  refine ⟨fun h6 => ?_, fun h6U => ?_, fun h13 => ?_⟩
  · exact card_le_six_mul hG.alt hG.nondegenerate h6.1 hG.isometry
      (by rw [h6.2]; exact factorization_seven_12096) N h7
  · exact card_le_six_mul hG.alt hG.nondegenerate h6U.1 hG.isometry
      (by rw [h6U.2]; exact factorization_seven_6048) N h7
  · exact eleven_dvd_card (by rw [hcard, h13.1]) h13.2 N h7

end CFSG.Quasithin.H13
