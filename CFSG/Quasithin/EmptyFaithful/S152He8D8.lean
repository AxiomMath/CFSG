module

public import CFSG.Quasithin.EmptyFaithful.S152He8Act

public section

namespace CFSG.Quasithin.He8

open CFSG.Open CFSG.QuasithinUnique Matrix
open CFSG.Quasithin.C1Pack12

variable {G : Type} [Group G] [Finite G]

theorem card_GL_two_three : Nat.card (GL (Fin 2) (ZMod 3)) = 48 := by
  rw [Matrix.card_GL_field]
  simp [Fin.prod_univ_two, ZMod.card]

theorem pow_three_eq_one_of_three_power (u : GL (Fin 2) (ZMod 3)) {k : ℕ} (hu : u ^ 3 ^ k = 1) :
    u ^ 3 = 1 := by
  have h48 : u ^ 48 = 1 := by
    have := pow_card_eq_one' (G := GL (Fin 2) (ZMod 3)) (x := u)
    rwa [card_GL_two_three] at this
  have h1 : orderOf u ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hu
  have h2 : orderOf u ∣ 48 := orderOf_dvd_of_pow_eq_one h48
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h1
  rw [hj] at h2
  have hj1 : j ≤ 1 := by
    by_contra hcon
    have h9 : 9 ∣ 3 ^ j := by
      obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (show 2 ≤ j by omega)
      exact ⟨3 ^ m, by rw [hm, pow_add]; norm_num⟩
    have := h9.trans h2
    omega
  rw [← orderOf_dvd_iff_pow_eq_one, hj]
  exact pow_dvd_pow 3 hj1

theorem repK_eq_one_of_three {T Mc H : Subgroup G} (hsylH : IsSylowTwoOf T H)
    (hsylMc : IsSylowTwoOf T Mc) (hHMc : H ≤ Mc) (φ : OTwoQuot H ≃* S152N.W3)
    (hKn : Mc ≤ Subgroup.normalizer (oTwoUpper H : Set G))
    (fK : Multiplicative (Fin 2 → ZMod 3) ≃* OTwoQuot (oTwoUpper H))
    (hfK : ∀ v, kappaBar φ (fK v) = WCoord.fW (Multiplicative.toAdd v))
    {x : ↥Mc} {k : ℕ} (hx : orderOf x = 3 ^ k) : repK hKn fK x = 1 := by
  classical
  set R := repK hKn fK with hR
  have hT4 : ∀ t : ↥Mc, (t : G) ∈ T → (R t) ^ 4 = 1 := by
    intro t ht
    obtain ⟨M, hM, hMeq⟩ := repK_mon_of_mem φ hKn hHMc fK hfK ⟨(t : G), hsylH.1 ht⟩
    have hteq : (⟨((⟨(t : G), hsylH.1 ht⟩ : ↥H) : G), hHMc (⟨(t : G), hsylH.1 ht⟩ : ↥H).2⟩ : ↥Mc) = t :=
      Subtype.ext rfl
    rw [hteq] at hMeq
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hMeq, isMon_pow_four M hM, Units.val_one]
  have h2 : ∀ g : ↥Mc, ∀ a : ℕ, orderOf g = 2 ^ a → (R g) ^ 4 = 1 := by
    intro g a hg
    have hP : IsPGroup 2 (Subgroup.zpowers (g : G)) := by
      refine IsPGroup.of_card (n := a) ?_
      rw [Nat.card_zpowers]
      have : orderOf (g : G) = orderOf g := Subgroup.orderOf_coe g
      rw [this, hg]
    obtain ⟨c, hcMc, hcT⟩ := F7.isSylowTwoOf_exists_conj_le hsylMc
      (P := Subgroup.zpowers (g : G)) (Subgroup.zpowers_le.mpr g.2) hP
    have hmem : (g : G) ∈ conjSub c T := hcT (Subgroup.mem_zpowers _)
    have hmem' : c⁻¹ * (g : G) * c ∈ T := mem_conjSub.mp hmem
    set c' : ↥Mc := ⟨c, hcMc⟩
    have h4 := hT4 (c'⁻¹ * g * c') (by simpa [c'] using hmem')
    have : R g = R c' * R (c'⁻¹ * g * c') * (R c')⁻¹ := by
      simp only [map_mul, map_inv]
      group
    rw [this]
    calc (R c' * R (c'⁻¹ * g * c') * (R c')⁻¹) ^ 4
        = R c' * (R (c'⁻¹ * g * c')) ^ 4 * (R c')⁻¹ := conj_pow
      _ = 1 := by rw [h4]; group
  have hu3 : (R x) ^ 3 = 1 := by
    apply pow_three_eq_one_of_three_power (k := k)
    rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  by_contra hne
  have hUne : ((R x : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) ≠ 1 := by
    intro h
    exact hne (Units.ext (by rw [h, Units.val_one]))
  have hU3 : ((R x : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hu3, Units.val_one]
  obtain ⟨M, hM, hM8, hM4⟩ := exists_mon_order_eight _ hU3 hUne
  obtain ⟨h, hh⟩ := exists_mem_repK_eq_mon φ hKn hHMc fK hfK hM
  set g : ↥Mc := ⟨(h : G), hHMc h.2⟩ * x with hg
  have hRg : ((R g : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
      M * ((R x : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
    rw [hg, map_mul, Units.val_mul]
    congr 1
  obtain ⟨a, r, hr, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  have hg2 : orderOf (g ^ r) = 2 ^ a := by
    rw [orderOf_pow' _ hr.pos.ne', hord, Nat.gcd_eq_right (dvd_mul_left r (2 ^ a)),
      Nat.mul_div_cancel _ hr.pos]
  have hz2 : ((R g) ^ 4) ^ 2 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hRg, ← pow_mul, Units.val_one]
    exact hM8
  have hz1 : (R g) ^ 4 ≠ 1 := by
    intro h
    apply hM4
    have := congrArg (fun u : GL (Fin 2) (ZMod 3) => (u : Matrix (Fin 2) (Fin 2) (ZMod 3))) h
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at this
    rwa [hRg] at this
  have hzr : ((R g) ^ 4) ^ r = (R g) ^ 4 := by
    obtain ⟨m, hm⟩ := hr
    rw [hm, pow_succ, pow_mul, hz2, one_pow, one_mul]
  have h4 : (R (g ^ r)) ^ 4 = 1 := h2 (g ^ r) a hg2
  have h5 : (R (g ^ r)) ^ 4 = ((R g) ^ 4) ^ r := by
    rw [map_pow, ← pow_mul, ← pow_mul, mul_comm]
  rw [h5, hzr] at h4
  exact hz1 h4

theorem commutator_mem_of_three {T Mc H : Subgroup G} (hsylH : IsSylowTwoOf T H)
    (hsylMc : IsSylowTwoOf T Mc) (hHMc : H ≤ Mc) (φ : OTwoQuot H ≃* S152N.W3)
    (hKn : Mc ≤ Subgroup.normalizer (oTwoUpper H : Set G)) {x : G} (hx : x ∈ Mc) {k : ℕ}
    (hxk : orderOf x = 3 ^ k) :
    ∀ y ∈ oTwoUpper H, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 (oTwoUpper H) := by
  obtain ⟨fK, hfK⟩ := exists_coords_K φ
  have h1 : repK hKn fK ⟨x, hx⟩ = 1 :=
    repK_eq_one_of_three hsylH hsylMc hHMc φ hKn fK hfK (x := ⟨x, hx⟩) (k := k)
      (by rw [Subgroup.orderOf_mk]; exact hxk)
  have h2 : kAct hKn ⟨x, hx⟩ = 1 := by
    apply repGL_injective fK
    rw [map_one]
    exact h1
  intro y hy
  have h3 := congrArg (fun a : MulAut (OTwoQuot (oTwoUpper H)) =>
    a (QuotientGroup.mk (⟨y, hy⟩ : ↥(oTwoUpper H)))) h2
  simp only [kAct_mk, MulAut.one_apply] at h3
  have hmem : x * y * x⁻¹ ∈ oTwoUpper H :=
    (Subgroup.mem_normalizer_iff.mp (hKn hx) y).mp hy
  have h4 : (QuotientGroup.mk ((⟨x * y * x⁻¹, hmem⟩ : ↥(oTwoUpper H)) *
      (⟨y, hy⟩ : ↥(oTwoUpper H))⁻¹) : OTwoQuot (oTwoUpper H)) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have h3' : (QuotientGroup.mk (⟨x * y * x⁻¹, hmem⟩ : ↥(oTwoUpper H)) : OTwoQuot (oTwoUpper H)) =
        QuotientGroup.mk (⟨y, hy⟩ : ↥(oTwoUpper H)) := h3
    rw [h3', mul_inv_cancel]
  exact (mk_eq_one_iff_mem_pCoreOf _).mp h4

end CFSG.Quasithin.He8
