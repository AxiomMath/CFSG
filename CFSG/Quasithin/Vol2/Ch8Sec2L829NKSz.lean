module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKDefs
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParSuzuki
public import CFSG.LieType.Ree.SuzukiSplitTorusCentralizers
public import CFSG.LieType.Suzuki.SuzukiOuterCyclic

public section

namespace CFSG.Quasithin.H13.L829NK

open CFSG.Quasithin CFSG.Blueprint CFSG.LieType.Ree

theorem five_dvd_sq_add_one_two_pow (a : ℕ) : 5 ∣ (2 ^ (2 * a + 1)) ^ 2 + 1 := by
  have e1 : (2 ^ (2 * a + 1)) ^ 2 = 2 ^ (4 * a) * 4 := by
    rw [← pow_mul, show (2 * a + 1) * 2 = 4 * a + 2 by ring, pow_add]
    norm_num
  have e2 : 2 ^ (4 * a) % 5 = 1 := by
    rw [pow_mul, Nat.pow_mod]
    norm_num
  rw [e1]
  generalize 2 ^ (4 * a) = t at e2 ⊢
  omega

theorem nk_leafSzDvd : NKLeafSzDvd := by
  unfold NKLeafSzDvd
  intro e X _ h
  obtain ⟨-, a, -, K, _, _, rfl, hK, ⟨E⟩⟩ := h
  rw [Nat.card_congr E.toEquiv, CFSG.LieType.Ree.suzuki_order hK]
  exact Dvd.dvd.mul_left (five_dvd_sq_add_one_two_pow a) _

theorem nk_outer_of_mulEquiv (a : ℕ) (ha : 1 ≤ a) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (X : Type) [Group X]
    (E : X ≃* suzukiGroup a K) : UOutAll X := by
  obtain ⟨-, hdvd⟩ := CFSG.LieType.Suzuki.suzukiGroup_outer_isCyclic_card_dvd ha hK
  have hOut : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) ∣ 2 * a + 1 := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence E).toEquiv]
    exact hdvd
  intro y hy
  have hy2 : y ^ 2 = 1 := by rw [pow_two]; exact hy
  let π : MulAut X →* CFSG.ComponentClassification.OuterAutomorphisms.Outer X :=
    QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner X)
  have h1 : orderOf (π y) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hy2, map_one])
  have h2 : orderOf (π y) ∣ 2 * a + 1 := (orderOf_dvd_natCard (π y)).trans hOut
  have hgcd : Nat.gcd 2 (2 * a + 1) = 1 := by
    rw [Nat.gcd_rec, show (2 * a + 1) % 2 = 1 by omega, Nat.gcd_one_left]
  have h3 : orderOf (π y) = 1 := by
    have h4 := Nat.dvd_gcd h1 h2
    rw [hgcd] at h4
    exact Nat.dvd_one.1 h4
  have h5 : π y = 1 := orderOf_eq_one_iff.1 h3
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 ((QuotientGroup.eq_one_iff y).1 h5)
  exact ⟨x, hx.symm⟩

theorem nk_finite_suzukiGroup (a : ℕ) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) : Finite (suzukiGroup a K) := by
  apply Nat.finite_of_card_ne_zero
  rw [suzuki_order hK]
  have h2 : 2 ≤ 2 ^ (2 * a + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsub : 2 ^ (2 * a + 1) - 1 ≠ 0 := by omega
  exact Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ two_ne_zero)) hsub)
    (Nat.succ_ne_zero _)

theorem nk_isConj_of_mulEquiv {X G : Type} [Group X] [Group G] (E : X ≃* G) {x y : X}
    (h : IsConj (E x) (E y)) : IsConj x y := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  refine isConj_iff.2 ⟨E.symm c, E.injective ?_⟩
  simpa [map_mul, map_inv] using hc

theorem nk_coprime_card_units (a : ℕ) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) : Nat.Coprime (Nat.card Kˣ) (2 ^ (a + 1) + 1) := by
  rw [Nat.card_units, hK, ← Nat.isCoprime_iff_coprime]
  have h1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  unfold IsCoprime
  refine ⟨-2, (2 : ℤ) ^ (a + 1) - 1, ?_⟩
  rw [Nat.cast_sub h1]
  push_cast
  have e1 : (2 : ℤ) ^ (2 * a + 1) = 2 * ((2 : ℤ) ^ a) ^ 2 := by ring
  have e2 : (2 : ℤ) ^ (a + 1) = 2 * (2 : ℤ) ^ a := by ring
  rw [e1, e2]
  ring

theorem nk_exists_torus_pow (a : ℕ) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (v : K) (hv : v ≠ 0) :
    ∃ c : Kˣ, (c : K) ^ (2 ^ (a + 1) + 1) = v := by
  obtain ⟨c, hc⟩ := (powCoprime (nk_coprime_card_units a K hK)).surjective (Units.mk0 v hv)
  rw [powCoprime_apply] at hc
  refine ⟨c, ?_⟩
  rw [← Units.val_pow_eq_pow_val, hc, Units.val_mk0]

theorem nk_suzukiU_involution (a : ℕ) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (u v : K)
    (hsq : suzukiSElt a K u v * suzukiSElt a K u v = 1) (hne : suzukiSElt a K u v ≠ 1) :
    u = 0 ∧ v ≠ 0 := by
  haveI : CharP K 2 := (suzuki_frobenius_exponents a K hK).1
  rw [suzukiSElt_mul hK, CharTwo.add_self_eq_zero u, CharTwo.add_self_eq_zero v, zero_add,
    ← suzukiSElt_zero_zero hK] at hsq
  obtain ⟨-, h2⟩ := suzukiSElt_inj.1 hsq
  have hu : u = 0 := by
    rcases mul_eq_zero.1 h2 with h | h
    · exact (pow_eq_zero_iff (n := 2 ^ (a + 1)) (by positivity)).1 h
    · exact h
  refine ⟨hu, fun hv => hne ?_⟩
  rw [hu, hv]
  exact suzukiSElt_zero_zero hK

theorem nk_suzuki_involution_isConj (a : ℕ) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (s : suzukiGroup a K) (hs : orderOf s = 2) :
    IsConj s (suzukiSElt a K 0 1) := by
  haveI : Finite (suzukiGroup a K) := nk_finite_suzukiGroup a K hK
  have hs2 : s ^ 2 = 1 := by
    rw [← hs]
    exact pow_orderOf_eq_one s
  have hss : s * s = 1 := by
    rw [← pow_two]
    exact hs2
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hs
    norm_num at hs
  obtain ⟨h, hmem⟩ :=
    CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar.exists_conj_mem_of_two_element
      (CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar.suzukiU_isSylowTwoOf hK)
      (⟨1, by simp [hs]⟩ : ∃ k : ℕ, orderOf s = 2 ^ k)
  have hcu : IsConj s (h⁻¹ * s * h) := isConj_iff.2 ⟨h⁻¹, by rw [inv_inv]⟩
  obtain ⟨u, v, hueq⟩ := (mem_suzukiU_iff hK).1 hmem
  have huu : suzukiSElt a K u v * suzukiSElt a K u v = 1 := by
    rw [hueq, show h⁻¹ * s * h * (h⁻¹ * s * h) = h⁻¹ * (s * s) * h by group, hss]
    group
  have hu1 : suzukiSElt a K u v ≠ 1 := by
    rw [hueq]
    intro h1
    apply hs1
    calc s = h * (h⁻¹ * s * h) * h⁻¹ := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨rfl, hv⟩ := nk_suzukiU_involution a K hK u v huu hu1
  obtain ⟨c, hc⟩ := nk_exists_torus_pow a K hK v hv
  have hconj := suzukiDElt_conj' hK c⁻¹ 0 1
  rw [inv_inv, mul_zero, mul_one, hc] at hconj
  have hcu2 : IsConj (suzukiSElt a K 0 1) (suzukiSElt a K 0 v) :=
    isConj_iff.2 ⟨suzukiDElt a K c⁻¹, hconj⟩
  rw [← hueq] at hcu
  exact hcu.trans hcu2.symm

theorem nk_UIn_of_mulEquiv (a : ℕ) (ha : 1 ≤ a) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (X : Type) [Group X]
    (E : X ≃* suzukiGroup a K) : UIn X := by
  haveI : Finite Kˣ := Finite.of_injective (fun u : Kˣ => (u : K)) Units.val_injective
  have hE : ∀ x : X, orderOf (E x) = orderOf x := fun x =>
    orderOf_injective E.toMonoidHom E.injective x
  have hEs : ∀ g : suzukiGroup a K, orderOf (E.symm g) = orderOf g := fun g =>
    orderOf_injective E.symm.toMonoidHom E.symm.injective g
  let Dh : Kˣ →* suzukiGroup a K :=
    { toFun := suzukiDElt a K
      map_one' := suzukiDElt_one
      map_mul' := fun l m => (suzukiDElt_mul l m).symm }
  have hD : ∀ l : Kˣ, orderOf (suzukiDElt a K l) = orderOf l := fun l =>
    orderOf_injective Dh (suzukiDElt_injective hK) l
  refine ⟨fun x y hx hy => ?_, ?_⟩
  · apply nk_isConj_of_mulEquiv E
    have hx' : orderOf (E x) = 2 := (hE x).trans hx
    have hy' : orderOf (E y) = 2 := (hE y).trans hy
    exact (nk_suzuki_involution_isConj a K hK (E x) hx').trans
      (nk_suzuki_involution_isConj a K hK (E y) hy').symm
  · obtain ⟨ν, hν⟩ : ∃ ν : Kˣ, orderOf ν = Nat.card Kˣ := IsCyclic.exists_ofOrder_eq_natCard
    have hν_ord : orderOf ν = 2 ^ (2 * a + 1) - 1 := by rw [hν, Nat.card_units, hK]
    have h8 : 2 ^ 3 ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hq6 : 6 ≤ 2 ^ (2 * a + 1) - 1 := by
      norm_num at h8
      omega
    have hodd : ¬ 2 ∣ 2 ^ (2 * a + 1) - 1 := by
      have h2 : 2 ^ (2 * a + 1) = 2 * 2 ^ (2 * a) := by ring
      have hpos : 0 < 2 ^ (2 * a) := by positivity
      rw [h2]
      generalize 2 ^ (2 * a) = t at hpos ⊢
      omega
    have hcop2 : Nat.Coprime (orderOf ν) 2 := by
      rw [hν_ord]
      exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd)
    have hνsq : orderOf (ν * ν) = orderOf ν := by
      rw [← pow_two]
      exact hcop2.orderOf_pow
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hW2 : suzukiWElt a K ^ 2 = 1 := by
      rw [pow_two]
      exact suzukiWElt_mul_self
    have hWne : suzukiWElt a K ≠ 1 := by
      intro h
      have h00 := congrArg
        (fun g : suzukiGroup a K => ((g : Matrix.GeneralLinearGroup (Fin 4) K) :
          Matrix (Fin 4) (Fin 4) K) 0 0) h
      simp [coe_suzukiWElt, suzukiW] at h00
    have hWord : orderOf (suzukiWElt a K) = 2 := orderOf_eq_prime hW2 hWne
    have key : suzukiWElt a K * ((suzukiDElt a K ν)⁻¹ * suzukiWElt a K * suzukiDElt a K ν) =
        suzukiDElt a K (ν * ν) := by
      have hW : suzukiWElt a K * (suzukiDElt a K ν)⁻¹ * suzukiWElt a K = suzukiDElt a K ν := by
        rw [suzukiDElt_inv, suzukiWElt_D_W hK, inv_inv]
      calc suzukiWElt a K * ((suzukiDElt a K ν)⁻¹ * suzukiWElt a K * suzukiDElt a K ν)
          = (suzukiWElt a K * (suzukiDElt a K ν)⁻¹ * suzukiWElt a K) * suzukiDElt a K ν := by
            simp only [mul_assoc]
        _ = suzukiDElt a K ν * suzukiDElt a K ν := by rw [hW]
        _ = suzukiDElt a K (ν * ν) := suzukiDElt_mul ν ν
    refine ⟨E.symm (suzukiWElt a K), E.symm (suzukiDElt a K ν), ?_, ?_⟩
    · rw [hEs, hWord]
    · have hprod : E.symm (suzukiWElt a K) * ((E.symm (suzukiDElt a K ν))⁻¹ *
          E.symm (suzukiWElt a K) * E.symm (suzukiDElt a K ν)) =
          E.symm (suzukiDElt a K (ν * ν)) := by
        rw [← key]
        simp only [map_mul, map_inv]
      rw [hprod, hEs, hD, hνsq, hν_ord]
      exact hq6

theorem nk_leafSzOut :
    ∀ (e : ℕ) (X : Type) [Group X], IsSz e X → UOutAll X := by
  intro e X _ h
  obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨E⟩⟩ := h
  exact nk_outer_of_mulEquiv a ha K hK X E

theorem nk_leafSzIn :
    ∀ (e : ℕ) (X : Type) [Group X], IsSz e X → UIn X := by
  intro e X _ h
  obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨E⟩⟩ := h
  exact nk_UIn_of_mulEquiv a ha K hK X E

theorem nk_leafSz : NKLeafSz := by
  unfold NKLeafSz
  intro e X _ h
  exact ⟨nk_leafSzIn e X h, nk_leafSzOut e X h⟩

end CFSG.Quasithin.H13.L829NK
