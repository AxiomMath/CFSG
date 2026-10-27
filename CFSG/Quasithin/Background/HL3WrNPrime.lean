module

public import CFSG.Quasithin.Background.HL3WrNorm
public import CFSG.Quasithin.Background.HA7
public import CFSG.Quasithin.Background.HSL3NPrime

public section

namespace CFSG.Quasithin

namespace H

namespace L3Wr

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix CFSG.Quasithin.H13
open scoped Matrix Pointwise

theorem card_SL32 : Nat.card ↥SL32 = 168 := by
  rw [← Nat.card_congr (SL3Pair.slEquiv (ZMod 2)).toEquiv]
  exact SL3One.card_SL_two (K := ZMod 2) (by simp)

theorem card_img : Nat.card img = 168 ^ 2 := by
  rw [img, ← Nat.card_congr (MonoidHom.ofInjective rho_injective).toEquiv, Nat.card_prod,
    card_SL32]
  norm_num

theorem mul_inv_mem_img {y z : MulAut WMod} (hy : y ∈ norm) (hz : z ∈ norm) (hy' : y ∉ img)
    (hz' : z ∉ img) : y * z⁻¹ ∈ img := by
  obtain ⟨g, rfl | rfl⟩ := mem_norm_iff.mp hy
  · exact absurd (rho_mem_img g) hy'
  obtain ⟨h, rfl | rfl⟩ := mem_norm_iff.mp hz
  · exact absurd (rho_mem_img h) hz'
  have : rho g * tau * (rho h * tau)⁻¹ = rho (g * h⁻¹) := by
    rw [map_mul, map_inv]
    group
  rw [this]
  exact rho_mem_img _

theorem card_inf_img_mul_two {K : Subgroup (MulAut WMod)} (hK : K ≤ norm) (hK' : ¬ K ≤ img) :
    Nat.card ↥(K ⊓ img) * 2 = Nat.card K := by
  classical
  obtain ⟨k, hkK, hk⟩ := Set.not_subset.mp hK'
  let f : ↥(K ⊓ img) × Bool → ↥K := fun p =>
    if p.2 then ⟨p.1 * k, K.mul_mem (Subgroup.mem_inf.mp p.1.2).1 hkK⟩
    else ⟨p.1, (Subgroup.mem_inf.mp p.1.2).1⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨x, a⟩ ⟨y, b⟩ hxy
      have hxi : (x : MulAut WMod) ∈ img := (Subgroup.mem_inf.mp x.2).2
      have hyi : (y : MulAut WMod) ∈ img := (Subgroup.mem_inf.mp y.2).2
      cases a <;> cases b <;> simp only [f, Bool.false_eq_true, ↓reduceIte, Subtype.mk.injEq]
        at hxy
      · exact Prod.ext (Subtype.ext hxy) rfl
      · exfalso
        apply hk
        have : k = (y : MulAut WMod)⁻¹ * x := by rw [hxy, inv_mul_cancel_left]
        rw [this]
        exact img.mul_mem (img.inv_mem hyi) hxi
      · exfalso
        apply hk
        have : k = (x : MulAut WMod)⁻¹ * y := by rw [← hxy, inv_mul_cancel_left]
        rw [this]
        exact img.mul_mem (img.inv_mem hxi) hyi
      · exact Prod.ext (Subtype.ext (mul_right_cancel hxy)) rfl
    · rintro ⟨z, hz⟩
      by_cases hzi : z ∈ img
      · exact ⟨(⟨z, Subgroup.mem_inf.mpr ⟨hz, hzi⟩⟩, false), rfl⟩
      · refine ⟨(⟨z * k⁻¹, Subgroup.mem_inf.mpr ⟨K.mul_mem hz (K.inv_mem hkK),
          mul_inv_mem_img (hK hz) (hK hkK) hzi hk⟩⟩, true), ?_⟩
        simp only [f, ↓reduceIte, inv_mul_cancel_right]
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod]
  simp

theorem card_norm : Nat.card norm = 2 * 168 ^ 2 := by
  have h := card_inf_img_mul_two (le_refl norm) fun h => tau_not_mem_img (h tau_mem_norm)
  rw [inf_eq_right.mpr img_le_norm, card_img] at h
  omega

theorem eq_img_or_eq_norm {X : Subgroup (MulAut WMod)} (hX1 : img ≤ X) (hX2 : X ≤ norm) :
    X = img ∨ X = norm := by
  by_cases h : X ≤ img
  · exact Or.inl (le_antisymm h hX1)
  · right
    refine le_antisymm hX2 fun y hy => ?_
    obtain ⟨x, hxX, hx⟩ := Set.not_subset.mp h
    by_cases hyi : y ∈ img
    · exact hX1 hyi
    · have := mul_inv_mem_img hy (hX2 hxX) hyi hx
      have h2 : y = (y * x⁻¹) * x := by rw [inv_mul_cancel_right]
      rw [h2]
      exact X.mul_mem (hX1 this) hxX

theorem card_of_isSylowIn {G : Type*} [Group G] [Finite G] {S H : Subgroup G}
    (hS : IsSylowIn 2 S H) {a m : ℕ} (hH : Nat.card H = 2 ^ a * m) (hm : Odd m) :
    Nat.card S = 2 ^ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [hS.card_eq, hH, Nat.factorization_mul (by positivity) (by rintro rfl; simp at hm),
    Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd
      (fun h => (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h)),
    add_zero]

section Prod

theorem card_eq_card_map_fst_mul (R : Subgroup (↥SL32 × ↥SL32)) :
    Nat.card R = Nat.card (R.map (MonoidHom.fst ↥SL32 ↥SL32)) *
      Nat.card (R.comap (MonoidHom.inr ↥SL32 ↥SL32)) := by
  let f : ↥R →* ↥SL32 := (MonoidHom.fst ↥SL32 ↥SL32).comp R.subtype
  have hrange : f.range = R.map (MonoidHom.fst ↥SL32 ↥SL32) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hmem : ∀ r : ↥f.ker,
      MonoidHom.inr ↥SL32 ↥SL32 ((r : ↥R) : ↥SL32 × ↥SL32).2 = ((r : ↥R) : ↥SL32 × ↥SL32) :=
    fun r => Prod.ext (MonoidHom.mem_ker.mp r.2).symm rfl
  have hker : Nat.card f.ker = Nat.card (R.comap (MonoidHom.inr ↥SL32 ↥SL32)) := by
    refine Nat.card_congr
      { toFun := fun r => ⟨((r : ↥R) : ↥SL32 × ↥SL32).2, by
          change MonoidHom.inr ↥SL32 ↥SL32 _ ∈ R
          rw [hmem r]
          exact (r : ↥R).2⟩
        invFun := fun b => ⟨⟨(1, b), b.2⟩, rfl⟩
        left_inv := fun r => Subtype.ext (Subtype.ext (hmem r))
        right_inv := fun b => rfl }
  rw [← Subgroup.card_mul_index f.ker, Subgroup.index_ker, hrange, hker, mul_comm]

theorem card_le_eight {H : Subgroup ↥SL32} (hH : IsPGroup 2 H) : Nat.card H ≤ 8 := by
  obtain ⟨k, hk⟩ := hH.exists_card_eq
  have hdvd : Nat.card H ∣ 8 * 21 := by
    have := Subgroup.card_subgroup_dvd_card H
    rwa [card_SL32] at this
  rw [hk] at hdvd ⊢
  have h8 : 2 ^ k ∣ 8 :=
    (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 21)).dvd_of_dvd_mul_right hdvd
  exact Nat.le_of_dvd (by norm_num) h8

theorem dvd_twentyOne_of_odd {d : ℕ} (hd : d ∣ 168) (ho : Odd d) : d ∣ 21 := by
  have h : d ∣ 2 ^ 3 * 21 := by simpa using hd
  exact (Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr ho)).dvd_of_dvd_mul_left h

theorem eq_top_of_dvd {Q : Subgroup ↥SL32} (h : 56 ∣ Nat.card Q) : Q = ⊤ := by
  have : IsSimpleGroup ↥SL32 := isSimpleGroup_SL32
  have h1 := Q.card_mul_index
  rw [card_SL32] at h1
  obtain ⟨d, hd⟩ := h
  rw [hd] at h1
  have hi : Q.index ≤ 3 := by
    have hpos : 0 < d := by
      rcases Nat.eq_zero_or_pos d with rfl | hp
      · simp at h1
      · exact hp
    nlinarith
  have hfac : (Q.index).factorial < Nat.card ↥SL32 := by
    rw [card_SL32]
    calc (Q.index).factorial ≤ (3 : ℕ).factorial := Nat.factorial_le hi
      _ < 168 := by decide
  exact Subgroup.index_eq_one.mp (A7.index_eq_one_of_simple Q hfac)

theorem false_of_orderOf_fst {R P B : Subgroup (↥SL32 × ↥SL32)} (hPR : P ≤ R)
    (hP2 : IsPGroup 2 P) (hP : Nat.card P = 64) (hBR : B ≤ R)
    (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hBodd : Odd (Nat.card B))
    (hR : Nat.card R = 64 * Nat.card B) {z : ↥SL32 × ↥SL32} (hz : z ∈ B)
    (hz1 : orderOf z.1 = 7) : False := by
  classical
  set P₁ := P.map (MonoidHom.fst ↥SL32 ↥SL32) with hP₁def
  set P₂ := P.map (MonoidHom.snd ↥SL32 ↥SL32) with hP₂def
  have hle : P ≤ P₁.prod P₂ := fun x hx => Subgroup.mem_prod.mpr ⟨⟨x, hx, rfl⟩, ⟨x, hx, rfl⟩⟩
  have hcardle : Nat.card P ≤ Nat.card (P₁.prod P₂) := Subgroup.card_le_of_le hle
  rw [card_prod_subgroup, hP] at hcardle
  have h1 := card_le_eight (hP2.map (MonoidHom.fst ↥SL32 ↥SL32))
  have h2 := card_le_eight (hP2.map (MonoidHom.snd ↥SL32 ↥SL32))
  rw [← hP₁def] at h1
  rw [← hP₂def] at h2
  have hP₁8 : Nat.card P₁ = 8 := by nlinarith
  have hP₂8 : Nat.card P₂ = 8 := by nlinarith
  have hPeq : P = P₁.prod P₂ :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [card_prod_subgroup, hP₁8, hP₂8, hP])
  have hQ7 : 7 ∣ Nat.card (R.map (MonoidHom.fst ↥SL32 ↥SL32)) := by
    rw [← hz1]
    exact Subgroup.orderOf_dvd_natCard _ ⟨z, hBR hz, rfl⟩
  have hQ8 : 8 ∣ Nat.card (R.map (MonoidHom.fst ↥SL32 ↥SL32)) := by
    rw [← hP₁8]
    exact Subgroup.card_dvd_of_le (Subgroup.map_mono hPR)
  have hQ : R.map (MonoidHom.fst ↥SL32 ↥SL32) = ⊤ :=
    eq_top_of_dvd (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) hQ7 hQ8 : 7 * 8 ∣ _)
  set K := R.comap (MonoidHom.inr ↥SL32 ↥SL32) with hKdef
  set C := B.comap (MonoidHom.inr ↥SL32 ↥SL32) with hCdef
  have hK8 : 8 ∣ Nat.card K := by
    have hle2 : P₂ ≤ K := fun b hb => by
      change ((1 : ↥SL32), b) ∈ R
      apply hPR
      rw [hPeq]
      exact Subgroup.mem_prod.mpr ⟨P₁.one_mem, hb⟩
    rw [← hP₂8]
    exact Subgroup.card_dvd_of_le hle2
  have hCK : C ≤ K := Subgroup.comap_mono hBR
  have hRc := card_eq_card_map_fst_mul R
  have hBc := card_eq_card_map_fst_mul B
  rw [hQ, Subgroup.card_top, card_SL32, ← hKdef] at hRc
  rw [← hCdef] at hBc
  have hCodd : Odd (Nat.card C) := Odd.of_dvd_nat hBodd (Dvd.intro_left _ hBc.symm)
  have hC8 : 8 * Nat.card C ∣ Nat.card K :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd
      (Nat.Coprime.pow_left 3 (Nat.coprime_two_left.mpr hCodd) : Nat.Coprime (2 ^ 3) _) hK8
      (Subgroup.card_dvd_of_le hCK)
  set B₁ := B.map (MonoidHom.fst ↥SL32 ↥SL32) with hB₁def
  have hge : 21 ≤ Nat.card B₁ := by
    have hK := Nat.le_of_dvd Nat.card_pos hC8
    have hCpos : 0 < Nat.card C := Nat.card_pos
    rw [hR, hBc] at hRc
    nlinarith
  have hB₁odd : Odd (Nat.card B₁) := Odd.of_dvd_nat hBodd (Dvd.intro _ hBc.symm)
  have hB₁dvd : Nat.card B₁ ∣ 168 := by
    have := Subgroup.card_subgroup_dvd_card B₁
    rwa [card_SL32] at this
  have hB₁21 : Nat.card B₁ = 21 :=
    le_antisymm (Nat.le_of_dvd (by norm_num) (dvd_twentyOne_of_odd hB₁dvd hB₁odd)) hge
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨γ, hγ⟩ := exists_prime_orderOf_dvd_card' (G := ↥B₁) 7
    (by rw [hB₁21]; norm_num : 7 ∣ Nat.card B₁)
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := ↥B₁) 3
    (by rw [hB₁21]; norm_num : 3 ∣ Nat.card B₁)
  have hcomm : (γ : ↥SL32) * ζ = ζ * γ := by
    obtain ⟨x, hx, hxγ⟩ := γ.2
    obtain ⟨y, hy, hyζ⟩ := ζ.2
    rw [← hxγ, ← hyζ, ← map_mul, ← map_mul, hBab x hx y hy]
  refine SL3One.false_of_commute (K := ZMod 2) (by simp)
    (γ := (SL3Pair.slEquiv (ZMod 2)).symm γ) (ζ := (SL3Pair.slEquiv (ZMod 2)).symm ζ) ?_ ?_ ?_
  · rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hγ]
  · rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hζ]
  · rw [← map_mul, ← map_mul, hcomm]

theorem false_of_orderOf_snd {R P B : Subgroup (↥SL32 × ↥SL32)} (hPR : P ≤ R)
    (hP2 : IsPGroup 2 P) (hP : Nat.card P = 64) (hBR : B ≤ R)
    (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hBodd : Odd (Nat.card B))
    (hR : Nat.card R = 64 * Nat.card B) {z : ↥SL32 × ↥SL32} (hz : z ∈ B)
    (hz2 : orderOf z.2 = 7) : False := by
  set σ : ↥SL32 × ↥SL32 ≃* ↥SL32 × ↥SL32 := MulEquiv.prodComm with hσ
  have hcard : ∀ H : Subgroup (↥SL32 × ↥SL32), Nat.card (H.map σ.toMonoidHom) = Nat.card H :=
    fun H => Subgroup.card_map_of_injective σ.injective
  refine false_of_orderOf_fst (R := R.map σ.toMonoidHom) (P := P.map σ.toMonoidHom)
    (B := B.map σ.toMonoidHom) (Subgroup.map_mono hPR) (hP2.map _) (by rw [hcard, hP])
    (Subgroup.map_mono hBR) ?_ (by rw [hcard]; exact hBodd) (by rw [hcard, hcard, hR])
    (z := σ z) ⟨z, hz, rfl⟩ hz2
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul, hBab a ha b hb]

end Prod

section Permute

variable {G : Type*} [Group G]

theorem coe_mul_eq_sup_of_card [Finite G] {A B : Subgroup G} (hAB : A ⊓ B = ⊥)
    (hc : Nat.card ↥(A ⊔ B) ≤ Nat.card A * Nat.card B) :
    (A : Set G) * (B : Set G) = ((A ⊔ B : Subgroup G) : Set G) := by
  let μ : ↥A × ↥B → G := fun p => p.1 * p.2
  have hμ : Function.Injective μ := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have e : (a : G) * b = a' * b' := h
    have hmem : (a' : G)⁻¹ * a ∈ A ⊓ B := by
      refine ⟨A.mul_mem (A.inv_mem a'.2) a.2, ?_⟩
      have : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← e, mul_inv_cancel_right]
      rw [this]
      exact B.mul_mem b'.2 (B.inv_mem b.2)
    rw [hAB, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    have h1 : a = a' := Subtype.ext hmem.symm
    subst h1
    exact Prod.ext rfl (Subtype.ext (mul_left_cancel e))
  have hrange : Set.range μ = (A : Set G) * (B : Set G) := by
    ext x
    constructor
    · rintro ⟨⟨a, b⟩, rfl⟩
      exact ⟨a, a.2, b, b.2, rfl⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  have hsub : (A : Set G) * (B : Set G) ⊆ ((A ⊔ B : Subgroup G) : Set G) := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact Subgroup.mul_mem_sup ha hb
  have hcard : Nat.card ↥((A : Set G) * (B : Set G)) = Nat.card A * Nat.card B := by
    rw [← hrange, Nat.card_range_of_injective hμ, Nat.card_prod]
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hcard]
  exact hc

theorem permute_of_card [Finite G] {H K : Subgroup G} (hinf : H ⊓ K = ⊥)
    (hc : Nat.card ↥(H ⊔ K) ≤ Nat.card H * Nat.card K) :
    (H : Set G) * (K : Set G) = (K : Set G) * (H : Set G) := by
  rw [coe_mul_eq_sup_of_card hinf hc, coe_mul_eq_sup_of_card (by rw [inf_comm, hinf])
    (by rw [sup_comm, mul_comm]; exact hc), sup_comm]

end Permute

theorem sup_tau_inf_img {H : Subgroup (MulAut WMod)} (hH : H ≤ img)
    (hτ : ∀ h ∈ H, tau * h * tau ∈ H) : (H ⊔ Subgroup.zpowers tau) ⊓ img = H := by
  have htt : tau * tau = 1 := tau_mul_self
  let D : Subgroup (MulAut WMod) :=
    { carrier := {x | x ∈ H ∨ x * tau ∈ H}
      one_mem' := Or.inl H.one_mem
      mul_mem' := by
        rintro x y (hx | hx) (hy | hy)
        · exact Or.inl (H.mul_mem hx hy)
        · right
          rw [mul_assoc]
          exact H.mul_mem hx hy
        · right
          have e : x * y * tau = x * tau * (tau * y * tau) := by
            calc x * y * tau = x * (tau * tau) * y * tau := by rw [htt, mul_one]
              _ = x * tau * (tau * y * tau) := by simp only [mul_assoc]
          rw [e]
          exact H.mul_mem hx (hτ y hy)
        · left
          have e : x * y = x * tau * (tau * (y * tau) * tau) := by
            calc x * y = x * (tau * tau) * y * (tau * tau) := by rw [htt, mul_one, mul_one]
              _ = x * tau * (tau * (y * tau) * tau) := by simp only [mul_assoc]
          rw [e]
          exact H.mul_mem hx (hτ _ hy)
      inv_mem' := by
        rintro x (hx | hx)
        · exact Or.inl (H.inv_mem hx)
        · right
          have e : x⁻¹ * tau = tau * (x * tau)⁻¹ * tau := by
            rw [_root_.mul_inv_rev, tau_inv]
            calc x⁻¹ * tau = (tau * tau) * x⁻¹ * tau := by rw [htt, one_mul]
              _ = tau * (tau * x⁻¹) * tau := by simp only [mul_assoc]
          rw [e]
          exact hτ _ (H.inv_mem hx) }
  have hle : H ⊔ Subgroup.zpowers tau ≤ D := by
    refine sup_le (fun h hh => Or.inl hh) ?_
    rw [Subgroup.zpowers_le]
    right
    rw [htt]
    exact H.one_mem
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_left hH)
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
  rcases hle hx1 with h | h
  · exact h
  · exfalso
    apply tau_not_mem_img
    have : tau = x⁻¹ * (x * tau) := by rw [inv_mul_cancel_left]
    rw [this]
    exact img.mul_mem (img.inv_mem hx2) (hH h)

theorem tau_mem_map_prod (A : Subgroup ↥SL32) :
    ∀ h ∈ (A.prod A).map rho, tau * h * tau ∈ (A.prod A).map rho := by
  rintro _ ⟨g, hg, rfl⟩
  refine ⟨g.swap, ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := Subgroup.mem_prod.mp hg
    exact Subgroup.mem_prod.mpr ⟨h2, h1⟩
  · rw [← tau_conj_rho, tau_inv]

theorem card_map_prod_sup_tau (A : Subgroup ↥SL32) :
    Nat.card ↥((A.prod A).map rho ⊔ Subgroup.zpowers tau) = 2 * Nat.card A ^ 2 := by
  have hle : (A.prod A).map rho ≤ img := Subgroup.map_le_range _ _
  have hN : (A.prod A).map rho ⊔ Subgroup.zpowers tau ≤ norm :=
    sup_le (hle.trans img_le_norm) ((Subgroup.zpowers_le).mpr tau_mem_norm)
  have hnot : ¬ (A.prod A).map rho ⊔ Subgroup.zpowers tau ≤ img := fun h =>
    tau_not_mem_img (h (Subgroup.mem_sup_right (Subgroup.mem_zpowers tau)))
  have h1 := card_inf_img_mul_two hN hnot
  rw [sup_tau_inf_img hle (tau_mem_map_prod A), Subgroup.card_map_of_injective rho_injective,
    card_prod_subgroup] at h1
  rw [← h1]
  ring

abbrev e0 : Fin 3 → ZMod 2 := Pi.single 0 1

abbrev e2 : Fin 3 → ZMod 2 := Pi.single 2 1

@[expose] def P1 : Subgroup ↥SL32 where
  carrier := {a | mat a *ᵥ e0 = e0}
  mul_mem' {a b} ha hb := by
    change mat (a * b) *ᵥ e0 = e0
    change mat a *ᵥ e0 = e0 at ha
    change mat b *ᵥ e0 = e0 at hb
    rw [mat_mul, ← Matrix.mulVec_mulVec, hb, ha]
  one_mem' := by
    change mat 1 *ᵥ e0 = e0
    rw [mat_one, Matrix.one_mulVec]
  inv_mem' {a} ha := by
    change mat a⁻¹ *ᵥ e0 = e0
    change mat a *ᵥ e0 = e0 at ha
    calc mat a⁻¹ *ᵥ e0 = mat a⁻¹ *ᵥ (mat a *ᵥ e0) := by rw [ha]
      _ = e0 := by rw [Matrix.mulVec_mulVec, mat_inv_mul, Matrix.one_mulVec]

@[expose] def P2 : Subgroup ↥SL32 where
  carrier := {a | e2 ᵥ* mat a = e2}
  mul_mem' {a b} ha hb := by
    change e2 ᵥ* mat (a * b) = e2
    change e2 ᵥ* mat a = e2 at ha
    change e2 ᵥ* mat b = e2 at hb
    rw [mat_mul, ← Matrix.vecMul_vecMul, ha, hb]
  one_mem' := by
    change e2 ᵥ* mat 1 = e2
    rw [mat_one, Matrix.vecMul_one]
  inv_mem' {a} ha := by
    change e2 ᵥ* mat a⁻¹ = e2
    change e2 ᵥ* mat a = e2 at ha
    calc e2 ᵥ* mat a⁻¹ = (e2 ᵥ* mat a) ᵥ* mat a⁻¹ := by rw [ha]
      _ = e2 := by rw [Matrix.vecMul_vecMul, mat_mul_inv, Matrix.vecMul_one]

@[expose] def U3 : Subgroup ↥SL32 := P1 ⊓ P2

theorem mulVec_e0_iff (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    M *ᵥ e0 = e0 ↔ M 1 0 = 0 ∧ M 2 0 = 0 ∧ M 0 0 = 1 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp [Matrix.mulVec_single] at h0 h1 h2
    exact ⟨h1, h2, h0⟩
  · rintro ⟨h1, h2, h0⟩
    ext i
    fin_cases i <;> simp [Matrix.mulVec_single, h0, h1, h2]

theorem e2_vecMul_iff (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    e2 ᵥ* M = e2 ↔ M 2 0 = 0 ∧ M 2 1 = 0 ∧ M 2 2 = 1 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp [Matrix.single_vecMul] at h0 h1 h2
    exact ⟨h0, h1, h2⟩
  · rintro ⟨h0, h1, h2⟩
    ext j
    fin_cases j <;> simp [Matrix.single_vecMul, h0, h1, h2]

theorem card_SL32_subtype (p : Matrix (Fin 3) (Fin 3) (ZMod 2) → Prop) [DecidablePred p] :
    Nat.card {a : ↥SL32 // p (mat a)} =
      (Finset.univ.filter fun M : Matrix (Fin 3) (Fin 3) (ZMod 2) => p M ∧ M.det = 1).card := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr
    { toFun := fun a => ⟨mat a.1, a.2, SL3Pair.mem_statedSL_iff.mp a.1.2⟩
      invFun := fun M => ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M.1
        (by rw [M.2.2]; exact one_ne_zero), mem_SL32 _⟩, M.2.1⟩
      left_inv := fun a => Subtype.ext (Subtype.ext (Units.ext rfl))
      right_inv := fun M => rfl }

theorem card_P1 : Nat.card ↥P1 = 24 := by
  have h : Nat.card ↥P1 = Nat.card {a : ↥SL32 // mat a 1 0 = 0 ∧ mat a 2 0 = 0 ∧ mat a 0 0 = 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun a => mulVec_e0_iff (mat a))
  rw [h]
  exact (card_SL32_subtype (fun M => M 1 0 = 0 ∧ M 2 0 = 0 ∧ M 0 0 = 1)).trans (by decide)

theorem card_U3 : Nat.card ↥U3 = 8 := by
  have h : Nat.card ↥U3 = Nat.card {a : ↥SL32 // mat a 1 0 = 0 ∧ mat a 2 0 = 0 ∧
      mat a 2 1 = 0 ∧ mat a 0 0 = 1 ∧ mat a 2 2 = 1} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun a => ?_)
    change mat a *ᵥ e0 = e0 ∧ e2 ᵥ* mat a = e2 ↔ _
    rw [mulVec_e0_iff, e2_vecMul_iff]
    tauto
  rw [h]
  exact (card_SL32_subtype (fun M => M 1 0 = 0 ∧ M 2 0 = 0 ∧ M 2 1 = 0 ∧ M 0 0 = 1 ∧
    M 2 2 = 1)).trans (by decide)

theorem U3_le_P1 : U3 ≤ P1 := inf_le_left

@[expose] noncomputable def c3 : ↥SL32 :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0, 0; 0, 0, 1; 0, 1, 1] (by decide), mem_SL32 _⟩

theorem mat_c3 : mat c3 = !![1, 0, 0; 0, 0, 1; 0, 1, 1] := rfl

theorem c3_mem_P1 : c3 ∈ P1 := by
  change mat c3 *ᵥ e0 = e0
  rw [mat_c3]
  decide

theorem orderOf_c3 : orderOf c3 = 3 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  apply orderOf_eq_prime
  · apply Subtype.ext
    apply Units.ext
    change mat (c3 ^ 3) = 1
    rw [pow_three, mat_mul, mat_mul, mat_c3]
    decide
  · intro h
    have h1 := congrArg mat h
    rw [mat_c3, mat_one] at h1
    revert h1
    decide

@[expose] noncomputable def C3 : Subgroup ↥SL32 := Subgroup.zpowers c3

theorem card_C3 : Nat.card ↥C3 = 3 := by
  rw [C3, Nat.card_zpowers, orderOf_c3]

theorem C3_le_P1 : C3 ≤ P1 := (Subgroup.zpowers_le).mpr c3_mem_P1

theorem two_le_nPrime {X : Subgroup (MulAut WMod)} (hX1 : img ≤ X) (hX2 : X ≤ norm) :
    2 ≤ E3.nPrime X := by
  have : Finite (MulAut WMod) := MulEquiv.finite_left
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := (C3.prod C3).map rho with hBdef
  set Y := Subgroup.zpowers (rho (c3, 1)) with hYdef
  have hBimg : B ≤ img := Subgroup.map_le_range _ _
  have hBcard : Nat.card B = 9 := by
    rw [Subgroup.card_map_of_injective rho_injective, card_prod_subgroup, card_C3]
  have hYB : Y ≤ B := (Subgroup.zpowers_le).mpr
    ⟨(c3, 1), Subgroup.mem_prod.mpr ⟨Subgroup.mem_zpowers c3, C3.one_mem⟩, rfl⟩
  have hYcard : Nat.card Y = 2 ^ 2 - 1 := by
    rw [hYdef, Nat.card_zpowers, orderOf_injective rho rho_injective]
    have : orderOf ((c3, 1) : ↥SL32 × ↥SL32) = orderOf c3 :=
      orderOf_injective (MonoidHom.inl ↥SL32 ↥SL32) (fun a b h => congrArg Prod.fst h) c3
    rw [this, orderOf_c3]
    norm_num
  have hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_prod.mp hx
    obtain ⟨hy1, hy2⟩ := Subgroup.mem_prod.mp hy
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hx1
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hx2
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy1
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp hy2
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_mul, Prod.fst_mul, ← hi, ← hk, ← _root_.zpow_add, ← _root_.zpow_add, add_comm]
    · rw [Prod.snd_mul, Prod.snd_mul, ← hj, ← hl, ← _root_.zpow_add, ← _root_.zpow_add, add_comm]
  have hBodd : Odd (Nat.card B) := by rw [hBcard]; decide
  have hperm : ∀ {S R : Subgroup (MulAut WMod)}, IsPGroup 2 S → B ≤ R → S ≤ R →
      Nat.card R ≤ Nat.card B * Nat.card S →
      (B : Set (MulAut WMod)) * (S : Set (MulAut WMod)) = (S : Set _) * (B : Set _) := by
    intro S R hS2 hBR hSR hR
    obtain ⟨k, hk⟩ := hS2.exists_card_eq
    have hcop : Nat.Coprime (Nat.card B) (Nat.card S) := by
      rw [hk]
      exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hBodd)
    exact permute_of_card (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
      ((Subgroup.card_le_of_le (sup_le hBR hSR)).trans hR)
  have hsyl : ∀ {S : Subgroup (MulAut WMod)} {a : ℕ}, S ≤ X → Nat.card S = 2 ^ a →
      Nat.card X = 2 ^ a * 441 → IsSylowIn 2 S X := by
    intro S a hSX hS hXc
    refine ⟨hSX, IsPGroup.of_card hS, fun h2 => ?_⟩
    have h1 := Subgroup.relIndex_mul_card (H := S) (K := X)
    rw [inf_eq_left.mpr hSX, hS, hXc] at h1
    have h3 : S.relIndex X = 441 := by
      have hpos : 0 < 2 ^ a := by positivity
      nlinarith [h1]
    rw [h3] at h2
    exact absurd h2 (by decide)
  rcases eq_img_or_eq_norm hX1 hX2 with rfl | rfl
  ·
    set S := (U3.prod U3).map rho with hSdef
    have hScard : Nat.card S = 2 ^ 6 := by
      rw [Subgroup.card_map_of_injective rho_injective, card_prod_subgroup, card_U3]
      norm_num
    have hS : IsSylowIn 2 S img := hsyl (Subgroup.map_le_range _ _) hScard
      (by rw [card_img]; norm_num)
    have hBS := hperm (S := S) (R := (P1.prod P1).map rho) (IsPGroup.of_card hScard)
      (Subgroup.map_mono (Subgroup.prod_mono C3_le_P1 C3_le_P1))
      (Subgroup.map_mono (Subgroup.prod_mono U3_le_P1 U3_le_P1))
      (by rw [Subgroup.card_map_of_injective rho_injective, card_prod_subgroup, card_P1, hBcard,
        hScard]; norm_num)
    exact E3.le_nPrime hYB hBimg (by rw [hYdef]; infer_instance) hYcard hBab hBodd hS hBS
  ·
    set S := (U3.prod U3).map rho ⊔ Subgroup.zpowers tau with hSdef
    have hScard : Nat.card S = 2 ^ 7 := by
      rw [hSdef, card_map_prod_sup_tau, card_U3]
      norm_num
    have hSN : S ≤ norm := sup_le ((Subgroup.map_le_range _ _).trans img_le_norm)
      ((Subgroup.zpowers_le).mpr tau_mem_norm)
    have hS : IsSylowIn 2 S norm := hsyl hSN hScard (by rw [card_norm]; norm_num)
    have hBS := hperm (S := S) (R := (P1.prod P1).map rho ⊔ Subgroup.zpowers tau)
      (IsPGroup.of_card hScard)
      ((Subgroup.map_mono (Subgroup.prod_mono C3_le_P1 C3_le_P1)).trans le_sup_left)
      (sup_le_sup_right (Subgroup.map_mono (Subgroup.prod_mono U3_le_P1 U3_le_P1)) _)
      (by rw [card_map_prod_sup_tau, card_P1, hBcard, hScard]; norm_num)
    exact E3.le_nPrime hYB (hBimg.trans img_le_norm) (by rw [hYdef]; infer_instance) hYcard
      hBab hBodd hS hBS

theorem mem_img_of_odd {x : MulAut WMod} (hx : x ∈ norm) (ho : Odd (orderOf x)) : x ∈ img := by
  obtain ⟨k, hk⟩ := ho
  have h1 : x = (x ^ 2) ^ (k + 1) := by
    rw [← pow_mul, show 2 * (k + 1) = orderOf x + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have h2 : x ^ 2 ∈ img := by
    obtain ⟨g, rfl | rfl⟩ := mem_norm_iff.mp hx
    · exact img.pow_mem (rho_mem_img g) 2
    · have e : (rho g * tau) ^ 2 = rho (g * g.swap) := by
        rw [pow_two, map_mul]
        calc rho g * tau * (rho g * tau) = rho g * (tau * rho g) * tau := by
              simp only [mul_assoc]
          _ = rho g * (rho g.swap * tau) * tau := by rw [tau_mul_rho]
          _ = rho g * rho g.swap * (tau * tau) := by simp only [mul_assoc]
          _ = rho g * rho g.swap := by rw [tau_mul_self, mul_one]
      rw [e]
      exact rho_mem_img _
  rw [h1]
  exact img.pow_mem h2 _

theorem card_comap_rho (H : Subgroup (MulAut WMod)) :
    Nat.card (H.comap rho) = Nat.card ↥(H ⊓ img) := by
  have h : (H.comap rho).map rho = H ⊓ img := by
    rw [Subgroup.map_comap_eq, inf_comm]
    rfl
  rw [← h, Subgroup.card_map_of_injective rho_injective]

theorem not_orderOf_seven {X B S : Subgroup (MulAut WMod)} (hX1 : img ≤ X) (hX2 : X ≤ norm)
    (hBX : B ≤ X) (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hBodd : Odd (Nat.card B))
    (hS : IsSylowIn 2 S X)
    (hBS : (B : Set (MulAut WMod)) * (S : Set (MulAut WMod)) = (S : Set _) * (B : Set _))
    {y : MulAut WMod} (hy : y ∈ B) (hy7 : orderOf y = 7) : False := by
  have : Finite (MulAut WMod) := MulEquiv.finite_left
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBimg : B ≤ img := fun b hb => mem_img_of_odd (hX2 (hBX hb))
    (Odd.of_dvd_nat hBodd (Subgroup.orderOf_dvd_natCard B hb))
  obtain ⟨k, hk⟩ := hS.isPGroup.exists_card_eq
  have hcop : Nat.Coprime (Nat.card B) (Nat.card S) := by
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hBodd)
  have hinf : B ⊓ S = ⊥ := (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have hsup : Nat.card ↥(B ⊔ S) = Nat.card B * Nat.card S :=
    SL3One.card_sup_of_permute hBS hinf
  have key : Nat.card ↥(S ⊓ img) = 64 ∧ Nat.card ↥((B ⊔ S) ⊓ img) = 64 * Nat.card B := by
    rcases eq_img_or_eq_norm hX1 hX2 with rfl | rfl
    · have hS64 : Nat.card S = 64 := card_of_isSylowIn hS (a := 6) (m := 441)
        (by rw [card_img]; norm_num) (by decide)
      have hSi : S ≤ img := hS.le
      rw [inf_eq_left.mpr hSi, inf_eq_left.mpr (sup_le hBX hSi), hsup, hS64]
      exact ⟨rfl, mul_comm _ _⟩
    · have hS128 : Nat.card S = 128 := card_of_isSylowIn hS (a := 7) (m := 441)
        (by rw [card_norm]; norm_num) (by decide)
      have hSnot : ¬ S ≤ img := fun h => by
        have h1 := Subgroup.card_dvd_of_le h
        rw [hS128, card_img] at h1
        norm_num at h1
      have h1 := card_inf_img_mul_two hS.le hSnot
      have h2 := card_inf_img_mul_two (sup_le hBX hS.le) fun h => hSnot (le_sup_right.trans h)
      rw [hS128] at h1
      rw [hsup, hS128] at h2
      constructor <;> omega
  set R := (B ⊔ S).comap rho with hRdef
  set P := S.comap rho with hPdef
  set B' := B.comap rho with hB'def
  have hB'card : Nat.card B' = Nat.card B := by
    rw [hB'def, card_comap_rho, inf_eq_left.mpr hBimg]
  have hP : Nat.card P = 64 := by rw [hPdef, card_comap_rho, key.1]
  have hR : Nat.card R = 64 * Nat.card B' := by
    rw [hRdef, card_comap_rho, key.2, hB'card]
  have hP2 : IsPGroup 2 P := IsPGroup.of_card (n := 6) (by rw [hP]; norm_num)
  have hPR : P ≤ R := Subgroup.comap_mono le_sup_right
  have hBR : B' ≤ R := Subgroup.comap_mono le_sup_left
  have hB'ab : ∀ a ∈ B', ∀ b ∈ B', a * b = b * a := fun a ha b hb =>
    rho_injective (by rw [map_mul, map_mul]; exact hBab _ ha _ hb)
  have hB'odd : Odd (Nat.card B') := by rw [hB'card]; exact hBodd
  obtain ⟨z, rfl⟩ := hBimg hy
  have hz : z ∈ B' := hy
  have hz7 : orderOf z = 7 := by rw [← orderOf_injective rho rho_injective]; exact hy7
  have hzp : z ^ 7 = 1 := by rw [← hz7, pow_orderOf_eq_one]
  have h1 : orderOf z.1 ∣ 7 := orderOf_dvd_of_pow_eq_one (by
    have := congrArg Prod.fst hzp
    rwa [Prod.pow_fst] at this)
  have h2 : orderOf z.2 ∣ 7 := orderOf_dvd_of_pow_eq_one (by
    have := congrArg Prod.snd hzp
    rwa [Prod.pow_snd] at this)
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp h1 with h1 | h1
  · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp h2 with h2 | h2
    · have hz1 : z = 1 := Prod.ext (orderOf_eq_one_iff.mp h1) (orderOf_eq_one_iff.mp h2)
      rw [hz1, orderOf_one] at hz7
      norm_num at hz7
    · exact false_of_orderOf_snd hPR hP2 hP hBR hB'ab hB'odd hR hz h2
  · exact false_of_orderOf_fst hPR hP2 hP hBR hB'ab hB'odd hR hz h1

theorem seven_dvd_of_dvd {c : ℕ} (hc : 3 ≤ c) (h : 2 ^ c - 1 ∣ 441) : 7 ∣ 2 ^ c - 1 := by
  have hle : 2 ^ c - 1 ≤ 441 := Nat.le_of_dvd (by norm_num) h
  have hc9 : c < 9 := by
    by_contra hc9
    push Not at hc9
    have : 2 ^ 9 ≤ 2 ^ c := Nat.pow_le_pow_right (by norm_num) hc9
    omega
  interval_cases c <;> revert h <;> decide

theorem nPrime_eq_two {X : Subgroup (MulAut WMod)} (hX1 : img ≤ X) (hX2 : X ≤ norm) :
    E3.nPrime X = 2 := by
  refine le_antisymm ?_ (two_le_nPrime hX1 hX2)
  have : Finite (MulAut WMod) := MulEquiv.finite_left
  unfold E3.nPrime
  refine csSup_le ⟨1, ⊥, ⊥, (E1.exists_isSylowIn_two X).choose, bot_le, bot_le, inferInstance,
    by simp, fun a ha b hb => ?_, by simp, (E1.exists_isSylowIn_two X).choose_spec, by simp⟩ ?_
  · rw [Subgroup.mem_bot.1 ha, Subgroup.mem_bot.1 hb]
  · rintro c ⟨Y, B, S, hYB, hBX, -, hYc, hBab, hBodd, hS, hBS⟩
    by_contra hc
    push Not at hc
    have hYodd : Odd (Nat.card Y) := Odd.of_dvd_nat hBodd (Subgroup.card_dvd_of_le hYB)
    have hYdvd : Nat.card Y ∣ 2 ^ 7 * 441 := by
      have h1 := Subgroup.card_dvd_of_le ((hYB.trans hBX).trans hX2)
      rw [card_norm] at h1
      exact h1.trans (by norm_num)
    have hY441 : Nat.card Y ∣ 441 :=
      (Nat.Coprime.pow_right 7 (Nat.coprime_two_right.mpr hYodd)).dvd_of_dvd_mul_left hYdvd
    have h7 : 7 ∣ Nat.card Y := by
      rw [hYc] at hY441 ⊢
      exact seven_dvd_of_dvd hc hY441
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) 7 h7
    exact not_orderOf_seven hX1 hX2 hBX hBab hBodd hS hBS (hYB y.2)
      (by rw [Subgroup.orderOf_coe]; exact hy)

theorem H44_L3Wreath_nPrime {V : Type*} [CommGroup V] {H M : Subgroup (MulAut V)}
    (hreal : (tensorPairModel SL32 SL32).RealizesMod H) (hHM : H ≤ M)
    (hMN : M ≤ Subgroup.normalizer (H : Set (MulAut V))) : E3.nPrime M = 2 := by
  obtain ⟨e, he⟩ := exists_model hreal
  have h1 : img ≤ M.map (congrHom e) := he ▸ Subgroup.map_mono hHM
  have h2 : M.map (congrHom e) ≤ norm := by
    have h3 : (Subgroup.normalizer (H : Set (MulAut V))).map (congrHom e) =
        Subgroup.normalizer ((H.map (congrHom e) : Subgroup (MulAut WMod)) :
          Set (MulAut WMod)) :=
      Subgroup.map_equiv_normalizer_eq H (MulAut.congr e)
    have h4 := (Subgroup.map_mono (f := congrHom e) hMN).trans (le_of_eq h3)
    have h5 := congrArg (fun K : Subgroup (MulAut WMod) => Subgroup.normalizer
      (K : Set (MulAut WMod))) he
    exact h4.trans (le_of_eq h5)
  have h6 := nPrime_map_congrHom e M
  rw [← h6]
  exact nPrime_eq_two h1 h2

end L3Wr

end H

end CFSG.Quasithin
