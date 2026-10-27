module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem25H
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem25I

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique Matrix
open scoped IsMulCommutative

namespace Lem25

variable {G : Type} [Group G]

theorem conj_eq_or_inv_of_sq {U : Subgroup G} {h t : G} {p : ℕ} (hp : p.Prime)
    (hord : orderOf h = p) (hhU : h ∈ Subgroup.normalizer (U : Set G))
    (htU : t ∈ Subgroup.normalizer (U : Set G)) (hUh : U ⊓ Subgroup.zpowers h = ⊥)
    (ht : t * h * t⁻¹ ∈ U ⊔ Subgroup.zpowers h) (ht2 : t * t = 1) :
    ∃ u ∈ U, t * h * t⁻¹ = u * h ∨ t * h * t⁻¹ = u * h⁻¹ := by
  have hPU : Subgroup.zpowers h ≤ Subgroup.normalizer (U : Set G) :=
    Subgroup.zpowers_le.mpr hhU
  obtain ⟨u, hu, q, hq, huq⟩ := Lem24.exists_mul_of_mem_sup_normal hPU ht
  obtain ⟨j₀, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
  set j : ℕ := (j₀ % (p : ℤ)).toNat with hjdef
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hj0 : 0 ≤ j₀ % (p : ℤ) := Int.emod_nonneg _ hp0.ne'
  have hjp : j < p := by
    have : j₀ % (p : ℤ) < p := Int.emod_lt_of_pos _ hp0
    omega
  have hhj : h ^ j₀ = h ^ j := by
    rw [← zpow_mod_orderOf, hord, ← zpow_natCast, hjdef, Int.toNat_of_nonneg hj0]
  rw [hhj] at huq
  have htinv : t⁻¹ = t := by rw [inv_eq_iff_mul_eq_one, ht2]
  obtain ⟨z, hz, hzj⟩ := Lem24.exists_pow_eq_mul_pow hu (Subgroup.pow_mem _ hhU j) j
  have hh : h = (t * u * t⁻¹) * z * h ^ (j * j) := by
    calc h = t * t * h * (t * t) := by rw [ht2, one_mul, mul_one]
      _ = t * (t * h * t⁻¹) * t⁻¹ := by rw [htinv]; group
      _ = t * (u * h ^ j) * t⁻¹ := by rw [huq]
      _ = (t * u * t⁻¹) * (t * h * t⁻¹) ^ j := by
          rw [_root_.conj_pow]; group
      _ = (t * u * t⁻¹) * (u * h ^ j) ^ j := by rw [← huq]
      _ = (t * u * t⁻¹) * z * h ^ (j * j) := by
          rw [hzj, ← pow_mul]; simp only [mul_assoc]
  have hw : (t * u * t⁻¹) * z ∈ U :=
    U.mul_mem ((Subgroup.mem_normalizer_iff.mp htU u).mp hu) hz
  have hpow : h * (h ^ (j * j))⁻¹ ∈ U ⊓ Subgroup.zpowers h := by
    refine ⟨?_, Subgroup.mul_mem _ (Subgroup.mem_zpowers h)
      (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers h) _))⟩
    have : h * (h ^ (j * j))⁻¹ = (t * u * t⁻¹) * z := mul_inv_eq_iff_eq_mul.mpr hh
    rw [this]
    exact hw
  rw [hUh, Subgroup.mem_bot, mul_inv_eq_one] at hpow
  have hj1 : 1 ≤ j := by
    by_contra hj
    have : j = 0 := by omega
    rw [this, mul_zero, pow_zero] at hpow
    rw [hpow, orderOf_one] at hord
    exact hp.one_lt.ne hord
  have hdvd : p ∣ (j - 1) * (j + 1) := by
    have h1 : h ^ (j * j) = h ^ 1 := by rw [pow_one]; exact hpow.symm
    rw [pow_eq_pow_iff_modEq, hord] at h1
    have h2 := (Nat.modEq_iff_dvd' (Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (by omega)))).mp h1.symm
    have h3 : j * j - 1 = (j - 1) * (j + 1) := by
      obtain ⟨k, hk⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      rw [hk, Nat.add_sub_cancel, show (k + 1) * (k + 1) = k * (k + 1 + 1) + 1 by ring]
      omega
    rw [← h3]
    exact h2
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with h4 | h4
  ·
    have h5 : j - 1 = 0 := Nat.eq_zero_of_dvd_of_lt h4 (by omega)
    have h6 : j = 1 := by omega
    exact ⟨u, hu, Or.inl (by rw [← huq, h6, pow_one])⟩
  ·
    have h5 : j + 1 = p := by
      obtain ⟨k, hk⟩ := h4
      have hk1 : k = 1 := by
        rcases k with _ | _ | k
        · omega
        · rfl
        · nlinarith [hp.pos]
      rw [hk, hk1, mul_one]
    refine ⟨u, hu, Or.inr ?_⟩
    rw [← huq]
    congr 1
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, h5, ← hord, pow_orderOf_eq_one]

theorem conj_inv_of_mem_V [Finite G] (h1222 : Stmt12_2_2) {T L V H P U I : Subgroup G} {h : G}
    {n p : ℕ} (hH : Hyp1223 G T L V) (hC : Config12_2_24 T L V H P U I h n p) :
    ∀ v ∈ V, v ∉ U → ∃ u ∈ U, v * h * v⁻¹ = u * h⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hHs, -, -, -, -, -, hp, hp2, hP, hord, -, -, hI, -, -, -, hUe, hD, hUP,
    hidx, -, hUO, -, hK, hHU, -, -, -, -, -⟩ := hC
  have hTH : T ≤ H := hHs.1.1
  have hVe : IsElemAbelian 2 V := S125.isElemAbelian_of_hyp1223 hH
  have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hVe
  have hU2 : IsPGroup 2 U := B2F.isPGroup_of_isElemAbelian hUe
  obtain ⟨S, rfl⟩ := exists_sylow_coe_eq hH.sylow
  have hUT : U ≤ (S : Subgroup G) :=
    hUO.trans (A7.pCoreOf_le_of_le_normalizer S (hTH.trans Subgroup.le_normalizer))
  obtain ⟨-, -, hall⟩ := ((h1222 G S hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left
    hH.notAlt) L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨⟨hVT, hTV, -, -⟩, -, -, -, -⟩ := hall V hH.irrPlus
  have hPh : P = Subgroup.zpowers h := hP
  have hh2 : h ∈ oTwoUpper H := by
    rw [hK, hPh]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers h)
  have hhU : h ∈ Subgroup.normalizer (U : Set G) := hHU (oTwoUpper_le H hh2)
  have hUh : U ⊓ Subgroup.zpowers h = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxU, hxh⟩
    obtain ⟨k, hk⟩ := hU2 ⟨x, hxU⟩
    have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hxp : x ^ p = 1 := by
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxh
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, ← hord,
        pow_orderOf_eq_one, _root_.one_zpow]
    have hcop : Nat.gcd (2 ^ k) p = 1 :=
      Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm)
    have := pow_gcd_eq_one.mpr ⟨hk', hxp⟩
    rw [hcop, pow_one] at this
    exact this
  have hconj : ∀ t ∈ (S : Subgroup G), t * h * t⁻¹ ∈ U ⊔ Subgroup.zpowers h := by
    intro t ht
    have h1 := (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper H (hTH ht)) h).mp hh2
    rwa [hK, hPh, sup_comm] at h1
  intro v₀ hv₀V hv₀U
  have hv₀2 : v₀ * v₀ = 1 := by rw [← pow_two]; exact hVe.2 v₀ hv₀V
  obtain ⟨u₀, hu₀, h1 | h1⟩ := conj_eq_or_inv_of_sq hp hord hhU (hHU (hTH (hVT hv₀V))) hUh
    (hconj v₀ (hVT hv₀V)) hv₀2
  ·
    exfalso
    have hcomm : ∀ v ∈ V, v * h * v⁻¹ * h⁻¹ ∈ U := by
      intro v hv
      by_cases hvU : v ∈ U
      · rw [show v * h * v⁻¹ * h⁻¹ = v * (h * v⁻¹ * h⁻¹) by group]
        exact U.mul_mem hvU ((Subgroup.mem_normalizer_iff.mp hhU _).mp (U.inv_mem hvU))
      · have ha : v₀⁻¹ * v ∈ U ⊓ V := by
          have h2 := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨v₀, hv₀V⟩ : ↥V)⁻¹)
            (b := (⟨v, hv⟩ : ↥V))).mpr (by
              rw [inv_mem_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
              exact iff_of_false (fun h3 => hv₀U h3.1) (fun h3 => hvU h3.1))
          rw [Subgroup.mem_subgroupOf] at h2
          exact h2
        obtain ⟨a, haUV, rfl⟩ : ∃ a ∈ U ⊓ V, v = v₀ * a := ⟨v₀⁻¹ * v, ha, by group⟩
        have hah : a * h * a⁻¹ * h⁻¹ ∈ U := by
          rw [show a * h * a⁻¹ * h⁻¹ = a * (h * a⁻¹ * h⁻¹) by group]
          exact U.mul_mem haUV.1 ((Subgroup.mem_normalizer_iff.mp hhU _).mp
            (U.inv_mem haUV.1))
        have h2 : v₀ * (a * h * a⁻¹ * h⁻¹) * v₀⁻¹ ∈ U :=
          (Subgroup.mem_normalizer_iff.mp (hHU (hTH (hVT hv₀V))) _).mp hah
        rw [show v₀ * a * h * (v₀ * a)⁻¹ * h⁻¹ =
          (v₀ * (a * h * a⁻¹ * h⁻¹) * v₀⁻¹) * (v₀ * h * v₀⁻¹ * h⁻¹) by group, h1,
          show u₀ * h * h⁻¹ = u₀ by group]
        exact U.mul_mem h2 hu₀
    have hVh : CFSG.conjugate V h ≤ U ⊔ V := by
      intro x hx
      have hxv : h * x * h⁻¹ ∈ V := BlueprintB2.mem_conjugate_iff.mp hx
      have h2 : h⁻¹ * ((h * x * h⁻¹) * h * (h * x * h⁻¹)⁻¹ * h⁻¹) * h ∈ U := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hhU) _).mp (hcomm _ hxv)
        rwa [inv_inv] at this
      have h3 : x = (h⁻¹ * ((h * x * h⁻¹) * h * (h * x * h⁻¹)⁻¹ * h⁻¹) * h) *
          (h * x * h⁻¹) := by group
      rw [h3]
      exact Subgroup.mul_mem_sup h2 hxv
    have hIUV : I ≤ U ⊔ V := by
      rw [hI]
      exact sup_le le_sup_right hVh
    have hUV2 : IsPGroup 2 ↥(U ⊔ V) :=
      IsPGroup.to_sup_of_normal_right' hU2 hV2 (hUT.trans hTV)
    have hI2 : IsPGroup 2 I := hUV2.to_le hIUV
    obtain ⟨_, ⟨eD⟩⟩ := hD
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (U.subgroupOf I)
    rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card] at hcard
    obtain ⟨k, hk⟩ := hI2.exists_card_eq
    have hpd : p ∣ 2 ^ k := by
      rw [← hk, hcard]
      exact Dvd.dvd.mul_right (dvd_mul_left p 2) _
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hpd))
  · exact ⟨u₀, hu₀, h1⟩

@[expose] def Nm3 (k : Fin 3 → ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  Matrix.of fun i j => (if i = j then 1 else 0) + (if j = 0 then k i else 0)

theorem nm3_sq : ∀ k : Fin 3 → ZMod 2, k 0 = 0 → Nm3 k * Nm3 k = 1 := by
  unfold Nm3
  decide +kernel

theorem nm3_fix : ∀ k x : Fin 3 → ZMod 2, k 0 = 0 → x 0 = 0 → Nm3 k *ᵥ x = x := by
  unfold Nm3
  decide +kernel

theorem nm3_zero : ∀ k x : Fin 3 → ZMod 2, k 0 = 0 → (Nm3 k *ᵥ x) 0 = x 0 := by
  unfold Nm3
  decide +kernel

@[expose] def nm3Unit (k : Fin 3 → ZMod 2) (hk : k 0 = 0) : GL (Fin 3) (ZMod 2) :=
  ⟨Nm3 k, Nm3 k, nm3_sq k hk, nm3_sq k hk⟩

theorem row0_of_iff {M : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (hM : ∀ x : Fin 3 → ZMod 2, (M *ᵥ x) 0 = 0 ↔ x 0 = 0) :
    M = !![1, 0, 0; M 1 0, M 1 1, M 1 2; M 2 0, M 2 1, M 2 2] := by
  have hz : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide
  have h0 := hM (Pi.single 0 1)
  have h1 := hM (Pi.single 1 1)
  have h2 := hM (Pi.single 2 1)
  rw [Matrix.mulVec_single_one] at h0 h1 h2
  simp at h0 h1 h2
  have e0 : M 0 0 = 1 := hz _ h0
  conv_lhs => rw [Matrix.eta_fin_three M]
  rw [e0, h1, h2]

theorem mul_nm3_eq : ∀ a b c d e f : ZMod 2,
    (∀ x : Fin 3 → ZMod 2, x 0 = 0 →
      !![1, 0, 0; a, b, c; d, e, f] *ᵥ (!![1, 0, 0; a, b, c; d, e, f] *ᵥ x) = x) →
    !![1, 0, 0; a, b, c; d, e, f] * Nm3 ![0, b * a + c * d, e * a + f * d] =
      !![1, 0, 0; 0, b, c; 0, e, f] := by
  unfold Nm3
  decide +kernel

theorem inv_cases : ∀ a b c d e f : ZMod 2,
    (∀ x : Fin 3 → ZMod 2, x 0 = 0 →
      !![1, 0, 0; a, b, c; d, e, f] *ᵥ (!![1, 0, 0; a, b, c; d, e, f] *ᵥ x) = x) →
    (∃ x : Fin 3 → ZMod 2, x 0 = 0 ∧ !![1, 0, 0; a, b, c; d, e, f] *ᵥ x ≠ x) →
    (b = 1 ∧ c = 1 ∧ e = 0 ∧ f = 1) ∨ (b = 1 ∧ c = 0 ∧ e = 1 ∧ f = 1) ∨
      (b = 0 ∧ c = 1 ∧ e = 1 ∧ f = 0) := by
  decide +kernel

theorem exists_conj_nm3 : ∀ b c e f : ZMod 2,
    ((b = 1 ∧ c = 1 ∧ e = 0 ∧ f = 1) ∨ (b = 1 ∧ c = 0 ∧ e = 1 ∧ f = 1) ∨
      (b = 0 ∧ c = 1 ∧ e = 1 ∧ f = 0)) →
    ∃ s s' : Matrix (Fin 3) (Fin 3) (ZMod 2), s * s' = 1 ∧ s' * s = 1 ∧
      s * Nm3 (Pi.single 1 1) = !![1, 0, 0; 0, b, c; 0, e, f] * s ∧
      ∃ x : Fin 3 → ZMod 2, x 0 = 0 ∧ !![1, 0, 0; 0, b, c; 0, e, f] *ᵥ x ≠ x := by
  rintro b c e f (⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩)
  · exact ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], !![0, 0, 1; 0, 1, 0; 1, 0, 0],
      by decide +kernel, by decide +kernel, by unfold Nm3; decide +kernel,
      ![0, 0, 1], rfl, by decide +kernel⟩
  · exact ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], !![0, 1, 0; 0, 0, 1; 1, 0, 0],
      by decide +kernel, by decide +kernel, by unfold Nm3; decide +kernel,
      ![0, 1, 0], rfl, by decide +kernel⟩
  · exact ⟨!![0, 0, 1; 0, 1, 0; 1, 1, 0], !![0, 1, 1; 0, 1, 0; 1, 0, 0],
      by decide +kernel, by decide +kernel, by unfold Nm3; decide +kernel,
      ![0, 1, 0], rfl, by decide +kernel⟩

theorem card_modEq_card_centralizer [Finite G] {F : Subgroup G} {c : G} {q : ℕ} [Fact q.Prime]
    (hc : IsPGroup q (Subgroup.zpowers c)) (hcF : c ∈ Subgroup.normalizer (F : Set G)) :
    Nat.card F ≡ Nat.card ↥(F ⊓ Subgroup.centralizer ({c} : Set G)) [MOD q] := by
  have hPN : Subgroup.zpowers c ≤ Subgroup.normalizer (F : Set G) :=
    Subgroup.zpowers_le.mpr hcF
  let φ₀ : ↥(Subgroup.zpowers c) →* MulAut ↥F :=
    (Subgroup.normalizerMonoidHom F).comp (Subgroup.inclusion hPN)
  let _ : MulAction ↥(Subgroup.zpowers c) ↥F := MulAction.compHom ↥F φ₀
  have hsmul : ∀ (g : ↥(Subgroup.zpowers c)) (f : ↥F),
      ((g • f : ↥F) : G) = (g : G) * (f : G) * (g : G)⁻¹ := fun _ _ => rfl
  have hmod := hc.card_modEq_card_fixedPoints ↥F
  have hC : Nat.card ↥(F ⊓ Subgroup.centralizer ({c} : Set G)) =
      Nat.card (MulAction.fixedPoints ↥(Subgroup.zpowers c) ↥F) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨⟨x, x.2.1⟩, fun g => Subtype.ext ?_⟩
        invFun := fun y => ⟨y.1, y.1.2, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    · rw [hsmul]
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp g.2
      have hxc : Commute c (x : G) :=
        (Subgroup.mem_centralizer_iff.mp x.2.2 c (Set.mem_singleton c))
      show (g : G) * (x : G) * (g : G)⁻¹ = x
      rw [← hj, ((hxc.zpow_left j).eq), mul_inv_cancel_right]
    · rw [Set.mem_singleton_iff] at hk
      subst hk
      have h1 := congrArg Subtype.val (y.2 ⟨k, Subgroup.mem_zpowers k⟩)
      rw [hsmul] at h1
      calc k * ((y : ↥F) : G) = k * (y : ↥F) * k⁻¹ * k := by group
        _ = (y : ↥F) * k := by rw [h1]
  rw [hC]
  exact hmod

theorem exists_involution_of_three
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h1216 : Stmt12_2_16) (h1220 : Stmt12_2_20) [Finite G] {T L V H P U I : Subgroup G} {h : G}
    {n p : ℕ} (hH : Hyp1223 G T L V) (hNE : NoEscape12_2_13 L V)
    (hC : Config12_2_24 T L V H P U I h n p) (hn3 : n = 3) :
    ∃ t ∈ T, t * t = 1 ∧ ∃ w ∈ U ⊓ V, t * w * t⁻¹ ≠ w := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstar := lem12225Star_of h331 h1222 h323 h1216 h1220 G T L V H P U I h n p hH hNE hC
  obtain ⟨S, rfl⟩ := exists_sylow_coe_eq hH.sylow
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hCVT, -⟩ := hstar
  obtain ⟨hHs, -, -, hVn, -, -, -, -, -, -, -, -, -, -, -, -, hUe, -, -,
    hidx, ⟨hcommV, htv⟩, hUO, -, -, hHU, -, -, -, -, -⟩ := hC
  subst hn3
  have hTH : (S : Subgroup G) ≤ H := hHs.1.1
  have hLV := le_normalizer_of_hyp1223 hH
  have hVe : IsElemAbelian 2 V := S125.isElemAbelian_of_hyp1223 hH
  have hU2' : ∀ u ∈ U, u * u = 1 := fun u hu => by rw [← pow_two]; exact hUe.2 u hu
  have hUT : U ≤ (S : Subgroup G) :=
    hUO.trans (A7.pCoreOf_le_of_le_normalizer S (hTH.trans Subgroup.le_normalizer))
  have : IsMulCommutative ↥V := hcommV
  have hV2' : ∀ v : ↥V, v * v = 1 := fun v => by
    rw [← pow_two]
    exact Subtype.ext (hVe.2 v v.2)
  obtain ⟨-, -, hall⟩ := ((h1222 G S hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left
    hH.notAlt) L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨⟨hVT, hTV, hredV, -⟩, -, -, -, -⟩ := hall V hH.irrPlus
  obtain ⟨-, -, -, htop, -, -⟩ := h1220 G S L V hH hNE
  have hUN : U ≤ Subgroup.normalizer (V : Set G) := hUT.trans hTV
  have hcard3 : Nat.card ↥V = 2 ^ (2 + 1) := hVn
  obtain ⟨e, he⟩ := exists_coords_index_two hV2' hcard3 (A := (U ⊓ V).subgroupOf V) hidx
  have he' : ∀ w : ↥V, (w : G) ∈ U ⊓ V ↔ Multiplicative.toAdd (e w) 0 = 0 := fun w => by
    rw [← he, Subgroup.mem_subgroupOf]
  have hsurj : ∀ x : Fin (2 + 1) → ZMod 2, ∃ w : ↥V, Multiplicative.toAdd (e w) = x :=
    fun x => ⟨e.symm (Multiplicative.ofAdd x), by rw [MulEquiv.apply_symm_apply, toAdd_ofAdd]⟩
  have heinj : ∀ w w' : ↥V, Multiplicative.toAdd (e w) = Multiplicative.toAdd (e w') →
      (w : G) = w' := fun w w' h1 =>
    congrArg Subtype.val (e.injective (Multiplicative.toAdd.injective h1))
  have hA4 : Nat.card ↥(U ⊓ V) = 4 := by
    have h1 := Subgroup.card_mul_index ((U ⊓ V).subgroupOf V)
    have hA2 : ((U ⊓ V).subgroupOf V).index = 2 := hidx
    rw [hA2, hVn] at h1
    have h2 : Nat.card ↥((U ⊓ V).subgroupOf V) = Nat.card ↥(U ⊓ V) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    omega
  have hCLV' : L ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 L :=
    Lem24.centralizer_le_pCoreOf hH hredV (by norm_num) e htop
  have hCVS : (L ⊔ (S : Subgroup G)) ⊓ Subgroup.centralizer (V : Set G) ≤ (S : Subgroup G) := by
    set X := (L ⊔ (S : Subgroup G)) ⊓ Subgroup.centralizer (V : Set G) with hX
    have hX2 : IsPGroup 2 X := by
      intro ⟨x, hx⟩
      obtain ⟨l, hl, t, ht, hlt⟩ := Lem24.exists_mul_of_mem_sup_normal hH.normalizes hx.1
      obtain ⟨k, hk⟩ := S.isPGroup' ⟨t, ht⟩
      have hk' : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      obtain ⟨z, hz, hzt⟩ := Lem24.exists_pow_eq_mul_pow hl (hH.normalizes ht) (2 ^ k)
      rw [hk', mul_one] at hzt
      have hzV : z ∈ Subgroup.centralizer (V : Set G) := by
        rw [← hzt, hlt]
        exact Subgroup.pow_mem _ hx.2 _
      have hzO := hCLV' ⟨hz, hzV⟩
      obtain ⟨j, hj⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) ⟨z, hzO⟩
      refine ⟨k + j, Subtype.ext ?_⟩
      have hj' : z ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
      show (x : G) ^ 2 ^ (k + j) = 1
      rw [pow_add, pow_mul, ← hlt, hzt, hj']
    have hXQ := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun g hg => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg,
        B6.le_normalizer_centralizer (sup_le hLV hTV) hg⟩) hX2
    exact hXQ.trans (A7.pCoreOf_le_of_le_normalizer S (le_sup_right.trans Subgroup.le_normalizer))
  have hUmat : ∀ k : Fin (2 + 1) → ZMod 2, k 0 = 0 → ∃ u : ↥U, ∀ w : ↥V,
      Multiplicative.toAdd (e (A4.actionOn V U hUN u w)) = Nm3 k *ᵥ Multiplicative.toAdd (e w) := by
    intro k hk
    set σ : MulAut ↥V :=
      (CFSG.SectionRank.Ccomm.elemAutEquivGL e).symm (nm3Unit k hk) with hσdef
    have hσv : ∀ w : ↥V, Multiplicative.toAdd (e (σ w)) = Nm3 k *ᵥ Multiplicative.toAdd (e w) := by
      intro w
      have h1 := CFSG.SectionRank.Ccomm.elemAutEquivGL_mulVec e σ w
      rw [hσdef, MulEquiv.apply_symm_apply] at h1
      exact h1.symm
    have hσT : σ ∈ transvAxis ((U ⊓ V).subgroupOf V) := by
      refine ⟨fun a ha => ?_, fun v => ?_⟩
      · have ha0 := (he a).mp ha
        apply e.injective
        apply Multiplicative.toAdd.injective
        rw [hσv, nm3_fix k _ hk ha0]
      · rw [he, map_mul, map_inv, toAdd_mul, toAdd_inv, hσv, Pi.add_apply, Pi.neg_apply,
          nm3_zero k _ hk]
        exact add_neg_cancel _
    obtain ⟨u, hu⟩ := (A4.mem_autOn_iff hUN).mp (htv ▸ hσT)
    exact ⟨u, fun w => by rw [hu, hσv]⟩
  obtain ⟨t₀, ht₀, w₀, hw₀A, hw₀⟩ : ∃ t ∈ (S : Subgroup G), ∃ w ∈ U ⊓ V, t * w * t⁻¹ ≠ w := by
    by_contra hno
    push Not at hno
    have hle : U ⊓ V ≤ V ⊓ Subgroup.centralizer ((S : Subgroup G) : Set G) := fun w hw =>
      ⟨hw.2, Subgroup.mem_centralizer_iff.mpr fun t ht => by
        have := hno t ht w hw
        calc t * w = t * w * t⁻¹ * t := by group
          _ = w * t := by rw [this]⟩
    have := Subgroup.card_le_of_le hle
    rw [hA4, hCVT] at this
    omega
  obtain ⟨k₀, hk₀⟩ := S.isPGroup' ⟨t₀, ht₀⟩
  have hk₀' : t₀ ^ 2 ^ k₀ = 1 := by simpa using congrArg Subtype.val hk₀
  have hex : ∃ i, ∀ w ∈ U ⊓ V, t₀ ^ 2 ^ i * w * (t₀ ^ 2 ^ i)⁻¹ = w :=
    ⟨k₀, fun w _ => by rw [hk₀']; group⟩
  have hi₀spec := Nat.find_spec hex
  have hi₀pos : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0] at hi₀spec
    exact hw₀ (by simpa using hi₀spec w₀ hw₀A)
  have hmin := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
  push Not at hmin
  obtain ⟨w₁, hw₁A, hw₁⟩ := hmin
  set t₁ := t₀ ^ 2 ^ (Nat.find hex - 1) with ht₁
  have ht₁S : t₁ ∈ (S : Subgroup G) := Subgroup.pow_mem _ ht₀ _
  have ht₁sq : ∀ w ∈ U ⊓ V, t₁ * (t₁ * w * t₁⁻¹) * t₁⁻¹ = w := by
    intro w hw
    have h1 := hi₀spec w hw
    have h2 : t₀ ^ 2 ^ Nat.find hex = t₁ * t₁ := by
      rw [ht₁, ← pow_two, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
        hi₀pos)]
    rw [h2] at h1
    rw [show t₁ * (t₁ * w * t₁⁻¹) * t₁⁻¹ = (t₁ * t₁) * w * (t₁ * t₁)⁻¹ by group]
    exact h1
  have ht₁A : ∀ w : ↥V, (t₁ * w * t₁⁻¹ ∈ U ⊓ V ↔ (w : G) ∈ U ⊓ V) := by
    intro w
    have hU := (Subgroup.mem_normalizer_iff.mp (hHU (hTH ht₁S)) w).symm
    constructor
    · rintro ⟨h1, -⟩
      exact ⟨hU.mp h1, w.2⟩
    · rintro ⟨h1, -⟩
      exact ⟨hU.mpr h1, (Subgroup.mem_normalizer_iff.mp (hTV ht₁S) w).mp w.2⟩
  set M₁ : Matrix (Fin (2 + 1)) (Fin (2 + 1)) (ZMod 2) :=
    ((actGL hTV e ⟨t₁, ht₁S⟩ : GL (Fin (2 + 1)) (ZMod 2)) :
      Matrix (Fin (2 + 1)) (Fin (2 + 1)) (ZMod 2)) with hM₁
  have hM₁v : ∀ w : ↥V, M₁ *ᵥ Multiplicative.toAdd (e w) =
      Multiplicative.toAdd (e (A4.actionOn V (S : Subgroup G) hTV ⟨t₁, ht₁S⟩ w)) :=
    fun w => actGL_mulVec hTV e ⟨t₁, ht₁S⟩ w
  have hM₁c : ∀ x, (M₁ *ᵥ x) 0 = 0 ↔ x 0 = 0 := by
    intro x
    obtain ⟨w, rfl⟩ := hsurj x
    rw [hM₁v, ← he', ← he', A4.actionOn_apply_coe]
    exact ht₁A w
  have hM₁2 : ∀ x : Fin (2 + 1) → ZMod 2, x 0 = 0 → M₁ *ᵥ (M₁ *ᵥ x) = x := by
    intro x hx
    obtain ⟨w, rfl⟩ := hsurj x
    have hwA : (w : G) ∈ U ⊓ V := (he' w).mpr hx
    rw [hM₁v, hM₁v]
    congr 2
    apply Subtype.ext
    simp only [A4.actionOn_apply_coe]
    exact ht₁sq w hwA
  have hM₁n : ∃ x : Fin (2 + 1) → ZMod 2, x 0 = 0 ∧ M₁ *ᵥ x ≠ x := by
    refine ⟨Multiplicative.toAdd (e ⟨w₁, hw₁A.2⟩), (he' _).mp hw₁A, fun h1 => hw₁ ?_⟩
    rw [hM₁v] at h1
    have := heinj _ _ h1
    rwa [A4.actionOn_apply_coe] at this
  have hrow := row0_of_iff hM₁c
  set a := M₁ 1 0
  set b := M₁ 1 1
  set c := M₁ 1 2
  set d := M₁ 2 0
  set e₁ := M₁ 2 1
  set f := M₁ 2 2
  rw [hrow] at hM₁2 hM₁n
  have hα := inv_cases a b c d e₁ f hM₁2 hM₁n
  set kv : Fin (2 + 1) → ZMod 2 := ![0, b * a + c * d, e₁ * a + f * d] with hkv
  obtain ⟨u', hu'⟩ := hUmat kv rfl
  set g : Matrix (Fin (2 + 1)) (Fin (2 + 1)) (ZMod 2) := !![1, 0, 0; 0, b, c; 0, e₁, f] with hg
  have hprod : M₁ * Nm3 kv = g := by rw [hrow]; exact mul_nm3_eq a b c d e₁ f hM₁2
  set t := t₁ * (u' : G) with htdef
  have htS : t ∈ (S : Subgroup G) := Subgroup.mul_mem _ ht₁S (hUT u'.2)
  have htv : ∀ w : ↥V, ∃ hw : t * w * t⁻¹ ∈ V,
      Multiplicative.toAdd (e ⟨t * w * t⁻¹, hw⟩) = g *ᵥ Multiplicative.toAdd (e w) := by
    intro w
    set w' := A4.actionOn V U hUN u' w with hw'
    have h1 := hM₁v w'
    rw [hu' w, Matrix.mulVec_mulVec, hprod] at h1
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hTV htS) w).mp w.2, ?_⟩
    rw [h1]
    congr 2
    apply Subtype.ext
    simp only [hw', A4.actionOn_apply_coe, htdef]
    group
  obtain ⟨sm, sm', hss', hs's, hsg, xA, hxA0, hgxA⟩ := exists_conj_nm3 b c e₁ f hα
  obtain ⟨x, hx⟩ := actGL_surjective hLV e htop ⟨sm, sm', hss', hs's⟩
  have hxv : ∀ w : ↥V, sm *ᵥ Multiplicative.toAdd (e w) =
      Multiplicative.toAdd (e (A4.actionOn V L hLV x w)) := fun w => by
    have h1 := actGL_mulVec hLV e x w
    rw [hx] at h1
    exact h1
  obtain ⟨u₀, hu₀⟩ := hUmat (Pi.single 1 1) rfl
  set t' := (x : G) * (u₀ : G) * (x : G)⁻¹ with ht'def
  have ht'v : ∀ w : ↥V, t' * w * t'⁻¹ = t * w * t⁻¹ := by
    intro w
    obtain ⟨hw, hwv⟩ := htv w
    set y₁ := A4.actionOn V L hLV x⁻¹ w with hy₁
    have hy₁e : Multiplicative.toAdd (e y₁) = sm' *ᵥ Multiplicative.toAdd (e w) := by
      have h1 := hxv y₁
      have h2 : A4.actionOn V L hLV x y₁ = w := by
        rw [hy₁, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
      rw [h2] at h1
      rw [← h1, Matrix.mulVec_mulVec, hs's, Matrix.one_mulVec]
    set y₂ := A4.actionOn V U hUN u₀ y₁ with hy₂
    have hgv : g *ᵥ Multiplicative.toAdd (e w) =
        Multiplicative.toAdd (e (A4.actionOn V L hLV x y₂)) := by
      rw [← hxv y₂, hy₂, hu₀, hy₁e, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hsg,
        Matrix.mul_assoc, hss', Matrix.mul_one]
    rw [← hwv] at hgv
    have := heinj _ _ hgv
    simp only [hy₂, hy₁, A4.actionOn_apply_coe, Subgroup.coe_inv, inv_inv] at this
    rw [show t' * w * t'⁻¹ = (x : G) * ((u₀ : G) * ((x : G)⁻¹ * w * (x : G)) *
      (u₀ : G)⁻¹) * (x : G)⁻¹ by rw [ht'def]; group]
    exact this.symm
  have ht'S : t' ∈ (S : Subgroup G) := by
    have hm : t⁻¹ * t' ∈ (L ⊔ (S : Subgroup G)) ⊓ Subgroup.centralizer (V : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨(L ⊔ (S : Subgroup G)).mul_mem
        (Subgroup.mem_sup_right (S.inv_mem htS))
        ((L ⊔ (S : Subgroup G)).mul_mem ((L ⊔ (S : Subgroup G)).mul_mem
          (Subgroup.mem_sup_left x.2) (Subgroup.mem_sup_right (hUT u₀.2)))
          (Subgroup.mem_sup_left (L.inv_mem x.2))), Subgroup.mem_centralizer_iff.mpr
          fun w hw => ?_⟩
      have h1 := ht'v ⟨w, hw⟩
      calc w * (t⁻¹ * t') = t⁻¹ * (t * w * t⁻¹) * t' := by group
        _ = t⁻¹ * (t' * w * t'⁻¹) * t' := by rw [← h1]
        _ = t⁻¹ * t' * w := by group
    have := Subgroup.mul_mem _ htS (hCVS hm)
    rwa [show t * (t⁻¹ * t') = t' by group] at this
  refine ⟨t', ht'S, ?_, ?_⟩
  · rw [ht'def, show (x : G) * u₀ * (x : G)⁻¹ * ((x : G) * u₀ * (x : G)⁻¹) =
      (x : G) * (u₀ * u₀) * (x : G)⁻¹ by group, hU2' _ u₀.2, mul_one, mul_inv_cancel]
  · obtain ⟨wA, hwA⟩ := hsurj xA
    refine ⟨wA, (he' wA).mpr (by rw [hwA]; exact hxA0), fun h1 => hgxA ?_⟩
    obtain ⟨hw, hwv⟩ := htv wA
    have h2 : (⟨t * wA * t⁻¹, hw⟩ : ↥V) = wA :=
      Subtype.ext (show t * (wA : G) * t⁻¹ = wA by rw [← ht'v wA]; exact h1)
    rw [h2, hwA] at hwv
    exact hwv.symm

theorem prime_eq_three_of_three
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h1216 : Stmt12_2_16) (h1220 : Stmt12_2_20) [Finite G] {T L V H P U I : Subgroup G} {h : G}
    {n p : ℕ} (hH : Hyp1223 G T L V) (hNE : NoEscape12_2_13 L V)
    (hC : Config12_2_24 T L V H P U I h n p) (hn3 : n = 3) : p = 3 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t', ht'T, ht'2, w', hw'A, hw'⟩ :=
    exists_involution_of_three h331 h1222 h323 h1216 h1220 hH hNE hC hn3
  have hinvV := conj_inv_of_mem_V h1222 hH hC
  obtain ⟨hHs, -, -, hVn, -, -, hp, hp2, hP, hord, -, -, -, -, hUd, hUi, hUe, -, hUP,
    hidx, -, hUO, -, hK, hHU, -, -, -, -, -⟩ := hC
  subst hn3
  have hTH : T ≤ H := hHs.1.1
  have hVe : IsElemAbelian 2 V := S125.isElemAbelian_of_hyp1223 hH
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hVe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hUe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hU2 : IsPGroup 2 U := B2F.isPGroup_of_isElemAbelian hUe
  obtain ⟨S, rfl⟩ := exists_sylow_coe_eq hH.sylow
  have hUT : U ≤ (S : Subgroup G) :=
    hUO.trans (A7.pCoreOf_le_of_le_normalizer S (hTH.trans Subgroup.le_normalizer))
  obtain ⟨-, -, hall⟩ := ((h1222 G S hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left
    hH.notAlt) L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨⟨hVT, -, -, -⟩, -, -, -, -⟩ := hall V hH.irrPlus
  have hPh : P = Subgroup.zpowers h := hP
  have hh2 : h ∈ oTwoUpper H := by
    rw [hK, hPh]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers h)
  have hhU : h ∈ Subgroup.normalizer (U : Set G) := hHU (oTwoUpper_le H hh2)
  have hUh : ∀ u ∈ U, h * u * h⁻¹ = u → u = 1 := by
    intro u hu hfix
    have huP : u ∈ U ⊓ Subgroup.centralizer (P : Set G) := by
      refine ⟨hu, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
      rw [hPh] at hk
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
      have hc : Commute h u := by
        calc h * u = h * u * h⁻¹ * h := by group
          _ = u * h := by rw [hfix]
      exact (hc.zpow_left j).eq
    rw [hUP, Subgroup.mem_bot] at huP
    exact huP
  have hUh' : U ⊓ Subgroup.zpowers h = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxU, hxh⟩
    obtain ⟨k, hk⟩ := hU2 ⟨x, hxU⟩
    have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hxp : x ^ p = 1 := by
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxh
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, ← hord,
        pow_orderOf_eq_one, _root_.one_zpow]
    have hcop : Nat.gcd (2 ^ k) p = 1 :=
      Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm)
    have := pow_gcd_eq_one.mpr ⟨hk', hxp⟩
    rw [hcop, pow_one] at this
    exact this
  have hconj : ∀ t ∈ (S : Subgroup G), t * h * t⁻¹ ∈ U ⊔ Subgroup.zpowers h := by
    intro t ht
    have h1 := (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper H (hTH ht)) h).mp hh2
    rwa [hK, hPh, sup_comm] at h1
  have hA4 : Nat.card ↥(U ⊓ V) = 4 := by
    have h1 := Subgroup.card_mul_index ((U ⊓ V).subgroupOf V)
    have hA2 : ((U ⊓ V).subgroupOf V).index = 2 := hidx
    rw [hA2, hVn] at h1
    have h2 : Nat.card ↥((U ⊓ V).subgroupOf V) = Nat.card ↥(U ⊓ V) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    omega
  have hBA : Nat.card ↥(U ⊓ CFSG.conjugate V h) = Nat.card ↥(U ⊓ V) := by
    have hf1 : ∀ x ∈ U ⊓ CFSG.conjugate V h, h * x * h⁻¹ ∈ U ⊓ V := fun x hx =>
      ⟨(Subgroup.mem_normalizer_iff.mp hhU _).mp hx.1, BlueprintB2.mem_conjugate_iff.mp hx.2⟩
    have hf2 : ∀ x ∈ U ⊓ V, h⁻¹ * x * h ∈ U ⊓ CFSG.conjugate V h := by
      intro x hx
      refine ⟨?_, BlueprintB2.mem_conjugate_iff.mpr ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hhU) _).mp hx.1
        rwa [inv_inv] at this
      · rw [show h * (h⁻¹ * x * h) * h⁻¹ = x by group]
        exact hx.2
    apply le_antisymm
    · refine Nat.card_le_card_of_injective
        (fun x : ↥(U ⊓ CFSG.conjugate V h) => (⟨h * x * h⁻¹, hf1 x x.2⟩ : ↥(U ⊓ V)))
        fun x y hxy => ?_
      have h1 : h * (x : G) * h⁻¹ = h * y * h⁻¹ := congrArg Subtype.val hxy
      exact Subtype.ext (by simpa using h1)
    · refine Nat.card_le_card_of_injective
        (fun x : ↥(U ⊓ V) => (⟨h⁻¹ * x * h, hf2 x x.2⟩ : ↥(U ⊓ CFSG.conjugate V h)))
        fun x y hxy => ?_
      have h1 : h⁻¹ * (x : G) * h = h⁻¹ * y * h := congrArg Subtype.val hxy
      exact Subtype.ext (by simpa using h1)
  have hU16 : Nat.card U = 16 := by
    have hBC : U ⊓ CFSG.conjugate V h ≤ Subgroup.centralizer ((U ⊓ V : Subgroup G) : Set G) :=
      fun g hg => Subgroup.mem_centralizer_iff.mpr fun c hc => hUab c hc.1 g hg.1
    have h1 := card_sup_eq_mul hBC hUi
    rw [← hUd, hBA, hA4] at h1
    exact h1
  have hp15 := dvd_card_sub_one_of_fpf hp hord hhU hUh
  rw [hU16] at hp15
  have hp35 : p = 3 ∨ p = 5 := by
    rcases (Nat.Prime.dvd_mul hp).mp (show p ∣ 3 * 5 from hp15) with h1 | h1
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h1)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h1)
  rcases hp35 with h3 | h5
  · exact h3
  exfalso
  subst h5
  have hstep2 : ∀ c ∈ (S : Subgroup G), c * h = h * c → c ∈ Subgroup.centralizer (U : Set G) := by
    intro c hc hch
    set F := U ⊓ Subgroup.centralizer ({c} : Set G) with hFdef
    have hcU : c ∈ Subgroup.normalizer (U : Set G) := hHU (hTH hc)
    have hmemF : ∀ g, g ∈ F ↔ g ∈ U ∧ c * g * c⁻¹ = g := by
      intro g
      rw [hFdef, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨hg, hcg⟩
        exact ⟨hg, by rw [← hcg, mul_inv_cancel_right]⟩
      · rintro ⟨hg, hcg⟩
        exact ⟨hg, by
          calc g * c = (c * g * c⁻¹) * c := by rw [hcg]
            _ = c * g := by group⟩
    have hhF : h ∈ Subgroup.normalizer (F : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro g
      have hcomm : c * (h * g * h⁻¹) * c⁻¹ = h * (c * g * c⁻¹) * h⁻¹ := by
        calc c * (h * g * h⁻¹) * c⁻¹ = (c * h) * g * (c * h)⁻¹ := by group
          _ = (h * c) * g * (h * c)⁻¹ := by rw [hch]
          _ = h * (c * g * c⁻¹) * h⁻¹ := by group
      rw [hmemF, hmemF, hcomm]
      constructor
      · rintro ⟨hg, hcg⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp hhU g).mp hg, by rw [hcg]⟩
      · rintro ⟨hg, hcg⟩
        refine ⟨(Subgroup.mem_normalizer_iff.mp hhU g).mpr hg, ?_⟩
        have := congrArg (fun z => h⁻¹ * z * h) hcg
        simpa [mul_assoc] using this
    have hdvd := dvd_card_sub_one_of_fpf hp hord hhF fun f hf hfix =>
      hUh f ((hmemF f).mp hf).1 hfix
    have hFdvd : Nat.card F ∣ 16 := hU16 ▸ Subgroup.card_dvd_of_le inf_le_left
    have hc2 : IsPGroup 2 (Subgroup.zpowers c) := S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hc)
    have hmod := card_modEq_card_centralizer hc2 hcU
    rw [hU16] at hmod
    have hF16 : Nat.card F = 16 := by
      have hle : Nat.card F ≤ 16 := Nat.le_of_dvd (by norm_num) hFdvd
      have hpos : 0 < Nat.card F := Nat.card_pos
      have hmod' : Nat.card F % 2 = 0 := by
        have := hmod.symm
        unfold Nat.ModEq at this
        omega
      interval_cases h1 : Nat.card F <;> omega
    have hFU : F = U := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hF16, hU16])
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' : u ∈ F := hFU ▸ hu
    have := ((hmemF u).mp hu').2
    calc u * c = c * (c⁻¹ * u * c) := by group
      _ = c * u := by
        rw [show c⁻¹ * u * c = u by
          calc c⁻¹ * u * c = c⁻¹ * (c * u * c⁻¹) * c := by rw [this]
            _ = u := by group]
  have hstep3 : ∀ t ∈ (S : Subgroup G), ∀ u₁ ∈ U, t * h * t⁻¹ = u₁ * h →
      t ∈ Subgroup.centralizer (U : Set G) := by
    intro t ht u₁ hu₁ h1
    obtain ⟨u, hu, hut⟩ := exists_mem_centralizer_of_conj_mul hUab hhU hUh hu₁ h1
    have hc := hstep2 (u⁻¹ * t) (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hUT hu)) ht) hut
    rw [show t = u * (u⁻¹ * t) by group]
    exact Subgroup.mul_mem _ (Subgroup.mem_centralizer_iff.mpr fun x hx => hUab x hx u hu) hc
  have hv₀ : ∃ v₀ ∈ V, v₀ ∉ U := by
    by_contra hno
    push Not at hno
    have hVU : (U ⊓ V).subgroupOf V = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_subgroupOf]
      exact ⟨hno x x.2, x.2⟩
    have : ((U ⊓ V).subgroupOf V).index = 2 := hidx
    rw [hVU, Subgroup.index_top] at this
    omega
  obtain ⟨v₀, hv₀V, hv₀U⟩ := hv₀
  obtain ⟨u₁, hu₁, h1 | h1⟩ := conj_eq_or_inv_of_sq hp hord hhU (hHU (hTH ht'T)) hUh'
    (hconj t' ht'T) ht'2
  · apply hw'
    have := Subgroup.mem_centralizer_iff.mp (hstep3 t' ht'T u₁ hu₁ h1) w' hw'A.1
    rw [← this, mul_inv_cancel_right]
  · obtain ⟨u₂, hu₂, hv₀h⟩ := hinvV v₀ hv₀V hv₀U
    have hu₂' : t' * u₂ * t'⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp (hHU (hTH ht'T)) u₂).mp hu₂
    have hu₁' : h * u₁⁻¹ * h⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp hhU _).mp (U.inv_mem hu₁)
    have h2 : t' * v₀ * h * (t' * v₀)⁻¹ = ((t' * u₂ * t'⁻¹) * (h * u₁⁻¹ * h⁻¹)) * h := by
      calc t' * v₀ * h * (t' * v₀)⁻¹ = t' * (v₀ * h * v₀⁻¹) * t'⁻¹ := by group
        _ = t' * (u₂ * h⁻¹) * t'⁻¹ := by rw [hv₀h]
        _ = (t' * u₂ * t'⁻¹) * (t' * h * t'⁻¹)⁻¹ := by group
        _ = (t' * u₂ * t'⁻¹) * (u₁ * h⁻¹)⁻¹ := by rw [h1]
        _ = ((t' * u₂ * t'⁻¹) * (h * u₁⁻¹ * h⁻¹)) * h := by group
    have h3 := hstep3 (t' * v₀) (Subgroup.mul_mem _ ht'T (hVT hv₀V)) _ (U.mul_mem hu₂' hu₁') h2
    apply hw'
    have h4 := Subgroup.mem_centralizer_iff.mp h3 w' hw'A.1
    have h5 : v₀ * w' = w' * v₀ := hVab v₀ hv₀V w' hw'A.2
    calc t' * w' * t'⁻¹ = (t' * v₀) * (v₀⁻¹ * w' * v₀) * (t' * v₀)⁻¹ := by group
      _ = (t' * v₀) * w' * (t' * v₀)⁻¹ := by
          rw [show v₀⁻¹ * w' * v₀ = w' by rw [mul_assoc, ← h5]; group]
      _ = w' := by rw [← h4]; group

end Lem25

end CFSG.Quasithin.H13
