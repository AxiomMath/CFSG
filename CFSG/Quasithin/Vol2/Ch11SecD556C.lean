module

public import CFSG.Quasithin.Vol2.Ch11SecD556B

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem two_eq_zero_of_card {F : Type} [Field F] [Finite F] (hn : n ≠ 0)
    (hF : Nat.card F = 2 ^ n) : (2 : F) = 0 := by
  have : Fintype F := Fintype.ofFinite F
  have hc : ((Fintype.card F : ℕ) : F) = 0 := FiniteField.cast_card_eq_zero F
  rw [← Nat.card_eq_fintype_card, hF] at hc
  push_cast at hc
  exact (pow_eq_zero_iff hn).mp hc

omit [Finite G] in
theorem pCoreOf_le_sectionCentralizer (K : Subgroup G) :
    pCoreOf 2 K ≤ sectionCentralizer K (pCoreOf 2 K) := fun q hq => by
  refine ⟨((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans Subgroup.le_normalizer) hq,
    Subgroup.le_normalizer hq, fun k hk => ?_⟩
  have hk' : k * q⁻¹ * k⁻¹ ∈ pCoreOf 2 K :=
    (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hk) _).mp
      (Subgroup.inv_mem _ hq)
  have e : q * k * q⁻¹ * k⁻¹ = q * (k * q⁻¹ * k⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ hq hk'

theorem mem_pCoreOf_lOf (h1110 : Stmt11_1_0) (h : Hyp11 G T L I n) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) {s : G} (hsL : s ∈ LOf L V₁)
    (hs : s ∈ sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁))) :
    s ∈ pCoreOf 2 (LOf L V₁) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := (h1110 G T L I n h).2.1 1 (Or.inl rfl) V₁ hV₁
  have h2F : (2 : F) = 0 := two_eq_zero_of_card (by have := h.one_lt; omega) hF
  have hsc := mem_sectionCentralizer_lOf (Subgroup.le_normalizer hsL) hs
  set L₁ := LOf L V₁ with hL₁def
  have hcen : (QuotientGroup.mk ⟨s, hsL⟩ : ↥L₁ ⧸ CFSG.pCore 2 ↥L₁) ∈
      Subgroup.center (↥L₁ ⧸ CFSG.pCore 2 ↥L₁) := by
    rw [Subgroup.mem_center_iff]
    intro q
    induction q using QuotientGroup.induction_on with
    | H l =>
      have h1 : (⟨s, hsL⟩ * l * (⟨s, hsL⟩ : ↥L₁)⁻¹ * l⁻¹ : ↥L₁) ∈ CFSG.pCore 2 ↥L₁ := by
        rw [← pCoreOf_subgroupOf, Subgroup.mem_subgroupOf]
        exact hsc.2.2 l l.2
      have h2 := (QuotientGroup.eq_one_iff _).mpr h1
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h2
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
  have hz : (QuotientGroup.mk ⟨s, hsL⟩ : ↥L₁ ⧸ CFSG.pCore 2 ↥L₁) = 1 := by
    have hez : e (QuotientGroup.mk ⟨s, hsL⟩) ∈
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := Subgroup.mem_center_iff.mp hcen (e.symm g)
      have h2 := congrArg e h1
      simpa [map_mul] using h2
    rw [center_SL2_eq_bot h2F, Subgroup.mem_bot] at hez
    exact e.injective (hez.trans e.map_one.symm)
  rw [QuotientGroup.eq_one_iff, ← pCoreOf_subgroupOf, Subgroup.mem_subgroupOf] at hz
  exact hz

theorem stmt11_5_6_two (h1110 : Stmt11_1_0) (h : Hyp11 G T L I n) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) :
    CFSG.pRank 3 ↥(Subgroup.centralizer (V₁ : Set G) ⊓
      sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁))) ≤ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := KOf L V₁ V₁ with hKdef
  set Q := pCoreOf 2 K with hQdef
  set Y := Subgroup.centralizer (V₁ : Set G) ⊓ sectionCentralizer K Q with hYdef
  set L₁ := LOf L V₁ with hL₁def
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := (h1110 G T L I n h).2.1 1 (Or.inl rfl) V₁ hV₁
  have h2F : (2 : F) = 0 := two_eq_zero_of_card (by have := h.one_lt; omega) hF
  have h3 : 3 ∣ Nat.card ↥L₁ := by
    have h1 := three_dvd_card_SL2 h2F
    rw [← Nat.card_congr e.toEquiv] at h1
    exact h1.trans (Subgroup.card_quotient_dvd_card _)
  obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hxord : orderOf (x₀ : G) = 3 := by rw [Subgroup.orderOf_coe, hx₀]
  have hxK : (x₀ : G) ∈ K := le_conjClosure _ _ x₀.2
  have hKN : K ≤ Subgroup.normalizer (V₁ : Set G) := kOf_le_normalizer (lOf_le_normalizer L V₁)
  have hYN : Y ≤ Subgroup.normalizer (V₁ : Set G) :=
    inf_le_left.trans (Subgroup.centralizer_le_normalizer _)
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hxQ : Subgroup.zpowers (x₀ : G) ≤ Subgroup.normalizer (Q : Set G) :=
    Subgroup.zpowers_le.mpr (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hxK)
  set D := Q ⊔ Subgroup.zpowers (x₀ : G) with hDdef
  have hDK : D ≤ K :=
    sup_le (CFSG.LieType.BorelTits.pCoreOf_le 2 K) (Subgroup.zpowers_le.mpr hxK)
  have hxD : (x₀ : G) ∈ D := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have h3D : 3 ∣ Nat.card D := by
    have hx3 : orderOf (⟨x₀, hxD⟩ : ↥D) = 3 := by rw [← Subgroup.orderOf_coe]; exact hxord
    rw [← hx3]
    exact orderOf_dvd_natCard _
  have hV₁T : V₁ ≤ T := (SecA.IsVi.le_fsuV hV₁).trans (SecA.fsuV_le_T h)
  apply csSup_le'
  rintro r ⟨A, hA, hAcard⟩
  set A' := A.map Y.subtype with hA'def
  have hA'Y : A' ≤ Y := Subgroup.map_subtype_le A
  have hA'ab : IsElemAbelian 3 A' := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
    · obtain ⟨a', ha', haa⟩ := Subgroup.mem_map.mp a.2
      obtain ⟨b', hb', hbb⟩ := Subgroup.mem_map.mp b.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← haa, ← hbb]
      have hc := congrArg (fun z : ↥A => ((z : ↥Y) : G)) (mul_comm (⟨a', ha'⟩ : ↥A) ⟨b', hb'⟩)
      simpa using hc
    · obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
      rw [← map_pow, CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 3) (A := A) a' ha',
        map_one]
  have hA'card : Nat.card A' = 3 ^ r := by
    rw [hA'def, Subgroup.card_map_of_injective Y.subtype_injective, hAcard]
  have hA'2 : IsPGroup 3 A' := fun a => ⟨1, Subtype.ext (by simpa using hA'ab.2 a a.2)⟩
  have hA'D : A' ≤ Subgroup.normalizer (D : Set G) := by
    intro a ha
    have haY := hA'Y ha
    apply A4.mem_normalizer_of_conj_mem
    have hD' : D ≤ D.comap (MulAut.conj a).toMonoidHom := by
      refine sup_le (fun q hq => ?_) (Subgroup.zpowers_le.mpr ?_)
      · show a * q * a⁻¹ ∈ D
        exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp haY.2.2.1 q).mp hq)
      · show a * x₀ * a⁻¹ ∈ D
        have hc : a * x₀ * a⁻¹ * (x₀ : G)⁻¹ ∈ Q := haY.2.2.2 _ hxK
        have e : a * x₀ * a⁻¹ = (a * x₀ * a⁻¹ * (x₀ : G)⁻¹) * x₀ := by group
        rw [e]
        exact D.mul_mem (Subgroup.mem_sup_left hc) hxD
    exact fun d hd => hD' hd
  obtain ⟨y, hyD, hyord, hyA⟩ := exists_orderOf_eq_of_isPGroup_normalizer hA'2 hA'D h3D
  have hyA' : y ∉ A' := by
    intro hyA'
    have hyY := hA'Y hyA'
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left Q _ hxQ] at hyD
    obtain ⟨q, hq, z, hz, rfl⟩ := hyD
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hxjsc : (x₀ : G) ^ j ∈ sectionCentralizer K Q := by
      have := (sectionCentralizer K Q).mul_mem
        ((sectionCentralizer K Q).inv_mem (pCoreOf_le_sectionCentralizer K hq)) hyY.2
      rwa [inv_mul_cancel_left] at this
    have hxjO := mem_pCoreOf_lOf h1110 h hV₁ (L₁.zpow_mem x₀.2 j) hxjsc
    have hxj1 : (x₀ : G) ^ j = 1 := by
      obtain ⟨k, hk⟩ := exists_pow_two_pow_eq_one_of_mem
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L₁) hxjO
      have h3' : ((x₀ : G) ^ j) ^ 3 = 1 := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hxord,
          pow_orderOf_eq_one, one_zpow]
      have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left
        (orderOf_dvd_of_pow_eq_one hk) (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)))
        (orderOf_dvd_of_pow_eq_one h3')
      exact orderOf_eq_one_iff.mp this
    simp only [hxj1, mul_one] at hyord
    obtain ⟨k, hk⟩ := exists_pow_two_pow_eq_one_of_mem hQ2 hq
    have h32 := orderOf_dvd_of_pow_eq_one hk
    rw [hyord] at h32
    have := Nat.prime_three.dvd_of_dvd_pow h32
    omega
  have hF3 := isElemAbelian_sup_zpowers hA'ab (by rw [← hyord]; exact pow_orderOf_eq_one y) hyA
  have hcard := card_sup_zpowers_of_not_mem hyord hyA hyA'
  rw [hA'card, ← pow_succ] at hcard
  have hle : A' ⊔ Subgroup.zpowers y ≤ Subgroup.normalizer (V₁ : Set G) :=
    sup_le (hA'Y.trans hYN) (Subgroup.zpowers_le.mpr (hKN (hDK hyD)))
  have := le_two_of_elemAbelian h.fsu.qtke.2.2 (SecA.IsVi.ne_bot h hV₁ le_rfl)
    (h.fsu.sylow.1.to_le hV₁T) Nat.prime_three (by norm_num) hle hF3 hcard
  omega

omit [Finite G] in
theorem not_three_dvd_of_even {m : ℕ} (h1 : Nat.Coprime m (2 ^ n - 1)) (hn : Even n) :
    ¬ 3 ∣ m := by
  intro h3
  obtain ⟨k, rfl⟩ := hn
  have h4 : 3 ∣ 2 ^ (k + k) - 1 := by
    have := Nat.sub_dvd_pow_sub_pow 4 1 k
    rw [one_pow] at this
    have e : 2 ^ (k + k) = 4 ^ k := by rw [← two_mul, pow_mul]; norm_num
    rw [e]
    exact this
  have := (Nat.Coprime.coprime_dvd_left h3 h1).eq_one_of_dvd h4
  omega

end CFSG.Quasithin.Vol2.Ch11.SecD
