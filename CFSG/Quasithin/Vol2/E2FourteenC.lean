module

public import CFSG.Quasithin.Vol2.E2FourteenB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2

namespace Pair

variable {G : Type} [Group G] [Finite G] {X T M V : Subgroup G} {g : G}

theorem exists_two_pow_le_relIndex_P (h : Pair X T M V g) (hchar : CharTwo X) {c : G}
    (hcX : c ∈ X) {ℓ a : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hc : orderOf c = ℓ ^ (a + 1)) :
    ∃ m : ℕ, 0 < m ∧ ℓ ^ (a + 1) ∣ 2 ^ m - 1 ∧
      2 ^ m ≤ (V ⊓ conjSub g V).relIndex ((kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := (kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V) with hP
  set Z := V ⊓ conjSub g V with hZ
  have hXP : X ≤ Subgroup.normalizer (P : Set G) := h.le_normalizer_P
  have hP2 : IsPGroup 2 P := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).to_le h.P_le_pCoreOf
  have hZP : Z ≤ P := h.inf_conj_le_P
  obtain ⟨d, hd⟩ := IsPGroup.iff_card.mp hP2
  set c' : Subgroup.normalizer (P : Set G) := ⟨c, hXP hcX⟩ with hc'
  have hc'ord : orderOf c' = ℓ ^ (a + 1) := by rw [hc', Subgroup.orderOf_mk, hc]
  have hc0X : c ^ ℓ ^ a ∈ X := X.pow_mem hcX _
  have hcoe : ((c' ^ ℓ ^ a : Subgroup.normalizer (P : Set G)) : G) = c ^ ℓ ^ a := by
    rw [Subgroup.coe_pow]
  have hne : P.normalizerMonoidHom (c' ^ ℓ ^ a) ≠ 1 := by
    intro h1
    have hc0C : c ^ ℓ ^ a ∈ Subgroup.centralizer (P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have h2 := congrArg Subtype.val (DFunLike.congr_fun h1 ⟨p, hp⟩)
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hcoe, MulAut.one_apply] at h2
      calc p * c ^ ℓ ^ a = (c ^ ℓ ^ a * p * (c ^ ℓ ^ a)⁻¹) * c ^ ℓ ^ a := by rw [h2]
        _ = c ^ ℓ ^ a * p := by group
    obtain ⟨n, hn⟩ := exists_pow_two_pow_eq_one_of_stable hXP hP2 hchar hc0X hc0C
      (fun q hq => h.commutator_mem_P_of_mem_pCoreOf hc0X hq)
    have hord : orderOf (c ^ ℓ ^ a) = ℓ := by
      rw [orderOf_pow_of_dvd (pow_ne_zero _ hℓ.ne_zero) (hc ▸ pow_dvd_pow ℓ (Nat.le_succ a)), hc,
        pow_succ, Nat.mul_div_cancel_left _ (pow_pos hℓ.pos _)]
    have hodd : Odd (orderOf (c ^ ℓ ^ a)) := by
      rw [hord]
      exact hℓ.odd_of_ne_two hℓ2
    have h1' := eq_one_of_two_pow_of_odd hn hodd
    rw [h1', orderOf_one] at hord
    exact hℓ.one_lt.ne hord
  have hfixZ : ∀ z ∈ Z.subgroupOf P, P.normalizerMonoidHom (c' ^ ℓ ^ a) z = z := by
    intro z hz
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hcoe]
    have hzc := h.mem_center (Subgroup.mem_subgroupOf.mp hz) hc0X
    rw [← hzc]
    group
  obtain ⟨m, hm0, hmZ, hmdvd⟩ :=
    Ch3E213M.exists_two_pow_of_orderOf P.normalizerMonoidHom hd hℓ hℓ2 hc'ord hne
      (Z.subgroupOf P) hfixZ
  have hZcard : Nat.card (Z.subgroupOf P) = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv
  have hPZ : Z.relIndex P * Nat.card Z = Nat.card P := by
    have h1 := Subgroup.relIndex_mul_card Z P
    rwa [inf_eq_left.2 hZP] at h1
  refine ⟨m, hm0, hmdvd, ?_⟩
  rw [hZcard, ← hd, ← hPZ] at hmZ
  exact Nat.le_of_mul_le_mul_right hmZ Nat.card_pos

end Pair

end E2

theorem ASInputs.e2_14_orders
    (hKG1 : E2.KGSz8CoverInvolutions) (hKG3 : E2.KGI22One)
    {G : Type} [Group G] [Finite G] {H T M V I : Subgroup G} {g : G} (h : E2.Hyp28 H T M V)
    (hchar : CharTwo H) (hTI : IsTISetIn V M) (hI : ASInputs.IsInIHTVC H T M V I) (hg : g ∈ I)
    (hgen : I = V ⊔ B6.conjSub g V) (hZ : V ⊓ B6.conjSub g V ≠ ⊥) {k : ℕ} (hk : 2 ≤ k)
    (hY : IsPSL 2 2 k (E2.StarQuot (M ⊓ I) I) ∨ IsSz k (E2.StarQuot (M ⊓ I) I)) :
    Nat.card (autI h.elem (ASInputs.e214A V I g)) =
        (V ⊓ B6.conjSub g V).relIndex (V ⊓ pCoreOf 2 I) ∧
      (V ⊓ B6.conjSub g V).relIndex V =
        2 ^ k * (V ⊓ B6.conjSub g V).relIndex (V ⊓ pCoreOf 2 I) ∧
      2 ^ k ≤ (V ⊓ B6.conjSub g V).relIndex (V ⊓ pCoreOf 2 I) ∧
      (IsPSL 2 2 k (E2.StarQuot (M ⊓ I) I) → ∃ s : ℕ,
        (V ⊓ B6.conjSub g V).relIndex (V ⊓ pCoreOf 2 I) = (2 ^ k) ^ s ∧
          (s = 1 → qOf (autI h.elem I) ≤ ((1 : ℚ) : WithTop ℚ))) ∧
      (IsSz k (E2.StarQuot (M ⊓ I) I) →
        2 ^ (2 * k) ≤ (V ⊓ B6.conjSub g V).relIndex (V ⊓ pCoreOf 2 I)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := E2P.finite_starQuot (M ⊓ I) I
  have hD : ASInputs.IsDihL2Sz (E2.StarQuot (M ⊓ I) I) :=
    hY.elim (fun hP => Or.inr (Or.inl ⟨k, hP⟩)) fun hS => Or.inr (Or.inr ⟨k, hS⟩)
  have hS6 := E2.isEmpty_perm_six_of_isDihL2Sz hD
  obtain ⟨hp, -, -, h4, hJ, -⟩ :=
    ASInputs.e2_11C_of_not_S6 hKG1 hKG3 h (ASInputs.isInIHTVNoRoot_of_isInIHTVC hI) hS6 hg hgen
  have hcharI : CharTwo I := (ASInputs.e2_9C_members h hI).2 hchar
  have hIV : I ≠ V := by
    intro hIV
    have hV2 : IsPGroup 2 ↥V := B6.isPGroup_of_isElemAbelian h.elem
    rw [← hIV] at hV2
    exact E2.not_isPGroup_of_isDihL2Sz hD (hV2.to_quotient _)
  obtain ⟨-, -, hAel, -, hnc, hCA⟩ := Ch3n.exists_cubic_of_pair hp hcharI hIV
  have hAeq := hp.conjSub_kerIn_inf_eq
  rw [hAeq] at hAel hnc hCA
  obtain ⟨h1, ⟨hP2, hVeq⟩, -⟩ := ASInputs.e2_14_one_two_six hKG1 hKG3 h hTI hI hg hgen hZ hD
  have hsyl := hI.2.2.1
  have hTMI : T ⊓ I ≤ M ⊓ I := inf_le_inf_right I h.minParabolic.le
  have hMN : M ⊓ I ≤ Subgroup.normalizer (V : Set G) := h1.le.trans inf_le_right
  set A := B6.conjSub g V ⊓ pCoreOf 2 I with hAdef
  set B := V ⊓ pCoreOf 2 I with hBdef
  set Z := V ⊓ B6.conjSub g V with hZdef
  have hBk : kerIn (M ⊓ I) I ⊓ V = B := hp.kerIn_inf_eq
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := h4 ▸ inf_le_right
  have hZB : Z ≤ B := le_inf inf_le_left hp.inf_conj_le_pCoreOf
  have hconjB : B6.conjSub g B = A := by rw [← hBk, hAeq]
  have hconjZ : B6.conjSub g Z = Z := hp.conjSub_inf_conj hg
  have hrelAB : Z.relIndex A = Z.relIndex B := by
    rw [← hconjB]
    conv_lhs => rw [← hconjZ]
    show (Z.map (MulAut.conj g).toMonoidHom).relIndex (B.map (MulAut.conj g).toMonoidHom) = _
    exact Subgroup.relIndex_map_map_of_injective _ _ fun x y hxy => (MulAut.conj g).injective hxy
  have hcardA : Nat.card (autI h.elem A) = Z.relIndex B := by
    rw [card_autI_eq h.elem hAN, hCA, hrelAB]
  have hS := E2.isSylowTwoOf_star_inf (M := M) hsyl
  obtain ⟨hcZ, -⟩ := E2.exists_conj_of_mem_center hk hY hS
  have hVB : B.relIndex V = 2 ^ k := by
    rw [← hBk, ← E2.card_star_of_le hp.V_le, hVeq]
    exact hcZ
  have hVZ : Z.relIndex V = 2 ^ k * Z.relIndex B := by
    rw [← Subgroup.relIndex_mul_relIndex Z B V hZB inf_le_left, hVB, mul_comm]
  have hss : 2 ^ k ≤ Z.relIndex B := by
    have h2 := hp.relIndex_le_of_isDihL2Sz hcharI hD
    rw [hBk, hVB] at h2
    exact h2
  refine ⟨hcardA, hVZ, hss, fun hP => ?_, fun hSz => ?_⟩
  ·
    have hPeq : ASInputs.e214P V I g = E2.Pair.PP (M ⊓ I) V I g := by
      show B6.conjSub g V ⊓ pCoreOf 2 I ⊔ V ⊓ pCoreOf 2 I =
        (kerIn (M ⊓ I) I ⊓ V) ⊔ B6.conjSub g (kerIn (M ⊓ I) I ⊓ V)
      rw [hp.conjSub_kerIn_inf_eq, hp.kerIn_inf_eq, sup_comm]
    have hPJ : E2.Pair.PP (M ⊓ I) V I g = kerIn (M ⊓ I) I := by
      rw [← hPeq]
      exact hP2.resolve_right (E2.not_isSz_three_of_isPSL hP)
    have hBor := E2.star_eq_normalizer_of_isBorelIn hTMI hsyl
      (ASInputs.isBorelIn_star_of_psl_or_sz hI hk (Or.inl hP))
    obtain ⟨s, hrel, -, hs1⟩ := E2.exists_natural_of_psl hp hsyl hg hgen hMN hJ hPJ hBor hVeq hk hP
    rw [hBk] at hrel
    refine ⟨s, hrel, fun hs => ?_⟩
    have hP1 := hs1 hs
    have hBP : B ≤ E2.Pair.PP (M ⊓ I) V I g := hBk ▸ le_sup_left
    have hAP : A ≤ E2.Pair.PP (M ⊓ I) V I g := hAeq ▸ le_sup_right
    have hBC : B ≤ V ⊓ Subgroup.centralizer (A : Set G) := by
      refine fun b hb => ⟨hb.1, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
      have e1 : a * b * (a * b) = 1 := by
        rw [← pow_two]
        exact hP1 _ ((E2.Pair.PP (M ⊓ I) V I g).mul_mem (hAP ha) (hBP hb))
      have e2 : a * a = 1 := by
        rw [← pow_two]
        exact hP1 a (hAP ha)
      have e3 : b * b = 1 := by
        rw [← pow_two]
        exact hP1 b (hBP hb)
      calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right e1).symm
        _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
        _ = b * a := by rw [inv_eq_of_mul_eq_one_right e2, inv_eq_of_mul_eq_one_right e3]
    have hAI : A ≤ I := inf_le_right.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 I)
    have hFF : IsFFModule (autI h.elem I) := by
      refine ⟨autI h.elem A, autI_mono h.elem hAI, ?_, ?_, ?_⟩
      · exact fun hb => hnc ((autI_eq_bot_iff h.elem hAN).1 hb)
      · exact isElemAbelian2_autI h.elem hAel hAN
      · rw [card_fixV_autI h.elem hAN, hcardA, hrel, hs, pow_one]
        have h2 := Subgroup.relIndex_mul_card B V
        rw [inf_eq_left.2 (inf_le_left : B ≤ V), hVB] at h2
        calc Nat.card (IntMod V h.elem) = Nat.card V := rfl
          _ = 2 ^ k * Nat.card B := h2.symm
          _ ≤ 2 ^ k * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) :=
            Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hBC)
    have hq := (B1_4_5 (fun v => IntMod.sq_eq_one v) (autI h.elem I)).out 1 3
    rw [WithTop.coe_one]
    exact hq.mp hFF
  ·
    obtain ⟨hk3, hcard⟩ := E2.card_of_isSz hSz
    obtain ⟨r, hr⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 4 * k) (by omega)
      (by omega)
    have : Fact r.Prime := ⟨hr.prime⟩
    have hrX : r ∣ Nat.card I := by
      have hc : (kerIn (M ⊓ I) I).relIndex I = (2 ^ k) ^ 2 * (((2 ^ k) ^ 2 + 1) * (2 ^ k - 1)) :=
        by rw [E2.relIndex_kerIn_eq_card, hcard]
      exact (((Ch3E213M.primitive_dvd_sq_add_one (by omega) hr).trans (Dvd.intro _ rfl)).trans
        (Dvd.intro_left _ hc.symm)).trans (Subgroup.relIndex_dvd_card _ _)
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' r hrX
    obtain ⟨m, hm0, hmdvd, hmP⟩ := hp.exists_two_pow_le_relIndex_P hcharI c.2 (a := 0) hr.prime
      (hr.ne_two (by omega)) (by rw [pow_one, Subgroup.orderOf_coe, hc])
    rw [zero_add, pow_one] at hmdvd
    have hkm : 4 * k ∣ m := (hr.dvd_sub_one_iff (by omega) m).1 hmdvd
    rw [Ch3E213M.relIndex_P_eq hp, hBk] at hmP
    have h5 : (2 ^ (2 * k)) ^ 2 ≤ (Z.relIndex B) ^ 2 := by
      calc (2 ^ (2 * k)) ^ 2 = 2 ^ (4 * k) := by rw [← pow_mul]; ring_nf
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (Nat.le_of_dvd hm0 hkm)
        _ ≤ (Z.relIndex B) ^ 2 := hmP
    exact (Nat.pow_le_pow_iff_left two_ne_zero).1 h5

theorem ASInputs.e2_14_seven_eight
    (hKG1 : E2.KGSz8CoverInvolutions) (hKG3 : E2.KGI22One)
    {G : Type} [Group G] [Finite G] {H T M V I : Subgroup G} {g : G} (h : E2.Hyp28 H T M V)
    (hchar : CharTwo H) (hTI : IsTISetIn V M) (hI : ASInputs.IsInIHTVC H T M V I) (hg : g ∈ I)
    (hgen : I = V ⊔ B6.conjSub g V) (hZ : V ⊓ B6.conjSub g V ≠ ⊥) :
    (∀ k : ℕ, (IsPSL 2 2 k (E2.StarQuot (M ⊓ I) I) ∨ IsSz k (E2.StarQuot (M ⊓ I) I)) →
      Nat.card (autI h.elem (ASInputs.e214A V I g)) ≤ 2 ^ (2 * k) →
      ((1 : ℚ) : WithTop ℚ) < qOf (autI h.elem I) →
      Nat.card (autI h.elem (ASInputs.e214A V I g)) = 2 ^ (2 * k) ∧
        (V ⊓ B6.conjSub g V).relIndex V = 2 ^ (3 * k)) ∧
    (IsPSL 2 2 2 (E2.StarQuot (M ⊓ I) I) →
      Nat.card (autI h.elem (ASInputs.e214A V I g)) ≤ 2 ^ 6 →
      ((1 : ℚ) : WithTop ℚ) < qOf (autI h.elem I) →
      ∃ s : ℕ, (s = 2 ∨ s = 3) ∧ Nat.card (autI h.elem (ASInputs.e214A V I g)) = 2 ^ (2 * s) ∧
        (V ⊓ B6.conjSub g V).relIndex V = 2 ^ (2 * (s + 1))) := by
  have hs2 : ∀ k : ℕ, 2 ≤ k → IsPSL 2 2 k (E2.StarQuot (M ⊓ I) I) →
      ((1 : ℚ) : WithTop ℚ) < qOf (autI h.elem I) →
      ∃ s : ℕ, 2 ≤ s ∧ (V ⊓ B6.conjSub g V).relIndex (V ⊓ pCoreOf 2 I) = (2 ^ k) ^ s := by
    intro k hk hP hq
    obtain ⟨-, -, hss, hL, -⟩ :=
      ASInputs.e2_14_orders hKG1 hKG3 h hchar hTI hI hg hgen hZ hk (Or.inl hP)
    obtain ⟨s, hrel, hs1⟩ := hL hP
    refine ⟨s, ?_, hrel⟩
    rcases Nat.lt_or_ge s 2 with hs | hs
    · exfalso
      interval_cases s
      · rw [hrel, pow_zero] at hss
        have : 1 < 2 ^ k := Nat.one_lt_two_pow (by omega)
        omega
      · exact absurd (hs1 rfl) (not_le.mpr hq)
    · exact hs
  refine ⟨fun k hY hle hq => ?_, fun hP hle hq => ?_⟩
  · have hk : 2 ≤ k := by
      rcases hY with hP | hSz
      · exact E2.two_le_of_isPSL hP
      · have := (E2.card_of_isSz hSz).1
        omega
    obtain ⟨hcardA, hVZ, -, -, hSzb⟩ :=
      ASInputs.e2_14_orders hKG1 hKG3 h hchar hTI hI hg hgen hZ hk hY
    have hBZ : (V ⊓ B6.conjSub g V).relIndex (V ⊓ pCoreOf 2 I) = 2 ^ (2 * k) := by
      rcases hY with hP | hSz
      · obtain ⟨s, hs, hrel⟩ := hs2 k hk hP hq
        rw [hcardA, hrel, ← pow_mul] at hle
        have h1 : k * s ≤ 2 * k := (Nat.pow_le_pow_iff_right (by norm_num)).1 hle
        have hs' : s = 2 := by
          have : k * s ≤ k * 2 := by omega
          have := Nat.le_of_mul_le_mul_left this (by omega)
          omega
        rw [hrel, hs', ← pow_mul, mul_comm]
      · exact le_antisymm (hcardA ▸ hle) (hSzb hSz)
    refine ⟨hcardA.trans hBZ, ?_⟩
    rw [hVZ, hBZ, ← pow_add]
    ring_nf
  · obtain ⟨hcardA, hVZ, -, -, -⟩ :=
      ASInputs.e2_14_orders hKG1 hKG3 h hchar hTI hI hg hgen hZ le_rfl (Or.inl hP)
    obtain ⟨s, hs, hrel⟩ := hs2 2 le_rfl hP hq
    rw [hcardA, hrel, ← pow_mul] at hle
    have h1 : 2 * s ≤ 6 := (Nat.pow_le_pow_iff_right (by norm_num)).1 hle
    refine ⟨s, by omega, ?_, ?_⟩
    · rw [hcardA, hrel, ← pow_mul]
    · rw [hVZ, hrel, ← pow_mul, ← pow_add]
      ring_nf

end CFSG.Quasithin
