module

public import CFSG.Quasithin.Vol2.E2Eleven
public import CFSG.Quasithin.Vol2.E2NineMembers
public import CFSG.Quasithin.Vol2.Ch3E213MFam
public import CFSG.Quasithin.Vol2.Ch3E213MShare

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2

theorem false_of_odd_dvd_two_pow {d n : ℕ} (hd : Odd d) (hd1 : 1 < d) (h : d ∣ 2 ^ n) : False := by
  have hcop : Nat.Coprime d (2 ^ n) := Nat.Coprime.pow_right n (Nat.coprime_two_right.2 hd)
  have := Nat.Coprime.eq_one_of_dvd hcop h
  omega

theorem isEmpty_perm_six_of_isDihL2Sz {X : Type} [Group X] (h : ASInputs.IsDihL2Sz X) :
    IsEmpty (X ≃* Equiv.Perm (Fin 6)) := by
  refine ⟨fun e => ?_⟩
  rcases h with ⟨m, hm, -, ⟨d⟩⟩ | ⟨k, hP⟩ | ⟨k, hS⟩
  · have h1 := Nat.card_congr (e.symm.trans d).toEquiv
    rw [DihedralGroup.nat_card, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      at h1
    have h720 : Nat.factorial 6 = 720 := by decide
    rw [h720] at h1
    have h360 : m = 360 := by omega
    rw [h360] at hm
    exact absurd hm (by decide)
  · have := isSimpleGroup_of_psl_or_sz (Or.inl hP)
    exact not_isSimpleGroup_perm_six (MulEquiv.isSimpleGroup e.symm)
  · have := isSimpleGroup_of_psl_or_sz (Or.inr hS)
    exact not_isSimpleGroup_perm_six (MulEquiv.isSimpleGroup e.symm)

theorem two_le_of_isPSL {X : Type} [Group X] {k : ℕ} (hP : IsPSL 2 2 k X) : 2 ≤ k := by
  obtain ⟨⟨-, hk1, -, h22, -⟩, -⟩ := hP
  rcases Nat.lt_or_ge k 2 with h | h
  · have hk : k = 1 := by omega
    subst hk
    exact absurd rfl h22
  · exact h

theorem card_of_isSz {X : Type} [Group X] {k : ℕ} (hS : IsSz k X) :
    3 ≤ k ∧ Nat.card X = (2 ^ k) ^ 2 * (((2 ^ k) ^ 2 + 1) * (2 ^ k - 1)) := by
  obtain ⟨-, a, ha, K, _, _, hf, hK, ⟨e⟩⟩ := hS
  subst hf
  refine ⟨by omega, ?_⟩
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK]
  ring

theorem not_isPGroup_of_isDihL2Sz {X : Type} [Group X] [Finite X]
    (h : ASInputs.IsDihL2Sz X) : ¬ IsPGroup 2 X := by
  intro hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hX
  rcases h with ⟨m, hm, hm1, ⟨d⟩⟩ | ⟨k, hP⟩ | ⟨k, hS⟩
  · rw [Nat.card_congr d.toEquiv, DihedralGroup.nat_card] at hn
    exact false_of_odd_dvd_two_pow hm hm1 ⟨2, by rw [← hn, mul_comm]⟩
  · obtain ⟨k', _, _, hk', ⟨θ⟩⟩ := Ch3E213M.exists_equiv_projectiveSL_of_isPSL hP
    rw [Nat.card_congr θ.toEquiv, Ch3E213M.card_projectiveSL_two_pow hk'] at hn
    have hk1 := two_le_of_isPSL hP
    have hq : (2 ^ k) ^ 2 = 2 ^ (2 * k) := by rw [← pow_mul, mul_comm]
    refine false_of_odd_dvd_two_pow (d := (2 ^ k) ^ 2 - 1) ?_ ?_ ⟨2 ^ k, by rw [← hn, mul_comm]⟩
    · rw [hq]
      exact Ch3E213M.odd_two_pow_sub_one (by omega)
    · have : 4 ≤ (2 ^ k) ^ 2 := by
        rw [hq]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (2 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  · obtain ⟨hk3, hc⟩ := card_of_isSz hS
    rw [hc] at hn
    have hq : (2 ^ k) ^ 2 = 2 ^ (2 * k) := by rw [← pow_mul, mul_comm]
    refine false_of_odd_dvd_two_pow (d := (2 ^ k) ^ 2 + 1) ?_ ?_
      ⟨(2 ^ k) ^ 2 * (2 ^ k - 1), by rw [← hn]; ring⟩
    · rw [hq]
      exact (Nat.even_pow.2 ⟨even_two, by omega⟩).add_one
    · have : 1 ≤ (2 ^ k) ^ 2 := Nat.one_le_pow _ _ (by positivity)
      omega

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem relIndex_kerIn_eq_card (M X : Subgroup G) :
    (kerIn M X).relIndex X = Nat.card (StarQuot M X) := rfl

theorem exists_orderOf_nine_of_star {M X : Subgroup G} {c : StarQuot M X} (hc : orderOf c = 9) :
    ∃ x ∈ X, orderOf x = 9 := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
  have hdvd : 9 ∣ orderOf y := hc ▸ orderOf_map_dvd (QuotientGroup.mk' _) y
  have hz : orderOf (y ^ (orderOf y / 9)) = 9 := orderOf_pow_orderOf_div (orderOf_pos y).ne' hdvd
  exact ⟨((y ^ (orderOf y / 9) : ↥X) : G), (y ^ (orderOf y / 9)).2,
    by rw [Subgroup.orderOf_coe, hz]⟩

namespace Pair

variable {X T M V : Subgroup G} {g : G}

theorem relIndex_le_of_isDihL2Sz (h : Pair X T M V g)
    (hchar : CharTwo X) (hD : ASInputs.IsDihL2Sz (StarQuot M X)) :
    (kerIn M X ⊓ V).relIndex V ≤ (V ⊓ conjSub g V).relIndex (kerIn M X ⊓ V) := by
  rcases hD with ⟨m, hm, hm1, ⟨d⟩⟩ | ⟨k, hP⟩ | ⟨k, hS⟩
  · have hc : (kerIn M X).relIndex X = 2 ^ 1 * m := by
      rw [relIndex_kerIn_eq_card, Nat.card_congr d.toEquiv, DihedralGroup.nat_card, pow_one]
    have hV2 := Ch3E213M.relIndex_le_two_pow h hm hc
    have hp := Nat.minFac_prime (show m ≠ 1 by omega)
    have hpm : Nat.minFac m ∣ m := Nat.minFac_dvd m
    have hp2 : Nat.minFac m ≠ 2 := fun h2 => by
      rw [h2] at hpm
      exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr hpm)
    refine Ch3E213M.relIndex_le_of_prime h hchar hp hp2 ?_ (by simpa using hV2)
    exact (hpm.trans (Dvd.intro_left _ hc.symm)).trans (Subgroup.relIndex_dvd_card _ _)
  · obtain ⟨k', _, _, hk', ⟨θ⟩⟩ := Ch3E213M.exists_equiv_projectiveSL_of_isPSL hP
    have hc : (kerIn M X).relIndex X = 2 ^ k * ((2 ^ k) ^ 2 - 1) := by
      rw [relIndex_kerIn_eq_card, Nat.card_congr θ.toEquiv,
        Ch3E213M.card_projectiveSL_two_pow hk']
    have hk2 := two_le_of_isPSL hP
    refine Ch3E213M.relIndex_le_of_psl2 h hchar hk2 hc fun hk3 => ?_
    subst hk3
    obtain ⟨c, hc9⟩ := Ch3E213M.exists_orderOf_nine_projectiveSL hk'
    exact exists_orderOf_nine_of_star (c := θ.symm c) (by rw [MulEquiv.orderOf_eq, hc9])
  · obtain ⟨hk3, hc⟩ := card_of_isSz hS
    exact Ch3E213M.relIndex_le_of_sz h hchar hk3 (by rw [relIndex_kerIn_eq_card, hc])

end Pair

end E2

theorem ASInputs.e2_13_I_of_isDihL2Sz
    (hKG1 : E2.KGSz8CoverInvolutions) (hKG3 : E2.KGI22One)
    {G : Type} [Group G] [Finite G] {H T M V I : Subgroup G} {g : G} (h : E2.Hyp28 H T M V)
    (hchar : CharTwo H) (hI : ASInputs.IsInIHTVC H T M V I) (hg : g ∈ I)
    (hgen : I = V ⊔ B6.conjSub g V) (hD : ASInputs.IsDihL2Sz (E2.StarQuot (M ⊓ I) I)) :
    (B6.conjSub g V ⊓ pCoreOf 2 I = B6.conjSub g V ⊓ Subgroup.normalizer (V : Set G) ∧
      ⁅⁅⁅V, B6.conjSub g V ⊓ pCoreOf 2 I⁆, B6.conjSub g V ⊓ pCoreOf 2 I⁆,
        B6.conjSub g V ⊓ pCoreOf 2 I⁆ = ⊥ ∧
      ¬ B6.conjSub g V ⊓ pCoreOf 2 I ≤ Subgroup.centralizer (V : Set G) ∧
      B6.conjSub g V ⊓ pCoreOf 2 I ⊓ Subgroup.centralizer (V : Set G) = V ⊓ B6.conjSub g V) ∧
    (V ⊓ B6.conjSub g V = ⊥ → qOf (autI h.elem H) ≤ ((1 : ℚ) : WithTop ℚ)) ∧
    (∀ x ∈ I, (∀ y ∈ (V ⊓ pCoreOf 2 I) ⊔ (B6.conjSub g V ⊓ pCoreOf 2 I),
        x * y * x⁻¹ * y⁻¹ ∈ V ⊓ B6.conjSub g V) → x ∈ pCoreOf 2 I) ∧
      pCoreOf 2 I = kerIn (M ⊓ I) I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS6 := E2.isEmpty_perm_six_of_isDihL2Sz hD
  obtain ⟨hp, -, -, h4, hJ, -, h5c, -⟩ :=
    ASInputs.e2_11C_of_not_S6 hKG1 hKG3 h (ASInputs.isInIHTVNoRoot_of_isInIHTVC hI) hS6 hg hgen
  have hcharI : CharTwo I := (ASInputs.e2_9C_members h hI).2 hchar
  have hIV : I ≠ V := by
    intro hIV
    have hV2 : IsPGroup 2 ↥V := B6.isPGroup_of_isElemAbelian h.elem
    rw [← hIV] at hV2
    exact E2.not_isPGroup_of_isDihL2Sz hD (hV2.to_quotient _)
  obtain ⟨-, -, hAel, hcub, hnc, hCA⟩ := Ch3n.exists_cubic_of_pair hp hcharI hIV
  have hAeq := hp.conjSub_kerIn_inf_eq
  rw [hAeq] at hAel hcub hnc hCA
  set A := B6.conjSub g V ⊓ pCoreOf 2 I with hAdef
  set B := V ⊓ pCoreOf 2 I with hBdef
  have hBk : kerIn (M ⊓ I) I ⊓ V = B := hp.kerIn_inf_eq
  refine ⟨⟨h4, hcub, hnc, hCA⟩, ?_, ?_, hJ⟩
  ·
    intro hZ
    have hss := hp.relIndex_le_of_isDihL2Sz hcharI hD
    rw [hBk, hZ, Subgroup.relIndex_bot_left] at hss
    have hAN : A ≤ Subgroup.normalizer (V : Set G) := h4 ▸ inf_le_right
    have hAH : A ≤ H := (inf_le_right.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 I)).trans hI.1
    have hcardA : Nat.card A = Nat.card B := by
      rw [← hAeq, hBk]
      exact (Nat.card_congr ((MulAut.conj g).subgroupMap B).toEquiv).symm
    have hCA1 : A ⊓ Subgroup.centralizer (V : Set G) = ⊥ := hCA.trans hZ
    have hBC : B ≤ V ⊓ Subgroup.centralizer (A : Set G) := by
      refine fun b hb => ⟨hb.1, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
      have hb' : b ∈ kerIn (M ⊓ I) I ⊓ V := hBk ▸ hb
      have ha' : a ∈ B6.conjSub g (kerIn (M ⊓ I) I ⊓ V) := hAeq ▸ ha
      have hc := hp.commutator_B_A hb' ha'
      rw [hZ, Subgroup.mem_bot] at hc
      have : b * a = a * b := by
        calc b * a = (b * a * b⁻¹ * a⁻¹) * (a * b) := by group
          _ = a * b := by rw [hc, one_mul]
      exact this.symm
    have hFF : IsFFModule (autI h.elem H) := by
      refine ⟨autI h.elem A, autI_mono h.elem hAH, ?_, ?_, ?_⟩
      · exact fun hb => hnc ((autI_eq_bot_iff h.elem hAN).1 hb)
      · exact isElemAbelian2_autI h.elem hAel hAN
      · have h1 := card_autI_mul_card_inf h.elem hAN
        rw [hCA1, Subgroup.card_bot, mul_one] at h1
        rw [card_fixV_autI h.elem hAN, h1, hcardA]
        have h2 := Subgroup.relIndex_mul_card B V
        rw [inf_eq_left.2 (inf_le_left : B ≤ V)] at h2
        calc Nat.card (IntMod V h.elem) = Nat.card V := rfl
          _ = B.relIndex V * Nat.card B := h2.symm
          _ ≤ Nat.card B * Nat.card B := Nat.mul_le_mul_right _ hss
          _ ≤ Nat.card B * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) :=
            Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hBC)
    have hq := (B1_4_5 (fun v => IntMod.sq_eq_one v) (autI h.elem H)).out 1 3
    rw [WithTop.coe_one]
    exact hq.mp hFF
  ·
    have hZc : ∀ z ∈ V ⊓ B6.conjSub g V, ∀ i ∈ I, i * z * i⁻¹ = z := fun z hz i hi => by
      rw [← hp.mem_center hz hi]
      group
    have hPeq : (kerIn (M ⊓ I) I ⊓ V) ⊔ B6.conjSub g (kerIn (M ⊓ I) I ⊓ V) = B ⊔ A := by
      rw [hAeq, hBk]
    have hPn : I ≤ Subgroup.normalizer ((B ⊔ A : Subgroup G) : Set G) := hPeq ▸ hp.le_normalizer_P
    have hP2 : IsPGroup 2 ↥(B ⊔ A) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I).to_le (hPeq ▸ hp.P_le_pCoreOf)
    let Y : Subgroup G :=
      { carrier := {x | x ∈ I ∧ ∀ y ∈ B ⊔ A, x * y * x⁻¹ * y⁻¹ ∈ V ⊓ B6.conjSub g V}
        mul_mem' := by
          rintro x x' ⟨hx, hxP⟩ ⟨hx', hx'P⟩
          refine ⟨I.mul_mem hx hx', fun y hy => ?_⟩
          have h1 := hx'P y hy
          have e : x * x' * y * (x * x')⁻¹ * y⁻¹ =
              (x * (x' * y * x'⁻¹ * y⁻¹) * x⁻¹) * (x * y * x⁻¹ * y⁻¹) := by group
          rw [e, hZc _ h1 x hx]
          exact Subgroup.mul_mem _ h1 (hxP y hy)
        one_mem' := ⟨I.one_mem, fun y _ => by simp⟩
        inv_mem' := by
          rintro x ⟨hx, hxP⟩
          refine ⟨I.inv_mem hx, fun y hy => ?_⟩
          have hy' : x⁻¹ * y * x⁻¹⁻¹ ∈ B ⊔ A :=
            (Subgroup.mem_normalizer_iff.mp (hPn (I.inv_mem hx)) y).mp hy
          have h1 := hxP _ hy'
          have e : x * (x⁻¹ * y * x⁻¹⁻¹) * x⁻¹ * (x⁻¹ * y * x⁻¹⁻¹)⁻¹ =
              (x⁻¹ * y * x⁻¹⁻¹ * y⁻¹)⁻¹ := by group
          rw [e] at h1
          simpa using Subgroup.inv_mem _ h1 }
    have hY2 : ∀ x ∈ Y, ∃ n : ℕ, x ^ 2 ^ n = 1 := by
      rintro x ⟨hx, hxP⟩
      have hx2C : x ^ 2 ∈ Subgroup.centralizer ((B ⊔ A : Subgroup G) : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hz := hxP y hy
        have hz2 : (x * y * x⁻¹ * y⁻¹) * (x * y * x⁻¹ * y⁻¹) = 1 := by
          rw [← pow_two]
          exact h.elem.2 _ hz.1
        have hxy : x * y * x⁻¹ = (x * y * x⁻¹ * y⁻¹) * y := by group
        have key : x ^ 2 * y * (x ^ 2)⁻¹ = y := by
          rw [pow_two]
          calc x * x * y * (x * x)⁻¹ = x * (x * y * x⁻¹) * x⁻¹ := by group
            _ = x * ((x * y * x⁻¹ * y⁻¹) * y) * x⁻¹ := by rw [← hxy]
            _ = (x * (x * y * x⁻¹ * y⁻¹) * x⁻¹) * (x * y * x⁻¹) := by group
            _ = (x * y * x⁻¹ * y⁻¹) * ((x * y * x⁻¹ * y⁻¹) * y) := by
              rw [hZc _ hz x hx, ← hxy]
            _ = y := by rw [← mul_assoc, hz2, one_mul]
        calc y * x ^ 2 = (x ^ 2 * y * (x ^ 2)⁻¹) * x ^ 2 := by rw [key]
          _ = x ^ 2 * y := by group
      have hd : ∀ q ∈ pCoreOf 2 I, x ^ 2 * q * (x ^ 2)⁻¹ * q⁻¹ ∈ B ⊔ A := by
        intro q hq
        have hqI : q ∈ I := CFSG.LieType.BorelTits.pCoreOf_le 2 I hq
        have h1 := (h5c q hqI).mpr hq (x ^ 2) (I.pow_mem hx 2)
        rw [inf_comm (pCoreOf 2 I) V, inf_comm (pCoreOf 2 I) (B6.conjSub g V)] at h1
        have e : x ^ 2 * q * (x ^ 2)⁻¹ * q⁻¹ = (q * x ^ 2 * q⁻¹ * (x ^ 2)⁻¹)⁻¹ := by group
        rw [e]
        exact Subgroup.inv_mem _ h1
      obtain ⟨n, hn⟩ :=
        E2.exists_pow_two_pow_eq_one_of_stable hPn hP2 hcharI (I.pow_mem hx 2) hx2C hd
      exact ⟨n + 1, by rw [pow_succ', pow_mul]; exact hn⟩
    have hYI : Y ≤ I := fun x hx => hx.1
    have hYp : IsPGroup 2 ↥Y := fun x => by
      obtain ⟨n, hn⟩ := hY2 x x.2
      exact ⟨n, Subtype.ext (by simpa using hn)⟩
    have hYn : I ≤ Subgroup.normalizer (Y : Set G) := by
      intro i hi
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨hx, hxP⟩
        refine ⟨I.mul_mem (I.mul_mem hi hx) (I.inv_mem hi), fun y hy => ?_⟩
        have hy' : i⁻¹ * y * i⁻¹⁻¹ ∈ B ⊔ A :=
          (Subgroup.mem_normalizer_iff.mp (hPn (I.inv_mem hi)) y).mp hy
        have h1 := hxP _ hy'
        have e : i * x * i⁻¹ * y * (i * x * i⁻¹)⁻¹ * y⁻¹ =
            i * (x * (i⁻¹ * y * i⁻¹⁻¹) * x⁻¹ * (i⁻¹ * y * i⁻¹⁻¹)⁻¹) * i⁻¹ := by group
        rw [e, hZc _ h1 i hi]
        exact h1
      · rintro ⟨hx, hxP⟩
        have hxI : x ∈ I := by
          have := I.mul_mem (I.mul_mem (I.inv_mem hi) hx) hi
          simpa [mul_assoc] using this
        refine ⟨hxI, fun y hy => ?_⟩
        have hy' : i * y * i⁻¹ ∈ B ⊔ A := (Subgroup.mem_normalizer_iff.mp (hPn hi) y).mp hy
        have h1 := hxP _ hy'
        have e : i * x * i⁻¹ * (i * y * i⁻¹) * (i * x * i⁻¹)⁻¹ * (i * y * i⁻¹)⁻¹ =
            i * (x * y * x⁻¹ * y⁻¹) * i⁻¹ := by group
        rw [e] at h1
        have h2 := hZc _ h1 i⁻¹ (I.inv_mem hi)
        have e2 : i⁻¹ * (i * (x * y * x⁻¹ * y⁻¹) * i⁻¹) * i⁻¹⁻¹ = x * y * x⁻¹ * y⁻¹ := by group
        rw [e2] at h2
        rw [h2]
        exact h1
    intro x hxI hxP
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hYI hYn hYp ⟨hxI, hxP⟩

@[expose] def ASInputs.AS_E_2_13_six : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V I : Subgroup G), E2.Hyp28 H T M V → CharTwo H →
    ASInputs.IsInIHTVC H T M V I →
    (∀ i ∈ I, B6.conjSub i V ≤ T → B6.conjSub i V ≤ Subgroup.centralizer (V : Set G)) →
      ∀ k : ℕ, ¬ ASInputs.IsSp4C k (E2.StarQuot (M ⊓ I) I)

theorem ASInputs.as_E_2_13_I_of
    (hKG1 : E2.KGSz8CoverInvolutions) (hKG3 : E2.KGI22One)
    (h6 : ASInputs.AS_E_2_13_six) : ASInputs.AS_E_2_13_I := by
  intro G _ _ H T M V I g h hchar hI hg hgen
  exact ⟨h6 G H T M V I h hchar hI,
    fun hD => ASInputs.e2_13_I_of_isDihL2Sz hKG1 hKG3 h hchar hI hg hgen hD⟩

end CFSG.Quasithin
