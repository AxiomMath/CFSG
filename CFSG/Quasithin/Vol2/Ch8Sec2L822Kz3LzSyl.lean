module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822R1

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.L319
open scoped commutatorElement

theorem card_eq_of_isSylowTwoOf_kz3 {G : Type} [Group G] [Finite G] {S H : Subgroup G}
    (h : IsSylowTwoOf S H) (hH : Nat.card ↥H = 443520) : Nat.card ↥S = 128 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSH, hS2, hodd⟩ := h
  have hcardS : Nat.card ↥(S.subgroupOf H) = Nat.card ↥S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSH).toEquiv
  have hmul := Subgroup.card_mul_index (S.subgroupOf H)
  rw [hcardS, hH] at hmul
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).mp hS2
  rw [ha]
  rw [ha] at hmul
  generalize (S.subgroupOf H).index = i at hmul hodd
  have ha19 : a < 19 := by
    by_contra hc
    have h1 : 2 ^ 19 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ a ≤ 443520 := by
      have : 2 ^ a ∣ 443520 := ⟨i, hmul.symm⟩
      exact Nat.le_of_dvd (by norm_num) this
    omega
  interval_cases a <;> norm_num at hmul ⊢ <;> omega

theorem card_inf_autOn_kz3 {G : Type} [Group G] [Finite G] {T L V : Subgroup G}
    (hT : quasithinIsSylowTwo T) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hA : Nat.card ↥(autOn L V) = 443520) :
    Nat.card ↥(autOn T V ⊓ autOn L V) = 128 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTsyl : IsSylowTwoOf T (L ⊔ T) := isSylowTwoOf_of_quasithinIsSylowTwo hT le_sup_right
  have hLn : (L.subgroupOf (L ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hTL)
  have hsyl : IsSylowTwoOf (T ⊓ L) L :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal hTsyl le_sup_left (Subgroup.Normal.isSubnormal hLn)
  have hAut : IsSylowTwoOf (autOn (T ⊓ L) V) (autOn L V) :=
    CFSG.Quasithin.AutOn.isSylowTwoOf_autOn hsyl hLV
  have hS128 : Nat.card ↥(autOn (T ⊓ L) V) = 128 := card_eq_of_isSylowTwoOf_kz3 hAut hA
  have hle1 : autOn (T ⊓ L) V ≤ autOn T V ⊓ autOn L V :=
    le_inf (CFSG.Quasithin.AutOn.autOn_mono inf_le_left) (CFSG.Quasithin.AutOn.autOn_mono inf_le_right)
  have hR2 : IsPGroup 2 ↥(autOn T V ⊓ autOn L V) :=
    IsPGroup.to_inf_left (CFSG.Quasithin.AutOn.isPGroup_autOn hT.1)
  have hdvd : Nat.card ↥(autOn T V ⊓ autOn L V) ∣ 443520 := by
    rw [← hA]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hge : 128 ≤ Nat.card ↥(autOn T V ⊓ autOn L V) := by
    rw [← hS128]
    exact Subgroup.card_le_of_le hle1
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hR2
  rw [hm] at hdvd hge ⊢
  have hm19 : m < 19 := by
    by_contra hc
    have h1 : 2 ^ 19 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ m ≤ 443520 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  interval_cases m <;> first | (norm_num at hge; done) | (norm_num at hdvd; done) | norm_num

theorem autOn_fix_kz3 {G : Type} [Group G] {T V : Subgroup G} {z : G}
    (hTz : T ≤ Subgroup.centralizer ({z} : Set G)) (hzV : z ∈ V) (r : MulAut ↥V)
    (hr : r ∈ autOn T V) : r ⟨z, hzV⟩ = ⟨z, hzV⟩ := by
  obtain ⟨n, hnT, rfl⟩ := CFSG.Quasithin.AutOn.mem_autOn_iff.mp hr
  apply Subtype.ext
  have hcomm : (n : G) * z = z * (n : G) := Subgroup.mem_centralizer_singleton_iff.mp (hTz hnT)
  have key : ((conjAct V n) ⟨z, hzV⟩ : G) = (n : G) * z * (n : G)⁻¹ := by
    simp [conjAct, Subgroup.normalizerMonoidHom_apply_apply_coe]
  rw [key, hcomm]
  group

theorem card_comap_kz3 {Q A : Type} [Group Q] [Finite Q] [Group A] [Finite A] (ψ : Q →* A)
    (hψ : Function.Surjective ψ) (K : Subgroup A) :
    Nat.card ↥(K.comap ψ) = Nat.card ↥ψ.ker * Nat.card ↥K := by
  have h1 := Subgroup.card_mul_index (K.comap ψ)
  have h2 := Subgroup.card_mul_index K
  have h3 : (K.comap ψ).index = K.index := Subgroup.index_comap_of_surjective K hψ
  have h4 : Nat.card Q = Nat.card ↥ψ.ker * Nat.card A := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv]
    ring
  have hi : 0 < K.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_right hi
  calc Nat.card ↥(K.comap ψ) * K.index = Nat.card ↥(K.comap ψ) * (K.comap ψ).index := by rw [h3]
    _ = Nat.card Q := h1
    _ = Nat.card ↥ψ.ker * (Nat.card ↥K * K.index) := by rw [h4, ← h2]
    _ = Nat.card ↥ψ.ker * Nat.card ↥K * K.index := by ring

theorem exists_order_three_of_center_kz3 {G : Type} [Group G] [Finite G] {L V M : Subgroup G}
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hLM : L ≤ M)
    (ψ : (↥L ⧸ CFSG.pCore 2 ↥L) →* ↥(autOn L V))
    (hψ : ∀ l : ↥L, ψ (QuotientGroup.mk l) = res822Act' hLV l)
    (q : ↥L ⧸ CFSG.pCore 2 ↥L) (hq3 : orderOf q = 3) (hqψ : ψ q = 1) :
    ∃ y ∈ M, (∀ v ∈ V, y * v * y⁻¹ = v) ∧ orderOf y = 3 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
  have h3 : (QuotientGroup.mk l : ↥L ⧸ CFSG.pCore 2 ↥L) ^ 3 = 1 := by
    rw [← hq3]
    exact pow_orderOf_eq_one _
  have hl3 : l ^ 3 ∈ CFSG.pCore 2 ↥L := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact h3
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨l ^ 3, hl3⟩
  have hk' : l ^ (3 * 2 ^ k) = 1 := by
    have h := congrArg Subtype.val hk
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h
    rw [← pow_mul] at h
    exact h
  have hord : orderOf l ∣ 3 * 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hpow : (QuotientGroup.mk l : ↥L ⧸ CFSG.pCore 2 ↥L) ^ orderOf l = 1 := by
    rw [← QuotientGroup.mk_pow, pow_orderOf_eq_one, QuotientGroup.mk_one]
  have h3dvd : 3 ∣ orderOf l := by
    rw [← hq3]
    exact orderOf_dvd_of_pow_eq_one hpow
  obtain ⟨m, hm⟩ := h3dvd
  have hmdvd : m ∣ 2 ^ k := by
    rw [hm] at hord
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hord
  obtain ⟨b, -, hmb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hmdvd
  have h2b : 2 ^ b ∣ orderOf l := by
    rw [hm, hmb]
    exact Dvd.intro_left 3 rfl
  have hy0 : orderOf (l ^ 2 ^ b) = 3 := by
    rw [orderOf_pow_of_dvd (by positivity) h2b, hm, hmb, Nat.mul_div_cancel _ (by positivity)]
  have hmkpow : (QuotientGroup.mk (l ^ 2 ^ b) : ↥L ⧸ CFSG.pCore 2 ↥L) = (QuotientGroup.mk l) ^ 2 ^ b := by
    rw [QuotientGroup.mk_pow]
  have hψy : res822Act' hLV (l ^ 2 ^ b) = 1 := by
    rw [← hψ, hmkpow, map_pow, hqψ, one_pow]
  have hact : res822Act hLV (l ^ 2 ^ b) = 1 := congrArg Subtype.val hψy
  refine ⟨((l ^ 2 ^ b : ↥L) : G), hLM (l ^ 2 ^ b).2, ?_, ?_⟩
  · intro v hv
    have h2 : (res822Act hLV (l ^ 2 ^ b) : MulAut ↥V) ⟨v, hv⟩ = ⟨v, hv⟩ := by
      rw [hact]
      rfl
    have h3' := res822Act_apply hLV (l ^ 2 ^ b) ⟨v, hv⟩
    rw [h2] at h3'
    exact h3'.symm
  · rw [Subgroup.orderOf_coe]
    exact hy0

theorem injective_of_noThree_kz3 {G : Type} [Group G] [Finite G] {L V M : Subgroup G}
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hLM : L ≤ M) (hNT : NoThreeInCV M V)
    (hQ : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (ψ : (↥L ⧸ CFSG.pCore 2 ↥L) →* ↥(autOn L V))
    (hψ : ∀ l : ↥L, ψ (QuotientGroup.mk l) = res822Act' hLV l)
    (hker : ψ.ker = Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))
    (hdvd12 : Nat.card ↥(Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) ∣ 12) :
    Function.Injective ψ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hO : CFSG.pCore 2 (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := CFSG.Quasithin.B6.pCore_quotient_pCore
  have hodd : ¬ 2 ∣ Nat.card ↥(Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) :=
    res822_not_two_dvd_card_of_central le_rfl hO
  have h3 : ¬ 3 ∣ Nat.card ↥(Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) := by
    intro h3
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))) 3 h3
    have hxq : orderOf (x : ↥L ⧸ CFSG.pCore 2 ↥L) = 3 := by
      rw [Subgroup.orderOf_coe]
      exact hx
    have hxψ : ψ (x : ↥L ⧸ CFSG.pCore 2 ↥L) = 1 := by
      have hmem : (x : ↥L ⧸ CFSG.pCore 2 ↥L) ∈ ψ.ker := by
        rw [hker]
        exact x.2
      exact MonoidHom.mem_ker.mp hmem
    obtain ⟨y, hyM, hcent, hy3⟩ :=
      exists_order_three_of_center_kz3 hLV hLM ψ hψ (x : ↥L ⧸ CFSG.pCore 2 ↥L) hxq hxψ
    exact hNT y hyM hcent hy3
  have hcard1 : Nat.card ↥(Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 1 := by
    generalize hk : Nat.card ↥(Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = k at hdvd12 hodd h3 ⊢
    have hle : k ≤ 12 := Nat.le_of_dvd (by norm_num) hdvd12
    interval_cases k <;> omega
  have hbot : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := Subgroup.eq_bot_of_card_eq _ hcard1
  exact (MonoidHom.ker_eq_bot_iff ψ).mp (hker.trans hbot)

end CFSG.Quasithin.H13
