module

public import CFSG.Walter.W67.Section6.R1512
public import CFSG.Walter.W67.Prop24
public import CFSG.Walter.PSL2Facts.Even

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups

namespace Sec56

variable {L : Type} [Group L] [Finite L]

theorem exists_psl28
    (hR : RFacts) (hL : JRGroup L) (hq3 : hL.q = 3)
    (hns : ¬ Group.IsSolvable L) :
    ∃ L' : Subgroup L, L'.Normal ∧ Nat.card L' = 504 ∧
      Nonempty (L' ≃* PSL(2, GaloisField 2 3)) := by
  obtain ⟨L₀, -, hsup, -, -, -, hcases⟩ := prop_2_4 L hL.toHyp hq3 hL.index_ne_two
  have hO := Sec6.pPrimeCore_eq_bot_of_R3 hR hL hq3
  rw [hO, sup_bot_eq] at hsup
  subst hsup
  have h1512 := Sec6.card_eq_1512 hR hL hq3 hns
  rcases hcases with ⟨h168, -⟩ | ⟨-, hidx3, ⟨e8⟩⟩
  · rw [Subgroup.card_top, h1512] at h168
    norm_num at h168
  · have hinj : Function.Injective (⊤ : Subgroup L).subtype := Subgroup.subtype_injective _
    refine ⟨(commutator (⊤ : Subgroup L)).map (⊤ : Subgroup L).subtype, ?_, ?_,
      ⟨(Subgroup.equivMapOfInjective _ _ hinj).symm.trans e8⟩⟩
    · exact Subgroup.Normal.map inferInstance _ fun y => ⟨⟨y, Subgroup.mem_top y⟩, rfl⟩
    · rw [Subgroup.card_map_of_injective hinj]
      have h1 := Subgroup.card_mul_index (commutator (⊤ : Subgroup L))
      rw [hidx3, Subgroup.card_top, h1512] at h1
      omega

theorem psl28_sylow_three_cyclic (P : Sylow 3 PSL(2, GaloisField 2 3)) :
    IsCyclic (P : Subgroup PSL(2, GaloisField 2 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : Nat.card (GaloisField 2 3) = 2 ^ 3 := GaloisField.card 2 3 (by norm_num)
  exact GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card (GaloisField 2 3) hK
    (by rw [hK]; norm_num) 3 (by norm_num) (by rw [hK]; norm_num) P

theorem card_inf_derived {L' T : Subgroup L} (hL'n : L'.Normal) (hL'c : Nat.card L' = 504)
    (h1512 : Nat.card L = 1512) (hT3 : IsPGroup 3 T) (hTc : Nat.card T = 27) :
    Nat.card (L' ⊓ T : Subgroup L) = 9 := by
  have hTN : T ≤ Subgroup.normalizer (L' : Set L) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hL'n]
    exact le_top
  have e1 := Sec52.card_sup_mul_card_inf hTN
  rw [hL'c, hTc] at e1
  have h1 : Nat.card (T ⊔ L' : Subgroup L) ≤ 1512 := h1512 ▸ Subgroup.card_le_card_group _
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hT3.to_le (inf_le_right : L' ⊓ T ≤ T))
  have hdvd : Nat.card (L' ⊓ T : Subgroup L) ∣ 504 := hL'c ▸ Subgroup.card_dvd_of_le inf_le_left
  rw [hk] at hdvd e1 ⊢
  have hk2 : k ≤ 2 := by
    by_contra h
    have : 3 ^ 3 ∣ 504 := (pow_dvd_pow 3 (by omega)).trans hdvd
    norm_num at this
  interval_cases k <;> norm_num at e1 ⊢ <;> omega

theorem exists_pow_three_ne_one_of_card
    (hR : RFacts) (hL : JRGroup L) (hq3 : hL.q = 3)
    (hns : ¬ Group.IsSolvable L) {T : Subgroup L} (hT3 : IsPGroup 3 T)
    (hTc : Nat.card T = 27) : ∃ y ∈ T, y ^ 3 ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨L', hL'n, hL'c, ⟨e⟩⟩ := exists_psl28 hR hL hq3 hns
  have h1512 := Sec6.card_eq_1512 hR hL hq3 hns
  have h9 := card_inf_derived hL'n hL'c h1512 hT3 hTc
  set P := L' ⊓ T with hPdef
  set P' : Subgroup PSL(2, GaloisField 2 3) := (P.subgroupOf L').map e.toMonoidHom with hP'def
  have hP'c : Nat.card P' = 9 := by
    rw [hP'def, Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, h9]
  have hPSLc : Nat.card PSL(2, GaloisField 2 3) = 504 := by
    rw [← Nat.card_congr e.toEquiv, hL'c]
  have hfac : (Nat.card PSL(2, GaloisField 2 3)).factorization 3 = 2 := by
    rw [hPSLc, show (504 : ℕ) = 3 ^ 2 * 56 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  let S : Sylow 3 PSL(2, GaloisField 2 3) := Sylow.ofCard P' (by rw [hP'c, hfac]; norm_num)
  have hcyc : IsCyclic P' := by
    have := psl28_sylow_three_cyclic S
    rwa [Sylow.coe_ofCard] at this
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hog : orderOf g = 9 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hP'c]
  obtain ⟨y, hyP, hye⟩ := Subgroup.mem_map.mp g.2
  have hoy : orderOf ((y : L') : L) = 9 := by
    rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq e y]
    change orderOf (e.toMonoidHom y) = 9
    rw [hye, Subgroup.orderOf_coe, hog]
  refine ⟨(y : L'), (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hyP)).2, fun h => ?_⟩
  have := orderOf_dvd_of_pow_eq_one h
  rw [hoy] at this
  norm_num at this

theorem eq_one_of_mem_center
    (hR : RFacts) (hL : JRGroup L) (hq3 : hL.q = 3)
    (hns : ¬ Group.IsSolvable L) {T : Subgroup L} (hT3 : IsPGroup 3 T)
    (hTc : Nat.card T = 27) {v : L} (hvT : v ∈ T) (hvc : ∀ w ∈ T, v * w = w * v) {t : L}
    (hot : orderOf t = 2) (hvt : v * t = t * v) : v = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨L', hL'n, hL'c, ⟨e⟩⟩ := exists_psl28 hR hL hq3 hns
  have h1512 := Sec6.card_eq_1512 hR hL hq3 hns
  obtain ⟨-, ⟨hR2a, hR2b⟩, -⟩ := hR L hL (by rw [hq3]; norm_num)
  have hL'N : ∀ X : Subgroup L, X ≤ Subgroup.normalizer (L' : Set L) := fun X => by
    rw [Subgroup.normalizer_eq_top_iff.mpr hL'n]
    exact le_top
  have hidx : Nat.card (L ⧸ L') = 3 := by
    have h1 := Subgroup.card_mul_index L'
    rw [hL'c, h1512, Subgroup.index] at h1
    omega
  have h2mem : ∀ y : L, ∀ k : ℕ, y ^ (2 ^ k) = 1 → y ∈ L' := by
    intro y k hy
    have h1 : orderOf (QuotientGroup.mk' L' y) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hy, map_one])
    have h2 : orderOf (QuotientGroup.mk' L' y) ∣ 3 := hidx ▸ orderOf_dvd_natCard _
    have h3 : orderOf (QuotientGroup.mk' L' y) = 1 := by
      have := Nat.dvd_gcd h1 h2
      rwa [(Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)).gcd_eq_one,
        Nat.dvd_one] at this
    rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
    exact h3
  have hS2 : ∀ S : Sylow 2 L, (S : Subgroup L) ≤ L' := by
    intro S y hy
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨y, hy⟩
    exact h2mem y k (congrArg Subtype.val hk)
  set P₃ := L' ⊓ T with hP₃def
  have hP₃c : Nat.card P₃ = 9 := card_inf_derived hL'n hL'c h1512 hT3 hTc
  have hP₃3 : IsPGroup 3 P₃ := hT3.to_le inf_le_right
  have hP₃N : ∀ S : Sylow 2 L, ∀ h ∈ P₃, h ∈ Subgroup.normalizer ((S : Subgroup L) : Set L) →
      h = 1 := by
    intro S h hh hhN
    have hsup : Subgroup.normalizer ((S : Subgroup L) : Set L) ⊔ L' = ⊤ :=
      Sylow.normalizer_sup_eq_top' S (hS2 S)
    have e1 := Sec52.card_sup_mul_card_inf (hL'N (Subgroup.normalizer ((S : Subgroup L) : Set L)))
    rw [hsup, Subgroup.card_top, h1512, hL'c, (hR2a S).2] at e1
    have h56 : Nat.card (L' ⊓ Subgroup.normalizer ((S : Subgroup L) : Set L) : Subgroup L) = 56 :=
      by omega
    have hX3 : IsPGroup 3 (P₃ ⊓ Subgroup.normalizer ((S : Subgroup L) : Set L) : Subgroup L) :=
      hP₃3.to_le inf_le_left
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX3
    have hdvd : Nat.card (P₃ ⊓ Subgroup.normalizer ((S : Subgroup L) : Set L) : Subgroup L) ∣ 56 :=
      h56 ▸ Subgroup.card_dvd_of_le (inf_le_inf_right _ inf_le_left)
    rw [hk] at hdvd
    have hk0 : k = 0 := by
      by_contra hk0
      have : 3 ∣ 56 := (dvd_pow_self 3 hk0).trans hdvd
      norm_num at this
    rw [hk0, pow_zero] at hk
    have hbot := Subgroup.eq_bot_of_card_eq _ hk
    have : h ∈ P₃ ⊓ Subgroup.normalizer ((S : Subgroup L) : Set L) :=
      Subgroup.mem_inf.mpr ⟨hh, hhN⟩
    rwa [hbot, Subgroup.mem_bot] at this
  obtain ⟨S₀⟩ : Nonempty (Sylow 2 L) := inferInstance
  have hcardSyl : Nat.card (Sylow 2 L) = 9 := by
    rw [Sylow.card_eq_index_normalizer S₀]
    change (Subgroup.normalizer ((S₀ : Subgroup L) : Set L)).index = 9
    have h1 := Subgroup.card_mul_index (Subgroup.normalizer ((S₀ : Subgroup L) : Set L))
    rw [(hR2a S₀).2, h1512] at h1
    omega
  let F : P₃ → Sylow 2 L := fun h => (h : L) • S₀
  have hFinj : Function.Injective F := by
    intro h h' hh
    have h1 : ((h : L)⁻¹ * h') • S₀ = S₀ := by
      rw [mul_smul]
      rw [← show (h : L) • S₀ = (h' : L) • S₀ from hh, inv_smul_smul]
    have h2 := hP₃N S₀ _ (P₃.mul_mem (P₃.inv_mem h.2) h'.2) (Sylow.smul_eq_iff_mem_normalizer.mp h1)
    apply Subtype.ext
    calc (h : L) = h * ((h : L)⁻¹ * h') := by rw [h2, mul_one]
      _ = h' := by group
  have hFsurj : Function.Surjective F := by
    have : Nat.card P₃ = Nat.card (Sylow 2 L) := by rw [hP₃c, hcardSyl]
    exact (Function.Injective.bijective_of_nat_card_le hFinj this.ge).2
  have hP₃ab : ∀ a ∈ P₃, ∀ b ∈ P₃, a * b = b * a := by
    have := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := P₃)
      (by rw [hP₃c]; norm_num)
    intro a ha b hb
    exact congrArg Subtype.val (this.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨h, hh⟩ := hFsurj (v • S₀)
  set w := (h : L)⁻¹ * v with hwdef
  have hwfix : ∀ S : Sylow 2 L, w • S = S := by
    intro S
    obtain ⟨h', rfl⟩ := hFsurj S
    have hwh' : w * h' = h' * w := by
      have h1 : v * h' = h' * v := hvc _ (Subgroup.mem_inf.mp h'.2).2
      have h2 : (h : L)⁻¹ * h' = h' * (h : L)⁻¹ :=
        hP₃ab _ (P₃.inv_mem h.2) _ h'.2
      calc w * h' = (h : L)⁻¹ * (v * h') := by rw [hwdef]; group
        _ = (h : L)⁻¹ * (h' * v) := by rw [h1]
        _ = ((h : L)⁻¹ * h') * v := by group
        _ = (h' * (h : L)⁻¹) * v := by rw [h2]
        _ = h' * w := by rw [hwdef]; group
    change w • ((h' : L) • S₀) = (h' : L) • S₀
    have h3 : w • S₀ = S₀ := by
      rw [hwdef, mul_smul, ← hh]
      exact inv_smul_smul _ _
    rw [← mul_smul, hwh', mul_smul, h3]
  set D : Subgroup L := ⨅ S : Sylow 2 L, Subgroup.normalizer ((S : Subgroup L) : Set L) with hDdef
  have hmemD : ∀ y : L, y ∈ D ↔ ∀ S : Sylow 2 L, y • S = S := by
    intro y
    rw [hDdef, Subgroup.mem_iInf]
    exact forall_congr' fun S => Sylow.smul_eq_iff_mem_normalizer.symm
  have hDn : D.Normal := ⟨fun d hd g => by
    rw [hmemD] at hd ⊢
    intro S
    rw [mul_smul, mul_smul, hd (g⁻¹ • S), smul_inv_smul]⟩
  have hDodd : Odd (Nat.card D) := by
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    intro h2
    obtain ⟨⟨d, hdD⟩, hod⟩ := exists_prime_orderOf_dvd_card' (G := D) 2 h2
    rw [Subgroup.orderOf_mk] at hod
    have hinv : ∀ y : L, orderOf y = 2 → y ∈ D := by
      intro y hy
      obtain ⟨c, hc⟩ := isConj_iff.mp (hR2b d y hod hy)
      rw [← hc]
      exact hDn.conj_mem d hdD c
    have hall : ∀ S : Sylow 2 L, S = S₀ := by
      intro S
      have hSD : (S : Subgroup L) ≤ Subgroup.normalizer ((S₀ : Subgroup L) : Set L) := by
        intro y hy
        by_cases hy1 : y = 1
        · rw [hy1]
          exact Subgroup.one_mem _
        have hy2 : y * y = 1 := by
          have := (hL.elementary_sylow S).exponent_dvd_p
          have h1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp this ⟨y, hy⟩
          rw [pow_two] at h1
          exact congrArg Subtype.val h1
        have hoy : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
        exact Sylow.smul_eq_iff_mem_normalizer.mp ((hmemD y).mp (hinv y hoy) S₀)
      have hp := IsPGroup.to_sup_of_normal_right' S.isPGroup' S₀.isPGroup' hSD
      have h1 := S₀.is_maximal' hp le_sup_right
      have h2 : (S : Subgroup L) ≤ S₀ := h1 ▸ le_sup_left
      exact Sylow.ext (S.is_maximal' S₀.isPGroup' h2).symm
    have : Nat.card (Sylow 2 L) ≤ 1 := by
      rw [Finite.card_le_one_iff_subsingleton]
      exact ⟨fun S S' => (hall S).trans (hall S').symm⟩
    omega
  have hD1 := Sec6.eq_bot_of_normal_odd hR hL hq3 D hDn hDodd
  have hw1 : w = 1 := by
    have : w ∈ D := (hmemD w).mpr hwfix
    rwa [hD1, Subgroup.mem_bot] at this
  have hvh : v = h := by
    have : (h : L)⁻¹ * v = 1 := hw1
    rw [inv_mul_eq_one] at this
    exact this.symm
  have hvL' : v ∈ L' := hvh ▸ (Subgroup.mem_inf.mp h.2).1
  have htL' : t ∈ L' := h2mem t 1 (by rw [pow_one, ← hot, pow_orderOf_eq_one])
  set v' : L' := ⟨v, hvL'⟩
  set t' : L' := ⟨t, htL'⟩
  have hot' : orderOf (e t') = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hot]
  have hvC : e v' ∈ Subgroup.centralizer ({e t'} : Set PSL(2, GaloisField 2 3)) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext hvt)
  have h2 := psl2_centralizer_isPGroup_of_charTwo hot' ⟨e v', hvC⟩
  obtain ⟨k, hk⟩ := h2
  have hk' : (e v') ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hT3
  have hv3 : v ^ (3 ^ m) = 1 := by
    rw [← hm]
    exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨v, hvT⟩ : T)))
  have hev3 : (e v') ^ (3 ^ m) = 1 := by
    rw [← map_pow]
    have : v' ^ (3 ^ m) = 1 := Subtype.ext (by simpa using hv3)
    rw [this, map_one]
  have hod : orderOf (e v') = 1 := by
    have h1 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one hev3)
    rwa [(Nat.Coprime.pow k m (by norm_num : Nat.Coprime 2 3)).gcd_eq_one, Nat.dvd_one] at h1
  rw [orderOf_eq_one_iff, map_eq_one_iff _ e.injective] at hod
  exact congrArg Subtype.val hod

end Sec56

end CFSG.Walter.W67
