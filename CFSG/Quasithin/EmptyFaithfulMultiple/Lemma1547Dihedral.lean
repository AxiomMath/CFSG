module

public import CFSG.Quasithin.EmptyFaithful.S14110D8
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralGenerators
public import CFSG.Quasithin.Background.A1cTransferVariants
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma1547Facts

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

namespace L1547

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits DihedralGroup

variable {G : Type*} [Group G] [Finite G]

theorem exists_dihedral_generators {T V : Subgroup G} (hT8 : Nat.card T = 8) (hVT : V ≤ T)
    (hV4 : Nat.card V = 4) (hV2 : ∀ v ∈ V, v ^ 2 = 1)
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) {z : G} (hzV : z ∈ V) (hz1 : z ≠ 1)
    (hzc : ∀ t ∈ T, t * z = z * t)
    (hfix : ∀ v ∈ V, (∀ t ∈ T, t * v = v * t) → v = 1 ∨ v = z) :
    ∃ a ∈ T, ∃ b ∈ T, a ^ 2 = z ∧ orderOf a = 4 ∧ b ^ 2 = 1 ∧ b * a * b⁻¹ = a⁻¹ ∧
      b ∉ Subgroup.zpowers a ∧ Subgroup.zpowers a ⊔ Subgroup.zpowers b = T := by
  have hVcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := by
    intro x hx y hy
    have h1 := hV2 _ (V.mul_mem hx hy)
    have hx2 := hV2 x hx
    have hy2 := hV2 y hy
    rw [pow_two] at h1 hx2 hy2
    calc x * y = x * (x * y * (x * y)) * y := by rw [h1, mul_one]
      _ = (x * x) * (y * x) * (y * y) := by group
      _ = y * x := by rw [hx2, hy2, one_mul, mul_one]
  have hz2 : z ^ 2 = 1 := hV2 z hzV
  have hzinv : z⁻¹ = z := by
    rw [pow_two] at hz2
    exact inv_eq_of_mul_eq_one_right hz2
  obtain ⟨v, hvV, hv1, hvz⟩ := exists_ne_of_card_eq_four hV4 z
  have hcases := mem_of_card_eq_four hV4 hV2 hzV hvV hz1 hv1 hvz
  have hv2 : v ^ 2 = 1 := hV2 v hvV
  have hvinv : v⁻¹ = v := by
    rw [pow_two] at hv2
    exact inv_eq_of_mul_eq_one_right hv2
  obtain ⟨t, htT, htv⟩ : ∃ t ∈ T, t * v ≠ v * t := by
    by_contra h
    push Not at h
    rcases hfix v hvV h with h1 | h1
    · exact hv1 h1
    · exact hvz h1
  have hconj : t * v * t⁻¹ = v * z := by
    have hmem : t * v * t⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hTV htT) v).mp hvV
    rcases hcases _ hmem with h | h | h | h
    · exfalso
      apply hv1
      calc v = t⁻¹ * (t * v * t⁻¹) * t := by group
        _ = 1 := by rw [h]; group
    · exfalso
      apply hvz
      calc v = t⁻¹ * (t * v * t⁻¹) * t := by group
        _ = t⁻¹ * (z * t) := by rw [h]; group
        _ = t⁻¹ * (t * z) := by rw [hzc t htT]
        _ = z := by group
    · exfalso
      apply htv
      calc t * v = t * v * t⁻¹ * t := by group
        _ = v * t := by rw [h]
    · exact h
  have hconj' : t⁻¹ * v * t = v * z := by
    have hzt : t⁻¹ * z * t = z := by
      rw [mul_assoc, ← hzc t htT, ← mul_assoc, inv_mul_cancel, one_mul]
    have h1 : (t⁻¹ * v * t) * (t⁻¹ * z * t) = v := by
      calc (t⁻¹ * v * t) * (t⁻¹ * z * t) = t⁻¹ * (v * z) * t := by group
        _ = t⁻¹ * (t * v * t⁻¹) * t := by rw [hconj]
        _ = v := by group
    rw [hzt] at h1
    calc t⁻¹ * v * t = (t⁻¹ * v * t) * z * z := by
          rw [mul_assoc (t⁻¹ * v * t) z z, ← pow_two, hz2, mul_one]
      _ = v * z := by rw [h1]
  have htV : t ∉ V := fun h => htv (hVcomm t h v hvV)
  have hidx : (V.subgroupOf T).index = 2 := by
    have h := Subgroup.relIndex_mul_card V T
    rw [inf_eq_left.mpr hVT, hV4, hT8] at h
    change V.relIndex T = 2
    omega
  have ht2V : t ^ 2 ∈ V := by
    have := Subgroup.sq_mem_of_index_two hidx ⟨t, htT⟩
    simpa using Subgroup.mem_subgroupOf.mp this
  have ht2 : t ^ 2 = 1 ∨ t ^ 2 = z := by
    refine hfix _ ht2V fun s hs => ?_
    rcases hcases _ ht2V with h | h | h | h
    · rw [h, one_mul, mul_one]
    · rw [h]
      exact hzc s hs
    · exfalso
      have : t * t ^ 2 = t ^ 2 * t := by rw [← pow_succ', ← pow_succ]
      rw [h] at this
      exact htv this
    · exfalso
      have h1 : t * t ^ 2 * t⁻¹ = t ^ 2 := by group
      rw [h, show t * (v * z) * t⁻¹ = (t * v * t⁻¹) * (t * z * t⁻¹) by group, hconj,
        show t * z * t⁻¹ = z by rw [hzc t htT]; group, mul_assoc, ← pow_two, hz2, mul_one] at h1
      exact hz1 (mul_left_cancel (h1.symm.trans (mul_one v).symm))
  obtain ⟨a, haT, ha2, haV, haform⟩ : ∃ a ∈ T, a ^ 2 = z ∧ a ∉ V ∧ (a = t ∨ a = t * v) := by
    rcases ht2 with h | h
    · refine ⟨t * v, T.mul_mem htT (hVT hvV), ?_, ?_, Or.inr rfl⟩
      · calc (t * v) ^ 2 = (t * v * t⁻¹) * t ^ 2 * v := by rw [pow_two, pow_two]; group
          _ = v * z * v := by rw [hconj, h, mul_one]
          _ = z := by
              rw [mul_assoc, hVcomm z hzV v hvV, ← mul_assoc, ← pow_two, hv2, one_mul]
      · intro hV
        apply htV
        have : t = t * v * v⁻¹ := by group
        rw [this]
        exact V.mul_mem hV (V.inv_mem hvV)
    · exact ⟨t, htT, h, htV, Or.inl rfl⟩
  have ha4 : a ^ 4 = 1 := by
    rw [show 4 = 2 * 2 by rfl, pow_mul, ha2, hz2]
  have hord : orderOf a = 4 := by
    have hdvd : orderOf a ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one ha4
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    interval_cases k
    · exfalso
      rw [pow_zero, orderOf_eq_one_iff] at hk'
      rw [hk', one_pow] at ha2
      exact hz1 ha2.symm
    · exfalso
      have : a ^ 2 = 1 := by rw [← pow_one 2, ← hk']; exact pow_orderOf_eq_one a
      rw [ha2] at this
      exact hz1 this
    · exact hk'
  have hrel : v * a * v⁻¹ = a⁻¹ := by
    have hainv : a⁻¹ = a * z := by
      have : a * (a * z) = 1 := by
        rw [← mul_assoc, ← pow_two, ha2, ← pow_two, hz2]
      exact (eq_inv_of_mul_eq_one_right this).symm
    rw [hainv, hvinv]
    have hvt : v * t = t * (v * z) := by
      calc v * t = t * (t⁻¹ * v * t) := by group
        _ = t * (v * z) := by rw [hconj']
    rcases haform with rfl | rfl
    · rw [hvt, mul_assoc, mul_assoc, hVcomm z hzV v hvV, ← mul_assoc v v, ← pow_two, hv2,
        one_mul]
    · calc v * (t * v) * v = (v * t) * (v * v) := by group
        _ = t * (v * z) * 1 := by rw [hvt, ← pow_two, hv2]
        _ = t * v * z := by group
  have hvA : v ∉ Subgroup.zpowers a := by
    intro hv
    obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers.mpr hv : v ∈ Submonoid.powers a)
    have hn' : a ^ (n % 4) = v := by rw [← hord, pow_mod_orderOf]; exact hn
    have hlt : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
    interval_cases (n % 4)
    · exact hv1 (by rw [← hn', pow_zero])
    · exact haV (by rw [pow_one] at hn'; rw [hn']; exact hvV)
    · exact hvz (by rw [← hn', ha2])
    · apply haV
      have : a = a ^ 3 * z := by
        rw [show a ^ 3 * z = a ^ 3 * a ^ 2 by rw [ha2], ← pow_add,
          show 3 + 2 = 4 + 1 by rfl, pow_add, ha4, one_mul, pow_one]
      rw [this, hn']
      exact V.mul_mem hvV hzV
  refine ⟨a, haT, v, hVT hvV, ha2, hord, hv2, hrel, hvA, ?_⟩
  refine Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr haT)
    (Subgroup.zpowers_le.mpr (hVT hvV))) ?_
  rw [hT8]
  have h4 : 4 ∣ Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers v) := by
    have := Subgroup.card_dvd_of_le (le_sup_left : Subgroup.zpowers a ≤
      Subgroup.zpowers a ⊔ Subgroup.zpowers v)
    rwa [Nat.card_zpowers, hord] at this
  obtain ⟨m, hm⟩ := h4
  have hm1 : m ≠ 1 := by
    intro hm1
    rw [hm1, mul_one] at hm
    have heq := Subgroup.eq_of_le_of_card_ge (le_sup_left : Subgroup.zpowers a ≤
      Subgroup.zpowers a ⊔ Subgroup.zpowers v) (by rw [hm, Nat.card_zpowers, hord])
    exact hvA (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers v))
  have hm0 : m ≠ 0 := by
    intro hm0
    rw [hm0, mul_zero] at hm
    exact (Nat.card_pos (α := ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers v))).ne' hm
  omega

theorem nonempty_mulEquiv_dihedralFour {T : Subgroup G} {a b : G} (haT : a ∈ T) (hbT : b ∈ T)
    (ha4 : orderOf a = 4) (hb2 : b ^ 2 = 1) (hrel : b * a * b⁻¹ = a⁻¹)
    (hba : b ∉ Subgroup.zpowers a) (hgen : Subgroup.zpowers a ⊔ Subgroup.zpowers b = T) :
    Nonempty (T ≃* DihedralGroup 4) := by
  let ρ : T := ⟨a, haT⟩
  let σ : T := ⟨b, hbT⟩
  have hgen' : (⊤ : Subgroup T) = Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ := by
    apply Subgroup.map_injective T.subtype_injective
    rw [Subgroup.map_top, Subgroup.range_subtype, Subgroup.map_sup, MonoidHom.map_zpowers,
      MonoidHom.map_zpowers]
    exact hgen.symm
  have hσ2 : σ ^ 2 = 1 := Subtype.ext (by simpa using hb2)
  have hrel' : σ * ρ * σ⁻¹ = ρ⁻¹ := Subtype.ext (by simpa using hrel)
  have hσρ : σ ∉ Subgroup.zpowers ρ := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    exact hba (Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩)
  have hord : orderOf ρ = 4 := by rw [Subgroup.orderOf_mk, ha4]
  rw [← hord]
  exact CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem ρ σ hgen' hσ2 hrel' hσρ

theorem centralizer_eq_of_dihedral (hEven : quasithinEvenCharacteristic G) (S : Sylow 2 G)
    (φ : (S : Subgroup G) ≃* DihedralGroup 4) {z : G} (hzS : z ∈ (S : Subgroup G))
    (hzφ : φ ⟨z, hzS⟩ = r 2) : Subgroup.centralizer ({z} : Set G) = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcenD : ∀ g : DihedralGroup 4, (∀ k : DihedralGroup 4, g * k = k * g) ↔
      (g = 1 ∨ g = r 2) := by decide
  have hz1 : z ≠ 1 := by
    intro h1
    have : (⟨z, hzS⟩ : (S : Subgroup G)) = 1 := Subtype.ext h1
    rw [this, map_one] at hzφ
    exact absurd hzφ (by decide)
  have hzcen : ∀ t ∈ (S : Subgroup G), t * z = z * t := by
    intro t ht
    have hc := (hcenD (r 2)).mpr (Or.inr rfl) (φ ⟨t, ht⟩)
    have : (⟨t, ht⟩ : (S : Subgroup G)) * ⟨z, hzS⟩ = ⟨z, hzS⟩ * ⟨t, ht⟩ := φ.injective (by
      rw [map_mul, map_mul, hzφ]; exact hc.symm)
    exact congrArg Subtype.val this
  have hz2 : orderOf z = 2 := by
    have h2 : (⟨z, hzS⟩ : (S : Subgroup G)) ^ 2 = 1 :=
      φ.injective (by rw [map_pow, hzφ, map_one]; decide)
    exact orderOf_eq_prime (by simpa using congrArg Subtype.val h2) hz1
  set P : Subgroup G := Subgroup.zpowers z with hP
  set N : Subgroup G := Subgroup.normalizer (P : Set G) with hN
  have hCN : Subgroup.centralizer ({z} : Set G) ≤ N := by
    have : Subgroup.centralizer ({z} : Set G) = Subgroup.centralizer (P : Set G) := by
      rw [hP, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [this]
    exact Subgroup.centralizer_le_normalizer _
  have hTC : (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzcen t ht)
  have hTN : (S : Subgroup G) ≤ N := hTC.trans hCN
  have hPp : IsPGroup 2 P := S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hzS)
  have hP1 : P ≠ ⊥ := fun hb => hz1 ((Subgroup.zpowers_eq_bot).mp hb)
  have hF : N ⊓ Subgroup.centralizer (pCoreOf 2 N : Set G) ≤ pCoreOf 2 N :=
    hEven N ⟨P, hP1, hPp, rfl⟩ ⟨S, hTN⟩
  set Q : Subgroup G := pCoreOf 2 N with hQ
  have hQT : Q ≤ (S : Subgroup G) := pCoreOf_two_le_sylow N S hTN
  have hzQ : z ∈ Q := hF ⟨hTN hzS, Subgroup.mem_centralizer_iff.mpr fun q hq =>
    hzcen q (hQT hq)⟩
  have hodd : ∀ x ∈ Subgroup.centralizer ({z} : Set G), ∀ p : ℕ, p.Prime → p ≠ 2 →
      orderOf x = p → False := by
    intro x hx p hp hp2 hxp
    have hxN : x ∈ N := hCN hx
    have hxQ : x ∈ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf 2 N hxN
    let β : MulAut Q := Q.normalizerMonoidHom ⟨x, hxQ⟩
    have hβ : ∀ q : Q, ((β q : Q) : G) = x * q * x⁻¹ :=
      fun q => Subgroup.normalizerMonoidHom_apply_apply_coe Q ⟨x, hxQ⟩ q
    let ι : Q →* DihedralGroup 4 := φ.toMonoidHom.comp (Subgroup.inclusion hQT)
    have hι : Function.Injective ι := φ.injective.comp (Subgroup.inclusion_injective hQT)
    have hιz : ι ⟨z, hzQ⟩ = r 2 := hzφ
    have hβz : β ⟨z, hzQ⟩ = ⟨z, hzQ⟩ := by
      apply Subtype.ext
      rw [hβ]
      change x * z * x⁻¹ = z
      rw [(Subgroup.mem_centralizer_singleton_iff.mp hx), mul_inv_cancel_right]
    have hβp : β ^ p = 1 := by
      have : (⟨x, hxQ⟩ : Subgroup.normalizer (Q : Set G)) ^ p = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, ← hxp, pow_orderOf_eq_one, Subgroup.coe_one]
      change Q.normalizerMonoidHom ⟨x, hxQ⟩ ^ p = 1
      rw [← map_pow, this, map_one]
    have hβ1 := mulAut_eq_one_of_dihedralFour ι hι hιz β hβz (hp.odd_of_ne_two hp2) hβp
    have hxC : x ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have h1 : ((β ⟨q, hq⟩ : Q) : G) = q := by rw [hβ1]; rfl
      rw [hβ] at h1
      calc q * x = (x * q * x⁻¹) * x := by rw [h1]
        _ = x * q := by group
    have hxQ' : x ∈ Q := hF ⟨hxN, hxC⟩
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 N) ⟨x, hxQ'⟩
    have hdvd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hk)
    rw [hxp] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))
  have hC2 : IsPGroup 2 (Subgroup.centralizer ({z} : Set G)) := by
    apply IsPGroup.of_card
      (n := (Nat.card (Subgroup.centralizer ({z} : Set G))).primeFactorsList.length)
    apply Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
    intro d hd hdvd
    by_contra hd2
    have : Fact d.Prime := ⟨hd⟩
    obtain ⟨x, hx⟩ :=
      exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer ({z} : Set G)) d hdvd
    exact hodd x x.2 d hd hd2 (by rw [← Subgroup.orderOf_coe] at hx; exact hx)
  exact S.is_maximal' hC2 hTC

theorem isConj_of_index_two [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (S : Sylow 2 G)
    {a z : G} (haS : a ∈ (S : Subgroup G)) (hidx : (Subgroup.zpowers a).relIndex S = 2)
    (hza : ∀ y ∈ Subgroup.zpowers a, orderOf y = 2 → y = z) {u : G} (hu : orderOf u = 2) :
    IsConj u z := by
  by_contra hnc
  have hQu : ∀ x : G, x⁻¹ * u * x ∉ Subgroup.zpowers a := by
    intro x hx
    apply hnc
    have hord : orderOf (x⁻¹ * u * x) = 2 := by
      have := (MulAut.conj x⁻¹).orderOf_eq u
      rw [MulAut.conj_apply, inv_inv] at this
      rw [this, hu]
    rw [isConj_iff]
    exact ⟨x⁻¹, by rw [inv_inv]; exact hza _ hx hord⟩
  obtain ⟨N, hNn, hsq, huN⟩ := thompson_transfer_exists_normal S
    (Subgroup.zpowers_le.mpr haS) hidx hu hQu
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · obtain ⟨x, y, hxy⟩ := hnonab
    apply hxy
    have hsq' : ∀ g : G, g ^ 2 = 1 := fun g => by
      have := hsq g
      rwa [h, Subgroup.mem_bot] at this
    have hinv : ∀ g : G, g⁻¹ = g := fun g =>
      inv_eq_of_mul_eq_one_right (by rw [← pow_two, hsq' g])
    calc x * y = (x * y)⁻¹ := (hinv _).symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by rw [hinv x, hinv y]
  · exact huN (h ▸ Subgroup.mem_top u)

end L1547

end CFSG.Quasithin.EmptyFaithfulMultiple
