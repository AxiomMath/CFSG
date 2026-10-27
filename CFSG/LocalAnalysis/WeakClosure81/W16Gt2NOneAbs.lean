module

public import CFSG.Adapters.Involutions
public import CFSG.Quasithin.Background.A1bBasic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Subgroup

namespace NOne

variable {Ω : Type} [Group Ω] [Finite Ω]

structure IsConjClosure (X K : Subgroup Ω) (t : Ω) : Prop where
  le : K ≤ X
  conj_mem : ∀ x ∈ X, x⁻¹ * t * x ∈ K
  normal : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K
  gen : ∀ J : Subgroup Ω, (∀ x ∈ X, x⁻¹ * t * x ∈ J) → K ≤ J

private theorem oddCore_eq_pPrimeCore_two (X : Type*) [Group X] :
    CFSG.oddCore X = CFSG.pPrimeCore 2 X := by
  unfold CFSG.oddCore CFSG.pPrimeCore
  congr 1
  ext N
  simp [Nat.coprime_two_left]

private theorem odd_card_oddCore (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.oddCore X)) := by
  rw [oddCore_eq_pPrimeCore_two]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := CFSG.pPrimeCore_coprime_card (p := 2) (G := X)
  simpa [Nat.coprime_two_left] using h

private theorem oddCore_characteristic (X : Type*) [Group X] :
    (CFSG.oddCore X).Characteristic := by
  rw [oddCore_eq_pPrimeCore_two]
  infer_instance

private theorem conj_mem_oddCore_map {K : Subgroup Ω} {x : Ω}
    (hx : x ∈ Subgroup.normalizer K) {o : Ω}
    (ho : o ∈ (CFSG.oddCore ↥K).map K.subtype) :
    x * o * x⁻¹ ∈ (CFSG.oddCore ↥K).map K.subtype := by
  obtain ⟨k, hk, rfl⟩ := ho
  have hfix := Subgroup.characteristic_iff_map_eq.mp (oddCore_characteristic ↥K)
    (Subgroup.normalizerMonoidHom K ⟨x, hx⟩)
  refine ⟨Subgroup.normalizerMonoidHom K ⟨x, hx⟩ k, ?_, ?_⟩
  · rw [← hfix]
    exact ⟨k, hk, rfl⟩
  · rfl

theorem exists_odd_normal_eq_zpowers_sup {Hh P K : Subgroup Ω} {t : Ω}
    (hK : IsConjClosure Hh K t) (hP : IsSylowIn 2 P Hh) (htP : t ∈ P) (ht2 : t * t = 1)
    (ht1 : t ≠ 1) (hPt : ∀ x ∈ P, x * t = t * x)
    (hwc : ∀ x ∈ Hh, x⁻¹ * t * x ∈ P → x⁻¹ * t * x = t) :
    ∃ O : Subgroup Ω, O ≤ K ∧ Odd (Nat.card O) ∧ (∀ x ∈ Hh, ∀ o ∈ O, x * o * x⁻¹ ∈ O) ∧
      K = Subgroup.zpowers t ⊔ O := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htH : t ∈ Hh := hP.le htP
  let zt : ↥Hh := ⟨t, htH⟩
  let S : Sylow 2 ↥Hh := hP.toSylow
  let z : (S : Subgroup ↥Hh) := ⟨zt, by
    rw [hP.coe_toSylow, Subgroup.mem_subgroupOf]
    exact htP⟩
  have hzt2 : zt * zt = 1 := by
    apply Subtype.ext
    simpa [zt] using ht2
  have htord : orderOf t = 2 := by
    rw [orderOf_eq_prime_iff]
    exact ⟨by rwa [pow_two], ht1⟩
  have hzord : orderOf z = 2 := by
    have h1 : orderOf ((z : ↥Hh) : Ω) = orderOf z :=
      (Subgroup.orderOf_coe (z : ↥Hh)).trans
        (Subgroup.orderOf_coe (H := (S : Subgroup ↥Hh)) z)
    have h1' : orderOf t = orderOf z := h1
    rw [htord] at h1'
    exact h1'.symm
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzord
    exact absurd hzord (by norm_num)
  have hzZ : z ∈ Subgroup.center (S : Subgroup ↥Hh) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    apply Subtype.ext
    exact hPt ((y : ↥Hh) : Ω) (Subgroup.mem_subgroupOf.mp y.2)
  have hwc' : ∀ g : ↥Hh, g⁻¹ * zt * g ∈ (S : Subgroup ↥Hh) → g⁻¹ * zt * g = zt := by
    intro g hg
    have hgP : ((g⁻¹ * zt * g : ↥Hh) : Ω) ∈ P := by
      have := hg
      rwa [hP.coe_toSylow, Subgroup.mem_subgroupOf] at this
    have h := hwc (g : Ω) g.2 hgP
    apply Subtype.ext
    exact h
  have hZ := (CFSG.Adapters.glauberman_zStar S z hzZ hzord hwc').2
  have hstep : ∀ x : ↥Hh, ∃ o ∈ CFSG.oddCore ↥Hh, x⁻¹ * zt * x = zt * o := by
    intro x
    have hcen := Subgroup.mem_center_iff.mp hZ (QuotientGroup.mk x)
    have hmk : (QuotientGroup.mk (x * zt) : ↥Hh ⧸ CFSG.oddCore ↥Hh)
        = QuotientGroup.mk (zt * x) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      exact hcen
    have hm : (x * zt)⁻¹ * (zt * x) ∈ CFSG.oddCore ↥Hh := by
      rw [← QuotientGroup.eq_one_iff]
      have h1 : (QuotientGroup.mk ((x * zt)⁻¹ * (zt * x)) :
            ↥Hh ⧸ CFSG.oddCore ↥Hh)
          = (QuotientGroup.mk (x * zt))⁻¹ * QuotientGroup.mk (zt * x) := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [h1, hmk, inv_mul_cancel]
    refine ⟨zt * (x⁻¹ * zt * x), ?_, ?_⟩
    · have hz_inv : zt⁻¹ = zt := inv_eq_of_mul_eq_one_right hzt2
      rwa [show (x * zt)⁻¹ * (zt * x) = zt * (x⁻¹ * zt * x) from by
        rw [mul_inv_rev, hz_inv]; group] at hm
    · rw [← mul_assoc, hzt2, one_mul]
  have hconj : ∀ x ∈ Hh, ∃ o ∈ (CFSG.oddCore ↥Hh).map Hh.subtype, x⁻¹ * t * x = t * o := by
    intro x hx
    obtain ⟨o, ho, hoeq⟩ := hstep ⟨x, hx⟩
    refine ⟨(o : Ω), ⟨o, ho, rfl⟩, ?_⟩
    have := congrArg (fun w : ↥Hh => (w : Ω)) hoeq
    simpa [zt] using this
  have hKnormalizer : ∀ x ∈ Hh, x ∈ Subgroup.normalizer K := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro k
    exact ⟨fun hk => hK.normal x hx k hk,
      fun hk => by
        have h := hK.normal x⁻¹ (Hh.inv_mem hx) (x * k * x⁻¹) hk
        rwa [show x⁻¹ * (x * k * x⁻¹) * x⁻¹⁻¹ = k from by group] at h⟩
  have hinfO : K ⊓ (CFSG.oddCore ↥Hh).map Hh.subtype ≤
      (CFSG.oddCore ↥K).map K.subtype := by
    intro m hm
    have hmK : m ∈ K := hm.1
    have hO₀odd : Odd (Nat.card ((CFSG.oddCore ↥Hh).map Hh.subtype)) := by
      rw [Subgroup.card_subtype Hh (CFSG.oddCore ↥Hh)]
      exact odd_card_oddCore ↥Hh
    have hsubN : ((K ⊓ (CFSG.oddCore ↥Hh).map Hh.subtype).subgroupOf K).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact ⟨hK.normal (g : Ω) (hK.le g.2) (n : Ω) hn.1,
        conj_mem_oddCore_map (Subgroup.le_normalizer (hK.le g.2)) hn.2⟩
    have hodd_inf : Odd (Nat.card (K ⊓ (CFSG.oddCore ↥Hh).map Hh.subtype : Subgroup Ω)) := by
      have hdvd : Nat.card (K ⊓ (CFSG.oddCore ↥Hh).map Hh.subtype : Subgroup Ω) ∣
          Nat.card ((CFSG.oddCore ↥Hh).map Hh.subtype) := by
        have h := Subgroup.card_subgroup_dvd_card
          ((K ⊓ (CFSG.oddCore ↥Hh).map Hh.subtype).subgroupOf
            ((CFSG.oddCore ↥Hh).map Hh.subtype))
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
          (inf_le_right : K ⊓ (CFSG.oddCore ↥Hh).map Hh.subtype ≤
            (CFSG.oddCore ↥Hh).map Hh.subtype)).toEquiv] at h
        simpa using h
      exact Odd.of_dvd_nat hO₀odd hdvd
    have hsubO : Odd (Nat.card ((K ⊓ (CFSG.oddCore ↥Hh).map Hh.subtype).subgroupOf K)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : K ⊓ (CFSG.oddCore ↥Hh).map Hh.subtype ≤ K)).toEquiv]
      exact hodd_inf
    have hm_sub : (⟨m, hmK⟩ : ↥K) ∈
        (K ⊓ (CFSG.oddCore ↥Hh).map Hh.subtype).subgroupOf K := by
      rw [Subgroup.mem_subgroupOf]
      exact hm
    have hmem : (⟨m, hmK⟩ : ↥K) ∈ CFSG.oddCore ↥K := by
      change (⟨m, hmK⟩ : ↥K) ∈ sSup {N : Subgroup ↥K | N.Normal ∧ Odd (Nat.card N)}
      exact Subgroup.mem_sSup_of_mem (S := {N : Subgroup ↥K | N.Normal ∧ Odd (Nat.card N)})
        ⟨hsubN, hsubO⟩ hm_sub
    exact ⟨⟨m, hmK⟩, hmem, rfl⟩
  refine ⟨(CFSG.oddCore ↥K).map K.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · rw [Subgroup.card_subtype K (CFSG.oddCore ↥K)]
    exact odd_card_oddCore ↥K
  · intro x hx o ho
    exact conj_mem_oddCore_map (hKnormalizer x hx) ho
  · refine le_antisymm ?_ ?_
    · refine hK.gen _ ?_
      intro x hx
      obtain ⟨o, hoO₀, hxeq⟩ := hconj x hx
      have htK : t ∈ K := by
        have := hK.conj_mem 1 Hh.one_mem
        simpa using this
      have hoK : o ∈ K := by
        have hto : t * (x⁻¹ * t * x) = o := by
          rw [hxeq, ← mul_assoc, ht2, one_mul]
        rw [← hto]
        exact K.mul_mem htK (hK.conj_mem x hx)
      have hoO : o ∈ (CFSG.oddCore ↥K).map K.subtype := hinfO ⟨hoK, hoO₀⟩
      rw [hxeq]
      exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers t) hoO
    · have htK : t ∈ K := by
        have := hK.conj_mem 1 Hh.one_mem
        simpa using this
      exact sup_le (Subgroup.zpowers_le.mpr htK) (Subgroup.map_subtype_le _)

theorem eq_of_invariant_of_not_commute {Hh R O N : Subgroup Ω} {t : Ω} (hR2 : IsPGroup 2 R)
    (htR : t ∈ R) (ht2 : t * t = 1) (hOH : O ≤ Hh) (hOodd : Odd (Nat.card O))
    (h73 : ∀ y ∈ Hh, y ≠ 1 → Odd (orderOf y) → t * y * t⁻¹ = y⁻¹ → R ⊔ Subgroup.zpowers y = Hh)
    (hNO : N ≤ O) (hNR : ∀ r ∈ R, ∀ n ∈ N, r * n * r⁻¹ ∈ N)
    (hnc : ∃ x ∈ N, t * x ≠ x * t) : N = O := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRO_disj : R ⊓ O = ⊥ :=
    Subgroup.inf_eq_bot_of_coprime (by
      obtain ⟨k, hk⟩ := hR2.exists_card_eq
      rw [hk]
      exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hOodd))
  obtain ⟨x, hxN, hxnc⟩ := hnc
  have hxO : x ∈ O := hNO hxN
  have hxH : x ∈ Hh := hOH hxO
  set y : Ω := x⁻¹ * (t * x * t⁻¹) with hy_def
  have hyN : y ∈ N := N.mul_mem (N.inv_mem hxN) (hNR t htR x hxN)
  have hy1 : y ≠ 1 := by
    intro hy
    apply hxnc
    have htx : t * x * t⁻¹ = x := by
      have := congrArg (fun w => x * w) hy
      simpa [hy_def] using this
    calc t * x = t * x * t⁻¹ * t := by group
      _ = x * t := by rw [htx]
  have hty : t * y * t⁻¹ = y⁻¹ := by
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    have hconj2 : t * (t * x * t⁻¹) * t⁻¹ = x := by
      calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * t⁻¹ * t⁻¹ := by group
        _ = x * (t⁻¹ * t⁻¹) := by rw [ht2]; group
        _ = x := by rw [htinv, ht2, mul_one]
    have hxy : x * y = t * x * t⁻¹ := by rw [hy_def]; group
    calc t * y * t⁻¹
        = (t * x⁻¹ * t⁻¹) * (t * (t * x * t⁻¹) * t⁻¹) := by rw [hy_def]; group
      _ = (t * x * t⁻¹)⁻¹ * x := by rw [hconj2]; congr 1; group
      _ = (x * y)⁻¹ * x := by rw [← hxy]
      _ = y⁻¹ := by group
  have hyH : y ∈ Hh := hOH (hNO hyN)
  have hyodd : Odd (orderOf y) :=
    Odd.of_dvd_nat hOodd (Subgroup.orderOf_dvd_natCard O (hNO hyN))
  have hy73 := h73 y hyH hy1 hyodd hty
  have hRH : R ≤ Hh := by rw [← hy73]; exact le_sup_left
  have hRN_eq : R ⊔ N = Hh := by
    refine le_antisymm (sup_le hRH (hNO.trans hOH)) ?_
    rw [← hy73]
    exact sup_le_sup le_rfl (Subgroup.zpowers_le.mpr hyN)
  have hRnorm : R ≤ Subgroup.normalizer N := fun r hr =>
    Subgroup.mem_normalizer_iff.mpr fun n => ⟨fun hn => hNR r hr n hn,
      fun hn => by
        have h := hNR r⁻¹ (R.inv_mem hr) (r * n * r⁻¹) hn
        rwa [show r⁻¹ * (r * n * r⁻¹) * r⁻¹⁻¹ = n from by group] at h⟩
  exact le_antisymm hNO fun o ho => by
    have hoz : o ∈ ((R ⊔ N : Subgroup Ω) : Set Ω) := by rw [hRN_eq]; exact hOH ho
    rw [Subgroup.coe_mul_of_left_le_normalizer_right R N hRnorm] at hoz
    obtain ⟨r, hrR, n, hnN, hrn⟩ := hoz
    have hrO : r ∈ O := by
      have : r = o * n⁻¹ := by rw [← hrn]; group
      rw [this]
      exact O.mul_mem ho (O.inv_mem (hNO hnN))
    have hr1 : r = 1 := by
      have : r ∈ (⊥ : Subgroup Ω) := by rw [← hRO_disj]; exact ⟨hrR, hrO⟩
      simpa using this
    rw [← hrn, hr1]
    simpa using hnN

theorem exists_not_commute_of_ne {K O : Subgroup Ω} {t : Ω} (hKO : K = Subgroup.zpowers t ⊔ O)
    (hk : ∃ k ∈ K, k⁻¹ * t * k ≠ t) : ∃ o ∈ O, t * o ≠ o * t := by
  by_contra h
  have hcomm : ∀ o ∈ O, t * o = o * t := by
    intro o ho
    by_contra hne
    exact h ⟨o, ho, hne⟩
  have hKc : K ≤ Subgroup.centralizer ({t} : Set Ω) := by
    rw [hKO]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    · intro o ho
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcomm o ho).symm
  obtain ⟨k, hkK, hkne⟩ := hk
  apply hkne
  have hkt : k * t = t * k := Subgroup.mem_centralizer_singleton_iff.mp (hKc hkK)
  calc k⁻¹ * t * k = k⁻¹ * (t * k) := by group
    _ = k⁻¹ * (k * t) := by rw [← hkt]
    _ = t := by group

end NOne

end CFSG.LocalAnalysis.WeakClosure81
