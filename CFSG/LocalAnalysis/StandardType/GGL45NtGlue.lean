module

public import CFSG.LocalAnalysis.StandardType.GGL45NtLift
public import CFSG.LocalAnalysis.StandardType.GGL45NtNonab
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggL45NtGlue_mul_conj_mul_inv {R : Type} [Group R] (φ : MulAut R) (x : R) :
    φ * MulAut.conj x * φ⁻¹ = MulAut.conj (φ x) := by
  ext y
  simp [MulAut.conj_apply, map_mul, map_inv]

private theorem ggL45NtGlue_eq_inducedAut {K : Type*} [Group K] {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) {ψ : MulAut K} {φ : MulAut R}
    (h : LargeEvenInduces θ (fun k k' => k' = ψ k) φ) : φ = ggInducedAut θ ψ := by
  ext r
  obtain ⟨q, rfl⟩ := θ.surjective r
  induction q using QuotientGroup.induction_on with
  | H l =>
    rw [ggInducedAut_apply]
    exact h l (ψ l) rfl

private theorem ggL45NtGlue_isPElt_zpow {p : ℕ} {M : Type*} [Group M] {α : M}
    (h : GGL45IsPElt p α) (c : ℤ) : GGL45IsPElt p (α ^ c) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  calc (α ^ c) ^ p ^ k = (α ^ c) ^ ((p ^ k : ℕ) : ℤ) := by rw [← zpow_natCast]
    _ = α ^ (c * ((p ^ k : ℕ) : ℤ)) := by rw [zpow_mul]
    _ = α ^ (((p ^ k : ℕ) : ℤ) * c) := by rw [mul_comm]
    _ = (α ^ ((p ^ k : ℕ) : ℤ)) ^ c := by rw [zpow_mul]
    _ = (α ^ p ^ k) ^ c := by rw [zpow_natCast]
    _ = 1 := by rw [hk, one_zpow]

private theorem ggL45NtGlue_isPElt_of_conj {p : ℕ} {R : Type} [Group R] {r : R}
    (hinj : Function.Injective (MulAut.conj : R →* MulAut R))
    (h : GGL45IsPElt p (MulAut.conj r)) : GGL45IsPElt p r := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  have h1 : MulAut.conj (r ^ p ^ k) = 1 := by rw [map_pow, hk]
  exact hinj (by rw [h1, map_one])

private theorem ggL45NtGlue_conj_injective {R : Type} [Group R]
    (hθ : ∀ {r : R}, (∀ s : R, s * r = r * s) → r = 1) :
    Function.Injective (MulAut.conj : R →* MulAut R) := by
  rw [injective_iff_map_eq_one]
  intro r hr
  apply hθ
  intro s
  have h1 := congrArg (fun f : MulAut R => f s) hr
  simp only [MulAut.conj_apply, MulAut.one_apply] at h1
  calc s * r = (r * s * r⁻¹) * r := by rw [h1]
    _ = r * s := by group

private theorem ggL45NtGlue_inCIp_iff {p : ℕ} {K : Type*} [Group K] {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) (I : Set (MulAut R)) (E : Subgroup (MulAut K))
    (u : MulAut R) :
    GGL45InCIp p I θ E u ↔ GGL45NtCIp p I (E.map (ggInducedAut θ)) u := by
  constructor
  · rintro ⟨hI, hcomm, hp⟩
    refine ⟨hI, ?_, hp⟩
    intro e' he'
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp he'
    exact hcomm e he
  · rintro ⟨hI, hcomm, hp⟩
    refine ⟨hI, ?_, hp⟩
    intro e he
    exact hcomm (ggInducedAut θ e) (Subgroup.mem_map.mpr ⟨e, he, rfl⟩)

private noncomputable def ggL45NtGlue_aOf {K : Type*} [Group K] {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) (h : K) : MulAut R :=
  MulAut.conj (θ (h : K ⧸ Subgroup.center K))

private theorem ggL45NtGlue_ntCIp_of_InS {p : ℕ} {K : Type*} [Group K] {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) (I : Set (MulAut R))
    (hInn : ∀ r : R, MulAut.conj r ∈ I) (E : Subgroup (MulAut K)) (h : K)
    (hh : GGL45InS p E h) :
    GGL45NtCIp p I (E.map (ggInducedAut θ)) (ggL45NtGlue_aOf θ h) := by
  refine ⟨hInn _, ?_, ?_⟩
  · intro e' he'
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp he'
    have hfix : ggInducedAut θ e (θ (h : K ⧸ Subgroup.center K)) =
        θ (h : K ⧸ Subgroup.center K) := by
      rw [ggInducedAut_apply, hh.2 e he]
    have hconj : ggInducedAut θ e * ggL45NtGlue_aOf θ h * (ggInducedAut θ e)⁻¹ =
        ggL45NtGlue_aOf θ h := by
      rw [ggL45NtGlue_aOf, ggL45NtGlue_mul_conj_mul_inv, hfix]
    have hcomm : ggInducedAut θ e * ggL45NtGlue_aOf θ h =
        ggL45NtGlue_aOf θ h * ggInducedAut θ e := by
      calc ggInducedAut θ e * ggL45NtGlue_aOf θ h
          = ggInducedAut θ e * ggL45NtGlue_aOf θ h * (ggInducedAut θ e)⁻¹ *
              ggInducedAut θ e := by group
        _ = ggL45NtGlue_aOf θ h * ggInducedAut θ e := by rw [hconj]
    exact hcomm.symm
  · obtain ⟨k, hk⟩ := hh.1
    refine ⟨k, ?_⟩
    rw [ggL45NtGlue_aOf]
    rw [← map_pow]
    have hQ : (θ (h : K ⧸ Subgroup.center K)) ^ p ^ k = 1 := by
      rw [← map_pow, ← QuotientGroup.mk_pow, hk, QuotientGroup.mk_one, map_one]
    rw [hQ, map_one]

private theorem ggL45NtGlue_h2_commute {p : ℕ} (hp : p.Prime) {K : Type*} [Group K]
    {R : Type} [Group R] (θ : K ⧸ Subgroup.center K ≃* R) (I : Set (MulAut R))
    (E : Subgroup (MulAut K)) (hInn : ∀ r : R, MulAut.conj r ∈ I)
    (hZ' : ¬ p ∣ Nat.card (Subgroup.center K))
    (hconj_inj : Function.Injective (MulAut.conj : R →* MulAut R))
    (C1 : ∀ u v : MulAut R, GGL45NtCIp p I (E.map (ggInducedAut θ)) u →
      GGL45NtCIp p I (E.map (ggInducedAut θ)) v → u * v = v * u)
    (h t : K) (hh : GGL45InS p E h) (ht : GGL45InS p E t) : h * t = t * h := by
  have hah := ggL45NtGlue_ntCIp_of_InS θ I hInn E h hh
  have hat := ggL45NtGlue_ntCIp_of_InS θ I hInn E t ht
  have hcomm := C1 _ _ hah hat
  have h2 : MulAut.conj (θ (h : K ⧸ Subgroup.center K) * θ (t : K ⧸ Subgroup.center K)) =
      MulAut.conj (θ (t : K ⧸ Subgroup.center K) * θ (h : K ⧸ Subgroup.center K)) := by
    rw [map_mul, map_mul]
    exact hcomm
  have h3 : θ (h : K ⧸ Subgroup.center K) * θ (t : K ⧸ Subgroup.center K) =
      θ (t : K ⧸ Subgroup.center K) * θ (h : K ⧸ Subgroup.center K) := hconj_inj h2
  have h4 : (θ ((h * t : K) : K ⧸ Subgroup.center K)) =
      θ ((t * h : K) : K ⧸ Subgroup.center K) := by
    have := h3
    rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at this
    exact this
  have h5 : ((h * t : K) : K ⧸ Subgroup.center K) = ((t * h : K) : K ⧸ Subgroup.center K) :=
    θ.injective h4
  set c : K := (h * t)⁻¹ * (t * h) with hcdef
  have hcZ : c ∈ Subgroup.center K := by rw [hcdef]; exact QuotientGroup.eq.mp h5
  have hrel : h⁻¹ * t * h = t * c := by rw [hcdef]; group
  have hrel_pow : ∀ n : ℕ, h⁻¹ * t ^ n * h = (t * c) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, pow_succ, ← ih, ← hrel]
      group
  have hcomm_tc : Commute t c := (Subgroup.mem_center_iff.mp hcZ) t
  obtain ⟨k, hk⟩ := ht.1
  have hc_pow : c ^ p ^ k = 1 := by
    have h := hrel_pow (p ^ k)
    rw [hk] at h
    have h1 : (t * c) ^ p ^ k = 1 := by simpa using h.symm
    rw [show (t * c) ^ p ^ k = t ^ p ^ k * c ^ p ^ k from hcomm_tc.mul_pow _,
      hk, one_mul] at h1
    exact h1
  have hc_order : orderOf c ∣ p ^ k := orderOf_dvd_of_pow_eq_one hc_pow
  have hc_dvd : orderOf c ∣ Nat.card (Subgroup.center K) := by
    have h := orderOf_dvd_natCard (⟨c, hcZ⟩ : Subgroup.center K)
    rwa [← Subgroup.orderOf_coe] at h
  have hpdvd : ¬ p ∣ orderOf c := fun hpd => hZ' (hpd.trans hc_dvd)
  have hcop : Nat.Coprime (orderOf c) p := ((hp.coprime_iff_not_dvd).mpr hpdvd).symm
  have h1 : orderOf c = 1 := Nat.Coprime.eq_one_of_dvd (hcop.pow_right k) hc_order
  have hc1 : c = 1 := orderOf_eq_one_iff.mp h1
  have hfinal : (h * t)⁻¹ = (t * h)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← hcdef]
    exact hc1
  simpa using congrArg Inv.inv hfinal

private theorem ggL45NtGlue_h2_exponent {p : ℕ} (hp : p.Prime) {K : Type*} [Group K]
    {R : Type} [Group R] (θ : K ⧸ Subgroup.center K ≃* R) (I : Set (MulAut R))
    (E : Subgroup (MulAut K)) (ψ : MulAut K) (s : ℕ) (c : ℤ)
    (hInn : ∀ r : R, MulAut.conj r ∈ I)
    (hZ' : ¬ p ∣ Nat.card (Subgroup.center K))
    (hconj_inj : Function.Injective (MulAut.conj : R →* MulAut R))
    (C1 : ∀ u v : MulAut R, GGL45NtCIp p I (E.map (ggInducedAut θ)) u →
      GGL45NtCIp p I (E.map (ggInducedAut θ)) v → u * v = v * u)
    (C2 : ∀ u : MulAut R, GGL45NtCIp p I (E.map (ggInducedAut θ)) u →
      u ^ p ^ s = 1 ∧ ggInducedAut θ ψ * u * (ggInducedAut θ ψ)⁻¹ = u ^ c)
    (hEψ : ∀ e ∈ E, e * ψ = ψ * e) (h : K)
    (hh : GGL45InS p E h) : h ^ p ^ s = 1 ∧ ψ h = h ^ c := by
  have hah := ggL45NtGlue_ntCIp_of_InS θ I hInn E h hh
  obtain ⟨hC2a, hC2b⟩ := C2 _ hah
  have hmem : h ^ p ^ s ∈ Subgroup.center K := by
    have h1 : MulAut.conj ((θ (h : K ⧸ Subgroup.center K)) ^ p ^ s) = 1 := by
      rw [map_pow]
      exact hC2a
    have h2 : (θ (h : K ⧸ Subgroup.center K)) ^ p ^ s = 1 :=
      hconj_inj (by rw [h1, map_one])
    rw [← QuotientGroup.eq_one_iff]
    apply θ.injective
    rw [map_one, QuotientGroup.mk_pow, map_pow]
    exact h2
  obtain ⟨k, hk⟩ := hh.1
  have horder : orderOf (h ^ p ^ s) ∣ p ^ k :=
    (orderOf_pow_dvd (p ^ s)).trans (orderOf_dvd_of_pow_eq_one hk)
  have hdvd : orderOf (h ^ p ^ s) ∣ Nat.card (Subgroup.center K) := by
    have h := orderOf_dvd_natCard (⟨h ^ p ^ s, hmem⟩ : Subgroup.center K)
    rwa [← Subgroup.orderOf_coe] at h
  have hpdvd : ¬ p ∣ orderOf (h ^ p ^ s) := fun hpd => hZ' (hpd.trans hdvd)
  have hcop : Nat.Coprime (orderOf (h ^ p ^ s)) p := ((hp.coprime_iff_not_dvd).mpr hpdvd).symm
  have h1 : h ^ p ^ s = 1 :=
    orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (hcop.pow_right k) horder)
  refine ⟨h1, ?_⟩
  have hψS : GGL45InS p E (ψ h) := by
    refine ⟨?_, ?_⟩
    · obtain ⟨m, hm⟩ := hh.1
      exact ⟨m, by rw [← map_pow, hm, map_one]⟩
    · intro e he
      rw [← MulAut.mul_apply, hEψ e he, MulAut.mul_apply, hh.2 e he]
  have hcS : GGL45InS p E (h ^ c) := by
    refine ⟨ggL45NtGlue_isPElt_zpow hh.1 c, ?_⟩
    intro e he
    rw [map_zpow, hh.2 e he]
  have hcommψ : Commute (ψ h) (h ^ c) :=
    ggL45NtGlue_h2_commute hp θ I E hInn hZ' hconj_inj C1 (ψ h) (h ^ c) hψS hcS
  have himg : θ ((ψ h : K) : K ⧸ Subgroup.center K) = θ ((h ^ c : K) : K ⧸ Subgroup.center K) := by
    have hC2b' := hC2b
    rw [ggL45NtGlue_aOf, ggL45NtGlue_mul_conj_mul_inv, ← map_zpow] at hC2b'
    have h6 := hconj_inj hC2b'
    rw [ggInducedAut_apply, ← map_zpow, ← QuotientGroup.mk_zpow] at h6
    exact h6
  have hgZ : (ψ h)⁻¹ * (h ^ c) ∈ Subgroup.center K := by
    rw [← QuotientGroup.eq_one_iff]
    apply θ.injective
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv, map_one, himg,
      inv_mul_cancel]
  have hψpow : (ψ h) ^ p ^ s = 1 := by rw [← map_pow, h1, map_one]
  have hcpow : (h ^ c) ^ p ^ s = 1 := by
    calc (h ^ c) ^ p ^ s = (h ^ c) ^ ((p ^ s : ℕ) : ℤ) := by rw [← zpow_natCast]
      _ = h ^ (c * ((p ^ s : ℕ) : ℤ)) := by rw [zpow_mul]
      _ = h ^ (((p ^ s : ℕ) : ℤ) * c) := by rw [mul_comm]
      _ = (h ^ ((p ^ s : ℕ) : ℤ)) ^ c := by rw [zpow_mul]
      _ = (h ^ p ^ s) ^ c := by rw [zpow_natCast]
      _ = 1 := by rw [h1, one_zpow]
  have hg_pow : ((ψ h)⁻¹ * (h ^ c)) ^ p ^ s = 1 := by
    rw [Commute.mul_pow hcommψ.inv_left, inv_pow, hψpow, hcpow, inv_one, one_mul]
  have hg_order : orderOf ((ψ h)⁻¹ * (h ^ c)) ∣ p ^ s := orderOf_dvd_of_pow_eq_one hg_pow
  have hg_dvd : orderOf ((ψ h)⁻¹ * (h ^ c)) ∣ Nat.card (Subgroup.center K) := by
    have h := orderOf_dvd_natCard (⟨(ψ h)⁻¹ * (h ^ c), hgZ⟩ : Subgroup.center K)
    rwa [← Subgroup.orderOf_coe] at h
  have hpdvd' : ¬ p ∣ orderOf ((ψ h)⁻¹ * (h ^ c)) := fun hpd => hZ' (hpd.trans hg_dvd)
  have hcop' : Nat.Coprime (orderOf ((ψ h)⁻¹ * (h ^ c))) p :=
    ((hp.coprime_iff_not_dvd).mpr hpdvd').symm
  have hg1 : (ψ h)⁻¹ * (h ^ c) = 1 :=
    orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (hcop'.pow_right s) hg_order)
  exact inv_mul_eq_one.mp hg1

theorem ggL45NtGlue_H2 {p : ℕ} (hp : p.Prime) {K : Type*} [Group K]
    {R : Type} [Group R] (θ : K ⧸ Subgroup.center K ≃* R) (I : Set (MulAut R)) (ψ : MulAut K)
    (E : Subgroup (MulAut K)) (hInn : ∀ r : R, MulAut.conj r ∈ I)
    (hZ' : ¬ p ∣ Nat.card (Subgroup.center K))
    (hconj_inj : Function.Injective (MulAut.conj : R →* MulAut R))
    (hEψ : ∀ e ∈ E, e * ψ = ψ * e) (s : ℕ) (c : ℤ)
    (C1 : ∀ u v : MulAut R, GGL45NtCIp p I (E.map (ggInducedAut θ)) u →
      GGL45NtCIp p I (E.map (ggInducedAut θ)) v → u * v = v * u)
    (C2 : ∀ u : MulAut R, GGL45NtCIp p I (E.map (ggInducedAut θ)) u →
      u ^ p ^ s = 1 ∧ ggInducedAut θ ψ * u * (ggInducedAut θ ψ)⁻¹ = u ^ c)
    (C3 : ∀ u : MulAut R, GGL45NtCIp p I (E.map (ggInducedAut θ)) u → ∀ w ∈ I,
      (∀ e ∈ E.map (ggInducedAut θ), w * e = e * w) → w * u = u * w) :
    GGL45HTwo p I θ ψ E s c := by
  refine ⟨?_, ?_, ?_⟩
  · intro h t hh ht
    exact ggL45NtGlue_h2_commute hp θ I E hInn hZ' hconj_inj C1 h t hh ht
  · intro h hh
    exact ggL45NtGlue_h2_exponent hp θ I E ψ s c hInn hZ' hconj_inj C1 C2 hEψ h hh
  · intro α hα hαE h hh
    have hps : h ^ p ^ s = 1 :=
      (ggL45NtGlue_h2_exponent hp θ I E ψ s c hInn hZ' hconj_inj C1 C2 hEψ h hh).1
    have hbar : ggInducedAut θ α ∈ I := (ggL45_inducesIn_iff θ I α).mp hα
    have hcommE : ∀ e ∈ E.map (ggInducedAut θ),
        ggInducedAut θ α * e = e * ggInducedAut θ α := by
      intro e' he'
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp he'
      rw [← map_mul, ← map_mul, hαE e he]
    have hah := ggL45NtGlue_ntCIp_of_InS θ I hInn E h hh
    have hcomm := C3 _ hah _ hbar hcommE
    have hconjA : ggInducedAut θ α * ggL45NtGlue_aOf θ h * (ggInducedAut θ α)⁻¹ =
        ggL45NtGlue_aOf θ h := by
      rw [hcomm]
      group
    have hfix : ggInducedAut θ α (θ (h : K ⧸ Subgroup.center K)) =
        θ (h : K ⧸ Subgroup.center K) := by
      apply hconj_inj
      rw [← ggL45NtGlue_mul_conj_mul_inv]
      exact hconjA
    have hfix' : θ ((α h : K) : K ⧸ Subgroup.center K) =
        θ (h : K ⧸ Subgroup.center K) := by
      have := hfix
      rwa [ggInducedAut_apply] at this
    set g : K := (α h)⁻¹ * h with hgdef
    have hgZ : g ∈ Subgroup.center K := by
      rw [← QuotientGroup.eq_one_iff]
      apply θ.injective
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv, map_one, hfix',
        inv_mul_cancel]
    have hαh : (α h) ^ p ^ s = 1 := by rw [← map_pow, hps, map_one]
    have hrel : α h = h * g⁻¹ := by rw [hgdef]; group
    have hcomm' : Commute h g⁻¹ := (Subgroup.mem_center_iff.mp (inv_mem hgZ)) h
    have hg_pow : g ^ p ^ s = 1 := by
      rw [hrel, hcomm'.mul_pow, hps, one_mul, inv_pow] at hαh
      simpa using hαh
    have hg_order : orderOf g ∣ p ^ s := orderOf_dvd_of_pow_eq_one hg_pow
    have hg_dvd : orderOf g ∣ Nat.card (Subgroup.center K) := by
      have h := orderOf_dvd_natCard (⟨g, hgZ⟩ : Subgroup.center K)
      rwa [← Subgroup.orderOf_coe] at h
    have hpdvd : ¬ p ∣ orderOf g := fun hpd => hZ' (hpd.trans hg_dvd)
    have hcop : Nat.Coprime (orderOf g) p := ((hp.coprime_iff_not_dvd).mpr hpdvd).symm
    have hg1 : g = 1 :=
      orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (hcop.pow_right s) hg_order)
    exact inv_mul_eq_one.mp hg1

theorem ggL45NtGlue_H3 {p : ℕ} (hp : p.Prime) {K : Type} [Group K] [Finite K]
    {R : Type} [Group R] (θ : K ⧸ Subgroup.center K ≃* R) (I : Set (MulAut R))
    (E : Subgroup (MulAut K)) (hOut : ∀ u ∈ I, GGL45IsPElt p u → ∃ r : R, u = MulAut.conj r)
    (hZ' : ¬ p ∣ Nat.card (Subgroup.center K))
    (hconj_inj : Function.Injective (MulAut.conj : R →* MulAut R))
    (hE : IsElemAbelian p E) (s : ℕ) (hs : 2 ≤ s) (c : ℤ)
    (C4 : ∃ a₁ a₂ : MulAut R, GGL45NtCIp p I (E.map (ggInducedAut θ)) a₁ ∧
      GGL45NtCIp p I (E.map (ggInducedAut θ)) a₂ ∧
      ∀ i j : ℕ, (a₁ ^ p ^ (s - 1)) ^ i * (a₂ ^ p ^ (s - 1)) ^ j = 1 → p ∣ i ∧ p ∣ j) :
    GGL45HThree p E s := by
  obtain ⟨a₁, a₂, ha₁, ha₂, hindep⟩ := C4
  obtain ⟨r₁, hr₁⟩ := hOut a₁ ha₁.1 ha₁.2.2
  obtain ⟨r₂, hr₂⟩ := hOut a₂ ha₂.1 ha₂.2.2
  have hfix₁ : ∀ e ∈ E.map (ggInducedAut θ), e r₁ = r₁ := by
    intro e' he'
    have h := ha₁.2.1 e' he'
    have hconj : e' * MulAut.conj r₁ * e'⁻¹ = MulAut.conj r₁ := by
      rw [← hr₁]
      calc e' * a₁ * e'⁻¹ = (a₁ * e') * e'⁻¹ := by rw [h]
        _ = a₁ := by group
    apply hconj_inj
    rw [← ggL45NtGlue_mul_conj_mul_inv]
    exact hconj
  have hfix₂ : ∀ e ∈ E.map (ggInducedAut θ), e r₂ = r₂ := by
    intro e' he'
    have h := ha₂.2.1 e' he'
    have hconj : e' * MulAut.conj r₂ * e'⁻¹ = MulAut.conj r₂ := by
      rw [← hr₂]
      calc e' * a₂ * e'⁻¹ = (a₂ * e') * e'⁻¹ := by rw [h]
        _ = a₂ := by group
    apply hconj_inj
    rw [← ggL45NtGlue_mul_conj_mul_inv]
    exact hconj
  have hp₁ : GGL45IsPElt p r₁ :=
    ggL45NtGlue_isPElt_of_conj hconj_inj (by rw [← hr₁]; exact ha₁.2.2)
  have hp₂ : GGL45IsPElt p r₂ :=
    ggL45NtGlue_isPElt_of_conj hconj_inj (by rw [← hr₂]; exact ha₂.2.2)
  have hEp : IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup hE
  obtain ⟨q₁, hq₁⟩ := θ.surjective r₁
  obtain ⟨k₁, rfl⟩ := QuotientGroup.mk_surjective q₁
  have hk₁ : ∃ m : ℕ, k₁ ^ p ^ m ∈ Subgroup.center K := by
    obtain ⟨m, hm⟩ := hp₁
    refine ⟨m, ?_⟩
    rw [← QuotientGroup.eq_one_iff]
    apply θ.injective
    rw [map_one, QuotientGroup.mk_pow, map_pow, hq₁, hm]
  have hfix₁' : ∀ a ∈ E, ((a k₁ : K) : K ⧸ Subgroup.center K) =
      (k₁ : K ⧸ Subgroup.center K) := by
    intro a ha
    have h := hfix₁ (ggInducedAut θ a) (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩)
    rw [← hq₁, ggInducedAut_apply] at h
    exact θ.injective h
  obtain ⟨k₁', hk₁'q, hk₁'p, hk₁'fix⟩ :=
    ggL45Nt_exists_fixed_pElt_lift (k₀ := k₁) hp hZ' E hEp hk₁ hfix₁'
  have hr₁' : MulAut.conj (θ (k₁' : K ⧸ Subgroup.center K)) = a₁ := by
    rw [hk₁'q, hq₁, hr₁]
  obtain ⟨q₂, hq₂⟩ := θ.surjective r₂
  obtain ⟨k₂, rfl⟩ := QuotientGroup.mk_surjective q₂
  have hk₂ : ∃ m : ℕ, k₂ ^ p ^ m ∈ Subgroup.center K := by
    obtain ⟨m, hm⟩ := hp₂
    refine ⟨m, ?_⟩
    rw [← QuotientGroup.eq_one_iff]
    apply θ.injective
    rw [map_one, QuotientGroup.mk_pow, map_pow, hq₂, hm]
  have hfix₂' : ∀ a ∈ E, ((a k₂ : K) : K ⧸ Subgroup.center K) =
      (k₂ : K ⧸ Subgroup.center K) := by
    intro a ha
    have h := hfix₂ (ggInducedAut θ a) (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩)
    rw [← hq₂, ggInducedAut_apply] at h
    exact θ.injective h
  obtain ⟨k₂', hk₂'q, hk₂'p, hk₂'fix⟩ :=
    ggL45Nt_exists_fixed_pElt_lift (k₀ := k₂) hp hZ' E hEp hk₂ hfix₂'
  have hr₂' : MulAut.conj (θ (k₂' : K ⧸ Subgroup.center K)) = a₂ := by
    rw [hk₂'q, hq₂, hr₂]
  let F : K →* MulAut R :=
    (MulAut.conj).comp (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)))
  have hF₁ : (F k₁') ^ p ^ (s - 1) = a₁ ^ p ^ (s - 1) := by
    dsimp [F]
    rw [hr₁']
  have hF₂ : (F k₂') ^ p ^ (s - 1) = a₂ ^ p ^ (s - 1) := by
    dsimp [F]
    rw [hr₂']
  have hb₁Z : k₁' ^ p ^ (s - 1) ∉ Subgroup.center K := by
    intro hmem
    have hZ1 : θ ((k₁' ^ p ^ (s - 1) : K) : K ⧸ Subgroup.center K) = 1 := by
      rw [(QuotientGroup.eq_one_iff _).mpr hmem, map_one]
    have hr1pow : r₁ ^ p ^ (s - 1) = 1 := by
      rw [QuotientGroup.mk_pow, map_pow, hk₁'q, hq₁] at hZ1
      exact hZ1
    have ha1pow : a₁ ^ p ^ (s - 1) = 1 := by
      rw [hr₁, ← map_pow, hr1pow, map_one]
    have hcontra := hindep 1 0 (by rw [ha1pow, pow_one, pow_zero, mul_one])
    exact hp.not_dvd_one hcontra.1
  refine ⟨⟨k₁', ⟨hk₁'p, hk₁'fix⟩, hb₁Z⟩, ?_⟩
  refine ⟨k₁' ^ p ^ (s - 1), k₂' ^ p ^ (s - 1), ?_, ?_, hb₁Z, ?_⟩
  · exact ⟨k₁', ⟨hk₁'p, hk₁'fix⟩, rfl⟩
  · exact ⟨k₂', ⟨hk₂'p, hk₂'fix⟩, rfl⟩
  · intro i j hij
    have h0 : F ((k₁' ^ p ^ (s - 1)) ^ i * (k₂' ^ p ^ (s - 1)) ^ j) = 1 := by
      rw [hij, map_one]
    simp only [map_mul, map_pow, hF₁, hF₂] at h0
    exact hindep i j h0

theorem ggL45TorusH123_of_core {p : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {I F : Set (MulAut R)} (hsimp : GGL45NtSimp R I F) (hrec : GGL45NtRec p R I F)
    (hcore : GGL45NtCore p R I F) {K : Type} [Group K] [Finite K]
    (θ : K ⧸ Subgroup.center K ≃* R) (hK : commutator K = ⊤)
    {lab : LargeEvenLabel} {ψ : MulAut K} {E : Subgroup (MulAut K)}
    (hyp : GGL45TorusKGHyp p lab I F θ ψ E) : GGL45TorusH123 p I θ ψ E := by
  have hnab := ggL45Nt_nonabelian_of_kghyp hp θ hK hyp
  have hS := hsimp hnab
  obtain ⟨hInn, hOut, hZ⟩ := hrec hS hnab
  obtain ⟨hψp, hfld, hE, hEcard, _hD4, hEI, hEψ, hsatK, _hRk, _hPi⟩ := hyp
  have hinj : Function.Injective (ggInducedAut θ) := ggInducedAut_injective_of_perfect hK θ
  have hconj_inj : Function.Injective (MulAut.conj : R →* MulAut R) :=
    ggL45NtGlue_conj_injective (fun {r} hr => ggL45Nt_eq_one_of_forall_commute hK θ hr)
  have hZ' : ¬ p ∣ Nat.card (Subgroup.center K) := by
    refine hZ K (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))) ?_ ?_ hK
    · exact θ.surjective.comp (QuotientGroup.mk'_surjective _)
    · intro x hx
      rw [MonoidHom.mem_ker] at hx
      have h1 : (QuotientGroup.mk' (Subgroup.center K)) x = 1 := by
        apply θ.injective
        rw [map_one]
        exact hx
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hI' : ∀ e ∈ E.map (ggInducedAut θ), e ∈ I := by
    intro e he
    obtain ⟨e₀, he₀, rfl⟩ := Subgroup.mem_map.mp he
    exact (ggL45_inducesIn_iff θ I e₀).mp (hEI e₀ he₀)
  have hE' : IsElemAbelian p (E.map (ggInducedAut θ)) :=
    CFSG.Open.IsElemAbelian.map hE (ggInducedAut θ)
  have hcard' : p ^ 2 ≤ Nat.card (E.map (ggInducedAut θ)) := by
    rw [Subgroup.card_map_of_injective hinj]
    exact hEcard
  obtain ⟨f, hf, u, hu, hord, hind⟩ := hfld
  have hfld' : ∃ f ∈ F, ∃ u ∈ I, orderOf f = p ∧ ggInducedAut θ ψ = u * f * u⁻¹ :=
    ⟨f, hf, u, hu, hord, (ggL45NtGlue_eq_inducedAut θ hind).symm⟩
  have hψ' : (ggInducedAut θ ψ) ^ p = 1 := by rw [← map_pow, hψp, map_one]
  have hcomm' : ∀ e ∈ E.map (ggInducedAut θ),
      e * ggInducedAut θ ψ = ggInducedAut θ ψ * e := by
    intro e' he'
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp he'
    rw [← map_mul, ← map_mul, hEψ e he]
  have satR : ∀ r : R, r ^ p = 1 → (∀ e ∈ E.map (ggInducedAut θ), e r = r) →
      ggInducedAut θ ψ r = r → MulAut.conj r ∈ E.map (ggInducedAut θ) :=
    ggL45Nt_satR_of_satK hp θ hZ' hE hψp hEψ hsatK
  obtain ⟨s, hs, c, k, hk, hc, C1, C2, C3, C4⟩ :=
    hcore hS hnab (E.map (ggInducedAut θ)) (ggInducedAut θ ψ) hE' hcard' hI' hψ' hfld' hcomm' satR
  refine ⟨s, hs, c, k, hk, hc, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro u v hu hv
      exact C1 u v ((ggL45NtGlue_inCIp_iff θ I E u).mp hu)
        ((ggL45NtGlue_inCIp_iff θ I E v).mp hv)
    · intro u hu
      exact C2 u ((ggL45NtGlue_inCIp_iff θ I E u).mp hu)
  · exact ggL45NtGlue_H2 hp θ I ψ E hInn hZ' hconj_inj hEψ s c C1 C2 C3
  · exact ggL45NtGlue_H3 hp θ I E hOut hZ' hconj_inj hE s hs c C4

end CFSG.StandardType
