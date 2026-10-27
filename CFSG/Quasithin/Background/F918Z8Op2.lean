module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Quasithin

theorem opq2_card_eq_inf_mul_relIndex {G : Type*} [Group G] (K H : Subgroup G) :
    Nat.card H = Nat.card ↥(H ⊓ K) * K.relIndex H := by
  rw [← Subgroup.relIndex_bot_left, ← Subgroup.relIndex_bot_left,
    ← Subgroup.inf_relIndex_right K H, inf_comm K H]
  exact (Subgroup.relIndex_mul_relIndex ⊥ (H ⊓ K) H bot_le inf_le_left).symm

theorem opq2_orderOf_of_pow {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {x : G} {e : ℕ}
    (he : 1 ≤ e) (h : orderOf (x ^ p) = p ^ e) : orderOf x = p ^ (e + 1) := by
  rw [orderOf_pow' x hp.ne_zero] at h
  by_cases hd : p ∣ orderOf x
  · rw [Nat.gcd_eq_right hd, Nat.div_eq_iff_eq_mul_left hp.pos hd] at h
    rw [h, pow_succ]
  · rw [Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd hp).mpr hd).symm,
      Nat.div_one] at h
    exact absurd (h ▸ dvd_pow_self p (by omega : e ≠ 0)) hd

theorem opq2_core {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {K : Subgroup Γ} [K.Normal] {g h w : Γ} {e : ℕ} (he : 1 ≤ e)
    (hgw : g ^ p = w) (hhw : h ^ p = w⁻¹) (hord : orderOf w = p ^ e)
    (hwc : ∀ x : Γ, x * w = w * x) (hgK : g ∉ K) (hwK : w ∈ K) (hhg : h * g⁻¹ ∈ K)
    (hΓ : ∀ x : Γ, ∃ (i : ℤ) (k : Γ), k ∈ K ∧ x = g ^ i * k)
    (hKp : ¬ p ^ (e + 1) ∣ Nat.card K) : False := by
  have hp : p.Prime := Fact.out
  have hog : orderOf g = p ^ (e + 1) := opq2_orderOf_of_pow hp he (by rw [hgw]; exact hord)
  have hoh : orderOf h = p ^ (e + 1) :=
    opq2_orderOf_of_pow hp he (by rw [hhw, orderOf_inv]; exact hord)
  have hq1 : ((g : Γ) : Γ ⧸ K) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, hgw]; exact (QuotientGroup.eq_one_iff _).mpr hwK
  have hq2 : ((g : Γ) : Γ ⧸ K) ≠ 1 := fun hq => hgK ((QuotientGroup.eq_one_iff _).mp hq)
  have hqo : orderOf ((g : Γ) : Γ ⧸ K) = p := orderOf_eq_prime hq1 hq2
  have hqgen : ∀ y : Γ ⧸ K, y ∈ Subgroup.zpowers ((g : Γ) : Γ ⧸ K) := by
    intro y
    induction y using QuotientGroup.induction_on with | H x => ?_
    obtain ⟨i, k, hk, rfl⟩ := hΓ x
    refine ⟨i, ?_⟩
    show (g : Γ ⧸ K) ^ i = ((g ^ i * k : Γ) : Γ ⧸ K)
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow, (QuotientGroup.eq_one_iff k).mpr hk, mul_one]
  have hidx : K.index = p := by
    rw [Subgroup.index, ← hqo]
    exact (orderOf_eq_card_of_forall_mem_zpowers hqgen).symm
  have hcard : Nat.card Γ = Nat.card K * p := by
    rw [← hidx]; exact (Subgroup.card_mul_index K).symm
  have hdvd : p ^ (e + 1) ∣ Nat.card Γ := by
    rw [← hog, ← Nat.card_zpowers]
    exact Subgroup.card_subgroup_dvd_card _
  have hndvd : ¬ p ^ (e + 2) ∣ Nat.card Γ := by
    intro h2
    rw [hcard, pow_succ] at h2
    exact hKp (Nat.dvd_of_mul_dvd_mul_right hp.pos h2)
  have hfac : (Nat.card Γ).factorization p = e + 1 := by
    apply le_antisymm
    · by_contra hlt
      exact hndvd ((hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').mpr (by omega))
    · exact (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hdvd
  let P₁ : Sylow p Γ := Sylow.ofCard (Subgroup.zpowers g) (by rw [Nat.card_zpowers, hog, hfac])
  let P₂ : Sylow p Γ := Sylow.ofCard (Subgroup.zpowers h) (by rw [Nat.card_zpowers, hoh, hfac])
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq Γ P₁ P₂
  have hhP₂ : h ∈ (P₂ : Subgroup Γ) := Subgroup.mem_zpowers h
  rw [← hx, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hhP₂
  change (MulAut.conj x)⁻¹ • h ∈ Subgroup.zpowers g at hhP₂
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hhP₂
  simp [MulAut.smul_def] at hj
  have hhx : h = x * g ^ j * x⁻¹ := by rw [hj]; group
  have hwj : w ^ j = w⁻¹ := by
    have h1 : h ^ p = x * (g ^ j) ^ p * x⁻¹ := by rw [hhx, conj_pow]
    have h2 : (g ^ j) ^ p = w ^ j := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hgw]
    have h3 : x * w ^ j = w ^ j * x := ((Commute.zpow_right (hwc x) j)).eq
    rw [h2, h3, mul_inv_cancel_right] at h1
    rw [← hhw, h1]
  have hj1 : (p : ℤ) ∣ j + 1 := by
    have h1 : w ^ (j + 1) = 1 := by rw [zpow_add_one, hwj, inv_mul_cancel]
    have h2 : (orderOf w : ℤ) ∣ j + 1 := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rw [hord] at h2
    exact (dvd_pow_self (p : ℤ) (by omega : e ≠ 0)).trans (by exact_mod_cast h2)
  have hmk : ((h : Γ) : Γ ⧸ K) = (g : Γ ⧸ K) := by
    have := (QuotientGroup.eq_one_iff _).mpr hhg
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_inv_eq_one] at this
    exact this
  have hmk2 : ((h : Γ) : Γ ⧸ K) = (g : Γ ⧸ K) ^ j := by
    rw [hhx, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_zpow]
    obtain ⟨i', hi'⟩ := hqgen (x : Γ ⧸ K)
    rw [← hi']
    show (g : Γ ⧸ K) ^ i' * (g : Γ ⧸ K) ^ j * ((g : Γ ⧸ K) ^ i')⁻¹ = (g : Γ ⧸ K) ^ j
    rw [(Commute.zpow_zpow_self (g : Γ ⧸ K) i' j).eq, mul_inv_cancel_right]
  have hj3 : (p : ℤ) ∣ j - 1 := by
    have h1 : (g : Γ ⧸ K) ^ (j - 1) = 1 := by
      rw [zpow_sub_one, ← hmk2, hmk, mul_inv_cancel]
    have h2 : (orderOf (g : Γ ⧸ K) : ℤ) ∣ j - 1 := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rwa [hqo] at h2
  have h2 : p ∣ 2 := by
    have := dvd_sub hj1 hj3
    rw [show (j + 1) - (j - 1) = 2 by ring] at this
    exact_mod_cast this
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)

theorem opq_sylow_glue {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {L' : Subgroup G}
    {g : G} (hgn : ∀ x ∈ L', g * x * g⁻¹ ∈ L') (hgp : ∃ k : ℕ, g ^ (p ^ k) = 1) :
    ∃ Q : Subgroup G, IsPGroup p Q ∧ g ∈ Q ∧ Q ≤ L' ⊔ Subgroup.zpowers g ∧
      ∃ m : ℕ, Nat.card L' = Nat.card ↥(Q ⊓ L') * m ∧ ¬ p ∣ m := by
  have hp : p.Prime := Fact.out
  obtain ⟨k, hk⟩ := hgp
  set H : Subgroup G := L' ⊔ Subgroup.zpowers g
  have hgH : g ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
  have hnorm : H ≤ Subgroup.normalizer (L' : Set G) :=
    sup_le Subgroup.le_normalizer
      (Subgroup.zpowers_le.mpr (Subgroup.mem_normalizer_fintype hgn))
  set a : H := ⟨g, hgH⟩
  have hak : a ^ p ^ k = 1 := Subtype.ext (by simpa using hk)
  have hgp' : IsPGroup p (Subgroup.zpowers a) := by
    rw [isPGroup_iff_pow_pow_eq_one]
    rintro ⟨x, hx⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    refine ⟨k, Subtype.ext ?_⟩
    show (a ^ j) ^ p ^ k = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hak, one_zpow]
  obtain ⟨Q', hQ'⟩ := hgp'.exists_le_sylow
  have haQ : a ∈ (Q' : Subgroup H) := hQ' (Subgroup.mem_zpowers a)
  set Q : Subgroup G := (Q' : Subgroup H).map H.subtype with hQ
  have hQH : Q ≤ H := Subgroup.map_subtype_le _
  have hgQ : g ∈ Q := ⟨a, haQ, rfl⟩
  have hQcard : Nat.card Q = p ^ (Nat.card H).factorization p := by
    rw [hQ, Subgroup.card_map_of_injective H.subtype_injective, Sylow.card_eq_multiplicity]
  refine ⟨Q, Q'.isPGroup'.map H.subtype, hgQ, hQH,
    Nat.card H / p ^ (Nat.card H).factorization p, ?_, Nat.not_dvd_ordCompl hp Nat.card_pos.ne'⟩
  have hLQ : Q ⊔ L' = H := by
    refine le_antisymm (sup_le hQH le_sup_left) (sup_le le_sup_right ?_)
    exact Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left hgQ)
  have hrel : L'.relIndex Q = L'.relIndex H := by
    let _ := Subgroup.normal_subgroupOf_of_le_normalizer (hQH.trans hnorm)
    let _ := Subgroup.normal_subgroupOf_sup_of_le_normalizer (hQH.trans hnorm)
    have := Nat.card_congr
      (QuotientGroup.quotientInfEquivProdNormalizerQuotient Q L' (hQH.trans hnorm)).toEquiv
    rw [← hLQ]
    exact this
  have h1 : Nat.card Q = Nat.card ↥(Q ⊓ L') * L'.relIndex H := by
    rw [← hrel]; exact opq2_card_eq_inf_mul_relIndex L' Q
  have h2 : Nat.card H = Nat.card L' * L'.relIndex H := by
    have := opq2_card_eq_inf_mul_relIndex L' H
    rwa [inf_eq_right.mpr le_sup_left] at this
  have hD : 0 < L'.relIndex H := by
    refine Nat.pos_of_ne_zero fun h => ?_
    rw [h] at h2
    have : 0 < Nat.card H := Nat.card_pos
    omega
  have hd : Nat.card H = Nat.card Q * (Nat.card H / p ^ (Nat.card H).factorization p) := by
    rw [hQcard]
    exact (Nat.ordProj_mul_ordCompl_eq_self (Nat.card H) p).symm
  apply Nat.eq_of_mul_eq_mul_right hD
  calc Nat.card L' * L'.relIndex H = Nat.card H := h2.symm
    _ = Nat.card Q * (Nat.card H / p ^ (Nat.card H).factorization p) := hd
    _ = Nat.card ↥(Q ⊓ L') * (Nat.card H / p ^ (Nat.card H).factorization p) *
        L'.relIndex H := by
      rw [h1]; ring

theorem opq_sylow_trick {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {L' : Subgroup G} {g w τ : G} {e : ℕ} (he : 1 ≤ e) (hgn : ∀ x ∈ L', g * x * g⁻¹ ∈ L')
    (hgw : g ^ p = w) (hw : w ∈ L') (hord : orderOf w = p ^ e) (hsyl : ¬ p ^ (e + 1) ∣ Nat.card L')
    (hτ : τ ∈ L') (hτ2 : τ * τ = 1) (hτw : τ * w * τ⁻¹ = w⁻¹) : False := by
  have hp : p.Prime := Fact.out
  have hog : orderOf g = p ^ (e + 1) := opq2_orderOf_of_pow hp he (by rw [hgw]; exact hord)
  have hgL : g ∉ L' := fun hg => hsyl (hog ▸ L'.orderOf_dvd_natCard hg)
  have hgc : Commute g w := hgw ▸ Commute.self_pow g p
  set C : Subgroup G := L' ⊓ Subgroup.centralizer {w} with hC
  have hmemC : ∀ x, x ∈ C ↔ x ∈ L' ∧ Commute x w := by
    intro x
    simp [hC, Subgroup.mem_centralizer_iff, Commute, SemiconjBy, eq_comm]
  have hwC : w ∈ C := (hmemC w).mpr ⟨hw, Commute.refl w⟩
  have hgnC : ∀ x ∈ C, g * x * g⁻¹ ∈ C := by
    intro x hx
    obtain ⟨hxL, hxw⟩ := (hmemC x).mp hx
    exact (hmemC _).mpr ⟨hgn x hxL, (hgc.mul_left hxw).mul_left hgc.inv_left⟩
  have hgnorm : g ∈ Subgroup.normalizer (C : Set G) := Subgroup.mem_normalizer_fintype hgnC
  set D : Subgroup G := C ⊔ Subgroup.zpowers g
  have hDn : D ≤ Subgroup.normalizer (C : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hgnorm)
  have hDc : ∀ x ∈ D, Commute x w := by
    have : D ≤ Subgroup.centralizer {w} := by
      refine sup_le inf_le_right (Subgroup.zpowers_le.mpr ?_)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff.mp hy]
      exact hgc.symm.eq
    intro x hx
    have := Subgroup.mem_centralizer_iff.mp (this hx) w rfl
    exact this.symm
  have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ2
  have hτ1 : τ * w = w⁻¹ * τ := mul_inv_eq_iff_eq_mul.mp hτw
  have hA : g⁻¹ * w = w * g⁻¹ := hgc.inv_left.eq
  have hB : τ⁻¹ * w = w⁻¹ * τ⁻¹ := by rw [hτi]; exact hτ1
  have hC' : g * w⁻¹ = w⁻¹ * g := hgc.inv_right.eq
  have hE : τ * w⁻¹ = w * τ := by
    calc τ * w⁻¹ = w * (w⁻¹ * τ) * w⁻¹ := by group
      _ = w * (τ * w) * w⁻¹ := by rw [hτ1]
      _ = w * τ := by group
  have huw : Commute (τ * g * τ⁻¹ * g⁻¹) w := by
    show τ * g * τ⁻¹ * g⁻¹ * w = w * (τ * g * τ⁻¹ * g⁻¹)
    calc τ * g * τ⁻¹ * g⁻¹ * w = τ * g * τ⁻¹ * (g⁻¹ * w) := by group
      _ = τ * g * τ⁻¹ * (w * g⁻¹) := by rw [hA]
      _ = τ * g * (τ⁻¹ * w) * g⁻¹ := by group
      _ = τ * g * (w⁻¹ * τ⁻¹) * g⁻¹ := by rw [hB]
      _ = τ * (g * w⁻¹) * τ⁻¹ * g⁻¹ := by group
      _ = τ * (w⁻¹ * g) * τ⁻¹ * g⁻¹ := by rw [hC']
      _ = (τ * w⁻¹) * g * τ⁻¹ * g⁻¹ := by group
      _ = (w * τ) * g * τ⁻¹ * g⁻¹ := by rw [hE]
      _ = w * (τ * g * τ⁻¹ * g⁻¹) := by group
  have huL : τ * g * τ⁻¹ * g⁻¹ ∈ L' := by
    have := L'.mul_mem hτ (hgn _ (L'.inv_mem hτ))
    simpa [mul_assoc] using this
  have huC : τ * g * τ⁻¹ * g⁻¹ ∈ C := (hmemC _).mpr ⟨huL, huw⟩
  have hhp : (τ * g * τ⁻¹) ^ p = w⁻¹ := by rw [conj_pow, hgw, hτw]
  have hgD : g ∈ D := Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
  have hwD : w ∈ D := Subgroup.mem_sup_left hwC
  have hhD : τ * g * τ⁻¹ ∈ D := by
    have : τ * g * τ⁻¹ = (τ * g * τ⁻¹ * g⁻¹) * g := by group
    rw [this]
    exact D.mul_mem (Subgroup.mem_sup_left huC) hgD
  have hKn : (C.subgroupOf D).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hDn
  have hΓ : ∀ x : D, ∃ (i : ℤ) (k : D), k ∈ C.subgroupOf D ∧ x = (⟨g, hgD⟩ : D) ^ i * k := by
    rintro ⟨x, hx⟩
    have hx' : x ∈ ((Subgroup.zpowers g ⊔ C : Subgroup G) : Set G) := by
      rw [sup_comm]; exact hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (Subgroup.zpowers_le.mpr hgnorm)] at hx'
    obtain ⟨a, ha, c, hc, rfl⟩ := hx'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact ⟨i, ⟨c, Subgroup.mem_sup_left hc⟩, Subgroup.mem_subgroupOf.mpr hc, Subtype.ext rfl⟩
  have hKp : ¬ p ^ (e + 1) ∣ Nat.card (C.subgroupOf D) := by
    intro hd
    have hCD : C ≤ D := le_sup_left
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCD).toEquiv] at hd
    exact hsyl (hd.trans (Subgroup.card_dvd_of_le inf_le_left))
  exact opq2_core (K := C.subgroupOf D) hp2 he (g := ⟨g, hgD⟩) (h := ⟨τ * g * τ⁻¹, hhD⟩)
    (w := ⟨w, hwD⟩) (Subtype.ext hgw) (Subtype.ext hhp)
    (by rw [Subgroup.orderOf_mk]; exact hord) (fun x => Subtype.ext (hDc x.1 x.2).eq)
    (fun hmem => hgL ((hmemC g).mp (Subgroup.mem_subgroupOf.mp hmem)).1)
    (Subgroup.mem_subgroupOf.mpr hwC) (Subgroup.mem_subgroupOf.mpr (by simpa using huC)) hΓ hKp

end CFSG.Quasithin
