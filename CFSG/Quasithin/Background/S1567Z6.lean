module

public import CFSG.Quasithin.Background.S1567Y

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

namespace S1567

section Abstract

theorem card_mulAut_kleinFour (X : Type*) [Group X] [IsKleinFour X] : Nat.card (MulAut X) = 6 := by
  rw [Nat.card_congr (CFSG.kleinFourAutomorphismEquivSymmetricThree X).toEquiv, Nat.card_perm]
  simp [Nat.factorial]

theorem mulAut_eq_one_of_commute_two_pow {X : Type*} [Group X] [IsKleinFour X] (ε γ : MulAut X)
    (hε1 : ε ≠ 1) (hε3 : ε ^ 3 = 1) (hc : ε * γ = γ * ε) (n : ℕ) (hγ : γ ^ 2 ^ n = 1) : γ = 1 := by
  by_contra hγ1
  have hcard := card_mulAut_kleinFour X
  have hd1 : orderOf γ ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hγ
  have hd2 : orderOf γ ∣ 6 := hcard ▸ orderOf_dvd_natCard γ
  have hcop : Nat.Coprime (orderOf γ) 3 :=
    Nat.Coprime.coprime_dvd_left hd1 (Nat.Coprime.pow_left n (by norm_num))
  have hd : orderOf γ ∣ 2 := hcop.dvd_of_dvd_mul_right (by simpa using hd2)
  exact mulAut_noncomm ε γ hε1 hε3 hγ1 (orderOf_dvd_iff_pow_eq_one.mp hd) hc

theorem eq_of_card_le_two {N : Type*} [Group N] [Finite N] (h : Nat.card N ≤ 2) {a b : N}
    (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
  classical
  by_contra hab
  have : Fintype N := Fintype.ofFinite N
  have h3 : ({1, a, b} : Finset N).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hab]
    simp [ha.symm, hb.symm]
  have := Finset.card_le_univ ({1, a, b} : Finset N)
  rw [h3, ← Nat.card_eq_fintype_card] at this
  omega

theorem eq_one_of_normal_two_group {X : Type*} [Group X] [IsKleinFour X] {H : Type*} [Group H]
    (φ : H →* MulAut X) {D : Subgroup H} (hD2 : ∀ d ∈ D, ∃ n : ℕ, φ d ^ 2 ^ n = 1) {h : H}
    (hhD : ∀ d ∈ D, h * d * h⁻¹ ∈ D) (hh1 : φ h ≠ 1) (hh3 : φ h ^ 3 = 1) (d : H) (hd : d ∈ D) :
    φ d = 1 := by
  classical
  have hcard := card_mulAut_kleinFour X
  have : Finite (MulAut X) := Nat.finite_of_card_ne_zero (by omega)
  set N : Subgroup (MulAut X) := D.map φ with hN
  have hp : IsPGroup 2 ↥N := by
    intro x
    obtain ⟨d', hd', hx⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨n, hn⟩ := hD2 d' hd'
    exact ⟨n, Subtype.ext (by simp [← hx, hn])⟩
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hdvd : Nat.card ↥N ∣ 6 := hcard ▸ Subgroup.card_subgroup_dvd_card N
  have hle : Nat.card ↥N ≤ 2 := by
    rw [hk] at hdvd ⊢
    have hk1 : k ≤ 1 := by
      by_contra hk2
      have h4 : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
      have h46 := h4.trans hdvd
      norm_num at h46
    interval_cases k <;> simp
  by_contra hne
  have hγ : φ d ∈ N := Subgroup.mem_map_of_mem φ hd
  have hγ' : φ h * φ d * (φ h)⁻¹ ∈ N := by
    have e : φ (h * d * h⁻¹) = φ h * φ d * (φ h)⁻¹ := by simp [map_mul, map_inv]
    rw [← e]
    exact Subgroup.mem_map_of_mem φ (hhD d hd)
  have hγ'1 : φ h * φ d * (φ h)⁻¹ ≠ 1 := by
    intro h1
    apply hne
    have := congrArg (fun z => (φ h)⁻¹ * z * φ h) h1
    simpa [mul_assoc] using this
  have heq := eq_of_card_le_two hle (a := (⟨φ d, hγ⟩ : ↥N)) (b := ⟨_, hγ'⟩)
    (fun h0 => hne (congrArg Subtype.val h0)) (fun h0 => hγ'1 (congrArg Subtype.val h0))
  have hc : φ h * φ d = φ d * φ h := by
    have := congrArg Subtype.val heq
    simp only at this
    calc φ h * φ d = φ h * φ d * (φ h)⁻¹ * φ h := by simp [mul_assoc]
      _ = φ d * φ h := by rw [← this]
  obtain ⟨n, hn⟩ := hD2 d hd
  exact hne (mulAut_eq_one_of_commute_two_pow (φ h) (φ d) hh1 hh3 hc n hn)

end Abstract

section BarAut

variable {G : Type} [Group G] {V E : Subgroup G}

@[expose] noncomputable def barAut [IsMulCommutative ↥V] (g : G)
    (hgV : g ∈ Subgroup.normalizer (V : Set G)) (hgE : g ∈ Subgroup.normalizer (E : Set G)) :
    MulAut (↥V ⧸ E.subgroupOf V) :=
  haveI : (E.subgroupOf V).Normal := Subgroup.normal_of_isMulCommutative _
  QuotientGroup.congr (E.subgroupOf V) (E.subgroupOf V) (conjAct V ⟨g, hgV⟩) (by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      show g * (y : G) * g⁻¹ ∈ E
      exact (Subgroup.mem_normalizer_iff.mp hgE y).mp hy
    · intro hx
      refine ⟨⟨g⁻¹ * (x : G) * g, ?_⟩, ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hgV) x).mp x.2 |>
          fun h => by simpa using h
      · rw [Subgroup.mem_subgroupOf]
        have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hgE) (x : G)).mp
          (Subgroup.mem_subgroupOf.mp hx)
        simpa using this
      · apply Subtype.ext
        show g * (g⁻¹ * (x : G) * g) * g⁻¹ = x
        group)

theorem barAut_mk [IsMulCommutative ↥V] {g : G}
    (hgV : g ∈ Subgroup.normalizer (V : Set G)) (hgE : g ∈ Subgroup.normalizer (E : Set G))
    (v : ↥V) :
    haveI : (E.subgroupOf V).Normal := Subgroup.normal_of_isMulCommutative _
    barAut g hgV hgE (QuotientGroup.mk v) =
      QuotientGroup.mk ⟨g * (v : G) * g⁻¹, (Subgroup.mem_normalizer_iff.mp hgV v).mp v.2⟩ := by
  have : (E.subgroupOf V).Normal := Subgroup.normal_of_isMulCommutative _
  unfold barAut
  rw [QuotientGroup.congr_mk]
  congr 1

theorem barAut_pow_mk [IsMulCommutative ↥V] {g : G}
    (hgV : g ∈ Subgroup.normalizer (V : Set G)) (hgE : g ∈ Subgroup.normalizer (E : Set G))
    (m : ℕ) (v : ↥V) :
    haveI : (E.subgroupOf V).Normal := Subgroup.normal_of_isMulCommutative _
    (barAut g hgV hgE ^ m) (QuotientGroup.mk v) =
      QuotientGroup.mk ⟨g ^ m * (v : G) * (g ^ m)⁻¹,
        (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).pow_mem hgV m) v).mp v.2⟩ := by
  have : (E.subgroupOf V).Normal := Subgroup.normal_of_isMulCommutative _
  induction m generalizing v with
  | zero =>
    show QuotientGroup.mk v = _
    congr 1
    apply Subtype.ext
    simp
  | succ m ih =>
    rw [pow_succ, MulAut.mul_apply, barAut_mk hgV hgE, ih]
    congr 1
    apply Subtype.ext
    show g ^ m * (g * (v : G) * g⁻¹) * (g ^ m)⁻¹ = g ^ (m + 1) * (v : G) * (g ^ (m + 1))⁻¹
    rw [pow_succ']
    group

theorem isKleinFour_quot (hV : IsElemAbelian 2 V) (hEV : E ≤ V) (hV16 : Nat.card ↥V = 16)
    (hE4 : Nat.card ↥E = 4) :
    haveI : (E.subgroupOf V).Normal := haveI := hV.1; Subgroup.normal_of_isMulCommutative _
    IsKleinFour (↥V ⧸ E.subgroupOf V) := by
  have := hV.1
  have : (E.subgroupOf V).Normal := Subgroup.normal_of_isMulCommutative _
  have hK : Nat.card ↥(E.subgroupOf V) = 4 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEV).toEquiv).trans hE4
  have hcard : Nat.card (↥V ⧸ E.subgroupOf V) = 4 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (E.subgroupOf V)
    rw [hV16, hK] at h
    omega
  have hsq : ∀ x : ↥V ⧸ E.subgroupOf V, x ^ 2 = 1 := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H v =>
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      have : v ^ 2 = 1 := Subtype.ext (by simpa using hV.2 v v.2)
      rw [this]
      exact Subgroup.one_mem _
  have hexp : Monoid.exponent (↥V ⧸ E.subgroupOf V) = 2 := by
    have hdvd : Monoid.exponent (↥V ⧸ E.subgroupOf V) ∣ 2 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one hsq
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exfalso
      have hsub : Subsingleton (↥V ⧸ E.subgroupOf V) := Monoid.exp_eq_one_iff.mp h1
      have := Nat.card_of_subsingleton (1 : ↥V ⧸ E.subgroupOf V)
      omega
    · exact h2
  exact ⟨hcard, hexp⟩

theorem barAut_eq_one_iff [IsMulCommutative ↥V] {g : G}
    (hgV : g ∈ Subgroup.normalizer (V : Set G)) (hgE : g ∈ Subgroup.normalizer (E : Set G)) :
    barAut g hgV hgE = 1 ↔ ∀ v ∈ V, ⁅g, v⁆ ∈ E := by
  have : (E.subgroupOf V).Normal := Subgroup.normal_of_isMulCommutative _
  constructor
  · intro h v hv
    have h1 := DFunLike.congr_fun h (QuotientGroup.mk ⟨v⁻¹, V.inv_mem hv⟩)
    rw [barAut_mk, MulAut.one_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
    simpa [commutatorElement_def, mul_assoc] using h1
  · intro h
    ext x
    induction x using QuotientGroup.induction_on with
    | H v =>
      rw [barAut_mk, MulAut.one_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have := h ((v : G)⁻¹) (V.inv_mem v.2)
      simpa [commutatorElement_def, mul_assoc] using this

@[expose] noncomputable def barHom [IsMulCommutative ↥V] :
    ↥(Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (E : Set G)) →*
      MulAut (↥V ⧸ E.subgroupOf V) :=
  haveI : (E.subgroupOf V).Normal := Subgroup.normal_of_isMulCommutative _
  MonoidHom.mk' (fun g => barAut g.1 g.2.1 g.2.2) (by
    intro g h
    ext x
    induction x using QuotientGroup.induction_on with
    | H v =>
      rw [MulAut.mul_apply, barAut_mk h.2.1 h.2.2, barAut_mk g.2.1 g.2.2, barAut_mk]
      congr 1
      apply Subtype.ext
      show (g.1 * h.1) * (v : G) * (g.1 * h.1)⁻¹ = g.1 * (h.1 * (v : G) * h.1⁻¹) * g.1⁻¹
      group)

theorem barHom_apply [IsMulCommutative ↥V]
    (g : ↥(Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (E : Set G))) :
    barHom (V := V) (E := E) g = barAut g.1 g.2.1 g.2.2 := rfl

theorem comm_le_of_normal_two_group (hV : IsElemAbelian 2 V) (hEV : E ≤ V) (hV16 : Nat.card ↥V = 16)
    (hE4 : Nat.card ↥E = 4) {D : Subgroup G}
    (hDN : D ≤ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (E : Set G))
    {h : G} (hhN : h ∈ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (E : Set G))
    (hhD : ∀ d ∈ D, h * d * h⁻¹ ∈ D) (hD2 : ∀ d ∈ D, ∃ n : ℕ, ∀ v ∈ V, ⁅d ^ 2 ^ n, v⁆ ∈ E)
    (hh1 : ∃ v ∈ V, ⁅h, v⁆ ∉ E) (hh3 : ∀ v ∈ V, ⁅h ^ 3, v⁆ ∈ E) :
    ∀ d ∈ D, ∀ v ∈ V, ⁅d, v⁆ ∈ E := by
  have := hV.1
  have : (E.subgroupOf V).Normal := Subgroup.normal_of_isMulCommutative _
  have := isKleinFour_quot hV hEV hV16 hE4
  let N := Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (E : Set G)
  have key := eq_one_of_normal_two_group (barHom (V := V) (E := E)) (D := D.subgroupOf N)
    (h := (⟨h, hhN⟩ : ↥N)) ?_ ?_ ?_ ?_
  · intro d hd v hv
    have hd' : d ∈ N := hDN hd
    have := key ⟨d, hd'⟩ (Subgroup.mem_subgroupOf.mpr hd)
    exact (barAut_eq_one_iff hd'.1 hd'.2).mp this v hv
  · intro d hd
    obtain ⟨n, hn⟩ := hD2 d.1 (Subgroup.mem_subgroupOf.mp hd)
    refine ⟨n, ?_⟩
    rw [← map_pow]
    exact (barAut_eq_one_iff (d ^ 2 ^ n).2.1 (d ^ 2 ^ n).2.2).mpr (fun v hv => by
      simpa using hn v hv)
  · intro d hd
    exact Subgroup.mem_subgroupOf.mpr (by simpa using hhD d.1 (Subgroup.mem_subgroupOf.mp hd))
  · intro h0
    obtain ⟨v, hv, hvE⟩ := hh1
    exact hvE ((barAut_eq_one_iff hhN.1 hhN.2).mp h0 v hv)
  · rw [← map_pow]
    exact (barAut_eq_one_iff ((⟨h, hhN⟩ : ↥N) ^ 3).2.1 ((⟨h, hhN⟩ : ↥N) ^ 3).2.2).mpr
      (fun v hv => by simpa using hh3 v hv)

end BarAut

end S1567

end CFSG.Quasithin
