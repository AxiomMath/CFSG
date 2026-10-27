module

public import CFSG.RankThree.PartTwo.Sec21.ThreeLocalSporProofChar
public import CFSG.Sporadic.Recognition.McLASCert
public import CFSG.RankThree.PartTwo.Sec6.Item611Res4ProofE81McL

public section

namespace CFSG.RankThree.PartTwo.Sec6.ThreeLocalSporProof

open CFSG CFSG.Blueprint
open CFSG.Sporadic.Schreier (mclP)

theorem isCharacteristicP_of_normal_pGroup {H : Type*} [Group H] [Finite H] {p : ℕ}
    [Fact p.Prime] {Q : Subgroup H} (hQn : Q.Normal) (hQp : IsPGroup p Q)
    (h : ∀ x : H, (orderOf x).Prime → orderOf x ≠ p → ¬ ∀ q ∈ Q, x * q = q * x) :
    IsCharacteristicP p H := by
  unfold IsCharacteristicP
  have hQle : Q ≤ pCore p H := le_sSup ⟨hQn, hQp⟩
  have hMp : IsPGroup p (Subgroup.centralizer (pCore p H : Set H)) := by
    rw [isPGroup_iff_card_dvd_pow]
    refine ⟨(Nat.card (Subgroup.centralizer (pCore p H : Set H))).primeFactorsList.length, ?_⟩
    rw [← Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_]
    intro d hd hdvd
    by_contra hne
    have : Fact d.Prime := ⟨hd⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' d hdvd
    refine h x ?_ ?_ fun q hq => ?_
    · rw [Subgroup.orderOf_coe, hx]
      exact hd
    · rw [Subgroup.orderOf_coe, hx]
      exact hne
    · exact (Subgroup.mem_centralizer_iff.mp x.2 q (hQle hq)).symm
  exact le_sSup ⟨inferInstance, hMp⟩

theorem prime_dvd_two_three_five {r a b c : ℕ} (hr : r.Prime) (h : r ∣ 2 ^ a * 3 ^ b * 5 ^ c) :
    r = 2 ∨ r = 3 ∨ r = 5 := by
  rcases (Nat.Prime.dvd_mul hr).mp h with h1 | h5
  · rcases (Nat.Prime.dvd_mul hr).mp h1 with h2 | h3
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h2))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp
        (hr.dvd_of_dvd_pow h3)))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_five).mp
      (hr.dvd_of_dvd_pow h5)))

@[expose] noncomputable def centralizerEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (x : G) :
    ↥(Subgroup.centralizer ({x} : Set G)) ≃* ↥(Subgroup.centralizer ({e x} : Set H)) :=
  (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (by
      ext y
      simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff,
        MulEquiv.coe_toMonoidHom]
      constructor
      · rintro ⟨w, hw, rfl⟩
        rw [← map_mul, ← map_mul, hw]
      · intro hy
        refine ⟨e.symm y, e.injective ?_, e.apply_symm_apply y⟩
        rw [map_mul, map_mul, e.apply_symm_apply, hy]))

theorem nonempty_centralizer_mulEquiv_of_isConj {G : Type*} [Group G] {a b : G}
    (h : IsConj a b) :
    Nonempty (↥(Subgroup.centralizer ({a} : Set G)) ≃* ↥(Subgroup.centralizer ({b} : Set G))) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  refine ⟨(centralizerEquiv (MulAut.conj c) a).trans (MulEquiv.subgroupCongr ?_)⟩
  rw [MulAut.conj_apply, hc]

theorem card_centralizer_of_isConj {G : Type*} [Group G] {a b : G} (h : IsConj a b) :
    Nat.card ↥(Subgroup.centralizer ({a} : Set G)) =
      Nat.card ↥(Subgroup.centralizer ({b} : Set G)) :=
  Nat.card_congr (nonempty_centralizer_mulEquiv_of_isConj h).some.toEquiv

theorem map_centralizer_singleton {X : Type*} [Group X] {H : Subgroup X} (z : H) :
    (Subgroup.centralizer ({z} : Set H)).map H.subtype =
      H ⊓ Subgroup.centralizer ({(z : X)} : Set X) := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hx))⟩
  · rintro ⟨hgH, hg⟩
    exact ⟨⟨g, hgH⟩, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hg)), rfl⟩

theorem card_centralizer_singleton {X : Type*} [Group X] {H : Subgroup X} (z : H) :
    Nat.card ↥(Subgroup.centralizer ({z} : Set H)) =
      Nat.card ↥(H ⊓ Subgroup.centralizer ({(z : X)} : Set X)) := by
  rw [← map_centralizer_singleton, Subgroup.card_map_of_injective H.subtype_injective]

theorem isConj_of_eq_conj {X : Type*} [Group X] {H : Subgroup X} {z t : H} {g : X} (hg : g ∈ H)
    (h : (z : X) = g * t * g⁻¹) : IsConj z t := by
  refine isConj_iff.mpr ⟨⟨g, hg⟩⁻¹, Subtype.ext ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, h]
  group

theorem exists_normal_pGroup_of_card_972 {H : Type*} [Group H] [Finite H]
    (hH : Nat.card H = 972) : ∃ Q : Subgroup H, Q.Normal ∧ IsPGroup 3 Q ∧ 81 ≤ Nat.card Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 3 H))
  have hfac : (972 : ℕ).factorization 3 = 5 := by
    have h : (972 : ℕ) = 3 ^ 5 * 4 := by norm_num
    rw [h, Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three]
    simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 3 ∣ 4 by norm_num)]
  have hS : Nat.card S = 243 := by
    rw [Sylow.card_eq_multiplicity, hH, hfac]
    norm_num
  have hidx : (S : Subgroup H).index = 4 := by
    have h1 := (S : Subgroup H).card_mul_index
    rw [hS, hH] at h1
    omega
  have : (S : Subgroup H).FiniteIndex := ⟨by rw [hidx]; norm_num⟩
  refine ⟨(S : Subgroup H).normalCore, inferInstance,
    S.isPGroup'.to_le (Subgroup.normalCore_le _), ?_⟩
  have hdvd : (S : Subgroup H).normalCore.index ∣ 24 := by
    have h1 := Subgroup.index_normalCore_dvd_factorial_index (S : Subgroup H)
    rw [hidx] at h1
    exact h1
  have hle24 : (S : Subgroup H).normalCore.index ≤ 24 := Nat.le_of_dvd (by norm_num) hdvd
  have hmul := (S : Subgroup H).normalCore.card_mul_index
  rw [hH] at hmul
  have hQS : Nat.card (S : Subgroup H).normalCore ∣ 3 ^ 5 := by
    rw [show (3 : ℕ) ^ 5 = 243 by norm_num, ← hS]
    exact Subgroup.card_dvd_of_le (Subgroup.normalCore_le _)
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hQS
  rw [hk'] at hmul ⊢
  interval_cases k <;> norm_num at hmul ⊢ <;> omega

section McL


theorem not_forall_comm_of_orderOf_five_mclP
    {D : Subgroup mclP} (hD : IsPGroup 3 D) (h9 : 9 ≤ Nat.card D) {u : mclP}
    (hu : orderOf u = 5) : ¬ ∀ d ∈ D, u * d = d * u := by
  intro hcomm
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hf₁, hf₂, -, -, c₁, c₂, -, -, -, hall⟩ :=
    CFSG.Sporadic.Recognition.McLAS.mclP_order_five_classes
      CFSG.Sporadic.Recognition.McLAS.fiveOuterCheck_eq_true
  have hDC : D ≤ Subgroup.centralizer ({u} : Set mclP) := fun d hd =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm d hd).symm
  have hdvd := Subgroup.card_dvd_of_le hDC
  obtain ⟨k, hk⟩ := hD.exists_card_eq
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have : 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h9d : 9 ∣ Nat.card D := by
    rw [hk]
    have h1 : 3 ^ 2 ∣ 3 ^ k := Nat.pow_dvd_pow 3 hk2
    simpa using h1
  have hu5 : orderOf (u : Equiv.Perm (Fin 275)) = 5 := by rw [Subgroup.orderOf_coe, hu]
  rcases hall u u.2 hu5 with ⟨g, hg, hug⟩ | ⟨g, hg, hug⟩
  · have hc := card_centralizer_of_isConj (isConj_of_eq_conj (t := ⟨_, hf₁⟩) hg hug)
    rw [card_centralizer_singleton (⟨_, hf₁⟩ : mclP)] at hc
    rw [c₁] at hc
    rw [hc] at hdvd
    have := h9d.trans hdvd
    norm_num at this
  · have hc := card_centralizer_of_isConj (isConj_of_eq_conj (t := ⟨_, hf₂⟩) hg hug)
    rw [card_centralizer_singleton (⟨_, hf₂⟩ : mclP)] at hc
    rw [c₂] at hc
    rw [hc] at hdvd
    have := h9d.trans hdvd
    norm_num at this

theorem isCharacteristicP_centralizer_mclP_of {z : mclP}
    (hcard : Nat.card ↥(Subgroup.centralizer ({z} : Set mclP)) = 2 ^ 3 * 3 ^ 6 * 5 ^ 1 ∨
      Nat.card ↥(Subgroup.centralizer ({z} : Set mclP)) = 2 ^ 2 * 3 ^ 5 * 5 ^ 0)
    {Q : Subgroup ↥(Subgroup.centralizer ({z} : Set mclP))} (hQn : Q.Normal)
    (hQp : IsPGroup 3 Q) (h81 : 81 ≤ Nat.card Q) :
    IsCharacteristicP 3 ↥(Subgroup.centralizer ({z} : Set mclP)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine isCharacteristicP_of_normal_pGroup hQn hQp fun x hxp hx3 hcomm => ?_
  have hDp : IsPGroup 3 (Q.map (Subgroup.centralizer ({z} : Set mclP)).subtype) :=
    hQp.map _
  have hD81 : 81 ≤ Nat.card (Q.map (Subgroup.centralizer ({z} : Set mclP)).subtype) := by
    rw [Subgroup.card_map_of_injective (Subgroup.centralizer ({z} : Set mclP)).subtype_injective]
    exact h81
  have hcommD : ∀ d ∈ Q.map (Subgroup.centralizer ({z} : Set mclP)).subtype,
      (x : mclP) * d = d * x := by
    rintro _ ⟨q, hq, rfl⟩
    exact congrArg Subtype.val (hcomm q hq)
  have hord : orderOf (x : mclP) = orderOf x := Subgroup.orderOf_coe x
  have hdvd : orderOf x ∣ Nat.card ↥(Subgroup.centralizer ({z} : Set mclP)) :=
    orderOf_dvd_natCard x
  have hr : orderOf x = 2 ∨ orderOf x = 3 ∨ orderOf x = 5 := by
    rcases hcard with h | h
    · rw [h] at hdvd
      exact prime_dvd_two_three_five hxp hdvd
    · rw [h] at hdvd
      exact prime_dvd_two_three_five hxp hdvd
  rcases hr with h2 | h3 | h5
  · refine Res611Res4.not_forall_comm_of_involution_mclP hDp hD81 (u := (x : mclP)) ?_ ?_
      hcommD
    · intro h1
      rw [h1, orderOf_one] at hord
      omega
    · rw [← h2, ← hord, pow_orderOf_eq_one]
  · exact hx3 h3
  · exact not_forall_comm_of_orderOf_five_mclP hDp (by omega) (hord.trans h5) hcommD

theorem exists_threeLocal_mclP : ∃ x : mclP,
    (x : Equiv.Perm (Fin 275)) = CFSG.Sporadic.Recognition.McLAS.three₁ ∧
      ∃ Q : Subgroup ↥(Subgroup.centralizer ({x} : Set mclP)), Q.Normal ∧ IsPGroup 3 Q ∧
        Nat.card Q = 243 := by
  obtain ⟨x, R, T, A, hx, -, -, -, hL⟩ :=
    CFSG.Sporadic.Recognition.McLAS.threeLocal_of_embedding mclP.subtype mclP.subtype_injective
      (Subgroup.range_subtype mclP) CFSG.Sporadic.Recognition.McLAS.threeFacts_cert'
      CFSG.Sporadic.Recognition.McLAS.threeLocalCheck_eq_true
  refine ⟨x, hx, ?_⟩
  have hxR : x ∈ R ⊓ Subgroup.centralizer (R : Set mclP) := by
    rw [hL.center_R]
    exact Subgroup.mem_zpowers x
  have hRC : R ≤ Subgroup.centralizer ({x} : Set mclP) := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hxR.2 r hr)
  have hCN : Subgroup.centralizer ({x} : Set mclP) ≤
      Subgroup.normalizer ((Subgroup.zpowers x : Subgroup mclP) : Set mclP) := by
    intro g hg
    have hgxc : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.mp hg
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · rintro ⟨n, rfl⟩
      refine ⟨n, ?_⟩
      have hc : g * x ^ n = x ^ n * g := (Commute.zpow_right hgxc n).eq
      change x ^ n = g * x ^ n * g⁻¹
      rw [hc, mul_inv_cancel_right]
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have hn' : x ^ n = g * w * g⁻¹ := hn
      have hc : g * x ^ n = x ^ n * g := (Commute.zpow_right hgxc n).eq
      change x ^ n = w
      calc x ^ n = g⁻¹ * (g * x ^ n) := by group
        _ = g⁻¹ * (x ^ n * g) := by rw [hc]
        _ = g⁻¹ * (g * w * g⁻¹ * g) := by rw [← hn']
        _ = w := by group
  refine ⟨R.subgroupOf (Subgroup.centralizer ({x} : Set mclP)), ⟨fun r hr g => ?_⟩, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf] at hr ⊢
    rw [← hL.pCore_eq] at hr ⊢
    obtain ⟨r', hr', hrr⟩ := hr
    have hg := hCN g.2
    refine ⟨⟨g, hg⟩ * r' * ⟨g, hg⟩⁻¹,
      (CFSG.pCore_normal (p := 3)).conj_mem r' hr' ⟨g, hg⟩, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hrr ⊢
    rw [hrr]
  · refine IsPGroup.of_card (n := 5) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRC).toEquiv, hL.card_R]
    norm_num
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRC).toEquiv, hL.card_R]

theorem centCharThree_mclP (z : mclP) (hz : orderOf z = 3) :
    IsCharacteristicP 3 ↥(Subgroup.centralizer ({z} : Set mclP)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ht₁, ht₂, -, -, c₁, c₂, -, -, -, hall⟩ :=
    CFSG.Sporadic.Recognition.McLAS.mclP_order_three_classes
      CFSG.Sporadic.Recognition.McLAS.threeFacts_cert
  have hz3 : orderOf (z : Equiv.Perm (Fin 275)) = 3 := by rw [Subgroup.orderOf_coe, hz]
  rcases hall z z.2 hz3 with ⟨g, hg, hzg⟩ | ⟨g, hg, hzg⟩
  ·
    obtain ⟨x, hx, Q, hQn, hQp, hQ⟩ := exists_threeLocal_mclP
    have hzx : IsConj z x := isConj_of_eq_conj (t := x) hg (by rw [hx]; exact hzg)
    have hcx : Nat.card ↥(Subgroup.centralizer ({x} : Set mclP)) = 2 ^ 3 * 3 ^ 6 * 5 ^ 1 := by
      rw [card_centralizer_singleton, hx, c₁]
      norm_num
    have hcharx := isCharacteristicP_centralizer_mclP_of (Or.inl hcx) hQn hQp (by omega)
    exact isCharacteristicP_of_mulEquiv
      (nonempty_centralizer_mulEquiv_of_isConj hzx).some.symm hcharx
  ·
    have hcard : Nat.card ↥(Subgroup.centralizer ({z} : Set mclP)) = 972 := by
      rw [card_centralizer_of_isConj (isConj_of_eq_conj (t := ⟨_, ht₂⟩) hg hzg),
        card_centralizer_singleton (⟨_, ht₂⟩ : mclP), c₂]
    obtain ⟨Q, hQn, hQp, hQ81⟩ := exists_normal_pGroup_of_card_972 hcard
    exact isCharacteristicP_centralizer_mclP_of (Or.inr (by rw [hcard]; norm_num)) hQn hQp hQ81

end McL

end CFSG.RankThree.PartTwo.Sec6.ThreeLocalSporProof
