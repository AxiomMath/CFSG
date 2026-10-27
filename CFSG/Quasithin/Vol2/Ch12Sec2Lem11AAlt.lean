module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem11A
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123Alt7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverCertA5

public section

namespace CFSG.Quasithin.H13

open CFSG.QuasithinUnique

namespace Lem11A

open Equiv

open CFSG.QuasithinUnique.Vol2Native.A312L.PermLat in
theorem three_dvd_of_latCert {n : ℕ} {A : Subgroup (Perm (Fin n))} (c : LatCert (Perm (Fin n)))
    (hM : Subgroup.closure {g | g ∈ c.mGens} = A)
    (hTA : Subgroup.closure {g | g ∈ c.tGens} ≤ A) (hc : c.check RN.enc = true)
    (hsz : ∀ j < (c.tGens :: c.lat).length, 0 < j → 3 ∣ c.sizes.getD j 0) :
    ∀ Z : Subgroup ↥A, (Subgroup.closure {g | g ∈ c.tGens}).subgroupOf A ≤ Z →
      Z ≠ (Subgroup.closure {g | g ∈ c.tGens}).subgroupOf A → 3 ∣ Nat.card Z := by
  intro Z hZ hne
  let Z' : Subgroup (Perm (Fin n)) := Z.map A.subtype
  have hDZ : Subgroup.closure {g | g ∈ c.tGens} ≤ Z' := fun t ht =>
    ⟨⟨t, hTA ht⟩, hZ (Subgroup.mem_subgroupOf.mpr ht), rfl⟩
  have hZM : Z' ≤ Subgroup.closure {g | g ∈ c.mGens} := by
    rw [hM]
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  obtain ⟨Lg, hL, hZL⟩ := c.overgroups (rawIsEnc n) hc Z' hDZ hZM
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hL
  have hcardZ : Nat.card Z = Nat.card Z' :=
    (Subgroup.card_map_of_injective A.subtype_injective).symm
  have hcard := c.card_member_idx (rawIsEnc n) (c.closedOK_of_check hc) (c.sizesOK_of_check hc) j hj
  rw [← hZL, ← hcardZ] at hcard
  rw [hcard]
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · exfalso
    apply hne
    subst h0
    have hZZ : Z'.subgroupOf A = Z := Subgroup.comap_map_eq_self_of_injective A.subtype_injective Z
    rw [← hZZ, hZL]
    rfl
  · exact hsz j hj hpos

open CFSG.QuasithinUnique.Bridge.Over in
theorem perm3_alt_five : Perm3 ↥(alternatingGroup (Fin 5)) :=
  perm3_of_model (MulEquiv.refl _) CertA5.isSylow_D
    (three_dvd_of_latCert CertA5.cert CertA5.closure_mGens CertA5.D_le CertA5.cert_check
      (by decide))

open CFSG.QuasithinUnique.L246C127 in
theorem perm3_alt_six : Perm3 ↥(alternatingGroup (Fin 6)) :=
  perm3_of_model (MulEquiv.refl _) Even6.isSylow_D
    (three_dvd_of_latCert Even6.cert Even6.closure_mGens Even6.D_le Even6.cert_check (by decide))

theorem exists_mem_dvd_of_prime_dvd_lcm {s : Multiset ℕ} {p : ℕ} (hp : p.Prime)
    (h : p ∣ s.lcm) : ∃ n ∈ s, p ∣ n := by
  induction s using Multiset.induction_on with
  | empty => exact absurd (by simpa using h) hp.not_dvd_one
  | cons a s ih =>
    rw [Multiset.lcm_cons, lcm_eq_nat_lcm, Nat.Prime.dvd_lcm hp] at h
    rcases h with ha | hs
    · exact ⟨a, Multiset.mem_cons_self a s, ha⟩
    · obtain ⟨n, hn, hpn⟩ := ih hs
      exact ⟨n, Multiset.mem_cons_of_mem hn, hpn⟩

theorem no_order_two_mul {n : ℕ} (hn : n ≤ 7) (σ : Perm (Fin n)) (hσ : Perm.sign σ = 1)
    {p : ℕ} (hp : p = 5 ∨ p = 7) : orderOf σ ≠ 2 * p := by
  intro h
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have hsum : σ.cycleType.sum ≤ 7 := by
    rw [Perm.sum_cycleType]
    exact (Finset.card_le_univ _).trans (by simpa using hn)
  have hle : ∀ a ∈ σ.cycleType, a ≤ 7 := fun a ha => (Multiset.le_sum_of_mem ha).trans hsum
  have hdvd : ∀ a ∈ σ.cycleType, a ∣ 2 * p := fun a ha => h ▸ Perm.dvd_of_mem_cycleType ha
  obtain ⟨a, ha, hpa⟩ := exists_mem_dvd_of_prime_dvd_lcm (s := σ.cycleType) hpp
    (by rw [Perm.lcm_cycleType, h]; exact dvd_mul_left p 2)
  obtain ⟨b, hb, h2b⟩ := exists_mem_dvd_of_prime_dvd_lcm (s := σ.cycleType) Nat.prime_two
    (by rw [Perm.lcm_cycleType, h]; exact dvd_mul_right 2 p)
  have ha' : a = p := by
    have h1 := hle a ha
    have h3 := Perm.two_le_of_mem_cycleType ha
    obtain ⟨c, rfl⟩ := hpa
    rcases hp with rfl | rfl <;> omega
  have hb' : b = 2 := by
    have h1 := hle b hb
    have h2 := hdvd b hb
    have h3 := Perm.two_le_of_mem_cycleType hb
    obtain ⟨c, rfl⟩ := h2b
    have hc : c ≤ 3 := by omega
    have hc1 : 1 ≤ c := by omega
    clear hle hdvd hsum hb h3 h1 ha hpa h
    rcases hp with rfl | rfl <;> interval_cases c <;> first | rfl | (exfalso; revert h2; decide)
  rw [ha'] at ha
  rw [hb'] at hb
  have hne : p ≠ 2 := by rcases hp with rfl | rfl <;> norm_num
  obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem ha
  have hbt : 2 ∈ t := by
    rw [ht] at hb
    exact (Multiset.mem_cons.mp hb).resolve_left (Ne.symm hne)
  obtain ⟨t', ht'⟩ := Multiset.exists_cons_of_mem hbt
  rw [ht, ht'] at hsum
  simp only [Multiset.sum_cons] at hsum
  have hp5 : p = 5 := by rcases hp with rfl | rfl <;> omega
  subst hp5
  have ht'0 : t' = 0 := by
    rw [Multiset.eq_zero_iff_forall_notMem]
    intro x hx
    have hx2 : 2 ≤ x := Perm.two_le_of_mem_cycleType (by rw [ht, ht']; simp [hx])
    have := Multiset.le_sum_of_mem hx
    omega
  rw [Perm.sign_of_cycleType, ht, ht', ht'0] at hσ
  simp at hσ
  exact absurd hσ (by decide)

variable {K : Type} [Group K] [Finite K]

theorem false_of_le_normalizer {S X : Subgroup K} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hX : Nat.card X = p) (hS2 : IsPGroup 2 S) (hcard : p - 1 < Nat.card S)
    (hN : ∀ s ∈ S, ∀ x ∈ X, s * x * s⁻¹ ∈ X) (hno : ∀ g : K, orderOf g ≠ 2 * p) : False := by
  classical
  obtain ⟨⟨x₀, hx₀X⟩, hx₀1⟩ : ∃ x : ↥X, x ≠ 1 := by
    by_contra hall
    push Not at hall
    have h1 : Nat.card X ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr
      ⟨fun a b => (hall a).trans (hall b).symm⟩
    rw [hX] at h1
    exact absurd h1 (by have := hp.two_le; omega)
  have hx₀1' : x₀ ≠ 1 := fun h0 => hx₀1 (Subtype.ext h0)
  have hord : orderOf x₀ = p := by
    have h1 : orderOf (⟨x₀, hx₀X⟩ : ↥X) ∣ p := hX ▸ orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    rcases (Nat.dvd_prime hp).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx₀1'
    · exact h
  have hmaps : ∀ s ∈ (S : Set K), s * x₀ * s⁻¹ ∈ (X : Set K) \ {1} := fun s hs =>
    ⟨hN s hs x₀ hx₀X, fun h1 => hx₀1' (by
      have h1' : s * x₀ * s⁻¹ = 1 := h1
      calc x₀ = s⁻¹ * (s * x₀ * s⁻¹) * s := by group
        _ = 1 := by rw [h1']; group)⟩
  have hlt : ((X : Set K) \ {1}).ncard < (S : Set K).ncard := by
    rw [Set.ncard_sdiff_singleton_of_mem (X.one_mem : (1 : K) ∈ (X : Set K)),
      ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact (by simpa [hX] using hcard)
  obtain ⟨s, hs, s', hs', hss, hfe⟩ := Set.exists_ne_map_eq_of_ncard_lt_of_maps_to hlt hmaps
  set c := s⁻¹ * s' with hc
  have hcS : c ∈ S := S.mul_mem (S.inv_mem hs) hs'
  have hc1 : c ≠ 1 := fun h1 => hss (by
    have : s' = s * c := by rw [hc]; group
    rw [this, h1, mul_one])
  have hcomm : Commute c x₀ := by
    have hfe' : s * x₀ * s⁻¹ = s' * x₀ * s'⁻¹ := hfe
    show c * x₀ = x₀ * c
    calc c * x₀ = s⁻¹ * (s' * x₀ * s'⁻¹) * s' := by rw [hc]; group
      _ = s⁻¹ * (s * x₀ * s⁻¹) * s' := by rw [hfe']
      _ = x₀ * c := by rw [hc]; group
  obtain ⟨k, hk⟩ := hS2 ⟨c, hcS⟩
  have hck : c ^ 2 ^ k = 1 := congrArg Subtype.val hk
  obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hck)
  have hi0 : i ≠ 0 := by
    rintro rfl
    exact hc1 (orderOf_eq_one_iff.mp (by simpa using hci))
  set t := c ^ 2 ^ (i - 1) with ht
  have hto : orderOf t = 2 := by
    rw [ht, orderOf_pow_of_dvd (by positivity) (by rw [hci]; exact Nat.pow_dvd_pow 2 (by omega)),
      hci]
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    simp [pow_succ]
  have htcomm : Commute t x₀ := hcomm.pow_left _
  have hmul : orderOf (t * x₀) = 2 * p := by
    rw [htcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by
      rw [hto, hord]
      exact (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)), hto, hord]
  exact hno _ hmul

omit [Finite K] in
theorem le_normalizer_map {Y : Subgroup K} (Q : Subgroup ↥Y) [hn : Q.Normal] :
    Y ≤ Subgroup.normalizer ((Q.map Y.subtype : Subgroup K) : Set K) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨⟨y, hy⟩ * q * ⟨y, hy⟩⁻¹, hn.conj_mem q hq _, rfl⟩
  · rintro ⟨q, hq, hqh⟩
    refine ⟨⟨y, hy⟩⁻¹ * q * ⟨y, hy⟩, ?_, ?_⟩
    · have := hn.conj_mem q hq ⟨y, hy⟩⁻¹
      rwa [inv_inv] at this
    · have hqh' : (q : K) = y * h * y⁻¹ := hqh
      show y⁻¹ * (q : K) * y = h
      rw [hqh']
      group

open CFSG.QuasithinUnique.L246.C123 in
theorem perm3_alt_seven : Perm3 ↥(alternatingGroup (Fin 7)) := by
  intro S X p hS hp hp2 hXp hX1 hSX
  by_contra hp3
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card ↥(alternatingGroup (Fin 7)) = 2520 := card_A7
  have hS8 : Nat.card S = 8 := by
    have hidx : ¬ 2 ∣ S.index := by
      have := hS.2.2
      rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
    rw [← IsPGroup.toSylow_coe hS.2.1 hidx, Sylow.card_eq_multiplicity, fac_card_A7]
    norm_num
  obtain ⟨k, hk⟩ := hXp.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hX1
    rw [← Subgroup.card_eq_one]
    simpa using hk
  have hdvdK : p ^ k ∣ 2520 := hk ▸ hK ▸ Subgroup.card_subgroup_dvd_card X
  have hp57 : p = 5 ∨ p = 7 := by
    have hpd : p ∣ 2 ^ 3 * 3 ^ 2 * 5 * 7 := (dvd_pow_self p hk0).trans (by simpa using hdvdK)
    rcases (Nat.Prime.dvd_mul hp).mp hpd with h | h7
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h5
      · rcases (Nat.Prime.dvd_mul hp).mp h with h2 | h3
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))
            hp2
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
            (hp.dvd_of_dvd_pow h3)) hp3
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h5)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h7)
  have hk1 : k = 1 := by
    by_contra hk1
    have h2 : p ^ 2 ∣ 2520 := (Nat.pow_dvd_pow p (by omega)).trans hdvdK
    rcases hp57 with rfl | rfl <;> norm_num at h2
  have hXc : Nat.card X = p := by rw [hk, hk1, pow_one]
  have hno : ∀ g : ↥(alternatingGroup (Fin 7)), orderOf g ≠ 2 * p := fun g h => by
    have hg := no_order_two_mul le_rfl (g : Perm (Fin 7)) (Perm.mem_alternatingGroup.mp g.2)
      hp57
    exact hg (by rwa [Subgroup.orderOf_coe])
  have hXS : ∀ y ∈ X, y ∈ S → y = 1 := fun y hyX hyS =>
    Lem22.eq_one_of_mem_of_mem hp hp2 hXp hS.2.1 hyX hyS
  set Y := Lem22.mulSub X S hSX with hYdef
  have hYc : Nat.card Y = p * 8 := by rw [hYdef, Lem22.card_mulSub hSX hXS, hXc, hS8]
  have hXY : X ≤ Y := fun x hx => ⟨x, hx, 1, S.one_mem, by rw [mul_one]⟩
  have hSY : S ≤ Y := fun s hs => ⟨1, X.one_mem, s, hs, by rw [one_mul]⟩
  have hX'p : IsPGroup p ↥(X.subgroupOf Y) :=
    hXp.of_equiv (Subgroup.subgroupOfEquivOfLe hXY).symm
  have hX'c : Nat.card (X.subgroupOf Y) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXY).toEquiv, hXc]
  have hidx : (X.subgroupOf Y).index = 8 := by
    have h1 := Subgroup.card_mul_index (X.subgroupOf Y)
    rw [hX'c, hYc] at h1
    exact Nat.eq_of_mul_eq_mul_left hp.pos h1
  have hnd : ¬ p ∣ (X.subgroupOf Y).index := by
    rw [hidx]
    rcases hp57 with rfl | rfl <;> decide
  set P : Sylow p ↥Y := hX'p.toSylow hnd with hPdef
  have hPc : (P : Subgroup ↥Y) = X.subgroupOf Y := IsPGroup.toSylow_coe hX'p hnd
  have hmod := card_sylow_modEq_one p ↥Y
  have hdvd := Sylow.card_dvd_index P
  rw [hPc, hidx] at hdvd
  have hnorm := Sylow.card_eq_index_normalizer P
  obtain ⟨m, hm⟩ : ∃ m, Nat.card (Sylow p ↥Y) = m := ⟨_, rfl⟩
  rw [hm] at hmod hdvd hnorm
  have hm8 : m ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
  have hcases : m = 1 ∨ (p = 7 ∧ m = 8) := by
    clear_value P Y
    rcases hp57 with rfl | rfl <;> interval_cases m <;>
      first
        | exact Or.inl rfl
        | exact Or.inr ⟨rfl, rfl⟩
        | (exfalso; revert hmod hdvd; decide)
  rcases hcases with h1 | ⟨hp7, h8⟩
  ·
    have htop : Subgroup.normalizer ((P : Subgroup ↥Y) : Set ↥Y) = ⊤ :=
      Subgroup.index_eq_one.mp (hnorm ▸ h1)
    refine false_of_le_normalizer hp hp2 hXc hS.2.1
      (by rw [hS8]; rcases hp57 with rfl | rfl <;> norm_num) (fun s hs x hx => ?_) hno
    have hsN : (⟨s, hSY hs⟩ : ↥Y) ∈ Subgroup.normalizer ((P : Subgroup ↥Y) : Set ↥Y) :=
      htop ▸ Subgroup.mem_top _
    have hxP : (⟨x, hXY hx⟩ : ↥Y) ∈ (P : Subgroup ↥Y) := by
      rw [hPc]
      exact Subgroup.mem_subgroupOf.mpr hx
    have h := (Subgroup.mem_normalizer_iff.mp hsN _).mp hxP
    rw [hPc, Subgroup.mem_subgroupOf] at h
    simpa using h
  ·
    subst hp7
    have hNidx : (Subgroup.normalizer ((P : Subgroup ↥Y) : Set ↥Y)).index = 8 := hnorm ▸ h8
    have hNc : Nat.card (Subgroup.normalizer ((P : Subgroup ↥Y) : Set ↥Y)) = 7 := by
      have h1 := Subgroup.card_mul_index (Subgroup.normalizer ((P : Subgroup ↥Y) : Set ↥Y))
      rw [hNidx, hYc] at h1
      omega
    have hNP : Subgroup.normalizer ((P : Subgroup ↥Y) : Set ↥Y) = (P : Subgroup ↥Y) :=
      (Subgroup.eq_of_le_of_card_ge Subgroup.le_normalizer (by rw [hNc, hPc, hX'c])).symm
    have hcyc : IsCyclic ↥(P : Subgroup ↥Y) := isCyclic_of_prime_card (hPc ▸ hX'c)
    have hPab : (P : Subgroup ↥Y) ≤ Subgroup.centralizer ((P : Subgroup ↥Y) : Set ↥Y) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have := hcyc.commGroup.mul_comm ⟨b, hb⟩ ⟨a, ha⟩
      exact congrArg Subtype.val this
    have hP' : Subgroup.normalizer ((P : Subgroup ↥Y) : Set ↥Y) ≤
        Subgroup.centralizer ((P : Subgroup ↥Y) : Set ↥Y) := by
      rw [hNP]
      exact hPab
    have hcomp := MonoidHom.ker_transferSylow_isComplement' P hP'
    have hPcard : Nat.card ↥(P : Subgroup ↥Y) = 7 := by rw [hPc]; exact hX'c
    have hQc : Nat.card (MonoidHom.transferSylow P hP').ker = 8 := by
      have h1 := hcomp.card_mul_card
      rw [hPcard, hYc] at h1
      omega
    have hYN := le_normalizer_map (Y := Y) (MonoidHom.transferSylow P hP').ker
    have hQm : Nat.card ((MonoidHom.transferSylow P hP').ker.map Y.subtype) = 8 := by
      rw [Subgroup.card_map_of_injective Y.subtype_injective, hQc]
    rw [normalizer_eq_of_card_eight hQm] at hYN
    have h1 := Subgroup.card_le_of_le hYN
    rw [hQm, hYc] at h1
    omega

end Lem11A

end CFSG.Quasithin.H13
