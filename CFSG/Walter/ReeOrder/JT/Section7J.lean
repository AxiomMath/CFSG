module

public import CFSG.Walter.ReeOrder.JT.Section7I
public import CFSG.Walter.ReeOrder.JT.AuxPClosed
public import CFSG.Walter.Transitivity.Step
public import CFSG.Walter.ReeOrder.JT.Section7H

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups
open CFSG

variable {G : Type} [Group G] [Finite G]

namespace TorusConf

variable {h : JTHyp G} (c : TorusConf h)

theorem w_mem_F : c.w ∈ h.F := c.torus.w_mem

theorem w_mul_w : c.w * c.w = 1 := c.torus.w_mul_self

theorem commute_t_w : Commute h.t c.w := (h.commute_of_mem_F c.w_mem_F).symm

theorem w_ne_one : c.w ≠ 1 := fun h0 => c.torus.w_not_mem (h0 ▸ c.C.one_mem)

theorem t_ne_w : h.t ≠ c.w := fun h0 => h.t_not_mem (h0 ▸ c.w_mem_F)

@[expose] noncomputable def T₀ : Subgroup G :=
  GorensteinWalter.kleinFourOfCommutingInvolutions h.t c.w h.t_mul_t c.w_mul_w c.commute_t_w

theorem mem_T₀ {x : G} : x ∈ c.T₀ ↔ x = h.t * c.w ∨ x = h.t ∨ x = c.w ∨ x = 1 := Iff.rfl

theorem isKleinFour_T₀ : IsKleinFour c.T₀ :=
  GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions _ _ _ _ h.t_ne_one c.w_ne_one
    c.t_ne_w c.commute_t_w

theorem t_mem_T₀ : h.t ∈ c.T₀ := c.mem_T₀.mpr (Or.inr (Or.inl rfl))

theorem w_mem_T₀ : c.w ∈ c.T₀ := c.mem_T₀.mpr (Or.inr (Or.inr (Or.inl rfl)))

theorem isPGroup_T₀ : IsPGroup 2 c.T₀ :=
  IsPGroup.of_card (n := 2) (by rw [c.isKleinFour_T₀.card_four]; norm_num)

theorem T₀_le_centralizer_t : c.T₀ ≤ Subgroup.centralizer ({h.t} : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  rcases c.mem_T₀.mp hx with rfl | rfl | rfl | rfl
  · rw [mul_assoc, ← c.commute_t_w.eq, ← mul_assoc]
  · rfl
  · exact c.commute_t_w.eq.symm
  · simp

theorem T₀_le_normalizer_C : c.T₀ ≤ Subgroup.normalizer (c.C : Set G) := by
  have ht : h.t ∈ Subgroup.normalizer (c.C : Set G) := mem_normalizer_of_conj_mem fun x hx => by
    rw [← h.commute_of_mem_F (c.torus.le hx), mul_inv_cancel_right]
    exact hx
  have hw : c.w ∈ Subgroup.normalizer (c.C : Set G) := mem_normalizer_of_conj_mem fun x hx => by
    rw [c.torus.inv x hx]
    exact c.C.inv_mem hx
  intro x hx
  rcases c.mem_T₀.mp hx with rfl | rfl | rfl | rfl
  · exact Subgroup.mul_mem _ ht hw
  · exact ht
  · exact hw
  · exact Subgroup.one_mem _

@[expose] noncomputable def Cp (p : ℕ) [Fact p.Prime] : Subgroup G :=
  ((default : Sylow p c.C) : Subgroup c.C).map c.C.subtype

variable (p : ℕ) [hp : Fact p.Prime]

theorem Cp_le_C : c.Cp p ≤ c.C := Subgroup.map_subtype_le _

theorem isPGroup_Cp : IsPGroup p (c.Cp p) := (default : Sylow p c.C).isPGroup'.map _

theorem card_Cp : Nat.card (c.Cp p) = p ^ (Nat.card c.C).factorization p := by
  rw [Cp, Subgroup.card_map_of_injective c.C.subtype_injective,
    Sylow.card_eq_multiplicity]

theorem T₀_le_normalizer_Cp : c.T₀ ≤ Subgroup.normalizer ((c.Cp p : Subgroup G) : Set G) :=
  c.T₀_le_normalizer_C.trans (normalizer_le_normalizer_of_le_isCyclic c.torus.cyclic
    (c.Cp_le_C p))

theorem Cp_ne_bot (hpC : p ∣ Nat.card c.C) : c.Cp p ≠ ⊥ := by
  intro h0
  have := c.card_Cp p
  rw [h0, Subgroup.card_bot] at this
  have hpos : 0 < (Nat.card c.C).factorization p :=
    (Nat.Prime.factorization_pos_of_dvd hp.out Nat.card_pos.ne' hpC)
  have : p ^ (Nat.card c.C).factorization p ≠ 1 :=
    (Nat.one_lt_pow hpos.ne' hp.out.one_lt).ne'
  omega

end TorusConf

namespace JTHyp

variable (h : JTHyp G) (hp3 : h.p = 3)
include hp3

theorem factorization_card_centralizer_t
    (c : TorusConf h) {p : ℕ} [hp : Fact p.Prime]
    (hpq : p ∣ (h.q - 1) / 2) :
    (Nat.card (Subgroup.centralizer ({h.t} : Set G))).factorization p =
      (Nat.card c.C).factorization p := by
  have hp2 := h.p_ne_two_of_eq_three hp3
  have hp7 := h.seven_le_of_pi hp3 hpq
  have hcard := h.card_centralizer_of_orderOf_eq_two hp2 h.orderOf_t
  have hq8 := h.q_mod_eight_of_eq_three hp3
  have hq3 := h.three_dvd_q hp3
  have hCq := c.card_C
  have hq1 : 0 < h.q := by omega
  have e : h.q * (h.q ^ 2 - 1) = h.q * (h.q + 1) * 2 * Nat.card c.C := by
    have : h.q ^ 2 - 1 = (h.q + 1) * (h.q - 1) := by
      rw [pow_two]
      have : 1 ≤ h.q := by omega
      zify [this, Nat.one_le_two_pow, Nat.one_le_iff_ne_zero.mpr (by positivity : h.q * h.q ≠ 0)]
      ring
    rw [this]
    have : h.q - 1 = 2 * Nat.card c.C := by omega
    rw [this]
    ring
  rw [hcard, e, Nat.factorization_mul (by positivity) (Nat.card_pos.ne'),
    Nat.factorization_mul (by positivity) (by norm_num),
    Nat.factorization_mul (by positivity) (by omega)]
  simp only [Finsupp.add_apply]
  have h1 : ¬ p ∣ h.q := by
    intro hd
    obtain ⟨n, -, hn⟩ := lemma_4_1 h hp2 ⟨h.f, by rw [JTHyp.q_eq, hp3]⟩
    rw [hn] at hd
    have := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).mp (hp.out.dvd_of_dvd_pow hd)
    omega
  have h2 : ¬ p ∣ h.q + 1 := by
    intro hd
    have h3 : p ∣ (h.q + 1) - 2 * ((h.q - 1) / 2) := Nat.dvd_sub hd (dvd_mul_of_dvd_right hpq 2)
    have : (h.q + 1) - 2 * ((h.q - 1) / 2) = 2 := by omega
    rw [this] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  have h4 : ¬ p ∣ 2 := fun hd => by have := Nat.le_of_dvd (by norm_num) hd; omega
  rw [Nat.factorization_eq_zero_of_not_dvd h1, Nat.factorization_eq_zero_of_not_dvd h2,
    Nat.factorization_eq_zero_of_not_dvd h4]
  ring

theorem isCyclic_of_le_centralizer_pi
    {r : ℕ} [hr : Fact r.Prime] (hrq : r ∣ (h.q - 1) / 2)
    {B : Subgroup G} (hBr : IsPGroup r B) {u : G} (hu : orderOf u = 2)
    (hBu : B ≤ Subgroup.centralizer ({u} : Set G)) : IsCyclic B := by
  have hp := h.p_ne_two_of_eq_three hp3
  have hr7 := h.seven_le_of_pi hp3 hrq
  obtain ⟨g, hg⟩ := h.exists_conj_eq_t hp hu
  set B' := B.map (MulAut.conj g).toMonoidHom
  have hB't : B' ≤ Subgroup.centralizer ({h.t} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxu := Subgroup.mem_centralizer_singleton_iff.mp (hBu hx)
    rw [← hg]
    change g * x * g⁻¹ * (g * u * g⁻¹) = g * u * g⁻¹ * (g * x * g⁻¹)
    calc g * x * g⁻¹ * (g * u * g⁻¹) = g * (x * u) * g⁻¹ := by group
      _ = g * (u * x) * g⁻¹ := by rw [hxu]
      _ = g * u * g⁻¹ * (g * x * g⁻¹) := by group
  have hB'r : IsPGroup r B' := hBr.map _
  have hB'odd : Odd (Nat.card B') := by
    obtain ⟨n, hn⟩ := hB'r.exists_card_eq
    rw [hn]
    exact (hr.out.odd_of_ne_two (by omega)).pow
  have hB'c : IsCyclic B' := (h.facts hp).cyclic r hr.out (by omega) (by rw [hp3]; omega) B'
    (h.le_F_of_odd hB't hB'odd) hB'r
  exact isCyclic_of_surjective (B.equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).symm
    (MulEquiv.surjective _)

end JTHyp

section Sylow

variable {X : Type*} [Group X] [Finite X]

theorem exists_sylow_eq_of_maximal {p : ℕ} [hp : Fact p.Prime] {P : Subgroup X}
    (hP : IsPGroup p P)
    (hmax : ∀ Q : Subgroup X, IsPGroup p Q → P ≤ Q →
      Q ≤ Subgroup.normalizer (P : Set X) → Q = P) :
    ∃ S : Sylow p X, (S : Subgroup X) = P := by
  obtain ⟨S, hPS⟩ := hP.exists_le_sylow
  refine ⟨S, ?_⟩
  by_contra hne
  obtain ⟨x, hxS, hxN, hxP⟩ := Walter.Transitivity.exists_mem_normalizer_not_mem
    (q := ⟨p, hp.out⟩) (isPiSubgroup_singleton_of_isPGroup S.isPGroup') hPS (Ne.symm hne)
  have hQ : IsPGroup p (P ⊔ Subgroup.zpowers x : Subgroup X) :=
    S.isPGroup'.to_le (sup_le hPS ((Subgroup.zpowers_le).mpr hxS))
  have hQN : P ⊔ Subgroup.zpowers x ≤ Subgroup.normalizer (P : Set X) :=
    sup_le Subgroup.le_normalizer ((Subgroup.zpowers_le).mpr hxN)
  have := hmax _ hQ le_sup_left hQN
  exact hxP (this ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x))

theorem le_map_pCore_of_centralize {p : ℕ} [hp : Fact p.Prime] {H : Subgroup X}
    (hH : Group.IsSolvable H)
    (hcomm : ∀ x ∈ H, IsPGroup p (Subgroup.zpowers x) → ∀ q : ℕ, q.Prime → q ≠ p →
      ∀ R : Subgroup X, R ≤ H → IsPGroup q R → x ∈ Subgroup.normalizer (R : Set X) →
        ∀ y ∈ R, x * y = y * x)
    {S : Subgroup X} (hS : IsPGroup p S) (hSH : S ≤ H) :
    S ≤ (pCore p H).map H.subtype := by
  have hcomm' : ∀ x : H, IsPGroup p (Subgroup.zpowers x) → ∀ q : ℕ, q.Prime → q ≠ p →
      ∀ R : Subgroup H, IsPGroup q R → x ∈ Subgroup.normalizer (R : Set H) →
        ∀ y ∈ R, x * y = y * x := by
    intro x hx q hq hqp R hR hxR y hy
    have hx' : IsPGroup p (Subgroup.zpowers (x : X)) := by
      have := hx.map H.subtype
      rwa [MonoidHom.map_zpowers] at this
    have hxR' : (x : X) ∈ Subgroup.normalizer ((R.map H.subtype : Subgroup X) : Set X) :=
      Subgroup.le_normalizer_map H.subtype ⟨x, hxR, rfl⟩
    have := hcomm x x.2 hx' q hq hqp (R.map H.subtype) (Subgroup.map_subtype_le _) (hR.map _)
      hxR' y ⟨y, hy, rfl⟩
    exact Subtype.ext this
  obtain ⟨S', hS'⟩ := (hS.comap_subtype (K := H)).exists_le_sylow
  have hle := sylow_le_pCore_of_centralize hH hcomm' S'
  intro x hx
  exact ⟨⟨x, hSH hx⟩, hle (hS' hx), rfl⟩

end Sylow

namespace JTHyp

variable (h : JTHyp G) (hp3 : h.p = 3)
include hp3

theorem exists_sylow_invariant
    (c : TorusConf h) {p : ℕ} [hp : Fact p.Prime]
    (hpq : p ∣ (h.q - 1) / 2) :
    ∃ P : Sylow p G, c.Cp p ≤ P ∧ c.T₀ ≤ Subgroup.normalizer ((P : Subgroup G) : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp7 := h.seven_le_of_pi hp3 hpq
  have hpC : p ∣ Nat.card c.C := by
    have := c.card_C
    have hq : (h.q - 1) / 2 = Nat.card c.C := by omega
    rwa [hq] at hpq
  set 𝒮 : Set (Subgroup G) :=
    {Q | IsPGroup p Q ∧ c.Cp p ≤ Q ∧ c.T₀ ≤ Subgroup.normalizer (Q : Set G)} with h𝒮
  obtain ⟨P, ⟨hPp, hCpP, hT₀P⟩, hPmax⟩ := (Set.toFinite 𝒮).exists_maximal
    ⟨c.Cp p, c.isPGroup_Cp p, le_rfl, c.T₀_le_normalizer_Cp p⟩
  have hP1 : P ≠ ⊥ := fun h0 => c.Cp_ne_bot p hpC (le_bot_iff.mp (h0 ▸ hCpP))
  set N := Subgroup.normalizer (P : Set G) with hNdef
  have hNs := h.isSolvable_normalizer_of_isPGroup_pi hp3 hpq hPp hP1
  have h8 := h.not_eight_dvd_card_normalizer_of_pi hp3 hpq hPp hP1
  set π : Set Nat.Primes := {⟨2, Nat.prime_two⟩, ⟨p, hp.out⟩} with hπ
  have hT₀π : IsPiSubgroup π (c.T₀.subgroupOf N) := by
    intro r hr
    have hc : Nat.card (c.T₀.subgroupOf N) = 2 ^ 2 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT₀P).toEquiv, c.isKleinFour_T₀.card_four]
      norm_num
    rw [hc] at hr
    have : r.val = 2 := (Nat.prime_dvd_prime_iff_eq r.2 Nat.prime_two).mp (r.2.dvd_of_dvd_pow hr)
    left
    exact Subtype.ext this
  obtain ⟨H, hH, hT₀H⟩ := SolvableHall.solvable_hall_containment hNs π _ hT₀π
  set HG : Subgroup G := H.map N.subtype with hHGdef
  have hHGN : HG ≤ N := Subgroup.map_subtype_le H
  have hHGs : Group.IsSolvable HG := isSolvable_of_le hHGN hNs
  have hcardHG : Nat.card HG = Nat.card H := Subgroup.card_map_of_injective N.subtype_injective
  have hT₀HG : c.T₀ ≤ HG := by
    intro x hx
    exact ⟨⟨x, hT₀P hx⟩, hT₀H (by rw [Subgroup.mem_subgroupOf]; exact hx), rfl⟩
  have hcomm : ∀ x ∈ HG, IsPGroup p (Subgroup.zpowers x) → ∀ q : ℕ, q.Prime → q ≠ p →
      ∀ R : Subgroup G, R ≤ HG → IsPGroup q R → x ∈ Subgroup.normalizer (R : Set G) →
        ∀ y ∈ R, x * y = y * x := by
    intro x _ hx q hq hqp R hRH hR hxR
    by_cases hq2 : q = 2
    · subst hq2
      refine commute_of_card_le_four (by omega) hx ?_ hxR
      obtain ⟨k, hk⟩ := hR.exists_card_eq
      have hdvd : 2 ^ k ∣ Nat.card N := hk ▸ Subgroup.card_dvd_of_le (hRH.trans hHGN)
      have hk2 : k ≤ 2 := by
        by_contra hk2
        exact h8 ((pow_dvd_pow 2 (by omega : 3 ≤ k)).trans hdvd)
      rw [hk]
      calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
        _ = 4 := by norm_num
    ·
      have : Fact q.Prime := ⟨hq⟩
      have hRbot : R = ⊥ := by
        by_contra hR1
        obtain ⟨k, hk⟩ := hR.exists_card_eq
        have hk0 : k ≠ 0 := by
          rintro rfl
          rw [pow_zero, Subgroup.card_eq_one] at hk
          exact hR1 hk
        have hqdvd : q ∣ Nat.card H := by
          rw [← hcardHG]
          exact (dvd_pow_self q hk0).trans (hk ▸ Subgroup.card_dvd_of_le hRH)
        have := hH.p_in_pi_of_p_dvd_card ⟨q, hq⟩ hqdvd
        rcases this with h1 | h1
        · exact hq2 (congrArg Subtype.val h1)
        · exact hqp (congrArg Subtype.val h1)
      intro y hy
      rw [hRbot, Subgroup.mem_bot] at hy
      rw [hy, mul_one, one_mul]
  set O : Subgroup G := (pCore p HG).map HG.subtype with hOdef
  have hOp : IsPGroup p O := pCore_isPGroup.map _
  have hPHG : P ≤ HG := by
    obtain ⟨SH⟩ : Nonempty (Sylow p H) := inferInstance
    have hidx : ¬ p ∣ H.index := fun hd => (hH.p_in_pi_of_p_dvd_index ⟨p, hp.out⟩ hd)
      (Or.inr rfl)
    have hfac : (Nat.card H).factorization p = (Nat.card N).factorization p := by
      rw [← H.card_mul_index, Nat.factorization_mul Nat.card_pos.ne'
        Subgroup.index_ne_zero_of_finite, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hidx, add_zero]
    let SN : Sylow p N := Sylow.ofCard ((SH : Subgroup H).map H.subtype) (by
      rw [Subgroup.card_map_of_injective H.subtype_injective, SH.card_eq_multiplicity, hfac])
    have hPN : (P.subgroupOf N).Normal := Subgroup.normal_in_normalizer
    have hPS : P.subgroupOf N ≤ SN :=
      IsPGroup.le_sylow_of_normal (N := P.subgroupOf N) (hPp.comap_subtype (K := N)) SN
    intro x hx
    have hxN : x ∈ N := Subgroup.le_normalizer hx
    obtain ⟨y, -, hy⟩ := hPS (show (⟨x, hxN⟩ : N) ∈ P.subgroupOf N from hx)
    exact ⟨⟨x, hxN⟩, hy ▸ y.2, rfl⟩
  have hPO : P ≤ O := le_map_pCore_of_centralize hHGs hcomm hPp hPHG
  have hT₀O : c.T₀ ≤ Subgroup.normalizer (O : Set G) := by
    intro x hx
    have hmem : (⟨x, hT₀HG hx⟩ : HG) ∈ Subgroup.normalizer (pCore p HG : Set HG) := by
      have := pCore_normal (p := p) (G := HG)
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top _
    exact Subgroup.le_normalizer_map HG.subtype ⟨_, hmem, rfl⟩
  have hOP : O = P := le_antisymm (hPmax ⟨hOp, hCpP.trans hPO, hT₀O⟩ hPO) hPO
  obtain ⟨S, hS⟩ := exists_sylow_eq_of_maximal hPp fun Q hQp hPQ hQN => by
    obtain ⟨SH⟩ : Nonempty (Sylow p HG) := inferInstance
    have hSH : (SH : Subgroup HG).map HG.subtype ≤ P :=
      hOP ▸ le_map_pCore_of_centralize hHGs hcomm (SH.isPGroup'.map _)
        (Subgroup.map_subtype_le _)
    have hidx : ¬ p ∣ H.index := fun hd => (hH.p_in_pi_of_p_dvd_index ⟨p, hp.out⟩ hd)
      (Or.inr rfl)
    have hfac : (Nat.card H).factorization p = (Nat.card N).factorization p := by
      rw [← H.card_mul_index, Nat.factorization_mul Nat.card_pos.ne'
        Subgroup.index_ne_zero_of_finite, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hidx, add_zero]
    obtain ⟨SQ, hSQ⟩ := (hQp.comap_subtype (K := N)).exists_le_sylow
    have h1 : Nat.card Q ≤ Nat.card (SQ : Subgroup N) := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQN).toEquiv]
      exact Subgroup.card_le_of_le hSQ
    have h2 : Nat.card (SQ : Subgroup N) = Nat.card ((SH : Subgroup HG).map HG.subtype) := by
      rw [Subgroup.card_map_of_injective HG.subtype_injective, SQ.card_eq_multiplicity,
        SH.card_eq_multiplicity, hcardHG, hfac]
    have h3 := Subgroup.card_le_of_le hSH
    exact (Subgroup.eq_of_le_of_card_ge hPQ (by omega)).symm
  exact ⟨S, hS ▸ hCpP, hS ▸ hT₀P⟩

end JTHyp

end CFSG.Walter.JT
