module

public import CFSG.Walter.ReeOrder.JT.Section6A
public import CFSG.Walter.ReeOrder.JT.AuxPSL2Borel
public import CFSG.Walter.ReeOrder.JT.Section4IA

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups
open CFSG

variable {G : Type} [Group G] [Finite G]

structure BorelData (h : JTHyp G) where
  R : Subgroup G
  C : Subgroup G
  τ : G
  R_le_F : R ≤ h.F
  card_R : Nat.card R = h.q
  C_le_F : C ≤ h.F
  card_C : 4 * Nat.card C + 1 = h.q
  C_le_normalizer : C ≤ Subgroup.normalizer (R : Set G)
  τ_mem_F : τ ∈ h.F
  orderOf_τ : orderOf τ = 2
  τ_inv : ∀ x ∈ R, τ * x * τ⁻¹ = x⁻¹
  C_comm : ∀ x ∈ C, x * τ = τ * x

namespace JTHyp

variable (h : JTHyp G)

theorem nonempty_borelData (hp : h.p ≠ 2) (hq5 : h.q % 8 = 5) : Nonempty (BorelData h) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := GaloisField h.p h.f
  have hKcard : Nat.card K = h.q := (GaloisField.card h.p h.f h.f_pos).trans (JTHyp.q_eq h).symm
  obtain ⟨D, hDc, hDcard, hDN, hEcard⟩ :=
    exists_borel_psl2 (K := K) (by rw [hKcard]; exact h.odd_q hp)
  set ι : PSL(2, K) →* G := h.F.subtype.comp h.iso.symm.toMonoidHom with hιdef
  have hι : Function.Injective ι := h.F.subtype_injective.comp h.iso.symm.injective
  have hιF : ∀ x, ι x ∈ h.F := fun x => (h.iso.symm x).2
  set R := (pslE K).map ι with hRdef
  set D' := D.map ι with hD'def
  have hRcard : Nat.card R = h.q := by rw [Subgroup.card_map_of_injective hι, hEcard, hKcard]
  have hD'card : 2 * Nat.card D' + 1 = h.q := by
    rw [Subgroup.card_map_of_injective hι, hDcard, hKcard]
  have hRF : R ≤ h.F := by rintro _ ⟨x, -, rfl⟩; exact hιF x
  have hD'F : D' ≤ h.F := by rintro _ ⟨x, -, rfl⟩; exact hιF x
  have hD'N : D' ≤ Subgroup.normalizer (R : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.le_normalizer_map ι ⟨x, hDN hx, rfl⟩
  have hD'c : IsCyclic D' := isCyclic_of_surjective
    (D.equivMapOfInjective _ hι).toMonoidHom (MulEquiv.surjective _)
  obtain ⟨c, hc⟩ : ∃ c, Nat.card D' = 2 * c := ⟨Nat.card D' / 2, by omega⟩
  obtain ⟨⟨g, hgD⟩, hgen⟩ := IsCyclic.exists_generator (α := D')
  have hgo : orderOf g = 2 * c := by
    rw [← hc, ← orderOf_eq_card_of_forall_mem_zpowers hgen, Subgroup.orderOf_mk]
  have hc0 : c ≠ 0 := by
    rintro rfl
    have := h.five_lt
    rw [← JTHyp.q_eq] at this
    omega
  have hcomm : ∀ x ∈ D', ∀ y ∈ D', x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((IsCyclic.commGroup (α := D')).mul_comm ⟨x, hx⟩ ⟨y, hy⟩)
  set τ := g ^ c with hτdef
  have hτo : orderOf τ = 2 := by
    rw [hτdef, orderOf_pow_of_dvd hc0 ⟨2, by rw [hgo, mul_comm]⟩, hgo]
    exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hc0)
  set C := Subgroup.zpowers (g ^ 2) with hCdef
  have hCcard : Nat.card C = c := by
    rw [hCdef, Nat.card_zpowers, orderOf_pow_of_dvd (by norm_num) ⟨c, hgo⟩, hgo]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  have hCD : C ≤ D' := (Subgroup.zpowers_le).mpr (D'.pow_mem hgD 2)
  have hτD : τ ∈ D' := D'.pow_mem hgD c
  have hτF : τ ∈ h.F := hD'F hτD
  have hpu := psl2UnipotentFacts h.F h.iso hp h.f_pos
  have hτR : τ ∈ Subgroup.normalizer (R : Set G) := hD'N hτD
  have hττ : τ * τ = 1 := by rw [← pow_two, ← hτo, pow_orderOf_eq_one]
  have hRodd : Odd (Nat.card R) := by rw [hRcard]; exact h.odd_q hp
  have hfix : ∀ x ∈ R, τ * x * τ⁻¹ = x → x = 1 := by
    intro x hx hτx
    by_contra hx1
    have hmem : τ ∈ h.F ⊓ Subgroup.centralizer ({x} : Set G) := by
      refine ⟨hτF, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc τ * x = τ * x * τ⁻¹ * τ := by group
        _ = x * τ := by rw [hτx]
    rw [hpu.centralizer R hRF (by rw [hRcard, JTHyp.q_eq]) x hx hx1] at hmem
    have h2 : 2 ∣ Nat.card R := hτo ▸ Subgroup.orderOf_dvd_natCard R hmem
    exact (Nat.not_even_iff_odd.mpr hRodd) (even_iff_two_dvd.mpr h2)
  exact ⟨⟨R, C, τ, hRF, hRcard, hCD.trans hD'F, by omega, hCD.trans hD'N, hτF, hτo,
    inv_of_fpf_involution hττ hτR hfix, fun x hx => hcomm x (hCD hx) τ hτD⟩⟩

end JTHyp

namespace BorelData

variable {h : JTHyp G} (b : BorelData h)

theorem odd_card_C (hq5 : h.q % 8 = 5) : Odd (Nat.card b.C) := by
  have := b.card_C
  exact ⟨Nat.card b.C / 2, by omega⟩

theorem three_le_card_C (hq5 : h.q % 8 = 5) : 3 ≤ Nat.card b.C := by
  have := b.card_C
  have h5 := h.five_lt
  rw [← JTHyp.q_eq] at h5
  omega

theorem τ_comm_t : b.τ * h.t = h.t * b.τ := h.commute_of_mem_F b.τ_mem_F

theorem C_comm_t {x : G} (hx : x ∈ b.C) : x * h.t = h.t * x := h.commute_of_mem_F (b.C_le_F hx)

theorem R_comm_t {x : G} (hx : x ∈ b.R) : x * h.t = h.t * x := h.commute_of_mem_F (b.R_le_F hx)

theorem τ_mul_τ : b.τ * b.τ = 1 := by rw [← pow_two, ← b.orderOf_τ, pow_orderOf_eq_one]

theorem τ_ne_one : b.τ ≠ 1 := by
  intro h0
  have := b.orderOf_τ
  rw [h0, orderOf_one] at this
  omega

theorem τ_ne_t : b.τ ≠ h.t := fun h0 => h.t_not_mem (h0 ▸ b.τ_mem_F)

@[expose] noncomputable def T : Subgroup G :=
  GorensteinWalter.kleinFourOfCommutingInvolutions h.t b.τ h.t_mul_t b.τ_mul_τ b.τ_comm_t.symm

theorem isKleinFour_T : IsKleinFour b.T :=
  GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions _ _ _ _ h.t_ne_one b.τ_ne_one
    (Ne.symm b.τ_ne_t) _

theorem mem_T_iff {x : G} : x ∈ b.T ↔ x = h.t * b.τ ∨ x = h.t ∨ x = b.τ ∨ x = 1 := Iff.rfl

theorem t_mem_T : h.t ∈ b.T := b.mem_T_iff.mpr (Or.inr (Or.inl rfl))

theorem τ_mem_T : b.τ ∈ b.T := b.mem_T_iff.mpr (Or.inr (Or.inr (Or.inl rfl)))

theorem mem_centralizer_T {x : G} (h1 : x * h.t = h.t * x) (h2 : x * b.τ = b.τ * x) :
    x ∈ Subgroup.centralizer (b.T : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rcases b.mem_T_iff.mp hy with rfl | rfl | rfl | rfl
  · calc h.t * b.τ * x = h.t * (b.τ * x) := by group
      _ = h.t * (x * b.τ) := by rw [h2]
      _ = (h.t * x) * b.τ := by group
      _ = (x * h.t) * b.τ := by rw [h1]
      _ = x * (h.t * b.τ) := by group
  · exact h1.symm
  · exact h2.symm
  · rw [one_mul, mul_one]

theorem exists_setup : ∃ s : Setup h, s.T = b.T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 b.T := IsPGroup.of_card (n := 2) (b.isKleinFour_T.card_four.trans
    (by norm_num))
  obtain ⟨S, hS⟩ := hT2.exists_le_sylow
  exact ⟨⟨S, hS b.t_mem_T, b.T, hS, b.isKleinFour_T, b.t_mem_T⟩, rfl⟩

variable (hp : h.p ≠ 2) (hq5 : h.q % 8 = 5)
include hp hq5

theorem Q_eq
    {s : Setup h} (hsT : s.T = b.T) : s.Q = b.C := by
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · intro x hx
    rw [s.mem_Q_iff hp, hsT]
    exact ⟨b.mem_centralizer_T (b.C_comm_t hx) (b.C_comm x hx),
      Odd.of_dvd_nat (b.odd_card_C hq5) (Subgroup.orderOf_dvd_natCard _ hx)⟩
  · have h1 := b.card_C
    rcases s.four_mul_card_Q_cases hp with ⟨h4, -⟩ | ⟨-, h4⟩
    · omega
    · omega

theorem mem_C_of_commute
    {x : G} (h1 : x * h.t = h.t * x) (h2 : x * b.τ = b.τ * x)
    (hodd : Odd (orderOf x)) : x ∈ b.C := by
  obtain ⟨s, hsT⟩ := b.exists_setup
  rw [← b.Q_eq hp hq5 hsT, s.mem_Q_iff hp, hsT]
  exact ⟨b.mem_centralizer_T h1 h2, hodd⟩

omit hp hq5 in
theorem coprime_card_C : Nat.Coprime (Nat.card b.C) h.p := by
  refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr fun hpC => ?_)
  have h1 := b.card_C
  have hpq : h.p ∣ h.q := by rw [JTHyp.q_eq]; exact dvd_pow_self _ h.f_pos
  have : h.p ∣ 1 := (Nat.dvd_add_right (Dvd.dvd.mul_left hpC 4)).mp (h1 ▸ hpq)
  exact (Fact.out : h.p.Prime).one_lt.ne' (Nat.dvd_one.mp this)

variable (hp3 : h.p ≠ 3)
include hp3

theorem card_inf_centralizer
    {u : G} (hu : orderOf u = 2) {Y : Subgroup G}
    (hYu : Y ≤ Subgroup.centralizer ({u} : Set G)) (hodd : Odd (Nat.card Y)) (hCY : b.C ≤ Y) :
    Nat.card Y = Nat.card b.C ∨ (Nat.card Y = h.q * Nat.card b.C ∧ ∃ N : Subgroup G, N ≤ Y ∧
      (∀ x ∈ Y, x ∈ Subgroup.normalizer (N : Set G)) ∧ IsPGroup h.p N ∧ Nat.card N = h.q) := by
  have hcC := b.card_C
  have hC3 := b.three_le_card_C hq5
  have hCodd := b.odd_card_C hq5
  have hcdvd : Nat.card b.C ∣ Nat.card Y := Subgroup.card_dvd_of_le hCY
  have hp5 : 5 ≤ h.p := by
    have := (Fact.out : h.p.Prime).two_le
    have h4 : h.p ≠ 4 := fun h4 => by
      have := (Fact.out : h.p.Prime)
      rw [h4] at this
      norm_num at this
    omega
  rcases h.odd_cases hp hu hYu hodd with
    ⟨N, hNY, hNn, hNp, m, t, hNcard, hmf, hYcard, htq, htm⟩ | hdvd
  ·
    have htodd : Odd t := Odd.of_dvd_nat hodd ⟨h.p ^ m, by rw [hYcard, mul_comm]⟩
    have ht2c : t ∣ 2 * Nat.card b.C := by
      have : (h.q - 1) / 2 = 2 * Nat.card b.C := by omega
      rwa [this] at htq
    have htc : t ∣ Nat.card b.C :=
      Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_right.mpr htodd) ht2c
    have hct : Nat.card b.C ∣ t := by
      have h1 : Nat.card b.C ∣ h.p ^ m * t := hYcard ▸ hcdvd
      exact Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.pow_right m b.coprime_card_C) h1
    have htC : t = Nat.card b.C := Nat.dvd_antisymm htc hct
    rw [htC] at hYcard htm
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · left
      rw [hYcard, hm0, pow_zero, one_mul]
    · rcases lt_or_eq_of_le hmf with hmf' | hmf'
      · exfalso
        have hpm1 : 1 < h.p ^ m := Nat.one_lt_pow hm0.ne' (Fact.out : h.p.Prime).one_lt
        have hle : Nat.card b.C ≤ h.p ^ m - 1 := Nat.le_of_dvd (by omega) htm
        have hq : h.p ^ m * h.p ≤ h.q := by
          rw [JTHyp.q_eq, ← pow_succ]
          exact Nat.pow_le_pow_right (Fact.out : h.p.Prime).pos hmf'
        have h5 : h.p ^ m * 5 ≤ h.p ^ m * h.p := Nat.mul_le_mul_left _ hp5
        omega
      · right
        refine ⟨by rw [hYcard, hmf', ← JTHyp.q_eq], N, hNY, hNn, hNp, ?_⟩
        rw [hNcard, hmf', ← JTHyp.q_eq]
  ·
    exfalso
    have h1 : Nat.card b.C ∣ 2 * Nat.card b.C + 1 := by
      have : (h.q + 1) / 2 = 2 * Nat.card b.C + 1 := by omega
      rw [← this]
      exact hcdvd.trans hdvd
    have : Nat.card b.C ∣ 1 := (Nat.dvd_add_right (Dvd.dvd.mul_left (dvd_refl _) 2)).mp h1
    have := Nat.le_of_dvd one_pos this
    omega

end BorelData

end CFSG.Walter.JT
