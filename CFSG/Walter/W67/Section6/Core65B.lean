module

public import CFSG.Walter.W67.Section6.Core65A
public import CFSG.Walter.W67.Section5.Prop52
public import CFSG.Walter.W67.Section6.Core62H

public section

namespace CFSG.Walter.W67.Sec65

open Sec6

variable {G : Type} [Group G] [Finite G]

theorem eq_of_prime_dvd_48 {ℓ : ℕ} (hℓ : ℓ.Prime) (hd : ℓ ∣ 48) : ℓ = 2 ∨ ℓ = 3 := by
  rw [show (48 : ℕ) = 2 ^ 4 * 3 by norm_num] at hd
  rcases (Nat.Prime.dvd_mul hℓ).mp hd with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp (hℓ.dvd_of_dvd_pow h))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp h)

theorem eq_of_prime_dvd_mul_seven_pow {ℓ m k : ℕ} (hℓ : ℓ.Prime) (hd : ℓ ∣ m * 7 ^ k)
    (hm : ∀ q : ℕ, q.Prime → q ∣ m → q = 2 ∨ q = 3) : ℓ = 2 ∨ ℓ = 3 ∨ ℓ = 7 := by
  rcases (Nat.Prime.dvd_mul hℓ).mp hd with h | h
  · rcases hm ℓ hℓ h with h2 | h3
    · exact Or.inl h2
    · exact Or.inr (Or.inl h3)
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hℓ (by norm_num)).mp (hℓ.dvd_of_dvd_pow h)))

theorem eq_of_prime_dvd_6 {ℓ : ℕ} (hℓ : ℓ.Prime) (hd : ℓ ∣ 6) : ℓ = 2 ∨ ℓ = 3 := by
  rw [show (6 : ℕ) = 2 * 3 by norm_num] at hd
  rcases (Nat.Prime.dvd_mul hℓ).mp hd with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h)
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp h)

theorem eq_of_prime_dvd_342 {ℓ : ℕ} (hℓ : ℓ.Prime) (hd : ℓ ∣ 342) : ℓ = 2 ∨ ℓ = 3 ∨ ℓ = 19 := by
  rw [show (342 : ℕ) = 2 * 3 ^ 2 * 19 by norm_num] at hd
  rcases (Nat.Prime.dvd_mul hℓ).mp hd with h | h
  · rcases (Nat.Prime.dvd_mul hℓ).mp h with h' | h'
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h')
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp
        (hℓ.dvd_of_dvd_pow h')))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hℓ (by norm_num)).mp h))

theorem inf_centralizer_ne_bot {r : ℕ} [Fact r.Prime] {X : Subgroup G} (hX : IsPGroup r X)
    (hX1 : X ≠ ⊥) : X ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥ := by
  have : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot X).mpr hX1
  have := hX.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center X)
  intro hbot
  apply hz
  have hzX : ((z : X) : G) ∈ X ⊓ Subgroup.centralizer (X : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨(z : X).2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have := Subgroup.mem_center_iff.mp z.2 ⟨y, hy⟩
    exact congrArg Subtype.val this
  rw [hbot, Subgroup.mem_bot] at hzX
  exact Subtype.ext (Subtype.ext hzX)

theorem exists_invariant_sylow {H Q : Subgroup G} {ρ : G} (hρ3 : orderOf ρ = 3)
    (hρH : ρ ∈ Subgroup.normalizer (H : Set G)) (h3 : ¬ 3 ∣ Nat.card H) (hQH : Q ≤ H)
    (hQ : IsPGroup 7 Q) (hρQ : ρ ∈ Subgroup.normalizer (Q : Set G)) :
    ∃ S : Subgroup G, Q ≤ S ∧ S ≤ H ∧ IsPGroup 7 S ∧
      Nat.card S = 7 ^ (Nat.card H).factorization 7 ∧ ρ ∈ Subgroup.normalizer (S : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hN : Subgroup.zpowers ρ ≤ Subgroup.normalizer (H : Set G) := Subgroup.zpowers_le.mpr hρH
  let : MulDistribMulAction (Subgroup.zpowers ρ) H := MulDistribMulAction.compHom H (conjHom hN)
  have hsmul : ∀ (a : Subgroup.zpowers ρ) (x : H), ((a • x : H) : G) = a * x * (a : G)⁻¹ :=
    fun _ _ => rfl
  have hA : IsPGroup 3 (Subgroup.zpowers ρ) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hρ3, pow_one])
  have hQ' : IsPGroup 7 (Q.subgroupOf H) := hQ.comap_of_injective H.subtype H.subtype_injective
  have hinv : DisconnectedInvolutionGraph.Helpers.InvariantSubgroup
      (A := Subgroup.zpowers ρ) (Q.subgroupOf H) := by
    intro a x hx
    rw [Subgroup.mem_subgroupOf, hsmul]
    have ha : (a : G) ∈ Subgroup.normalizer (Q : Set G) := (Subgroup.zpowers_le.mpr hρQ) a.2
    exact (Subgroup.mem_normalizer_iff.mp ha x).mp hx
  obtain ⟨S, hQS, hSinv⟩ :=
    DisconnectedInvolutionGraph.Helpers.coprime_pgroup_invariant_sylow_containment 3 7 hA h3 _
      hQ' hinv
  refine ⟨(S : Subgroup H).map H.subtype, ?_, Subgroup.map_subtype_le _, S.isPGroup'.map _, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨x, hQH hx⟩, hQS hx, rfl⟩
  · rw [Subgroup.card_map_of_injective H.subtype_injective, Sylow.card_eq_multiplicity]
  · apply Sec53.mem_normalizer_of_conj_le
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨_, hSinv ⟨ρ, Subgroup.mem_zpowers ρ⟩ y hy, rfl⟩

namespace Hyp65

variable {e u ρ : G} (h : Hyp65 G e u ρ)
include h

theorem prime_dvd_card_normalizer_P {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hdvd : ℓ ∣ Nat.card (Subgroup.normalizer ((PP e u : Subgroup G) : Set G))) :
    ℓ = 3 ∨ ℓ = 7 := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  set N := Subgroup.normalizer ((PP e u : Subgroup G) : Set G) with hN
  obtain ⟨⟨y, hyN⟩, hyo⟩ := exists_prime_orderOf_dvd_card' (G := N) ℓ hdvd
  rw [Subgroup.orderOf_mk] at hyo
  by_cases h2 : ℓ = 2
  · exfalso
    have hy2 : y * y = 1 := by rw [← pow_two, ← h2, ← hyo, pow_orderOf_eq_one]
    have hy1 := h.eq_one_of_mem_normalizer h.isPGroup_P le_rfl hyN hy2
    rw [hy1, orderOf_one] at hyo
    exact hℓ.one_lt.ne hyo
  by_contra h37
  push Not at h37
  have hmod := Sec64.card_modEq_card_inf_centralizer (ℓ := ℓ) hyN (k := 1)
    (by rw [pow_one, ← hyo, pow_orderOf_eq_one])
  rw [h.card_P] at hmod
  have hdvd' : Nat.card ↥(PP e u ⊓ Subgroup.centralizer ({y} : Set G)) ∣ 7 ^ 2 :=
    h.card_P ▸ Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨j, hj, hjc⟩ := (Nat.dvd_prime_pow (by norm_num)).mp hdvd'
  rw [hjc] at hmod
  interval_cases j
  · have h48 := (Nat.modEq_iff_dvd' (by norm_num)).mp hmod.symm
    norm_num at h48
    rcases eq_of_prime_dvd_48 hℓ h48 with h' | h'
    · exact h2 h'
    · exact h37.1 h'
  · have h42 := (Nat.modEq_iff_dvd' (by norm_num)).mp hmod.symm
    norm_num at h42
    rcases eq_of_prime_dvd_mul_seven_pow (m := 6) (k := 1) hℓ (by simpa using h42)
      (fun q hq hqd => eq_of_prime_dvd_6 hq hqd) with h' | h' | h'
    · exact h2 h'
    · exact h37.1 h'
    · exact h37.2 h'
  ·
    have heq : PP e u ⊓ Subgroup.centralizer ({y} : Set G) = PP e u :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hjc, h.card_P])
    have hyC : y ∈ Subgroup.centralizer ((PP e u : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hx' : x ∈ PP e u ⊓ Subgroup.centralizer ({y} : Set G) := by rw [heq]; exact hx
      exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx').2
    have hyP := h.centralizer_P_le hyC
    have h49 := Subgroup.orderOf_dvd_natCard _ hyP
    rw [hyo, h.card_P] at h49
    exact h37.2 ((Nat.prime_dvd_prime_iff_eq hℓ (by norm_num)).mp (hℓ.dvd_of_dvd_pow h49))

theorem normalizer_P_eq_of_sylow (hPc : Nat.card (PP e u) = 7 ^ (Nat.card G).factorization 7) :
    Subgroup.normalizer ((PP e u : Subgroup G) : Set G) = PP e u ⊔ Subgroup.zpowers ρ := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact h.normalizer_eq_sup h.isPGroup_P h.ρ_mem_normalizer_P h.P_inf_centralizer_ρ
    (card_eq_of_le_of_card_eq Subgroup.le_normalizer hPc)
    (fun _ hℓ hd => h.prime_dvd_card_normalizer_P hℓ hd)

theorem exists_P₁ (hPc : Nat.card (PP e u) ≠ 7 ^ (Nat.card G).factorization 7) :
    ∃ P₁ : Subgroup G, PP e u ≤ P₁ ∧ IsPGroup 7 P₁ ∧ Nat.card (PP e u) < Nat.card P₁ ∧
      ρ ∈ Subgroup.normalizer (P₁ : Set G) ∧
      P₁ ⊓ Subgroup.centralizer (P₁ : Set G) = Subgroup.zpowers u := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := Subgroup.normalizer ((PP e u : Subgroup G) : Set G) with hN
  have hNc := eq_three_pow_mul_seven_pow Nat.card_pos.ne'
    (fun _ hℓ hd => h.prime_dvd_card_normalizer_P hℓ hd)
  have h3 := h.factorization_three_le h.ρ_mem_normalizer_P h.P_inf_centralizer_ρ
  rw [← hN] at hNc h3
  obtain ⟨S⟩ : Nonempty (Sylow 7 N) := inferInstance
  have hidx : (S : Subgroup N).index = 3 ^ (Nat.card N).factorization 3 := by
    have h1 := (S : Subgroup N).card_mul_index
    rw [Sylow.card_eq_multiplicity] at h1
    conv_rhs at h1 => rw [hNc]
    rw [mul_comm (3 ^ _)] at h1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  have hn : Nat.card (Sylow 7 N) = 1 := by
    have hd : Nat.card (Sylow 7 N) ∣ 3 := by
      refine (hidx ▸ Sylow.card_dvd_index S).trans ?_
      calc 3 ^ (Nat.card N).factorization 3 ∣ 3 ^ 1 := pow_dvd_pow 3 h3
        _ = 3 := pow_one 3
    have hm := card_sylow_modEq_one 7 N
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h1
    · exact h1
    · rw [h1] at hm
      exact absurd hm (by decide)
  have : Subsingleton (Sylow 7 N) := (Nat.card_eq_one_iff_unique.mp hn).1
  have hSn : (S : Subgroup N).Normal := Sylow.normal_of_subsingleton S
  set P₁ := (S : Subgroup N).map N.subtype with hP₁
  have hP₁7 : IsPGroup 7 P₁ := S.isPGroup'.map _
  have hP₁N : P₁ ≤ N := Subgroup.map_subtype_le _
  have hPP₁ : PP e u ≤ P₁ := by
    have hPn : ((PP e u).subgroupOf N).Normal := Subgroup.normal_in_normalizer
    have hP7 : IsPGroup 7 ((PP e u).subgroupOf N) :=
      h.isPGroup_P.comap_of_injective N.subtype N.subtype_injective
    have := hP7.le_sylow_of_normal S
    intro x hx
    exact ⟨⟨x, Subgroup.le_normalizer hx⟩, this hx, rfl⟩
  have hρP₁ : ρ ∈ Subgroup.normalizer (P₁ : Set G) := by
    apply Sec53.mem_normalizer_of_conj_le
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨_, hSn.conj_mem y hy ⟨ρ, h.ρ_mem_normalizer_P⟩, rfl⟩
  have hlt : Nat.card (PP e u) < Nat.card P₁ := by
    obtain ⟨Q, hQ7, hPQ, hQN, hQP⟩ : ∃ Q : Subgroup G, IsPGroup 7 Q ∧ PP e u ≤ Q ∧ Q ≤ N ∧
        ¬ Q ≤ PP e u := by
      by_contra hno
      push Not at hno
      exact hPc (card_eq_of_normalizer h.isPGroup_P fun Q hQ hPQ hQN => hno Q hQ hPQ hQN)
    have hQP₁ : Q ≤ P₁ := by
      obtain ⟨S', hS'⟩ := (hQ7.comap_of_injective N.subtype N.subtype_injective).exists_le_sylow
      rw [Subsingleton.elim S' S] at hS'
      intro x hx
      exact ⟨⟨x, hQN hx⟩, hS' hx, rfl⟩
    refine lt_of_le_of_ne (Subgroup.card_le_of_le hPP₁) fun heq => hQP ?_
    rw [Subgroup.eq_of_le_of_card_ge hPP₁ heq.symm.le]
    exact hQP₁
  refine ⟨P₁, hPP₁, hP₁7, hlt, hρP₁, ?_⟩
  set Z := P₁ ⊓ Subgroup.centralizer (P₁ : Set G) with hZ
  have hZP : Z ≤ PP e u := fun z hz => h.centralizer_P_le
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hPP₁) (Subgroup.mem_inf.mp hz).2)
  have hZ1 : Z ≠ ⊥ := inf_centralizer_ne_bot hP₁7 (by
    intro hbot
    rw [hbot, Subgroup.card_bot, h.card_P] at hlt
    omega)
  have hZP' : Z ≠ PP e u := by
    intro heq
    have hPC : PP e u ≤ Subgroup.centralizer (P₁ : Set G) := heq ▸ inf_le_right
    have hP₁P : P₁ ≤ PP e u := h.centralizer_P_le.trans' (Subgroup.le_centralizer_iff.mp hPC)
    exact absurd (Subgroup.card_le_of_le hP₁P) (not_le.mpr hlt)
  have hZc : Nat.card Z = 7 := by
    obtain ⟨j, hj, hjc⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 7)).mp
      (h.card_P ▸ Subgroup.card_dvd_of_le hZP)
    interval_cases j
    · exact absurd (Subgroup.card_eq_one.mp (by rw [hjc, pow_zero])) hZ1
    · rw [hjc, pow_one]
    · exact absurd (Subgroup.eq_of_le_of_card_ge hZP (by rw [hjc, h.card_P])) hZP'
  have hρZ : ρ ∈ Subgroup.normalizer (Z : Set G) :=
    mem_normalizer_inf hρP₁ (normalizer_le_normalizer_centralizer' P₁ hρP₁)
  rcases h.eq_E_or_U hZP hZc hρZ with hZE | hZU
  · exfalso
    have heZ : e ∈ Z := hZE ▸ Subgroup.mem_zpowers e
    have hP₁e : P₁ ≤ Subgroup.centralizer ({e} : Set G) := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp heZ).2 x hx)
    have := h.card_seven P₁ hP₁7 hP₁e
    rw [h.card_P] at hlt
    omega
  · exact hZU

theorem exists_sylow_le_centralizer_u (hPc : Nat.card (PP e u) ≠ 7 ^ (Nat.card G).factorization 7) :
    ∃ T : Subgroup G, Nat.card T = 7 ^ (Nat.card G).factorization 7 ∧
      T ≤ Subgroup.centralizer ({u} : Set G) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨P₁, hPP₁, hP₁7, hlt, -, hZ⟩ := h.exists_P₁ hPc
  obtain ⟨T, hT⟩ := hP₁7.exists_le_sylow
  refine ⟨T, Sylow.card_eq_multiplicity T, ?_⟩
  set ZT := (T : Subgroup G) ⊓ Subgroup.centralizer ((T : Subgroup G) : Set G) with hZTdef
  have hZT : ZT ≤ Subgroup.zpowers u := by
    rw [← hZ]
    intro z hz
    obtain ⟨-, hzC⟩ := Subgroup.mem_inf.mp hz
    have hzC₁ : z ∈ Subgroup.centralizer (P₁ : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hT) hzC
    have hzP : z ∈ PP e u := h.centralizer_P_le
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (hPP₁.trans hT)) hzC)
    exact Subgroup.mem_inf.mpr ⟨hPP₁ hzP, hzC₁⟩
  have hZT1 : ZT ≠ ⊥ := inf_centralizer_ne_bot T.isPGroup' (by
    intro hbot
    have := Subgroup.card_le_of_le (hPP₁.trans hT)
    rw [hbot, Subgroup.card_bot, h.card_P] at this
    omega)
  have hZTU : ZT = Subgroup.zpowers u := by
    have hdvd : Nat.card ZT ∣ 7 := h.card_U ▸ Subgroup.card_dvd_of_le hZT
    rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h1 | h7
    · exact absurd (Subgroup.card_eq_one.mp h1) hZT1
    · exact Subgroup.eq_of_le_of_card_ge hZT (by rw [h7, h.card_U])
  have hu : u ∈ ZT := hZTU ▸ Subgroup.mem_zpowers u
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hu).2 x hx)

theorem not_three_dvd_card_centralizer_u : ¬ 3 ∣ Nat.card (Subgroup.centralizer ({u} : Set G)) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  intro h3
  obtain ⟨⟨R, hRu⟩, hRo⟩ := exists_prime_orderOf_dvd_card' (p := 3)
    (G := Subgroup.centralizer ({u} : Set G)) h3
  rw [Subgroup.orderOf_mk] at hRo
  obtain ⟨k, hkE, hfac⟩ := h.centralizer_three R hRo
  have hUR : Subgroup.zpowers u ≤ Subgroup.centralizer ({R} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hRu).symm)
  obtain ⟨c, -, hc⟩ := exists_conj_of_sylowIn hkE hUR
    (by rw [card_cj, h.card_E, hfac, pow_one]) (by rw [h.card_U, hfac, pow_one])
  rw [← cj_mul] at hc
  have hNU : Subgroup.normalizer ((Subgroup.zpowers u : Subgroup G) : Set G) ≤
      Subgroup.centralizer ((Subgroup.zpowers u : Subgroup G) : Set G) := by
    rw [hc, ← cj_normalizer, ← cj_centralizer]
    exact cj_mono h.normalizer_E
  have := Subgroup.mem_centralizer_iff.mp (hNU h.ρ_mem) u (Subgroup.mem_zpowers u)
  exact h.ρ_not_comm this.symm

theorem exists_Pstar (hPc : Nat.card (PP e u) ≠ 7 ^ (Nat.card G).factorization 7) :
    ∃ X : Subgroup G, PP e u ≤ X ∧ IsPGroup 7 X ∧
      Nat.card X = 7 ^ (Nat.card G).factorization 7 ∧ ρ ∈ Subgroup.normalizer (X : Set G) ∧
      X ≤ Subgroup.centralizer ({u} : Set G) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set H := Subgroup.centralizer ({u} : Set G) with hH
  have hρH : ρ ∈ Subgroup.normalizer (H : Set G) := by
    rw [hH, ← Sec52.centralizer_zpowers_eq]
    exact normalizer_le_normalizer_centralizer' _ h.ρ_mem
  have hPH : PP e u ≤ H := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h.P_comm x hx u u_mem_P)
  obtain ⟨S, hPS, hSH, hS7, hSc, hρS⟩ := exists_invariant_sylow h.orderOf_ρ hρH
    h.not_three_dvd_card_centralizer_u hPH h.isPGroup_P h.ρ_mem_normalizer_P
  obtain ⟨T, hTc, hTH⟩ := h.exists_sylow_le_centralizer_u hPc
  have hTc' := card_eq_of_le_of_card_eq hTH hTc
  rw [hTc] at hTc'
  refine ⟨S, hPS, hS7, ?_, hρS, hSH⟩
  rw [hSc, hTc']

theorem inf_centralizer_ρ_of_le {X : Subgroup G} (hX : IsPGroup 7 X) (hPX : PP e u ≤ X) :
    X ⊓ Subgroup.centralizer ({ρ} : Set G) = Subgroup.zpowers e := by
  refine (Subgroup.eq_of_le_of_card_ge (le_inf (E_le_P.trans hPX) h.E_le_centralizer_ρ) ?_).symm
  rw [h.card_E]
  exact h.card_le_seven_of_le_centralizer_ρ (hX.to_le inf_le_left) inf_le_right

theorem inf_centralizer_e_of_le {X : Subgroup G} (hX : IsPGroup 7 X) (hPX : PP e u ≤ X) :
    X ⊓ Subgroup.centralizer ({e} : Set G) = PP e u := by
  have hPe : PP e u ≤ Subgroup.centralizer ({e} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h.P_comm x hx e e_mem_P)
  refine (Subgroup.eq_of_le_of_card_ge (le_inf hPX hPe) ?_).symm
  rw [h.card_P]
  exact h.card_seven _ (hX.to_le inf_le_left) inf_le_right

theorem inf_centralizer_Pstar {X : Subgroup G} (hPX : PP e u ≤ X)
    (hXu : X ≤ Subgroup.centralizer ({u} : Set G)) (hXc : 7 ^ 2 < Nat.card X) :
    X ⊓ Subgroup.centralizer (X : Set G) = Subgroup.zpowers u ∧
      Subgroup.centralizer (X : Set G) ≤ Subgroup.zpowers u := by
  have hCP : Subgroup.centralizer (X : Set G) ≤ PP e u :=
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hPX)).trans h.centralizer_P_le
  have huC : u ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hXu hx))
  have hUZ : Subgroup.zpowers u ≤ X ⊓ Subgroup.centralizer (X : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hPX u_mem_P, huC⟩)
  have hZP : X ⊓ Subgroup.centralizer (X : Set G) ≤ PP e u := inf_le_right.trans hCP
  have hZne : X ⊓ Subgroup.centralizer (X : Set G) ≠ PP e u := by
    intro heq
    have hPC : PP e u ≤ Subgroup.centralizer (X : Set G) := heq ▸ inf_le_right
    have hXP : X ≤ PP e u := h.centralizer_P_le.trans' (Subgroup.le_centralizer_iff.mp hPC)
    have := Subgroup.card_le_of_le hXP
    rw [h.card_P] at this
    omega
  have hZ : X ⊓ Subgroup.centralizer (X : Set G) = Subgroup.zpowers u := by
    obtain ⟨j, hj, hjc⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 7)).mp
      (h.card_P ▸ Subgroup.card_dvd_of_le hZP)
    interval_cases j
    · have := Subgroup.card_le_of_le hUZ
      rw [hjc, h.card_U] at this
      omega
    · exact (Subgroup.eq_of_le_of_card_ge hUZ (by rw [hjc, h.card_U, pow_one])).symm
    · exact absurd (Subgroup.eq_of_le_of_card_ge hZP (by rw [hjc, h.card_P])) hZne
  refine ⟨hZ, fun x hx => ?_⟩
  rw [← hZ]
  exact Subgroup.mem_inf.mpr ⟨hPX (hCP hx), hx⟩

end Hyp65

end CFSG.Walter.W67.Sec65
