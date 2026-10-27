module

public import CFSG.Walter.W67.Section5.P56K3b
public import CFSG.Walter.W67.Section5.P56Quad

public section

namespace CFSG.Walter.W67

variable {G : Type} [Group G] [Finite G]

namespace Sec56

omit [Finite G] in
theorem map_hallPResidual_le {p : ℕ} {H K : Subgroup G} (hHK : H ≤ K) :
    (BenderSuzuki.External.hallPResidual p H).map H.subtype ≤
      (BenderSuzuki.External.hallPResidual p K).map K.subtype := by
  rw [BenderSuzuki.External.hallPResidual, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨h, hh, rfl⟩
  refine ⟨⟨h, hHK h.2⟩, Subgroup.subset_closure ?_, rfl⟩
  change Nat.Coprime p (orderOf (⟨h, hHK h.2⟩ : K))
  rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe]
  exact hh

theorem exists_mem_normalizer_of_lt {p : ℕ} [Fact p.Prime] {V W : Subgroup G}
    (hW : IsPGroup p W) (hVW : V < W) :
    ∃ w ∈ W, w ∉ V ∧ w ∈ Subgroup.normalizer (V : Set G) := by
  have : Group.IsNilpotent W := hW.isNilpotent
  have hlt : V.subgroupOf W < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => hVW.ne (le_antisymm hVW.le ?_)
    intro w hw
    have : (⟨w, hw⟩ : W) ∈ V.subgroupOf W := by rw [h]; exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  obtain ⟨w, hwN, hwV⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  refine ⟨w, w.2, fun h => hwV (Subgroup.mem_subgroupOf.mpr h), ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro r
  constructor
  · intro hr
    have := (Subgroup.mem_normalizer_iff.mp hwN ⟨r, hVW.le hr⟩).mp
      (Subgroup.mem_subgroupOf.mpr hr)
    exact Subgroup.mem_subgroupOf.mp this
  · intro hr
    have hrW : r ∈ W := by
      have h1 : (w : G) * r * (w : G)⁻¹ ∈ W := hVW.le hr
      have : r = (w : G)⁻¹ * ((w : G) * r * (w : G)⁻¹) * w := by group
      rw [this]
      exact W.mul_mem (W.mul_mem (W.inv_mem w.2) h1) w.2
    have := (Subgroup.mem_normalizer_iff.mp hwN ⟨r, hrW⟩).mpr (Subgroup.mem_subgroupOf.mpr hr)
    exact Subgroup.mem_subgroupOf.mp this

end Sec56

namespace Frame5

variable {s : Std G} {f5 : Frame5 s}

theorem eq_one_of_mul_mem_centralizer (h26i : S_lemma_2_6_i) {P : Subgroup G} (hP1 : P ≠ ⊥)
    (hBP : f5.B ≤ Subgroup.normalizer (P : Set G))
    (hfpf : ∀ b ∈ f5.B, b ≠ 1 → ∀ y ∈ P, b * y = y * b → y = 1) {b e : G} (hb : b ∈ f5.B)
    (he : e ∈ s.fr.E) (hbeC : b * e ∈ Subgroup.centralizer (P : Set G)) : b = 1 ∧ e = 1 := by
  have hBC : f5.B ⊓ Subgroup.centralizer (P : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    obtain ⟨hcB, hcC⟩ := Subgroup.mem_inf.mp hc
    rw [Subgroup.mem_bot]
    by_contra hc1
    obtain ⟨y, hy, hy1⟩ := (Subgroup.bot_or_exists_ne_one P).resolve_left hP1
    exact hy1 (hfpf c hcB hc1 y hy (Subgroup.mem_centralizer_iff.mp hcC y hy).symm)
  have hbeB : ∀ b' ∈ f5.B, b * e * b' = b' * (b * e) := by
    intro b' hb'
    have hbeN : b * e ∈ Subgroup.normalizer (f5.B : Set G) :=
      Subgroup.mul_mem _ (Subgroup.le_normalizer hb) (f5.E_le_normalizer_B he)
    have h1 : b * e * b' * (b * e)⁻¹ * b'⁻¹ ∈ f5.B :=
      f5.B.mul_mem ((Subgroup.mem_normalizer_iff.mp hbeN b').mp hb') (f5.B.inv_mem hb')
    have h2 : b * e * b' * (b * e)⁻¹ * b'⁻¹ ∈ Subgroup.centralizer (P : Set G) := by
      have h3 : b' * (b * e)⁻¹ * b'⁻¹ ∈ Subgroup.centralizer (P : Set G) :=
        (Subgroup.mem_normalizer_iff.mp (Sec54.mem_normalizer_centralizer (hBP hb'))
          (b * e)⁻¹).mp (Subgroup.inv_mem _ hbeC)
      rw [show b * e * b' * (b * e)⁻¹ * b'⁻¹ = (b * e) * (b' * (b * e)⁻¹ * b'⁻¹) by group]
      exact Subgroup.mul_mem _ hbeC h3
    have h4 : b * e * b' * (b * e)⁻¹ * b'⁻¹ ∈ f5.B ⊓ Subgroup.centralizer (P : Set G) :=
      Subgroup.mem_inf.mpr ⟨h1, h2⟩
    rw [hBC, Subgroup.mem_bot] at h4
    calc b * e * b' = (b * e * b' * (b * e)⁻¹ * b'⁻¹) * (b' * (b * e)) := by group
      _ = b' * (b * e) := by rw [h4, one_mul]
  have he1 : e = 1 := by
    by_contra he1
    obtain ⟨b', hb', hne⟩ := f5.exists_not_comm_B h26i he he1
    apply hne
    calc e * b' = b⁻¹ * (b * e * b') := by group
      _ = b⁻¹ * (b' * (b * e)) := by rw [hbeB b' hb']
      _ = (b⁻¹ * b') * b * e := by group
      _ = (b' * b⁻¹) * b * e := by rw [f5.B_comm _ (f5.B.inv_mem hb) _ hb']
      _ = b' * e := by group
  subst he1
  refine ⟨?_, rfl⟩
  rw [mul_one] at hbeC
  have : b ∈ f5.B ⊓ Subgroup.centralizer (P : Set G) := Subgroup.mem_inf.mpr ⟨hb, hbeC⟩
  rwa [hBC, Subgroup.mem_bot] at this

namespace K3Data

variable {R V : Subgroup G} (hK : f5.K3Data R V)
include hK

theorem center_elementary
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) (hp : s.p = 3) :
    IsElementaryAbelian 3 (V ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) :=
  { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext
      (hK.comm _ (hK.center_le a.2) _ (hK.center_le b.2))⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => Subtype.ext (by
      simpa using hK.pow_three h22 h26i hp (hK.center_le a.2)) }

theorem center_fpf
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) (hp : s.p = 3) :
    ∀ b ∈ f5.B, b ≠ 1 → ∀ y ∈ V ⊓ Subgroup.centralizer (V : Set G), b * y = y * b → y = 1 :=
  fun b hb hb1 y hy hby => hK.fpf h22 h26i hp b hb hb1 y (Subgroup.mem_inf.mp hy).1 hby

theorem center_irred
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) (hp : s.p = 3) :
    ∀ Q : Subgroup G, Q ≤ V ⊓ Subgroup.centralizer (V : Set G) →
      f5.JBE ≤ Subgroup.normalizer (Q : Set G) →
      Q = ⊥ ∨ Q = V ⊓ Subgroup.centralizer (V : Set G) := by
  intro Q hQ hQN
  obtain ⟨k, hk⟩ := f5.card_eq_q_pow hp (hK.isPGroup.to_le (hQ.trans inf_le_left))
    (fun b hb => hQN (Subgroup.mem_sup_left (Subgroup.mem_sup_right hb)))
    (fun b hb hb1 y hy => hK.center_fpf h22 h26i hp b hb hb1 y (hQ hy))
  have h1 := Subgroup.card_le_of_le hQ
  rw [hk, hK.card_center h22 h26i hp] at h1
  have hk1 : k ≤ 1 := (Nat.pow_le_pow_iff_right s.one_lt_q).mp (by rwa [pow_one])
  rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
  · left
    exact Subgroup.eq_bot_of_card_eq _ (by rw [hk, pow_zero])
  · right
    exact Subgroup.eq_of_le_of_card_ge hQ (by rw [hk, hK.card_center h22 h26i hp, pow_one])

theorem J_inv_center
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) (hp : s.p = 3) {y : G}
    (hy : y ∈ V ⊓ Subgroup.centralizer (V : Set G)) : s.J * y * s.J⁻¹ = y⁻¹ := by
  rw [hK.center_eq h22 h26i hp] at hy
  exact hy.2

theorem odd_card_centralizer
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) (hp : s.p = 3) :
    ¬ 2 ∣ Nat.card (Subgroup.centralizer
      ((V ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h2
  obtain ⟨y, hy, hy1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hK.center_ne_bot
  have hyJ := hK.J_inv_center h22 h26i hp hy
  have hy3 : y ^ (3 ^ 1) = 1 := by rw [pow_one]; exact hK.pow_three h22 h26i hp (hK.center_le hy)
  set C := Subgroup.centralizer ((V ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G)
    with hCdef
  have hJN : s.J ∈ Subgroup.normalizer (C : Set G) :=
    Sec54.mem_normalizer_centralizer (mem_normalizer_center hK.J_le)
  have hJC : s.J ∉ C := by
    intro hJ
    have h1 : s.J * y * s.J⁻¹ = y := by
      rw [← Subgroup.mem_centralizer_iff.mp hJ y hy, mul_inv_cancel_right]
    have hyy : y * y = 1 := by
      have h3 : y = y⁻¹ := h1.symm.trans hyJ
      calc y * y = y * y⁻¹ := by rw [← h3]
        _ = 1 := mul_inv_cancel y
    have hodd : Odd (orderOf y) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hK.isPGroup
      exact Odd.of_dvd_nat (hk ▸ Odd.pow (by decide))
        (Subgroup.orderOf_dvd_natCard V (Subgroup.mem_inf.mp hy).1)
    have h4 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, hyy])
    rcases (Nat.dvd_prime Nat.prime_two).mp h4 with h | h
    · exact hy1 (orderOf_eq_one_iff.mp h)
    · rw [h] at hodd
      exact absurd hodd (by decide)
  set D := C ⊔ Subgroup.zpowers s.J with hDdef
  have hJD : Subgroup.zpowers s.J ≤ Subgroup.normalizer (C : Set G) := Subgroup.zpowers_le.mpr hJN
  have e1 := Sec52.card_sup_mul_card_inf hJD
  have hinf : C ⊓ Subgroup.zpowers s.J = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzC, hzJ⟩ := Subgroup.mem_inf.mp hz
    rcases eq_one_or_eq_of_mem_zpowers s.orderOf_J hzJ with h | h
    · rw [h]; exact Subgroup.one_mem _
    · exact absurd (h ▸ hzC) hJC
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, s.orderOf_J, sup_comm, ← hDdef] at e1
  have hJ2 : IsPGroup 2 ((Subgroup.zpowers s.J).subgroupOf D) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv, Nat.card_zpowers,
      s.orderOf_J, pow_one]
  obtain ⟨S, hS⟩ := hJ2.exists_le_sylow
  set S' := (S : Subgroup D).map D.subtype with hS'def
  have hS'D : S' ≤ D := Subgroup.map_subtype_le _
  have hS'2 : IsPGroup 2 S' := S.isPGroup'.map _
  have hJS' : s.J ∈ S' :=
    ⟨⟨s.J, Subgroup.mem_sup_right (Subgroup.mem_zpowers _)⟩,
      hS (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers _)), rfl⟩
  have hS'card : Nat.card S' = 2 ^ (Nat.card D).factorization 2 := by
    rw [hS'def, Subgroup.card_map_of_injective D.subtype_injective, Sylow.card_eq_multiplicity]
  have hS'N : S' ≤ Subgroup.normalizer (C : Set G) :=
    hS'D.trans (sup_le Subgroup.le_normalizer hJD)
  have e2 := Sec52.card_sup_mul_card_inf hS'N
  have h3 : Nat.card (S' ⊔ C : Subgroup G) ≤ Nat.card D :=
    Subgroup.card_le_of_le (sup_le hS'D le_sup_left)
  have h4 : 4 ≤ Nat.card S' := by
    rw [hS'card, e1]
    have h5 : 2 ≤ (Nat.card C * 2).factorization 2 := by
      rw [Nat.factorization_mul Nat.card_pos.ne' (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_self Nat.prime_two]
      have := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two Nat.card_pos.ne').mp h2
      omega
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (Nat.card C * 2).factorization 2 := Nat.pow_le_pow_right (by norm_num) h5
  have h5 : 2 ≤ Nat.card (C ⊓ S' : Subgroup G) := by
    have hC0 : 0 < Nat.card C := Nat.card_pos
    have h6 : Nat.card C * Nat.card S' ≤ Nat.card C * (2 * Nat.card (C ⊓ S' : Subgroup G)) := by
      rw [← e2]
      calc Nat.card (S' ⊔ C : Subgroup G) * Nat.card (C ⊓ S' : Subgroup G)
          ≤ Nat.card D * Nat.card (C ⊓ S' : Subgroup G) := Nat.mul_le_mul_right _ h3
        _ = Nat.card C * (2 * Nat.card (C ⊓ S' : Subgroup G)) := by rw [e1]; ring
    have h7 := Nat.le_of_mul_le_mul_left h6 hC0
    omega
  obtain ⟨t, ht, ht1⟩ := (Subgroup.bot_or_exists_ne_one (C ⊓ S')).resolve_left (fun h => by
    rw [h, Subgroup.card_bot] at h5
    omega)
  obtain ⟨htC, htS⟩ := Subgroup.mem_inf.mp ht
  have htt : t * t = 1 := s.fr.mul_self_of_isPGroup (hS'2.to_le (Subgroup.zpowers_le.mpr htS))
  have hot : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact htt) ht1
  have hS'ab := s.toHyp.isMulCommutative_of_isPGroup hS'2
  have hJt : s.J * t = t * s.J :=
    congrArg Subtype.val (hS'ab.is_comm.comm ⟨s.J, hJS'⟩ ⟨t, htS⟩)
  exact s.no_real_three h22 hp hot
    (Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp htC y hy))
    (Subgroup.mem_centralizer_singleton_iff.mpr hJt) hy1 hy3 s.J_mul_J hyJ

theorem mem_P₁
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) (hp : s.p = 3) {c : G}
    (hcH : c ∈ s.H) (hcN : c ∈ Subgroup.normalizer (V : Set G))
    (hcC : c ∈ Subgroup.centralizer
      ((V ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G))
    (hodd : Odd (orderOf c)) : c ∈ f5.P₁ := by
  have hcKE := s.fr.mem_KE_of_odd hcH hodd
  have hcP : c ∈ Subgroup.normalizer (f5.P₁ : Set G) := by
    rw [← hK.inf_H h22 h26i hp]
    exact Sec54.mem_normalizer_inf hcN (Subgroup.le_normalizer hcH)
  have hk : c ∈ Subgroup.normalizer (f5.P₁ : Set G) ⊓ (s.K ⊔ s.fr.E) :=
    Subgroup.mem_inf.mpr ⟨hcP, hcKE⟩
  rw [f5.normalizer_eq] at hk
  have hBN := f5.B_le_normalizer_P₁
  have hEN : s.fr.E ≤ Subgroup.normalizer ((f5.P₁ ⊔ f5.B : Subgroup G) : Set G) :=
    fun e he => Sec52.mem_normalizer_sup (f5.E_le_normalizer_P₁ he) (f5.E_le_normalizer_B he)
  obtain ⟨y, hy, e, he, rfl⟩ := (mem_sup_iff_of_le_normalizer hEN).mp hk
  obtain ⟨u, hu, b, hb, rfl⟩ := (mem_sup_iff_of_le_normalizer hBN).mp hy
  have huC : u ∈ Subgroup.centralizer
      ((V ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun n hn =>
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hn).2 u (hK.P₁_le hu)).symm
  have hbeC : b * e ∈ Subgroup.centralizer
      ((V ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ huC) hcC
    rwa [show u⁻¹ * (u * b * e) = b * e by group] at this
  obtain ⟨rfl, rfl⟩ := f5.eq_one_of_mul_mem_centralizer h26i hK.center_ne_bot
    (fun b hb => mem_normalizer_center (hK.B_le hb)) (hK.center_fpf h22 h26i hp) hb he hbeC
  rw [mul_one, mul_one]
  exact hu

theorem card_le_of_le_centralizer
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) (hp : s.p = 3)
    {Q : Subgroup G} (hQ : IsPGroup 3 Q)
    (hQC : Q ≤ Subgroup.centralizer
      ((V ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G)) :
    Nat.card Q ≤ Nat.card V := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ((V ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G)
    with hCdef
  set M := C ⊓ Subgroup.normalizer (V : Set G) with hMdef
  have hVC : V ≤ C := fun v hv => Subgroup.mem_centralizer_iff.mpr fun n hn =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hn).2 v hv).symm
  have hVM : V ≤ M := le_inf hVC Subgroup.le_normalizer
  have hModd : ¬ 2 ∣ Nat.card M := fun h => hK.odd_card_centralizer h22 h26i hp
    (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hNM : ∀ g ∈ Subgroup.normalizer (V : Set G), g ∈ Subgroup.normalizer (M : Set G) :=
    fun g hg => Sec54.mem_normalizer_inf
      (Sec54.mem_normalizer_centralizer (mem_normalizer_center hg)) (Subgroup.le_normalizer hg)
  set A := Subgroup.zpowers s.J with hAdef
  have hAM : A ≤ Subgroup.normalizer (M : Set G) := Subgroup.zpowers_le.mpr (hNM _ hK.J_le)
  have hA2 : IsPGroup 2 A :=
    IsPGroup.of_card (n := 1) (by rw [hAdef, Nat.card_zpowers, s.orderOf_J, pow_one])
  let := JT.conjAct A M hAM
  obtain ⟨T, hTinv⟩ := DisconnectedInvolutionGraph.Helpers.coprime_pgroup_exists_invariant_sylow
    (A := A) 2 3 hA2 hModd
  set S₂ := (T : Subgroup M).map M.subtype with hS₂def
  have hS₂M : S₂ ≤ M := Subgroup.map_subtype_le _
  have hS₂3 : IsPGroup 3 S₂ := T.isPGroup'.map _
  have hS₂card : Nat.card S₂ = 3 ^ (Nat.card M).factorization 3 := by
    rw [hS₂def, Subgroup.card_map_of_injective M.subtype_injective, Sylow.card_eq_multiplicity]
  have hVS₂ : V ≤ S₂ := by
    have hn : (V.subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hVM).mpr inf_le_right
    have h3 : IsPGroup 3 (V.subgroupOf M) :=
      hK.isPGroup.comap_of_injective M.subtype M.subtype_injective
    have hle := h3.le_sylow_of_normal T
    intro v hv
    exact ⟨⟨v, hVM hv⟩, hle (Subgroup.mem_subgroupOf.mpr hv), rfl⟩
  have hJS₂ : s.J ∈ Subgroup.normalizer (S₂ : Set G) := by
    apply Sec53.mem_normalizer_of_conj_le
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨_, hTinv ⟨s.J, Subgroup.mem_zpowers _⟩ y hy, rfl⟩
  have huniq : ∀ S' : Subgroup G, S' ≤ M → Nat.card S' = Nat.card S₂ →
      s.J ∈ Subgroup.normalizer (S' : Set G) → S' = S₂ := by
    intro S' hS'M hS'card hJS'
    have hcard' : Nat.card (S'.subgroupOf M) = 3 ^ (Nat.card M).factorization 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS'M).toEquiv, hS'card, hS₂card]
    let T' : Sylow 3 M := Sylow.ofCard (S'.subgroupOf M) hcard'
    have hT'inv : ∀ a : A, ∀ x ∈ (T' : Subgroup M), a • x ∈ (T' : Subgroup M) := by
      intro a x hx
      have haN : (a : G) ∈ Subgroup.normalizer (S' : Set G) := Subgroup.zpowers_le.mpr hJS' a.2
      exact (Subgroup.mem_normalizer_iff.mp haN x).mp hx
    obtain ⟨c, hcfix, hc⟩ :=
      SolvableHall.coprime_invariant_sylow_conjugacy hA2 hModd T T' hTinv hT'inv
    have hcH : (c : G) ∈ s.H := by
      have h1 := congrArg Subtype.val
        ((FixedPoints.mem_subgroup A M c).mp hcfix ⟨s.J, Subgroup.mem_zpowers _⟩)
      change s.J * (c : G) * s.J⁻¹ = c at h1
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (c : G) * s.J = s.J * (c : G) * s.J⁻¹ * s.J := by rw [h1]
        _ = s.J * c := by group
    have hcodd : Odd (orderOf (c : G)) := by
      rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
      exact fun h => hModd (h.trans (Subgroup.orderOf_dvd_natCard M c.2))
    have hcP := hK.mem_P₁ h22 h26i hp hcH (Subgroup.mem_inf.mp c.2).2
      (Subgroup.mem_inf.mp c.2).1 hcodd
    have hcT : c⁻¹ ∈ (T : Subgroup M) := by
      have : (c : G) ∈ S₂ := hVS₂ (hK.P₁_le hcP)
      obtain ⟨c', hc'T, hc'⟩ := this
      have : c' = c := Subtype.ext hc'
      rw [← this]
      exact Subgroup.inv_mem _ hc'T
    rw [Sec56.map_conj_eq (Subgroup.le_normalizer hcT)] at hc
    have h1 : S'.subgroupOf M = (T : Subgroup M) := by
      rw [hc]
      exact (Sylow.coe_ofCard _ hcard').symm
    calc S' = (S'.subgroupOf M).map M.subtype := by
          rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hS'M]
      _ = S₂ := by rw [h1]
  have hconjS₂ : ∀ g ∈ Subgroup.normalizer (V : Set G), g * s.J = s.J * g →
      g ∈ Subgroup.normalizer (S₂ : Set G) := by
    intro g hgV hgJ
    set S' := S₂.map (MulAut.conj g).toMonoidHom with hS'def
    have hS'M : S' ≤ M := by
      rintro _ ⟨r, hr, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hNM g hgV) r).mp (hS₂M hr)
    have hS'card : Nat.card S' = Nat.card S₂ :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    have hJS' : s.J ∈ Subgroup.normalizer (S' : Set G) := by
      apply Sec53.mem_normalizer_of_conj_le
      rintro _ ⟨r, hr, rfl⟩
      refine ⟨s.J * r * s.J⁻¹, (Subgroup.mem_normalizer_iff.mp hJS₂ r).mp hr, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have hJg : s.J * g⁻¹ = g⁻¹ * s.J := by
        calc s.J * g⁻¹ = g⁻¹ * (g * s.J) * g⁻¹ := by group
          _ = g⁻¹ * (s.J * g) * g⁻¹ := by rw [hgJ]
          _ = g⁻¹ * s.J := by group
      calc g * (s.J * r * s.J⁻¹) * g⁻¹ = (g * s.J) * r * (s.J⁻¹ * g⁻¹) := by group
        _ = (s.J * g) * r * (g⁻¹ * s.J⁻¹) := by
          rw [hgJ, show s.J⁻¹ * g⁻¹ = (g * s.J)⁻¹ by group, hgJ,
            show (s.J * g)⁻¹ = g⁻¹ * s.J⁻¹ by group]
        _ = s.J * (g * r * g⁻¹) * s.J⁻¹ := by group
    have := huniq S' hS'M hS'card hJS'
    apply Sec56.mem_normalizer_of_map_conj_le
    rw [← hS'def, this]
  have hBS₂ : f5.B ≤ Subgroup.normalizer (S₂ : Set G) := fun b hb =>
    hconjS₂ b (hK.B_le hb) (s.commute_J (s.K_le_H (f5.B_le hb)))
  have hES₂ : s.fr.E ≤ Subgroup.normalizer (S₂ : Set G) := fun e he =>
    hconjS₂ e (hK.E_le he) (s.commute_J (s.fr.E_le_H he))
  have hS₂V : S₂ = V := hK.max S₂ hS₂3 hVS₂ hJS₂ hBS₂ hES₂
  have hMle : ∀ X : Subgroup G, IsPGroup 3 X → X ≤ M → Nat.card X ≤ Nat.card V := by
    intro X hX hXM
    have hX' : IsPGroup 3 (X.subgroupOf M) := hX.comap_of_injective M.subtype M.subtype_injective
    obtain ⟨T₃, hT₃⟩ := hX'.exists_le_sylow
    calc Nat.card X = Nat.card (X.subgroupOf M) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv).symm
      _ ≤ Nat.card T₃ := Subgroup.card_le_of_le hT₃
      _ = Nat.card V := by rw [Sylow.card_eq_multiplicity, ← hS₂card, hS₂V]
  have hV' : IsPGroup 3 (V.subgroupOf C) :=
    hK.isPGroup.comap_of_injective C.subtype C.subtype_injective
  obtain ⟨S₁, hS₁⟩ := hV'.exists_le_sylow
  set S₁' := (S₁ : Subgroup C).map C.subtype with hS₁'def
  have hVS₁ : V ≤ S₁' := fun v hv => ⟨⟨v, hVC hv⟩, hS₁ (Subgroup.mem_subgroupOf.mpr hv), rfl⟩
  have hS₁'3 : IsPGroup 3 S₁' := S₁.isPGroup'.map _
  have hS₁'C : S₁' ≤ C := Subgroup.map_subtype_le _
  have hQS : Nat.card Q ≤ Nat.card S₁' := by
    have hQ' : IsPGroup 3 (Q.subgroupOf C) := hQ.comap_of_injective C.subtype C.subtype_injective
    obtain ⟨S₃, hS₃⟩ := hQ'.exists_le_sylow
    calc Nat.card Q = Nat.card (Q.subgroupOf C) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQC).toEquiv).symm
      _ ≤ Nat.card S₃ := Subgroup.card_le_of_le hS₃
      _ = Nat.card S₁' := by
          rw [Sylow.card_eq_multiplicity, hS₁'def,
            Subgroup.card_map_of_injective C.subtype_injective, Sylow.card_eq_multiplicity]
  have hS₁V : S₁' = V := by
    by_contra hne
    obtain ⟨w, hwS, hwV, hwN⟩ :=
      Sec56.exists_mem_normalizer_of_lt hS₁'3 (lt_of_le_of_ne hVS₁ (Ne.symm hne))
    have hX : V ⊔ Subgroup.zpowers w ≤ M := sup_le hVM (Subgroup.zpowers_le.mpr
      (Subgroup.mem_inf.mpr ⟨hS₁'C hwS, hwN⟩))
    have hX3 : IsPGroup 3 (V ⊔ Subgroup.zpowers w : Subgroup G) :=
      hS₁'3.to_le (sup_le hVS₁ (Subgroup.zpowers_le.mpr hwS))
    have hlt : V < V ⊔ Subgroup.zpowers w := lt_of_le_of_ne le_sup_left fun h =>
      hwV (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers w))
    have h1 := Subgroup.card_lt_of_lt hlt
    have h2 := hMle _ hX3 hX
    omega
  rw [← hS₁V]
  exact hQS

theorem normalizer_le
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) (hp : s.p = 3) :
    Subgroup.normalizer (R : Set G) ≤
      Subgroup.normalizer ((V ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hR1 : R ≠ ⊥ := fun h => f5.P₁_ne_bot (le_antisymm (h ▸ hK.rdata.P₁_le) bot_le)
  have hq : ∀ v ∈ V, ∀ m ∈ R, v * (m⁻¹ * (v * m * v⁻¹)) * v⁻¹ = m⁻¹ * (v * m * v⁻¹) := by
    intro v hv m hm
    have h1 := hK.commutator_mem h22 h26i hp (R.inv_mem hm) hv
    rw [inv_inv] at h1
    rw [show m⁻¹ * (v * m * v⁻¹) = m⁻¹ * v * m * v⁻¹ by group]
    rw [Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp h1).2 v hv, mul_inv_cancel_right]
  obtain ⟨M, hVM, -, hNM, hD⟩ := Sec56.exists_fixed_of_quadratic s.abelian_sylow
    hK.rdata.isPGroup hR1 hK.comm (hK.le_normalizer h22 h26i hp) hq
  set D := R ⊓ Subgroup.centralizer (M : Set G) with hDdef
  have hDN₁ : D ≤ V ⊓ Subgroup.centralizer (V : Set G) := fun d hd =>
    Subgroup.mem_inf.mpr ⟨hK.le (Subgroup.mem_inf.mp hd).1, Subgroup.mem_centralizer_iff.mpr
      fun v hv => Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hd).2 v (hVM hv)⟩
  have hDnorm : ∀ g ∈ Subgroup.normalizer (R : Set G), g ∈ Subgroup.normalizer (D : Set G) :=
    fun g hg => Sec54.mem_normalizer_inf hg (Sec54.mem_normalizer_centralizer (hNM g hg))
  obtain ⟨k, hk⟩ := f5.card_eq_q_pow hp (hK.rdata.isPGroup.to_le inf_le_left)
    (fun b hb => hDnorm b (hK.rdata.B_le hb))
    (fun b hb hb1 y hy => hK.fpf h22 h26i hp b hb hb1 y (hK.le (Subgroup.mem_inf.mp hy).1))
  have hk0 : k ≠ 0 := fun h => hD (Subgroup.eq_bot_of_card_eq _ (by rw [hk, h, pow_zero]))
  have hDeq : D = V ⊓ Subgroup.centralizer (V : Set G) :=
    Subgroup.eq_of_le_of_card_ge hDN₁ (by
      rw [hK.card_center h22 h26i hp, hk]
      exact Nat.le_self_pow hk0 _)
  intro g hg
  rw [← hDeq]
  exact hDnorm g hg

theorem false_of_exp
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) (hp : s.p = 3)
    (h3 : 3 ∣ Nat.card s.fr.E) (hexp : ∃ y ∈ V, y ^ 3 ≠ 1) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h54 := lemma_5_4_of h22 h26i
  have hN₁el := hK.center_elementary h22 h26i hp
  have hJBE : f5.JBE ≤ Subgroup.normalizer
      ((V ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
    fun g hg => mem_normalizer_center (hK.JBE_le hg)
  have hirr := hK.center_irred h22 h26i hp
  have hN := h54 G s hp f5 _ hN₁el hK.center_ne_bot hJBE hirr
  have hNR := hK.normalizer_le h22 h26i hp
  have hVR := hK.le_normalizer h22 h26i hp
  obtain ⟨S₀⟩ : Nonempty (Sylow 3 s.fr.E) := inferInstance
  set P₀ := (S₀ : Subgroup s.fr.E).map s.fr.E.subtype with hP₀def
  have hP₀E : P₀ ≤ s.fr.E := Subgroup.map_subtype_le _
  set a := (Nat.card s.fr.E).factorization 3 with ha
  have hP₀card : Nat.card P₀ = 3 ^ a := by
    rw [hP₀def, Subgroup.card_map_of_injective s.fr.E.subtype_injective,
      Sylow.card_eq_multiplicity]
  have hapos : 0 < a := Nat.Prime.factorization_pos_of_dvd Nat.prime_three Nat.card_pos.ne' h3
  have hP₀N : P₀ ≤ Subgroup.normalizer (V : Set G) := hP₀E.trans hK.E_le
  have hinf : V ⊓ P₀ = ⊥ := by
    have := f5.inf_E_eq_bot h26i hp hK.isPGroup hK.B_le
    rw [eq_bot_iff, ← this]
    exact inf_le_inf_left _ hP₀E
  set S := V ⊔ P₀ with hSdef
  have hScard : Nat.card S = Nat.card V * 3 ^ a := by
    rw [hSdef, Sec54.card_sup_eq_mul hP₀N hinf, hP₀card]
  have hS3 : IsPGroup 3 S := IsPGroup.of_card (n := 3 * s.f + a) (by
    rw [hScard, hK.card_V, Hyp.q, hp, ← pow_mul, ← pow_add, mul_comm s.f 3])
  have hSN : S ≤ Subgroup.normalizer (R : Set G) := sup_le hVR (hP₀E.trans hK.rdata.E_le)
  have hQmax : ∀ Q' : Subgroup G, IsPGroup 3 Q' → S ≤ Q' →
      Q' ≤ Subgroup.normalizer (R : Set G) → Q' ≤ S := by
    intro Q' hQ' hSQ' hQ'N
    have h1 := f5.card_le_of_le_normalizer hp hN hQ' (hQ'N.trans hNR)
    have h2 := hK.card_le_of_le_centralizer h22 h26i hp (hQ'.to_le inf_le_left) inf_le_right
    have hle : Nat.card Q' ≤ Nat.card S := by
      rw [hScard]
      calc Nat.card Q' ≤ 3 ^ (Nat.card s.fr.E).factorization 3 *
            Nat.card (Q' ⊓ Subgroup.centralizer
              ((V ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) : Subgroup G) := h1
        _ ≤ 3 ^ a * Nat.card V := Nat.mul_le_mul_left _ h2
        _ = Nat.card V * 3 ^ a := mul_comm _ _
    exact (Subgroup.eq_of_le_of_card_ge hSQ' hle).ge
  have hconj : ∀ g : G, R.map (MulAut.conj g).toMonoidHom ≤ S →
      R.map (MulAut.conj g).toMonoidHom = R := by
    intro g hg
    refine hK.eq_of_elementary h22 h26i hp hexp hP₀E hg ?_ ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [show g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ by group, hK.comm x hx y hy]
      group
    · rintro _ ⟨x, hx, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [conj_pow, hK.pow_three h22 h26i hp hx]
      group
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hK.card_R]
  have hweak : ∀ g : G, (∀ w ∈ R, g * w * g⁻¹ ∈ S) → ∀ w ∈ R, g * w * g⁻¹ ∈ R := by
    intro g hg w hw
    have h1 := hconj g (by rintro _ ⟨v, hv, rfl⟩; exact hg v hv)
    have : g * w * g⁻¹ ∈ R.map (MulAut.conj g).toMonoidHom := ⟨w, hw, rfl⟩
    rwa [h1] at this
  let P : Sylow 3 G := ⟨S, hS3, fun hS' hle =>
    Sec56.eq_of_le_of_weaklyClosed (hK.le.trans le_sup_left) hSN hQmax hweak hS' hle⟩
  have hWC : BenderSuzuki.External.WeaklyClosedIn (P : Subgroup G) R :=
    ⟨hK.le.trans le_sup_left, fun g hg => hconj g⁻¹ hg⟩
  have hres := Sec56.hallPResidual_normalizer_eq s.perfect P hWC hK.comm
  have h3P₀ : 3 ∣ Nat.card P₀ := by
    rw [hP₀card]
    exact dvd_pow_self 3 hapos.ne'
  obtain ⟨⟨x, hxP₀⟩, hox⟩ := exists_prime_orderOf_dvd_card' (G := P₀) 3 h3P₀
  rw [Subgroup.orderOf_mk] at hox
  have hxE : x ∈ s.fr.E := hP₀E hxP₀
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hox
    norm_num at hox
  apply Frame5.not_mem_hallPResidual h54 hp f5 hN₁el hK.center_ne_bot hJBE hirr
    (hK.center_fpf h22 h26i hp) hxE hox (f5.exists_not_comm_B h26i hxE hx1)
  have hxR : x ∈ (BenderSuzuki.External.hallPResidual 3
      (Subgroup.normalizer (R : Set G))).map (Subgroup.normalizer (R : Set G)).subtype := by
    rw [hres]
    exact hK.rdata.E_le hxE
  exact Sec56.map_hallPResidual_le hNR hxR

end K3Data

end Frame5

end CFSG.Walter.W67
