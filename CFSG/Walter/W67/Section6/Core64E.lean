module

public import CFSG.Walter.W67.Section6.Core64D
public import CFSG.Walter.W67.Section5.P56K3c

public section

namespace CFSG.Walter.W67

namespace Sec6

variable {G : Type} [Group G] [Finite G] {s : Std G}

namespace Sol

variable (σ : Sol s)
include σ

theorem card_P₁ (f5 : Frame5 s) : Nat.card f5.P₁ = 3 ^ 7 := by
  rw [f5.card_P₁, σ.q_eq]

theorem card_three_le
    {g : G} (hgen : Subgroup.zpowers g = s.fr.E) {Q : Subgroup G}
    (hQ : IsPGroup 3 Q) (hQC : Q ≤ Subgroup.centralizer ({g} : Set G)) : Nat.card Q ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQN : Q ≤ Subgroup.normalizer (s.fr.E : Set G) := by
    rw [normalizer_eq_centralizer, ← hgen, Sec52.centralizer_zpowers_eq]
    exact hQC
  have hdvd := Subgroup.card_dvd_of_le hQN
  rw [σ.card_normalizer_E] at hdvd
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  rw [hk] at hdvd ⊢
  have hk1 : k ≤ 1 := by
    by_contra hk1
    have : 3 ^ 2 ∣ 3 ^ k := pow_dvd_pow 3 (by omega)
    have := this.trans hdvd
    norm_num at this
  calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
    _ = 3 := pow_one 3

theorem card_le_of_le_centralizer
    (f5 : Frame5 s) {Q : Subgroup G} (hQ : IsPGroup 3 Q)
    (hQC : Q ≤ Subgroup.centralizer (f5.P₁ : Set G)) : Nat.card Q ≤ 3 ^ 7 := by
  obtain ⟨R, hR3, -, -, hRN, hmax⟩ := f5.exists_R lemma_2_6_i σ.p3
  have hBR : f5.B ≤ Subgroup.normalizer (R : Set G) := fun b hb =>
    hRN (Subgroup.mem_inf.mpr ⟨s.K_le_H (f5.B_le hb), f5.B_le_normalizer_P₁ hb⟩)
  have hER : s.fr.E ≤ Subgroup.normalizer (R : Set G) := fun e he =>
    hRN (Subgroup.mem_inf.mpr ⟨s.fr.E_le_H he, f5.E_le_normalizer_P₁ he⟩)
  obtain ⟨g, hg, hgen, hg7⟩ := σ.exists_gen
  have h7 := σ.card_inf_centralizer_pow_seven f5 hR3 hBR hER hg hg7
  have h3 := σ.card_three_le hgen (hR3.to_le inf_le_left) inf_le_right
  calc Nat.card Q ≤ Nat.card R := hmax Q hQ hQC
    _ = Nat.card (R ⊓ Subgroup.centralizer ({g} : Set G) : Subgroup G) ^ 7 := h7.symm
    _ ≤ 3 ^ 7 := Nat.pow_le_pow_left h3 7

theorem card_P₁_eq
    (f5 : Frame5 s) : Nat.card f5.P₁ = 3 ^ (Nat.card G).factorization 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h54 := lemma_5_4_of lemma_2_2 lemma_2_6_i
  have hN := h54 G s σ.p3 f5 f5.P₁ (f5.isElementaryAbelian_P₁ σ.p3) f5.P₁_ne_bot
    f5.JBE_le_normalizer_P₁ f5.irred_JBE
  refine card_eq_of_normalizer (f5.isPGroup_P₁ σ.p3) fun Q hQ hP₁Q hQN => ?_
  have h1 := f5.card_le_of_le_normalizer σ.p3 hN hQ hQN
  have h2 := σ.card_le_of_le_centralizer f5 (hQ.to_le inf_le_left) inf_le_right
  rw [σ.E7, Nat.factorization_eq_zero_of_not_dvd (by norm_num), pow_zero, one_mul] at h1
  have hle : Nat.card Q ≤ Nat.card f5.P₁ := by
    rw [σ.card_P₁ f5]
    exact h1.trans h2
  exact (Subgroup.eq_of_le_of_card_ge hP₁Q hle).symm.le

theorem exists_fixed (f5 : Frame5 s) {g : G} (hg : g ∈ s.fr.E) (hg7 : orderOf g = 7) :
    ∃ x ∈ f5.P₁, x ≠ 1 ∧ x * g = g * x := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hmod := Sec64.card_modEq_card_inf_centralizer (ℓ := 7) (f5.E_le_normalizer_P₁ hg)
    (k := 1) (by rw [pow_one, ← hg7, pow_orderOf_eq_one])
  rw [σ.card_P₁ f5] at hmod
  by_contra hne
  push Not at hne
  have hbot : f5.P₁ ⊓ Subgroup.centralizer ({g} : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxP, hxC⟩ := Subgroup.mem_inf.mp hx
    by_contra hx1
    exact hne x hxP hx1 (Subgroup.mem_centralizer_singleton_iff.mp hxC)
  rw [hbot, Subgroup.card_bot] at hmod
  unfold Nat.ModEq at hmod
  norm_num at hmod

theorem exists_conj_of_mem (f5 : Frame5 s) {x : G} (hx : x ∈ f5.P₁) (hx1 : x ≠ 1) {y : G}
    (hy : y ∈ f5.P₁) (hy1 : y ≠ 1) :
    ∃ b ∈ f5.B, y = b * x * b⁻¹ ∨ y = b * x⁻¹ * b⁻¹ := by
  classical
  have hBodd : Odd (Nat.card f5.B) := by rw [σ.card_B f5]; decide
  have hfpf := f5.fpf_P₁
  have hx3 : x ^ 3 = 1 := by simpa [σ.p3] using f5.P₁_pow x hx
  have hxinv : x⁻¹ ≠ x := by
    intro h
    have h2 : x ^ 2 = 1 := by
      rw [pow_two]
      nth_rw 1 [← h]
      exact inv_mul_cancel x
    have := pow_gcd_eq_one.mpr ⟨hx3, h2⟩
    norm_num at this
    exact hx1 this
  have hmem : ∀ b ∈ f5.B, ∀ z ∈ f5.P₁, b * z * b⁻¹ ∈ f5.P₁ := fun b hb z hz =>
    (Subgroup.mem_normalizer_iff.mp (f5.B_le_normalizer_P₁ hb) z).mp hz
  let F : Option (f5.B ⊕ f5.B) → f5.P₁ := fun o =>
    match o with
    | none => 1
    | some (Sum.inl b) => ⟨b * x * (b : G)⁻¹, hmem b b.2 x hx⟩
    | some (Sum.inr b) => ⟨b * x⁻¹ * (b : G)⁻¹, hmem b b.2 _ (f5.P₁.inv_mem hx)⟩
  have hcomm : ∀ c ∈ f5.B, ∀ z ∈ f5.P₁, z ≠ 1 → c * z * c⁻¹ = z → c = 1 := by
    intro c hc z hz hz1 hcz
    by_contra hc1
    apply hz1
    exact hfpf c hc hc1 z hz (by
      calc c * z = c * z * c⁻¹ * c := by group
        _ = z * c := by rw [hcz])
  have hinv : ∀ c ∈ f5.B, c * x * c⁻¹ ≠ x⁻¹ := by
    intro c hc hcx
    have hc2 : c * c * x * (c * c)⁻¹ = x := by
      calc c * c * x * (c * c)⁻¹ = c * (c * x * c⁻¹) * c⁻¹ := by group
        _ = c * x⁻¹ * c⁻¹ := by rw [hcx]
        _ = (c * x * c⁻¹)⁻¹ := by group
        _ = x := by rw [hcx, inv_inv]
    have h1 := hcomm (c * c) (f5.B.mul_mem hc hc) x hx hx1 hc2
    have hc1 : c = 1 := by
      have h2 : c ^ 2 = 1 := by rw [pow_two, h1]
      have h3 : c ^ Nat.card f5.B = 1 := by
        rw [← orderOf_dvd_iff_pow_eq_one]
        exact Subgroup.orderOf_dvd_natCard _ hc
      have h4 := pow_gcd_eq_one.mpr ⟨h3, h2⟩
      rwa [Nat.Coprime.gcd_eq_one (Nat.coprime_two_right.mpr hBodd), pow_one] at h4
    rw [hc1] at hcx
    simp only [one_mul, inv_one, mul_one] at hcx
    exact hxinv hcx.symm
  have hF : Function.Injective F := by
    have key : ∀ b b' : G, b ∈ f5.B → b' ∈ f5.B → ∀ z ∈ f5.P₁, z ≠ 1 →
        b * z * b⁻¹ = b' * z * b'⁻¹ → b = b' := by
      intro b b' hb hb' z hz hz1 h
      have h1 : (b'⁻¹ * b) * z * (b'⁻¹ * b)⁻¹ = z := by
        calc (b'⁻¹ * b) * z * (b'⁻¹ * b)⁻¹ = b'⁻¹ * (b * z * b⁻¹) * b' := by group
          _ = b'⁻¹ * (b' * z * b'⁻¹) * b' := by rw [h]
          _ = z := by group
      have h2 := hcomm _ (f5.B.mul_mem (f5.B.inv_mem hb') hb) z hz hz1 h1
      calc b = b' * (b'⁻¹ * b) := by group
        _ = b' := by rw [h2, mul_one]
    have cross : ∀ b b' : G, b ∈ f5.B → b' ∈ f5.B → b * x * b⁻¹ ≠ b' * x⁻¹ * b'⁻¹ := by
      intro b b' hb hb' h
      apply hinv (b'⁻¹ * b) (f5.B.mul_mem (f5.B.inv_mem hb') hb)
      calc (b'⁻¹ * b) * x * (b'⁻¹ * b)⁻¹ = b'⁻¹ * (b * x * b⁻¹) * b' := by group
        _ = b'⁻¹ * (b' * x⁻¹ * b'⁻¹) * b' := by rw [h]
        _ = x⁻¹ := by group
    have hne1 : ∀ b : G, ∀ z : G, z ≠ 1 → b * z * b⁻¹ ≠ 1 := by
      intro b z hz h
      apply hz
      calc z = b⁻¹ * (b * z * b⁻¹) * b := by group
        _ = 1 := by rw [h]; group
    intro o o' h
    rcases o with _ | ⟨b | b⟩ <;> rcases o' with _ | ⟨b' | b'⟩
    · rfl
    · exact absurd (congrArg Subtype.val h).symm (hne1 b' x hx1)
    · exact absurd (congrArg Subtype.val h).symm (hne1 b' x⁻¹ (inv_ne_one.mpr hx1))
    · exact absurd (congrArg Subtype.val h) (hne1 b x hx1)
    · exact congrArg (some ∘ Sum.inl) (Subtype.ext (key b b' b.2 b'.2 x hx hx1
        (congrArg Subtype.val h)))
    · exact absurd (congrArg Subtype.val h) (cross b b' b.2 b'.2)
    · exact absurd (congrArg Subtype.val h) (hne1 b x⁻¹ (inv_ne_one.mpr hx1))
    · exact absurd (congrArg Subtype.val h).symm (cross b' b b'.2 b.2)
    · exact congrArg (some ∘ Sum.inr) (Subtype.ext (key b b' b.2 b'.2 x⁻¹
        (f5.P₁.inv_mem hx) (inv_ne_one.mpr hx1) (congrArg Subtype.val h)))
  have hcard : Nat.card f5.P₁ ≤ Nat.card (Option (f5.B ⊕ f5.B)) := by
    rw [Finite.card_option, Nat.card_sum, σ.card_B f5, σ.card_P₁ f5]
    norm_num
  obtain ⟨o, ho⟩ := (hF.bijective_of_nat_card_le hcard).2 ⟨y, hy⟩
  rcases o with _ | ⟨b | b⟩
  · exact absurd (congrArg Subtype.val ho).symm hy1
  · exact ⟨b, b.2, Or.inl (congrArg Subtype.val ho).symm⟩
  · exact ⟨b, b.2, Or.inr (congrArg Subtype.val ho).symm⟩

theorem factorization_centralizer
    {x : G} (hxL : x ∈ s.L s.fr.E) (hx3 : orderOf x = 3) :
    (Nat.card (Subgroup.centralizer ({x} : Set G))).factorization 7 = 1 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set C := Subgroup.centralizer ({x} : Set G) with hCdef
  have hEC : s.fr.E ≤ C := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (L_le_centralizer s le_rfl s.E_ne_bot hxL) e he)
  have hE7 : IsPGroup 7 s.fr.E := IsPGroup.of_card (n := 1) (by rw [σ.E7, pow_one])
  have hE7' : IsPGroup 7 (s.fr.E.subgroupOf C) :=
    hE7.comap_of_injective C.subtype C.subtype_injective
  obtain ⟨T, hT⟩ := hE7'.exists_le_sylow
  set T' := (T : Subgroup C).map C.subtype with hT'
  have hT'r : IsPGroup 7 T' := T.isPGroup'.map _
  have hET' : s.fr.E ≤ T' := fun e he => ⟨⟨e, hEC he⟩, hT (Subgroup.mem_subgroupOf.mpr he), rfl⟩
  have hT'C : T' ≤ C := Subgroup.map_subtype_le _
  have hT'eq : T' = s.fr.E := by
    by_contra hne
    have hlt : s.fr.E < T' := lt_of_le_of_ne hET' (Ne.symm hne)
    obtain ⟨w, hwT, hwE, hwN⟩ := Sec56.exists_mem_normalizer_of_lt hT'r hlt
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hT'r) ⟨w, hwT⟩
    rw [Subgroup.orderOf_mk] at hk
    obtain ⟨l, hl, e, he, rfl, hle⟩ := decomp hwN
    have hl7k := (σ.pow_eq_one_of_decomp hl he hle
      (by rw [← hk, pow_orderOf_eq_one] : (l * e) ^ 7 ^ k = 1)).1
    have hl7 : l ^ 7 = 1 := by
      have h168' := Subgroup.orderOf_dvd_natCard _ hl
      rw [σ.L168.card_L] at h168'
      have h1 : orderOf l ∣ 7 ^ k := orderOf_dvd_of_pow_eq_one hl7k
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (by norm_num)).mp h1
      rw [hj] at h168'
      have hj1 : j ≤ 1 := by
        by_contra hj1
        have : 7 ^ 2 ∣ 7 ^ j := pow_dvd_pow 7 (by omega)
        have := this.trans h168'
        norm_num at this
      rw [← orderOf_dvd_iff_pow_eq_one, hj]
      exact (pow_dvd_pow 7 hj1).trans (by norm_num)
    have hwx : (l * e) * x = x * (l * e) :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hT'C hwT))
    have hex : e * x = x * e :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hEC he))
    have hlx : l * x = x * l := by
      have h1 : l * e * x = l * x * e := by rw [mul_assoc, hex, ← mul_assoc]
      have h2 : x * (l * e) = x * l * e := by rw [mul_assoc]
      have := hwx
      rw [h1, h2] at this
      exact mul_right_cancel this
    by_cases hl1 : l = 1
    · subst hl1
      rw [one_mul] at hwE
      exact hwE he
    · have hlo : orderOf l = 7 := orderOf_eq_prime hl7 hl1
      exact σ.L168.not_comm hl hlo hxL hx3 hlx
  have hcard : Nat.card T' = 7 ^ (Nat.card C).factorization 7 := by
    rw [hT', Subgroup.card_map_of_injective C.subtype_injective, Sylow.card_eq_multiplicity]
  rw [hT'eq, σ.E7] at hcard
  have h := congrArg (fun n => n.factorization 7) hcard
  simp only [Nat.Prime.factorization_self (by norm_num : Nat.Prime 7),
    Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, mul_one] at h
  exact h.symm

theorem exists_cj_P₁
    (f5 : Frame5 s) (P : Sylow 3 G) : ∃ c : G, (P : Subgroup G) = cj c f5.P₁ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P₁' : Sylow 3 G := Sylow.ofCard f5.P₁ (σ.card_P₁_eq f5)
  have hP₁' : (P₁' : Subgroup G) = f5.P₁ := Sylow.coe_ofCard _ _
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G P₁' P
  refine ⟨c, ?_⟩
  rw [← hc, Sylow.coe_subgroup_smul, hP₁', Subgroup.pointwise_smul_def]
  rfl

theorem centralizer_three
    {R : G} (hR : orderOf R = 3) :
    ∃ h : G, cj h s.fr.E ≤ Subgroup.centralizer ({R} : Set G) ∧
      (Nat.card (Subgroup.centralizer ({R} : Set G))).factorization 7 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨f5⟩ := Frame5.nonempty s
  have hR3 : IsPGroup 3 (Subgroup.zpowers R) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hR, pow_one])
  obtain ⟨P, hP⟩ := hR3.exists_le_sylow
  obtain ⟨c, hc⟩ := σ.exists_cj_P₁ f5 P
  have hRP : R ∈ cj c f5.P₁ := hc ▸ hP (Subgroup.mem_zpowers R)
  rw [mem_cj] at hRP
  have hR1 : c⁻¹ * R * c ≠ 1 := by
    intro h
    have : R = 1 := by
      calc R = c * (c⁻¹ * R * c) * c⁻¹ := by group
        _ = 1 := by rw [h]; group
    rw [this, orderOf_one] at hR
    norm_num at hR
  obtain ⟨g, hg, hgen, hg7⟩ := σ.exists_gen
  obtain ⟨x, hx, hx1, hxg⟩ := σ.exists_fixed f5 hg hg7
  have hx3 : orderOf x = 3 := by
    apply orderOf_eq_prime _ hx1
    simpa [σ.p3] using f5.P₁_pow x hx
  have hxN : x ∈ Subgroup.normalizer (s.fr.E : Set G) := by
    rw [normalizer_eq_centralizer, ← hgen, Sec52.centralizer_zpowers_eq]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hxg
  have hxL := σ.mem_L_of_coprime hxN (by rw [hx3]; norm_num)
  have hfac := σ.factorization_centralizer hxL hx3
  have hEx : s.fr.E ≤ Subgroup.centralizer ({x} : Set G) := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (L_le_centralizer s le_rfl s.E_ne_bot hxL) e he)
  obtain ⟨b, -, hb⟩ := σ.exists_conj_of_mem f5 hx hx1 hRP hR1
  have hCx : Subgroup.centralizer ({x⁻¹} : Set G) = Subgroup.centralizer ({x} : Set G) := by
    ext z
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      calc z * x = x * (x⁻¹ * z) * x := by group
        _ = x * (z * x⁻¹) * x := by rw [h]
        _ = x * z := by group
    · intro h
      calc z * x⁻¹ = x⁻¹ * (x * z) * x⁻¹ := by group
        _ = x⁻¹ * (z * x) * x⁻¹ := by rw [h]
        _ = x⁻¹ * z := by group
  have hCR : ∃ y : G, (y = x ∨ y = x⁻¹) ∧ R = (c * b) * y * (c * b)⁻¹ := by
    rcases hb with hb | hb
    · refine ⟨x, Or.inl rfl, ?_⟩
      calc R = c * (c⁻¹ * R * c) * c⁻¹ := by group
        _ = c * (b * x * b⁻¹) * c⁻¹ := by rw [hb]
        _ = (c * b) * x * (c * b)⁻¹ := by group
    · refine ⟨x⁻¹, Or.inr rfl, ?_⟩
      calc R = c * (c⁻¹ * R * c) * c⁻¹ := by group
        _ = c * (b * x⁻¹ * b⁻¹) * c⁻¹ := by rw [hb]
        _ = (c * b) * x⁻¹ * (c * b)⁻¹ := by group
  obtain ⟨y, hy, hRy⟩ := hCR
  have hCy : Subgroup.centralizer ({y} : Set G) = Subgroup.centralizer ({x} : Set G) := by
    rcases hy with rfl | rfl
    · rfl
    · exact hCx
  have hCRe : Subgroup.centralizer ({R} : Set G) = cj (c * b) (Subgroup.centralizer ({x} : Set G))
      := by
    rw [hRy, ← cj_centralizer_singleton, hCy]
  refine ⟨c * b, ?_, ?_⟩
  · rw [hCRe]
    exact cj_mono hEx
  · rw [hCRe, card_cj]
    exact hfac

theorem sylow_three :
    ∀ P : Sylow 3 G, IsElementaryAbelian 3 (P : Subgroup G) ∧
    Nat.card (P : Subgroup G) = 3 ^ 7 ∧ ∀ x ∈ (P : Subgroup G), x ≠ 1 →
      (Nat.card (Subgroup.centralizer ({x} : Set G))).factorization 7 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨f5⟩ := Frame5.nonempty s
  intro P
  obtain ⟨c, hc⟩ := σ.exists_cj_P₁ f5 P
  have hpow : ∀ y ∈ (P : Subgroup G), y ^ 3 = 1 := by
    intro y hy
    rw [hc, mem_cj] at hy
    have h1 : (c⁻¹ * y * c) ^ 3 = 1 := by simpa [σ.p3] using f5.P₁_pow _ hy
    have h2 : y = c * (c⁻¹ * y * c) * c⁻¹ := by group
    rw [h2, conj_pow, h1]
    group
  have hcomm : ∀ y ∈ (P : Subgroup G), ∀ z ∈ (P : Subgroup G), y * z = z * y := by
    rw [hc]
    exact comm_cj f5.P₁_comm
  refine ⟨{ toIsMulCommutative := ⟨⟨fun y z => Subtype.ext (hcomm y.1 y.2 z.1 z.2)⟩⟩
            exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun y =>
              Subtype.ext (by simpa using hpow y.1 y.2) }, ?_, ?_⟩
  · rw [Sylow.card_eq_multiplicity, ← σ.card_P₁_eq f5, σ.card_P₁ f5]
  · intro y hy hy1
    have hy3 : orderOf y = 3 := orderOf_eq_prime (hpow y hy) hy1
    obtain ⟨-, -, h⟩ := σ.centralizer_three hy3
    exact h

end Sol

end Sec6

end CFSG.Walter.W67
