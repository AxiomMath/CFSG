module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Background.F6Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace F6

variable {D : Type*} [Group D] [Finite D] {G₁ G₂ : Subgroup D}

omit [Finite D] in
theorem mem_normalizer_conj {S : Subgroup D} {t g : D}
    (h : t⁻¹ * g * t ∈ Subgroup.normalizer (S : Set D)) :
    g ∈ Subgroup.normalizer ((S.map (MulAut.conj t).toMonoidHom : Subgroup D) : Set D) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨(t⁻¹ * g * t) * s * (t⁻¹ * g * t)⁻¹,
      (Subgroup.mem_normalizer_iff.mp h s).mp hs, by group⟩
  · rintro ⟨s, hs, hsx⟩
    refine ⟨(t⁻¹ * g * t)⁻¹ * s * (t⁻¹ * g * t), ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ h) s).mp hs
      simpa using this
    · calc t * ((t⁻¹ * g * t)⁻¹ * s * (t⁻¹ * g * t)) * t⁻¹ = g⁻¹ * (t * s * t⁻¹) * g := by group
        _ = x := by rw [hsx]; group

theorem eq_bot_of_le_pCoreOf_of_normalizes (h : IsGoldschmidtTriple G₁ G₂)
    (hQ : Open.pCore 2 D = ⊥) {D₂ : Subgroup D} (hD₂ : IsSylowIn 3 D₂ G₂) {S : Subgroup D}
    (hS : S ≤ pCoreOf 2 G₂) (hSD : D₂ ≤ Subgroup.normalizer (S : Set D))
    (hSn : pCoreOf 2 G₂ ⊔ twoResidual G₁ ≤ Subgroup.normalizer (S : Set D)) : S = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q₂ := pCoreOf 2 G₂ with hQ₂
  set T := G₁ ⊓ G₂ with hTdef
  have hQT : Q₂ ≤ T := pCoreOf_le_inf_right h
  have hQG : Q₂ ≤ G₂ := pCoreOf_le 2 G₂
  have hQn : G₂ ≤ Subgroup.normalizer (Q₂ : Set D) := le_normalizer_pCoreOf 2 G₂
  have hQS : Q₂ ≤ Subgroup.normalizer (S : Set D) := le_sup_left.trans hSn
  have hLS : twoResidual G₁ ≤ Subgroup.normalizer (S : Set D) := le_sup_right.trans hSn
  obtain ⟨a, ha⟩ := exists_card_inf_eq h
  have hD₂card : Nat.card D₂ = 3 := by
    rw [hD₂.card_eq, card_right h, ha, Nat.factorization_mul (by norm_num) (by positivity),
      Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_three, Nat.factorization_pow,
      Nat.Prime.factorization Nat.prime_two]
    simp
  have hD₂Q : D₂ ≤ Subgroup.normalizer (Q₂ : Set D) := hD₂.le.trans hQn
  have hQD : D₂ ⊓ Q₂ = ⊥ := by
    have h1 : Nat.card ↥(D₂ ⊓ Q₂) ∣ 3 := hD₂card ▸ Subgroup.card_dvd_of_le inf_le_left
    have h2 : IsPGroup 2 ↥(D₂ ⊓ Q₂) := (pCoreOf_isPGroup 2 G₂).to_le inf_le_right
    obtain ⟨k, hk⟩ := h2.exists_card_eq
    rw [hk] at h1
    have hk0 : k = 0 := by
      by_contra hne
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two Nat.prime_three).mp
        ((dvd_pow_self 2 hne).trans h1)
      omega
    rw [hk0, pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq _ hk
  set M := D₂ ⊔ Q₂ with hMdef
  have hMcard : Nat.card M = 3 * Nat.card Q₂ := by
    have h1 := A4.relIndex_sup_eq_of_le_normalizer' (D := Q₂) (T := D₂) hD₂Q
    have h2 := Subgroup.relIndex_mul_card (H := Q₂) (K := D₂ ⊔ Q₂)
    have h3 := Subgroup.relIndex_mul_card (H := Q₂) (K := D₂)
    rw [inf_eq_left.mpr le_sup_right, h1] at h2
    rw [inf_comm, hQD, Subgroup.card_bot, mul_one, hD₂card] at h3
    rw [← h2, h3]
  have hMG : M ≤ G₂ := sup_le hD₂.le hQG
  have hMidx : M.relIndex G₂ = 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := M) (K := G₂)
    rw [inf_eq_left.mpr hMG, hMcard, card_left_eq_six_mul h.symm] at h1
    have hpos : 0 < Nat.card Q₂ := Nat.card_pos
    nlinarith
  have hMn : (M.subgroupOf G₂).Normal := Subgroup.normal_of_index_eq_two hMidx
  have hMS : M ≤ Subgroup.normalizer (S : Set D) := sup_le hSD hQS
  obtain ⟨t, htT, htQ⟩ : ∃ t ∈ T, t ∉ Q₂ := by
    by_contra hne
    push Not at hne
    have := relIndex_pCoreOf_right h
    rw [Subgroup.relIndex_eq_one.mpr hne] at this
    omega
  have htG₁ : t ∈ G₁ := (Subgroup.mem_inf.mp htT).1
  have htG₂ : t ∈ G₂ := (Subgroup.mem_inf.mp htT).2
  have htM : t ∉ M := by
    intro htM
    have hTM : IsPGroup 2 ↥(M ⊓ T) := h.isPGroup_inf.to_le inf_le_right
    obtain ⟨k, hk⟩ := hTM.exists_card_eq
    obtain ⟨b, hb⟩ := (pCoreOf_isPGroup 2 G₂).exists_card_eq
    have h1 : Nat.card ↥(M ⊓ T) ∣ 3 * 2 ^ b := hb ▸ hMcard ▸ Subgroup.card_dvd_of_le inf_le_left
    rw [hk] at h1
    have h2 : 2 ^ k ∣ 2 ^ b :=
      (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)).dvd_of_dvd_mul_left h1
    have h3 : Q₂ ≤ M ⊓ T := le_inf le_sup_right hQT
    have h4 : M ⊓ T = Q₂ := by
      refine (Subgroup.eq_of_le_of_card_ge h3 ?_).symm
      rw [hk, hb]
      exact Nat.le_of_dvd (by positivity) h2
    exact htQ (h4 ▸ ⟨htM, htT⟩)
  have ht2 : t ^ 2 ∈ Q₂ := by
    have hidx : (Q₂.subgroupOf T).index = 2 := relIndex_pCoreOf_right h
    have := Subgroup.sq_mem_of_index_two hidx ⟨t, htT⟩
    simpa [Subgroup.mem_subgroupOf] using this
  set St := S.map (MulAut.conj t).toMonoidHom with hSt
  set R := S ⊔ St with hR
  have hSt2 : St.map (MulAut.conj t).toMonoidHom = S := by
    rw [hSt, Subgroup.map_map]
    have : (MulAut.conj t).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
        (MulAut.conj (t ^ 2)).toMonoidHom := by
      ext x
      simp [pow_two, mul_assoc]
    rw [this]
    exact (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hQS ht2))
  have hnormR : ∀ g : D, (g ∈ Subgroup.normalizer (S : Set D) ∧
      t⁻¹ * g * t ∈ Subgroup.normalizer (S : Set D)) →
      g ∈ Subgroup.normalizer (R : Set D) :=
    fun g hg => mem_normalizer_sup hg.1 (mem_normalizer_conj hg.2)
  have htR : t ∈ Subgroup.normalizer (R : Set D) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, hR, Subgroup.map_sup]
    change St ⊔ St.map (MulAut.conj t).toMonoidHom = S ⊔ St
    rw [hSt2, sup_comm]
  have hM : M ≤ Subgroup.normalizer (R : Set D) := by
    intro g hg
    refine hnormR g ⟨hMS hg, hMS ?_⟩
    have := hMn.conj_mem ⟨g, hMG hg⟩ hg ⟨t⁻¹, G₂.inv_mem htG₂⟩
    simpa [Subgroup.mem_subgroupOf] using this
  have hL : twoResidual G₁ ≤ Subgroup.normalizer (R : Set D) := by
    intro g hg
    refine hnormR g ⟨hLS hg, hLS ?_⟩
    have htN := le_normalizer_twoResidual G₁ (G₁.inv_mem htG₁)
    have := (Subgroup.mem_normalizer_iff.mp htN g).mp hg
    simpa [mul_assoc] using this
  have hG₂ : G₂ ≤ Subgroup.normalizer (R : Set D) := by
    have h1 : M ⊔ Subgroup.zpowers t ≤ Subgroup.normalizer (R : Set D) :=
      sup_le hM (Subgroup.zpowers_le.mpr htR)
    have h2 : M ⊔ Subgroup.zpowers t = G₂ := by
      have hle : M ⊔ Subgroup.zpowers t ≤ G₂ :=
        sup_le hMG (Subgroup.zpowers_le.mpr htG₂)
      have hdvd := Subgroup.relIndex_dvd_of_le_left G₂ (le_sup_left : M ≤ M ⊔ Subgroup.zpowers t)
      rw [hMidx] at hdvd
      have hne : M.relIndex (M ⊔ Subgroup.zpowers t) ≠ 1 := by
        intro h1
        exact htM (Subgroup.relIndex_eq_one.mp h1 (Subgroup.mem_sup_right
          (Subgroup.mem_zpowers t)))
      have hmul := Subgroup.relIndex_mul_relIndex M (M ⊔ Subgroup.zpowers t) G₂ le_sup_left hle
      rw [hMidx] at hmul
      have h3 : (M ⊔ Subgroup.zpowers t).relIndex G₂ = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp ⟨_, hmul.symm⟩ with h4 | h4
        · exact absurd h4 hne
        · rw [h4] at hmul; omega
      exact le_antisymm hle (Subgroup.relIndex_eq_one.mp h3)
    exact h2 ▸ h1
  have hG₁ : G₁ ≤ Subgroup.normalizer (R : Set D) := by
    rw [← inf_sup_twoResidual_left h]
    exact sup_le (inf_le_right.trans hG₂) hL
  have hRn : R.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, ← top_le_iff, ← h.gen]
    exact sup_le hG₁ hG₂
  have hRQ : R ≤ Q₂ := by
    refine sup_le hS ?_
    rintro _ ⟨s, hs, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hQn htG₂) s).mp (hS hs)
  have hR2 : IsPGroup 2 R := (pCoreOf_isPGroup 2 G₂).to_le hRQ
  have hRO : R ≤ Open.pCore 2 D := le_pCore 2 hRn hR2
  rw [hQ] at hRO
  exact le_bot_iff.mp (le_sup_left.trans hRO)

theorem eq_bot_of_characteristic (h : IsGoldschmidtTriple G₁ G₂) (hQ : Open.pCore 2 D = ⊥)
    {S : Subgroup D} (hS : S ≤ pCoreOf 2 G₂)
    (hchar : (S.subgroupOf (pCoreOf 2 G₂)).Characteristic)
    (hSn : pCoreOf 2 G₂ ⊔ twoResidual G₁ ≤ Subgroup.normalizer (S : Set D)) : S = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨D₂, hD₂, -⟩ := exists_isSylowIn_ge 3 (H := G₂) bot_le
    (IsPGroup.of_card (n := 0) (by simp))
  refine eq_bot_of_le_pCoreOf_of_normalizes h hQ hD₂ hS ?_ hSn
  have h1 := normalizer_le_normalizer_map_of_characteristic (S.subgroupOf (pCoreOf 2 G₂))
  rw [Subgroup.map_subgroupOf_eq_of_le hS] at h1
  exact hD₂.le.trans ((le_normalizer_pCoreOf 2 G₂).trans h1)

variable {X : Subgroup D}

omit [Finite D] in
theorem sup_eq_top_of_twoResidual_le [Finite D] (h : IsGoldschmidtTriple G₁ G₂)
    (hL₁ : twoResidual G₁ ≤ X) : X ⊔ G₂ = ⊤ := by
  refine top_le_iff.mp (h.gen ▸ sup_le ?_ le_sup_right)
  rw [← inf_sup_twoResidual_left h]
  exact sup_le (inf_le_right.trans le_sup_right) (hL₁.trans le_sup_left)

theorem normal_sup_pCoreOf (h : IsGoldschmidtTriple G₁ G₂) [hXn : X.Normal]
    (hL₁ : twoResidual G₁ ≤ X) : (X ⊔ pCoreOf 2 G₂).Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, ← top_le_iff, ← sup_eq_top_of_twoResidual_le h hL₁]
  refine sup_le (le_sup_left.trans Subgroup.le_normalizer) fun g hg => ?_
  exact mem_normalizer_sup ((Subgroup.normalizer_eq_top_iff.mpr hXn).ge (Subgroup.mem_top g))
    (le_normalizer_pCoreOf 2 G₂ hg)

theorem isSylowTwoOf_pCoreOf_sup (h : IsGoldschmidtTriple G₁ G₂) [hXn : X.Normal]
    (hL₂ : ¬ twoResidual G₂ ≤ X) : IsSylowTwoOf (pCoreOf 2 G₂) (X ⊔ pCoreOf 2 G₂) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX : IsSubnormal X ⊤ := isSubnormal_top_of_normal
  obtain ⟨-, e₂, hsyl⟩ := ((tfae_inf_le_pCoreOf h.symm hX).out 3 2).mp hL₂
  rw [← e₂] at hsyl
  set Q₂ := pCoreOf 2 G₂
  refine ⟨le_sup_right, pCoreOf_isPGroup 2 G₂, ?_⟩
  change ¬ 2 ∣ Q₂.relIndex (X ⊔ Q₂)
  rw [sup_comm]
  have h1 : X.relIndex (Q₂ ⊔ X) = X.relIndex Q₂ := Subgroup.relIndex_sup_right Q₂ X
  have h2 := Subgroup.relIndex_mul_relIndex (Q₂ ⊓ X) Q₂ (Q₂ ⊔ X) inf_le_left le_sup_left
  have h3 := Subgroup.relIndex_mul_relIndex (Q₂ ⊓ X) X (Q₂ ⊔ X) inf_le_right le_sup_right
  have h4 : (Q₂ ⊓ X).relIndex Q₂ = X.relIndex Q₂ := Subgroup.inf_relIndex_left Q₂ X
  rw [h4] at h2
  rw [h1] at h3
  have hpos : X.relIndex Q₂ ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h5 : Q₂.relIndex (Q₂ ⊔ X) = (Q₂ ⊓ X).relIndex X := by
    have := h2.trans h3.symm
    rw [mul_comm ((Q₂ ⊓ X).relIndex X)] at this
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hpos) this
  rw [h5]
  exact hsyl.2.2

omit [Finite D] in
theorem eq_bot_of_isPGroup_of_odd [Finite D] {P X : Subgroup D} (hPX : P ≤ X)
    (hP : IsPGroup 2 P) (hX : Odd (Nat.card X)) : P = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hdvd : 2 ^ k ∣ Nat.card X := hk ▸ Subgroup.card_dvd_of_le hPX
  have hk0 : k = 0 := by
    by_contra hne
    exact (Nat.not_even_iff_odd.mpr hX) (even_iff_two_dvd.mpr ((dvd_pow_self 2 hne).trans hdvd))
  rw [hk0, pow_zero] at hk
  exact Subgroup.eq_bot_of_card_eq _ hk

theorem commutator_eq_bot_of_odd [hXn : X.Normal] (hL₁ : twoResidual G₁ ≤ X)
    (hX : Odd (Nat.card X)) : ⁅pCoreOf 2 G₁, twoResidual G₁⁆ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : ⁅pCoreOf 2 G₁, twoResidual G₁⁆ ≤ pCoreOf 2 G₁ ⊓ X := by
    rw [Subgroup.commutator_le]
    intro q hq l hl
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have hlN := le_normalizer_pCoreOf 2 G₁ (twoResidual_le G₁ hl)
      have := (Subgroup.mem_normalizer_iff.mp hlN q⁻¹).mp ((pCoreOf 2 G₁).inv_mem hq)
      rw [commutatorElement_def]
      have h2 := (pCoreOf 2 G₁).mul_mem hq this
      simpa [mul_assoc] using h2
    · rw [commutatorElement_def]
      have h1 := hXn.conj_mem l (hL₁ hl) q
      exact X.mul_mem h1 (X.inv_mem (hL₁ hl))
  have h0 : pCoreOf 2 G₁ ⊓ X = ⊥ :=
    eq_bot_of_isPGroup_of_odd inf_le_right ((pCoreOf_isPGroup 2 G₁).to_le inf_le_left) hX
  exact le_bot_iff.mp (h0 ▸ hle)

theorem mem_of_card_eq_three {L : Subgroup D} (hL : Nat.card L = 3) {x : D} (hx : x ∈ L)
    (hx1 : x ≠ 1) {y : D} (hy : y ∈ L) : y = 1 ∨ y = x ∨ y = x⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf x = 3 := by
    have h1 : orderOf x ∣ 3 := hL ▸ Subgroup.orderOf_dvd_natCard L hx
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h2 | h2
    · exact absurd (orderOf_eq_one_iff.mp h2) hx1
    · exact h2
  have hz : Subgroup.zpowers x = L := Subgroup.eq_of_le_of_card_ge
    (Subgroup.zpowers_le.mpr hx) (by rw [Nat.card_zpowers, hord, hL])
  rw [← hz] at hy
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hord] at hy
  simp only [Finset.mem_image, Finset.mem_range] at hy
  obtain ⟨k, hk, rfl⟩ := hy
  have hx3 : x ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one x
  interval_cases k
  · left; simp
  · right; left; simp
  · right; right
    rw [eq_inv_iff_mul_eq_one, ← pow_succ]
    exact hx3

@[expose] def sqClosure (P : Subgroup D) : Subgroup D :=
  Subgroup.closure {y | ∃ p ∈ P, p ^ 2 = y}

omit [Finite D] in
theorem sqClosure_le (P : Subgroup D) : sqClosure P ≤ P :=
  (Subgroup.closure_le _).mpr fun _ ⟨_, hp, hpy⟩ => hpy ▸ P.pow_mem hp 2

omit [Finite D] in
theorem normalizer_le_normalizer_sqClosure (P : Subgroup D) :
    Subgroup.normalizer (P : Set D) ≤ Subgroup.normalizer (sqClosure P : Set D) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, sqClosure, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨g * p * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg p).mp hp,
      by show (g * p * g⁻¹) ^ 2 = g * p ^ 2 * g⁻¹; exact conj_pow⟩
  · rintro ⟨p, hp, rfl⟩
    refine ⟨(g⁻¹ * p * g) ^ 2, ⟨g⁻¹ * p * g, ?_, rfl⟩,
      by show g * (g⁻¹ * p * g) ^ 2 * g⁻¹ = p ^ 2; rw [pow_two, pow_two]; group⟩
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) p).mp hp
    simpa using this

theorem f6_13_three (h : IsGoldschmidtTriple G₁ G₂) (hQ : Open.pCore 2 D = ⊥)
    (hL₁ : Nat.card ↥(twoResidual G₁) = 3) :
    (IsElemAbelian 2 (pCoreOf 2 G₂) ∧ Nat.card ↥(pCoreOf 2 G₂) ≤ 2 ^ 3) ∧
      (twoResidual G₁ ≤ Subgroup.normalizer (pCoreOf 2 G₂ : Set D) → pCoreOf 2 G₂ = ⊥) ∧
      (pCoreOf 2 G₂ ⊔ twoResidual G₁ ≤
          Subgroup.normalizer (pCoreOf 2 (twoResidual G₂) : Set D) →
        pCoreOf 2 (twoResidual G₂) = ⊥) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q₂ := pCoreOf 2 G₂ with hQ₂def
  set L₁ := twoResidual G₁ with hL₁def
  obtain ⟨D₂, hD₂, -⟩ := exists_isSylowIn_ge 3 (H := G₂) bot_le
    (IsPGroup.of_card (n := 0) (by simp))
  have hD₂N : D₂ ≤ Subgroup.normalizer (Q₂ : Set D) := hD₂.le.trans (le_normalizer_pCoreOf 2 G₂)
  have hQT : Q₂ ≤ G₁ ⊓ G₂ := pCoreOf_le_inf_right h
  have hQL : Q₂ ≤ Subgroup.normalizer (L₁ : Set D) :=
    hQT.trans (inf_le_left.trans (le_normalizer_twoResidual G₁))
  obtain ⟨x, hxL, hx1⟩ : ∃ x ∈ L₁, x ≠ 1 := by
    by_contra hne
    push Not at hne
    have : L₁ = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hne
    rw [this, Subgroup.card_bot] at hL₁
    omega
  have hconj : ∀ q ∈ Subgroup.normalizer (L₁ : Set D), q * x * q⁻¹ = x ∨ q * x * q⁻¹ = x⁻¹ := by
    intro q hq
    have hmem := (Subgroup.mem_normalizer_iff.mp hq x).mp hxL
    rcases mem_of_card_eq_three hL₁ hxL hx1 hmem with h1 | h1 | h1
    · exfalso
      apply hx1
      calc x = q⁻¹ * (q * x * q⁻¹) * q := by group
        _ = 1 := by rw [h1]; group
    · exact Or.inl h1
    · exact Or.inr h1
  have hcentL : ∀ g : D, g * x = x * g → g ∈ Subgroup.centralizer (L₁ : Set D) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases mem_of_card_eq_three hL₁ hxL hx1 hy with rfl | rfl | rfl
    · simp
    · exact hg.symm
    · calc x⁻¹ * g = x⁻¹ * (g * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * g) * x⁻¹ := by rw [hg]
        _ = g * x⁻¹ := by group
  have h612 : ∀ S : Subgroup D, S ≤ Q₂ → D₂ ≤ Subgroup.normalizer (S : Set D) →
      Q₂ ≤ Subgroup.normalizer (S : Set D) → L₁ ≤ Subgroup.normalizer (S : Set D) → S = ⊥ :=
    fun S hS hSD hSQ hSL => eq_bot_of_le_pCoreOf_of_normalizes h hQ hD₂ hS hSD (sup_le hSQ hSL)
  have hsq : sqClosure Q₂ = ⊥ := by
    refine h612 _ (sqClosure_le Q₂) (hD₂N.trans (normalizer_le_normalizer_sqClosure Q₂))
      (Subgroup.le_normalizer.trans (normalizer_le_normalizer_sqClosure Q₂)) ?_
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro l hl
    have h1 : l ∈ Subgroup.centralizer {y | ∃ p ∈ Q₂, p ^ 2 = y} := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨q, hq, rfl⟩
      have hq2 : q ^ 2 ∈ Subgroup.centralizer (L₁ : Set D) := by
        refine hcentL _ ?_
        rw [pow_two]
        rcases hconj q (hQL hq) with h2 | h2
        · calc q * q * x = q * (q * x * q⁻¹) * q⁻¹ * (q * q) := by group
            _ = x * (q * q) := by rw [h2, h2]
        · calc q * q * x = q * (q * x * q⁻¹) * q⁻¹ * (q * q) := by group
            _ = q * x⁻¹ * q⁻¹ * (q * q) := by rw [h2]
            _ = (q * x * q⁻¹)⁻¹ * (q * q) := by group
            _ = x * (q * q) := by rw [h2, inv_inv]
      exact ((Subgroup.mem_centralizer_iff.mp hq2) l hl).symm
    rw [sqClosure, Subgroup.centralizer_closure]
    exact h1
  have hQ2 : ∀ q ∈ Q₂, q ^ 2 = 1 := by
    intro q hq
    have : q ^ 2 ∈ sqClosure Q₂ := Subgroup.subset_closure ⟨q, hq, rfl⟩
    rw [hsq, Subgroup.mem_bot] at this
    exact this
  have hQab : ∀ a ∈ Q₂, ∀ b ∈ Q₂, a * b = b * a := by
    intro a ha b hb
    have h1 := hQ2 _ (Q₂.mul_mem ha hb)
    have h2 := hQ2 a ha
    have h3 := hQ2 b hb
    rw [pow_two] at h1 h2 h3
    calc a * b = a * (a * b * (a * b)) * b := by rw [h1, mul_one]
      _ = (a * a) * (b * a) * (b * b) := by group
      _ = b * a := by rw [h2, h3, one_mul, mul_one]
  set A := Q₂ ⊓ Subgroup.centralizer (L₁ : Set D) with hAdef
  have hAQ : A ≤ Q₂ := inf_le_left
  have hAidx : A.relIndex Q₂ ≤ 2 := by
    let φ : ↥Q₂ →* MulAut ↥L₁ := L₁.normalizerMonoidHom.comp (Subgroup.inclusion hQL)
    have hker : φ.ker = A.subgroupOf Q₂ := by
      ext q
      simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hAdef, Subgroup.mem_inf]
      constructor
      · intro hq
        refine ⟨q.2, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
        have := congrArg (fun a : MulAut ↥L₁ => ((a ⟨l, hl⟩ : ↥L₁) : D)) hq
        simp only [φ, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
          Subgroup.coe_inclusion, MulAut.one_apply] at this
        calc l * q = q * l * (q : D)⁻¹ * q := by rw [this]
          _ = q * l := by group
      · rintro ⟨-, hq⟩
        refine MulEquiv.ext fun l => Subtype.ext ?_
        simp only [φ, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
          Subgroup.coe_inclusion, MulAut.one_apply]
        rw [← (Subgroup.mem_centralizer_iff.mp hq) l l.2, mul_inv_cancel_right]
    have hcyc : IsCyclic ↥L₁ := isCyclic_of_prime_card hL₁
    have hcardAut : Nat.card (MulAut ↥L₁) = 2 := by
      rw [IsCyclic.card_mulAut, hL₁, Nat.totient_prime Nat.prime_three]
    change (A.subgroupOf Q₂).index ≤ 2
    rw [← hker, Subgroup.index_ker, ← hcardAut]
    exact Subgroup.card_le_card_group _
  obtain ⟨a3, ha3⟩ := exists_card_inf_eq h
  have hD₂card : Nat.card D₂ = 3 := by
    rw [hD₂.card_eq, card_right h, ha3, Nat.factorization_mul (by norm_num) (by positivity),
      Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_three, Nat.factorization_pow,
      Nat.Prime.factorization Nat.prime_two]
    simp
  obtain ⟨d, hdD, hd1⟩ : ∃ d ∈ D₂, d ≠ 1 := by
    by_contra hne
    push Not at hne
    have : D₂ = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hne
    rw [this, Subgroup.card_bot] at hD₂card
    omega
  have hd3 : d ^ 3 = 1 := by
    rw [← hD₂card]
    have := Subgroup.pow_index_mem (⊥ : Subgroup ↥D₂) ⟨d, hdD⟩
    rw [Subgroup.index_bot, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  let cj : D → Subgroup D → Subgroup D := fun g H => H.map (MulAut.conj g).toMonoidHom
  have hcj_inj : ∀ g : D, Function.Injective (MulAut.conj g).toMonoidHom :=
    fun g => (MulAut.conj g).injective
  have hcj_mul : ∀ (g k : D) (H : Subgroup D), cj g (cj k H) = cj (g * k) H := by
    intro g k H
    simp only [cj, Subgroup.map_map]
    congr 1
    ext x
    simp [mul_assoc]
  have hcj_one : ∀ H : Subgroup D, cj 1 H = H := by
    intro H
    simp only [cj]
    ext x
    simp
  have hcjQ : ∀ g ∈ D₂, cj g Q₂ = Q₂ :=
    fun g hg => Subgroup.mem_normalizer_iff_map_conj_eq.mp (hD₂N hg)
  set B := A ⊓ cj d A ⊓ cj d⁻¹ A with hBdef
  have hBQ : B ≤ Q₂ := inf_le_left.trans (inf_le_left.trans hAQ)
  have hidx_cj : ∀ g ∈ D₂, (cj g A).relIndex Q₂ = A.relIndex Q₂ := by
    intro g hg
    calc (cj g A).relIndex Q₂ = (cj g A).relIndex (cj g Q₂) := by rw [hcjQ g hg]
      _ = A.relIndex Q₂ := Subgroup.relIndex_map_map_of_injective A Q₂ (hcj_inj g)
  have hBidx : B.relIndex Q₂ ≤ 8 := by
    have h1 := Subgroup.relIndex_inf_le (H := A ⊓ cj d A) (K := cj d⁻¹ A) (L := Q₂)
    have h2 := Subgroup.relIndex_inf_le (H := A) (K := cj d A) (L := Q₂)
    rw [hidx_cj d hdD] at h2
    rw [hidx_cj d⁻¹ (D₂.inv_mem hdD)] at h1
    calc B.relIndex Q₂ ≤ (A ⊓ cj d A).relIndex Q₂ * A.relIndex Q₂ := h1
      _ ≤ (A.relIndex Q₂ * A.relIndex Q₂) * A.relIndex Q₂ := Nat.mul_le_mul_right _ h2
      _ ≤ (2 * 2) * 2 := by gcongr
      _ = 8 := by norm_num
  have hd2 : d * d = d⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_two, ← pow_succ]
    exact hd3
  have hBd : cj d B = B := by
    show (A ⊓ cj d A ⊓ cj d⁻¹ A).map (MulAut.conj d).toMonoidHom = A ⊓ cj d A ⊓ cj d⁻¹ A
    rw [Subgroup.map_inf_eq _ _ _ (hcj_inj d), Subgroup.map_inf_eq _ _ _ (hcj_inj d)]
    change cj d A ⊓ cj d (cj d A) ⊓ cj d (cj d⁻¹ A) = A ⊓ cj d A ⊓ cj d⁻¹ A
    rw [hcj_mul, hcj_mul, hd2, mul_inv_cancel, hcj_one, inf_comm, ← inf_assoc]
  have hBD : D₂ ≤ Subgroup.normalizer (B : Set D) := by
    intro g hg
    rcases mem_of_card_eq_three hD₂card hdD hd1 hg with rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hBd
    · exact Subgroup.inv_mem _ (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hBd)
  have hBQn : Q₂ ≤ Subgroup.normalizer (B : Set D) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hQab b (hBQ hb) q hq
  have hBL : L₁ ≤ Subgroup.normalizer (B : Set D) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hbA : b ∈ A := (inf_le_left : A ⊓ cj d A ≤ A)
      ((inf_le_left : A ⊓ cj d A ⊓ cj d⁻¹ A ≤ A ⊓ cj d A) hb)
    exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hbA).2) l hl).symm
  have hB : B = ⊥ := h612 B hBQ hBD hBQn hBL
  have hcardQ : Nat.card Q₂ ≤ 8 := by
    rw [← Subgroup.relIndex_bot_left, ← hB]
    exact hBidx
  refine ⟨⟨⟨⟨⟨fun a b => Subtype.ext (hQab a a.2 b b.2)⟩⟩, hQ2⟩, by norm_num; exact hcardQ⟩,
    fun hN => h612 Q₂ le_rfl hD₂N Subgroup.le_normalizer hN, fun hN => ?_⟩
  have hO : pCoreOf 2 (twoResidual G₂) ≤ Q₂ := by
    refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans (twoResidual_le G₂)) ?_
      (pCoreOf_isPGroup 2 _)
    exact (le_normalizer_twoResidual G₂).trans (normalizer_le_normalizer_pCoreOf 2 _)
  refine h612 _ hO ?_ (le_sup_left.trans hN) (le_sup_right.trans hN)
  exact hD₂.le.trans ((le_normalizer_twoResidual G₂).trans (normalizer_le_normalizer_pCoreOf 2 _))

theorem card_twoResidual_eq_three_of_le (h : IsGoldschmidtTriple G₁ G₂) (hX : IsPGroup 3 X)
    (hL₁ : twoResidual G₁ ≤ X) : Nat.card ↥(twoResidual G₁) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := (hX.to_le hL₁).exists_card_eq
  obtain ⟨a, ha⟩ := exists_card_inf_eq h
  have hdvd : 3 ^ k ∣ 3 * 2 ^ a := by
    rw [← hk, ← ha, ← card_left h]
    exact Subgroup.card_dvd_of_le (twoResidual_le G₁)
  have hk1 : k ≤ 1 := by
    by_contra hne
    have h9 : 3 ^ 2 ∣ 3 * 2 ^ a := (pow_dvd_pow 3 (by omega)).trans hdvd
    have : 3 ∣ 2 ^ a := Nat.dvd_of_mul_dvd_mul_left (k := 3) (by norm_num)
      (by simpa [pow_two] using h9)
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow this)
    omega
  have hk0 : k ≠ 0 := by
    intro hk0
    rw [hk0, pow_zero] at hk
    obtain ⟨x, hx, h3⟩ := exists_orderOf_eq_three_left h
    have hxL : x ∈ twoResidual G₁ := mem_twoResidual_of_odd hx (by rw [h3]; decide)
    have := (Subgroup.eq_bot_of_card_eq _ hk) ▸ hxL
    rw [Subgroup.mem_bot] at this
    rw [this, orderOf_one] at h3
    omega
  have : k = 1 := by omega
  rw [hk, this, pow_one]

theorem f6_14 (h : IsGoldschmidtTriple G₁ G₂)
    (hL : Odd (Nat.card ↥(twoResidual (⊤ : Subgroup D)))) (hQ : Open.pCore 2 D = ⊥) :
    Nonempty (↥(G₁ ⊓ G₂) ≃* Multiplicative (ZMod 2)) ∨
      (Nonempty (↥(pCoreOf 2 G₁) ≃* Multiplicative (ZMod 2)) ∧
        Nonempty (↥(pCoreOf 2 G₂) ≃* Multiplicative (ZMod 2)) ∧
        Nonempty (↥(G₁ ⊓ G₂) ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T := G₁ ⊓ G₂
  set Q₁ := pCoreOf 2 G₁
  set Q₂ := pCoreOf 2 G₂
  have hLn : (twoResidual (⊤ : Subgroup D)).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_twoResidual ⊤))
  have hcomm : ∀ {G : Subgroup D}, ⁅pCoreOf 2 G, twoResidual G⁆ = ⊥ := by
    intro G
    exact commutator_eq_bot_of_odd (X := twoResidual ⊤) (twoResidual_mono le_top) hL
  have hcent : ∀ {G : Subgroup D}, twoResidual G ≤
      Subgroup.centralizer (pCoreOf 2 G : Set D) := by
    intro G l hl
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have := Subgroup.commutator_mem_commutator hq hl
    rw [hcomm, Subgroup.mem_bot, commutatorElement_def] at this
    calc q * l = q * l * q⁻¹ * l⁻¹ * (l * q) := by group
      _ = l * q := by rw [this, one_mul]
  have hQ₁T : Q₁ ≤ T := pCoreOf_le_inf_left h
  have hQ₂T : Q₂ ≤ T := pCoreOf_le_inf_right h
  have hTn : ∀ {G : Subgroup D}, T ≤ G → T ≤ Subgroup.normalizer (pCoreOf 2 G : Set D) :=
    fun hTG => hTG.trans (le_normalizer_pCoreOf 2 _)
  have hI : Q₁ ⊓ Q₂ = ⊥ := by
    have hT : T ≤ Subgroup.normalizer ((Q₁ ⊓ Q₂ : Subgroup D) : Set D) := by
      intro t ht
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have h1 := Subgroup.mem_normalizer_iff.mp (hTn inf_le_left ht) x
      have h2 := Subgroup.mem_normalizer_iff.mp (hTn inf_le_right ht) x
      simp only [Subgroup.mem_inf]
      rw [h1, h2]
    have hLi : ∀ {G : Subgroup D}, Q₁ ⊓ Q₂ ≤ pCoreOf 2 G →
        twoResidual G ≤ Subgroup.normalizer ((Q₁ ⊓ Q₂ : Subgroup D) : Set D) :=
      fun hle => hcent.trans ((Subgroup.centralizer_le hle).trans
        (Subgroup.centralizer_le_normalizer _))
    have hn : (Q₁ ⊓ Q₂).Normal := by
      rw [← Subgroup.normalizer_eq_top_iff, ← top_le_iff, ← h.gen]
      refine sup_le ?_ ?_
      · rw [← inf_sup_twoResidual_left h]
        exact sup_le hT (hLi inf_le_left)
      · rw [← inf_sup_twoResidual_right h]
        exact sup_le hT (hLi inf_le_right)
    have := h.le_pCore_of_normal_le_inf (N := Q₁ ⊓ Q₂) (inf_le_left.trans hQ₁T)
    rw [hQ] at this
    exact le_bot_iff.mp this
  have hQ₁n : Q₁ ≤ Subgroup.normalizer (Q₂ : Set D) := hQ₁T.trans (hTn inf_le_right)
  have hcard : Nat.card ↥(Q₁ ⊔ Q₂) = Nat.card Q₁ * Nat.card Q₂ := by
    have h1 := A4.relIndex_sup_eq_of_le_normalizer' (D := Q₂) (T := Q₁) hQ₁n
    have h2 := Subgroup.relIndex_mul_card (H := Q₂) (K := Q₁ ⊔ Q₂)
    have h3 := Subgroup.relIndex_mul_card (H := Q₂) (K := Q₁)
    rw [inf_eq_left.mpr le_sup_right, h1] at h2
    rw [inf_comm, hI, Subgroup.card_bot, mul_one] at h3
    rw [← h2, h3]
  have hle : Nat.card ↥(Q₁ ⊔ Q₂) ≤ Nat.card T := Subgroup.card_le_of_le (sup_le hQ₁T hQ₂T)
  have hT₁ : Nat.card T = 2 * Nat.card Q₁ := by
    have := Subgroup.relIndex_mul_card (H := Q₁) (K := T)
    rw [relIndex_pCoreOf_left h, inf_eq_left.mpr hQ₁T] at this
    exact this.symm
  have hT₂ : Nat.card T = 2 * Nat.card Q₂ := by
    have := Subgroup.relIndex_mul_card (H := Q₂) (K := T)
    rw [relIndex_pCoreOf_right h, inf_eq_left.mpr hQ₂T] at this
    exact this.symm
  have hQ₁pos : 0 < Nat.card Q₁ := Nat.card_pos
  have hQ₁le : Nat.card Q₁ ≤ 2 := by nlinarith
  rcases (show Nat.card Q₁ = 1 ∨ Nat.card Q₁ = 2 by omega) with h1 | h1
  · left
    exact ⟨mulEquivOfPrimeCardEq (p := 2) (by omega) (by rw [Nat.card_eq_fintype_card]; rfl)⟩
  · right
    have hq₂ : Nat.card Q₂ = 2 := by omega
    have hT4 : Nat.card T = 4 := by omega
    refine ⟨⟨mulEquivOfPrimeCardEq (p := 2) h1 (by rw [Nat.card_eq_fintype_card]; rfl)⟩,
      ⟨mulEquivOfPrimeCardEq (p := 2) hq₂ (by rw [Nat.card_eq_fintype_card]; rfl)⟩, ?_⟩
    have hQ₂n : Q₂ ≤ Subgroup.normalizer (Q₁ : Set D) := hQ₂T.trans (hTn inf_le_left)
    have hcomm' : ∀ (a : ↥Q₁) (b : ↥Q₂),
        Commute (Subgroup.inclusion hQ₁T a) (Subgroup.inclusion hQ₂T b) := by
      intro a b
      apply Subtype.ext
      have hc : (a : D) * b * (a : D)⁻¹ * (b : D)⁻¹ ∈ Q₁ ⊓ Q₂ := by
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · have h1 := (Subgroup.mem_normalizer_iff.mp (hQ₂n b.2) (a : D)⁻¹).mp (Q₁.inv_mem a.2)
          have := Q₁.mul_mem a.2 h1
          simpa [mul_assoc] using this
        · have h1 := (Subgroup.mem_normalizer_iff.mp (hQ₁n a.2) b).mp b.2
          simpa [mul_assoc] using Q₂.mul_mem h1 (Q₂.inv_mem b.2)
      rw [hI, Subgroup.mem_bot] at hc
      simp only [Subgroup.coe_mul, Subgroup.coe_inclusion]
      calc (a : D) * b = (a : D) * b * (a : D)⁻¹ * (b : D)⁻¹ * (b * a) := by group
        _ = b * a := by rw [hc, one_mul]
    let φ := MonoidHom.noncommCoprod (Subgroup.inclusion hQ₁T) (Subgroup.inclusion hQ₂T) hcomm'
    have hφinj : Function.Injective φ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      rintro ⟨a, b⟩ hab
      have hab' : (a : D) * b = 1 := by
        have := congrArg Subtype.val ((MonoidHom.mem_ker).mp hab)
        simpa [φ] using this
      have ha : (a : D) ∈ Q₁ ⊓ Q₂ := by
        refine Subgroup.mem_inf.mpr ⟨a.2, ?_⟩
        rw [eq_inv_of_mul_eq_one_left hab']
        exact Q₂.inv_mem b.2
      rw [hI, Subgroup.mem_bot] at ha
      have hb : (b : D) = 1 := by rw [ha, one_mul] at hab'; exact hab'
      rw [Subgroup.mem_bot]
      exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
    have hφbij : Function.Bijective φ := by
      rw [Nat.bijective_iff_injective_and_card]
      refine ⟨hφinj, ?_⟩
      rw [Nat.card_prod, h1, hq₂, hT4]
    let e := (MulEquiv.ofBijective φ hφbij).symm
    let e₁ := mulEquivOfPrimeCardEq (p := 2) (G := ↥Q₁) (G' := Multiplicative (ZMod 2)) h1
      (by rw [Nat.card_eq_fintype_card]; rfl)
    let e₂ := mulEquivOfPrimeCardEq (p := 2) (G := ↥Q₂) (G' := Multiplicative (ZMod 2)) hq₂
      (by rw [Nat.card_eq_fintype_card]; rfl)
    exact ⟨e.trans (e₁.prodCongr e₂)⟩

end F6

end CFSG.Quasithin
