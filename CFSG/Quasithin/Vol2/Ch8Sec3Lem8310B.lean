module

public import CFSG.Quasithin.H13.NQCatLieOverRank1
public import CFSG.Adapters.LinearSmallCatalog
public import CFSG.Timmesfeld.RankOne.SL2
public import CFSG.Quasithin.EmptyFaithful.S146zRPair

public section

namespace CFSG.Quasithin.H13

namespace Ch8310

open CFSG.Open
open scoped Pointwise

variable {Q : Type*} [Group Q]

@[expose] def proj1 (N₁ N₂ Y : Subgroup Q) (hcomm : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) :
    Subgroup Q where
  carrier := {a | a ∈ N₁ ∧ ∃ b ∈ N₂, a * b ∈ Y}
  one_mem' := ⟨N₁.one_mem, 1, N₂.one_mem, by rw [mul_one]; exact Y.one_mem⟩
  mul_mem' := by
    rintro a a' ⟨ha, b, hb, hab⟩ ⟨ha', b', hb', hab'⟩
    refine ⟨N₁.mul_mem ha ha', b * b', N₂.mul_mem hb hb', ?_⟩
    have e : a * a' * (b * b') = (a * b) * (a' * b') := by
      have h := hcomm a' ha' b hb
      calc a * a' * (b * b') = a * (a' * b) * b' := by group
        _ = a * (b * a') * b' := by rw [h]
        _ = (a * b) * (a' * b') := by group
    rw [e]
    exact Y.mul_mem hab hab'
  inv_mem' := by
    rintro a ⟨ha, b, hb, hab⟩
    refine ⟨N₁.inv_mem ha, b⁻¹, N₂.inv_mem hb, ?_⟩
    have e : a⁻¹ * b⁻¹ = (a * b)⁻¹ := by
      rw [_root_.mul_inv_rev]
      have h := hcomm a⁻¹ (N₁.inv_mem ha) b⁻¹ (N₂.inv_mem hb)
      exact h
    rw [e]
    exact Y.inv_mem hab

theorem mem_proj1 {N₁ N₂ Y : Subgroup Q} {hcomm : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a} {a : Q} :
    a ∈ proj1 N₁ N₂ Y hcomm ↔ a ∈ N₁ ∧ ∃ b ∈ N₂, a * b ∈ Y := Iff.rfl

theorem le_or_forall_of_swap [Finite Q] {N₁ N₂ Y E : Subgroup Q} {σ : Q}
    (hs : IsSimpleGroup ↥N₁) (hR : IsRankOneSylow ↥N₁)
    (hcomm : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a)
    (hσ₂ : ∀ b ∈ N₂, σ⁻¹ * b * σ ∈ N₁) (hσ₃ : ∀ a ∈ N₁, σ⁻¹ * a * σ ∈ N₂)
    (hY : Y ≤ N₁ ⊔ N₂) (hYσ : ∀ y ∈ Y, σ * y * σ⁻¹ ∈ Y) (hYσ' : ∀ y ∈ Y, σ⁻¹ * y * σ ∈ Y)
    (hEN : E ≤ N₁) (hE2 : IsPGroup 2 E) (hEodd : ¬ 2 ∣ (E.subgroupOf N₁).index)
    (hEY : E ≤ Y) :
    N₁ ⊔ N₂ ≤ Y ∨ ∀ y ∈ Y, ∃ a ∈ N₁, ∃ b ∈ N₂, y = a * b ∧
      a ∈ Subgroup.normalizer (E : Set Q) ∧ σ⁻¹ * b * σ ∈ Subgroup.normalizer (E : Set Q) := by
  classical
  set P := proj1 N₁ N₂ Y hcomm with hP
  have hEP : E ≤ P := fun a ha => ⟨hEN ha, 1, N₂.one_mem, by rw [mul_one]; exact hEY ha⟩
  have hE2' : IsPGroup 2 ↥(E.subgroupOf N₁) := hE2.of_equiv (Subgroup.subgroupOfEquivOfLe hEN).symm
  obtain ⟨hNtop, hmax, -⟩ := hR (E.subgroupOf N₁) hE2' hEodd
  have hnorm : N₁ ≤ Subgroup.normalizer (N₂ : Set Q) := fun x hx => by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have : x * y * x⁻¹ = y := by rw [hcomm x hx y hy]; group
      rw [this]; exact hy
    · intro hy
      have e1 := hcomm x hx _ hy
      have e2 : x * y * x⁻¹ = y := by
        have e3 : x * (x * y * x⁻¹) = x * y := by rw [e1]; group
        exact mul_left_cancel e3
      rw [e2] at hy
      exact hy
  have hmul : (↑(N₁ ⊔ N₂) : Set Q) = (N₁ : Set Q) * (N₂ : Set Q) :=
    Subgroup.coe_mul_of_left_le_normalizer_right N₁ N₂ hnorm
  have hdec : ∀ y ∈ N₁ ⊔ N₂, ∃ a ∈ N₁, ∃ b ∈ N₂, y = a * b := fun y hy => by
    have hy' : y ∈ (↑(N₁ ⊔ N₂) : Set Q) := hy
    rw [hmul] at hy'
    obtain ⟨a, ha, b, hb, rfl⟩ := hy'
    exact ⟨a, ha, b, hb, rfl⟩
  by_cases htop : P.subgroupOf N₁ = ⊤
  ·
    left
    have hYN : ((Y ⊓ N₁).subgroupOf N₁).Normal := by
      refine ⟨fun c hc g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hc ⊢
      have hgP : (g : Q) ∈ P := by
        have : g ∈ P.subgroupOf N₁ := by rw [htop]; exact Subgroup.mem_top g
        exact this
      obtain ⟨-, b, hb, hgb⟩ := hgP
      refine ⟨?_, N₁.mul_mem (N₁.mul_mem g.2 hc.2) (N₁.inv_mem g.2)⟩
      have e : (g : Q) * c * (g : Q)⁻¹ = ((g : Q) * b) * c * ((g : Q) * b)⁻¹ := by
        have h1 := hcomm c hc.2 b hb
        calc (g : Q) * c * (g : Q)⁻¹ = (g : Q) * (c * b) * b⁻¹ * (g : Q)⁻¹ := by group
          _ = (g : Q) * (b * c) * b⁻¹ * (g : Q)⁻¹ := by rw [h1]
          _ = ((g : Q) * b) * c * ((g : Q) * b)⁻¹ := by group
      show (g : Q) * c * (g : Q)⁻¹ ∈ Y
      rw [e]
      exact Y.mul_mem (Y.mul_mem hgb hc.1) (Y.inv_mem hgb)
    have hne : (Y ⊓ N₁).subgroupOf N₁ ≠ ⊥ := by
      intro h
      apply hNtop
      have hEbot : E.subgroupOf N₁ = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have : x ∈ (Y ⊓ N₁).subgroupOf N₁ :=
          Subgroup.mem_subgroupOf.mpr ⟨hEY (Subgroup.mem_subgroupOf.mp hx), x.2⟩
        rwa [h] at this
      rw [hEbot]
      exact Subgroup.normalizer_eq_top_iff.mpr (Subgroup.normal_bot)
    rcases hYN.eq_bot_or_eq_top with h | h
    · exact absurd h hne
    · have hN₁Y : N₁ ≤ Y := fun x hx => by
        have : (⟨x, hx⟩ : ↥N₁) ∈ (Y ⊓ N₁).subgroupOf N₁ := by rw [h]; exact Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf.mp this).1
      have hN₂Y : N₂ ≤ Y := fun b hb => by
        have h1 := hYσ _ (hN₁Y (hσ₂ b hb))
        have e : σ * (σ⁻¹ * b * σ) * σ⁻¹ = b := by group
        rwa [e] at h1
      exact sup_le hN₁Y hN₂Y
  ·
    right
    have hPE : P ≤ Subgroup.normalizer (E : Set Q) := by
      intro a ha
      have h1 := hmax (P.subgroupOf N₁)
        (fun x hx => Subgroup.mem_subgroupOf.mpr (hEP (Subgroup.mem_subgroupOf.mp hx))) htop
      have h2 : (⟨a, ha.1⟩ : ↥N₁) ∈ Subgroup.normalizer ((E.subgroupOf N₁) : Set ↥N₁) :=
        h1 (Subgroup.mem_subgroupOf.mpr ha)
      rw [Subgroup.mem_normalizer_iff] at h2 ⊢
      intro x
      by_cases hx : x ∈ N₁
      · have h3 := h2 ⟨x, hx⟩
        simp only [Subgroup.mem_subgroupOf] at h3
        exact h3
      · constructor
        · intro hxE
          exact absurd (hEN hxE) hx
        · intro hxE
          exfalso
          apply hx
          have h4 := hEN hxE
          have e : x = a⁻¹ * (a * x * a⁻¹) * a := by group
          rw [e]
          exact N₁.mul_mem (N₁.mul_mem (N₁.inv_mem ha.1) h4) ha.1
    intro y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec y (hY hy)
    refine ⟨a, ha, b, hb, rfl, hPE ⟨ha, b, hb, hy⟩, hPE ⟨hσ₂ b hb, σ⁻¹ * a * σ, hσ₃ a ha, ?_⟩⟩
    have e : σ⁻¹ * b * σ * (σ⁻¹ * a * σ) = σ⁻¹ * (a * b) * σ := by
      have h1 := hcomm a ha b hb
      calc σ⁻¹ * b * σ * (σ⁻¹ * a * σ) = σ⁻¹ * (b * a) * σ := by group
        _ = σ⁻¹ * (a * b) * σ := by rw [h1]
    rw [e]
    exact hYσ' _ hy

theorem a5_facts {N : Type*} [Group N]
    [Finite N] (e : N ≃* alternatingGroup (Fin 5)) :
    IsRankOneSylow N ∧ ∀ E : Subgroup N, IsPGroup 2 E → ¬ 2 ∣ E.index →
      Nat.card E = 4 ∧ (Subgroup.normalizer (E : Set N)).index = 5 := by
  have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card]
    decide
  obtain ⟨e₅⟩ := CFSG.Walter.Suzuki.nonempty_mulEquiv_psl24 (X := alternatingGroup (Fin 5)) h60
  have hB : CFSG.GH74.Uniqueness.Bender.BenderType N 2 1 1 := .linear 2 le_rfl (e.trans e₅)
  refine ⟨CFSG.Quasithin.H13.NQCat.isRankOneSylow_of_benderType hB, fun E hE hodd => ?_⟩
  obtain ⟨t, hc⟩ := hB.exists_benderCore (hE.toSylow hodd)
  rw [IsPGroup.toSylow_coe] at hc
  refine ⟨?_, ?_⟩
  · rw [hc.card_eq]
    norm_num
  · have h := hc.index_eq
    rw [CFSG.GH74.Uniqueness.Bender.borel] at h
    rw [h]
    norm_num

theorem sl24_of_psl25 {X : Type} [Group X]
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 2 5 1) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have e' : X ≃* CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 K) := e
  obtain ⟨e₅⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five K
    (Or.inr (by rw [hK]; norm_num))
  have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card]
    decide
  obtain ⟨e₄⟩ := CFSG.Walter.Suzuki.nonempty_mulEquiv_psl24 (X := alternatingGroup (Fin 5)) h60
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨GaloisField 2 2, inferInstance, inferInstance,
    by rw [GaloisField.card 2 2 (by norm_num)]; norm_num,
    ⟨((e'.trans e₅).trans e₄).trans (CFSG.Timmesfeld.RankOne.psl2EquivSL2 (GaloisField 2 2))⟩⟩

@[expose] noncomputable def sl2MapEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Matrix.SpecialLinearGroup (Fin 2) R ≃* Matrix.SpecialLinearGroup (Fin 2) S :=
  MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map e.toRingHom)
    (Matrix.SpecialLinearGroup.map e.symm.toRingHom) (by ext x i j; simp) (by ext x i j; simp)

theorem a5_of_sl24 {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4) :
    Nonempty (Matrix.SpecialLinearGroup (Fin 2) F ≃* alternatingGroup (Fin 5)) := by
  have : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card]
    decide
  obtain ⟨e₄⟩ := CFSG.Walter.Suzuki.nonempty_mulEquiv_psl24 (X := alternatingGroup (Fin 5)) h60
  have hc : Fintype.card F = Fintype.card (GaloisField 2 2) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF,
      GaloisField.card 2 2 (by norm_num)]
    norm_num
  exact ⟨((sl2MapEquiv (FiniteField.ringEquivOfCardEq hc)).trans
    (CFSG.Timmesfeld.RankOne.psl2EquivSL2 (GaloisField 2 2)).symm).trans e₄.symm⟩

theorem a5_of_psl25 {X : Type} [Group X]
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 2 5 1) :
    Nonempty (X ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have e' : X ≃* CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 K) := e
  obtain ⟨e₅⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five K
    (Or.inr (by rw [hK]; norm_num))
  exact ⟨e'.trans e₅⟩

theorem le_normalizer_of_comm {A B : Subgroup Q} (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    B ≤ Subgroup.normalizer (A : Set Q) := fun x hx => by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have e : x * y * x⁻¹ = y := by rw [← hcomm y hy x hx]; group
    rw [e]
    exact hy
  · intro hy
    have e1 := hcomm _ hy x hx
    have e3 : x * y = x * (x * y * x⁻¹) := by
      calc x * y = x * y * x⁻¹ * x := by group
        _ = x * (x * y * x⁻¹) := e1
    rw [← mul_left_cancel e3] at hy
    exact hy

theorem mem_normalizer_subgroupOf_iff {N E : Subgroup Q} (hEN : E ≤ N) (x : ↥N) :
    x ∈ Subgroup.normalizer ((E.subgroupOf N : Subgroup ↥N) : Set ↥N) ↔
      (x : Q) ∈ Subgroup.normalizer (E : Set Q) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h q
    by_cases hq : q ∈ N
    · have h3 := h ⟨q, hq⟩
      simp only [Subgroup.mem_subgroupOf] at h3
      exact h3
    · constructor
      · intro hqE
        exact absurd (hEN hqE) hq
      · intro hqE
        exfalso
        apply hq
        have e : q = (x : Q)⁻¹ * ((x : Q) * q * (x : Q)⁻¹) * x := by group
        rw [e]
        exact N.mul_mem (N.mul_mem (N.inv_mem x.2) (hEN hqE)) x.2
  · intro h y
    simp only [Subgroup.mem_subgroupOf]
    exact h y

section Quot

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem image_mono {Gz Y Z : Subgroup G} (h : Y ≤ Z) :
    imageOTwoQuot Gz Y ≤ imageOTwoQuot Gz Z :=
  Subgroup.map_mono fun _ hx => h hx

omit [Finite G] in
theorem mem_of_qPi_mem {Gz T Kz Z : Subgroup G}
    (hO : ∀ o : ↥Gz, o ∈ CFSG.Open.pCore 2 ↥Gz → (o : G) ∈ T)
    (hZK : Z ≤ Kz) (hTZ : T ⊓ Kz ≤ Z) {y : G} (hyG : y ∈ Gz) (hyK : y ∈ Kz)
    (h : qPi Gz ⟨y, hyG⟩ ∈ imageOTwoQuot Gz Z) : y ∈ Z := by
  obtain ⟨w, hw, hwy⟩ := h
  have hwZ : (w : G) ∈ Z := Subgroup.mem_subgroupOf.mp hw
  have hker : w⁻¹ * ⟨y, hyG⟩ ∈ CFSG.Open.pCore 2 ↥Gz := QuotientGroup.eq.mp hwy
  have h1 : (w : G)⁻¹ * y ∈ T := hO _ hker
  have h2 : (w : G)⁻¹ * y ∈ Kz := Kz.mul_mem (Kz.inv_mem (hZK hwZ)) hyK
  have e : y = (w : G) * ((w : G)⁻¹ * y) := by group
  rw [e]
  exact Z.mul_mem hwZ (hTZ ⟨h1, h2⟩)

omit [Finite G] in
theorem image_inf_le {Gz T K : Subgroup G}
    (hO : ∀ o : ↥Gz, o ∈ CFSG.Open.pCore 2 ↥Gz → (o : G) ∈ T) :
    imageOTwoQuot Gz T ⊓ imageOTwoQuot Gz K ≤ imageOTwoQuot Gz (T ⊓ K) := by
  rintro x ⟨⟨t, ht, rfl⟩, ⟨k, hk, hkt⟩⟩
  have hker : t⁻¹ * k ∈ CFSG.Open.pCore 2 ↥Gz := QuotientGroup.eq.mp hkt.symm
  have h1 : (t : G)⁻¹ * k ∈ T := hO _ hker
  have hkT : (k : G) ∈ T := by
    have e : (k : G) = t * ((t : G)⁻¹ * k) := by group
    rw [e]
    exact T.mul_mem (Subgroup.mem_subgroupOf.mp ht) h1
  exact ⟨k, Subgroup.mem_subgroupOf.mpr ⟨hkT, Subgroup.mem_subgroupOf.mp hk⟩, hkt⟩

omit [Finite G] in
theorem conj_mem_image {Gz B : Subgroup G} {s : G} (hsG : s ∈ Gz)
    (hsB : s ∈ Subgroup.normalizer (B : Set G)) {y : OTwoQuot Gz}
    (hy : y ∈ imageOTwoQuot Gz B) :
    qPi Gz ⟨s, hsG⟩ * y * (qPi Gz ⟨s, hsG⟩)⁻¹ ∈ imageOTwoQuot Gz B :=
  q_image_normalizes (L := Subgroup.zpowers s) ((Subgroup.zpowers_le).mpr hsB) _
    ⟨⟨s, hsG⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers s), rfl⟩ y hy

omit [Finite G] in
theorem conj_inv_mem_image {Gz B : Subgroup G} {s : G} (hsG : s ∈ Gz)
    (hsB : s ∈ Subgroup.normalizer (B : Set G)) {y : OTwoQuot Gz}
    (hy : y ∈ imageOTwoQuot Gz B) :
    (qPi Gz ⟨s, hsG⟩)⁻¹ * y * qPi Gz ⟨s, hsG⟩ ∈ imageOTwoQuot Gz B := by
  have hσ : (qPi Gz ⟨s, hsG⟩)⁻¹ ∈ imageOTwoQuot Gz (Subgroup.zpowers s) :=
    ⟨⟨s, hsG⟩⁻¹, Subgroup.mem_subgroupOf.mpr (Subgroup.inv_mem _ (Subgroup.mem_zpowers s)),
      map_inv (qPi Gz) _⟩
  have h := q_image_normalizes (L := Subgroup.zpowers s) ((Subgroup.zpowers_le).mpr hsB) _ hσ y hy
  rwa [inv_inv] at h

theorem factorization_3600 : (3600 : ℕ).factorization 2 = 4 := by
  have e : (3600 : ℕ) = 2 ^ 4 * 225 := by norm_num
  rw [e, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

theorem borel_setting
    {Gz K T X Kz : Subgroup G} {s : G}
    (hK : K ∈ cComp Gz) (hTG : IsSylowIn 2 T Gz) (hsT : s ∈ T)
    (hsN : s ∉ Subgroup.normalizer (K : Set G))
    (hKz : Kz = K ⊔ CFSG.Quasithin.conjSub s⁻¹ K) (hKzN : Gz ≤ Subgroup.normalizer (Kz : Set G))
    (hA5 : Nonempty (OTwoQuot K ≃* alternatingGroup (Fin 5)))
    (hXKz : X ≤ Kz) (hXs : s ∈ Subgroup.normalizer (X : Set G)) (h9 : 9 ∣ Nat.card X)
    (hB' : ¬ Kz ≤ X ⊔ (T ⊓ Kz)) :
    (∀ Y : Subgroup G, T ⊓ Kz ≤ Y → Y ≤ Kz → s ∈ Subgroup.normalizer (Y : Set G) →
        Kz ≤ Y ∨ Y ≤ X ⊔ (T ⊓ Kz)) ∧
      X ≤ Subgroup.normalizer ((T ⊓ Kz : Subgroup G) : Set G) ∧
      ∃ k : ℕ, Nat.card X ∣ 144 * 2 ^ k := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  subst hKz
  set K₂ := CFSG.Quasithin.conjSub s⁻¹ K with hK₂def
  set Kz := K ⊔ K₂ with hKzdef
  have hsG : s ∈ Gz := hTG.le hsT
  have hKG : K ≤ Gz := le_of_mem_cComp hK
  have hK₂ : K₂ ∈ cComp Gz := conjSub_mem_cComp_of_mem hK (Gz.inv_mem hsG)
  have hK₂G : K₂ ≤ Gz := le_of_mem_cComp hK₂
  have hKzG : Kz ≤ Gz := sup_le hKG hK₂G
  have hsN' : s⁻¹ ∉ Subgroup.normalizer (K : Set G) := fun h =>
    hsN (by simpa using (Subgroup.normalizer (K : Set G)).inv_mem h)
  have hss : CFSG.Quasithin.conjSub s⁻¹ K₂ = K :=
    SBc16.conjSub_conjSub_eq_of_mem_cComp hK hK₂ (Gz.inv_mem hsG) hsN' hKzN
  have hsK : CFSG.Quasithin.conjSub s K = K₂ := by
    calc CFSG.Quasithin.conjSub s K
        = CFSG.Quasithin.conjSub s (CFSG.Quasithin.conjSub s⁻¹ K₂) := by rw [hss]
      _ = K₂ := CFSG.Quasithin.conjSub_inv_conjSub s K₂
  have hne : K ≠ K₂ := by
    intro h
    apply hsN'
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have h1 : s⁻¹ * x * s⁻¹⁻¹ ∈ K₂ := CFSG.Quasithin.mul_mem_conjSub hx
      rwa [← h] at h1
    · intro hx
      have hx' : s⁻¹ * x * s⁻¹⁻¹ ∈ K₂ := h ▸ hx
      have h1 := CFSG.Quasithin.mem_conjSub.mp hx'
      rwa [show s⁻¹⁻¹ * (s⁻¹ * x * s⁻¹⁻¹) * s⁻¹ = x by group] at h1
  have hO : ∀ o : ↥Gz, o ∈ CFSG.Open.pCore 2 ↥Gz → (o : G) ∈ T := by
    intro o ho
    have := CFSG.LieType.BorelTits.pCore_normal 2 (G := ↥Gz)
    have h := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥Gz) 2).le_sylow_of_normal
      hTG.toSylow
    exact Subgroup.mem_subgroupOf.mp (h ho)
  set σ : OTwoQuot Gz := qPi Gz ⟨s, hsG⟩ with hσdef
  set N₁ := imageOTwoQuot Gz K with hN₁def
  set N₂ := imageOTwoQuot Gz K₂ with hN₂def
  have hN₂σ : N₂ = N₁.map (MulAut.conj σ).toMonoidHom := by
    rw [hN₂def, ← hsK]
    exact q_image_conjSub hsG
  have hN₂σ' : N₂ = N₁.map (MulAut.conj σ⁻¹).toMonoidHom := by
    rw [hN₂def, hK₂def, q_image_conjSub (Gz.inv_mem hsG)]
    have e : qPi Gz ⟨s⁻¹, Gz.inv_mem hsG⟩ = σ⁻¹ := map_inv (qPi Gz) ⟨s, hsG⟩
    rw [e]
  have hσ₃ : ∀ a ∈ N₁, σ⁻¹ * a * σ ∈ N₂ := fun a ha => by
    rw [hN₂σ']
    refine ⟨a, ha, ?_⟩
    simp
  have hσ₂ : ∀ b ∈ N₂, σ⁻¹ * b * σ ∈ N₁ := fun b hb => by
    rw [hN₂σ] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    have e : σ⁻¹ * (MulAut.conj σ).toMonoidHom a * σ = a := by
      simp [MulAut.conj_apply, mul_assoc]
    rw [e]
    exact ha
  obtain ⟨e₁⟩ := q_oTwoQuot_equiv_image (G₁ := Gz) (subnormal_of_mem_cComp hK)
  obtain ⟨e₅⟩ := hA5
  have eN : ↥N₁ ≃* alternatingGroup (Fin 5) := e₁.symm.trans e₅
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hs₁ : IsSimpleGroup ↥N₁ := eN.isSimpleGroup
  obtain ⟨hR, hEf⟩ := a5_facts eN
  have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hN₁card : Nat.card ↥N₁ = 60 := (Nat.card_congr eN.toEquiv).trans h60
  obtain ⟨hcomm, hdisj⟩ := q_pair_comm_disjoint hK hK₂ hne hs₁
    (le_sup_right.trans (SBc16.sup_le_normalizer_of_mem_cComp hK hK₂))
    (le_sup_right.trans (SBc16.sup_le_normalizer_of_mem_cComp hK₂ hK))
  have hN₂card : Nat.card ↥N₂ = 60 := by
    rw [hN₂σ, Subgroup.card_map_of_injective (MulAut.conj σ).injective]
    exact hN₁card
  have hKzhat : imageOTwoQuot Gz Kz = N₁ ⊔ N₂ := q_image_sup hKG hK₂G
  have hN12card : Nat.card ↥(N₁ ⊔ N₂) = 3600 := by
    rw [SBc15.card_sup_eq_mul_of_commute hcomm (disjoint_iff.mpr hdisj), hN₁card, hN₂card]
  set That := imageOTwoQuot Gz T with hThatdef
  have hThat : IsSylowIn 2 That ⊤ := by
    let P : Sylow 2 (OTwoQuot Gz) := hTG.toSylow.mapSurjective (qPi_surjective Gz)
    have hP : (P : Subgroup (OTwoQuot Gz)) = That := by
      rw [Sylow.coe_mapSurjective]
      rfl
    refine ⟨le_top, ?_, ?_⟩
    · rw [← hP]
      exact P.isPGroup'
    · rw [Subgroup.relIndex_top_right, ← hP]
      exact P.not_dvd_index
  have hN12n : (N₁ ⊔ N₂).Normal := by
    rw [← hKzhat]
    have h1 : (Kz.subgroupOf Gz).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKzG).mpr hKzN
    exact h1.map (qPi Gz) (qPi_surjective Gz)
  have hN₂N₁ : N₂ ≤ Subgroup.normalizer (N₁ : Set (OTwoQuot Gz)) := le_normalizer_of_comm hcomm
  have hN12norm : ((N₁ ⊔ N₂).subgroupOf ⊤).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mpr
      (Subgroup.normalizer_eq_top_iff.mpr hN12n).ge
  have hS12 : IsSylowIn 2 (That ⊓ (N₁ ⊔ N₂)) (N₁ ⊔ N₂) := hThat.inf_normal le_top hN12norm
  have hS12card : Nat.card ↥(That ⊓ (N₁ ⊔ N₂)) = 16 := by
    rw [hS12.card_eq, hN12card, factorization_3600]
    norm_num
  have hN1n : (N₁.subgroupOf (N₁ ⊔ N₂)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hN₂N₁)
  set E := That ⊓ N₁ with hEdef
  have hE : IsSylowIn 2 E N₁ := by
    have h := hS12.inf_normal le_sup_left hN1n
    rwa [inf_assoc, inf_eq_right.mpr (le_sup_left : N₁ ≤ N₁ ⊔ N₂)] at h
  have hE2' : IsPGroup 2 ↥(E.subgroupOf N₁) :=
    hE.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hE.le).symm
  have hEodd : ¬ 2 ∣ (E.subgroupOf N₁).index := hE.not_dvd_relIndex
  obtain ⟨hEcard', hNEidx⟩ := hEf (E.subgroupOf N₁) hE2' hEodd
  have hEcard : Nat.card ↥E = 4 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE.le).toEquiv).symm.trans hEcard'
  set B₁ := N₁ ⊓ Subgroup.normalizer (E : Set (OTwoQuot Gz)) with hB₁def
  have hB₁sub : B₁.subgroupOf N₁ =
      Subgroup.normalizer ((E.subgroupOf N₁ : Subgroup ↥N₁) : Set ↥N₁) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_normalizer_subgroupOf_iff hE.le]
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  have hB₁card : Nat.card ↥B₁ = 12 := by
    have h1 := (Subgroup.normalizer ((E.subgroupOf N₁ : Subgroup ↥N₁) : Set ↥N₁)).card_mul_index
    rw [hNEidx, hN₁card] at h1
    have h2 : Nat.card ↥B₁ = Nat.card ↥(B₁.subgroupOf N₁) :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm
    rw [h2, hB₁sub]
    omega
  set B₂ := B₁.map (MulAut.conj σ).toMonoidHom with hB₂def
  have hB₂N₂ : B₂ ≤ N₂ := by
    rw [hN₂σ]
    exact Subgroup.map_mono inf_le_left
  have hB₂card : Nat.card ↥B₂ = 12 := by
    rw [hB₂def, Subgroup.card_map_of_injective (MulAut.conj σ).injective]
    exact hB₁card
  set Bh := B₁ ⊔ B₂ with hBhdef
  have hBhcard : Nat.card ↥Bh = 144 := by
    have hd : Disjoint B₁ B₂ := by
      rw [disjoint_iff, eq_bot_iff]
      intro x hx
      rw [← hdisj]
      exact ⟨hx.1.1, hB₂N₂ hx.2⟩
    have hc : ∀ a ∈ B₁, ∀ b ∈ B₂, a * b = b * a := fun a ha b hb => hcomm a ha.1 b (hB₂N₂ hb)
    rw [hBhdef, SBc15.card_sup_eq_mul_of_commute hc hd, hB₁card, hB₂card]
  have hEimg : ∀ Y : Subgroup G, T ⊓ Kz ≤ Y → E ≤ imageOTwoQuot Gz Y := fun Y hTY =>
    (image_inf_le hO).trans (image_mono ((inf_le_inf_left T le_sup_left).trans hTY))
  have key : ∀ Y : Subgroup G, T ⊓ Kz ≤ Y → Y ≤ Kz → s ∈ Subgroup.normalizer (Y : Set G) →
      Kz ≤ Y ∨ imageOTwoQuot Gz Y ≤ Bh := by
    intro Y hTY hYK hsY
    have hYhat : imageOTwoQuot Gz Y ≤ N₁ ⊔ N₂ := hKzhat ▸ image_mono hYK
    rcases le_or_forall_of_swap hs₁ hR hcomm hσ₂ hσ₃ hYhat
        (fun y hy => conj_mem_image hsG hsY hy) (fun y hy => conj_inv_mem_image hsG hsY hy)
        hE.le hE.isPGroup hEodd (hEimg Y hTY) with h | h
    · left
      intro y hy
      have hyG := hKzG hy
      have hmem : qPi Gz ⟨y, hyG⟩ ∈ N₁ ⊔ N₂ :=
        hKzhat ▸ ⟨⟨y, hyG⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
      exact mem_of_qPi_mem hO hYK hTY hyG hy (h hmem)
    · right
      intro y hy
      obtain ⟨a, ha, b, hb, rfl, haE, hbE⟩ := h y hy
      refine Subgroup.mul_mem_sup ⟨ha, haE⟩ ⟨σ⁻¹ * b * σ, ⟨hσ₂ b hb, hbE⟩, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
  have hB'K : X ⊔ (T ⊓ Kz) ≤ Kz := sup_le hXKz inf_le_right
  have hsTKz : s ∈ Subgroup.normalizer ((T ⊓ Kz : Subgroup G) : Set G) :=
    E1.mem_normalizer_inf (Subgroup.le_normalizer hsT) (hKzN hsG)
  have hsB' : s ∈ Subgroup.normalizer ((X ⊔ (T ⊓ Kz) : Subgroup G) : Set G) :=
    E1.mem_normalizer_sup hXs hsTKz
  have hB'img : imageOTwoQuot Gz (X ⊔ (T ⊓ Kz)) ≤ Bh := by
    rcases key _ le_sup_right hB'K hsB' with h | h
    · exact absurd h hB'
    · exact h
  set Bp := imageOTwoQuot Gz (X ⊔ (T ⊓ Kz)) with hBpdef
  have hEB : E ≤ Bp := hEimg _ le_sup_right
  set Eσ := E.map (MulAut.conj σ).toMonoidHom with hEσdef
  have hEσB : Eσ ≤ Bp := by
    rintro _ ⟨x, hx, rfl⟩
    exact conj_mem_image hsG hsB' (hEB hx)
  have hEσN₂ : Eσ ≤ N₂ := by
    rw [hN₂σ]
    exact Subgroup.map_mono hE.le
  have hEσcard : Nat.card ↥Eσ = 4 := by
    rw [hEσdef, Subgroup.card_map_of_injective (MulAut.conj σ).injective]
    exact hEcard
  have hEEcard : Nat.card ↥(E ⊔ Eσ) = 16 := by
    have hd : Disjoint E Eσ := by
      rw [disjoint_iff, eq_bot_iff]
      intro x hx
      rw [← hdisj]
      exact ⟨hE.le hx.1, hEσN₂ hx.2⟩
    rw [SBc15.card_sup_eq_mul_of_commute (fun a ha b hb => hcomm a (hE.le ha) b (hEσN₂ hb)) hd,
      hEcard, hEσcard]
  have h16 : 16 ∣ Nat.card ↥Bp := hEEcard ▸ Subgroup.card_dvd_of_le (sup_le hEB hEσB)
  have hXG : X ≤ Gz := hXKz.trans hKzG
  have hXcard : ∃ k : ℕ, 2 ^ k * Nat.card ↥(imageOTwoQuot Gz X) = Nat.card X := by
    set φ := (qPi Gz).comp (Subgroup.inclusion hXG) with hφ
    have hr : φ.range = imageOTwoQuot Gz X := q_range_comp_eq_image hXG
    have hk2 : IsPGroup 2 φ.ker := by
      have hle : φ.ker ≤ (CFSG.Open.pCore 2 ↥Gz).comap (Subgroup.inclusion hXG) := fun x hx => by
        have h1 : (QuotientGroup.mk (Subgroup.inclusion hXG x) : OTwoQuot Gz) = 1 := hx
        exact (QuotientGroup.eq_one_iff (Subgroup.inclusion hXG x)).mp h1
      exact ((CFSG.LieType.BorelTits.pCore_isPGroup 2).comap_of_injective _
        (Subgroup.inclusion_injective hXG)).to_le hle
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hk2
    have hcard := φ.ker.card_mul_index
    rw [Subgroup.index_ker, hr, hk] at hcard
    exact ⟨k, hcard⟩
  obtain ⟨kX, hkX⟩ := hXcard
  have h9X : 9 ∣ Nat.card ↥(imageOTwoQuot Gz X) := by
    have h1 : 9 ∣ 2 ^ kX * Nat.card ↥(imageOTwoQuot Gz X) := hkX ▸ h9
    have hcop : Nat.Coprime 9 (2 ^ kX) :=
      Nat.Coprime.pow_right kX (by norm_num)
    exact hcop.dvd_of_dvd_mul_left h1
  have h9B : 9 ∣ Nat.card ↥Bp := h9X.trans (Subgroup.card_dvd_of_le (image_mono le_sup_left))
  have h144 : 144 ∣ Nat.card ↥Bp := by
    have h := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 16 9) h16 h9B
    norm_num at h
    exact h
  have hBpeq : Bp = Bh := by
    apply Subgroup.eq_of_le_of_card_ge hB'img
    rw [hBhcard]
    exact Nat.le_of_dvd Nat.card_pos h144
  refine ⟨fun Y hTY hYK hsY => ?_, ?_, kX, ?_⟩
  rotate_left 2
  ·
    rw [← hkX, mul_comm]
    refine Nat.mul_dvd_mul_right ?_ _
    rw [← hBhcard, ← hBpeq]
    exact Subgroup.card_dvd_of_le (image_mono le_sup_left)
  · rcases key Y hTY hYK hsY with h | h
    · exact Or.inl h
    · right
      intro y hy
      have hyG := hKzG (hYK hy)
      have hmem : qPi Gz ⟨y, hyG⟩ ∈ Bp :=
        hBpeq ▸ h ⟨⟨y, hyG⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
      exact mem_of_qPi_mem hO hB'K le_sup_right hyG (hYK hy) hmem
  ·
    set D := imageOTwoQuot Gz (T ⊓ Kz) with hDdef
    have hED : E ⊔ Eσ ≤ D := by
      refine sup_le (hEimg _ le_rfl) ?_
      rintro _ ⟨x, hx, rfl⟩
      exact conj_mem_image hsG hsTKz (hEimg _ le_rfl hx)
    have hDS : D ≤ That ⊓ (N₁ ⊔ N₂) :=
      le_inf (image_mono inf_le_left) (hKzhat ▸ image_mono inf_le_right)
    have hDeq : E ⊔ Eσ = D := by
      apply Subgroup.eq_of_le_of_card_ge hED
      rw [hEEcard, ← hS12card]
      exact Subgroup.card_le_of_le hDS
    have hB₁E : B₁ ≤ Subgroup.normalizer ((E ⊔ Eσ : Subgroup (OTwoQuot Gz)) : Set (OTwoQuot Gz)) :=
      fun x hx => E1.mem_normalizer_sup hx.2
        (le_normalizer_of_comm (fun a ha b (hb : b ∈ B₁) => (hcomm b hb.1 a (hEσN₂ ha)).symm) hx)
    have hB₂E : B₂ ≤ Subgroup.normalizer ((E ⊔ Eσ : Subgroup (OTwoQuot Gz)) : Set (OTwoQuot Gz)) :=
      fun x hx => E1.mem_normalizer_sup
        (le_normalizer_of_comm (fun a ha b hb => hcomm a (hE.le ha) b (hB₂N₂ hb)) hx)
        ((Subgroup.map_mono (inf_le_right : B₁ ≤ _)).trans
          (Subgroup.le_normalizer_map (MulAut.conj σ).toMonoidHom) hx)
    have hBhD : Bh ≤ Subgroup.normalizer (D : Set (OTwoQuot Gz)) := hDeq ▸ sup_le hB₁E hB₂E
    intro x hxX
    have hxG := hXG hxX
    have hxK := hXKz hxX
    refine E1.mem_normalizer_of_conj_mem fun d hd => ?_
    have hdG := hKzG hd.2
    have hcK : x * d * x⁻¹ ∈ Kz := Kz.mul_mem (Kz.mul_mem hxK hd.2) (Kz.inv_mem hxK)
    have hcG := hKzG hcK
    have hxq : qPi Gz ⟨x, hxG⟩ ∈ Subgroup.normalizer (D : Set (OTwoQuot Gz)) :=
      hBhD (hBpeq ▸ image_mono le_sup_left ⟨⟨x, hxG⟩, Subgroup.mem_subgroupOf.mpr hxX, rfl⟩)
    have hdq : qPi Gz ⟨d, hdG⟩ ∈ D := ⟨⟨d, hdG⟩, Subgroup.mem_subgroupOf.mpr hd, rfl⟩
    have hmem : qPi Gz ⟨x * d * x⁻¹, hcG⟩ ∈ D := by
      have h1 := (Subgroup.mem_normalizer_iff.mp hxq _).mp hdq
      have e : qPi Gz ⟨x * d * x⁻¹, hcG⟩ =
          qPi Gz ⟨x, hxG⟩ * qPi Gz ⟨d, hdG⟩ * (qPi Gz ⟨x, hxG⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [e]
      exact h1
    exact mem_of_qPi_mem hO inf_le_right le_rfl hcG hcK hmem

end Quot

end Ch8310

end CFSG.Quasithin.H13
