module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15221Three
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15221Y1
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15221Y0Eq
public import CFSG.Quasithin.EmptyFaithful.S14117Star
public import CFSG.Quasithin.EmptyFaithful.S152Y02

public section

namespace CFSG.Quasithin.S15221

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.S15223

variable {G : Type} [Group G] [Finite G]

section Generic

theorem inf_eq_bot_of_card_three {K : Type*} [Group K] {A B : Subgroup K} (hA : Nat.card A = 3)
    (hB : Nat.card B = 3) (hne : A ≠ B) : A ⊓ B = ⊥ := by
  have : Finite A := Nat.finite_of_card_ne_zero (by omega)
  have : Finite B := Nat.finite_of_card_ne_zero (by omega)
  by_contra hbot
  have hd : Nat.card ↥(A ⊓ B) ∣ 3 := hA ▸ Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
  · exact hbot (Subgroup.card_eq_one.mp h1)
  · have e1 : A ⊓ B = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hA])
    have e2 : A ⊓ B = B := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, hB])
    exact hne (e1.symm.trans e2)

theorem card_sup_eq_nine {K : Type*} [Group K] {A B E : Subgroup K} (hA : Nat.card A = 3)
    (hB : Nat.card B = 3) (hE : Nat.card E = 9) (hAE : A ≤ E) (hBE : B ≤ E) (hne : A ≠ B) :
    Nat.card ↥(A ⊔ B) = 9 := by
  have : Finite A := Nat.finite_of_card_ne_zero (by omega)
  have : Finite B := Nat.finite_of_card_ne_zero (by omega)
  have : Finite E := Nat.finite_of_card_ne_zero (by omega)
  have hle : A ⊔ B ≤ E := sup_le hAE hBE
  have : Finite ↥(A ⊔ B) :=
    Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  have hd : Nat.card ↥(A ⊔ B) ∣ 9 := hE ▸ Subgroup.card_dvd_of_le hle
  have hd3 : 3 ∣ Nat.card ↥(A ⊔ B) := hA ▸ Subgroup.card_dvd_of_le le_sup_left
  have hne3 : Nat.card ↥(A ⊔ B) ≠ 3 := by
    intro h3
    have e1 : A = A ⊔ B := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h3, hA])
    have e2 : B = A ⊔ B := Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [h3, hB])
    exact hne (e1.trans e2.symm)
  have : Nat.card ↥(A ⊔ B) ≤ 9 := Nat.le_of_dvd (by norm_num) hd
  have : 0 < Nat.card ↥(A ⊔ B) := Nat.card_pos
  interval_cases h : Nat.card ↥(A ⊔ B) <;> omega

theorem pow_eq_one_of_mem_sup {K : Type*} [Group K] {A B : Subgroup K} {p : ℕ}
    (hA : ∀ a ∈ A, a ^ p = 1) (hB : ∀ b ∈ B, b ^ p = 1) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    ∀ x ∈ A ⊔ B, x ^ p = 1 := by
  have hBN : B ≤ Subgroup.normalizer (A : Set K) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      have h1 : e * k * e⁻¹ = k := by
        have := hc k hk e he
        calc e * k * e⁻¹ = (k * e) * e⁻¹ := by rw [this]
          _ = k := by group
      rw [h1]
      exact hk
    · intro hk
      have h1 := hc _ hk e⁻¹ (B.inv_mem he)
      have h2 : k = e * k * e⁻¹ := by
        calc k = e⁻¹ * (e * k * e⁻¹) * e := by group
          _ = (e * k * e⁻¹) * e⁻¹ * e := by rw [← h1]
          _ = e * k * e⁻¹ := by group
      rw [h2]
      exact hk
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_le_normalizer hBN).mp hx
  rw [(show Commute a b from hc a ha b hb).mul_pow, hA a ha, hB b hb, one_mul]

theorem exists_sylow_three_of_card_nine {V X : Subgroup G}
    (hXV : X ≤ Subgroup.normalizer (V : Set G))
    (h2 : IsPGroup 2 ↥(X ⊓ Subgroup.centralizer (V : Set G))) (h9 : Nat.card (autOn X V) = 9) :
    ∃ D : Subgroup G, D ≤ X ∧ IsPGroup 3 D ∧ Nat.card D = 9 ∧
      D ⊓ Subgroup.centralizer (V : Set G) = ⊥ := by
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨D, hD⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 X
  have hD3 : IsPGroup 3 D := hD.isPGroup
  refine ⟨D, hD.le, hD3, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
    have h1 := Subgroup.relIndex_mul_card (X ⊓ Subgroup.centralizer (V : Set G)) X
    rw [inf_of_le_left (inf_le_left : X ⊓ Subgroup.centralizer (V : Set G) ≤ X),
      ← card_autOn_eq_relIndex hXV, h9, hk] at h1
    have hfac : (Nat.card X).factorization 3 = 2 := by
      rw [← h1, Nat.factorization_mul (by norm_num) (by positivity)]
      have e9 : (9 : ℕ) = 3 ^ 2 := by norm_num
      rw [e9, Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three,
        Nat.Prime.factorization_pow Nat.prime_two]
      simp
    rw [hD.card_eq, hfac]
    norm_num
  · have hdis : Disjoint (X ⊓ Subgroup.centralizer (V : Set G)) D :=
      IsPGroup.disjoint_of_ne 2 3 (by norm_num) _ _ h2 hD3
    refine le_bot_iff.mp ?_
    calc D ⊓ Subgroup.centralizer (V : Set G)
        ≤ (X ⊓ Subgroup.centralizer (V : Set G)) ⊓ D :=
          le_inf (inf_le_inf_right _ hD.le) inf_le_left
      _ = ⊥ := disjoint_iff.mp hdis

end Generic

section Setting

variable {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I : Subgroup G}

theorem autOn_le_oTwoUpper_autOn {V Y M : Subgroup G} (hMV : M ≤ Subgroup.normalizer (V : Set G))
    (hYM : Y ≤ M) (hY : Y = oTwoUpper Y) : autOn Y V ≤ oTwoUpper (autOn M V) := by
  have h1 : autOn Y V = autOn (oTwoUpper Y) V := congrArg (fun X => autOn X V) hY
  rw [h1, ← A4.oTwoUpper_autOn (hYM.trans hMV)]
  exact oTwoUpper_mono (A4.autOn_mono hYM)

theorem isPGroup_two_sup_inf_centralizer {V Y Y₁ M : Subgroup G}
    (hMV : M ≤ Subgroup.normalizer (V : Set G)) (hYM : Y ≤ M)
    (hYn : M ≤ Subgroup.normalizer (Y : Set G)) (hY₁M : Y₁ ≤ M)
    (hYC : Y ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 M)
    (hY₁C : Y₁ ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 Y₁)
    (hbot : autOn Y V ⊓ autOn Y₁ V = ⊥) :
    IsPGroup 2 ↥((Y ⊔ Y₁) ⊓ Subgroup.centralizer (V : Set G)) := by
  intro z
  obtain ⟨hzX, hzC⟩ := z.2
  obtain ⟨y, hy, y₁, hy₁, hyz⟩ :=
    (mem_sup_iff_of_le_normalizer (hY₁M.trans hYn)).mp hzX
  have hyM : y ∈ M := hYM hy
  have hy₁M : y₁ ∈ M := hY₁M hy₁
  have hzM : (z : G) ∈ M := by rw [← hyz]; exact M.mul_mem hyM hy₁M
  have h1 : conjAct V ⟨y, hMV hyM⟩ * conjAct V ⟨y₁, hMV hy₁M⟩ = 1 := by
    rw [← map_mul]
    have : (⟨y, hMV hyM⟩ * ⟨y₁, hMV hy₁M⟩ : Subgroup.normalizer (V : Set G)) =
        ⟨(z : G), hMV hzM⟩ := Subtype.ext hyz
    rw [this]
    exact A4.conjAct_eq_one_iff.mpr hzC
  have h2 : conjAct V ⟨y, hMV hyM⟩ = (conjAct V ⟨y₁, hMV hy₁M⟩)⁻¹ := eq_inv_of_mul_eq_one_left h1
  have hmem1 : conjAct V ⟨y, hMV hyM⟩ ∈ autOn Y V ⊓ autOn Y₁ V :=
    ⟨mem_autOn_of_mem (hMV hyM) hy, by
      rw [h2]
      exact (autOn Y₁ V).inv_mem (mem_autOn_of_mem (hMV hy₁M) hy₁)⟩
  rw [hbot, Subgroup.mem_bot] at hmem1
  have hyC : y ∈ Subgroup.centralizer (V : Set G) := A4.conjAct_eq_one_iff.mp hmem1
  have hy₁C' : conjAct V ⟨y₁, hMV hy₁M⟩ = 1 := by
    rw [h2] at hmem1
    simpa using hmem1
  have hy₁C : y₁ ∈ Subgroup.centralizer (V : Set G) := A4.conjAct_eq_one_iff.mp hy₁C'
  have hyQ : y ∈ pCoreOf 2 M := hYC ⟨hy, hyC⟩
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 Y₁ ⟨y₁, by rw [← hY₁C]; exact ⟨hy₁, hy₁C⟩⟩
  have hk' : y₁ ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hzk : (z : G) ^ 2 ^ k ∈ pCoreOf 2 M := by
    have hq : (QuotientGroup.mk (⟨(z : G), hzM⟩ : ↥M) : OTwoQuot M) ^ 2 ^ k = 1 := by
      have e : (⟨(z : G), hzM⟩ : ↥M) = ⟨y, hyM⟩ * ⟨y₁, hy₁M⟩ := Subtype.ext hyz.symm
      rw [e, QuotientGroup.mk_mul, (mk_eq_one_iff_mem_pCoreOf _).mpr hyQ, one_mul,
        ← QuotientGroup.mk_pow]
      have : (⟨y₁, hy₁M⟩ : ↥M) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
      rw [this, QuotientGroup.mk_one]
    rw [← QuotientGroup.mk_pow] at hq
    have := (mk_eq_one_iff_mem_pCoreOf _).mp hq
    simpa using this
  obtain ⟨j, hj⟩ := pCoreOf_isPGroup 2 M ⟨(z : G) ^ 2 ^ k, hzk⟩
  refine ⟨k + j, Subtype.ext ?_⟩
  have hj' : ((z : G) ^ 2 ^ k) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have : (z : G) ^ 2 ^ (k + j) = 1 := by rw [pow_add, pow_mul, hj']
  simpa using this

theorem isThreePrimeGroup_of_caseIII (h : S152Y.Data T Mc M) (hs : Setting152 T Mc M)
    (hB₀ : IsB0 T Mc M B₀) (hD : Inputs152 T Mc M H B₀ I) (hii : Concl15218ii T Mc M H B₀ I)
    (hYn : M ≤ Subgroup.normalizer (yOf152 T Mc M : Set G)) (c3 : Case15203iii T Mc M)
    {Y₁ : Subgroup G} (hY₁N : Y₁ ≤ M ⊓ I) (hY₁eq : Y₁ = oTwoUpper Y₁)
    (hY₁3 : (pCoreOf 2 Y₁).relIndex Y₁ = 3) (hnot : ¬ Y₁ ≤ Mc ⊓ I) :
    IsThreePrimeGroup (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) := by
  obtain ⟨-, -, -, hY3, hYC, n, -, hSyl⟩ := c3
  have hOmS : Om4FactsStatement := fun _ _ _ _ hX => S152O4.om4_facts hX
  have hMV : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := le_normalizer_V154 T Mc M
  have hYM : yOf152 T Mc M ≤ M := h.yOf_le_M
  have hYeq : yOf152 T Mc M = oTwoUpper (yOf152 T Mc M) := (oTwoUpper_idem_eq _).symm
  obtain ⟨hodd, hEab⟩ := oTwoUpper_Mb_odd_comm hD hOmS
  have hE9 : Nat.card (oTwoUpper (autOn M (V154 T Mc M))) = 9 := (om4_card152 hOmS hii.2.2.1).2
  have hY₁M : Y₁ ≤ M := hY₁N.trans inf_le_left
  obtain ⟨hE₁, hY₁card, hY₁C⟩ := autOn_Y1_facts hs hD hodd hY₁M hY₁eq hY₁3 hnot
  have hD0 : autOn Y₁ (V154 T Mc M) ≠ ⊥ := fun hb => by
    rw [hb, Subgroup.card_bot] at hY₁card
    omega
  have hne := autOn_ne_of_normal hs hB₀ hD hii hY₁N hE₁ hD0 hYM hYn
  have hE_Y := autOn_le_oTwoUpper_autOn hMV hYM hYeq
  have hbot := inf_eq_bot_of_card_three hY3 hY₁card hne
  have hXV : yOf152 T Mc M ⊔ Y₁ ≤ Subgroup.normalizer (V154 T Mc M : Set G) :=
    sup_le (hYM.trans hMV) (hY₁M.trans hMV)
  have hX9 : Nat.card (autOn (yOf152 T Mc M ⊔ Y₁) (V154 T Mc M)) = 9 := by
    rw [autOn_sup (hYM.trans hMV) (hY₁M.trans hMV)]
    exact card_sup_eq_nine hY3 hY₁card hE9 hE_Y hE₁ hne
  have h2 := isPGroup_two_sup_inf_centralizer hMV hYM hYn hY₁M hYC hY₁C hbot
  obtain ⟨D, hDX, hD3, hD9, hDC⟩ := exists_sylow_three_of_card_nine hXV h2 hX9
  have hDM : D ≤ M := hDX.trans (sup_le hYM hY₁M)
  have hexp : ∀ a ∈ autOn (yOf152 T Mc M ⊔ Y₁) (V154 T Mc M), a ^ 3 = 1 := by
    rw [autOn_sup (hYM.trans hMV) (hY₁M.trans hMV)]
    refine pow_eq_one_of_mem_sup (fun a ha => ?_) (fun b hb => ?_) (fun a ha b hb => ?_)
    · have := pow_card_eq_one' (G := autOn (yOf152 T Mc M) (V154 T Mc M)) (x := ⟨a, ha⟩)
      rw [hY3] at this
      simpa using congrArg Subtype.val this
    · have := pow_card_eq_one' (G := autOn Y₁ (V154 T Mc M)) (x := ⟨b, hb⟩)
      rw [hY₁card] at this
      simpa using congrArg Subtype.val this
    · exact hEab a (hE_Y ha) b (hE₁ hb)
  have hDe : ∀ x ∈ D, x ^ 3 = 1 := by
    intro x hx
    have hxN : x ∈ Subgroup.normalizer (V154 T Mc M : Set G) := hXV (hDX hx)
    have h1 : (conjAct (V154 T Mc M) ⟨x, hxN⟩) ^ 3 = 1 :=
      hexp _ (mem_autOn_of_mem hxN (hDX hx))
    have h2' : conjAct (V154 T Mc M) ⟨x ^ 3, hXV (hDX (D.pow_mem hx 3))⟩ = 1 := by
      rw [← h1, ← map_pow]
      rfl
    have h3 : x ^ 3 ∈ D ⊓ Subgroup.centralizer (V154 T Mc M : Set G) :=
      ⟨D.pow_mem hx 3, A4.conjAct_eq_one_iff.mp h2'⟩
    rw [hDC, Subgroup.mem_bot] at h3
    exact h3
  have hCvN : M ≤ Subgroup.normalizer
      ((M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf_centralizer' Subgroup.le_normalizer hMV
  refine isThreePrimeGroup_of_sylow inf_le_left hCvN hDM hD3 hD9 hDe ?_ hSyl
  exact le_bot_iff.mp (hDC ▸ inf_le_inf_left D (inf_le_right : M ⊓ Subgroup.centralizer
    (V154 T Mc M : Set G) ≤ Subgroup.centralizer (V154 T Mc M : Set G)))

end Setting

end CFSG.Quasithin.S15221
