module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34E16
public import CFSG.Quasithin.Vol2.Ch5Sec1L34InputsParChief
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem518D5T

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

section ChiefStep

variable {G : Type} [Group G]

theorem exists_noncentral_of_isChiefSeriesFrom {H U N : Subgroup G} {n : ℕ}
    (h : IsChiefSeriesFrom H U N n) (hn : 0 < n) :
    ∃ A B : Subgroup G, IsChiefStep H U B A ∧ ¬ IsCentralStep H B A := by
  induction h with
  | bot => exact absurd hn (lt_irrefl 0)
  | central _ _ _ ih => exact ih hn
  | @noncentral N L n hstep hnc _ _ => exact ⟨N, L, hstep, hnc⟩

end ChiefStep

section Image

variable {G : Type} [Group G] {K U : Subgroup G}

theorem isElemAbelian_imgO2_of
    (hcomm : ∀ x ∈ U, ∀ y ∈ U, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 K)
    (hsq : ∀ x ∈ U, x ^ 2 ∈ pCoreOf 2 K) : IsElemAbelian 2 (imgO2 K U) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a, ha, hax⟩ := x.2
    obtain ⟨b, hb, hby⟩ := y.2
    apply Subtype.ext
    show (x : O2Q K) * y = y * x
    rw [← hax, ← hby]
    have h2 : (QuotientGroup.mk (a * b * a⁻¹ * b⁻¹) : O2Q K) = 1 :=
      (mem_pCoreOf_iff_mk_eq_one (a * b * a⁻¹ * b⁻¹).2).mp (hcomm a ha b hb)
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv] at h2
    rw [← commutatorElement_eq_one_iff_mul_comm, commutatorElement_def]
    exact h2
  · obtain ⟨a, ha, rfl⟩ := hx
    have h2 : (QuotientGroup.mk (a ^ 2) : O2Q K) = 1 :=
      (mem_pCoreOf_iff_mk_eq_one (a ^ 2).2).mp (hsq a ha)
    rw [QuotientGroup.mk_pow] at h2
    exact h2

theorem card_imgO2_of [Finite G] (hOU : pCoreOf 2 K ≤ U) (hUK : U ≤ K)
    (hcard : Nat.card U = 16 * Nat.card (pCoreOf 2 K)) : Nat.card (imgO2 K U) = 16 := by
  have h := card_preimageModTwoCore K (imgO2 K U)
  rw [preimageModTwoCore_imgO2 hOU hUK, hcard] at h
  have hpos : 0 < Nat.card (pCoreOf 2 K) := Nat.card_pos
  exact (Nat.eq_of_mul_eq_mul_right hpos h).symm

theorem imgO2_inf_normalizer_eq (hOU : pCoreOf 2 K ≤ U) (hUK : U ≤ K) :
    imgO2 K (K ⊓ Subgroup.normalizer (U : Set G)) =
      Subgroup.normalizer ((imgO2 K U : Subgroup (O2Q K)) : Set (O2Q K)) := by
  have h := imgO2_inf_normalizer_preimage (K := K) (imgO2 K U)
  rwa [preimageModTwoCore_imgO2 hOU hUK] at h

end Image

section Parabolic

variable {G : Type} [Group G] [Finite G]

theorem three_le_of_parabolic {K U K₂ : Subgroup G} (hX : LieModel (O2Q K) .PSL 3 2 2)
    (hC : CharTwo K) (hOU : pCoreOf 2 K ≤ U) (hUK : U ≤ K)
    (hcomm : ∀ x ∈ U, ∀ y ∈ U, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 K)
    (hsq : ∀ x ∈ U, x ^ 2 ∈ pCoreOf 2 K) (hcard : Nat.card U = 16 * Nat.card (pCoreOf 2 K))
    (hK₂ : K₂ = oTwoUpper (K ⊓ Subgroup.normalizer (U : Set G)))
    (hIrr : ∀ A B : Subgroup G, IsChiefStep K (pCoreOf 2 K) B A → ¬ IsCentralStep K B A →
      ∀ m : ℕ, F112W.IsChiefSeriesBetween K₂ (pCoreOf 2 K₂) (⁅A, K₂⁆ ⊓ B) ⁅A, K₂⁆ m → 2 ≤ m)
    {n : ℕ} (hn : IsChiefSeriesFrom K₂ (pCoreOf 2 K₂) (pCoreOf 2 K₂) n) : 3 ≤ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOK : pCoreOf 2 K ≤ K := pCoreOf_le 2 K
  have hO2 : IsPGroup 2 (pCoreOf 2 K) := pCoreOf_isPGroup 2 K
  have hKO : K ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hK₂N₀ : K₂ ≤ K ⊓ Subgroup.normalizer (U : Set G) := by
    rw [hK₂]
    exact oTwoUpper_le _
  have hK₂K : K₂ ≤ K := hK₂N₀.trans inf_le_left
  have hK₂U : K₂ ≤ Subgroup.normalizer (U : Set G) := hK₂N₀.trans inf_le_right
  have hK₂O2 : K₂ ≤ oTwoUpper K := by
    rw [hK₂]
    exact oTwoUpper_mono inf_le_left
  have hK₂K₂ : oTwoUpper K₂ = K₂ := by
    rw [hK₂]
    exact D14.oTwoUpper_oTwoUpper _
  have hOK₂ : pCoreOf 2 K ≤ Subgroup.normalizer (K₂ : Set G) := by
    have h1 : pCoreOf 2 K ≤ K ⊓ Subgroup.normalizer (U : Set G) :=
      le_inf hOK (hOU.trans Subgroup.le_normalizer)
    refine h1.trans ?_
    rw [hK₂]
    exact le_normalizer_oTwoUpper _
  have hP₂K₂ : pCoreOf 2 K₂ ≤ K₂ := pCoreOf_le 2 K₂
  have hK₂P₂ : K₂ ≤ Subgroup.normalizer (pCoreOf 2 K₂ : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K₂
  have hU2 : IsPGroup 2 U := by
    obtain ⟨a, ha⟩ := hO2.exists_card_eq
    refine IsPGroup.of_card (n := a + 4) ?_
    rw [hcard, ha, pow_add]
    ring
  obtain ⟨S₀, -, hTP, s, hsS₀, hsC⟩ := exists_twoParRad_of_isElemAbelian hX
    (isElemAbelian_imgO2_of hcomm hsq) (card_imgO2_of hOU hUK hcard)
  have hK₂img : imgO2 K K₂ =
      Subgroup.normalizer ((imgO2 K U : Subgroup (O2Q K)) : Set (O2Q K)) := by
    rw [hK₂, imgO2_oTwoUpper inf_le_left, imgO2_inf_normalizer_eq hOU hUK]
    exact hTP.2.2.2.2.2.1
  have hsK₂ : s ∈ imgO2 K K₂ := by
    rw [hK₂img]
    exact hTP.2.1 (Subgroup.le_normalizer hsS₀)
  obtain ⟨k₀, hk₀, hk₀s⟩ := hsK₂
  have hk₀K₂ : (k₀ : G) ∈ K₂ := hk₀
  obtain ⟨r, hr, hrs⟩ : ∃ r ∈ imgO2 K U, r * s ≠ s * r := by
    by_contra hall
    push Not at hall
    exact hsC (Subgroup.mem_centralizer_iff.mpr hall)
  have hrK₂ : r ∈ imgO2 K K₂ := by
    rw [hK₂img]
    exact Subgroup.le_normalizer hr
  obtain ⟨k₁, hk₁, hk₁r⟩ := hrK₂
  have hk₁K₂ : (k₁ : G) ∈ K₂ := hk₁
  have e₁ : (QuotientGroup.mk k₁ : O2Q K) = r := hk₁r
  have e₀ : (QuotientGroup.mk k₀ : O2Q K) = s := hk₀s
  have hk₁U : (k₁ : G) ∈ U := by
    refine (mk_mem_imgO2_iff hOU k₁).mp ?_
    rw [e₁]
    exact hr
  have hUK₂P₂ : U ⊓ K₂ ≤ pCoreOf 2 K₂ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
      (F7.le_normalizer_inf hK₂U Subgroup.le_normalizer) (hU2.to_le inf_le_left)
  have hnot : ¬ ⁅pCoreOf 2 K₂, K₂⁆ ≤ pCoreOf 2 K := by
    intro hle
    have hc := hle (Subgroup.commutator_mem_commutator (hUK₂P₂ ⟨hk₁U, hk₁K₂⟩) hk₀K₂)
    have hx : ((k₁ * k₀ * k₁⁻¹ * k₀⁻¹ : ↥K) : G) ∈ pCoreOf 2 K := hc
    have h2 : (QuotientGroup.mk (k₁ * k₀ * k₁⁻¹ * k₀⁻¹) : O2Q K) = 1 :=
      (mem_pCoreOf_iff_mk_eq_one (k₁ * k₀ * k₁⁻¹ * k₀⁻¹).2).mp hx
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, e₁, e₀] at h2
    apply hrs
    rw [← commutatorElement_eq_one_iff_mul_comm, commutatorElement_def]
    exact h2
  have hOn : IsNormalIn K (pCoreOf 2 K) (pCoreOf 2 K) :=
    F112W.isNormalIn_of_le_normalizer le_rfl hKO
  obtain ⟨n₀, hn₀⟩ := D15Proof.exists_isChiefSeriesFrom (H := K) (U := pCoreOf 2 K) _ hOn
  have hn₀pos : 0 < n₀ := by
    rcases Nat.eq_zero_or_pos n₀ with h0 | h0
    · exfalso
      subst h0
      have hc := (F112W.isChiefSeriesFrom_zero_iff hOK le_rfl hOn).mp hn₀
      have hK₂O : K₂ ≤ pCoreOf 2 K := by
        intro k hk
        refine hC ⟨hK₂K hk, Subgroup.mem_centralizer_iff.mpr fun o ho => ?_⟩
        have h1 := Subgroup.commutator_mem_commutator ho (hK₂O2 hk)
        rw [hc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
        exact h1
      apply hsC
      have hs1 : s = 1 := by
        rw [← e₀]
        exact (mem_pCoreOf_iff_mk_eq_one k₀.2).mp (hK₂O hk₀K₂)
      rw [hs1]
      exact Subgroup.one_mem _
    · exact h0
  obtain ⟨A, B, hstep, hnc⟩ := exists_noncentral_of_isChiefSeriesFrom hn₀ hn₀pos
  have hAO : A ≤ pCoreOf 2 K := hstep.1.1
  have hKA : K ≤ Subgroup.normalizer (A : Set G) := D14.le_normalizer_of_isNormalIn hstep.1
  have hKB : K ≤ Subgroup.normalizer (B : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hQN : K₂ ≤ Subgroup.normalizer ((pCoreOf 2 K ⊓ K₂ : Subgroup G) : Set G) :=
    F7.le_normalizer_inf (hK₂K.trans hKO) Subgroup.le_normalizer
  have hQP₂ : pCoreOf 2 K ⊓ K₂ ≤ pCoreOf 2 K₂ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hQN (hO2.to_le inf_le_left)
  have hCA : ⁅A, K₂⁆ ≤ A := F112W.commutator_le_self_of_le_normalizer (hK₂K.trans hKA)
  have hCK₂ : ⁅A, K₂⁆ ≤ K₂ := by
    rw [Subgroup.commutator_comm]
    exact F112W.commutator_le_self_of_le_normalizer (hAO.trans hOK₂)
  have hCQ : ⁅A, K₂⁆ ≤ pCoreOf 2 K ⊓ K₂ := le_inf (hCA.trans hAO) hCK₂
  have hCN : K₂ ≤ Subgroup.normalizer ((⁅A, K₂⁆ : Subgroup G) : Set G) := fun g hg =>
    A4.mem_normalizer_commutator (hKA (hK₂K hg)) (Subgroup.le_normalizer hg)
  have hP₂n : IsNormalIn K₂ (pCoreOf 2 K₂) (pCoreOf 2 K₂) :=
    F112W.isNormalIn_of_le_normalizer le_rfl hK₂P₂
  have hQn : IsNormalIn K₂ (pCoreOf 2 K₂) (pCoreOf 2 K ⊓ K₂) :=
    F112W.isNormalIn_of_le_normalizer hQP₂ hQN
  have hCn : IsNormalIn K₂ (pCoreOf 2 K₂) ⁅A, K₂⁆ :=
    F112W.isNormalIn_of_le_normalizer (hCQ.trans hQP₂) hCN
  have hC'n : IsNormalIn K₂ (pCoreOf 2 K₂) (⁅A, K₂⁆ ⊓ B) :=
    F112W.isNormalIn_of_le_normalizer (inf_le_left.trans (hCQ.trans hQP₂))
      (F7.le_normalizer_inf hCN (hK₂K.trans hKB))
  obtain ⟨a, ha⟩ := F112W.exists_isChiefSeriesBetween hQn _ hP₂n hQP₂
  have hPa := F112W.eta_eq_add hP₂K₂ hQn ha
  have ha0 : a ≠ 0 := by
    rintro rfl
    have h1 := (F112W.isChiefSeriesBetween_zero_iff hP₂K₂ le_rfl hQn hP₂n hQP₂).mp ha
    rw [hK₂K₂] at h1
    exact hnot (h1.trans inf_le_left)
  obtain ⟨m, hm⟩ := F112W.exists_isChiefSeriesBetween hC'n _ hCn inf_le_left
  have hCm := F112W.eta_eq_add hP₂K₂ hC'n hm
  have hm2 := hIrr A B hstep hnc m hm
  have hCQeta := F112W.eta_le_of_le hP₂K₂ hCn hQn hCQ
  have hneta := (F112W.isChiefSeriesFrom_iff_eta hP₂K₂ hP₂n).mp hn
  omega

end Parabolic

theorem l34ParabolicChiefFact_of (hIrr : L34IrredParabolicFact) : L34ParabolicChiefFact :=
  fun G _ _ K U hX hC hOU hUK hcomm hsq hcard _ hn =>
    three_le_of_parabolic hX hC hOU hUK hcomm hsq hcard rfl
      (fun A B hAB hnc m hm => hIrr G K U A B hX hOU hUK hcomm hsq hcard hAB hnc m hm) hn

end CFSG.Quasithin.H13
