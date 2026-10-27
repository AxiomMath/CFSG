module

public import CFSG.Quasithin.Background.VolIE54
public import CFSG.Quasithin.Background.GoldschmidtE5TwoStab
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.RonanE51

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_of_forall_pow_mem {Y : Type*} [Group Y] [Finite Y] {N : Subgroup Y} [N.Normal]
    (hN : Group.IsSolvable ↥N) (h : ∀ y : Y, ∃ k : ℕ, y ^ 2 ^ k ∈ N) : Group.IsSolvable Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : IsPGroup 2 (Y ⧸ N) := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk⟩ := h y
    exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hk⟩
  have : Group.IsSolvable (Y ⧸ N) := by
    have := hq.isNilpotent
    infer_instance
  exact Group.isSolvable_of_subgroup_quotient N

theorem iSup_corank_eq_wGen {P Q : Subgroup G} {k : ℕ} (hQP : Q ≤ P) (hk : k < CFSG.Open.pRank 2 P) :
    (⨆ (B : Subgroup G) (_ : IsElemAbelianCorank P k B ∧ B ≤ Q), B) = E5.wGen k P Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · refine iSup₂_le fun B hB => E5.le_wGen ⟨hB.2, hB.1.2.1, fun B' hB'P hB' => ?_⟩
    calc Nat.card B' ≤ 2 ^ CFSG.Open.pRank 2 P := VolI.E54.card_le_two_pow_pRank_of_le hB'P hB'
      _ = 2 ^ k * Nat.card B := by rw [← hB.1.2.2, mul_comm]
  · refine iSup₂_le fun A hA => ?_
    intro a ha
    obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian P
    have hA₀c := (isMaxElemAbelian_iff_corank_zero.mp hA₀).2.2
    rw [pow_zero, mul_one] at hA₀c
    have hAc : 2 ^ CFSG.Open.pRank 2 P ≤ 2 ^ k * Nat.card A := hA₀c ▸ hA.2.2 A₀ hA₀.1 hA₀.2.1
    obtain ⟨c, hc⟩ := (IsPGroup.iff_card (p := 2)).mp (B2F.isPGroup_of_isElemAbelian hA.2.1)
    have hkm : CFSG.Open.pRank 2 P - k ≤ c := by
      rw [hc, ← pow_add] at hAc
      have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hAc
      omega
    have hdvd : 2 ^ (CFSG.Open.pRank 2 P - k) ∣ Nat.card A := by
      rw [hc]
      exact pow_dvd_pow 2 hkm
    have hza : Nat.card (Subgroup.zpowers a) ∣ 2 ^ (CFSG.Open.pRank 2 P - k) := by
      rw [Nat.card_zpowers]
      have h2 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (hA.2.1.2 a ha)
      exact h2.trans (dvd_pow_self 2 (by omega))
    obtain ⟨K, hKc, haK, hKA⟩ :=
      Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two hza hdvd
        (Subgroup.zpowers_le.mpr ha)
    have hK : IsElemAbelianCorank P k K :=
      ⟨(hKA.trans hA.1).trans hQP, B2F.isElemAbelian_mono hKA hA.2.1, by
        rw [hKc, ← pow_add, Nat.sub_add_cancel hk.le]⟩
    exact le_iSup₂_of_le (f := fun K (_ : IsElemAbelianCorank P k K ∧ K ≤ Q) => K) K
      ⟨hK, hKA.trans hA.1⟩ le_rfl (haK (Subgroup.mem_zpowers a))

theorem le_thompsonJk_of_corank {P A : Subgroup G} {i n : ℕ} (hin : i ≤ n)
    (hA : IsElemAbelianCorank P i A) : A ≤ H13.thompsonJk n P :=
  E5.le_thompsonJk hA.1 hA.2.1 fun B hBP hB =>
    calc Nat.card B ≤ 2 ^ CFSG.Open.pRank 2 P := VolI.E54.card_le_two_pow_pRank_of_le hBP hB
      _ = 2 ^ i * Nat.card A := by rw [← hA.2.2, mul_comm]
      _ ≤ 2 ^ n * Nat.card A := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hin)

theorem inf_mem_wFam {P Q A : Subgroup G} {i j : ℕ} (hA : IsElemAbelianCorank P i A)
    (hAQ : Nat.card A ≤ 2 ^ j * Nat.card ↥(A ⊓ Q)) : A ⊓ Q ∈ E5.wFam (i + j) P Q := by
  refine ⟨inf_le_right, B2F.isElemAbelian_mono inf_le_left hA.2.1, fun B hBP hB => ?_⟩
  calc Nat.card B ≤ 2 ^ CFSG.Open.pRank 2 P := VolI.E54.card_le_two_pow_pRank_of_le hBP hB
    _ = Nat.card A * 2 ^ i := hA.2.2.symm
    _ ≤ (2 ^ j * Nat.card ↥(A ⊓ Q)) * 2 ^ i := Nat.mul_le_mul_right _ hAQ
    _ = 2 ^ (i + j) * Nat.card ↥(A ⊓ Q) := by rw [pow_add]; ring

theorem le_wGen_of_commute {k : ℕ} {P Q A₁ V : Subgroup G} (hA₁ : A₁ ∈ E5.wFam k P Q)
    (hV : IsElemAbelian 2 V) (hVQ : V ≤ Q) (hcomm : ∀ v ∈ V, ∀ a ∈ A₁, v * a = a * v) :
    V ≤ E5.wGen k P Q := by
  have hsup : IsElemAbelian 2 (V ⊔ A₁) := B2F.isElemAbelian_sup_of_commute hV hA₁.2.1 hcomm
  have hmem : V ⊔ A₁ ∈ E5.wFam k P Q :=
    ⟨sup_le hVQ hA₁.1, hsup, fun B' hB'P hB' =>
      (hA₁.2.2 B' hB'P hB').trans (Nat.mul_le_mul_left _ (Subgroup.card_le_of_le le_sup_right))⟩
  exact le_sup_left.trans (E5.le_wGen hmem)

theorem omegaOneCenter_le_of_tau {P A K : Subgroup G} {n : ℕ} (hAJ : A ≤ H13.thompsonJk n P)
    (hτ : E1.tauOf ⊤ P A ≤ P ⊓ K) : omegaOneCenterOf (H13.thompsonJk n P) ≤ K := by
  intro d hd
  have hdP : d ∈ P := E5.thompsonJk_le n P (omegaOneCenterOf_le _ hd)
  have hτd : d ∈ E1.tauOf ⊤ P A := by
    refine (E1.mem_tauOf_of_le le_top).2 ⟨hdP, fun a ha => ?_⟩
    have h1 : a * d = d * a := mem_centralizer_of_mem_omegaOneCenterOf hd (hAJ ha)
    have h2 : ⁅d, a⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 h1.symm
    rw [h2]
    exact Subgroup.one_mem _
  exact (hτ hτd).2

theorem pCoreOf_le_of_isSylow {P K : Subgroup G} (hPK : IsSylowIn 2 (P ⊓ K) K) :
    pCoreOf 2 K ≤ P := by
  have hKQ : K ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hQK : pCoreOf 2 K ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  have hQ2 : IsPGroup 2 (pCoreOf 2 K) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  exact (hPK.le_of_normal hQK ((Subgroup.normal_subgroupOf_iff_le_normalizer hQK).2 hKQ)
    hQ2).trans inf_le_left

theorem stabilizer_facts {K Q W D : Subgroup G} (hKQ : K ≤ Subgroup.normalizer (Q : Set G))
    (hKW : K ≤ Subgroup.normalizer (W : Set G)) (hWQ : W ≤ Q) (hQ2 : IsPGroup 2 Q)
    (hDK : D ≤ K) (hDW : D ≤ Subgroup.centralizer (W : Set G))
    (hQD : Q ≤ Subgroup.normalizer (D : Set G)) (hDQW : D ⊓ Q ≤ W) :
    D ≤ K ⊓ Subgroup.centralizer (W : Set G) ⊓ E5.quotStab Q W ∧
    K ≤ Subgroup.normalizer
      ((K ⊓ Subgroup.centralizer (W : Set G) ⊓ E5.quotStab Q W : Subgroup G) : Set G) ∧
    twoResidual (K ⊓ Subgroup.centralizer (W : Set G) ⊓ E5.quotStab Q W) ≤
      Subgroup.centralizer (Q : Set G) := by
  refine ⟨fun d hd => ⟨⟨hDK hd, hDW hd⟩, hKW (hDK hd), fun q hq => ?_⟩,
    E5.le_normalizer_stabilizer hKQ hKW, E5.twoResidual_stabilizer_le hWQ hQ2 hKQ⟩
  have h1 : ⁅d, q⁆ ∈ D := by
    have : q * d⁻¹ * q⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.1 (hQD hq) _).1 (D.inv_mem hd)
    have e : ⁅d, q⁆ = d * (q * d⁻¹ * q⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact D.mul_mem hd this
  have h2 : ⁅d, q⁆ ∈ Q := by
    have : d * q * d⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 (hKQ (hDK hd)) q).1 hq
    have e : ⁅d, q⁆ = (d * q * d⁻¹) * q⁻¹ := by
      simp only [commutatorElement_def]
    rw [e]
    exact Q.mul_mem this (Q.inv_mem hq)
  exact hDQW ⟨h1, h2⟩

theorem card_le_two_pow_mul_card_inf {P Q A D : Subgroup G} {i j : ℕ}
    (hA : IsElemAbelianCorank P i A) (hAQ : Nat.card A ≤ 2 ^ j * Nat.card ↥(A ⊓ Q))
    (hD : IsElemAbelian 2 D) (hDP : D ≤ P) (hDA : ∀ d ∈ D, ∀ a ∈ A, d * a = a * d) :
    Nat.card D ≤ 2 ^ (i + j) * Nat.card ↥(D ⊓ Q) := by
  have hDAe : IsElemAbelian 2 (D ⊔ A) := B2F.isElemAbelian_sup_of_commute hD hA.2.1 hDA
  have hcard : Nat.card ↥(D ⊔ A) ≤ 2 ^ CFSG.Open.pRank 2 P :=
    VolI.E54.card_le_two_pow_pRank_of_le (sup_le hDP hA.1) hDAe
  have hprod := B2F.card_sup_mul_card_inf_of_commute hDA
  have hApos : 0 < Nat.card A := Nat.card_pos
  have h1 : Nat.card D ≤ 2 ^ i * Nat.card ↥(D ⊓ A) := by
    have h2 : Nat.card D * Nat.card A ≤ (2 ^ i * Nat.card ↥(D ⊓ A)) * Nat.card A := by
      rw [← hprod]
      calc Nat.card ↥(D ⊔ A) * Nat.card ↥(D ⊓ A)
          ≤ 2 ^ CFSG.Open.pRank 2 P * Nat.card ↥(D ⊓ A) := Nat.mul_le_mul_right _ hcard
        _ = (Nat.card A * 2 ^ i) * Nat.card ↥(D ⊓ A) := by rw [hA.2.2]
        _ = (2 ^ i * Nat.card ↥(D ⊓ A)) * Nat.card A := by ring
    exact Nat.le_of_mul_le_mul_right h2 hApos
  have hrel : Q.relIndex A ≤ 2 ^ j := by
    have h3 := Subgroup.relIndex_mul_card Q A
    have hQA : Q ⊓ A = A ⊓ Q := inf_comm Q A
    have h4 : Q.relIndex A * Nat.card ↥(Q ⊓ A) ≤ 2 ^ j * Nat.card ↥(Q ⊓ A) := by
      rw [h3, hQA]; exact hAQ
    exact Nat.le_of_mul_le_mul_right h4 Nat.card_pos
  have hX : Nat.card ↥(D ⊓ A) ≤ 2 ^ j * Nat.card ↥(D ⊓ Q) := by
    have h5 : Q.relIndex (D ⊓ A) ≤ Q.relIndex A :=
      Subgroup.relIndex_le_of_le_right inf_le_right (E3.relIndex_ne_zero' _ _)
    have h6 := Subgroup.relIndex_mul_card Q (D ⊓ A)
    have h7 : Nat.card ↥(Q ⊓ (D ⊓ A)) ≤ Nat.card ↥(D ⊓ Q) :=
      Subgroup.card_le_of_le (fun x hx => ⟨hx.2.1, hx.1⟩)
    calc Nat.card ↥(D ⊓ A) = Q.relIndex (D ⊓ A) * Nat.card ↥(Q ⊓ (D ⊓ A)) := h6.symm
      _ ≤ 2 ^ j * Nat.card ↥(D ⊓ Q) := Nat.mul_le_mul (h5.trans hrel) h7
  calc Nat.card D ≤ 2 ^ i * Nat.card ↥(D ⊓ A) := h1
    _ ≤ 2 ^ i * (2 ^ j * Nat.card ↥(D ⊓ Q)) := Nat.mul_le_mul_left _ hX
    _ = 2 ^ (i + j) * Nat.card ↥(D ⊓ Q) := by rw [pow_add]; ring

end CFSG.Quasithin.RonanE51
