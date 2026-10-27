module

public import CFSG.LocalAnalysis.UniquenessCase.UC6N588B9
public import CFSG.LocalAnalysis.UniquenessCase.UC6N588B8

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Perm
open CFSG.LocalAnalysis.UniquenessCase.UC6.A10N588
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

theorem add_le_pRank_uc6b {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {E₁ E₂ H : Subgroup G} (hE₁ : IsElemAbelian p E₁) (hE₂ : IsElemAbelian p E₂) {r₁ r₂ : ℕ}
    (h₁ : Nat.card E₁ = p ^ r₁) (h₂ : Nat.card E₂ = p ^ r₂)
    (hc : ∀ x ∈ E₁, ∀ y ∈ E₂, x * y = y * x) (hdisj : E₁ ⊓ E₂ = ⊥) (hH : E₁ ⊔ E₂ ≤ H) :
    r₁ + r₂ ≤ CFSG.Open.pRank p H :=
  le_pRank_of_elemAbelian hp hH (hE₁.sup_of_commute hE₂ hc)
    (by rw [card_sup_of_commute_of_disjoint hc hdisj, h₁, h₂, pow_add])

@[expose] def kleinSub : Subgroup A10 where
  carrier := {x | ∃ i j : ℕ, x = v₁ ^ i * v₂ ^ j}
  mul_mem' := by
    rintro _ _ ⟨i, j, rfl⟩ ⟨k, l, rfl⟩
    refine ⟨i + k, j + l, ?_⟩
    have h : v₂ ^ j * v₁ ^ k = v₁ ^ k * v₂ ^ j :=
      (Commute.pow_pow (show Commute v₁ v₂ from v₁₂_comm).symm j k).eq
    calc v₁ ^ i * v₂ ^ j * (v₁ ^ k * v₂ ^ l) = v₁ ^ i * (v₂ ^ j * v₁ ^ k) * v₂ ^ l := by
          simp only [mul_assoc]
      _ = v₁ ^ (i + k) * v₂ ^ (j + l) := by rw [h]; simp only [pow_add, mul_assoc]
  one_mem' := ⟨0, 0, by simp⟩
  inv_mem' := by
    rintro _ ⟨i, j, rfl⟩
    refine ⟨i, j, ?_⟩
    have h1 : v₁⁻¹ = v₁ := inv_eq_of_mul_eq_one_left (by rw [← sq, v₁_sq])
    have h2 : v₂⁻¹ = v₂ := inv_eq_of_mul_eq_one_left (by rw [← sq, v₂_sq])
    rw [mul_inv_rev, ← inv_pow, ← inv_pow, h1, h2]
    exact ((Commute.pow_pow (show Commute v₁ v₂ from v₁₂_comm) i j)).symm.eq

theorem isPGroup_kleinSub : IsPGroup 2 kleinSub := by
  rintro ⟨_, i, j, rfl⟩
  refine ⟨1, Subtype.ext ?_⟩
  show (v₁ ^ i * v₂ ^ j) ^ 2 ^ 1 = 1
  rw [pow_one, (Commute.pow_pow (show Commute v₁ v₂ from v₁₂_comm) i j).mul_pow, ← pow_mul,
    ← pow_mul, mul_comm i 2, mul_comm j 2, pow_mul, pow_mul, v₁_sq, v₂_sq, one_pow, one_pow,
    one_mul]

theorem kleinSub_ne_bot : kleinSub ≠ ⊥ := by
  intro h
  have : v₁ ∈ kleinSub := ⟨1, 0, by simp⟩
  rw [h, mem_bot] at this
  exact v₁_ne this

theorem kleinSub_le : kleinSub ≤ altA T4 := by
  rintro _ ⟨i, j, rfl⟩
  exact (altA T4).mul_mem ((altA T4).pow_mem v₁_mem_T4 i) ((altA T4).pow_mem v₂_mem_T4 j)

theorem x₃_normalizes_kleinSub : ∀ v ∈ kleinSub, x₃ * v * x₃⁻¹ ∈ kleinSub := by
  rintro _ ⟨i, j, rfl⟩
  refine ⟨i + j, i, ?_⟩
  have e : x₃ * (v₁ ^ i * v₂ ^ j) * x₃⁻¹ = (x₃ * v₁ * x₃⁻¹) ^ i * (x₃ * v₂ * x₃⁻¹) ^ j := by
    rw [conj_pow, conj_pow]
    group
  rw [e, x₃_v₁, x₃_v₂, (show Commute v₁ v₂ from v₁₂_comm).mul_pow, pow_add]
  have h : v₂ ^ i * v₁ ^ j = v₁ ^ j * v₂ ^ i :=
    (Commute.pow_pow (show Commute v₁ v₂ from v₁₂_comm).symm i j).eq
  calc v₁ ^ i * v₂ ^ i * v₁ ^ j = v₁ ^ i * (v₂ ^ i * v₁ ^ j) := by rw [mul_assoc]
    _ = v₁ ^ i * v₁ ^ j * v₂ ^ i := by rw [h, mul_assoc]

namespace Mz614

variable {G : Type} [Group G] [Finite G] {m : Mz614 G}

theorem mem_M_of_normalizes (h620 : m.C620) {Y : Subgroup G} (hY : Y ≤ m.A ⊓ m.L) (hY1 : Y ≠ ⊥)
    {n : G} (hnL : n ∈ m.L) (hn : n ∈ normalizer (Y : Set G)) : n ∈ m.M := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  set S := Y ⊔ m.Z with hS
  have hYA : Y ≤ m.A := hY.trans inf_le_left
  have hcomm : ∀ x ∈ Y, ∀ z ∈ m.Z, x * z = z * x := fun x hx z hz =>
    congrArg Subtype.val (m.isElemAbelian_A.1.is_comm.comm ⟨x, hYA hx⟩ ⟨z, m.Z_le_A hz⟩)
  have hYZ : Y ⊓ m.Z = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : x ∈ m.Z ⊓ m.L := ⟨hx.2, (hY hx.1).2⟩
    rwa [inf_eq_bot_of_not_le_of_card_prime m.hr m.card_Z h620.2] at h1
  have hSA : S ≤ m.A := sup_le hYA m.Z_le_A
  have hSp : IsPGroup m.r S := m.d.sylow.isPGroup.to_le (hSA.trans m.A_le_R)
  have hYcard : m.r ≤ Nat.card Y := by
    have hYp : IsPGroup m.r Y := hSp.to_le le_sup_left
    obtain ⟨k, hk⟩ := hYp.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hY1 (Subgroup.eq_bot_of_card_eq Y (by simpa using hk))
    rw [hk]
    calc m.r = m.r ^ 1 := (pow_one _).symm
      _ ≤ m.r ^ k := Nat.pow_le_pow_right m.hr.pos (Nat.one_le_iff_ne_zero.2 hk0)
  have hScard : m.r ^ 2 ≤ Nat.card S := by
    rw [hS, card_sup_of_commute_of_disjoint hcomm hYZ, m.card_Z, sq]
    exact Nat.mul_le_mul_right _ hYcard
  have hX1 : m.E ⊓ S ≠ ⊥ := by
    intro hbot
    have hcES : ∀ x ∈ m.E, ∀ y ∈ S, x * y = y * x := fun x hx y hy =>
      congrArg Subtype.val (m.isElemAbelian_A.1.is_comm.comm ⟨x, m.E_le_A hx⟩ ⟨y, hSA hy⟩)
    have h1 := card_sup_of_commute_of_disjoint hcES hbot
    have h2 : Nat.card ↥(m.E ⊔ S) ≤ Nat.card m.A := Subgroup.card_le_of_le (sup_le m.E_le_A hSA)
    rw [h1, m.d.E_card, m.card_A] at h2
    have h3 : m.r ^ 2 * m.r ^ 2 ≤ m.r ^ 2 * Nat.card S := Nat.mul_le_mul_left _ hScard
    have h4 : m.r ^ 3 < m.r ^ 4 := Nat.pow_lt_pow_right m.hr.one_lt (by norm_num)
    have h5 : m.r ^ 2 * m.r ^ 2 = m.r ^ 4 := by ring
    omega
  have hNS : normalizer (S : Set G) ≤ m.M :=
    m.d.normalizer_le_of_le_pGroup m.hC inf_le_left hX1 inf_le_right hSp
  apply hNS
  refine mem_normalizer_of_forward_uc6 fun s hs => ?_
  obtain ⟨y, hy, z, hz, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hs
  have hnz : n * z * n⁻¹ = z := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (m.Z_comm_L hz hnL).symm
  have e : n * (y * z) * n⁻¹ = (n * y * n⁻¹) * (n * z * n⁻¹) := by group
  rw [e, hnz]
  exact S.mul_mem (mem_sup_left ((mem_normalizer_iff.1 hn y).1 hy)) (mem_sup_right hz)

namespace A10Setup

variable (D : A10Setup m)

theorem ι_t₀_mem_M (h620 : m.C620) : D.ι t₀ ∈ m.M := by
  have hY : line₂.map D.ι ≤ m.A ⊓ m.L := D.map_ι_line_le line₂_le
  have hY1 : line₂.map D.ι ≠ ⊥ := by
    intro h
    have := D.card_map_ι line₂
    rw [h, Subgroup.card_bot, card_line₂] at this
    norm_num at this
  refine mem_M_of_normalizes h620 hY hY1 (D.ι_mem_L t₀) (mem_normalizer_of_forward_uc6 ?_)
  rintro _ ⟨σ, hσ, rfl⟩
  have hσ' : σ ∈ zpowers a₂ := line₂_eq ▸ hσ
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hσ'
  refine ⟨t₀ * a₂ ^ k * t₀⁻¹, ?_, by simp⟩
  have : t₀ * a₂ ^ k * t₀⁻¹ = a₂ ^ k := by
    rw [(Commute.zpow_right (show Commute t₀ a₂ from t₀_a₂) k).eq, mul_inv_cancel_right]
  rw [this, line₂_eq]
  exact zpow_mem_zpowers a₂ k

include D in
theorem three_not_mem_sigma (h619 : m.C619) (h620 : m.C620) : 3 ∉ uniqueFourSigma m.M := by
  intro h3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSE : IsStronglyPEmbedded 3 m.M :=
    isStronglyPEmbedded_of_sigmaOne m.hU m.S.maxLocal h3 (m.hσ1 h3)
  have hcent : ∀ τ : A10, (τ : Equiv.Perm (Fin 10)).IsThreeCycle → D.ι τ ∈ m.M →
      centralizer ({D.ι τ} : Set G) ≤ m.M := by
    intro τ hτ hτM
    have hτ1 : D.ι τ ≠ 1 := fun h => by
      have : τ = 1 := D.ι_injective (h.trans (map_one _).symm)
      rw [this] at hτ
      exact hτ.ne_one rfl
    have hτ3 : D.ι τ ^ 3 = 1 := by
      rw [← map_pow]
      have hτo : orderOf (τ : Equiv.Perm (Fin 10)) = 3 := hτ.orderOf
      have h' : ((τ ^ 3 : A10) : Equiv.Perm (Fin 10)) = 1 := by
        rw [Subgroup.coe_pow, ← hτo, pow_orderOf_eq_one]
      have : τ ^ 3 = 1 := Subtype.ext h'
      rw [this, map_one]
    exact hSE.centralizer_le hτ1 hτ3 hτM
  have hcomm_mem : ∀ σ τ : A10, σ * τ = τ * σ → (τ : Equiv.Perm (Fin 10)).IsThreeCycle →
      D.ι τ ∈ m.M → D.ι σ ∈ m.M := by
    intro σ τ hστ hτ hτM
    apply hcent τ hτ hτM
    rw [mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff.1 hx, ← map_mul, ← map_mul, hστ]
  have ht₀3 : (t₀ : Equiv.Perm (Fin 10)).IsThreeCycle := t₀_isThreeCycle
  have ht₀M := D.ι_t₀_mem_M h620
  have hall : ∀ σ : A10, (σ : Equiv.Perm (Fin 10)).IsThreeCycle → σ ∈ m.M.comap D.ι := by
    intro σ hσ
    obtain ⟨τ, hτ, hτT, hdis⟩ := exists_isThreeCycle_disjoint hσ
    set τ' : A10 := ⟨τ, hτ.mem_alternatingGroup⟩ with hτ'
    have hτ'M : D.ι τ' ∈ m.M := hcomm_mem τ' t₀ (Subtype.ext (commute_t₀ hτT)) ht₀3 ht₀M
    exact hcomm_mem σ τ' (commute_of_disjoint_support hdis) hτ hτ'M
  have htop := eq_top_of_threeCycles hall
  apply m.L_not_le_M h619
  intro x hx
  obtain ⟨σ, rfl⟩ := D.exists_ι hx
  have : σ ∈ m.M.comap D.ι := htop ▸ mem_top σ
  exact this

include D in
theorem three_dvd_card : 3 ∣ Nat.card G := by
  have h1 : orderOf (D.ι t₀) = 3 := by
    have h3 : D.ι t₀ ^ 3 = 1 := by rw [← map_pow, t₀_pow, map_one]
    have h1 : D.ι t₀ ≠ 1 := fun h => t₀_ne (D.ι_injective (h.trans (map_one _).symm))
    exact orderOf_eq_prime h3 h1
  rw [← h1]
  exact orderOf_dvd_natCard _

include D in
theorem three_not_mem_beta (h619 : m.C619) (h620 : m.C620) : 3 ∉ uniqueFourBeta G := by
  intro h3
  have hp : m.S.p = 3 := m.hMS.1 h3
  have := m.S.hp
  rw [hp] at this
  exact D.three_not_mem_sigma h619 h620 this

include D in
theorem twoLocalPrimeRank_three_le (h619 : m.C619) (h620 : m.C620) :
    CFSG.Open.twoLocalPrimeRank 3 G ≤ 3 := by
  by_contra h
  push Not at h
  exact D.three_not_mem_beta h619 h620 ⟨Nat.prime_three, by norm_num, D.three_dvd_card, h⟩

@[expose] noncomputable def Xa : Subgroup G := (altA T4).map D.ι

@[expose] noncomputable def Ka : Subgroup G := centralizer (D.Xa : Set G)

theorem ι_mem_Ka_iff (σ : A10) : D.ι σ ∈ D.Ka ↔ σ ∈ altA T6 := by
  rw [← mem_altA_T6_iff, Ka, mem_centralizer_iff]
  constructor
  · intro h x hx
    apply D.ι_injective
    rw [map_mul, map_mul]
    exact h _ ⟨x, hx, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, h x hx]

theorem mem_Ka_iff {g : G} : g ∈ D.Ka ↔ ∀ σ ∈ altA T4, D.ι σ * g = g * D.ι σ := by
  rw [Ka, mem_centralizer_iff]
  constructor
  · intro h σ hσ
    exact h _ ⟨σ, hσ, rfl⟩
  · rintro h _ ⟨σ, hσ, rfl⟩
    exact h σ hσ

theorem centralizer_L_le_Ka : centralizer (m.L : Set G) ≤ D.Ka := by
  intro c hc
  rw [mem_Ka_iff]
  intro σ _
  exact mem_centralizer_iff.1 hc _ (D.ι_mem_L σ)

theorem Z_le_Ka : m.Z ≤ D.Ka := by
  intro z hz
  rw [Ka, mem_centralizer_iff]
  rintro _ ⟨σ, -, rfl⟩
  exact (m.Z_comm_L hz (D.ι_mem_L σ)).symm

theorem Ka_inf_Xa : D.Ka ⊓ D.Xa = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨hK, ⟨σ, hσ, rfl⟩⟩
  have h6 := (D.ι_mem_Ka_iff σ).1 hK
  have : σ ∈ altA T6 ⊓ altA T4 := ⟨h6, hσ⟩
  rw [altA_inf_eq_bot T6_T4, mem_bot] at this
  rw [this, map_one]
  exact one_mem _

theorem kleinSub_facts :
    (kleinSub.map D.ι ≠ ⊥ ∧ IsPGroup 2 (kleinSub.map D.ι)) ∧
      D.Ka ≤ normalizer ((kleinSub.map D.ι : Subgroup G) : Set G) ∧
      D.ι x₃ ∈ normalizer ((kleinSub.map D.ι : Subgroup G) : Set G) := by
  refine ⟨⟨fun h => kleinSub_ne_bot ?_, isPGroup_kleinSub.map D.ι⟩, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro v hv
    have : D.ι v ∈ kleinSub.map D.ι := ⟨v, hv, rfl⟩
    rw [h, mem_bot] at this
    rw [mem_bot]
    exact D.ι_injective (this.trans (map_one _).symm)
  · intro k hk
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [mem_centralizer_iff]
    rintro _ ⟨v, hv, rfl⟩
    exact (mem_centralizer_iff.1 hk _ ⟨v, kleinSub_le hv, rfl⟩)
  · refine mem_normalizer_of_forward_uc6 ?_
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨x₃ * v * x₃⁻¹, x₃_normalizes_kleinSub v hv, ?_⟩
    simp

theorem pRank_Ka (h619 : m.C619) (h620 : m.C620) : CFSG.Open.pRank 3 D.Ka = 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : ∀ τ : A10, τ ^ 3 = 1 → τ ≠ 1 →
      IsElemAbelian 3 (zpowers (D.ι τ)) ∧ Nat.card (zpowers (D.ι τ)) = 3 ^ 1 := by
    intro τ h3 h1
    have hι1 : D.ι τ ≠ 1 := fun h => h1 (D.ι_injective (h.trans (map_one _).symm))
    have hι3 : D.ι τ ^ 3 = 1 := by rw [← map_pow, h3, map_one]
    have hcard : Nat.card (zpowers (D.ι τ)) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hι3 hι1]
    exact ⟨isElemAbelian_of_card_prime Nat.prime_three hcard, by rw [hcard, pow_one]⟩
  apply le_antisymm
  ·
    obtain ⟨P, hPK, hPel, hPcard⟩ :=
      CFSG.PreuniquenessRankFour.Helpers.pRank_attained 3 Nat.prime_three D.Ka
    obtain ⟨hE, hEcard⟩ := hcyc x₃ x₃_pow x₃_ne
    obtain ⟨⟨hV1, hV2⟩, hVK, hVx⟩ := D.kleinSub_facts
    have hx₃X : D.ι x₃ ∈ D.Xa := ⟨x₃, x₃_mem_T4, rfl⟩
    have hc : ∀ x ∈ P, ∀ y ∈ zpowers (D.ι x₃), x * y = y * x := by
      intro x hx y hy
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
      have h1 : x * D.ι x₃ = D.ι x₃ * x := (mem_centralizer_iff.1 (hPK hx) _ hx₃X).symm
      exact (Commute.zpow_right (show Commute x (D.ι x₃) from h1) k).eq
    have hdisj : P ⊓ zpowers (D.ι x₃) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have h1 : x ∈ D.Ka ⊓ D.Xa := ⟨hPK hx.1, (Subgroup.zpowers_le.2 hx₃X) hx.2⟩
      rwa [D.Ka_inf_Xa] at h1
    have hle : P ⊔ zpowers (D.ι x₃) ≤ normalizer ((kleinSub.map D.ι : Subgroup G) : Set G) :=
      sup_le (hPK.trans hVK) ((Subgroup.zpowers_le).2 hVx)
    have h1 := add_le_pRank_uc6b Nat.prime_three hPel hE hPcard hEcard hc hdisj hle
    have hloc : IsTwoLocal (normalizer ((kleinSub.map D.ι : Subgroup G) : Set G)) :=
      ⟨_, hV1, hV2, rfl⟩
    have h2 : CFSG.Open.pRank 3 (normalizer ((kleinSub.map D.ι : Subgroup G) : Set G)) ≤
        CFSG.Open.twoLocalPrimeRank 3 G :=
      le_csSup (CFSG.PreuniquenessRankFour.Helpers.twoLocalRank_bddAbove 3 Nat.prime_three)
        ⟨_, hloc, rfl⟩
    have h3 := D.twoLocalPrimeRank_three_le h619 h620
    omega
  ·
    obtain ⟨hE₀, hE₀c⟩ := hcyc t₀ t₀_pow t₀_ne
    obtain ⟨hE₁, hE₁c⟩ := hcyc t₁ t₁_pow t₁_ne
    have hc : ∀ x ∈ zpowers (D.ι t₀), ∀ y ∈ zpowers (D.ι t₁), x * y = y * x := by
      intro x hx y hy
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
      obtain ⟨l, rfl⟩ := mem_zpowers_iff.1 hy
      have h1 : D.ι t₀ * D.ι t₁ = D.ι t₁ * D.ι t₀ := by rw [← map_mul, ← map_mul, t₀₁_comm]
      exact (Commute.zpow_zpow (show Commute (D.ι t₀) (D.ι t₁) from h1) k l).eq
    have hdisj : zpowers (D.ι t₀) ⊓ zpowers (D.ι t₁) = ⊥ := by
      by_contra hne
      have hle : zpowers (D.ι t₀) ⊓ zpowers (D.ι t₁) ≤ zpowers (D.ι t₁) := inf_le_right
      have hcard1 := hE₁c
      rw [pow_one] at hcard1
      have heq : zpowers (D.ι t₀) ⊓ zpowers (D.ι t₁) = zpowers (D.ι t₁) := by
        have hdvd := Subgroup.card_dvd_of_le hle
        rw [hcard1] at hdvd
        rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
        · exact absurd (Subgroup.eq_bot_of_card_eq _ h) hne
        · exact Subgroup.eq_of_le_of_card_ge hle (by rw [h, hcard1])
      have hmem : D.ι t₁ ∈ zpowers (D.ι t₀) := by
        have h1 : D.ι t₁ ∈ zpowers (D.ι t₀) ⊓ zpowers (D.ι t₁) := by
          rw [heq]
          exact mem_zpowers _
        exact h1.1
      rw [← MonoidHom.map_zpowers] at hmem
      obtain ⟨σ, hσ, hσt⟩ := hmem
      have hσ' : σ = t₁ := D.ι_injective hσt
      rw [hσ'] at hσ
      obtain ⟨n, hn⟩ := mem_zpowers_nat.1 hσ
      rw [pow_eq_pow_mod n t₀_pow] at hn
      exact t₁_not_pow ⟨n % 3, Nat.mod_lt _ (by norm_num)⟩ hn
    have hle : zpowers (D.ι t₀) ⊔ zpowers (D.ι t₁) ≤ D.Ka :=
      sup_le ((Subgroup.zpowers_le).2 ((D.ι_mem_Ka_iff t₀).2 t₀_mem_T6))
        ((Subgroup.zpowers_le).2 ((D.ι_mem_Ka_iff t₁).2 t₁_mem_T6))
    have := add_le_pRank_uc6b Nat.prime_three hE₀ hE₁ hE₀c hE₁c hc hdisj hle
    omega

end A10Setup

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6
