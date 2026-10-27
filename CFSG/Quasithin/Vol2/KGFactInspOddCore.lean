module

public import CFSG.Quasithin.Vol2.KGFactInspModelL
public import CFSG.Quasithin.Vol2.KGFactInspSL2Odd
public import CFSG.Quasithin.Vol2.KGFactL3EvenConf
public import CFSG.Quasithin.Vol2.KGFactInspPerf

public section

namespace CFSG.Quasithin.H13.KGInspOdd

open Subgroup
open CFSG.Open (pCoreOf IsElemAbelian)
open CFSG.Quasithin.H13.KGL3Even (LConf)
open scoped MatrixGroups commutatorElement

theorem exists_noncomm_of_perfect {G : Type*} [Group G] {K : Subgroup G} (hK : ⁅K, K⁆ = K)
    (hK1 : K ≠ ⊥) : ∃ a ∈ K, ∃ b ∈ K, a * b ≠ b * a := by
  by_contra h
  push Not at h
  apply hK1
  rw [← hK, eq_bot_iff, Subgroup.commutator_le]
  intro a ha b hb
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact h a ha b hb

theorem card_sl2 {F : Type*} [Field F] [Finite F] :
    Nat.card SL(2, F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num)]
  simp

theorem eq_five_of_mul {q : ℕ} (h : q * (q ^ 2 - 1) = 120) : q = 5 := by
  have hq : q < 6 := by
    by_contra hq
    push Not at hq
    have h1 : 35 ≤ q ^ 2 - 1 := by
      have : 36 ≤ q ^ 2 := by nlinarith
      omega
    have : 6 * 35 ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul hq h1
    omega
  interval_cases q <;> first | rfl | (norm_num at h)

theorem neg_one_ne_one {F : Type*} [Field F] (hF : ringChar F ≠ 2) : (-1 : SL(2, F)) ≠ 1 := by
  intro h
  have h1 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
    Matrix.neg_apply, Matrix.one_apply_eq] at h1
  exact Ring.two_ne_zero hF (by linear_combination -h1)

variable {P : Type*} [Group P] [Finite P]

theorem core_eq {F₀ : Type} [Field F₀] [Finite F₀]
    (hM : InvCentModel P F₀) (hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F₀))
    (hrank : CFSG.Open.pRank 2 (⊤ : Subgroup P) ≤ 2) {R K : Subgroup P} (hc : LConf R K)
    (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R) (hK : ⁅K, K⁆ = K) (hK1 : K ≠ ⊥) {n : ℕ} (hn : 2 ≤ n)
    {F' : Type} [Field F'] [Fintype F'] (hF' : Fintype.card F' = 2 ^ n) (χ : ↥K →* SL(2, F'))
    (hχ : Function.Surjective χ) (hχk : IsPGroup 2 χ.ker) : n = 2 ∧ Nat.card F₀ = 5 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F' 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) hF'
  obtain ⟨p, f, hp, hpodd, hf, hq⟩ := hodd
  have hqodd : Odd (Nat.card F₀) := hq ▸ hpodd.pow
  have hF₀ : ringChar F₀ ≠ 2 := by
    intro h2
    have : Fintype F₀ := Fintype.ofFinite F₀
    have hdvd : ringChar F₀ ∣ Nat.card F₀ :=
      ringChar.dvd (by rw [Nat.card_eq_fintype_card]; exact FiniteField.cast_card_eq_zero F₀)
    rw [h2] at hdvd
    exact (Nat.not_even_iff_odd.mpr hqodd) (even_iff_two_dvd.mpr hdvd)
  have hrank' : ∀ E : Subgroup P, E ≤ R → IsElemAbelian 2 E → Nat.card E ≤ 4 := by
    intro E hER hE
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hR2.to_le hER)
    have hk2 := (CFSG.SectionRank.le_pRank (by norm_num) le_top hE hk).trans hrank
    rw [hk]
    calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
      _ = 4 := by norm_num
  obtain ⟨z, -, hz2, hzc, hzK⟩ :=
    exists_involution_centralized hK hc.le_normalizer hR hR2 hrank'
  obtain ⟨ι, hιinj, hιC, hCC, hschur⟩ := hM z hz2
  have hKC : K ≤ centralizer ({z} : Set P) := fun k hk =>
    mem_centralizer_singleton_iff.mpr (hzK k hk)
  have hKι : K ≤ ι.range :=
    calc K = ⁅K, K⁆ := hK.symm
      _ ≤ ⁅centralizer ({z} : Set P), centralizer ({z} : Set P)⁆ :=
        Subgroup.commutator_mono hKC hKC
      _ ≤ ι.range := hCC
  set K₂ : Subgroup SL(2, F₀) := K.comap ι with hK₂def
  have hmapK : K₂.map ι = K := Subgroup.map_comap_eq_self hKι
  let eK : ↥K₂ ≃* ↥K := (K₂.equivMapOfInjective ι hιinj).trans (MulEquiv.subgroupCongr hmapK)
  have hK₂ : ⁅K₂, K₂⁆ = K₂ := by
    apply Subgroup.map_injective hιinj
    rw [Subgroup.map_commutator, hmapK, hK]
  have hK₂1 : K₂ ≠ ⊥ := by
    intro hb
    apply hK1
    rw [← hmapK, hb, Subgroup.map_bot]
  set χ₂ : ↥K₂ →* SL(2, F') := χ.comp eK.toMonoidHom with hχ₂
  have hχ₂s : Function.Surjective χ₂ := hχ.comp eK.surjective
  have hχ₂k : IsPGroup 2 χ₂.ker := by
    rw [hχ₂, ← MonoidHom.comap_ker]
    exact hχk.comap_of_injective _ eK.injective
  have hn2 : n = 2 := le_antisymm (n_eq_two ⟨p, f, hp, hpodd, hf, hq⟩ hK₂ hK₂1 hF' χ₂ hχ₂s hχ₂k) hn
  subst hn2
  have hF'4 : Nat.card F' = 4 := by rw [Nat.card_eq_fintype_card, hF']; norm_num
  have hSL' : Nat.card SL(2, F') = 60 := by rw [card_sl2, hF'4]; norm_num
  have hcardK₂ := Subgroup.card_ker_mul_card_of_surjective hχ₂s
  rw [hSL'] at hcardK₂
  have hneg : (-1 : SL(2, F₀)) ∈ K₂ :=
    neg_one_mem hF₀ (by rw [← hcardK₂]; exact Dvd.dvd.mul_left (by norm_num) _)
  have h120 : Nat.card ↥K₂ = 120 := by
    rw [← hcardK₂, ker_chi_eq hK₂ hK₂1 χ₂ hχ₂s hχ₂k,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe ((Subgroup.zpowers_le).mpr hneg)).toEquiv,
      Nat.card_zpowers, orderOf_eq_prime neg_one_sq (neg_one_ne_one hF₀)]
  have hRK : ∀ y ∈ R ⊓ K, ∀ k ∈ K, y * k = k * y := by
    intro y hy k hk
    obtain ⟨t, rfl⟩ := hKι (Subgroup.mem_inf.mp hy).2
    obtain ⟨t', rfl⟩ := hKι hk
    set N₂ : Subgroup SL(2, F₀) := (R ⊓ K).comap ι with hN₂
    have hN2 : IsPGroup 2 N₂ := (hR2.to_le inf_le_left).comap_of_injective ι hιinj
    have hNK : N₂ ≤ K₂ := Subgroup.comap_mono inf_le_right
    have hKN : K₂ ≤ Subgroup.normalizer (N₂ : Set SL(2, F₀)) := by
      intro s hs
      rw [Subgroup.mem_normalizer_iff]
      intro u
      have hsR := Subgroup.mem_normalizer_iff.mp (hc.le_normalizer hs)
      have hsK := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (show ι s ∈ K from hs))
      simp only [hN₂, Subgroup.mem_comap, Subgroup.mem_inf, map_mul, map_inv]
      exact and_congr (hsR (ι u)) (hsK (ι u))
    have ht : t ∈ Subgroup.center SL(2, F₀) :=
      zpowers_le_center (pCoreOf_le_zpowers hK₂ hK₂1
        (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hNK hKN hN2 hy))
    calc ι t * ι t' = ι (t * t') := (map_mul ι t t').symm
      _ = ι (t' * t) := by rw [(Subgroup.mem_center_iff.mp ht t').symm]
      _ = ι t' * ι t := map_mul ι t' t
  have hRc : ∀ r ∈ R, ∀ k ∈ K, r * k = k * r := by
    intro r hr
    refine centralizes_of_commutator_mem hK inf_le_right hRK fun k hk => ?_
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h1 : k * r⁻¹ * k⁻¹ ∈ R :=
        (Subgroup.mem_normalizer_iff.mp (hc.le_normalizer hk) r⁻¹).mp (R.inv_mem hr)
      have e : r * k * r⁻¹ * k⁻¹ = r * (k * r⁻¹ * k⁻¹) := by group
      rw [e]
      exact R.mul_mem hr h1
    · have h1 : r * k * r⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp
        (hc.normalizer_le (Subgroup.le_normalizer hr)) k).mp hk
      exact K.mul_mem h1 (K.inv_mem hk)
  have hRZ : ∀ r ∈ R, ∀ c ∈ centralizer ({z} : Set P), r * c = c * r := fun r hr =>
    hschur K₂ (exists_noncomm_of_perfect hK₂ hK₂1) r
      (mem_centralizer_singleton_iff.mpr (hzc r hr).symm) fun h hh => hRc r hr (ι h) hh
  have hCN : centralizer ({z} : Set P) ≤ Subgroup.normalizer (R : Set P) := by
    intro c hc'
    rw [Subgroup.mem_normalizer_iff]
    intro r
    constructor
    · intro hr
      have e : c * r * c⁻¹ = r := by rw [← hRZ r hr c hc', mul_inv_cancel_right]
      rw [e]
      exact hr
    · intro hr
      have e : r = c * r * c⁻¹ := by
        have h1 := hRZ _ hr c hc'
        calc r = c⁻¹ * (c * r * c⁻¹ * c) := by group
          _ = c⁻¹ * (c * (c * r * c⁻¹)) := by rw [h1]
          _ = c * r * c⁻¹ := by group
      rw [e]
      exact hr
  have hK₂N : K₂.Normal := by
    refine ⟨fun t ht s => ?_⟩
    have hs : ι s ∈ Subgroup.normalizer (K : Set P) :=
      hc.normalizer_le (hCN (hιC ⟨s, rfl⟩))
    show ι (s * t * s⁻¹) ∈ K
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hs (ι t)).mp ht
  have hle : 120 ≤ Nat.card F₀ * (Nat.card F₀ ^ 2 - 1) := by
    rw [← h120, ← card_sl2]
    exact Subgroup.card_le_card_group K₂
  have h4 : 4 ≤ Nat.card F₀ := by
    have h3 : 3 ≤ Nat.card F₀ := by
      rw [hq]
      have hp3 : 3 ≤ p := by
        have := hp.two_le
        obtain ⟨m, hm⟩ := hpodd
        omega
      exact hp3.trans (Nat.le_self_pow (by omega) p)
    by_contra h4
    have h3' : Nat.card F₀ = 3 := by omega
    rw [h3'] at hle
    norm_num at hle
  have htop := eq_top_of_normal h4 hK₂ hK₂1 hneg hK₂N
  refine ⟨rfl, eq_five_of_mul ?_⟩
  rw [← card_sl2, ← h120, htop, Subgroup.card_top]

end CFSG.Quasithin.H13.KGInspOdd
