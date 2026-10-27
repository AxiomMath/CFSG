module

public import CFSG.Quasithin.EmptyFaithful.Insp9Cases3
public import CFSG.Quasithin.EmptyFaithful.Insp9P7
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace Insp9

section B56

variable {W : Type} [CommGroup W] [Finite W]

theorem b56_four_dvd_or_three_primes {G : Subgroup (MulAut W)}
    (h : B56Case1 G ∨ B56Case3 G ∨ B56Case4 G ∨ B56Case5 G) :
    4 ∣ Nat.card ↥G ∨ 3 ≤ (Nat.card ↥G).primeFactors.card := by
  rcases h with h1 | h3 | h4 | h5
  · right
    obtain ⟨hLq, -, -⟩ := h1
    have hLG : quasithinGenFitting G ≤ G := quasithinGenFitting_le G
    have hdvd : Nat.card ↥(quasithinGenFitting G) ∣ Nat.card ↥G := Subgroup.card_dvd_of_le hLG
    have hpf : (Nat.card ↥(quasithinGenFitting G)).primeFactors ⊆ (Nat.card ↥G).primeFactors :=
      Nat.primeFactors_mono hdvd Nat.card_pos.ne'
    refine le_trans ?_ (Finset.card_le_card hpf)
    by_contra hcon
    push Not at hcon
    have hsolv := CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two (G := ↥(quasithinGenFitting G)) (by omega)
    have : Group.IsPerfect ↥(quasithinGenFitting G) := hLq.1
    have hnt : Nontrivial ↥(quasithinGenFitting G) := by
      have hsimple := hLq.2.1
      obtain ⟨x, y, hxy⟩ := exists_pair_ne
        (↥(quasithinGenFitting G) ⧸ Subgroup.center ↥(quasithinGenFitting G))
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
      exact ⟨a, b, fun hab => hxy (by rw [hab])⟩
    exact Group.IsPerfect.not_isSolvable ↥(quasithinGenFitting G) hsolv
  · left
    obtain ⟨G₁, G₂, hsup, hinf, hcomm, hF₁, hF₂, -⟩ := h3
    have hprod := card_sup_eq_mul hcomm hinf
    rw [hsup] at hprod
    rw [hprod]
    exact (Nat.mul_dvd_mul (b56FL_even hF₁) (b56FL_even hF₂) : 2 * 2 ∣ _)
  · left
    obtain ⟨G₁, G₂, t, hG, -, -, ⟨e⟩, -⟩ := h4
    have hG1card : Nat.card ↥G₁ = 360 := by
      rw [Nat.card_congr e.toEquiv, card_alternatingGroup1527d 6 (by norm_num)]
      simp [Nat.factorial]
    have hle : G₁ ≤ G := hG ▸ le_sup_left.trans le_sup_left
    have := Subgroup.card_dvd_of_le hle
    rw [hG1card] at this
    exact Dvd.dvd.trans (by norm_num) this
  · left
    obtain ⟨G₁, G₂, hsup, -, -, -, ⟨e⟩, -⟩ := h5
    have hG1card : Nat.card ↥G₁ = 168 := by
      rw [Nat.card_congr e.toEquiv, card_statedSL_three1527d, Nat.card_zmod]
      norm_num
    have hle : G₁ ≤ G := hsup ▸ le_sup_left
    have := Subgroup.card_dvd_of_le hle
    rw [hG1card] at this
    exact Dvd.dvd.trans (by norm_num) this

end B56

section Core

variable {D : Type} [Group D] [Finite D] {D₁ D₂ J N : Subgroup D}

theorem Data.card_T_of (h : Data D₁ D₂ J N) {a : ℕ} (h1 : 2 ^ a ∣ Nat.card D)
    (h2 : ¬ 2 ^ (a + 1) ∣ Nat.card D) : Nat.card ↥(D₁ ⊓ D₂) = 2 ^ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT'⟩ := h.amalgam.toIsGoldschmidtTriple.sylow
  have hc : Nat.card ↥T = 2 ^ (Nat.card D).factorization 2 := Sylow.card_eq_multiplicity T
  have h3 : Nat.card ↥T = Nat.card ↥(D₁ ⊓ D₂) := by rw [← hT']; rfl
  have hD0 : Nat.card D ≠ 0 := Nat.card_pos.ne'
  have ha : a ≤ (Nat.card D).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hD0).mp h1
  have hb : ¬ a + 1 ≤ (Nat.card D).factorization 2 := fun hb =>
    h2 ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hD0).mpr hb)
  have : (Nat.card D).factorization 2 = a := by omega
  rw [← h3, hc, this]

theorem case2_core (h : Data D₁ D₂ J N) (hs : B56Setting D N) {A : Type} [CommGroup A]
    (φ : D →* A) (hφ : Function.Surjective φ) (hA : Nat.card A = 4)
    (hk : Nat.card ↥φ.ker ∣ 27) : Nonempty (↥N ≃* Equiv.Perm (Fin 3)) := by
  have hDcard : Nat.card ↥φ.ker * Nat.card A = Nat.card D := Subgroup.card_ker_mul_card_of_surjective hφ
  rw [hA] at hDcard
  obtain ⟨k, hk27⟩ := hk
  have hkodd : Nat.card ↥φ.ker ∣ 27 := ⟨k, hk27⟩
  have hkodd' : ¬ 2 ∣ Nat.card ↥φ.ker := fun h2 => by
    have := h2.trans hkodd
    omega
  have hD4 : 2 ^ 2 ∣ Nat.card D := ⟨Nat.card ↥φ.ker, by rw [← hDcard]; ring⟩
  have hD8 : ¬ 2 ^ (2 + 1) ∣ Nat.card D := by
    intro h8
    rw [← hDcard] at h8
    have : 2 ∣ Nat.card ↥φ.ker := by
      have h8' : 2 ^ 3 ∣ 4 * Nat.card ↥φ.ker := by
        rwa [mul_comm] at h8
      omega
    exact hkodd' this
  have hT := h.card_T_of hD4 hD8
  have hD1 : Nat.card ↥D₁ = 12 := by rw [h.card_D₁, hT]; norm_num
  have hJ2 : Nat.card ↥J ∣ 2 := by
    have hJle : J ≤ pCoreOf 2 D₁ := le_pCoreOf_of_le_normalizer 2 h.le h.norm h.pgrp
    have h1 : Nat.card ↥J ∣ Nat.card ↥(pCoreOf 2 D₁) := Subgroup.card_dvd_of_le hJle
    have h2 : Nat.card ↥(pCoreOf 2 D₁) = Nat.card ↥(Open.pCore 2 ↥D₁) :=
      Subgroup.card_map_of_injective D₁.subtype_injective
    obtain ⟨e⟩ := h.amalgam.quotient₁
    have h3 : Nat.card (↥D₁ ⧸ Open.pCore 2 ↥D₁) = 6 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
      simp [Nat.factorial]
    have h4 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Open.pCore 2 ↥D₁)
    rw [h3, hD1] at h4
    have h5 : Nat.card ↥(Open.pCore 2 ↥D₁) = 2 := by omega
    rw [h2, h5] at h1
    exact h1
  set P : Subgroup D := φ.ker with hPdef
  have hcomm : ∀ x y : D, x * y * x⁻¹ * y⁻¹ ∈ P := by
    intro x y
    rw [hPdef, MonoidHom.mem_ker]
    have : φ (x * y * x⁻¹ * y⁻¹) = ⁅φ x, φ y⁆ := by
      rw [commutatorElement_def]; simp
    rw [this]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  have hRnormal : (J ⊔ P).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hn
    have e1 : g * (a * b) * g⁻¹ = (g * a * g⁻¹ * a⁻¹) * a * (g * b * g⁻¹) := by group
    rw [e1]
    refine (J ⊔ P).mul_mem ((J ⊔ P).mul_mem ?_ ?_) ?_
    · exact (le_sup_right : P ≤ J ⊔ P) (hcomm g a)
    · exact (le_sup_left : J ≤ J ⊔ P) ha
    · exact (le_sup_right : P ≤ J ⊔ P) (Subgroup.Normal.conj_mem inferInstance b hb g)
  have hNR : N ≤ J ⊔ P := by
    rw [h.eq]
    exact Subgroup.normalClosure_le_normal (le_sup_left : J ≤ J ⊔ P)
  have hRcard : Nat.card ↥(J ⊔ P) ∣ 2 * Nat.card ↥P := by
    have hP' : P ≤ J ⊔ P := le_sup_right
    have e2 := QuotientGroup.quotientInfEquivProdNormalQuotient J P
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (P.subgroupOf (J ⊔ P))
    have h2 : Nat.card (↥(J ⊔ P) ⧸ P.subgroupOf (J ⊔ P)) ∣ Nat.card ↥J := by
      rw [← Nat.card_congr e2.toEquiv, ← Subgroup.index_eq_card]
      exact Subgroup.index_dvd_card _
    have h3 : Nat.card ↥(P.subgroupOf (J ⊔ P)) = Nat.card ↥P :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP').toEquiv
    rw [h3] at h1
    rw [h1]
    exact Nat.mul_dvd_mul (h2.trans hJ2) dvd_rfl
  have hN54 : Nat.card ↥N ∣ 54 := by
    have h1 : Nat.card ↥N ∣ Nat.card ↥(J ⊔ P) := Subgroup.card_dvd_of_le hNR
    have h2 : 2 * Nat.card ↥P ∣ 2 * 27 := Nat.mul_dvd_mul dvd_rfl ⟨k, hk27⟩
    exact (h1.trans hRcard).trans h2
  obtain ⟨W, _, _, _, ρ, hρ, -, hcases⟩ := hs
  have hcardN : Nat.card ↥(N.map ρ) = Nat.card ↥N := Subgroup.card_map_of_injective hρ
  have h4N : ¬ 4 ∣ Nat.card ↥N := by
    intro h4
    have := h4.trans hN54
    omega
  have hpf : (Nat.card ↥N).primeFactors.card < 3 := by
    have hsub : (Nat.card ↥N).primeFactors ⊆ ({2, 3} : Finset ℕ) := by
      intro p hp
      have hp' := Nat.mem_primeFactors.mp hp
      have hp54 : p ∣ 2 * 3 ^ 3 := by norm_num; exact hp'.2.1.trans hN54
      rcases (Nat.Prime.dvd_mul hp'.1).mp hp54 with h2 | h3
      · have := (Nat.prime_dvd_prime_iff_eq hp'.1 Nat.prime_two).mp h2
        simp [this]
      · have := (Nat.prime_dvd_prime_iff_eq hp'.1 Nat.prime_three).mp (hp'.1.dvd_of_dvd_pow h3)
        simp [this]
    exact lt_of_le_of_lt (Finset.card_le_card hsub) (by decide)
  rcases hcases with h1 | h2 | h3 | h4 | h5
  · exfalso
    rcases b56_four_dvd_or_three_primes (Or.inl h1) with h | h
    · rw [hcardN] at h; exact h4N h
    · rw [hcardN] at h; omega
  · obtain ⟨e⟩ := h2.1
    exact ⟨(Subgroup.equivMapOfInjective N ρ hρ).trans e⟩
  all_goals
    exfalso
    rcases b56_four_dvd_or_three_primes (by tauto) with h | h
    · rw [hcardN] at h; exact h4N h
    · rw [hcardN] at h; omega

end Core

theorem inspCase2 : InspCase fun {D} _ _ _ => F6.IsF618CaseTwo D := by
  intro D _ _ D₁ D₂ J N h hs hP
  have hD : F6.IsF618CaseTwo D := hP.elim id id
  left
  rcases hD with he | ⟨φ, hφ, hker⟩
  ·
    obtain ⟨e⟩ := he
    let ψ : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) →* ℤˣ × ℤˣ :=
      (Equiv.Perm.sign : Equiv.Perm (Fin 3) →* ℤˣ).prodMap
        (Equiv.Perm.sign : Equiv.Perm (Fin 3) →* ℤˣ)
    have hψ : Function.Surjective ψ := by
      rintro ⟨a, b⟩
      obtain ⟨x, hx⟩ := Equiv.Perm.sign_surjective (Fin 3) a
      obtain ⟨y, hy⟩ := Equiv.Perm.sign_surjective (Fin 3) b
      exact ⟨(x, y), by simp [ψ, hx, hy]⟩
    have hφ : Function.Surjective (ψ.comp e.toMonoidHom) := hψ.comp e.surjective
    have hA : Nat.card (ℤˣ × ℤˣ) = 4 := by
      rw [Nat.card_prod, Nat.card_eq_fintype_card]
      have : Fintype.card ℤˣ = 2 := by decide
      rw [this]
    have hD36 : Nat.card D = 36 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_perm]
      simp [Nat.factorial]
    have hk := Subgroup.card_ker_mul_card_of_surjective hφ
    rw [hA, hD36] at hk
    have hk9 : Nat.card ↥(ψ.comp e.toMonoidHom).ker = 9 := by omega
    exact case2_core h hs (ψ.comp e.toMonoidHom) hφ hA (by rw [hk9]; norm_num)
  ·
    have hA : Nat.card (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) = 4 := card_E4
    have hk27 : Nat.card ↥φ.ker = 27 := by simpa using hker.2.1
    exact case2_core h hs φ hφ hA (Dvd.intro 1 (by rw [mul_one]; exact hk27))

end Insp9

end CFSG.Quasithin
