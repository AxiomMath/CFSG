module

public import CFSG.LocalAnalysis.StandardType.GGResUnitaryQPlusKProducers

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.StandardType.LineU TableB

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem GGResHyp.dvd_rank_add_one_of_unitary_exactThree_K
    (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {ℓ : ℕ}
    (hU : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ lab.rank = ℓ ∧ p ∣ 2 ^ lab.n + 1) p Bs K)
    (hℓ : 4 ≤ ℓ) (h63 : ¬ (ℓ + 1 = 6 ∧ p = 3))
    (h3 : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) :
    ∃ n : ℕ, p ∣ 2 ^ n + 1 ∧ p ∣ ℓ + 1 := by
  classical
  obtain ⟨-, lab, hΛ, hraw⟩ := hU
  obtain ⟨R₀, iR₀, I₀, F₀, hQ₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ₀, hP₀⟩ := hQ₀
  obtain ⟨⟨htag, hrank, hpq⟩, -, -⟩ := hP₀
  obtain ⟨tag, rank, n⟩ := lab
  change tag = .twA at htag
  change rank = ℓ at hrank
  change p ∣ 2 ^ n + 1 at hpq
  subst htag hrank
  dsimp only [LargeEvenRawDatumLegacy] at hraw
  obtain ⟨F, hField, hFinite, hFK, hQ⟩ := hraw
  let _ : Field F := hField
  let _ : Finite F := hFinite
  obtain ⟨-, -, θ, -, hN, hact⟩ := hQ
  obtain ⟨ψ, hM, hdiag⟩ :=
    hH.exists_unitaryModel_K_of_marking_data hFK hΛ.1 (by omega) hpq h63 θ hN hact
  obtain ⟨-, -, hpd, -⟩ :=
    hH.unitary_exactThree_typeA_card_J_of_K hLB hM hpq (by omega) hdiag h3
  exact ⟨n, hpq, hpd⟩

theorem GGResHyp.false_of_unitary_rank_six_exactThree_K
    (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hU : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ lab.rank = 6 ∧ p ∣ 2 ^ lab.n + 1) p Bs K)
    (h3 : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) : False := by
  have hp : p.Prime := Fact.out
  obtain ⟨n, hpq, hpd⟩ :=
    hH.dvd_rank_add_one_of_unitary_exactThree_K hLB hU (by norm_num) (by omega) h3
  have hp7 : p = 7 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).mp hpd
  rw [hp7] at hpq
  have h2 : ∀ k : ℕ, 2 ^ k % 7 = 1 ∨ 2 ^ k % 7 = 2 ∨ 2 ^ k % 7 = 4 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Nat.mul_mod]
      rcases ih with h | h | h <;> rw [h] <;> norm_num
  have h2n := h2 n
  generalize 2 ^ n = t at h2n hpq
  omega

theorem GGResHyp.false_of_unitary_rank_seven_exactThree_K
    (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hU : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ lab.rank = 7 ∧ p ∣ 2 ^ lab.n + 1) p Bs K)
    (h3 : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) : False := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  obtain ⟨-, -, hpd⟩ :=
    hH.dvd_rank_add_one_of_unitary_exactThree_K hLB hU (by norm_num) (by omega) h3
  have h8 : p ∣ 2 ^ 3 := by simpa using hpd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h8))

section Cert


theorem ggResLeaf_unitary_rank_six_exactThree_K :
    GGResLeaf fun _ _ _ p _ _ Bs _ L _ J _ K =>
      GGInnerDiagOnLabel
        (fun p lab => lab.tag = .twA ∧ lab.rank = 6 ∧ 2 ≤ lab.n ∧
          p ∣ 2 ^ lab.n + 1) p Bs K ∧
      GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny ∧
      ¬ ggReservedRows p J L K ∧
      ¬ (GGResRowAt ggRowTwoNode p J L ∨ GGResRowAt ggRowTwoNode p J K) ∧
      ¬ (GGResRowAt ggRowCorank2C p J L ∨ GGResRowAt ggRowCorank2C p J K) ∧
      ¬ (GGResRowAt ggRowSUCorank2 p J L ∨ GGResRowAt ggRowSUCorank2 p J K) := by
  intro G _ _ p B Bs x L D J y K hH _ _ _ _ hP
  obtain ⟨hU, h3, -⟩ := hP
  exact (hH.false_of_unitary_rank_six_exactThree_K ggGammaSuppliers_proved.1
    (GGInnerDiagOnLabel.mono_label (fun _ h => ⟨h.1, h.2.1, h.2.2.2⟩) hU) h3).elim


theorem ggResLeaf_unitary_rank_seven_exactThree_K :
    GGResLeaf fun _ _ _ p _ _ Bs _ L _ J _ K =>
      GGInnerDiagOnLabel
        (fun p lab => lab.tag = .twA ∧ lab.rank = 7 ∧ 2 ≤ lab.n ∧
          p ∣ 2 ^ lab.n + 1) p Bs K ∧
      GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny ∧
      ¬ ggReservedRows p J L K ∧
      ¬ (GGResRowAt ggRowTwoNode p J L ∨ GGResRowAt ggRowTwoNode p J K) ∧
      ¬ (GGResRowAt ggRowCorank2C p J L ∨ GGResRowAt ggRowCorank2C p J K) ∧
      ¬ (GGResRowAt ggRowSUCorank2 p J L ∨ GGResRowAt ggRowSUCorank2 p J K) := by
  intro G _ _ p B Bs x L D J y K hH _ _ _ _ hP
  obtain ⟨hU, h3, -⟩ := hP
  exact (hH.false_of_unitary_rank_seven_exactThree_K ggGammaSuppliers_proved.1
    (GGInnerDiagOnLabel.mono_label (fun _ h => ⟨h.1, h.2.1, h.2.2.2⟩) hU) h3).elim

end Cert

end CFSG.StandardType

end
