module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCase2
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocOmega
public import CFSG.Sporadic.J4

public section

namespace CFSG.Quasithin.J4Loc

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

@[expose] def J4TwoLocalOvergroups : Prop :=
  ∀ N : Subgroup J, IsPGroup 2 N → N ≠ ⊥ → P0 ≤ Subgroup.normalizer (N : Set J) →
    Subgroup.normalizer (N : Set J) ≤ Hj ∨
      Subgroup.normalizer (N : Set J) ≤ Subgroup.centralizer ({z0} : Set J) ∨
      Subgroup.normalizer (N : Set J) ≤ Subgroup.normalizer (V0 : Set J)

theorem elem_abelian_overgroups
    (hF : J4Facts) {A : Subgroup J} (hAP : A ≤ P0) (hn : ∀ g ∈ P0, ∀ x ∈ A, g * x * g⁻¹ ∈ A)
    (hne : A ≠ ⊥) (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hsq : ∀ x ∈ A, x * x = 1) :
    Subgroup.normalizer (A : Set J) ≤ Hj ∨
      Subgroup.normalizer (A : Set J) ≤ Subgroup.centralizer ({z0} : Set J) ∨
      Subgroup.normalizer (A : Set J) ≤ Subgroup.normalizer (V0 : Set J) := by
  by_cases hAE : A ≤ Eg uJ 11
  · exact case1 hF hAE hn hne
  · exact case2 hF hAP hn hcomm hsq hAE

theorem twoLocalOvergroups_of_facts
    (hF : J4Facts) : J4TwoLocalOvergroups := by
  intro N hN hne hP
  have hM := hF.mat
  have hNP : N ≤ P0 := by
    let S : Sylow 2 J := Sylow.ofCard P0 (by rw [card_P0 hM hF, card_J_factorization hF])
    have hsup : IsPGroup 2 ↥(N ⊔ P0) := hN.to_sup_of_normal_left' (isPGroup_P0 hF) hP
    have h1 := S.is_maximal' hsup (by rw [Sylow.coe_ofCard]; exact le_sup_right)
    rw [Sylow.coe_ofCard] at h1
    rw [← h1]
    exact le_sup_left
  have hA : omegaZ N ≠ ⊥ := omegaZ_ne_bot hN hne
  have hAP : omegaZ N ≤ P0 := (omegaZ_le N).trans hNP
  have hn : ∀ g ∈ P0, ∀ x ∈ omegaZ N, g * x * g⁻¹ ∈ omegaZ N := fun g hg x hx =>
    omegaZ_conj (hP hg) hx
  have hcomm : ∀ x ∈ omegaZ N, ∀ y ∈ omegaZ N, x * y = y * x := fun x hx y hy => hx.2.1 y hy.1
  have hsq : ∀ x ∈ omegaZ N, x * x = 1 := fun x hx => hx.2.2
  have hNA : Subgroup.normalizer (N : Set J) ≤ Subgroup.normalizer (omegaZ N : Set J) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => omegaZ_conj hg hx
    · intro hx
      have hg' : g⁻¹ ∈ Subgroup.normalizer (N : Set J) :=
        (Subgroup.normalizer (N : Set J)).inv_mem hg
      have h1 := omegaZ_conj hg' hx
      have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
      rwa [e] at h1
  rcases elem_abelian_overgroups hF hAP hn hA hcomm hsq with h | h | h
  · exact Or.inl (hNA.trans h)
  · exact Or.inr (Or.inl (hNA.trans h))
  · exact Or.inr (Or.inr (hNA.trans h))

theorem j4TwoLocalOvergroups :
    J4TwoLocalOvergroups :=
  twoLocalOvergroups_of_facts j4Facts

theorem overgroup_of_normal_two_subgroup (h : J4TwoLocalOvergroups) {Y : Subgroup J}
    (hY : P0 ≤ Y) {N : Subgroup J} (hN : IsPGroup 2 N) (hne : N ≠ ⊥)
    (hNY : ∀ y ∈ Y, ∀ x ∈ N, y * x * y⁻¹ ∈ N) :
    Y ≤ Hj ∨ Y ≤ Subgroup.centralizer ({z0} : Set J) ∨ Y ≤ Subgroup.normalizer (V0 : Set J) := by
  have hYN : Y ≤ Subgroup.normalizer (N : Set J) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hNY y hy x hx, fun hx => ?_⟩
    have := hNY y⁻¹ (Y.inv_mem hy) _ hx
    have e : y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x := by group
    rwa [e] at this
  rcases h N hN hne (hY.trans hYN) with h1 | h1 | h1
  · exact Or.inl (hYN.trans h1)
  · exact Or.inr (Or.inl (hYN.trans h1))
  · exact Or.inr (Or.inr (hYN.trans h1))

end CFSG.Quasithin.J4Loc
