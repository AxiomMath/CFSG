module

public import CFSG.GH74.GLS.C3.Layer1.BkP89J2Facts
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Sporadic.J2

open Subgroup CFSG.GH74.GLS.C3.Layer1.Bk.J2C
open scoped commutatorElement

structure J2CentEAFacts (X : Type*) [Group X] (t : X) (E : Subgroup X) : Prop where
  comm_not_ea : ∀ g ∈ Subgroup.centralizer ({t} : Set X), g ∉ E → g * g = 1 →
    ∃ e₁ ∈ E, ∃ e₂ ∈ E, ⁅e₁, g⁆ * ⁅e₂, g⁆ ≠ ⁅e₂, g⁆ * ⁅e₁, g⁆ ∨ ⁅e₁, g⁆ * ⁅e₁, g⁆ ≠ 1
  card_ea_le : ∀ A : Subgroup X, A ≤ E → CFSG.Open.IsElemAbelian 2 A → Nat.card A ≤ 4

section Transport

variable {Q Q' : Type*} [Group Q] [Group Q']

theorem J2CentEAFacts.of_mulEquiv (φ : Q ≃* Q') {t' : Q'} {E' : Subgroup Q'}
    (h : J2CentEAFacts Q' t' E') : J2CentEAFacts Q (φ.symm t') (E'.map φ.symm.toMonoidHom) := by
  have hmemE : ∀ x, x ∈ E'.map φ.symm.toMonoidHom ↔ φ x ∈ E' := mem_map_symm_iff φ E'
  refine ⟨fun g hg hgE hg2 => ?_, fun A hA hAe => ?_⟩
  · rw [centralizer_singleton_symm φ t', mem_map_symm_iff] at hg
    obtain ⟨e₁, he₁, e₂, he₂, h12⟩ := h.comm_not_ea (φ g) hg (fun h' => hgE ((hmemE g).2 h'))
      (by rw [← map_mul, hg2, map_one])
    refine ⟨φ.symm e₁, (hmemE _).2 (by simpa using he₁), φ.symm e₂,
      (hmemE _).2 (by simpa using he₂), ?_⟩
    have key : ∀ e : Q', ⁅φ.symm e, g⁆ = φ.symm ⁅e, φ g⁆ := fun e => by
      rw [map_commutatorElement, MulEquiv.symm_apply_apply]
    simp only [key, ← map_mul, ne_eq, EmbeddingLike.map_eq_one_iff, φ.symm.injective.eq_iff]
    exact h12
  · have hA' : A.map φ.toMonoidHom ≤ E' := by
      rintro _ ⟨a, ha, rfl⟩
      exact (hmemE a).1 (hA ha)
    have := h.card_ea_le _ hA' (hAe.map φ.toMonoidHom)
    rwa [Subgroup.card_map_of_injective φ.injective] at this

end Transport

variable {X : Type*} [Group X] {t : X} {E : Subgroup X}

theorem eq_of_j2CentFacts {E' : Subgroup X} (h : J2CentFacts X t E) (h' : J2CentFacts X t E') :
    E = E' := by
  have : Finite ↥E' := Nat.finite_of_card_ne_zero (by rw [h'.card_E]; norm_num)
  have hp : IsPGroup 2 ↥E := IsPGroup.of_card (n := 5) (by rw [h.card_E]; norm_num)
  exact Subgroup.eq_of_le_of_card_ge (h'.two_core E h.E_le h.E_normal hp)
    (by rw [h.card_E, h'.card_E])

private theorem card_le_of_forall_mem_finset {A : Subgroup X} (F : Finset X)
    (hF : ∀ a ∈ A, a ∈ F) : Nat.card A ≤ F.card :=
  calc Nat.card A = (A : Set X).ncard := Nat.card_coe_set_eq _
    _ ≤ (F : Set X).ncard := Set.ncard_le_ncard (fun a ha => hF a ha) F.finite_toSet
    _ = F.card := Set.ncard_coe_finset F

theorem card_le_four_of_forall_eq_mul {A : Subgroup X}
    (h : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x ≠ 1 → y ≠ 1 → z ≠ 1 → y ≠ x → z ≠ x → z ≠ y → z = x * y) :
    Nat.card A ≤ 4 := by
  classical
  by_contra hlt
  push Not at hlt
  have hout : ∀ F : Finset X, F.card ≤ 4 → ∃ a ∈ A, a ∉ F := fun F hF => by
    by_contra hall
    push Not at hall
    have := card_le_of_forall_mem_finset F hall
    omega
  obtain ⟨x, hx, hx1⟩ := hout {1} (by simp)
  obtain ⟨y, hy, hy1⟩ := hout {1, x} (Finset.card_le_two.trans (by norm_num))
  obtain ⟨z, hz, hz1⟩ := hout {1, x, y, x * y} Finset.card_le_four
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx1 hy1 hz1
  exact hz1.2.2.2 (h x hx y hy z hz hx1 hy1.1 hz1.1 hy1.2 hz1.2.1 hz1.2.2.1)

private theorem mul_self_eq_one_of_j2CentFacts (h : J2CentFacts X t E) : t * t = 1 := by
  rcases h.sq_mem t h.t_mem with h1 | h1
  · exact h1
  · rw [mul_eq_left.1 h1, mul_one]

private theorem pow_four_eq_one_of_mem (h : J2CentFacts X t E) {x : X} (hx : x ∈ E) :
    x ^ 2 ^ 2 = 1 := by
  have e : x ^ 2 ^ 2 = x * x * (x * x) := by
    rw [show 2 ^ 2 = 2 + 2 by norm_num, pow_add, pow_two]
  rcases h.sq_mem x hx with h1 | h1
  · rw [e, h1, mul_one]
  · rw [e, h1]
    exact mul_self_eq_one_of_j2CentFacts h

private theorem exists_mul_self_eq_of_j2CentFacts (h : J2CentFacts X t E) :
    ∃ x ∈ E, x * x = t := by
  classical
  by_contra hne
  push Not at hne
  have h1 : ∀ x ∈ E, x * x = 1 := fun x hx => (h.sq_mem x hx).resolve_right (hne x hx)
  have hinv : ∀ x ∈ E, x⁻¹ = x := fun x hx => inv_eq_of_mul_eq_one_right (h1 x hx)
  have hsub : ∀ x ∈ E, x ∈ ({1, t} : Finset X) := fun x hx => by
    have hc : ∀ y ∈ E, x * y = y * x := fun y hy => by
      have hxy := mul_eq_one_iff_eq_inv.1 (h1 _ (E.mul_mem hx hy))
      rwa [mul_inv_rev, hinv x hx, hinv y hy] at hxy
    rcases h.center x hx hc with rfl | rfl <;> simp
  have hcard := (card_le_of_forall_mem_finset _ hsub).trans Finset.card_le_two
  rw [h.card_E] at hcard
  omega

private theorem not_forall_commutator_mem (h' : J2CentEAFacts X t E) {g : X}
    (hg : g ∈ centralizer ({t} : Set X)) (hgE : g ∉ E) (hg2 : g * g = 1) {S : Set X}
    (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) (hS2 : ∀ a ∈ S, a * a = 1) :
    ¬ ∀ e ∈ E, ⁅e, g⁆ ∈ S := by
  intro hall
  obtain ⟨e₁, he₁, e₂, he₂, h12 | h11⟩ := h'.comm_not_ea g hg hgE hg2
  · exact h12 (hS _ (hall e₁ he₁) _ (hall e₂ he₂))
  · exact h11 (hS2 _ (hall e₁ he₁))

private theorem commutator_mem_of_sq_mem (h : J2CentFacts X t E) {N : Subgroup X}
    (hsq : ∀ x ∈ centralizer ({t} : Set X), (∃ k : ℕ, x ^ 2 ^ k = 1) → x ^ 2 ∈ N) {c : X}
    (hc : c ∈ centralizer ({t} : Set X)) (hc2 : c * c = 1) {e : X} (he : e ∈ E) :
    ⁅e, c⁆ ∈ N := by
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
  have heC : e ∈ centralizer ({t} : Set X) := h.E_le he
  have h2E : (e⁻¹ * c) ^ 2 ∈ E := by
    have e2 : (e⁻¹ * c) ^ 2 = e⁻¹ * (c * e⁻¹ * c⁻¹) := by
      rw [hcinv, pow_two]
      simp only [mul_assoc]
    rw [e2]
    exact E.mul_mem (E.inv_mem he) (h.E_normal c hc _ (E.inv_mem he))
  have h8 : (e⁻¹ * c) ^ 2 ^ 3 = 1 := by
    rw [show 2 ^ 3 = 2 * 2 ^ 2 by norm_num, pow_mul]
    exact pow_four_eq_one_of_mem h h2E
  have hN1 := hsq e heC ⟨2, pow_four_eq_one_of_mem h he⟩
  have hN2 := hsq _ (mul_mem (inv_mem heC) hc) ⟨3, h8⟩
  have ec : ⁅e, c⁆ = e ^ 2 * (e⁻¹ * c) ^ 2 := by
    rw [commutatorElement_def, hcinv, pow_two, pow_two]
    simp only [mul_assoc, mul_inv_cancel_left]
  rw [ec]
  exact N.mul_mem hN1 hN2

theorem card_elemAbelian_le_four_of_normalized (h : J2CentFacts X t E)
    (h' : J2CentEAFacts X t E) {N A : Subgroup X}
    (hNn : ∀ c ∈ Subgroup.centralizer ({t} : Set X), ∀ k ∈ N, c * k * c⁻¹ ∈ N)
    (hsq : ∀ x ∈ Subgroup.centralizer ({t} : Set X), (∃ k : ℕ, x ^ 2 ^ k = 1) → x ^ 2 ∈ N)
    (hA : A ≤ Subgroup.centralizer ({t} : Set X)) (hAe : CFSG.Open.IsElemAbelian 2 A)
    (hNA : N ≤ Subgroup.normalizer (A : Set X)) : Nat.card A ≤ 4 := by
  by_cases hAE : A ≤ E
  · exact h'.card_ea_le A hAE hAe
  exfalso
  obtain ⟨c, hcA, hcE⟩ := SetLike.not_le_iff_exists.1 hAE
  have hcC := hA hcA
  have hc2 : c * c = 1 := by rw [← pow_two]; exact hAe.2 c hcA
  have htt := mul_self_eq_one_of_j2CentFacts h
  have htN : t ∈ N := by
    obtain ⟨x, hx, hxt⟩ := exists_mul_self_eq_of_j2CentFacts h
    have := hsq x (h.E_le hx) ⟨2, pow_four_eq_one_of_mem h hx⟩
    rwa [pow_two, hxt] at this
  have hcE' : ∀ e ∈ E, ⁅e, c⁆ ∈ E := fun e he => by
    rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc c]
    exact E.mul_mem he (h.E_normal c hcC _ (E.inv_mem he))
  have hout : ¬ ∀ e ∈ E, ⁅e, c⁆ ∈ ({1, t} : Set X) := by
    refine not_forall_commutator_mem h' hcC hcE hc2 ?_ ?_
    · rintro a (rfl | rfl) b (rfl | rfl) <;> simp
    · rintro a (rfl | rfl)
      · exact mul_one 1
      · exact htt
  simp only [not_forall] at hout
  obtain ⟨e, he, hne⟩ := hout
  have hEN : E ≤ N ⊓ E := h.irred (N ⊓ E) inf_le_right ⟨htN, h.t_mem⟩
    (fun y hy n hn => ⟨hNn y hy n hn.1, h.E_normal y hy n hn.2⟩)
    ⟨⁅e, c⁆, ⟨commutator_mem_of_sq_mem h hsq hcC hc2 he, hcE' e he⟩,
      fun h1 => hne (Or.inl h1), fun h1 => hne (Or.inr h1)⟩
  refine not_forall_commutator_mem h' hcC hcE hc2 (S := (A : Set X))
    (fun a ha b hb => congrArg Subtype.val (hAe.1.is_comm.comm (⟨a, ha⟩ : A) ⟨b, hb⟩))
    (fun a ha => by rw [← pow_two]; exact hAe.2 a ha) fun e he => ?_
  have heN : e ∈ normalizer (A : Set X) := hNA (hEN he).1
  rw [commutatorElement_def]
  exact A.mul_mem ((mem_normalizer_iff.1 heN c).1 hcA) (A.inv_mem hcA)

end CFSG.Sporadic.J2
