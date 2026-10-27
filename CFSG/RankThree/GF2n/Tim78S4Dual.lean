module

public import Mathlib.GroupTheory.Index
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

public section

namespace CFSG.RankThree.GF2n.Tim78

open scoped commutatorElement

open IsMulCommutative in
private theorem exists_eq_of_pairing_ker {P : Type*} [Group P] [Finite P] (N : Subgroup P)
    (hN : ∀ a b : P, ⁅a, b⁆ ∈ N) (ψ : P → P → ℂˣ) (χ : P → ℂˣ)
    (hψ₂ : ∀ x p p', ψ x (p * p') = ψ x p * ψ x p')
    (hχ : ∀ p p', χ (p * p') = χ p * χ p')
    (hψ₁ : ∀ x x' p, ψ (x * x') p = ψ x p * ψ x' p)
    (hψN : ∀ x, ∀ n ∈ N, ψ x n = 1) (hχN : ∀ n ∈ N, χ n = 1)
    (hker : ∀ x, (∀ p, ψ x p = 1) → x ∈ N) : ∃ x, ∀ p, ψ x p = χ p := by
  haveI : N.Normal := ⟨fun n hn g => by
    have h := N.mul_mem (hN g n) hn
    simpa [commutatorElement_def, mul_assoc] using h⟩
  haveI : IsMulCommutative (P ⧸ N) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr (by
      rw [commutator_eq_closure]
      exact (Subgroup.closure_le N).mpr (by rintro _ ⟨a, b, rfl⟩; exact hN a b))
  let ψh : P → P →* ℂˣ := fun x => MonoidHom.mk' (ψ x) (hψ₂ x)
  let χh : P →* ℂˣ := MonoidHom.mk' χ hχ
  have hψhN : ∀ x, N ≤ (ψh x).ker := fun x n hn => hψN x n hn
  have hχhN : N ≤ χh.ker := fun n hn => hχN n hn
  let r : P ⧸ N → P := Function.surjInv QuotientGroup.mk_surjective
  have hr : ∀ a : P ⧸ N, ((r a : P) : P ⧸ N) = a :=
    Function.surjInv_eq QuotientGroup.mk_surjective
  let Ψ : P ⧸ N → ((P ⧸ N) →* ℂˣ) := fun a => QuotientGroup.lift N (ψh (r a)) (hψhN _)
  have hΨ : ∀ a (p : P), Ψ a (p : P ⧸ N) = ψ (r a) p := fun a p => rfl
  have hinj : Function.Injective Ψ := by
    intro a a' h
    have h1 : ∀ p, ψ (r a) p = ψ (r a') p := fun p => by
      rw [← hΨ, ← hΨ, h]
    have h2 : (r a)⁻¹ * r a' ∈ N := by
      refine hker _ fun p => ?_
      have h3 := hψ₁ (r a) ((r a)⁻¹ * r a') p
      rw [mul_inv_cancel_left, ← h1 p] at h3
      exact mul_left_cancel (a := ψ (r a) p) (by rw [mul_one]; exact h3.symm)
    rw [← hr a, ← hr a']
    exact QuotientGroup.eq.mpr h2
  haveI : NeZero ((Monoid.exponent (P ⧸ N) : ℕ) : ℂ) :=
    ⟨by exact_mod_cast Monoid.exponent_ne_zero_of_finite⟩
  have hcard : Nat.card ((P ⧸ N) →* ℂˣ) = Nat.card (P ⧸ N) :=
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (P ⧸ N) ℂ
  haveI : Finite ((P ⧸ N) →* ℂˣ) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.card_pos.ne')
  have hbij : Function.Bijective Ψ :=
    (Nat.bijective_iff_injective_and_card Ψ).mpr ⟨hinj, hcard.symm⟩
  obtain ⟨a, ha⟩ := hbij.2 (QuotientGroup.lift N χh hχhN)
  exact ⟨r a, fun p => DFunLike.congr_fun ha (p : P ⧸ N)⟩

variable {G : Type} [Group G]

open _root_.Classical in
private noncomputable def sgn (Hh : Subgroup G) (u : G) : ℂˣ := if u ∈ Hh then 1 else -1

private theorem sgn_eq_one_iff (Hh : Subgroup G) (u : G) : sgn Hh u = 1 ↔ u ∈ Hh := by
  unfold sgn
  split_ifs with h
  · simp [h]
  · simp only [h, iff_false]
    intro h1
    have := congrArg Units.val h1
    norm_num at this

private theorem sgn_one (Hh : Subgroup G) : sgn Hh 1 = 1 := (sgn_eq_one_iff Hh 1).mpr Hh.one_mem

private theorem sgn_mul_self (Hh : Subgroup G) (u : G) : sgn Hh u * sgn Hh u = 1 := by
  unfold sgn
  split_ifs <;> simp

private theorem commutator_mul_left (y x p : G) :
    ⁅y * x, p⁆ = y * ⁅x, p⁆ * y⁻¹ * ⁅y, p⁆ := by
  simp only [commutatorElement_def]; group

private theorem commutator_mul_right (y p p' : G) :
    ⁅y, p * p'⁆ = ⁅y, p⁆ * (p * ⁅y, p'⁆ * p⁻¹) := by
  simp only [commutatorElement_def]; group

variable [Finite G]

private theorem index_subgroupOf_eq_two {B Hh : Subgroup G} (hHB : Hh ≤ B)
    (hH2 : Nat.card Hh * 2 = Nat.card B) : (Hh.subgroupOf B).index = 2 := by
  have h1 := Subgroup.card_mul_index (Hh.subgroupOf B)
  have h2 : Nat.card (Hh.subgroupOf B) = Nat.card Hh :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHB).toEquiv
  rw [h2] at h1
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans hH2.symm)

private theorem sgn_mul {B Hh : Subgroup G} (hHB : Hh ≤ B) (hH2 : Nat.card Hh * 2 = Nat.card B)
    {u v : G} (hu : u ∈ B) (hv : v ∈ B) : sgn Hh (u * v) = sgn Hh u * sgn Hh v := by
  have key : u * v ∈ Hh ↔ (u ∈ Hh ↔ v ∈ Hh) :=
    Subgroup.mul_mem_iff_of_index_two (index_subgroupOf_eq_two hHB hH2)
      (a := ⟨u, hu⟩) (b := ⟨v, hv⟩)
  unfold sgn
  by_cases h1 : u ∈ Hh
  · by_cases h2 : v ∈ Hh
    · rw [if_pos h1, if_pos h2, if_pos (key.mpr (iff_of_true h1 h2)), mul_one]
    · rw [if_pos h1, if_neg h2, if_neg fun h => h2 ((key.mp h).mp h1), one_mul]
  · by_cases h2 : v ∈ Hh
    · rw [if_neg h1, if_pos h2, if_neg fun h => h1 ((key.mp h).mpr h2), mul_one]
    · rw [if_neg h1, if_neg h2, if_pos (key.mpr (iff_of_false h1 h2))]
      simp

theorem exists_inner_of_hyperplane {Q P B Hh : Subgroup G} (hPQ : P ≤ Q)
    (hQQ : ∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ ∈ B)
    (hBc : ∀ b ∈ B, ∀ x ∈ Q, b * x = x * b)
    (hHB : Hh ≤ B) (hH2 : Nat.card Hh * 2 = Nat.card B)
    (hker : ∀ x ∈ P, (∀ p ∈ P, ⁅x, p⁆ ∈ Hh) → x ∈ B) {y : G} (hy : y ∈ Q) :
    ∃ x ∈ P, ∀ p ∈ P, ⁅y * x, p⁆ ∈ Hh := by
  have hcen : ∀ b ∈ B, ∀ x ∈ Q, x * b * x⁻¹ = b := fun b hb x hx => by
    rw [← hBc b hb x hx]; group
  have h2 : ∀ z ∈ Q, ∀ p ∈ Q, ∀ p' ∈ Q, ⁅z, p * p'⁆ = ⁅z, p⁆ * ⁅z, p'⁆ :=
    fun z hz p hp p' hp' => by
      rw [commutator_mul_right, hcen _ (hQQ z hz p' hp') p hp]
  have h1 : ∀ z ∈ Q, ∀ x ∈ Q, ∀ p ∈ Q, ⁅z * x, p⁆ = ⁅x, p⁆ * ⁅z, p⁆ :=
    fun z hz x hx p hp => by
      rw [commutator_mul_left, hcen _ (hQQ x hx p hp) z hz]
  have hone : ∀ z ∈ Q, ∀ n ∈ B, ⁅z, n⁆ = 1 := fun z hz n hn =>
    commutatorElement_eq_one_iff_mul_comm.mpr (hBc n hn z hz).symm
  obtain ⟨x, hx⟩ := exists_eq_of_pairing_ker (B.subgroupOf P)
    (fun a b => Subgroup.mem_subgroupOf.mpr (hQQ _ (hPQ a.2) _ (hPQ b.2)))
    (fun x p => sgn Hh ⁅(x : G), (p : G)⁆) (fun p => sgn Hh ⁅y, (p : G)⁆)
    (fun x p p' => by
      rw [Subgroup.coe_mul, h2 _ (hPQ x.2) _ (hPQ p.2) _ (hPQ p'.2),
        sgn_mul hHB hH2 (hQQ _ (hPQ x.2) _ (hPQ p.2)) (hQQ _ (hPQ x.2) _ (hPQ p'.2))])
    (fun p p' => by
      rw [Subgroup.coe_mul, h2 _ hy _ (hPQ p.2) _ (hPQ p'.2),
        sgn_mul hHB hH2 (hQQ _ hy _ (hPQ p.2)) (hQQ _ hy _ (hPQ p'.2))])
    (fun x x' p => by
      rw [Subgroup.coe_mul, h1 _ (hPQ x.2) _ (hPQ x'.2) _ (hPQ p.2),
        sgn_mul hHB hH2 (hQQ _ (hPQ x'.2) _ (hPQ p.2)) (hQQ _ (hPQ x.2) _ (hPQ p.2)), mul_comm])
    (fun x n hn => by
      rw [hone _ (hPQ x.2) _ (Subgroup.mem_subgroupOf.mp hn), sgn_one])
    (fun n hn => by rw [hone _ hy _ (Subgroup.mem_subgroupOf.mp hn), sgn_one])
    (fun x h => Subgroup.mem_subgroupOf.mpr (hker x x.2 fun p hp =>
      (sgn_eq_one_iff Hh _).mp (h ⟨p, hp⟩)))
  refine ⟨x, x.2, fun p hp => ?_⟩
  rw [← sgn_eq_one_iff, h1 _ hy _ (hPQ x.2) _ (hPQ hp),
    sgn_mul hHB hH2 (hQQ _ (hPQ x.2) _ (hPQ hp)) (hQQ _ hy _ (hPQ hp)), hx ⟨p, hp⟩,
    sgn_mul_self]

end CFSG.RankThree.GF2n.Tim78
