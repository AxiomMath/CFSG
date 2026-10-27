module

public import CFSG.RankThree.CentralCover.SteinbergBNCoverPairingCore

public section

namespace CFSG.RankThree.CentralCover

open CFSG.Assembly
open scoped MatrixGroups

theorem commute_of_mem_closure_range {T ι : Type*} [Group T] {h : ι → T} {z : T}
    (hz : ∀ i, Commute z (h i)) {x : T} (hx : x ∈ Subgroup.closure (Set.range h)) :
    Commute z x := by
  have hle : Subgroup.closure (Set.range h) ≤ Subgroup.centralizer {z} :=
    (Subgroup.closure_le _).2 (by
      rintro _ ⟨i, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.2 (hz i).eq.symm)
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hx)).symm

theorem commuting_SL2_inversion_package {Y H K : Type*} [Group Y] [Group H] [Field K]
    {φ : Y →* H} (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y) {m : ℕ}
    (ι : Fin m → SL(2, K) →* H) (hι : ∀ i, Function.Injective (ι i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B : SL(2, K), ι i A * ι j B = ι j B * ι i A) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {h w : SL(2, K)} (hord : orderOf h = p)
    (hinv : w * h * w⁻¹ = h⁻¹) :
    IsElemAbelian p (Subgroup.closure (Set.range fun i => ι i h)) ∧
      Nat.card (Subgroup.closure (Set.range fun i => ι i h)) = p ^ m ∧
      ∀ x ∈ (Subgroup.closure (Set.range fun i => ι i h)).comap φ,
        ∀ y ∈ (Subgroup.closure (Set.range fun i => ι i h)).comap φ, x * y = y * x := by
  have hcommh : ∀ i j, Commute (ι i h) (ι j h) := fun i j => by
    by_cases hij : i = j
    · rw [hij]
    · exact hcomm i j hij h h
  have hordi : ∀ i, orderOf (ι i h) = p := fun i => by rw [orderOf_injective _ (hι i), hord]
  have hinvi : ∀ i, ι i w * ι i h * (ι i w)⁻¹ = (ι i h)⁻¹ := fun i => by
    rw [← map_inv, ← map_mul, ← map_mul, hinv, map_inv]
  have hfixi : ∀ i j, i ≠ j → ι i w * ι j h * (ι i w)⁻¹ = ι j h := fun i j hij => by
    rw [hcomm i j hij w h, mul_inv_cancel_right]
  have := inversion_basis_package hφ hker hp hp2 (fun i => ι i h) (fun i => ι i w) hcommh hordi
    hinvi hfixi
  rwa [Fintype.card_fin] at this

end CFSG.RankThree.CentralCover
