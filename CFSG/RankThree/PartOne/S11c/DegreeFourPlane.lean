module

public import CFSG.RankThree.PartOne.S11c.DegreeFourPlaneCore
public import CFSG.RankThree.PartOne.S11c.DegreeSixPrimes

public section

namespace CFSG.RankThree.PartOne

theorem odd_characteristic_degree_four_special_linear_plane_centralizes_two_subgroup
    {k : Type*} [Field k] (h2 : (2 : k) ≠ 0) {n : ℕ} (hn : n ≤ 4)
    {Q E : Subgroup (GL (Fin n) k)} [Finite Q] (hQ : IsPGroup 2 Q) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hEdet : ∀ x ∈ E, (x : Matrix (Fin n) (Fin n) k).det = 1)
    (hEel : CFSG.IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2)
    (hEQ : E ≤ Subgroup.normalizer (Q : Set (GL (Fin n) k))) : ⁅E, Q⁆ = ⊥ := by
  have : IsElementaryAbelian p E := hEel
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hEcard]; exact pow_ne_zero 2 hp.ne_zero)
  by_cases hp5 : 5 < p
  · exact odd_characteristic_degree_six_primes_above_five_centralize_two_subgroups h2
      (by omega) hQ hp hp5 (IsElementaryAbelian.isPGroup p E) hEQ
  · have hp5' : p = 5 := by
      have h4 : p ≠ 4 := by
        rintro rfl
        norm_num at hp
      omega
    subst hp5'
    have : Fact (Nat.Prime 5) := ⟨hp⟩
    let ψ : GL (Fin n) k →* (Module.End k (Fin n → k))ˣ :=
      (Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := k)).toMonoidHom
    have hψinj : Function.Injective ψ := Matrix.GeneralLinearGroup.toLin.injective
    have : Finite (Q.map ψ) := Finite.of_surjective
      (fun x : Q => (⟨ψ x.1, Subgroup.mem_map_of_mem ψ x.2⟩ : Q.map ψ)) (by
        rintro ⟨_, x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩)
    have : IsElementaryAbelian 5 (E.map ψ) := IsElementaryAbelian.map ψ
    have hEcard' : Nat.card (E.map ψ) = 5 ^ 2 := by
      rw [Subgroup.card_map_of_injective hψinj, hEcard]
    have hdet' : ∀ x ∈ E.map ψ,
        LinearMap.det ((x : (Module.End k (Fin n → k))ˣ) : Module.End k (Fin n → k)) = 1 := by
      rintro _ ⟨y, hy, rfl⟩
      have h : ((ψ y : (Module.End k (Fin n → k))ˣ) : Module.End k (Fin n → k)) =
          Matrix.toLin' (y : Matrix (Fin n) (Fin n) k) := rfl
      rw [h, LinearMap.det_toLin']
      exact hEdet y hy
    have hEQ' : E.map ψ ≤ Subgroup.normalizer ((Q.map ψ : Subgroup _) : Set _) :=
      (Subgroup.map_mono hEQ).trans (Subgroup.le_normalizer_map ψ)
    have hmain := DegreeFourInduction.plane_five h2 (V := Fin n → k)
      (by rw [Module.finrank_fin_fun]; exact hn) (hQ.map ψ) hEcard' hdet' hEQ'
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact hψinj (by
      rw [map_mul, map_mul]
      exact (hmain (ψ u) (Subgroup.mem_map_of_mem ψ hu) (ψ q) (Subgroup.mem_map_of_mem ψ hq)).symm)

end CFSG.RankThree.PartOne
