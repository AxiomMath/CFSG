module

public import CFSG.RankThree.PartOne.S11c.DegreeSixPrimesCore

public section

namespace CFSG.RankThree.PartOne

theorem odd_characteristic_degree_six_primes_above_five_centralize_two_subgroups
    {k : Type*} [Field k] (h2 : (2 : k) ≠ 0) {n : ℕ} (hn : n ≤ 6)
    {Q P : Subgroup (GL (Fin n) k)} [Finite Q] (hQ : IsPGroup 2 Q) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 < p) [Finite P] (hP : IsPGroup p P)
    (hPQ : P ≤ Subgroup.normalizer (Q : Set (GL (Fin n) k))) : ⁅P, Q⁆ = ⊥ := by
  let ψ : GL (Fin n) k →* (Module.End k (Fin n → k))ˣ :=
    (Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := k)).toMonoidHom
  have hψinj : Function.Injective ψ := Matrix.GeneralLinearGroup.toLin.injective
  have : Finite (Q.map ψ) := Finite.of_surjective
    (fun x : Q => (⟨ψ x.1, Subgroup.mem_map_of_mem ψ x.2⟩ : Q.map ψ)) (by
      rintro ⟨_, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩)
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  obtain ⟨m, hm⟩ := hP ⟨u, hu⟩
  have huN : u ^ p ^ m = 1 := congrArg Subtype.val hm
  have hcore := DegreeSixInduction.commuteStmt_of_finrank_le_six h2 hp hp5 n (Fin n → k)
    (Module.finrank_fin_fun k) hn
  have h := hcore (Q.map ψ) (hQ.map ψ) (ψ u)
    (Subgroup.le_normalizer_map ψ (Subgroup.mem_map_of_mem ψ (hPQ hu))) m
    (by rw [← map_pow, huN, map_one]) (ψ q) (Subgroup.mem_map_of_mem ψ hq)
  exact hψinj (by rw [map_mul, map_mul]; exact h.symm)

end CFSG.RankThree.PartOne
