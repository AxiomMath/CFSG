module

public import CFSG.RankThree.PartTwo.Sec11.Item116R2FaSL
public import CFSG.RankThree.PartTwo.Sec11.Item116R2FaSU
public import CFSG.RankThree.PartTwo.Sec4.Census.CoverSLThree46
public import CFSG.RankThree.PartTwo.KFacts.KS12SLCenter

public section

open CFSG CFSG.Assembly.LowTwoRank

namespace CFSG.RankThree.PartTwo.Sec11

theorem noncomm_in_sylow_of_mulEquiv {J Y : Type} [Group J] [Finite J] [Group Y] (e : J ≃* Y)
    (H : Subgroup Y) (hH : IsPGroup 3 H) {x y : Y} (hx : x ∈ H) (hy : y ∈ H) (hx3 : x ^ 3 = 1)
    (hy3 : y ^ 3 = 1) (hxy : x * y ≠ y * x) (S : Sylow 3 J) :
    ∃ x' ∈ (S : Subgroup J), ∃ y' ∈ (S : Subgroup J), x' ^ 3 = 1 ∧ y' ^ 3 = 1 ∧ x' * y' ≠ y' * x' := by
  refine exists_noncomm_in_sylow_of_isPGroup (H := H.map e.symm.toMonoidHom) (x := e.symm x)
    (y := e.symm y) (hH.map e.symm.toMonoidHom) (Subgroup.mem_map_of_mem _ hx)
    (Subgroup.mem_map_of_mem _ hy) ?_ ?_ ?_ S
  · rw [← map_pow, hx3, map_one]
  · rw [← map_pow, hy3, map_one]
  · intro h
    apply hxy
    apply e.symm.injective
    rw [map_mul, map_mul]
    exact h

section Certified



theorem fa_L3 {J : Type} [Group J] [Finite J] (hq : IsQuasisimple J)
    (hZ3 : IsPGroup 3 (Subgroup.center J)) (hZ : Subgroup.center J ≠ ⊥)
    {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e) (hb : p = 2 ∨ e ≤ 2)
    (hpi : Sec4.IsoLThreePi (J ⧸ Subgroup.center J) p e) (S : Sylow 3 J) :
    ∃ x ∈ (S : Subgroup J), ∃ y ∈ (S : Subgroup J), x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y ≠ y * x := by
  have hq3 : p ^ e % 3 = 1 ∨ p ^ e % 3 = 2 := by
    rcases hpi with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hEps := Sec4.Census.coverSLThree46 J hq hZ3 hZ p e he hb hpi
  obtain ⟨K, _, _, hK | hK⟩ := KFacts.isSLThreePiAt_of_isSLThreeEpsAt he hEps hq3 hZ
  · obtain ⟨hKc, hmod, ⟨φ⟩⟩ := hK
    obtain ⟨H, hH, x, hx, y, hy, hx3, hy3, hxy⟩ :=
      exists_heisenberg_statedSL (K := K) (by rw [hKc]; exact hmod)
    exact noncomm_in_sylow_of_mulEquiv φ H hH hx hy hx3 hy3 hxy S
  · obtain ⟨hKc, hmod, ⟨φ⟩⟩ := hK
    obtain ⟨H, hH, x, hx, y, hy, hx3, hy3, hxy⟩ :=
      exists_heisenberg_statedSU (K := K) (q := p ^ e) hKc hmod
    exact noncomm_in_sylow_of_mulEquiv φ H hH hx hy hx3 hy3 hxy S

end Certified

end CFSG.RankThree.PartTwo.Sec11
