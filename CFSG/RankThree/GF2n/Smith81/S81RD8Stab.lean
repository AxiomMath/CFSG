module

public import CFSG.RankThree.GF2n.Smith81.S81A5Root
public import CFSG.RankThree.GF2n.Smith81.S81BA5Form

open Matrix exteriorPower

public section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

variable {K : Type} [Field K]

theorem ι3_ne_zero_of_linearIndependent {v : Fin 3 → Fin 6 → K} (hv : LinearIndependent K v) :
    ιMulti K 3 v ≠ 0 := by
  intro h0
  obtain ⟨g, -, hgp⟩ := exists_gam_p0_eq_iota v hv
  rw [h0] at hgp
  have hp : p0 K = 0 := g.injective (by rw [map_zero]; exact hgp)
  exact p0_ne_zero hp

private theorem stabPure_shear (x y z : Fin 6 → K) (c d : K) :
    ιMulti K 3 ![x, y + c • x, z + d • x] = ιMulti K 3 ![x, y, z] := by
  rw [ι3_add_snd, ι3_smul_snd, ι3_eq_fst_snd, smul_zero, add_zero, ι3_add_thd, ι3_smul_thd,
    ι3_eq_fst_thd, smul_zero, add_zero]

private theorem stabPure_pivot {σ : GL (Fin 6) K} {w θ : Fin 6 → K}
    (hσ : (σ : Matrix (Fin 6) (Fin 6) K) = 1 + vecMulVec w θ)
    {t : Fin 3 → Fin 6 → K} (ht : LinearIndependent K t)
    (hfix : rho K σ (ιMulti K 3 t) = ιMulti K 3 t) (h0 : θ ⬝ᵥ t 0 ≠ 0) :
    w ∈ Submodule.span K (Set.range t) := by
  have hte : t = ![t 0, t 1, t 2] := by
    funext i
    fin_cases i <;> rfl
  have hι : ιMulti K 3 t = ιMulti K 3 ![t 0, t 1, t 2] := congrArg (ιMulti K 3) hte
  obtain ⟨c1, hc1⟩ : ∃ c : K, c = -(θ ⬝ᵥ t 1) / (θ ⬝ᵥ t 0) := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ c : K, c = -(θ ⬝ᵥ t 2) / (θ ⬝ᵥ t 0) := ⟨_, rfl⟩
  obtain ⟨y1, hy1⟩ : ∃ y : Fin 6 → K, y = t 1 + c1 • t 0 := ⟨_, rfl⟩
  obtain ⟨y2, hy2⟩ : ∃ y : Fin 6 → K, y = t 2 + c2 • t 0 := ⟨_, rfl⟩
  have hd1 : θ ⬝ᵥ y1 = 0 := by
    rw [hy1, dotProduct_add, dotProduct_smul, smul_eq_mul, hc1, div_mul_cancel₀ _ h0,
      add_neg_cancel]
  have hd2 : θ ⬝ᵥ y2 = 0 := by
    rw [hy2, dotProduct_add, dotProduct_smul, smul_eq_mul, hc2, div_mul_cancel₀ _ h0,
      add_neg_cancel]
  have hι1 : ιMulti K 3 ![t 0, y1, y2] = ιMulti K 3 t := by
    rw [hι, hy1, hy2]
    exact stabPure_shear (t 0) (t 1) (t 2) c1 c2
  have hne : ιMulti K 3 ![t 0, y1, y2] ≠ 0 := by
    rw [hι1]
    exact ι3_ne_zero_of_linearIndependent ht
  have hli : LinearIndependent K ![t 0, y1, y2] := linearIndependent_of_ιMulti_ne_zero hne
  have hli12 : LinearIndependent K ![y1, y2] := (linearIndependent_finCons.mp hli).1
  have hfix1 : rho K σ (ιMulti K 3 ![t 0, y1, y2]) = ιMulti K 3 ![t 0, y1, y2] := by
    rw [hι1]
    exact hfix
  have hz : ιMulti K 3 ![w, y1, y2] = 0 := by
    have hrel := rho_sub_one_ιMulti hσ (t 0) y1 y2
    simp only [hfix1, sub_self, hd1, hd2, zero_smul, add_zero] at hrel
    rcases smul_eq_zero.mp hrel.symm with h | h
    · exact absurd h h0
    · exact h
  have hw2 : w ∈ Submodule.span K (Set.range ![y1, y2]) := by
    by_contra hw2
    have hlin : LinearIndependent K ![w, y1, y2] := linearIndependent_finCons.mpr ⟨hli12, hw2⟩
    exact ι3_ne_zero_of_linearIndependent hlin hz
  have hy1mem : y1 ∈ Submodule.span K (Set.range t) := by
    rw [hy1]
    exact Submodule.add_mem _ (Submodule.subset_span (Set.mem_range_self (1 : Fin 3)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self (0 : Fin 3))))
  have hy2mem : y2 ∈ Submodule.span K (Set.range t) := by
    rw [hy2]
    exact Submodule.add_mem _ (Submodule.subset_span (Set.mem_range_self (2 : Fin 3)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self (0 : Fin 3))))
  have hle : Submodule.span K (Set.range ![y1, y2]) ≤ Submodule.span K (Set.range t) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hy1mem
    · exact hy2mem
  exact hle hw2

theorem stab_pure {σ : GL (Fin 6) K} {w θ : Fin 6 → K}
    (hσ : (σ : Matrix (Fin 6) (Fin 6) K) = 1 + vecMulVec w θ)
    {s : Fin 3 → Fin 6 → K} (hs : LinearIndependent K s)
    (hfix : rho K σ (ιMulti K 3 s) = ιMulti K 3 s) :
    (∀ i, θ ⬝ᵥ s i = 0) ∨ w ∈ Submodule.span K (Set.range s) := by
  by_cases hall : ∀ i, θ ⬝ᵥ s i = 0
  · exact Or.inl hall
  right
  obtain ⟨i, hi⟩ := not_forall.mp hall
  obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by
    fin_cases i <;> simp
  · exact stabPure_pivot hσ hs hfix hi
  · have hsw : ιMulti K 3 (s ∘ Equiv.swap (0 : Fin 3) 1) = -ιMulti K 3 s :=
      (ιMulti K 3).map_swap s (by decide)
    have hli : LinearIndependent K (s ∘ Equiv.swap (0 : Fin 3) 1) :=
      hs.comp _ (Equiv.injective _)
    have hfx : rho K σ (ιMulti K 3 (s ∘ Equiv.swap (0 : Fin 3) 1)) =
        ιMulti K 3 (s ∘ Equiv.swap (0 : Fin 3) 1) := by
      rw [hsw, map_neg, hfix]
    have h0 : θ ⬝ᵥ (s ∘ Equiv.swap (0 : Fin 3) 1) 0 ≠ 0 := by
      simpa [Equiv.swap_apply_left] using hi
    have hpiv := stabPure_pivot hσ hli hfx h0
    rwa [EquivLike.range_comp] at hpiv
  · have hsw : ιMulti K 3 (s ∘ Equiv.swap (0 : Fin 3) 2) = -ιMulti K 3 s :=
      (ιMulti K 3).map_swap s (by decide)
    have hli : LinearIndependent K (s ∘ Equiv.swap (0 : Fin 3) 2) :=
      hs.comp _ (Equiv.injective _)
    have hfx : rho K σ (ιMulti K 3 (s ∘ Equiv.swap (0 : Fin 3) 2)) =
        ιMulti K 3 (s ∘ Equiv.swap (0 : Fin 3) 2) := by
      rw [hsw, map_neg, hfix]
    have h0 : θ ⬝ᵥ (s ∘ Equiv.swap (0 : Fin 3) 2) 0 ≠ 0 := by
      simpa [Equiv.swap_apply_left] using hi
    have hpiv := stabPure_pivot hσ hli hfx h0
    rwa [EquivLike.range_comp] at hpiv

end CFSG.RankThree.GF2n.Smith81.A5Cube
