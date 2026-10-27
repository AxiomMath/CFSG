module

public import CFSG.RankThree.GF2n.Smith81.S81A5Root
public import CFSG.RankThree.GF2n.Smith81.S81A5KerRho
public import CFSG.RankThree.GF2n.Smith81.S81A5Pure

open CFSG.RankThree.GF2n.Smith81.A5Cube
open Matrix exteriorPower

public section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

variable {K : Type*} [Field K]

private abbrev m5a_Wdiv (a : Fin 6 → K) : Submodule K (Cube K) :=
  Submodule.span K {ξ | ∃ v w : Fin 6 → K, ξ = ιMulti K 3 ![a, v, w]}

private theorem m5a_gen_mem (a v w : Fin 6 → K) : ιMulti K 3 ![a, v, w] ∈ m5a_Wdiv a :=
  Submodule.subset_span ⟨v, w, rfl⟩

private theorem m5a_swap_fst_snd (x y z : Fin 6 → K) :
    ιMulti K 3 ![y, x, z] = -ιMulti K 3 ![x, y, z] := by
  have h := (ιMulti K 3).map_swap ![x, y, z] (i := 0) (j := 1) (by decide)
  have h' : (![x, y, z] ∘ Equiv.swap (0 : Fin 3) 1) = ![y, x, z] := by
    funext i; fin_cases i <;> simp [Equiv.swap_apply_def]
  rw [h'] at h
  exact h

private theorem m5a_swap_snd_thd (x y z : Fin 6 → K) :
    ιMulti K 3 ![x, z, y] = -ιMulti K 3 ![x, y, z] := by
  have h := (ιMulti K 3).map_swap ![x, y, z] (i := 1) (j := 2) (by decide)
  have h' : (![x, y, z] ∘ Equiv.swap (1 : Fin 3) 2) = ![x, z, y] := by
    funext i; fin_cases i <;> simp [Equiv.swap_apply_def]
  rw [h'] at h
  exact h

private theorem m5a_cyc (x y z : Fin 6 → K) :
    ιMulti K 3 ![x, y, z] = ιMulti K 3 ![z, x, y] := by
  rw [m5a_swap_fst_snd x z y, m5a_swap_snd_thd x y z, neg_neg]

private theorem m5a_range_le {t : GL (Fin 6) K} {a f : Fin 6 → K}
    (ht : (t : Matrix (Fin 6) (Fin 6) K) = 1 + vecMulVec a f) :
    LinearMap.range (rho K t - 1) ≤ m5a_Wdiv a := by
  rw [LinearMap.range_le_iff_comap, ← top_le_iff, ← exteriorPower.ιMulti_span K 3 (Fin 6 → K),
    Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  show (rho K t - 1) (ιMulti K 3 v) ∈ m5a_Wdiv a
  have hv : ιMulti K 3 v = ιMulti K 3 ![v 0, v 1, v 2] := by
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [hv, LinearMap.sub_apply, Module.End.one_apply, rho_sub_one_ιMulti ht]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · exact Submodule.smul_mem _ _ (m5a_gen_mem a (v 1) (v 2))
  · rw [m5a_swap_fst_snd a (v 0) (v 2), smul_neg]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (m5a_gen_mem a (v 0) (v 2)))
  · rw [m5a_cyc (v 0) (v 1) a]
    exact Submodule.smul_mem _ _ (m5a_gen_mem a (v 0) (v 1))

private theorem m5a_rho_mul_apply (g h : GL (Fin 6) K) (ξ : Cube K) :
    rho K (g * h) ξ = rho K g (rho K h ξ) := by
  rw [rho_mul, Module.End.mul_apply]

private theorem m5a_rho_one : rho K (1 : GL (Fin 6) K) = 1 :=
  map_one (TauCeti.extPowerRep K 6 3)

private theorem m5a_rho_mem (g : GL (Fin 6) K) (a : Fin 6 → K) {ξ : Cube K}
    (hξ : ξ ∈ m5a_Wdiv a) :
    rho K g ξ ∈ m5a_Wdiv ((g : Matrix (Fin 6) (Fin 6) K).mulVec a) := by
  induction hξ using Submodule.span_induction with
  | mem η hη =>
    obtain ⟨v, w, rfl⟩ := hη
    rw [rho_ιMulti]
    have hfun : (fun i => (g : Matrix (Fin 6) (Fin 6) K).mulVec (![a, v, w] i)) =
        ![(g : Matrix (Fin 6) (Fin 6) K).mulVec a, (g : Matrix (Fin 6) (Fin 6) K).mulVec v,
          (g : Matrix (Fin 6) (Fin 6) K).mulVec w] := by
      funext i
      fin_cases i <;> rfl
    rw [hfun]
    exact m5a_gen_mem _ _ _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

private theorem m5a_coord_e_zero (i : Fin 6) (I : Set.powersetCard (Fin 6) 3)
    (hi : i ∉ I.val) (v w : Fin 6 → K) : coord K (ιMulti K 3 ![e K i, v, w]) I = 0 := by
  rw [coord_ιMulti]
  apply Matrix.det_eq_zero_of_row_eq_zero (0 : Fin 3)
  intro j
  have hmem : enum I j ∈ I.val :=
    (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem I (enum I j)).mp ⟨j, rfl⟩
  have hne : enum I j ≠ i := fun h => hi (by rw [← h]; exact hmem)
  simp [e, Pi.single_apply, hne]

private theorem m5a_coord_of_Wdiv_e (i : Fin 6) (I : Set.powersetCard (Fin 6) 3)
    (hi : i ∉ I.val) {η : Cube K} (hη : η ∈ m5a_Wdiv (e K i)) : coord K η I = 0 := by
  induction hη using Submodule.span_induction with
  | mem ξ hξ =>
    obtain ⟨v, w, rfl⟩ := hξ
    exact m5a_coord_e_zero i I hi v w
  | zero => exact coord_zero I
  | add x y _ _ hx hy => rw [coord_add, hx, hy, add_zero]
  | smul c x _ hx => rw [coord_smul, hx, mul_zero]

private theorem m5a_not_mem_of_tau_ne_two (I : Set.powersetCard (Fin 6) 3) (h : tau I ≠ 2) :
    (0 : Fin 6) ∉ I.val ∨ (1 : Fin 6) ∉ I.val := by
  by_contra hc
  simp only [not_or, not_not] at hc
  obtain ⟨h0, h1⟩ := hc
  apply h
  unfold tau
  have hF : I.val.filter (fun i : Fin 6 => i.val < 2) = {0, 1} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨-, hx⟩
      have hx' : x.val = 0 ∨ x.val = 1 := by omega
      rcases hx' with hx' | hx'
      · exact Or.inl (Fin.ext hx')
      · exact Or.inr (Fin.ext hx')
    · rintro (rfl | rfl)
      · exact ⟨h0, by decide⟩
      · exact ⟨h1, by decide⟩
  rw [hF]
  decide

theorem pure_of_range_inf_range_indep {x y : GL (Fin 6) K} {a b f g : Fin 6 → K}
    (hxa : (x : Matrix (Fin 6) (Fin 6) K) = 1 + vecMulVec a f)
    (hyb : (y : Matrix (Fin 6) (Fin 6) K) = 1 + vecMulVec b g)
    (hab : LinearIndependent K ![a, b]) :
    ∀ ξ ∈ LinearMap.range (rho K x - 1) ⊓ LinearMap.range (rho K y - 1), IsPure K ξ := by
  intro ξ hξ
  obtain ⟨hξx, hξy⟩ := Submodule.mem_inf.mp hξ
  have hA : ξ ∈ m5a_Wdiv a := m5a_range_le hxa hξx
  have hB : ξ ∈ m5a_Wdiv b := m5a_range_le hyb hξy
  obtain ⟨s, hsdet, hsa, hsb⟩ := exists_det_one_mulVec_two hab
  obtain ⟨sG, hsG⟩ : ∃ g : GL (Fin 6) K, (g : Matrix (Fin 6) (Fin 6) K) = s :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero s (by rw [hsdet]; exact one_ne_zero), rfl⟩
  have hη0 : rho K sG ξ ∈ m5a_Wdiv (e K 0) := by
    have h := m5a_rho_mem sG a hA
    rw [hsG, hsa] at h
    exact h
  have hη1 : rho K sG ξ ∈ m5a_Wdiv (e K 1) := by
    have h := m5a_rho_mem sG b hB
    rw [hsG, hsb] at h
    exact h
  have hsupp : rho K sG ξ ∈ supp K 2 := by
    show ∀ I : Set.powersetCard (Fin 6) 3, tau I ≠ 2 → coord K (rho K sG ξ) I = 0
    intro I hI
    rcases m5a_not_mem_of_tau_ne_two I hI with h0 | h1
    · exact m5a_coord_of_Wdiv_e 0 I h0 hη0
    · exact m5a_coord_of_Wdiv_e 1 I h1 hη1
  have hU : rho K sG ξ ∈ Usp K := supp_le_Vt (K := K) 2 hsupp
  have hP : IsPure K (rho K sG ξ) := isPure_of_mem_Usp hU
  have hback : rho K sG⁻¹ (rho K sG ξ) = ξ := by
    rw [← m5a_rho_mul_apply, inv_mul_cancel, m5a_rho_one, Module.End.one_apply]
  have h2 := hP.rho sG⁻¹
  rw [hback] at h2
  exact h2

end CFSG.RankThree.GF2n.Smith81.A5Cube
