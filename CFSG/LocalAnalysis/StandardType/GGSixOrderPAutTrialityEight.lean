module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTrialityDefs
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTrialityEightLin
public import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613C3Frame
public import CFSG.RankThree.PartOne.AUTSL.OmegaDickson

public section

namespace CFSG.StandardType

open Module CFSG.StandardType.Triality CFSG.StandardType.D4Rank CFSG.StandardType.L613C3
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL
  QuadraticMap

namespace OrdPTriEight

variable {K : Type} [Field K]

theorem even_finrank_range_omRep_sub_one [CharP K 2] (g : Om8 K) :
    Even (finrank K (LinearMap.range (omRep g - 1))) := by
  have hnd := (regular_coordinateQuadPlus 4 K (by norm_num)).1
  have hmem : matrixLinearIso (g : GL (Fin (2 * 4)) K) ∈
      CFSG.RankThree.Classical2.orthDerived (coordinateQuadPlus 4 K) := by
    rw [← map_matrixDerived_linearIso]
    exact ⟨g, g.2, rfl⟩
  exact (CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hnd hmem).2

theorem mem_eigenspace_omRep {z : Om8 K} {l : K} {u : Fin (2 * 4) → K} :
    u ∈ (omRep z).eigenspace l ↔ act z u = l • u :=
  Module.End.mem_eigenspace_iff

theorem map_le_eigenspace {z : Om8 K} {N : Module.End K (Fin (2 * 4) → K)}
    (hNZ : N * omRep z = omRep z * N) (l : K) :
    ((omRep z).eigenspace l).map N ≤ (omRep z).eigenspace l := by
  intro y hy
  obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hy
  rw [Module.End.mem_eigenspace_iff] at hw ⊢
  rw [← Module.End.mul_apply, ← hNZ, Module.End.mul_apply, hw, map_smul]

theorem finrank_eigenspace_le_four {z : Om8 K} {l : K} (hl : l * l ≠ 1) :
    finrank K ((omRep z).eigenspace l) ≤ 4 := by
  have hnd := (regular_coordinateQuadPlus 4 K (by norm_num)).1
  have h := two_mul_finrank_le_of_isotropic hnd (U := (omRep z).eigenspace l) fun a ha b hb =>
    L613C3.polar_eq_zero_of_eigen (mem_eigenspace_omRep.1 ha) (mem_eigenspace_omRep.1 hb) hl
  rw [Module.finrank_fin_fun] at h
  omega

theorem pow_four_apply_eigen_eq_zero {z : Om8 K} {N : Module.End K (Fin (2 * 4) → K)}
    (hNZ : N * omRep z = omRep z * N) {m : ℕ} (hN : N ^ m = 0) {l : K} (hl : l * l ≠ 1)
    {u : Fin (2 * 4) → K} (hu : act z u = l • u) : (N ^ 4) u = 0 :=
  pow_apply_eq_zero_of_finrank_le (map_le_eigenspace hNZ l) (m := m)
    (fun y _ => by rw [hN, LinearMap.zero_apply]) (finrank_eigenspace_le_four hl)
    (mem_eigenspace_omRep.2 hu)

section Eigen

variable [CharP K 2] {ω : K} {z : Om8 K}

theorem exists_eigen_of_ne_one (hω : ω ^ 2 + ω + 1 = 0) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    (∃ u, act z u = ω • u ∧ u ≠ 0) ∨ ∃ u, act z u = ω ^ 2 • u ∧ u ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  refine hz1 (eq_one_of_omFixDim ?_)
  have htop : LinearMap.ker (omRep z - 1) = ⊤ := by
    refine eq_top_iff.2 fun v _ => mem_ker_iff_act.2 ?_
    have hv : v = eproj z 1 v := by
      have h := eq_eproj_add (z := z) hω v
      rwa [h1 _ (act_eproj hz3 (omega_cube hω) v), h2 _ (act_eproj hz3 (omega_sq_cube hω) v),
        add_zero, add_zero] at h
    have he := act_eproj hz3 (one_pow 3) v
    rw [one_smul, ← hv] at he
    exact he
  show finrank K (LinearMap.ker (omRep z - 1)) = 8
  rw [htop, finrank_top, Module.finrank_fin_fun]

theorem exists_omega_sq_eigen (hω : ω ^ 2 + ω + 1 = 0) (hz3 : z ^ 3 = 1)
    {u : Fin (2 * 4) → K} (hu : act z u = ω • u) (hu0 : u ≠ 0) :
    ∃ w, act z w = ω ^ 2 • w ∧ w ≠ 0 := by
  have hnd := (regular_coordinateQuadPlus 4 K (by norm_num)).1
  by_contra hcon
  push Not at hcon
  refine hu0 (hnd.1 u fun y => ?_)
  change polar (coordinateQuadPlus 4 K) u y = 0
  rw [eq_eproj_add (z := z) hω y, polar_add_right, polar_add_right,
    L613C3.polar_eq_zero_of_eigen hu (act_eproj hz3 (one_pow 3) y)
      (by rw [mul_one]; exact omega_ne_one hω),
    L613C3.polar_eq_zero_of_eigen hu (act_eproj hz3 (omega_cube hω) y) (omega_mul_self_ne_one hω),
    hcon _ (act_eproj hz3 (omega_sq_cube hω) y), polar_zero_right, add_zero, add_zero]

theorem exists_omega_eigen (hω : ω ^ 2 + ω + 1 = 0) (hz3 : z ^ 3 = 1)
    {u : Fin (2 * 4) → K} (hu : act z u = ω ^ 2 • u) (hu0 : u ≠ 0) :
    ∃ w, act z w = ω • w ∧ w ≠ 0 := by
  have hnd := (regular_coordinateQuadPlus 4 K (by norm_num)).1
  by_contra hcon
  push Not at hcon
  refine hu0 (hnd.1 u fun y => ?_)
  change polar (coordinateQuadPlus 4 K) u y = 0
  rw [eq_eproj_add (z := z) hω y, polar_add_right, polar_add_right,
    L613C3.polar_eq_zero_of_eigen hu (act_eproj hz3 (one_pow 3) y)
      (by rw [mul_one]; exact omega_sq_ne_one hω),
    hcon _ (act_eproj hz3 (omega_cube hω) y), polar_zero_right,
    L613C3.polar_eq_zero_of_eigen hu (act_eproj hz3 (omega_sq_cube hω) y)
      (omega_sq_mul_sq_ne_one hω), add_zero, add_zero]

theorem injective_eigenvalues (hω : ω ^ 2 + ω + 1 = 0) :
    Function.Injective ![(1 : K), ω, ω ^ 2] := by
  have h12 : (1 : K) ≠ ω := fun h => omega_ne_one hω h.symm
  have h13 : (1 : K) ≠ ω ^ 2 := fun h => omega_sq_ne_one hω h.symm
  have h23 : ω ≠ ω ^ 2 := fun h => by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    exact one_ne_zero (show (1 : K) = 0 by linear_combination hω + h - ω * h2)
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first
    | rfl
    | exact absurd hij h12 | exact absurd hij.symm h12
    | exact absurd hij h13 | exact absurd hij.symm h13
    | exact absurd hij h23 | exact absurd hij.symm h23

theorem three_le_finrank_ker (hω : ω ^ 2 + ω + 1 = 0) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    {N : Module.End K (Fin (2 * 4) → K)} (hNZ : N * omRep z = omRep z * N) {m : ℕ}
    (hN : N ^ m = 0) (hN4 : N ^ 4 ≠ 0) : 3 ≤ finrank K (LinearMap.ker N) := by
  obtain ⟨v, hv⟩ : ∃ v, (N ^ 4) v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hN4 (LinearMap.ext hcon)
  have hu1 : (N ^ 4) (eproj z 1 v) ≠ 0 := by
    intro h0
    apply hv
    rw [eq_eproj_add (z := z) hω v, map_add, map_add, h0,
      pow_four_apply_eigen_eq_zero hNZ hN (omega_mul_self_ne_one hω)
        (act_eproj hz3 (omega_cube hω) v),
      pow_four_apply_eigen_eq_zero hNZ hN (omega_sq_mul_sq_ne_one hω)
        (act_eproj hz3 (omega_sq_cube hω) v), add_zero, add_zero]
  have hker : ∀ (l : K) (u : Fin (2 * 4) → K), act z u = l • u → u ≠ 0 →
      ∃ w, act z w = l • w ∧ w ≠ 0 ∧ N w = 0 := by
    intro l u hu hu0
    obtain ⟨w, hw, hw0, hNw⟩ := exists_ne_zero_apply_eq_zero (map_le_eigenspace hNZ l) m u
      (mem_eigenspace_omRep.2 hu) (by rw [hN, LinearMap.zero_apply]) hu0
    exact ⟨w, mem_eigenspace_omRep.1 hw, hw0, hNw⟩
  obtain ⟨u2, hu2, hu20, u3, hu3, hu30⟩ : ∃ u2, act z u2 = ω • u2 ∧ u2 ≠ 0 ∧
      ∃ u3, act z u3 = ω ^ 2 • u3 ∧ u3 ≠ 0 := by
    rcases exists_eigen_of_ne_one hω hz3 hz1 with ⟨u, hu, hu0⟩ | ⟨u, hu, hu0⟩
    · obtain ⟨w, hw, hw0⟩ := exists_omega_sq_eigen hω hz3 hu hu0
      exact ⟨u, hu, hu0, w, hw, hw0⟩
    · obtain ⟨w, hw, hw0⟩ := exists_omega_eigen hω hz3 hu hu0
      exact ⟨w, hw, hw0, u, hu, hu0⟩
  obtain ⟨w1, hw1, hw10, hNw1⟩ :=
    hker 1 _ (act_eproj hz3 (one_pow 3) v) fun h => hu1 (by rw [h, map_zero])
  obtain ⟨w2, hw2, hw20, hNw2⟩ := hker ω u2 hu2 hu20
  obtain ⟨w3, hw3, hw30, hNw3⟩ := hker (ω ^ 2) u3 hu3 hu30
  have hli : LinearIndependent K ![w1, w2, w3] := by
    refine Module.End.eigenvectors_linearIndependent' (omRep z) ![(1 : K), ω, ω ^ 2]
      (injective_eigenvalues hω) _ fun i => ?_
    fin_cases i
    · exact Module.End.hasEigenvector_iff.2 ⟨mem_eigenspace_omRep.2 hw1, hw10⟩
    · exact Module.End.hasEigenvector_iff.2 ⟨mem_eigenspace_omRep.2 hw2, hw20⟩
    · exact Module.End.hasEigenvector_iff.2 ⟨mem_eigenspace_omRep.2 hw3, hw30⟩
  have hle : Submodule.span K (Set.range ![w1, w2, w3]) ≤ LinearMap.ker N := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact LinearMap.mem_ker.2 hNw1
    · exact LinearMap.mem_ker.2 hNw2
    · exact LinearMap.mem_ker.2 hNw3
  have h3 := finrank_span_eq_card hli
  rw [Fintype.card_fin] at h3
  have h4 := Submodule.finrank_mono hle
  omega

theorem pow_four_eq_one_of_commute (hω : ω ^ 2 + ω + 1 = 0) {x : Om8 K} (hz3 : z ^ 3 = 1)
    (hz1 : z ≠ 1) (hxz : x * z = z * x) (hx8 : x ^ 8 = 1) : x ^ 4 = 1 := by
  by_contra hx4
  have hNZ : (omRep x - 1) * omRep z = omRep z * (omRep x - 1) := by
    rw [sub_mul, mul_sub, one_mul, mul_one, ← map_mul omRep x z, hxz, map_mul]
  have hN8 : (omRep x - 1) ^ 8 = 0 := by
    rw [sub_one_pow_eight, ← map_pow omRep x 8, hx8, map_one, sub_self]
  have hN4 : (omRep x - 1) ^ 4 = omRep (x ^ 4) - 1 := by
    rw [sub_one_pow_four, map_pow omRep x 4]
  have hN4ne : (omRep x - 1) ^ 4 ≠ 0 := by
    intro h
    refine hx4 (eq_one_of_omFixDim ?_)
    show finrank K (LinearMap.ker (omRep (x ^ 4) - 1)) = 8
    rw [← hN4, h, LinearMap.ker_zero, finrank_top, Module.finrank_fin_fun]
  have hE1 := even_finrank_range_omRep_sub_one x
  have hE4 := even_finrank_range_omRep_sub_one (x ^ 4)
  rw [← hN4] at hE4
  have hR4 : LinearMap.range ((omRep x - 1) ^ 4) ≠ ⊥ := fun h =>
    hN4ne (LinearMap.range_eq_bot.1 h)
  have hchain : finrank K (LinearMap.range ((omRep x - 1) ^ 4)) + 3 ≤
      finrank K (LinearMap.range (omRep x - 1)) := by
    have e : LinearMap.range ((omRep x - 1) ^ 4) =
        (LinearMap.range (omRep x - 1)).map ((omRep x - 1) ^ 3) := by
      rw [← LinearMap.range_comp, ← Module.End.mul_eq_comp, ← pow_succ]
    rw [e] at hR4 ⊢
    exact finrank_map_pow_add_le LinearMap.map_le_range (m := 8)
      (fun y _ => by rw [hN8, LinearMap.zero_apply]) 3 hR4
  have hpos := Submodule.one_le_finrank_iff.2 hR4
  have hker := three_le_finrank_ker hω hz3 hz1 hNZ hN8 hN4ne
  have hrk := LinearMap.finrank_range_add_finrank_ker (omRep x - 1)
  rw [Module.finrank_fin_fun] at hrk
  obtain ⟨r, hr⟩ := hE4
  obtain ⟨s, hs⟩ := hE1
  omega

end Eigen

end OrdPTriEight

namespace OrdPTri

theorem ggD4ThreeCentralizerEightInput_holds : GGD4ThreeCentralizerEightInput := by
  intro K _ _ _ hK3 z x hz3 hz1 hxz hx
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ : ∃ ω : Kˣ, orderOf ω = 3 :=
    exists_prime_orderOf_dvd_card' 3 (by rw [Nat.card_units]; exact hK3)
  have hω3 : (ω : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hω, pow_orderOf_eq_one, Units.val_one]
  have hω1 : (ω : K) ≠ 1 := fun h => by
    rw [show ω = 1 from Units.ext h, orderOf_one] at hω
    exact absurd hω (by norm_num)
  have hω' : (ω : K) ^ 2 + ω + 1 = 0 := by
    have h : ((ω : K) - 1) * ((ω : K) ^ 2 + ω + 1) = 0 := by linear_combination hω3
    exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hω1)
  have h4 := OrdPTriEight.pow_four_eq_one_of_commute hω' hz3 hz1 hxz
    (by rw [← hx]; exact pow_orderOf_eq_one x)
  have hd := orderOf_dvd_of_pow_eq_one h4
  rw [hx] at hd
  exact absurd hd (by norm_num)

end OrdPTri

end CFSG.StandardType
