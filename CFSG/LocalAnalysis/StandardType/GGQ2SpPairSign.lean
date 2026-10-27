module

public import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksCent
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Embed
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksCentExt
import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2Sp4TwoRootSix

public section

namespace CFSG.StandardType.GGQ2Frame.SpBlocks

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.SpJoin
  CFSG.StandardType.ClassicalPosition CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
  CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.LieType.Steinberg
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.SeitzReduction.F4Pilot
  Matrix
open CFSG.Open (StatedSp)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem mem_coords_union_iff {m : ℕ} {i j : Fin m} (y : Fin m ⊕ Fin m) :
    y ∈ coords i ∪ coords j ↔ Sum.elim id id y ∈ ({i, j} : Finset (Fin m)) := by
  rcases y with k | k
  · rw [inl_mem_union_iff]
    simp
  · rw [inr_mem_union_iff]
    simp

private theorem parClosed_coords_union {m : ℕ} (i j : Fin m) :
    ParClosed (coords i ∪ coords j) := by
  intro a ha
  rcases ha with ha | ha
  · exact Or.inl (parClosed_coords i a ha)
  · exact Or.inr (parClosed_coords j a ha)

omit [Finite K] [CharP K 2] in
theorem levi_pair_eq_range_spEmbed {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    levi (K := K) m ({i, j} : Finset (Fin m)) =
      (spEmbed (K := K) (pairMap i j) (pairMap_injective hij)).range := by
  rw [range_spEmbed (pairMap_injective hij), range_pairMap]
  ext g
  rw [mem_suppGroup_iff (parClosed_coords_union i j)]
  constructor
  · intro hg t ht x
    exact coe_apply_of_mem_levi hg x ((mem_coords_union_iff t).not.mp ht)
  · intro h
    refine mem_levi_of_col (K := K) fun x y hy => ?_
    exact h y ((mem_coords_union_iff y).not.mpr hy) x

omit [Finite K] [CharP K 2] in
private theorem rho_eq_shortBlock {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    rho i j hij = shortBlock K hij := by
  refine MonoidHom.ext fun x => ?_
  apply statedSp_ext
  rw [coe_rho, ← mat_apply, mat_shortBlock]
  rfl

omit [Finite K] [CharP K 2] in
theorem spEmbed_lam {m : ℕ} {i j : Fin m} (hij : i ≠ j)
    (x : SpecialLinearGroup (Fin 2) K) :
    spEmbed (pairMap i j) (pairMap_injective hij) (lam (1 : Fin 2) x) = lam j x := by
  calc
    spEmbed (pairMap i j) (pairMap_injective hij) (lam (1 : Fin 2) x) =
        spEmbed (pairMap i j) (pairMap_injective hij) (longBlock K 2 1 x) := by
      rw [show lam (1 : Fin 2) x = longBlock K 2 1 x from statedSp_ext rfl]
    _ = longBlock K m j x := DFunLike.congr_fun (spEmbed_comp_longBlock hij) x
    _ = lam j x := (show lam j x = longBlock K m j x from statedSp_ext rfl).symm

omit [Finite K] [CharP K 2] in
theorem spEmbed_rho {m : ℕ} {i j : Fin m} (hij : i ≠ j)
    (x : SpecialLinearGroup (Fin 2) K) :
    spEmbed (pairMap i j) (pairMap_injective hij)
      (rho (0 : Fin 2) (1 : Fin 2) (by decide) x) = rho i j hij x := by
  rw [rho_eq_shortBlock (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide),
    rho_eq_shortBlock (i := i) (j := j) hij]
  exact DFunLike.congr_fun (spEmbed_comp_shortBlock hij) x

omit [Finite K] in
private theorem sl2W_eq_upper_lower_upper :
    (sl2W : SpecialLinearGroup (Fin 2) K) = sl2Upper 1 * sl2Lower 1 * sl2Upper 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_sl2W,
    Sp.coe_sl2Upper, Sp.coe_sl2Lower]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq, CharTwo.add_self_eq_zero]

omit [Finite K] [CharP K 2] in
private theorem lam_sl2Upper {m : ℕ} (i : Fin m) (c : K) :
    lam i (sl2Upper c) = elt (.positiveLong i) c := by
  rw [show lam i (sl2Upper c) = longBlock K m i (sl2Upper c) from statedSp_ext rfl,
    longBlock_sl2Upper]

omit [Finite K] [CharP K 2] in
private theorem lam_sl2Lower {m : ℕ} (i : Fin m) (c : K) :
    lam i (sl2Lower c) = elt (.negativeLong i) c := by
  rw [show lam i (sl2Lower c) = longBlock K m i (sl2Lower c) from statedSp_ext rfl,
    longBlock_sl2Lower]

private theorem sign_short :
    Equiv.Perm.sign (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 2 4 * Equiv.swap 3 5) = -1 := by
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
    Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
  decide

private theorem sign_short_neg :
    Equiv.Perm.sign (Equiv.swap (0 : Fin 6) 5 * Equiv.swap 1 4 * Equiv.swap 2 3) = -1 := by
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
    Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
  decide

private theorem sign_lam_sl2W (hK : Nat.card K = 2) :
    Equiv.Perm.sign (sp4EquivPerm hK (lam (1 : Fin 2) sl2W)) = -1 := by
  have h1 : sp4EquivPerm hK (lam (1 : Fin 2) sl2W) =
      Equiv.swap 2 3 * Equiv.swap 2 4 * Equiv.swap 2 3 := by
    rw [sl2W_eq_upper_lower_upper]
    simp only [map_mul]
    rw [lam_sl2Upper, lam_sl2Lower]
    rw [sp4EquivPerm_elt_long, sp4EquivPerm_elt_long_neg]
  rw [h1, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
    Equiv.Perm.sign_swap (by decide)]
  decide

private theorem sign_rho_sl2W (hK : Nat.card K = 2) :
    Equiv.Perm.sign
      (sp4EquivPerm hK (rho (0 : Fin 2) (1 : Fin 2) (by decide) sl2W)) = -1 := by
  have h1 : sp4EquivPerm hK (rho (0 : Fin 2) (1 : Fin 2) (by decide) sl2W) =
      (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 2 4 * Equiv.swap 3 5) *
        (Equiv.swap 0 5 * Equiv.swap 1 4 * Equiv.swap 2 3) *
        (Equiv.swap 0 1 * Equiv.swap 2 4 * Equiv.swap 3 5) := by
    rw [rho_eq_shortBlock (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide),
      sl2W_eq_upper_lower_upper]
    simp only [map_mul]
    rw [shortBlock_sl2Upper, shortBlock_sl2Lower]
    rw [sp4EquivPerm_elt_short, sp4EquivPerm_elt_short_neg]
  rw [h1, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, sign_short, sign_short_neg]
  decide

omit [CharP K 2] in
private theorem mem_commutator_iff_sign (hK : Nat.card K = 2) (g : StatedSp 2 K) :
    g ∈ commutator (StatedSp 2 K) ↔
      Equiv.Perm.sign (sp4EquivPerm hK g) = 1 := by
  have hmap : (commutator (StatedSp 2 K)).map (sp4EquivPerm hK).toMonoidHom =
      alternatingGroup (Fin 6) := by
    rw [map_commutator_eq (f := (sp4EquivPerm hK).toMonoidHom),
      MonoidHom.range_eq_top.mpr (sp4EquivPerm hK).surjective, ← commutator_def,
      alternatingGroup.commutator_perm_eq (by simp)]
  constructor
  · intro hg
    have hm : sp4EquivPerm hK g ∈ (commutator (StatedSp 2 K)).map
        (sp4EquivPerm hK).toMonoidHom := ⟨g, hg, rfl⟩
    rw [hmap] at hm
    exact Equiv.Perm.mem_alternatingGroup.mp hm
  · intro hg
    have hm : sp4EquivPerm hK g ∈ (commutator (StatedSp 2 K)).map
        (sp4EquivPerm hK).toMonoidHom := by
      rw [hmap]
      exact Equiv.Perm.mem_alternatingGroup.mpr hg
    obtain ⟨x, hx, hxg⟩ := hm
    rw [(sp4EquivPerm hK).injective hxg] at hx
    exact hx

omit [Finite K] [CharP K 2] in
private theorem ycode_pair_eq_map_commutator (ζ : Multiplicative (ZMod 3) →*
      SpecialLinearGroup (Fin 2) K) {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    Ycode ζ m (.zero ({i, j} : Finset (Fin m))) =
      (commutator (StatedSp 2 K)).map
        (spEmbed (pairMap i j) (pairMap_injective hij)) := by
  change ⁅levi m ({i, j} : Finset (Fin m)), levi m ({i, j} : Finset (Fin m))⁆ = _
  rw [levi_pair_eq_range_spEmbed hij]
  exact (map_commutator_eq (f :=
    (spEmbed (pairMap i j) (pairMap_injective hij)))).symm

omit [CharP K 2] in
private theorem mem_ycode_pair_iff (hK : Nat.card K = 2)
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) {m : ℕ} {i j : Fin m}
    (hij : i ≠ j) (g : StatedSp 2 K) :
    spEmbed (pairMap i j) (pairMap_injective hij) g ∈
        Ycode ζ m (.zero ({i, j} : Finset (Fin m))) ↔
      Equiv.Perm.sign (sp4EquivPerm hK g) = 1 := by
  rw [ycode_pair_eq_map_commutator (ζ := ζ) hij]
  constructor
  · rintro ⟨x, hx, hxg⟩
    rw [spEmbed_injective (pairMap_injective hij) hxg] at hx
    exact (mem_commutator_iff_sign hK g).mp hx
  · intro hg
    exact ⟨g, (mem_commutator_iff_sign hK g).mpr hg, rfl⟩

private theorem sign_rho_mul_lam (hK : Nat.card K = 2) :
    Equiv.Perm.sign
      (sp4EquivPerm hK
        (rho (0 : Fin 2) (1 : Fin 2) (by decide) sl2W * lam (1 : Fin 2) sl2W)) = 1 := by
  rw [show sp4EquivPerm hK
        (rho (0 : Fin 2) (1 : Fin 2) (by decide) sl2W * lam (1 : Fin 2) sl2W) =
      sp4EquivPerm hK (rho (0 : Fin 2) (1 : Fin 2) (by decide) sl2W) *
        sp4EquivPerm hK (lam (1 : Fin 2) sl2W) from map_mul _ _ _,
    Equiv.Perm.sign_mul, sign_rho_sl2W hK, sign_lam_sl2W hK]
  decide

theorem rho_mul_lam_mem_ycode_pair (hK : Nat.card K = 2)
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) {m : ℕ} {i j : Fin m}
    (hij : i ≠ j) :
    rho i j hij sl2W * lam j sl2W ∈ Ycode ζ m (.zero {i, j}) := by
  rw [show rho i j hij sl2W * lam j sl2W =
      spEmbed (pairMap i j) (pairMap_injective hij)
        (rho (0 : Fin 2) (1 : Fin 2) (by decide) sl2W * lam (1 : Fin 2) sl2W) from by
    rw [map_mul, spEmbed_rho hij, spEmbed_lam hij]]
  exact (mem_ycode_pair_iff hK ζ hij _).mpr (sign_rho_mul_lam hK)

theorem lam_not_mem_ycode_pair (hK : Nat.card K = 2)
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) {m : ℕ} {i j : Fin m}
    (hij : i ≠ j) :
    lam j sl2W ∉ Ycode ζ m (.zero {i, j}) := by
  rw [show lam j sl2W = spEmbed (pairMap i j) (pairMap_injective hij)
      (lam (1 : Fin 2) sl2W) from (spEmbed_lam hij _).symm]
  rw [mem_ycode_pair_iff hK ζ hij]
  rw [sign_lam_sl2W hK]
  decide

end CFSG.StandardType.GGQ2Frame.SpBlocks

end
