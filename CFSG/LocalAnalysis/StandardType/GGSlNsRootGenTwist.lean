module

public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenWeyl
public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenTorus

public section

namespace CFSG.StandardType.SlNsRootGen

open Matrix Polynomial CoordSL CFSG.RankThree.CALinearPlane CFSG.Assembly TableB Multiplicative

section Coord

variable {s p : ℕ}

@[expose] def sswapMap (i j : Fin s) (t : Fin s → ZMod p) : Fin s → ZMod p :=
  negMap j (swapMap i j (negMap j t))

private theorem negMap_single (i m : Fin s) (c : ZMod p) :
    negMap i (Pi.single m c) = Pi.single m (if m = i then -c else c) := by
  funext x
  by_cases hx : x = i
  · rw [hx]
    by_cases hm : m = i
    · rw [hm]
      simp [negMap, Function.update_apply]
    · simp [negMap, Function.update_apply, Pi.single_apply, hm, Ne.symm hm]
  · by_cases hm : m = i
    · rw [hm]
      simp [negMap, Function.update_apply, Pi.single_apply, hx, Ne.symm hx]
    · simp [negMap, Function.update_apply, Pi.single_apply, hx, Ne.symm hx, hm, Ne.symm hm]

private theorem swapMap_single (i j m : Fin s) (c : ZMod p) :
    swapMap i j (Pi.single m c) = Pi.single (Equiv.swap i j m) c := by
  funext x
  by_cases hx : x = Equiv.swap i j m
  · subst hx
    rw [swapMap, Function.comp_apply, Equiv.swap_apply_self, Pi.single_eq_same,
      Pi.single_eq_same]
  · have hx' : Equiv.swap i j x ≠ m := by
      intro h
      apply hx
      calc x = Equiv.swap i j (Equiv.swap i j x) := (Equiv.swap_apply_self i j x).symm
        _ = Equiv.swap i j m := by rw [h]
    rw [swapMap, Function.comp_apply, Pi.single_eq_of_ne hx', Pi.single_eq_of_ne hx]

private theorem sswapMap_apply_left {i j : Fin s} (hij : i ≠ j) (t : Fin s → ZMod p) :
    sswapMap i j t i = -t j := by
  simp [sswapMap, negMap, swapMap, Function.update_apply, hij, Ne.symm hij,
    Equiv.swap_apply_left]

private theorem sswapMap_apply_right {i j : Fin s} (hij : i ≠ j) (t : Fin s → ZMod p) :
    sswapMap i j t j = -t i := by
  simp [sswapMap, negMap, swapMap, Function.update_apply, hij, Ne.symm hij,
    Equiv.swap_apply_right]

private theorem sswapMap_apply_of_ne {i j m : Fin s} (hmi : m ≠ i) (hmj : m ≠ j)
    (t : Fin s → ZMod p) : sswapMap i j t m = t m := by
  simp [sswapMap, negMap, swapMap, Function.update_apply, hmi, hmj,
    Equiv.swap_apply_of_ne_of_ne hmi hmj]

private theorem sswapMap_coeff {i j m : Fin s} (hij : i ≠ j) :
    (if Equiv.swap i j m = j then -((if m = j then (-1 : ZMod p) else 1))
        else (if m = j then -1 else 1)) =
      if m = i ∨ m = j then -1 else 1 := by
  by_cases hmi : m = i
  · rw [hmi]
    simp [Equiv.swap_apply_left, hij]
  · by_cases hmj : m = j
    · rw [hmj]
      simp [Equiv.swap_apply_right, hij]
    · have h1 : Equiv.swap i j m ≠ j := by
        intro h
        have h2 := congrArg (Equiv.swap i j) h
        rw [Equiv.swap_apply_self, Equiv.swap_apply_right] at h2
        exact hmi h2
      simp [h1, hmi, hmj]

private theorem sswapMap_single {i j m : Fin s} (hij : i ≠ j) :
    sswapMap i j (Pi.single m (1 : ZMod p)) =
      Pi.single (Equiv.swap i j m) (if m = i ∨ m = j then -1 else 1) := by
  rw [sswapMap, negMap_single, swapMap_single, negMap_single, sswapMap_coeff hij]

private theorem sswapMap_self (i : Fin s) (t : Fin s → ZMod p) : sswapMap i i t = t := by
  funext m
  by_cases hm : m = i
  · rw [hm]
    simp [sswapMap, negMap, swapMap, Function.update_apply, Equiv.swap_apply_left]
  · have hmi : Equiv.swap i i m = m := Equiv.swap_apply_of_ne_of_ne hm hm
    simp [sswapMap, negMap, swapMap, Function.update_apply, hm, hmi]

theorem sswapMap_sswapMap (i j : Fin s) (t : Fin s → ZMod p) :
    sswapMap i j (sswapMap i j t) = t := by
  by_cases hij : i = j
  · subst hij
    simp only [sswapMap_self]
  · funext m
    by_cases hmi : m = i
    · rw [hmi]
      rw [sswapMap_apply_left hij (sswapMap i j t), sswapMap_apply_right hij t, neg_neg]
    · by_cases hmj : m = j
      · rw [hmj]
        rw [sswapMap_apply_right hij (sswapMap i j t), sswapMap_apply_left hij t, neg_neg]
      · rw [sswapMap_apply_of_ne hmi hmj (sswapMap i j t), sswapMap_apply_of_ne hmi hmj t]

theorem sswapMap_eq_self_iff {i j : Fin s} (hij : i ≠ j) {t : Fin s → ZMod p} :
    sswapMap i j t = t ↔ t i = -t j := by
  constructor
  · intro h
    have h1 := congrFun h i
    rw [sswapMap_apply_left hij] at h1
    exact h1.symm
  · intro h
    funext m
    by_cases hmi : m = i
    · rw [hmi]
      rw [sswapMap_apply_left hij]
      exact h.symm
    · by_cases hmj : m = j
      · rw [hmj]
        rw [sswapMap_apply_right hij, h, neg_neg]
      · rw [sswapMap_apply_of_ne hmi hmj]

theorem card_fixed_sswapMap {i j : Fin s} (hij : i ≠ j) :
    Nat.card {t // sswapMap (p := p) i j t = t} * p = p ^ s := by
  let f : (Fin s → ZMod p) →+ ZMod p :=
    AddMonoidHom.mk' (fun t => t i + t j) fun t u => by
      simp only [Pi.add_apply]
      abel
  have hsurj : Function.Surjective f := by
    intro c
    refine ⟨Pi.single i c, ?_⟩
    simp [f, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hij)]
  have hiff : ∀ t, t ∈ f.ker ↔ sswapMap i j t = t := by
    intro t
    rw [AddMonoidHom.mem_ker, sswapMap_eq_self_iff hij]
    exact ⟨fun h => eq_neg_iff_add_eq_zero.mpr (by simpa [f] using h),
      fun h => by simpa [f] using (eq_neg_iff_add_eq_zero.mp h)⟩
  have hcard := AddSubgroup.card_ker_mul_card_of_surjective hsurj (f := f)
  have hcard' : Nat.card ↥f.ker * p = Nat.card (Fin s → ZMod p) := by
    simpa [Nat.card_zmod] using hcard
  have hker : Nat.card ↥f.ker = Nat.card {t // sswapMap i j t = t} :=
    Nat.card_congr (Equiv.subtypeEquivRight hiff)
  rw [← hker, hcard', Nat.card_fun, Nat.card_zmod, Nat.card_fin]

variable [Fact p.Prime]

private theorem sswapMap_single_coeff_ne_zero {i j m : Fin s} :
    (if m = i ∨ m = j then (-1 : ZMod p) else 1) ≠ 0 := by
  have hp1 : (1 : ZMod p) ≠ 0 := by
    intro h
    exact (Fact.out : p.Prime).not_dvd_one
      ((ZMod.natCast_eq_zero_iff 1 p).mp (by simpa using h))
  split_ifs with h
  · intro h0
    exact hp1 (neg_eq_zero.mp h0)
  · exact hp1

theorem pair_eq_of_sswapMap_eq {i j k l : Fin s} (hij : i ≠ j) (hkl : k ≠ l)
    (h : sswapMap (p := p) i j = sswapMap k l) : ({i, j} : Finset (Fin s)) = {k, l} := by
  have hind : ∀ m : Fin s, Equiv.swap i j m = Equiv.swap k l m := by
    intro m
    have h1 := congrFun h (Pi.single m 1)
    rw [sswapMap_single hij, sswapMap_single hkl] at h1
    have h1' := congrFun h1 (Equiv.swap i j m)
    rw [Pi.single_eq_same] at h1'
    by_contra hne
    rw [Pi.single_eq_of_ne hne] at h1'
    exact sswapMap_single_coeff_ne_zero h1'
  have hswap : Equiv.swap i j = Equiv.swap k l := Equiv.ext hind
  have hsupp := congrArg Equiv.Perm.support hswap
  rwa [Equiv.Perm.support_swap hij, Equiv.Perm.support_swap hkl] at hsupp

theorem sswapMap_ne_swapMap (hp2 : p ≠ 2) {i j : Fin s} (hij : i ≠ j) (k l : Fin s) :
    sswapMap (p := p) i j ≠ swapMap k l := by
  intro h
  have h1 := congrFun (congrFun h (Pi.single i 1)) j
  rw [sswapMap_apply_right hij (Pi.single i 1), Pi.single_eq_same] at h1
  rw [swapMap, Function.comp_apply, Pi.single_apply] at h1
  have hp2' : 2 < p := by
    have hle := (Fact.out : p.Prime).two_le
    omega
  haveI : Fact (2 < p) := ⟨hp2'⟩
  split_ifs at h1
  · exact (CharP.neg_one_ne_one (ZMod p) p) h1
  · exact one_ne_zero (neg_eq_zero.mp h1)

end Coord

section Twist

variable {K : Type} [Field K] [Fintype K] (g : K[X]) [Fact (Irreducible g)] {n s r p : ℕ}
  [NeZero p] [Fact p.Prime]

@[expose] noncomputable def twistPairBlock [CharP K 2] (hζ : AdjoinRoot.root g ^ p = 1)
    (hpK : p ∣ Nat.card K + 1) (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    (i j : Fin s) : Subgroup (SpecialLinearGroup (Fin n) K) :=
  (pairBlock g ε i j).map (MulAut.conj (negSL g hζ hpK ε j)).toMonoidHom

variable {g}

theorem exists_sswap_mem_twistPairBlock [CharP K 2]
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) (hC : (rootMat g).det = 1)
    (hCp : rootMat g ^ p = 1) (hζ : AdjoinRoot.root g ^ p = 1) (hpK : p ∣ Nat.card K + 1)
    (i j : Fin s) :
    ∃ w ∈ twistPairBlock g hζ hpK ε i j, ∀ t : Fin s → ZMod p,
      w * torusSL ε hC hCp (ofAdd t) * w⁻¹ = torusSL ε hC hCp (ofAdd (sswapMap i j t)) := by
  obtain ⟨w₀, hw₀mem, hw₀⟩ := exists_swap_mem_pairBlock (g := g) ε hC hCp i j
  let N : SpecialLinearGroup (Fin n) K := negSL g hζ hpK ε j
  have hN : N * N = 1 := negSL_mul_self g hζ hpK ε j
  have hNinv : N⁻¹ = N := inv_eq_of_mul_eq_one_right hN
  have hNconj : ∀ u : Fin s → ZMod p,
      N * torusSL ε hC hCp (ofAdd u) * N⁻¹ =
        torusSL ε hC hCp (ofAdd (negMap j u)) :=
    fun u => negSL_conj g hC hCp hζ hpK ε j u
  refine ⟨N * w₀ * N⁻¹, ?_, ?_⟩
  · have hmem : MulAut.conj N w₀ ∈
        (pairBlock g ε i j).map (MulAut.conj N).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj N).toMonoidHom hw₀mem
    simpa [twistPairBlock, N, MulAut.conj_apply] using hmem
  · intro t
    have hstep : N⁻¹ * torusSL ε hC hCp (ofAdd t) * N =
        torusSL ε hC hCp (ofAdd (negMap j t)) := by
      simpa only [hNinv] using hNconj t
    calc
      (N * w₀ * N⁻¹) * torusSL ε hC hCp (ofAdd t) * (N * w₀ * N⁻¹)⁻¹
          = N * w₀ * (N⁻¹ * torusSL ε hC hCp (ofAdd t) * N) * w₀⁻¹ * N⁻¹ := by
            group
      _ = N * w₀ * torusSL ε hC hCp (ofAdd (negMap j t)) * w₀⁻¹ * N⁻¹ := by
            rw [hstep]
      _ = N * (w₀ * torusSL ε hC hCp (ofAdd (negMap j t)) * w₀⁻¹) * N⁻¹ := by
            group
      _ = N * torusSL ε hC hCp (ofAdd (swapMap i j (negMap j t))) * N⁻¹ := by
            rw [hw₀ (negMap j t)]
      _ = torusSL ε hC hCp (ofAdd (negMap j (swapMap i j (negMap j t)))) := hNconj _
      _ = torusSL ε hC hCp (ofAdd (sswapMap i j t)) := rfl

end Twist

end CFSG.StandardType.SlNsRootGen

end
