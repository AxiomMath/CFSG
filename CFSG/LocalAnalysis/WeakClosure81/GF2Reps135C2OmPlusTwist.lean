module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusCurtis
public import CFSG.RankThree.GF2n.Smith81.S81QGraphRoot

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis CFSG.LieType.Universal.Spin CFSG.LieType.RootSystem
open CFSG.RankThree.GF2n.Smith81.D6Spin (graphSpin flipAt graphSpin_longRoot swapIso
  swapIso_swapIso cliffMap_cliffMap)

section Generic

variable {G : Type*} [Group G] [Finite G] {B : Type*} {M : CoxeterMatrix B} {W : Type*}
  [Group W] {cs : CoxeterSystem M W} {p : ℕ} {D : CurtisDatum G cs p}
  {k V : Type*} [Field k] [AddCommGroup V] [Module k V] {ρ : Representation k G V}

theorem mu_eq_of_twist [Fact p.Prime] [CharP k p] (hρ : IsSimpleRep ρ) {y : V} {χ : G → k}
    {μ : B → k} (ht : D.IsCurtisType ρ y χ μ) (γ : G ≃* G) (π : B → B)
    (hU : ∀ u ∈ D.U, γ.symm u ∈ D.U) (hX : ∀ s x, x ∈ D.X s ↔ γ x ∈ D.X (π s))
    (hn : ∀ s, γ (D.n s) = D.n (π s)) (T : V ≃ₗ[k] V)
    (hT : ∀ (g : G) (v : V), T (ρ g v) = ρ (γ g) (T v)) (s : B) : μ (π s) = μ s := by
  obtain ⟨hy, hy0, hχ, hμ⟩ := ht
  have ht0 : D.IsCurtisType ρ y χ μ := ⟨hy, hy0, hχ, hμ⟩
  have hTy : T y ∈ D.fixU ρ := by
    rw [D.mem_fixU]
    intro u hu
    calc ρ u (T y) = T (ρ (γ.symm u) y) := by
          rw [hT (γ.symm u) y, γ.apply_symm_apply]
      _ = T y := by
          rw [(D.mem_fixU (ρ := ρ) (v := y)).mp hy (γ.symm u) (hU u hu)]
  obtain ⟨c, hc⟩ := D.fixU_eq_smul hρ ht0 hTy
  have hc0 : c ≠ 0 := by
    rintro hc0
    exact hy0 (T.injective (by rw [hc, hc0, zero_smul, map_zero]))
  let e : D.X s ≃ D.X (π s) :=
    { toFun := fun x => ⟨γ (x : G), (hX s (x : G)).mp x.2⟩
      invFun := fun z => ⟨γ.symm (z : G),
        (hX s (γ.symm (z : G))).mpr (by rw [γ.apply_symm_apply]; exact z.2)⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun z => Subtype.ext (by simp) }
  have hsum : T (D.heckeT ρ s y) = D.heckeT ρ (π s) (T y) := by
    have hfin_s : Fintype (D.X s) := Fintype.ofFinite (D.X s)
    have hfin_π : Fintype (D.X (π s)) := Fintype.ofFinite (D.X (π s))
    rw [D.heckeT_apply ρ s y, map_sum, D.heckeT_apply ρ (π s) (T y)]
    refine Fintype.sum_equiv e _ _ (fun x => ?_)
    have hγ : γ ((x : G) * D.n s) = γ (x : G) * D.n (π s) := by
      rw [map_mul, hn]
    have hAB : γ (x : G) * D.n (π s) = (↑(e x) : G) * D.n (π s) := rfl
    exact (hT ((x : G) * D.n s) y).trans (by rw [hγ, hAB])
  have hTs : T (D.heckeT ρ s y) = μ s • T y := by rw [hμ s, map_smul]
  have hmain : μ s • T y = D.heckeT ρ (π s) (T y) := by rw [← hTs, hsum]
  rw [hc, map_smul, hμ (π s), smul_smul, smul_smul, mul_comm c (μ (π s))] at hmain
  have hzero : (μ s * c - μ (π s) * c) • y = 0 := by
    rw [sub_smul, hmain, sub_self]
  have h1 : μ s * c - μ (π s) * c = 0 := by
    rcases smul_eq_zero.mp hzero with h | h
    · exact h
    · exact absurd h hy0
  have h2 : μ s * c = μ (π s) * c := sub_eq_zero.mp h1
  exact (mul_right_cancel₀ hc0 h2).symm

end Generic

@[expose] def omGraphSwap {n : ℕ} (hn : 2 ≤ n) : Equiv.Perm (Fin n) :=
  Equiv.swap ⟨n - 2, by omega⟩ ⟨n - 1, by omega⟩

variable {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem omPlusTwist_graphSpin_graphSpin {n : ℕ} {K : Type} [Field K] (i₀ : Fin n)
    (x : spinGroup (quadPlus n K)) :
    graphSpin n K i₀ (graphSpin n K i₀ x) = x := by
  apply Subtype.ext
  show CliffordAlgebra.map (swapIso n K i₀) (CliffordAlgebra.map (swapIso n K i₀)
    (x : CliffordAlgebra (quadPlus n K))) = x
  exact cliffMap_cliffMap _ (swapIso_swapIso n K i₀) _

private lemma omPlusTwist_val_rootIdxD {n : ℕ} (k : Fin n) :
    (rootIdxD n k).val = if k.val + 1 < n then k.val else n - 2 := by
  by_cases h : k.val + 1 < n
  · rw [rootIdxD_of_lt n h]
    simp [h]
  · rw [val_rootIdxD_of_not_lt n h]
    simp [h]

private lemma omPlusTwist_val_rootIdxD' {n : ℕ} (k : Fin n) :
    (rootIdxD' n k).val = if k.val + 1 < n then k.val + 1 else n - 1 := by
  by_cases h : k.val + 1 < n
  · rw [rootIdxD'_of_lt n h]
    simp [h]
  · rw [val_rootIdxD'_of_not_lt n h]
    simp [h]

private lemma omPlusTwist_rootIdxD_omGraphSwap {n : ℕ} (hn : 3 ≤ n) (k : Fin n) :
    rootIdxD n (omGraphSwap (by omega) k) = rootIdxD n k ∧
      rootIdxD' n (omGraphSwap (by omega) k) = rootIdxD' n k := by
  by_cases h2 : k.val = n - 2
  · have hk : k = ⟨n - 2, by omega⟩ := Fin.ext h2
    rw [hk]
    have hπ : omGraphSwap (by omega) (⟨n - 2, by omega⟩ : Fin n) = ⟨n - 1, by omega⟩ := by
      rw [omGraphSwap, Equiv.swap_apply_left]
    rw [hπ]
    constructor
    · apply Fin.ext
      rw [omPlusTwist_val_rootIdxD, omPlusTwist_val_rootIdxD]
      simp only
      split_ifs <;> omega
    · apply Fin.ext
      rw [omPlusTwist_val_rootIdxD', omPlusTwist_val_rootIdxD']
      simp only
      split_ifs <;> omega
  · by_cases h1 : k.val = n - 1
    · have hk : k = ⟨n - 1, by omega⟩ := Fin.ext h1
      rw [hk]
      have hπ : omGraphSwap (by omega) (⟨n - 1, by omega⟩ : Fin n) = ⟨n - 2, by omega⟩ := by
        rw [omGraphSwap, Equiv.swap_apply_right]
      rw [hπ]
      constructor
      · apply Fin.ext
        rw [omPlusTwist_val_rootIdxD, omPlusTwist_val_rootIdxD]
        simp only
        split_ifs <;> omega
      · apply Fin.ext
        rw [omPlusTwist_val_rootIdxD', omPlusTwist_val_rootIdxD']
        simp only
        split_ifs <;> omega
    · have hπ : omGraphSwap (by omega) k = k := by
        rw [omGraphSwap, Equiv.swap_apply_of_ne_of_ne]
        · intro h
          exact h2 (congrArg Fin.val h)
        · intro h
          exact h1 (congrArg Fin.val h)
      rw [hπ]
      exact ⟨rfl, rfl⟩

private lemma omPlusTwist_rootIdxD_ne_last {n : ℕ} (hn : 3 ≤ n) (k : Fin n) :
    rootIdxD n k ≠ ⟨n - 1, by omega⟩ := by
  intro h
  have hv : (rootIdxD n k).val = n - 1 := by rw [h]
  by_cases hk : k.val + 1 < n
  · rw [rootIdxD_of_lt n hk] at hv
    omega
  · rw [val_rootIdxD_of_not_lt n hk] at hv
    omega

private lemma omPlusTwist_flipAt_rootIdxD_true {n : ℕ} (hn : 3 ≤ n) (k : Fin n) :
    flipAt n ⟨n - 1, by omega⟩ (rootIdxD n k) true = true := by
  rw [flipAt, if_neg (omPlusTwist_rootIdxD_ne_last hn k)]

private lemma omPlusTwist_flipAt_rootIdxD'_rootSignD_two {n : ℕ} (hn : 3 ≤ n) {k : Fin n}
    (h2 : k.val = n - 2) :
    flipAt n ⟨n - 1, by omega⟩ (rootIdxD' n k) (rootSignD n k) =
      rootSignD n (omGraphSwap (by omega) k) := by
  have hk : k = ⟨n - 2, by omega⟩ := Fin.ext h2
  rw [hk]
  have hπ : omGraphSwap (by omega) (⟨n - 2, by omega⟩ : Fin n) = ⟨n - 1, by omega⟩ := by
    rw [omGraphSwap, Equiv.swap_apply_left]
  have hidx : rootIdxD' n (⟨n - 2, by omega⟩ : Fin n) = ⟨n - 1, by omega⟩ := by
    apply Fin.ext
    rw [omPlusTwist_val_rootIdxD']
    simp only
    split_ifs <;> omega
  have hs : rootSignD n (⟨n - 2, by omega⟩ : Fin n) = false := by
    simp only [rootSignD, decide_eq_false_iff_not]
    omega
  have ht : rootSignD n (⟨n - 1, by omega⟩ : Fin n) = true := by
    simp only [rootSignD, decide_eq_true_eq]
    omega
  rw [hπ, hidx, hs, ht, flipAt]
  simp

private lemma omPlusTwist_flipAt_rootIdxD'_rootSignD_ne_two {n : ℕ} (hn : 3 ≤ n) {k : Fin n}
    (h2 : k.val ≠ n - 2) :
    flipAt n ⟨n - 1, by omega⟩ (rootIdxD' n k) (rootSignD n k) =
      rootSignD n (omGraphSwap (by omega) k) := by
  by_cases h1 : k.val = n - 1
  · have hk : k = ⟨n - 1, by omega⟩ := Fin.ext h1
    rw [hk]
    have hπ : omGraphSwap (by omega) (⟨n - 1, by omega⟩ : Fin n) = ⟨n - 2, by omega⟩ := by
      rw [omGraphSwap, Equiv.swap_apply_right]
    have hidx : rootIdxD' n (⟨n - 1, by omega⟩ : Fin n) = ⟨n - 1, by omega⟩ := by
      apply Fin.ext
      rw [omPlusTwist_val_rootIdxD']
      simp only
      split_ifs <;> omega
    have hs : rootSignD n (⟨n - 1, by omega⟩ : Fin n) = true := by
      simp only [rootSignD, decide_eq_true_eq]
      omega
    have ht : rootSignD n (⟨n - 2, by omega⟩ : Fin n) = false := by
      simp only [rootSignD, decide_eq_false_iff_not]
      omega
    rw [hπ, hidx, hs, ht, flipAt]
    simp
  · have hπ : omGraphSwap (by omega) k = k := by
      rw [omGraphSwap, Equiv.swap_apply_of_ne_of_ne]
      · intro h
        exact h2 (congrArg Fin.val h)
      · intro h
        exact h1 (congrArg Fin.val h)
    have hlt : k.val + 1 < n := by omega
    have hidx : rootIdxD' n k = ⟨k.val + 1, hlt⟩ := rootIdxD'_of_lt n hlt
    have hne : (⟨k.val + 1, hlt⟩ : Fin n) ≠ ⟨n - 1, by omega⟩ := by
      intro h
      have hv : k.val + 1 = n - 1 := congrArg Fin.val h
      omega
    have hsign : rootSignD n k = false := rootSignD_of_lt n hlt
    rw [hπ, hidx, hsign]
    rw [flipAt, if_neg hne]

private lemma omPlusTwist_flipAt_rootIdxD'_rootSignD {n : ℕ} (hn : 3 ≤ n) (k : Fin n) :
    flipAt n ⟨n - 1, by omega⟩ (rootIdxD' n k) (rootSignD n k) =
      rootSignD n (omGraphSwap (by omega) k) := by
  by_cases h2 : k.val = n - 2
  · exact omPlusTwist_flipAt_rootIdxD'_rootSignD_two hn h2
  · exact omPlusTwist_flipAt_rootIdxD'_rootSignD_ne_two hn h2

private lemma omPlusTwist_flipAt_not {n : ℕ} (hn : 3 ≤ n) (a : Fin n) (s : Bool) :
    flipAt n ⟨n - 1, by omega⟩ a (!s) = !(flipAt n ⟨n - 1, by omega⟩ a s) := by
  by_cases h : a = ⟨n - 1, by omega⟩ <;> simp [flipAt, h]

private lemma omPlusTwist_longRoot_congr {n : ℕ} {K : Type} [Field K] (hn : 3 ≤ n)
    {i j i' j' : Fin n} {hij : i ≠ j} {hij' : i' ≠ j'} {s t s' t' : Bool} {c : K}
    (hi : i = i') (hj : j = j') (hs : s = s') (ht : t = t') :
    (plusFrame n K hn).longRoot hij s t (.ofAdd c) =
      (plusFrame n K hn).longRoot hij' s' t' (.ofAdd c) := by
  apply Subtype.ext
  rw [HypFrame.coe_longRoot, HypFrame.coe_longRoot, hi, hj, hs, ht]

private theorem omPlusTwist_graphSpin_rootD {n : ℕ} {K : Type} [Field K] (hn : 3 ≤ n)
    (k : Fin n) (x : Multiplicative K) :
    graphSpin n K ⟨n - 1, by omega⟩ (rootD K hn k x) =
      rootD K hn (omGraphSwap (by omega) k) x := by
  unfold rootD
  rw [show x = Multiplicative.ofAdd (Multiplicative.toAdd x) from rfl]
  rw [graphSpin_longRoot]
  refine omPlusTwist_longRoot_congr hn ?_ ?_ ?_ ?_
  · exact (omPlusTwist_rootIdxD_omGraphSwap hn k).1.symm
  · exact (omPlusTwist_rootIdxD_omGraphSwap hn k).2.symm
  · exact omPlusTwist_flipAt_rootIdxD_true hn k
  · exact omPlusTwist_flipAt_rootIdxD'_rootSignD hn k

private theorem omPlusTwist_graphSpin_negRootD {n : ℕ} {K : Type} [Field K] (hn : 3 ≤ n)
    (k : Fin n) (x : Multiplicative K) :
    graphSpin n K ⟨n - 1, by omega⟩ (negRootD K hn k x) =
      negRootD K hn (omGraphSwap (by omega) k) x := by
  unfold negRootD
  rw [show x = Multiplicative.ofAdd (Multiplicative.toAdd x) from rfl]
  rw [graphSpin_longRoot]
  refine omPlusTwist_longRoot_congr hn ?_ ?_ ?_ ?_
  · exact (omPlusTwist_rootIdxD_omGraphSwap hn k).2.symm
  · exact (omPlusTwist_rootIdxD_omGraphSwap hn k).1.symm
  · rw [omPlusTwist_flipAt_not hn, omPlusTwist_flipAt_rootIdxD'_rootSignD hn]
  · rw [flipAt, if_neg (omPlusTwist_rootIdxD_ne_last hn k)]

private lemma omPlusTwist_boolSign_flipAt_mul {n : ℕ} (hn : 3 ≤ n) (a : Fin n) (u : Bool) :
    boolSign (flipAt n ⟨n - 1, by omega⟩ a u) * ((n : ℤ) - 1 - a) =
      boolSign u * ((n : ℤ) - 1 - a) := by
  by_cases ha : a = ⟨n - 1, by omega⟩
  · subst ha
    have hz : ((n : ℤ) - 1 - (⟨n - 1, by omega⟩ : Fin n)) = 0 := by
      simp only
      omega
    rw [flipAt, if_pos rfl, hz]
    simp
  · rw [flipAt, if_neg ha]

private theorem omPlusTwist_graphSpin_mem_posUnipotent {n : ℕ} {K : Type} [Field K]
    (hn : 3 ≤ n) {u : spinGroup (quadPlus n K)}
    (hu : u ∈ CFSG.LieType.Steinberg.posUnipotent (plusDatum n K hn)) :
    graphSpin n K ⟨n - 1, by omega⟩ u ∈
      CFSG.LieType.Steinberg.posUnipotent (plusDatum n K hn) := by
  have key : CFSG.LieType.Steinberg.posUnipotent (plusDatum n K hn) ≤
      (CFSG.LieType.Steinberg.posUnipotent (plusDatum n K hn)).comap
        (graphSpin n K ⟨n - 1, by omega⟩).toMonoidHom := by
    unfold CFSG.LieType.Steinberg.posUnipotent
    refine iSup₂_le fun γ hγ => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    obtain ⟨i, j, hij, s, t, hstd, hgrp⟩ := exists_plusRootGroup_eq (K := K) hn hγ.1
    obtain ⟨γ', hγ'mem, hγ'std⟩ := exists_mem_rootsD_toStdD_eq n hij
      (boolSign_eq_one_or_eq_neg_one (flipAt n ⟨n - 1, by omega⟩ i s))
      (boolSign_eq_one_or_eq_neg_one (flipAt n ⟨n - 1, by omega⟩ j t))
    have hht : CFSG.LieType.Steinberg.ht γ' = CFSG.LieType.Steinberg.ht γ := by
      calc CFSG.LieType.Steinberg.ht γ'
          = boolSign (flipAt n ⟨n - 1, by omega⟩ i s) * ((n : ℤ) - 1 - i) +
              boolSign (flipAt n ⟨n - 1, by omega⟩ j t) * ((n : ℤ) - 1 - j) :=
            ht_of_toStdD_eq_add n (by omega) hγ'std
        _ = boolSign s * ((n : ℤ) - 1 - i) + boolSign t * ((n : ℤ) - 1 - j) := by
            rw [omPlusTwist_boolSign_flipAt_mul hn i s,
              omPlusTwist_boolSign_flipAt_mul hn j t]
        _ = CFSG.LieType.Steinberg.ht γ := (ht_of_toStdD_eq_add n (by omega) hstd).symm
    have hpos : 0 < CFSG.LieType.Steinberg.ht γ' := by
      rw [hht]
      exact hγ.2
    have hle : plusRootGroup n K hn γ' ≤
        CFSG.LieType.Steinberg.posUnipotent (plusDatum n K hn) := by
      unfold CFSG.LieType.Steinberg.posUnipotent
      exact le_iSup_of_le γ' (le_iSup_of_le ⟨hγ'mem, hpos⟩ le_rfl)
    have hroot : (plusDatum n K hn).rootGroup γ = plusRootGroup n K hn γ := rfl
    rw [hroot, hgrp]
    refine Subgroup.map_le_iff_le_comap.mpr fun x hx => ?_
    rw [Subgroup.mem_comap]
    obtain ⟨c, rfl⟩ := hx
    rw [show (plusFrame n K hn).longRoot hij s t c =
      (plusFrame n K hn).longRoot hij s t (.ofAdd (Multiplicative.toAdd c)) from rfl]
    have hcoe : ∀ y, (graphSpin n K ⟨n - 1, by omega⟩).toMonoidHom y =
        graphSpin n K ⟨n - 1, by omega⟩ y := fun y => rfl
    rw [hcoe, graphSpin_longRoot]
    refine hle ?_
    rw [plusRootGroup_eq hn hij _ _ hγ'std]
    exact ⟨c, rfl⟩
  exact Subgroup.mem_comap.mp (key hu)

theorem graphSpin_symm_mem_U_omPlus (hn : 3 ≤ n) {u : spinGroup (quadPlus n K)}
    (hu : u ∈ (omPlusCurtisDatum n K hn).U) :
    (graphSpin n K ⟨n - 1, by omega⟩).symm u ∈ (omPlusCurtisDatum n K hn).U := by
  have hsymm : (graphSpin n K ⟨n - 1, by omega⟩).symm =
      graphSpin n K ⟨n - 1, by omega⟩ := by
    refine MulEquiv.ext fun x => ?_
    apply (graphSpin n K ⟨n - 1, by omega⟩).injective
    rw [MulEquiv.apply_symm_apply, omPlusTwist_graphSpin_graphSpin]
  rw [hsymm]
  rw [omPlusCurtisDatum_U hn] at hu ⊢
  exact omPlusTwist_graphSpin_mem_posUnipotent hn hu

theorem mem_X_iff_graphSpin_mem_omPlus (hn : 3 ≤ n) (s : Fin n)
    (x : spinGroup (quadPlus n K)) :
    x ∈ (omPlusCurtisDatum n K hn).X s ↔
      graphSpin n K ⟨n - 1, by omega⟩ x ∈
        (omPlusCurtisDatum n K hn).X (omGraphSwap (by omega) s) := by
  rw [omPlusCurtisDatum_X, omPlusCurtisDatum_X, plusRootGroup_single, plusRootGroup_single]
  constructor
  · rintro ⟨c, rfl⟩
    rw [omPlusTwist_graphSpin_rootD]
    exact ⟨c, rfl⟩
  · rintro ⟨c, hc⟩
    have hπ : omGraphSwap (by omega) (omGraphSwap (by omega) s) = s := by
      rw [omGraphSwap]
      exact Equiv.swap_apply_self _ _ s
    have h1 : graphSpin n K ⟨n - 1, by omega⟩
        (rootD K hn (omGraphSwap (by omega) s) c) = x := by
      rw [hc, omPlusTwist_graphSpin_graphSpin]
    have h2 : rootD K hn (omGraphSwap (by omega) (omGraphSwap (by omega) s)) c = x := by
      rw [← h1, omPlusTwist_graphSpin_rootD]
    rw [hπ] at h2
    exact ⟨c, h2⟩

theorem graphSpin_n_omPlus (hn : 3 ≤ n) (s : Fin n) :
    graphSpin n K ⟨n - 1, by omega⟩ ((omPlusCurtisDatum n K hn).n s) =
      (omPlusCurtisDatum n K hn).n (omGraphSwap (by omega) s) := by
  rw [omPlusCurtisDatum_n, omPlusCurtisDatum_n, weylD_eq, weylD_eq, map_mul, map_mul,
    omPlusTwist_graphSpin_rootD, omPlusTwist_graphSpin_negRootD]

theorem mu_eq_of_twist_graphSpin (hn : 3 ≤ n) {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) (spinGroup (quadPlus n K)) V} (hρ : IsSimpleRep ρ) {y : V}
    {χ : spinGroup (quadPlus n K) → ZMod 2} {μ : Fin n → ZMod 2}
    (ht : (omPlusCurtisDatum n K hn).IsCurtisType ρ y χ μ) (T : V ≃ₗ[ZMod 2] V)
    (hT : ∀ (g : spinGroup (quadPlus n K)) (v : V),
      T (ρ g v) = ρ (graphSpin n K ⟨n - 1, by omega⟩ g) (T v)) :
    μ ⟨n - 2, by omega⟩ = μ ⟨n - 1, by omega⟩ := by
  have h := mu_eq_of_twist (D := omPlusCurtisDatum n K hn) (p := 2) (k := ZMod 2)
    (ρ := ρ) hρ ht (graphSpin n K ⟨n - 1, by omega⟩) (omGraphSwap (by omega))
    (fun u hu => graphSpin_symm_mem_U_omPlus hn hu)
    (fun s x => mem_X_iff_graphSpin_mem_omPlus hn s x)
    (fun s => graphSpin_n_omPlus hn s) T hT ⟨n - 2, by omega⟩
  have hswap : omGraphSwap (by omega) (⟨n - 2, by omega⟩ : Fin n) = ⟨n - 1, by omega⟩ := by
    rw [omGraphSwap, Equiv.swap_apply_left]
  rw [hswap] at h
  exact h.symm

end CFSG.LocalAnalysis.WeakClosure81
